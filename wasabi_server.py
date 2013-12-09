#!/usr/bin/env python
#coding: utf-8

# Back-end server to support Wasabi web application
# Written by Andres Veidenberg [andres.veidenberg{at}helsinki.fi] and Alan Medlar, University of Helsinki [2012]

import os
import string
import random
import cgi
import urllib2
import subprocess
import time
import json
import socket
import shutil
import sys
import threading
import Queue
import multiprocessing
import tempfile
import ConfigParser
import logging
import webbrowser
import argparse
import smtplib
import zipfile
import re
from BaseHTTPServer import BaseHTTPRequestHandler, HTTPServer
from SocketServer import ThreadingMixIn


wasabiexec = os.path.realpath(__file__)
appdir = os.path.dirname(wasabiexec) #get wasabi homedir
wasabidir = os.path.realpath(os.path.join(appdir,os.pardir))
osxbundle = False
if(os.path.isfile(os.path.join(appdir,'AppSettings.plist'))):
    wasabidir = os.path.realpath(os.path.join(wasabidir,'..','..')) #OSX bundle path
    osxbundle = True
os.chdir(wasabidir)
prankbin = os.path.join(appdir,'binaries','prank','prank')

job_queue = None

def getconf(opt='',vtype=''): #parse conf file values
    try:
        if(vtype=='int'): return config.getint('server_settings',opt)
        elif(vtype=='bool'): return config.getboolean('server_settings',opt)
        else:
            val = config.get('server_settings',opt)
            return '' if(vtype=='file' and '.' not in val) else val
    except ConfigParser.Error: return 0 if(vtype=='int') else ''

#Initialize: read/create settings and work folders
config = ConfigParser.ConfigParser()
defaultsettings = os.path.join(appdir,'default_settings.cfg')
config.read(defaultsettings)
dataroot = os.path.realpath(getconf('datadir') or 'wasabi_data')
if not os.path.exists(dataroot): os.makedirs(dataroot,0775)
settingsfile = os.path.join(dataroot,'wasabi_settings.cfg')
if not os.path.isfile(settingsfile):
    try: shutil.copy(defaultsettings, settingsfile)
    except IOError as why: print "Could not create settings file: "+str(why) 
else: config.read(settingsfile)
datadir = os.path.join(dataroot,'analyses')
if not os.path.exists(datadir):
    os.makedirs(datadir,0775)
    try: shutil.copytree(os.path.join(appdir,'example'), os.path.join(datadir,'example'))
    except IOError as why: print "Could not create analysis library directory: "+str(why)
sys.stdout.flush()
exportdir = os.path.join(dataroot,'exports')
if not os.path.exists(exportdir): os.makedirs(exportdir,0775)
#set globals from config file
serverport = getconf('serverport','int') or 8000
num_workers = getconf('workerthreads','int') or multiprocessing.cpu_count()
cpulimit = getconf('cputime','int')
datalimit = getconf('datalimit','int')
autoupdate = getconf('autoupdate','bool')
useraccounts = getconf('useraccounts','bool')
logtofile = getconf('logfile','bool')
debug = getconf('debug','bool')
local = getconf('local','bool')
eposcript = getconf('eposcript')
gmail = getconf('gmail')
browsername = getconf('browser') or 'default'
userexpire = getconf('userexpire','int')
userlog = os.path.join(datadir,'user.log')
if useraccounts: open(userlog,'w').close()
linuxdesktop = getconf('linuxdesktop','bool')

#set up logging
logfile = os.path.join(dataroot,'server.log') if logtofile else False
if logfile: open(logfile,'w').close()
loglevel = logging.DEBUG if(debug) else logging.INFO
logging.basicConfig(level=loglevel, filename=logfile, format='%(asctime)s - %(message)s', datefmt='%d.%m.%y %H:%M:%S')

#create linux shortcut
if(sys.platform.startswith('linux') and linuxdesktop):
    try:
    	deskfile = os.path.join(appdir,'wasabi.desktop')
        deskconf = ConfigParser.ConfigParser()
        deskconf.optionxform = str
        deskconf.read(deskfile)
        if(deskconf.get('Desktop Entry','Exec') is not wasabiexec):
            deskconf.set('Desktop Entry','Exec',wasabiexec)
            deskconf.set('Desktop Entry','Icon',os.path.join(appdir,'images','icon.png'))
            with open(deskfile,'wb') as fhandle: deskconf.write(fhandle)
            shutil.copy(deskfile, os.path.expanduser('~/Desktop'))
    except (ConfigParser.Error, shutil.Error, IOError) as why: logging.error('Could not create desktop shortcut: '+str(why))

#change to directory to be served (for GET requests)
os.chdir(appdir)

def apath(path, d=wasabidir, uid=''): #confines a filepath
    path = os.path.realpath(path)
    testdir = os.path.realpath(d)
    if(useraccounts and testdir is datadir and uid is not 'skip'):
        if(uid): testdir = os.path.join(datadir,uid)
        else: raise IOError(404, 'Userid required for file: '+os.path.basename(path))
    if(d is 'skip' or path.startswith(testdir)): return path
    else: raise IOError(404, 'Restricted path: '+path)

def joinp(*args,**kwargs): #join paths with confinment check
    testdir = kwargs.pop('d', datadir)
    userid = kwargs.pop('uid', '')
    return apath(os.path.join(*args), testdir, userid)

def userpath(path, uid=''): #gets path relative to user or library directory
    return path.split(os.path.join(datadir,uid,''))[-1]

def write_file(filename, filecontents):
    f = open(filename, 'w')
    f.write(filecontents)
    f.close()
    return f.name
    
def getlibrary(jobid='', uid='', skipmeta=''):
    global datadir
    if os.path.isabs(jobid): return jobid
    toplevel = datadir if uid=='skip' else joinp(datadir,uid,uid=uid)
    jobdirs = []
    for (dirpath,dirs,files) in os.walk(toplevel):
        if ('meta.txt' not in files and not skipmeta): continue
        if (jobid):
            if(jobid == os.path.basename(dirpath)): return dirpath
        else: jobdirs.append(dirpath)
    if(jobid and not jobdirs): raise IOError(404, "Getlib: Could not find job dir '%s' : %s" % (jobid,str(jobdirs)))
    else: return jobdirs

def create_job_dir(d = datadir, uid = '', newlibrary = False):
    if(d is not datadir): d = apath(d,d=datadir,uid=uid)
    else:
        if(uid): d = joinp(d,uid,uid=uid)
        elif(useraccounts): newlibrary = True
            
    if(not os.path.isdir(d)):
        try : os.makedirs(d,0775)
        except OSError as e:
            raise OSError(501,'Could not create a job folder to %s : %s' % (userpath(d), e.strerror))
                
    newdir = tempfile.mkdtemp(prefix='', dir=d)
    os.chmod(newdir,0775)
    
    if(newlibrary): #create library folder for a new user
        try: shutil.copytree(joinp(datadir,'example'),joinp(newdir,'example'))
        except shutil.Error: pass
        
        if userexpire:  #cleanup old user libraries (default: >30 days)
            try:
                for dname in os.listdir(datadir):
                    dpath = os.path.join(datadir,dname)
                    if(not os.path.isdir(dpath)): continue
                    lasttime = os.path.getmtime(dpath) #faulty in Windows?
                    dirage = (time.time()-filetime)/86400
                    if(dirage > userexpire): os.rmtree(apath(dpath,datadir,uid='skip'))
            except (OSError, IOError) as why: logging.error('Library cleanup failed: '+str(why))
    else: #create files for keeping metadata
        Metadata.create(newdir)
        Metadata.create(newdir, filename="importmeta.txt")
    return newdir

def info(msg):
    if(logfile): logging.info(msg)
    else:
        print str(msg)
        sys.stdout.flush()

def getsize(start_path = '.'): #get total filesize of a dirpath
    total_size = 0
    for dirpath, dirnames, filenames in os.walk(start_path):
        for f in filenames:
            fp = os.path.join(dirpath, f)
            total_size += os.path.getsize(fp)
    return total_size


#class to handle Wasabi server<=>browser communication
class WasabiServer(BaseHTTPRequestHandler):
    def log_message(self, format, *args):
        return #disable console printout of server events
    
    def sendError(self, errno=404, msg='', action=''): #log the error and send it to client browser
        #try: linenr = str(sys.exc_info()[2].tb_lineno)
        #except AttributeError: linenr = 'unknown'
        logging.error('Request "'+action+'" => '+str(errno)+': '+msg)
        if(debug): logging.exception('Details: ')
        self.send_error(errno,msg)
        
    
    def sendOK(self, msg='', size=0):
        self.send_response(200)
        if size:
            self.send_header("Content-Type", "text/octet-stream")
            self.send_header("Content-Length", str(size))
            self.send_header("Cache-Control", "no-cache")
        else: self.send_header("Content-Type", "text/plain")
        self.end_headers()
        if msg: self.wfile.write(msg)
        
    def do_HEAD(self):
        try:
            self.send_response(200)
            self.end_headers()
            self.wfile.write('URL exists')
            return   
        except IOError:
            self.sendError(404,'File Not Found: %s' % self.path,'HEAD')
    
    #serve files        
    def do_GET(self):
        try:
            url = self.path
            urldir = ''
            params = ''
            filecontent = ''
            userid = ''
            filename = ''
            
            if url.endswith("/"): url += "index.html"
            url = url[1:] #remove leading /
            if('?' in url):
                urlarr = url.split('?')
                url = urlarr[0]
                params = dict([x.split('=') for x in urlarr[1].split('&')])
                
            if("." not in url and "/" not in url):
                if(os.path.isdir(joinp(datadir,url,uid='skip'))): #check user ID in url
                    userid = url
                url = "index.html"
            
            if params :
                logging.debug("Get: userid=%s %s" % (userid, str(params)))
            
            if 'type' in params:
                ctype = 'text/plain' if(params['type'] is 'text') else 'application/octet-stream'
            elif url.endswith(".html") | url.endswith(".css") | url.endswith(".js"): #send as text
                ctype = 'text/css' if url.endswith(".css") else 'text/javascript' if url.endswith(".js") else 'text/html'
            else: #send as binary
                ctype = 'image' if url.endswith(".jpg")|url.endswith(".png")|url.endswith(".gif") else 'application/octet-stream'
           
            root = wasabidir  
            if('file' in params and 'type' in params): #access datafiles from external directories
                if 'getlibrary' in params and params['getlibrary']:
                    if('share' in params): userid = 'skip'
                    url = os.path.join(getlibrary(uid=userid,jobid=params['getlibrary']), params['file'])
                    filename = params['file']
                elif local: #local wasabi installation permits unrestricted file reading
                    url = params['file']
                    root = 'skip'
                else: raise IOError(404,'faulty request')
            elif 'getexport' in params:
                url = joinp(exportdir, params['getexport'], d=exportdir)
                filename = params['getexport']
                
            f = open(apath(url,root)) if 'text' in ctype else open(apath(url,root),'rb')
            filecontent = f.read()
            f.close()
            self.send_response(200)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", len(filecontent))
            if(ctype == 'image'): self.send_header("Cache-Control", "max-age=300000")
            if(filename): self.send_header("Content-Disposition", "attachment; filename="+filename)
            self.end_headers()
            self.wfile.write(filecontent)  
        except IOError as e:
            self.sendError(e.errno, 'File Not Found: %s (%s)' % (url, e.strerror), 'GET')

    #send server status
    def post_checkserver(self, form, userid):
        status = {"status":"OK"}
        if(useraccounts):
            if(not userid or not os.path.isdir(joinp(datadir, userid, uid='skip'))): #create new user folder
                userid = os.path.basename(create_job_dir(newlibrary=True))
                status["newuser"] = "yes"
            os.utime(joinp(datadir, userid, uid='skip'),None) #timestamp last login
            status["userid"] = userid
        if(autoupdate): status["autoupdate"] = "yes"
        if(local):
            status["local"] = "yes"
            status["datadir"] = dataroot
            status["browser"] = browsername or "default"
            if(osxbundle): status["osxbundle"] = "yes"
            if(sys.platform.startswith('linux')):
                status["linuxdesktop"] = "yes" if linuxdesktop else ""
        if(eposcript): status["epoimport"] = "yes"
        if(gmail): status["email"] = "yes"
        if(cpulimit): status["cpulimit"] = cpulimit
        if(datalimit):
            status["datalimit"] = datalimit
            status["datause"] = getsize(joinp(datadir, userid, uid='skip'))
        if(userexpire): status["userexpire"] = userexpire
        self.sendOK()
        self.wfile.write(json.dumps(status))

    #reflect uploaded file
    def post_echofile(self, form, userid):
        self.sendOK()
        self.wfile.write(form.getvalue('upfile'))

    #forward remote file
    def post_geturl(self, form, userid):
        url = form.getvalue('fileurl','')
        try:
            urlfile = urllib2.urlopen(url)
            totalsize = int(urlfile.info().getheaders("Content-Length")[0])
        except (ValueError, urllib2.URLError) as e:
            raise IOError(404, e.reason or 'Invalid URL: '+url)
        self.sendOK(size=totalsize)
        self.wfile.write(urlfile.read())
    
    #store form fields
    def _add_if_present(self, store, form, key):
        val = form.getvalue(key,'')
        if val: store[key] = json.loads(val)
  
    #save files to libary
    def post_save(self, form, userid):
        self.post_startalign_save(form, 'save', userid)
            
    #start new alignment job
    def post_startalign(self, form, userid):
        self.post_startalign_save(form, 'startalign', userid)

    def post_startalign_save(self, form, action, userid):
        global job_queue, datadir
                
        parentid = form.getvalue('parentid','')
        currentid = form.getvalue('id','')
        writemode = form.getvalue('writemode','') #infer target path in library
        name = form.getvalue('name','')
        odir = datadir
        
        logging.debug("%s: userid=%s parentid=%s currentid=%s writemode=%s" % (action, userid, parentid, currentid, writemode))
        
        if(writemode=='child' or writemode=='sibling'):  #create a child job
            if writemode=='child': parentid = currentid
            odir = create_job_dir(d=getlibrary(jobid=parentid,uid=userid), uid=userid)
        elif(writemode=='overwrite' and currentid):  #rerun of job, use same directory
            odir = getlibrary(jobid=currentid, uid=userid)
        else: odir = create_job_dir(uid=userid)  #create new top-level job directory
        
        jobid = os.path.basename(odir)
        response = {"id":jobid}

        #metadata files
        metadata = Metadata(jobid, uid=userid)
        importdata = Metadata(jobid, filename="importmeta.txt", uid=userid)
        #store form info to metadata file
        self._add_if_present(importdata, form, "idnames")
        self._add_if_present(importdata, form, "ensinfo")
        self._add_if_present(importdata, form, "nodeinfo")
        self._add_if_present(importdata, form, "visiblecols")
    
        if action == 'startalign' : #start new alignment job
            infile = write_file(os.path.join(odir, 'input.fas'), form.getvalue('fasta',''))
            outfile = os.path.join(odir, 'out')
            treefile = None
            logfile = os.path.join(odir, 'output.log')
            
            if 'newick' in form :
                treefile = write_file(os.path.join(odir, 'input.tree'), form.getvalue('newick',''))

            job = PrankJob(jobid, name, infile, outfile, treefile, logfile, form)
            
            metadata.update(job.json())
            job_queue.enqueue(jobid, job)

        elif action == 'save': #write files to library path
            savename = "saved.xml"
            response["name"] = savename
            savefile = write_file(os.path.join(odir,savename), form.getvalue('file',''))
            for p in ["name","source","parameters"]:
                pval = form.getvalue(p,'')
                if(pval): metadata[p] = pval
            metadata["savetime"] = str(time.time())
            metadata["outfile"] = os.path.basename(savefile)

        metadata.flush()
        importdata.flush()

        self.sendOK()
        self.wfile.write(json.dumps(response))
    
    #fetch EPO alignment to library
    def post_startepo(self, form, userid):
        if(not eposcript or not os.path.isfile(eposcript)): raise IOError(404,'EPO dump script not found: '+str(eposcript))
        
        odir = create_job_dir(uid=userid)
        epofilename = os.path.join(odir,form.getvalue('output_file','epo_slice.xml'))
        params = [eposcript, '--output_format', 'xml', '--output_file', epofilename, '--restrict']
        for param in ['alignment','set','species','seq_region','seq_region_start','seq_region_end','db','masked_seq']:
            params.append('--'+param)
            params.append(form.getvalue(param,''))

        jobid = os.path.basename(odir)
        logfilename = 'output.log'
        metadata = Metadata(jobid, uid=userid)
        metadata["name"] = 'EPO alignment'
        metadata["source"] = 'Ensembl'
        metadata["starttime"] = str(time.time())
        metadata["savetime"] = metadata["starttime"]
        metadata["outfile"] = ''
        metadata["logfile"] = logfilename
        metadata.flush()
        logfile = open(os.path.join(odir,logfilename), 'w')
        
        detach_flag = 0x00000008 if os.name is 'nt' else 0 #for windows
        popen = subprocess.Popen(params, stdout=logfile, stderr=logfile, creationflags=detach_flag, close_fds=True)
        status = popen.poll()
        status = str(status) if status else 'running' #0=finished, -2=failed, None=running
        
        self.sendOK()
        self.wfile.write('{"id":"'+jobid+'","status":"'+status+'"}')

    #add data to job metadata file
    def post_writemeta(self, form, userid):
        jobid = form.getvalue('id', '')
        if(not jobid): raise IOError(404,'No jobID given for writemeta')
        key = form.getvalue('key', 'imported')
        value = form.getvalue('value', str(time.time()))
        try :
            md = Metadata(jobid, uid=userid)
            md[key] = value
            md.flush()
            self.sendOK()
            self.wfile.write('['+str(md)+']')
        except MetadataError as mde :
            logging.error('Metadata write error: %s' % mde)
            self.sendOK()
            return
    
    #send summary of entire analysis library
    def post_getlibrary(self, form, userid):
        metadata = []
        parent = ""
        rootlevel = userid or os.path.basename(datadir)
        for jobdir in getlibrary(uid=userid):
            try :
                md = Metadata(jobdir)
                if(not md['imported']): md.update_log()
                parent = os.path.basename(os.path.dirname(jobdir))
                if(parent == rootlevel): parent = ""
                md['parentid'] = parent
                metadata.append(str(md))
            except MetadataError as mde:
                logging.error('Metadata read error: %s' % mde)
        self.sendOK()
        self.wfile.write('['+','.join(metadata)+']')

    #send extra metadata for analysis import
    def post_getimportmeta(self, form, userid):
        jobid = form.getvalue('id','')
        if(form.getvalue('share')): userid = 'skip'
        self.sendOK()
        try:
            md = Metadata(jobid, filename="importmeta.txt", uid=userid)
            self.wfile.write(str(md))
        except MetadataError:
            self.wfile.write("{}")
    
    #send a library directory filelist
    def post_getdir(self, form, userid):
        jobdir = form.getvalue('dir', '')
        if not jobdir:
            self.sendOK()
            return
        dirpath = getlibrary(jobid=jobdir,uid=userid)
        if not os.path.isdir(dirpath):
            self.sendOK()
            return
        files = {}
        for item in os.listdir(dirpath):
            if item.startswith("."): continue
            itempath = os.path.join(dirpath,item)
            fsize = "folder" if os.path.isdir(itempath) else os.path.getsize(itempath)
            files[item] = fsize
        self.sendOK()
        self.wfile.write(json.dumps(files))

    #remove data dir
    def post_rmdir(self, form, userid):
        global job_queue
        jobid = form.getvalue('id','')
        
        if jobid :
            job_queue.terminate(jobid)
            rmpath = getlibrary(jobid=jobid,uid='skip',skipmeta=True) if form.getvalue('reset','') else getlibrary(jobid=jobid,uid=userid)
            shutil.rmtree(rmpath)
        
        self.sendOK('Deleted')

    #kill a running job
    def post_terminate(self, form, userid):
        global job_queue
        jobid = form.getvalue('id','')
        
        if jobid:
            job_queue.terminate(jobid)
            md = Metadata(jobid) #check result
            if(md['status']=='queued' or md['status']=='running'):
                md['status'] = '-15'
                md.flush()
        
        self.sendOK('Terminated')

    #write exported file to disk and send download link
    def post_makefile(self, form, userid):
        global exportdir
        filename = form.getvalue('filename','exported_data.txt')
        if userid: filename = userid+'_'+filename
        filedata = form.getvalue('filedata','')
        filepath = joinp(exportdir, filename, d=exportdir, uid=userid)
        exportfile = open(filepath,'w')
        exportfile.write(filedata)
        self.sendOK()
        self.wfile.write(userid+'?type=binary&getexport='+filename)
        
        for filename in os.listdir(exportdir): #cleanup old files (>2 days)
            filepath = os.path.join(exportdir,filename)
            filestat = os.stat(filepath)
            filetime = filestat.st_mtime
            curtime = time.time()
            fileage = (curtime-filetime)/86400
            if(fileage > 2): os.remove(filepath)
    
    #save a client-sent errorlog
    def post_errorlog(self, form, userid=''):
        global datadir
        global userlog
        global currentheader
        errorheader = '\n'+userid+' : '+(self.client_address[0] or '')+':\n'
        if(currentheader!=errorheader): currentheader = errorheader
        else: errorheader = ''
        errorlog = errorheader+form.getvalue('errorlog','')+'\n'
        with open(userlog,'a') as userlogfile: userlogfile.write(errorlog)
        self.sendOK('Done')
        
    #send a welcome email
    def post_sendmail(self, form, userid=''):
        guser, gpass = gmail.split(':')
        if '@' not in guser: guser += '@gmail.com'
        to = form.getvalue('email','')
        url = form.getvalue('url','')
        webaddr = 'http://'+self.headers.get('Host')
        msg = 'Wasabi is a web application for phylogenetic sequence analysis.\r\n'
        msg += 'You can learn more about Wasabi from http://wasabi.biocenter.helsinki.fi\r\n\r\n'
        if url:
            subj = 'Shared data from Wasabi'
            msg += 'To view the dataset that was shared with you, go to '+webaddr+'?'+url.split('?')[-1]
        else:
            subj = 'Welcome to Wasabi'
            msg += 'You can access your analysis library in Wasabi server at '+webaddr+'/'+userid
        st = 'Failed'
        if guser and gpass and '@' in to:
            try:
                gserver = smtplib.SMTP('smtp.gmail.com:587')
                gserver.ehlo()
                gserver.starttls()
                gserver.login(guser,gpass)
                mailstr = '\r\n'.join(['From: '+guser, 'To: '+to, 'Subject: '+subj, '', msg])
                gserver.sendmail(guser, [to], mailstr)
                gserver.quit()
                st = 'Sent'
            except: raise
        self.sendOK(st)
    
    #automated Wasabi update
    def post_update(self, form, userid=''):
        global osxbundle
        try:  #download update, with progress feedback
            if osxbundle: updname = 'Wasabi.dmg'
            else:
                osname = 'osx' if sys.platform.startswith('darwin') else 'windows' if sys.platform.startswith('win') else 'linux'
                updname = 'wasabi_'+osname+'.zip'
            urlfile = urllib2.urlopen('http://wasabi2.biocenter.helsinki.fi/download/'+updname)
            totalsize = int(urlfile.info().getheaders("Content-Length")[0]) or 18000000
            chunksize = 100*1024
            chunkcount = int(totalsize/chunksize)
            updpath = os.path.join(dataroot,updname)
            self.sendOK(size=chunkcount+28)
            with open(updpath,'wb') as downfile:
                for chunk in iter(lambda:urlfile.read(chunksize),''):
                    downfile.write(chunk)
                    self.wfile.write('#')
        except (urllib2.URLError, shutil.Error) as why:
            raise IOError(404,'Failed to download Wasabi: %s' % why)
        oldappdir = os.path.realpath(os.path.join(appdir,'..','..')) if osxbundle else appdir
        appname = os.path.basename(oldappdir)
        if(os.path.isdir(oldappdir) and os.listdir(oldappdir)):  #make a backup
            archive = os.path.join(dataroot,'backups')
            try:
                if(not os.path.isdir(archive)): os.makedirs(archive,0775)
                basepath, ext = os.path.splitext(oldappdir)
                safedir = basepath+str(len(os.listdir(archive)) or '')+ext
                os.rename(oldappdir,safedir)
            except OSError: pass
            shutil.move(safedir,archive)
        self.wfile.write('##########')
        if osxbundle: #extract new app from diskimage
            try: subprocess.check_output(['hdiutil','attach','-noverify','-nobrowse','-mountpoint','/Volumes/Wasabi',updpath], stderr=subprocess.STDOUT)
            except subprocess.CalledProcessError as e: raise IOError(404,'Failed to mount Wasabi diskimage: %s' % e.output)
            shutil.copytree('/Volumes/Wasabi/Wasabi.app', os.path.join(wasabidir,appname))
            subprocess.call('hdiutil detach -quiet -force /Volumes/Wasabi', shell=True)
        else:  #extract new app from zipfile
            zipf = zipfile.ZipFile(updpath)
            newappname = zipf.namelist()[0][:-1]
            zipf.extractall(wasabidir)
            if(newappname is not appname): os.rename(joinp(wasabidir,newappname,d=wasabidir,uid='skip'),appdir)
        self.wfile.write('##########')
        try:
            newconfig = ConfigParser.ConfigParser()
            newconfig.read(defaultsettings)  #read new config file 
            newconfig.set('server_settings','datadir',dataroot)  #save current datadir
            with open(defaultsettings,'wb') as newconffile: newconfig.write(newconffile)
        except ConfigParser.Error: logging.error('Wasabi update error: Could not update settings file.')
        self.wfile.write('Updated')
    
    #change server settings
    def post_settings(self, form, userid=''):
        global local
        global osxbundle
        global settingsfile
        if(local):
            setting = form.getvalue('setting','')
            value = form.getvalue('value','')
            if(setting=='OutputType' and osxbundle):  #update OSX app settings
                value = 'Text Window' if value=='true' else 'None'
                with open(os.path.join(appdir,'AppSettings.plist'),'r+b') as f:   
                    fcontent = f.read()
                    fcontent = re.sub(r'(<key>OutputType</key>\s+<string>).+</string>', r'\1'+value+'</string>', fcontent)
                    f.seek(0)
                    f.truncate()
                    f.write(fcontent)
            else:  #update Wasabi app settings
                try:
                    if(setting=='datadir' and not os.path.isdir(value)): raise IOError(404, 'Invalid folder path.')
                    config.set('server_settings',setting,value)
                    with open(defaultsettings if setting=='datadir' else settingsfile,'wb') as newconffile: config.write(newconffile)
                except ConfigParser.Error as e: logging.error("Could not update settings file: %s", e)
            self.sendOK('Setting updated')
        else: raise IOError(404, 'Restricted request: only for local installation.')
    
    #POST request sent to server
    def do_POST(self):
        try:
            form = cgi.FieldStorage(fp = self.rfile, headers = self.headers, environ={'REQUEST_METHOD':'POST'})
            action = form.getvalue('action','')
            userid = form.getvalue('userid','') if useraccounts else ''
            
            if(action!='getlibrary'): logging.debug("Post: %s, userid=%s" % (action, userid))
            if(useraccounts and action not in ['checkserver','errorlog','terminate']): #userid check
                if(not userid or not os.path.isdir(joinp(datadir, userid, uid='skip'))) :
                    raise IOError(404,'Post '+action+' => User folder "'+userid+'" does not exist')
                    
            getattr(self, "post_%s" % action)(form, userid)
            
        except IOError as e:
            if hasattr(e, 'reason'): self.sendError(404,'URL does not exist. %s' % e.reason, action)
            else: self.sendError(404, str(e), action)
        except OSError as e:
            self.sendError(501,"System error. %s" % e.strerror, action)
        except AttributeError as e:
            self.sendError(501, 'Invalid POST request. %s' % str(e), action)
            raise

#HTTP server subclass for multithread requests
class MultiThreadServer(ThreadingMixIn, HTTPServer):
    allow_reuse_address = True #allow restart after dirty close
    
    def __init__(self, *args):
        HTTPServer.__init__(self, *args)
        
    def process_request_thread(self, request, client_address):
        try:
            self.finish_request(request, client_address)
            self.close_request(request)
        except socket.error:
            logging.debug('Disconnected request from %s' % str(client_address))

#class for queuing server-side jobs
class WorkQueue(object):
    def __init__(self, numworkers=0, qtimeout=1, maxsize=0):
        self.jobs = {}
        self.q = Queue.Queue(maxsize)
        self.workers = self._init_workers(numworkers)
        self.q_timeout = qtimeout
        self.running = False

    def _introspect_cores(self):
        return multiprocessing.cpu_count()

    def _init_workers(self, numworkers):
        if numworkers == 0 :
            numworkers = self._introspect_cores()
        tmp = []
        
        for _ in range(numworkers):
            t = threading.Thread(target=self._consume_queue)
            t.daemon = True
            tmp.append(t)

        return tmp

    def start(self):
        self.running = True
        
        for t in self.workers:
            t.start()
        #logging.debug("WorkQueue: started")

    def stop(self):
        self.running = False
        self.q.join()
        
        for t in self.workers:
            t.join()
        #logging.debug("WorkQueue: stopped")

    def enqueue(self, key, job):
        logging.debug("WorkQueue: enqueuing %s" % key)
        self.jobs[key] = job
        self.q.put(job)  #this can fail if maxsize has been set (or if we run out of RAM)

    def get_status(self, key) :
        return self.get(key).status()

    def get(self, key):
        try :
            return self.jobs[key]
        except KeyError:
            logging.error("WorkQueue: %s not queued" % key)

    def _consume_queue(self):
        while self.running :
            try :
                work = self.q.get(timeout=self.q_timeout)
            except Queue.Empty:
                continue

            logging.debug("WorkQueue: starting %s" % work.jobid())

            work.process()
            del self.jobs[work.jobid()]
            self.q.task_done()

            logging.debug("WorkQueue: completed %s (status: %s)" % (work.jobid(), work.status()))

    def terminate(self, jobid) :
        logging.debug("WorkQueue: terminate %s" % jobid)
        
        try :
            j = self.jobs[jobid]
            j.terminate()
            
        except KeyError:
            pass

class MetadataError(Exception) :
    pass

#class for handling metadata files in job directories
class Metadata(object):
    def __init__(self, jobid, filename="meta.txt", uid = '') :
        global datadir
                
        self.jobdir = getlibrary(jobid=jobid, uid=uid)
        self.md_file = os.path.join(self.jobdir, filename)

        if not os.path.exists(self.md_file) :
            raise MetadataError("file not found: %s" % self.md_file)

        self.metadata = json.load(open(self.md_file))

    def __getitem__(self, key) :
        try: return self.metadata[key]
        except KeyError:
            #logging.error('"'+key+'" not found in metadata!')
            return False
    
    def __setitem__(self, key, value) :
        self.metadata[key] = value
    
    def __len__(self):
        return len(self.metadata)
    
    def __str__(self) :
        return json.dumps(self.metadata)
    
    def update(self, d) :
        for k in d :
            self.metadata[k] = d[k]
    
    def flush(self) :
        f = tempfile.NamedTemporaryFile(suffix=os.path.basename(self.md_file), prefix='', dir=self.jobdir, delete=False)
        json.dump(self.metadata, f, indent=2)
        f.close()
        os.rename(f.name, self.md_file)
    
    def update_log(self) :
        if(self['logfile']):
            self['log'] = self.last_log_line(self['logfile'])
            self['lasttime'] = os.stat(os.path.join(self.jobdir,self['logfile'])).st_mtime
    
    def last_log_line(self, filename='output.log') :
        try:
            f = open(os.path.join(self.jobdir, filename))
        except IOError:
            return "No log file yet."
            
        feedback = "Nothing logged yet."
        for line in f :
            line = line.strip()
            prefix = ''
            
            if line == '': continue
            elif 'iteration' in line: prefix = line
            elif '\b' in line: feedback = prefix+line.split('\b')[-1]
            else: feedback = line
    
        f.close()
        return feedback

    @staticmethod
    def create(d, filename="meta.txt") :
        f = open(joinp(d, filename), 'w')
        f.write('{"id":"'+os.path.basename(d)+'", "imported":"", "outfile":"", "starttime":"'+str(time.time())+'"}')
        f.close()
        return Metadata(d, filename)

#a job class for WorkQueue
class Job(object):
    INIT,QUEUED,RUNNING,FAIL,SUCCESS,TERMINATED = range(6)

    def __init__(self, key, name):
        self.key = key
        self.name = name
        
        self.job_status = Job.QUEUED
        self.starttime = time.time()
        self.endtime = 0
        
        self.lock = threading.Lock()
        self.popen = None

        self.states = {
            Job.INIT    : 'init',
            Job.QUEUED  : 'queued',
            Job.RUNNING : 'running',
            Job.FAIL    : '-1',
            Job.SUCCESS : '0'
        }

        self.items = {
            "id"         : self.jobid,
            "name"       : self.description,
            "status"     : self.status,
            
            "aligner"    : self.program,
            "parameters" : self.parameters,
            
            "logfile"    : self.logfile,
            "infile"     : self.infile,
            "outfile"    : self.outfile,
            
            "starttime"  : self.start_time,
            "endtime"    : self.end_time,
            "savetime"   : self.save_time,
            "lasttime"   : self.last_time,
            "imported"   : self.imported,
            
            "log"        : self.last_log_line
        }

    def __getitem__(self, key) :
        return self.items[key]()

    def lock_status(self) :
        self.lock.acquire()
    
    def unlock_status(self) :
        self.lock.release()

    def terminate(self) :
        self.lock_status()
        
        self.job_status = Job.TERMINATED
    
        if self.popen is not None:
            self.popen.terminate()

        self.unlock_status()

    def set_status(self, state) :
        self.job_status = state

    def done(self) :
        return self.status in (Job.FAIL, Job.SUCCESS)
    
    def begin(self) :
        self.starttime = time.time()
        self.set_status(Job.RUNNING)
        md = Metadata(self.jobid())
        md['status'] = self.status()
        md.flush()
    
    def end(self, rc) :
        self.endtime = time.time()
        
        if rc == 0 :
            self.set_status(Job.SUCCESS)
        else :
            self.set_status(Job.FAIL)
            self.states[Job.FAIL] = str(rc)
    
        md = Metadata(self.jobid())
        md.update(self.json())
        md.flush()
    
    def imported(self): return ""

    def jobid(self): return self.key
    
    def description(self): return self.name

    def program(self): raise RuntimeException()
        
    def parameters(self): raise RuntimeException()

    def infile(self): raise RuntimeException()
    
    def outfile(self): raise RuntimeException()

    def logfile(self): raise RuntimeException()

    def last_log_line(self): return "Nothing yet..."

    def status(self): return self._str_status(self.job_status)

    def start_time(self): return self.starttime
    
    def end_time(self): return self.endtime
    
    def save_time(self): return ""
    
    def last_time(self): return time.time()

    def _str_status(self, s): return self.states[s]

    def json(self): #stringify status for metadata file
        mdata = {}
        
        for k in self.items :
            val = str(self.items[k]())
            if k.endswith("time") and (val=="0"): val = ""
            if k.endswith("file"):
                if "." not in val: val = ""
                else: val = os.path.basename(val)
            mdata[k] = val
        return mdata

#Job class extension for prank alignment jobs
class PrankJob(Job):
    def __init__(self, key, name, infile, outfile, treefile, logfile, prank_options):
        global prankbin
        
        super(PrankJob, self).__init__(key, name)
        
        # in, out and log files should be defined in the Job superclass
        self.files = {
            'infile'   : infile,
            'outfile'  : outfile,
            'treefile' : treefile,
            'logfile'  : logfile
        }
        
        self.params = [prankbin, '-d='+infile, '-o='+outfile, '-prunetree', '-showxml', '-showevents']
        
        if treefile is not None :
            self.params.append('-t='+treefile)
            
        flags = ['F','e','dots','update','nomissing','uselogs']
        numvals = ['gaprate','gapext','kappa','rho']
        optset = set()
        
        for opt in prank_options:
            if prank_options[opt].value:
                if opt in flags: self.params.append('-'+opt)
                elif opt in numvals: self.params.append('-'+opt+'='+prank_options[opt].value)
                else: optset.add(opt)
    
        if 'anchor' not in optset: self.params.append('-noanchors')
        
        if 'iterate' not in optset: self.params.append('-once')
        else: self.params.append('-iterate='+prank_options.getvalue('rounds','5'))
        
        if 'translate' in optset:
            self.params.append('-'+prank_options.getvalue('translateto','translate'))
        
        if 'nomissing' in prank_options : self.params.append('-termgap')
        
        if optset >= {'A','C','G','T'}:
            vals = ','.join([prank_options[b].value for b in ['A','C','G','T']])
            self.params.append('-dnafreqs='+vals)
         
        if optset >= {'ind1','ind2','ind3','ind4'}:
            vals = ','.join([prank_options['ind'+n].value for n in ['1','2','3','4']])
            self.params.append('-indelscore='+vals)
    
    def program(self): return "PRANK"
        
    def parameters(self): return ','.join(os.path.basename(p) for p in self.params[1:])

    def infile(self): return self.files['infile']
    
    def outfile(self): return self.files['outfile']

    def logfile(self): return self.files['logfile']

    def _reset_results_file(self):
        out = self.files['outfile']
        for ver in ['.best','.2','.1','.0','']:
            outfile = out + ver + '.xml'
            if os.path.isfile(outfile):
                self.files['outfile'] = outfile
                break

    def process(self):
        self.lock_status()

        if self.job_status == Job.TERMINATED:
            self.unlock_status()
            return

        self.begin()

        logfile = open(self.files['logfile'], 'w')
        #limit cpu load
        cputime = ['ulimit','-t',str(cpulimit*3600)+';'] if(cpulimit) else []
        self.popen = subprocess.Popen(cputime+['nice','-n','20']+self.params, stdout=logfile, stderr=logfile, close_fds=True)
        
        self.unlock_status()
        ret = self.popen.wait()

        self.lock_status()
        self._reset_results_file()
        self.end(ret)
        logfile.close()
        self.unlock_status()

def main():
    global job_queue
    global serverport
    global num_workers
    global local
    global debug
    global browsername
    global osxbundle
    
    parser = argparse.ArgumentParser(description="A support server for Wasabi webapp.")
    parser.add_argument("-p", "--port", type=int, metavar="N", help="set server port (default: %s)" % serverport, default=serverport)
    vgroup = parser.add_mutually_exclusive_group()
    vgroup.add_argument("-v", "--verbose", action='store_true', help="show server traffic %s" % ("(default)" if debug else ""), default=debug)
    vgroup.add_argument("-q", "--quiet", action='store_true', help="minimal feedback %s" % ("(default)" if not debug else ""))
    lgroup = parser.add_mutually_exclusive_group()
    lgroup.add_argument("-l", "--local", action='store_true', help="autolaunch web browser %s" % ("(default)" if local else ""), default=local)
    lgroup.add_argument("-r", "--remote", action='store_true', help="just start the server %s" % ("(default)" if not local else ""))
    args = parser.parse_args()
    serverport = args.port
    debug = False if args.quiet else args.verbose
    local = False if args.remote else args.local
    if not debug: logging.disable(logging.DEBUG)

    info('Starting server...\n')
    job_queue = WorkQueue(num_workers)
    job_queue.start()

    try:
        server = MultiThreadServer(('',serverport), WasabiServer)
        info("Wasabi HTTP server started at port %d\n" % serverport)
        if(not osxbundle): info("Press CRTL+C to stop the server.\n")
        logging.debug('Serving from: '+str(appdir))
        logging.debug(socket.getfqdn()) #get server hostname
        
        if(local and browsername!='NO'): #autolaunch wasabi in a webbrowser
            if(browsername=='default'): browsername = None
            try:
                if sys.platform=='darwin': webbrowser.register("chrome", None, webbrowser.MacOSXOSAScript("Google Chrome"))
                else: webbrowser.register("chrome", "google-chrome %s", None) #register Chrome
                controller = webbrowser.get(browsername)
                controller.open("http://localhost:%d" % serverport, 1, True)
            except webbrowser.Error, e: logging.error("Failed to open a web browser: %s" % e)
        server.serve_forever()
    except socket.error, e :
        logging.error(e)
        return -1
    except KeyboardInterrupt:
        info("\nShutting down server...")
        server.socket.close()
    
    if(len(job_queue.jobs)):
        info("Warning: %s jobs in the queue were cancelled." % len(job_queue.jobs))
    job_queue.stop()
    return 0

if __name__ == '__main__':
    sys.exit(main())

