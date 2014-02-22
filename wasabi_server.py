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
#for tracking library content
job_queue = None
libdirs = {}

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
if useraccounts: open(userlog,'wb').close()
linuxdesktop = getconf('linuxdesktop','bool')

#set up logging
logfile = os.path.join(dataroot,'server.log') if logtofile else False
if logfile: open(logfile,'wb').close()
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
    f = open(filename, 'wb')
    f.write(filecontents)
    f.close()
    return f.name
    
def maplibrary(libraryid=''): #index library directories
    global libdirs
    libdirs = {}
    libroot = getlibrary(jobid=libraryid) if libraryid else datadir
    for (dirpath,dirs,files) in os.walk(libroot,followlinks=False):
        path = dirpath.split(os.path.sep)
        if('meta.txt' not in files): Metadata.create(dirpath, imported=True)
        libdirs[path[-1]] = {'parent':path[-2],'children':dirs}
    if useraccounts: #remove reference to analysis root folder
        try: del libdirs[os.path.basename(datadir)]
        except KeyError: pass

def librarypath(jobid, getroot=False): #build directory path from library index
    if(jobid not in libdirs): raise IOError(404, "Invalid library ID: "+jobid)
    libpath = jobid
    while jobid in libdirs:
        libpath = libdirs[jobid]['parent']+os.path.sep+libpath
        jobid = libdirs[jobid]['parent']
    if getroot: return libpath.split(os.path.sep)[1] #just return libraryID
    rootpath = os.path.dirname(datadir)
    if not useraccounts: rootpath = os.path.dirname(rootpath)
    dirpath = os.path.join(rootpath,libpath)
    return dirpath

def librarypaths(libraryid, inclroot=False): #get all subfolder paths
    dirpaths = [librarypath(libraryid)] if inclroot else []
    if libraryid in libdirs:
        for childid in libdirs[libraryid]['children']:
            dirpaths.append(librarypath(childid))
            dirpaths += librarypaths(childid)
    return dirpaths
    
def getlibrary(jobid='', uid='', checkowner=False): #search analyses library
    if os.path.isabs(jobid): return jobid
    if jobid: #return a directory path
        if(uid and checkowner and uid!=librarypath(jobid,True)): raise IOError(404,'Permission denied for '+jobid)
        if(jobid not in libdirs): maplibrary() #remap and try again
        if(jobid not in libdirs): raise IOError(404, "Invalid library ID: "+jobid)
        return librarypath(jobid)
    else: return librarypaths(uid or os.path.basename(datadir)) #return all library paths

def getmeta(dirpath, rootlevel, shareroot=None): #get processed metadata
    try:
        md = Metadata(dirpath)
        if(not md['imported']): md.update_log()
        dirid = md['id'] or os.path.basename(dirpath)
        md['parentid'] = "" if libdirs[dirid]['parent'] == rootlevel else libdirs[dirid]['parent']
        md['children'] = len(libdirs[dirid]['children'])
        if md['shared'] and shareroot is None: #check shared IDs added to this libfolder
            idlist = [d for d in md['shared'] if d in libdirs]
            if len(idlist) is not len(md['shared']):
                md.update({"shared":idlist})
                md['shared'] = idlist
            md['children'] += len(idlist)
        elif shareroot is not None: #this is shared analysis
            if not md['parentid']: md['parentid'] = shareroot
            md['shared'] = "true"
    except MetadataError as why:
        logging.error('Metadata parsing error: %s' % why)
    return md

def create_job_dir(d = datadir, uid = '', newlibrary = False, newfolder = False):
    if(d is not datadir): d = apath(d,d=datadir,uid=uid)
    else:
        if(uid): d = joinp(d,uid,uid=uid)
        elif(useraccounts): newlibrary = True
            
    if(not os.path.isdir(d)):
        try : os.makedirs(d,0775)
        except OSError as e:
            raise OSError(501,'Could not create a job folder to %s : %s' % (userpath(d), e.strerror))
                
    newdir = tempfile.mkdtemp(prefix='', dir=d)
    while(os.path.basename(newdir) in libdirs): #check for uniqueness
        os.rmdir(newdir)
        newdir = tempfile.mkdtemp(prefix='', dir=d)
    os.chmod(newdir,0775)
    
    if(newlibrary): #create library folder for a new user
        md = Metadata.create(newdir, name="Library root folder", imported=True)
        md.update({"shared":["example"]})
        maplibrary()
        
        if userexpire and useraccounts:  #cleanup old user libraries (default: >30 days)
            try:
                for dname in os.listdir(datadir):
                    dpath = os.path.join(datadir,dname)
                    if(not os.path.isdir(dpath)): continue
                    lasttime = os.path.getmtime(dpath) #faulty in Windows?
                    dirage = (time.time()-lasttime)/86400
                    if(dirage > userexpire): os.rmtree(apath(dpath,datadir,uid='skip'))
            except (OSError, IOError) as why: logging.error('Library cleanup failed: '+str(why))
    else: #create files for keeping metadata
        if newfolder: Metadata.create(newdir, name="new folder", imported=True)
        else:
            Metadata.create(newdir)
            Metadata.create(newdir, filename="importmeta.txt")
        maplibrary(uid)
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
        url = self.path
        urldir = ''
        params = ''
        filecontent = ''
        userid = ''
        filename = ''
            
        if url.startswith("/"): url = url[1:]
        if url.endswith("/"): url += "index.html"
        if('?' in url):
            urlarr = url.split('?')
            url = urlarr[0]
            params = dict([x.split('=') for x in urlarr[1].split('&')])
                
        if("." not in url and "/" not in url):
            if(url in libdirs): userid = url #check user ID   
            url = "index.html"
            
        if params :
            logging.debug("Get: userid=%s %s" % (userid, str(params)))
            
        if 'type' in params:
            ctype = 'text/plain' if(params['type'] is 'text') else 'application/octet-stream'
        elif 'file' in params or 'getlibrary' in params or 'getexport' in params:
            ctype = 'text/plain'
        elif url.endswith(".html") or url.endswith(".css") or url.endswith(".js"): #send as text
            ctype = 'text/css' if url.endswith(".css") else 'text/javascript' if url.endswith(".js") else 'text/html'
        else: #send as binary
            ctype = 'image' if url.endswith(".jpg")|url.endswith(".png")|url.endswith(".gif") else 'application/octet-stream'
           
        if 'getlibrary' in params and params['getlibrary']: #access datafiles from external directories
            filename = params['file'] if 'file' in params else 'meta.txt'
            if 'child' in params: #check requested ID
                url = os.path.join(getlibrary(uid=userid,jobid=params['child']), filename)
                if userid: #add shared ID to library
                    md = Metadata(librarypath(userid))
                    idlist = md['shared'] or [] 
                    if params['getlibrary'] not in idlist: md.update({'shared':idlist+[params['getlibrary']]})
            url = os.path.join(getlibrary(uid=userid,jobid=params['getlibrary']), filename)
            root = datadir
        elif 'file' in params and local: #local wasabi installation permits unrestricted file reading
            url = params['file']
            filename = os.path.basename(url)
            root = 'skip'
        elif 'getexport' in params:
            url = joinp(exportdir, params['getexport'], d=exportdir)
            filename = params['getexport']
            root = exportdir
        else: root = wasabidir
            
        try:    
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
    
    #send summary of entire analysis library
    def post_getlibrary(self, form, userid):
        rootlevel = userid or os.path.basename(datadir)
        metadata = []
        for path in librarypaths(rootlevel,inclroot=True):
            md = getmeta(path,rootlevel)
            if(md['id'] == rootlevel): md['parentid'] = ''
            if md['shared']: #add shared analyses/folders
                metadata += [str(getmeta(spath,libdirs[sid]['parent'],md['parentid'])) for sid in md['shared'] for spath in librarypaths(sid,True)]
                del md['shared']
            if(md['id'] != rootlevel): metadata.append(str(md))
        rootmd = Metadata(getlibrary(jobid=rootlevel))
        self.sendOK()
        self.wfile.write('['+','.join(metadata)+']')

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
        if val: store[key] = val
  
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
        emptyfolder = True if action=='save' and 'file' not in form else False
        
        logging.debug("%s: userid=%s parentid=%s currentid=%s writemode=%s" % (action, userid, parentid, currentid, writemode))
        
        if(writemode=='child' or writemode=='sibling'):  #create a child job
            if writemode=='child': parentid = currentid
            odir = create_job_dir(d=getlibrary(jobid=parentid, uid=userid, checkowner=True), uid=userid, newfolder=emptyfolder)
        elif(writemode=='overwrite' and currentid):  #rerun of job, use same directory
            odir = getlibrary(jobid=currentid, uid=userid, checkowner=True)
        else: odir = create_job_dir(uid=userid, newfolder=emptyfolder)  #create new top-level job directory
        
        jobid = os.path.basename(odir)
        response = {"id":jobid}

        #store form info to metadata file
        importdata = {}
        for p in ["idnames","ensinfo","nodeinfo","visiblecols"]: self._add_if_present(importdata,form,p)
        if len(importdata):
            importmd = Metadata(jobid, filename="importmeta.txt", uid=userid)
            importmd.update(importdata)
        
        metadata = Metadata(jobid, uid=userid)
        if action == 'startalign': #start new alignment job
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
            for p in ["name","source","parameters"]: self._add_if_present(metadata,form,p)
            if 'file' in form:
                filename = form.getvalue('filename','saved.xml')
                savefile = write_file(os.path.join(odir,filename), form.getvalue('file',''))
                metadata["savetime"] = str(time.time())
                response["outfile"] = metadata["outfile"] = filename
            metadata.flush()

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
        logfile = open(os.path.join(odir,logfilename), 'wb')
        
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
        if(userid and userid!=librarypath(jobid,True)): raise IOError(404,'Permission denied')
        key = form.getvalue('key', 'imported')
        value = form.getvalue('value', str(time.time()))
        try :
            md = Metadata(jobid, uid=userid)
            md[key] = value
            md.flush()
            self.sendOK()
            self.wfile.write('['+str(md)+']')
        except MetadataError as why :
            self.sendError(501, 'Metadata write error: %s' % why)
    
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

    #remove data dir from library
    def post_rmdir(self, form, userid):
        global job_queue
        jobid = form.getvalue('id','')
        if(not jobid): raise IOError(404,'No jobID given')
        
        if(userid and userid!=librarypath(jobid,True)): #remove shared ID
            md = Metadata(jobid)
            if md['shared']: md['shared'].remove(jobid)
            md.flush()
        else: #remove real dir
            job_queue.terminate(jobid)
            shutil.rmtree(apath(getlibrary(jobid=jobid),d=datadir)) #check for valid library path
            maplibrary(userid)
        self.sendOK('Deleted')
        
    #move/copy data in library
    def post_movedir(self, form, userid):
        jobid = form.getvalue('id','')
        parentid = form.getvalue('parentid','')
        targetid = form.getvalue('target','')
        duplicate = form.getvalue('copy','')
        if(not jobid or not targetid): raise IOError(404,'Source or target ID not given')
        if(userid and userid!=librarypath(targetid,True)): raise IOError(404,'Permission denied')
        sourcepath = librarypath(jobid)
        targetpath = librarypath(targetid)
        if(userid and userid!=librarypath(jobid,True)): #move shared dir
            if parentid and not duplicate:
                md = Metadata(parentid)
                if md['shared']: md['shared'].remove(parentid)
                md.flush()
            md2 = Metadata(targetid)
            idlist = md2['shared'] or []
            idlist.append(jobid)
            md2.update({'shared':idlist})
        else: #move real dir
            if duplicate: shutil.copytree(sourcepath, os.path.join(targetpath,jobid))
            else: shutil.move(sourcepath, targetpath)
            maplibrary(userid)
        self.sendOK('Done')
             
         

    #kill a running job
    def post_terminate(self, form, userid):
        global job_queue
        jobid = form.getvalue('id','')
        if(not jobid): raise IOError(404,'No jobID given')
        if(userid and userid!=librarypath(jobid,True)): raise IOError(404,'Permission denied')
        
        job_queue.terminate(jobid)
        md = Metadata(jobid) #check result
        if(md['status']=='queued' or md['status']=='running'):
            md.update({'status':'-15'})
        
        self.sendOK('Terminated')

    #write exported file to disk and send download link
    def post_makefile(self, form, userid):
        global exportdir
        filename = form.getvalue('filename','exported_data.txt')
        filepath = joinp(exportdir, filename, d=exportdir, uid=userid)
        if(os.path.isfile(filepath)):
            filepath += '_'+len(os.listdir(exportdir))
        filedata = form.getvalue('filedata','')
        exportfile = open(filepath,'wb')
        exportfile.write(filedata)
        self.sendOK()
        self.wfile.write(userid+'?type=binary&getexport='+os.path.basename(filepath))
        
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
                if(not userid or userid not in libdirs) :
                    raise IOError(404,'Post '+action+' => Invalid user ID "'+userid)
                    
            getattr(self, "post_%s" % action)(form, userid)
            
        except IOError as e:
            if hasattr(e, 'reason'): self.sendError(404,"URL does not exist. %s" % e.reason, action)
            else: self.sendError(404, str(e), action)
        except shutil.Error as why:
            self.sendError(501,"File operation failed: %s" %why)
        except OSError as e:
            self.sendError(501,"System error. %s" % e.strerror, action)
        except AttributeError as e:
            self.sendError(501, "Invalid POST request. %s" % str(e), action)
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

        if not os.path.exists(self.md_file):
            self.create(self.jobdir, filename)
            #raise MetadataError("File not found: %s" % self.md_file)
            
        try:
            self.metadata = json.load(open(self.md_file))
        except ValueError as why:
            os.rename(self.md_file,self.md_file+".corrupted")
            logging.error("Renamed corrupt metadata file: "+self.md_file)

    def __getitem__(self, key) :
        try: return self.metadata[key]
        except KeyError:
            #logging.error('"'+key+'" not found in metadata!')
            return False
    
    def __setitem__(self, key, value) :
        self.metadata[key] = value
    
    def __delitem__(self, key):
        del self.metadata[key]
    
    def __len__(self):
        return len(self.metadata)
    
    def __iter__(self):
        return iter(self.metadata)
    
    def __str__(self) :
        return json.dumps(self.metadata)
    
    def update(self, data) :
        for k in data :
            self.metadata[k] = data[k]
        self.flush()
    
    def flush(self) :
        f = tempfile.NamedTemporaryFile(suffix=os.path.basename(self.md_file), prefix='', dir=self.jobdir, delete=False)
        json.dump(self.metadata, f, indent=2)
        f.close()
        os.rename(f.name, self.md_file)
    
    def update_log(self) :
        if(self['logfile']):
            self['log'] = self.last_log_line(self['logfile'])
            self['lasttime'] = os.stat(os.path.join(self.jobdir,self['logfile'])).st_mtime
        elif(not self['imported']):
            self.update({'imported':str(time.time())})
    
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
    def create(dpath, filename="meta.txt", name="unnamed", imported="") :
        f = open(joinp(dpath, filename), 'wb')
        curtime = str(time.time())
        if imported: imported = curtime
        f.write('{"id":"'+os.path.basename(dpath)+'"')
        if filename == "meta.txt":
            f.write(', "imported":"'+imported+'", "outfile":"", "starttime":"'+curtime+'", "name":"'+name+'"')
        f.write('}')
        f.close()
        return Metadata(dpath, filename)

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
        md.update({'status':self.status()})
    
    def end(self, rc) :
        self.endtime = time.time()
        
        if rc == 0 :
            self.set_status(Job.SUCCESS)
        else :
            self.set_status(Job.FAIL)
            self.states[Job.FAIL] = str(rc)
    
        md = Metadata(self.jobid())
        md.update(self.json())
    
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
    
    #select the correct Prank output file for import
    def _reset_results_file(self):
        out = self.files['outfile']
        for ver in ['.best','.2','.1','.0','']:
            for trans in ['.nuc','','.pep']:
                outfile = out+ver+trans+'.xml'
                if os.path.isfile(outfile):
                    self.files['outfile'] = outfile
                    return

    def process(self):
        self.lock_status()

        if self.job_status == Job.TERMINATED:
            self.unlock_status()
            return

        self.begin()

        logfile = open(self.files['logfile'], 'wb')
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

    info('Starting server...\n') #start task queue
    job_queue = WorkQueue(num_workers)
    job_queue.start()
    maplibrary() #build library index

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

