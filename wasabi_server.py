#!/usr/bin/env python
#coding: utf-8

# Back-end server for Wasabi web application (http://wasabiapp.org). Compatible with Python 2.7 and Python 3+
# Copyright Andres Veidenberg (andres.veidenberg{at}helsinki.fi) and Alan Medlar, University of Helsinki (2015)
# Distributed under AGPL license (http://www.gnu.org/licenses/agpl)

import argparse
import cgi

try:
    import configparser  #if python 3
except ImportError:
    import ConfigParser as configparser  #rename for python 2 compatibility
from glob import glob
import json
import logging
import logging.handlers
import multiprocessing
import os
try:
    import queue  #python 3
except ImportError:
    import Queue as queue  #python 2
import random
import re
import resource
import shutil
import smtplib
import socket
import string
import subprocess
import sys
import tempfile
import threading
import time
import traceback
try:  #python 3
    from urllib.request import urlopen
    from urllib.parse import unquote
    from urllib.error import URLError
except ImportError:  #python 2
    from urllib import unquote, urlopen
    from urllib2 import URLError
import webbrowser
import zipfile
try:  #python 3
    from http.server import BaseHTTPRequestHandler, HTTPServer
    from socketserver import ThreadingMixIn
except ImportError:  #python 2
    from BaseHTTPServer import BaseHTTPRequestHandler, HTTPServer
    from SocketServer import ThreadingMixIn


#define some globals
version = 190115
wasabiexec = os.path.realpath(__file__)
appdir = os.path.dirname(wasabiexec) #get wasabi homedir
wasabidir = os.path.realpath(os.path.join(appdir,os.pardir))
osxbundle = False
if(os.path.isfile(os.path.join(appdir,'AppSettings.plist'))):
    wasabidir = os.path.realpath(os.path.join(wasabidir,'..','..')) #OSX bundle path
    osxbundle = True
os.chdir(wasabidir)
#for tracking library content
job_queue = None
libdirs = {}
datestamp = '' #last cleanup date

def getconf(opt='',vtype=''): #parse conf file values
    try:
        if(vtype=='int'): return config.getint('server_settings',opt)
        elif(vtype=='bool'): return config.getboolean('server_settings',opt)
        else:
            val = config.get('server_settings',opt)
            return '' if(vtype=='file' and '.' not in val) else val
    except configparser.Error: return 0 if(vtype=='int') else ''

#Initialize: read/create settings and work folders
config = configparser.ConfigParser()
defaultsettings = os.path.join(appdir,'default_settings.cfg')
config.read(defaultsettings)
dataroot = os.path.realpath(getconf('datadir') or 'wasabi_data')
if not os.path.exists(dataroot): os.makedirs(dataroot, 0o775)
settingsfile = os.path.join(dataroot,'wasabi_settings.cfg')
if not os.path.isfile(settingsfile):
    try:
        shutil.copy(defaultsettings, settingsfile)
        try: os.chmod(defaultsettings, 0o664)
        except (OSError, IOError): pass
    except (OSError, IOError) as why: print("Setup error: Could not create settings file: "+str(why))
else: config.read(settingsfile)
datadir = os.path.join(dataroot,'analyses')
if not os.path.exists(datadir):
    os.makedirs(datadir, 0o775)
    try: shutil.copytree(os.path.join(appdir,'example'), os.path.join(datadir,'example'))
    except (OSError, IOError) as why: print("Setup error: Could not create analysis library directory: "+str(why))
sys.stdout.flush()
exportdir = os.path.join(dataroot,'exports')
if not os.path.exists(exportdir): os.makedirs(exportdir, 0o775)
plugindir = os.path.realpath(os.path.join(appdir, (getconf('plugindir') or 'plugins')))
if not os.path.exists(plugindir): os.makedirs(plugindir, 0o775)
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
userexpire = getconf('userexpire','int') or ''
userlog = os.path.join(datadir,'user.log')
userheader = ''
linuxdesktop = getconf('linuxdesktop','bool')
urldomain = getconf('urldomain') or ''
hostname = getconf('hostname') or ''

#set up logging
class TimedFileHandler(logging.handlers.TimedRotatingFileHandler):
    def _open(self):
        gwmask = os.umask(0o002) #make logfile group writable
        fstream = logging.handlers.TimedRotatingFileHandler._open(self)
        os.umask(gwmask)
        return fstream

def start_logging():
    if logtofile:
        loghandler = TimedFileHandler(os.path.join(dataroot,'server.log'), when='d', interval=1, backupCount=1)
    else:
        loghandler = logging.StreamHandler()
    loglevel = logging.DEBUG if(debug) else logging.INFO
    loghandler.setLevel(loglevel)
    loghandler.setFormatter(logging.Formatter('%(asctime)s - %(message)s', '%d.%m.%y %H:%M:%S'))
    logging.getLogger().setLevel(loglevel)
    logging.getLogger().addHandler(loghandler)

    global userlog
    if useraccounts:
        try:
            open(userlog,'wb').close()
            try: os.chmod(userlog, 0o664)
            except (OSError, IOError): pass
        except (OSError, IOError) as why:
            logging.error('Setup error: Could not access user log file: '+str(why))
            userlog = False

#create linux shortcut
if(sys.platform.startswith('linux') and linuxdesktop):
    try:
        deskfile = os.path.join(appdir,'wasabi.desktop')
        deskconf = configparser.ConfigParser()
        deskconf.optionxform = str
        deskconf.read(deskfile)
        if(deskconf.get('Desktop Entry','Exec') is not wasabiexec):
            deskconf.set('Desktop Entry','Exec',wasabiexec)
            deskconf.set('Desktop Entry','Icon',os.path.join(appdir,'images','icon.png'))
            with open(deskfile,'wb') as fhandle: deskconf.write(fhandle)
            shutil.copy(deskfile, os.path.expanduser('~/Desktop'))
    except (configparser.Error, shutil.Error, OSError, IOError) as why: print('Setup error: Could not create Linux desktop shortcut: '+str(why))

#change to directory to be served (for GET requests)
os.chdir(appdir)
    
def apath(path, d=wasabidir, uid=''): #check if filepath is in wasabi sandbox
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

def write_file(filepath, filedata='', checkdata=False):
    if(checkdata and not filedata):
        return False
    else:
        f = open(filepath, 'wb')
        f.write(filedata)
        f.close()
        return os.path.basename(f.name)


def maplibrary(rootid='', remove=False): #index library directories
    ''' Result: libdirs = {analysisID:{parent:parentId, children:[childID,..]}, ..} (for userIDs, parent="analyses") '''
    global libdirs

    def getkids(libid): #flatten librarytree
        kidarr = [libid]
        for kidid in libdirs[libid]['children']:
            kidarr = kidarr + getkids(kidid)
        return kidarr

    if(rootid and rootid in libdirs): #partial remap
        libroot = getlibrary(jobid=rootid)
        for oldid in getkids(rootid):
            try: del libdirs[oldid]
            except KeyError: pass
        if remove:
            del libdirs[rootid]
            return
    else: #full remap
        libroot = datadir
        libdirs = {}
    
    for (dirpath,dirs,files) in os.walk(libroot, topdown=True):
        path = dirpath.split(os.path.sep)
        if('meta.txt' in files): #index an analysis id
            libdirs[path[-1]] = {'parent':path[-2], 'children':[]}
            if(path[-2] in libdirs): libdirs[path[-2]]['children'].append(path[-1])
        else: del dirs[:] #skip subtree indexing
            
    if useraccounts: #remove the entry for analysis root folder (has meta.txt)
        try: del libdirs[os.path.basename(datadir)]
        except KeyError: pass


def librarypath(jobid, getroot=False): #analysis ID => absolute path
    ''' Returns absolute_path/analyses/userID/childID/.../jobID or userID (getroot=True)'''
    if(jobid not in libdirs): raise IOError(404, "Invalid library ID: "+jobid)
    libpath = jobid
    while jobid in libdirs:
        libpath = libdirs[jobid]['parent']+os.path.sep+libpath #build analysis path bottom-up
        jobid = libdirs[jobid]['parent']
    if getroot: return libpath.split(os.path.sep)[1] #return just userID  (from ['analyses', userID, childID, .., jobID])
    rootpath = os.path.dirname(datadir)
    if not useraccounts: rootpath = os.path.dirname(rootpath) #libpath=datadir/...
    dirpath = os.path.join(rootpath,libpath)
    return dirpath


def librarypaths(libraryid, inclroot=False): #get all subfolder paths
    dirpaths = [librarypath(libraryid)] if inclroot else []
    if libraryid in libdirs: #valid ID
        for childid in libdirs[libraryid]['children']:
            if childid in libdirs:
                dirpaths.append(librarypath(childid))
                dirpaths += librarypaths(childid)
            else:
                logging.error("Invalid analysis ID "+childid+" found in "+librarypath(libraryid))
    return dirpaths


def getlibrary(jobid='', uid='', checkowner=False):
    ''' Traverse analyses library. Return a path of analysis (jobid) or list paths of all user (uid) analyses. '''
    if os.path.isabs(jobid): return jobid
    if jobid: #return a directory path
        if(jobid==uid): return librarypath(uid)
        if(uid and checkowner and uid!=librarypath(jobid,True)): raise IOError(404,'Access denied to analysis ID '+jobid)
        if(jobid not in libdirs): maplibrary() #remap and try again
        if(jobid not in libdirs): raise IOError(404, "Getlib: Invalid library ID: "+jobid)
        return librarypath(jobid)
    else: return librarypaths(uid or os.path.basename(datadir)) #return all library paths


def getmeta(dirpath, rootlevel, shareroot=None): #get processed metadata
    md = Metadata(dirpath)
    if('status' in md and not md['imported']): #running job
        md.update_log()
    else:  #library item
        if(not md['imported']): md.update('imported', time.time())
        dirid = md['id'] or os.path.basename(dirpath)
        md['parentid'] = "" if libdirs[dirid]['parent'] == rootlevel else libdirs[dirid]['parent']
        md['children'] = len(libdirs[dirid]['children'])
        if 'shared' in md and shareroot is None: #check validity of shared IDs in the library folder
            idlist = [id for id in md['shared'] if id in libdirs]
            if len(idlist) is not len(md['shared']): md["shared"] = md.update({"shared": idlist})
            md['children'] += len(idlist)
        elif shareroot is not None: #analysis in a shared folder; mark as shared
            if not md['parentid']: md['parentid'] = shareroot
            md['shared'] = "true"
    return md

def sendmail(subj='Email from Wasabi', msg='Empty message (sent by error)', to=''):
    if not gmail: return 'Failed: no gmail user'
    global hostname
    #add Wasabi footer
    msg += '\r\n\r\n-------------------------------------------------\r\n'
    msg += 'Wasabi is a web application for phylogenetic sequence analysis.\r\n'
    msg += 'You can learn more about Wasabi from http://wasabiapp.org\r\n\r\n'
    #get email from user account
    if(to and '@' not in to and to in libdirs):
        userID = librarypath(to, True)
        to = Metadata(userID)['email']
        msg += 'This message was sent to the e-mail address registered in Wasabi app.\r\n\r\n'
        if(hostname): msg += 'You can use your Wasabi account at http://'+hostname+'/'+userID+'\r\n\r\n'
    #send the message
    guser, gpass = gmail.split(':')
    if '@' not in guser: guser += '@gmail.com'
    if guser and gpass and '@' in to:
        try:
            gserver = smtplib.SMTP('smtp.gmail.com:587')
            gserver.ehlo()
            gserver.starttls()
            gserver.login(guser,gpass)
            mailstr = '\r\n'.join(['From: '+guser, 'To: '+to, 'Subject: '+subj, '', msg])
            gserver.sendmail(guser, [to], mailstr)
            gserver.quit()
            return 'Sent'
        except: raise
    else: return 'Failed'

def cleanup(): #remove obseolete user accounts (library files)
    today = time.strftime("%d%m%y")
    global datestamp #last cleanup
    global hostname
    if userexpire and useraccounts and datestamp is not today: #max. 1 cleanup/day
        try:
            for dname in os.listdir(datadir):
                dpath = os.path.join(datadir,dname)
                fpath = os.path.join(dpath,'meta.txt')
                if(not os.path.isdir(dpath) or not os.path.isfile(fpath)): continue
                usermd = Metadata(dpath)
                if(usermd['keepAccount']): continue #skip flagged accounts
                lasttime = os.path.getmtime(fpath)
                dirage = (time.time()-lasttime)//86400 #time in seconds => days
                tmpuserage = int((time.time()-int(usermd['tmpAccount']))//86400) if usermd['tmpAccount'] else 0
                if(dirage > userexpire or tmpuserage): #remove expired user account
                    jdirs = len(sum([trio[1] for trio in os.walk(dpath)],[])) #len(flattened list of subdir lists)
                    shutil.rmtree(apath(dpath,datadir,uid='skip'))
                    info('Cleanup: removed account %s (%s analyses, last visit %s days ago)' % (dname, jdirs, int(dirage)))
                elif(dirage == userexpire-10 and  usermd['email'] and gmail): #send warning email
                    msg = 'Your Wasabi account and anlysis library expires in 10 days due to inactivity.\r\n'
                    msg += 'You can postpone the expiry date by %s days by visiting you account page: http://%s/%s' % (userexpire, hostname, dname)
                    msg += '\r\nYou can ingore this message to have the account data deleted on expiry date.'
                    sendmail('Wasabi account about to expire', msg, usermd['id'])
            datestamp = today
        except (OSError, IOError) as why: logging.error('Library cleanup failed: '+str(why))


def create_job_dir(d='', uid='', newlibrary=False, metadata={}):
    if(not d):
        d = datadir
        if(useraccounts):
            if(not uid or uid not in libdirs): newlibrary = True
            else: d = librarypath(uid)  
    
    newdir = tempfile.mkdtemp(prefix='', dir=d)
    while(os.path.basename(newdir) in libdirs): #ensure unique ID
        os.rmdir(newdir)
        newdir = tempfile.mkdtemp(prefix='', dir=d)
    os.chmod(newdir, 0o775)
    uid = os.path.basename(newdir)
    
    if(newlibrary): #create library root folder for a new user
        md = Metadata.create(newdir, name="Wasabi user account", imported=True)
        cleanup() #check and remove neglected accounts
    else: #create empty analysis folder
        md = Metadata.create(newdir)
    if(md and metadata): md.update(metadata)
    maplibrary(uid)
    return newdir

def change_ids(d='', uid='', newdate=True): #replace IDs of library item(s)
    if(not d or d==datadir): raise OSError(501, "No path given for ID change")
    names = tempfile._RandomNameSequence()  #random ID generator
    newids = []
    for (dirpath,dirs,files) in os.walk(d,followlinks=False,topdown=False):
        newid = next(names)
        while(newid in libdirs): newid = next(names) #pick unique ID
        try:
            newpath = os.path.join(os.path.dirname(dirpath),newid)
            os.rename(dirpath, newpath)
            md = Metadata(newpath)
            md.update("id", newid)
            t = time.time()
            if newdate: md.update({"created":t,"saved":t,"imported":"never"})
            if('importmeta.txt' in files):
                md = Metadata(newpath, filename='importmeta.txt')
                md.update("id", newid)
        except (OSError, IOError) as why: raise OSError(501, "ID renaming failed for %s (%s)" % dirpath,why)
        newids.append(newid)
    return newids

def check_id(form, userid=''): #user-supplied library ID validity check
    jobid = form.getvalue('id', '')
    if(not jobid): raise IOError(404, 'No analysis ID given')
    if(userid and userid!=librarypath(jobid,True)): raise IOError(404, 'Access denied for analysis '+jobid)
    return jobid


def info(msg): logging.info(msg)

def getsize(start_path = '.'): #get total filesize of a dirpath
    total_size = 0
    for dirpath, dirnames, filenames in os.walk(start_path):
        for f in filenames:
            fp = os.path.join(dirpath, f)
            try: total_size += os.path.getsize(fp)
            except OSError: pass
    return total_size

#class to handle Wasabi server<=>browser communication
class WasabiServer(BaseHTTPRequestHandler):
    def log_message(self, format, *args):
        return #disable console printout of server events

    #send error response (and log error details)
    def sendError(self, errno=404, msg='', action='', skiplog=False): #log the error and send it to client browser
        if(not skiplog):
            logging.error('Error: request "'+action+'" => '+str(errno)+': '+msg)
            if(debug and action!='GET'): logging.exception('Error details: ')
        if(msg[0]!='{'): msg = '{"error":"'+msg+'"}' #add json padding
        if hasattr(self, 'callback'): #send as jsonp
            msg = self.callback+'('+msg+')'
            self.command = 'HEAD' #do custom HTML text (jsonp)
            self.send_error(errno)
            self.wfile.write(msg)
        else:
            self.send_error(errno, msg)

    #send OK response (status:200)
    def sendOK(self, msg='', size=0):
        self.send_response(200)
        if size:
            self.send_header("Content-Type", "text/octet-stream")
            self.send_header("Content-Length", str(size))
            self.send_header("Cache-Control", "no-cache")
        else: self.send_header("Content-Type", "text/plain")
        self.end_headers()
        if msg:
            if hasattr(self, 'callback'): #add jsonp padding
                if(msg[0]!='{' and msg[0]!='['): msg = '{"data":"'+msg+'"}' #plaintext=>json
                msg = self.callback+'('+msg+')'
            self.wfile.write(msg)

    #HEAD requests
    def do_HEAD(self):
        try:
            self.send_response(200)
            self.end_headers()
            self.wfile.write('URL exists')
            return  
        except IOError:
            self.sendError(404,'File Not Found: %s' % self.path,'HEAD')

    #serve files (GET requests)
    def do_GET(self):
        url = unquote(self.path)
        urldir = ''
        params = {}
        filecontent = ''
        userid = ''
        filename = ''
        
        if url.startswith("/"): url = url[1:]
        if url.endswith("/"): url += "index.html"
        
        if('?' in url):
            urlarr = url.split('?')
            url = urlarr[0]
            params = dict([x.split('=') for x in urlarr[1].split('&')])
            logging.debug("Get: %s %s" % (userid, str(params))) 
        
        if("." not in url and "/" not in url):
            if(url in libdirs): userid = url #check user ID
            url = "index.html"
        
        if 'type' in params:
            ctype = 'text/plain' if('text' in params['type']) else 'application/octet-stream'
        elif 'callback' in params:
            ctype = 'application/json' #jsonp requested
        elif url.endswith(".html") or url.endswith(".css") or url.endswith(".js"): #send as text
            ctype = 'text/css' if url.endswith(".css") else 'text/javascript' if url.endswith(".js") else 'text/html'
        else: #send as binary
            ctype = 'image' if url.endswith(".jpg")|url.endswith(".png")|url.endswith(".gif") else 'application/octet-stream'
        
        if 'callback' in params: self.callback = params['callback']
        
        logfile = False
        try:
            checkroot = wasabidir
            if 'getanalysis' in params and params['getanalysis']: #access datafiles from analysis library
                filename = params['file'] if 'file' in params else 'meta.txt'
                md = Metadata(params['getanalysis'])  #throws error for invalid ID
                if('logfile' in md and md['logfile']==filename): logfile = True  #logfile requested
                if('dir' in params and params['dir']) or 'folder' in md.metadata: #analysis folder/tree
                    if('dir' in params):  #analysis subtree access via child ID. check validity
                        if params['getanalysis'] not in librarypath(params['dir']): raise IOError(404, "Child check: Invalid analysis ID: "+params['dir'])
                    if userid: #has useraccount: add the requested analysis to user library (as shared analysis)
                        md = Metadata(librarypath(userid))
                        idlist = md['shared'] or []
                        isowner = librarypath(params['getanalysis'], getroot=True) == userid #check if already in library
                        if not isowner and params['getanalysis'] not in idlist: md.update({'shared': idlist+[params['getanalysis']]})
                url = os.path.join(librarypath(params['getanalysis']), filename)
                checkroot = datadir
            elif 'getlibrary' in params: #(shared) analysis library content via GET
                self.post_getlibrary(None, params['getlibrary'])
                return
            elif 'getdir' in params: #analysis folder filelist
                self.post_getdir(None, params['getdir'])
                return
            elif 'checkserver' in params:
                self.post_checkserver(None, userid)
                return
            elif 'checkuser' in params:
                self.post_checkuser(None, userid)
                return
            elif 'maplibrary' in params:
                if(not userid):
                    self.sendError(msg="GET maplibrary: userid missing")
                else:
                    maplibrary(None, userid)
                    self.sendOK('{"status":"library cache updated"}')
                return
            elif 'debug' in params:
                if(not userid):
                    self.sendError(msg="GET debug: (admin)userid missing")
                else:
                    self.post_debug(None, userid)
                return
            elif 'getexport' in params:
                filename = params['getexport']
                url = os.path.join(exportdir, filename)
                filename = filename.split('/')[1]
                checkroot = exportdir
            elif 'plugin' in params: #get a file from the plugins folder
                if 'file' in params:
                    filename = params['file']
                    plugin = params['plugin']
                else:
                    filename = os.path.basename(params['plugin'])
                    plugin = os.path.dirname(params['plugin'])
                url = os.path.join(plugindir, plugin, filename)
            elif 'file' in params and local: #local wasabi installation permits unrestricted file reading
                url = params['file']
                filename = os.path.basename(url)
                checkroot = 'skip'
            
            f = open(apath(url, checkroot)) if 'text' in ctype else open(apath(url, checkroot),'rb') #includes symlink check
            filecontent = f.read()
            f.close()
            if(logfile): filecontent = filecontent.replace(librarypath(params['getanalysis']),'analysisPath') #mask librarypaths in logfile
            if 'callback' in params: #add jsonp padding
                filecontent = filecontent.replace('\n','').replace('\r','').replace('\t','')
                if(filecontent[0]!='{' and filecontent[0]!='['): filecontent = '{"filedata":"'+filecontent.replace('"','\'')+'"}' #textfile=>json
                filecontent = params['callback']+"("+filecontent+")"
                filename = ''
            self.send_response(200)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", len(filecontent))
            if(ctype == 'image'): self.send_header("Cache-Control", "max-age=300000")
            if(filename): self.send_header("Content-Disposition", "attachment; filename="+filename) #file download
            self.end_headers()
            self.wfile.write(filecontent)
        except IOError as e:
            errmsg = 'File Not Found: %s (%s)' % (url, e.strerror)
            if('getanalysis' in params): errmsg = errmsg.replace(librarypath(params['getanalysis']),'analysisPath') #mask librarypaths 
            self.sendError(404, errmsg, 'GET', filename=='importmeta.txt')


#======POST request functions========

    #send server status
    def post_checkserver(self, form, userid=''):
        status = {"status":"OK"}
        if(useraccounts):
            status["useraccounts"] = userexpire or "yes"
            if(userid and userid in libdirs): status["userid"] = userid
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
        if(datalimit): status["datalimit"] = datalimit
        os.chdir(plugindir)
        status["plugins"] = glob('*.json') + glob('*'+os.sep+'*.json')
        os.chdir(appdir)
        self.sendOK(json.dumps(status))

    #send user account metadata
    def post_checkuser(self, form, userid):
        if(not userid or userid not in libdirs): raise IOError(404, 'UserID '+userid+' does not exist.')
        md = Metadata(userid)
        md.update("updated", time.time()) #timestamp last visit
        if(datalimit): md["datause"] = getsize(joinp(datadir, userid, uid='skip'))
        self.sendOK(str(md))

    #create new user
    def post_createuser(self, form, userid=''):
        global hostname
        hostname = self.headers.get('Host') #update
        sharelist = ['example']
        addid = form.getvalue('addshared','')
        tmpuser = time.time() if form.getvalue('tmpuser','') else None
        if addid and addid in libdirs: sharelist.append(addid)
        newmeta = {'username':form.getvalue('username','anonymous'), 'email':form.getvalue('email',''), 'shared':sharelist, 'tmpAccount':tmpuser}
        userid = os.path.basename(create_job_dir(newlibrary=True, metadata=newmeta)) #create new user
        userexpire = ', "userexpire":1' if tmpuser else ''
        self.sendOK('{"userid":"'+userid+'"'+userexpire+'}')

    #send summary of entire analysis library
    def post_getlibrary(self, form, userid):
        rootlevel = userid or os.path.basename(datadir)
        sharedir = bool(userid and libdirs[userid]['parent']!=os.path.basename(datadir)) #non-owner userid: send as shared dir
        metadata = []
        for path in librarypaths(rootlevel, inclroot=True):
            md = getmeta(path, rootlevel)
            if(md['id'] == rootlevel and not sharedir): md['id'] = ''
            if 'shared' in md.metadata: #add shared analyses/folders
                if md['shared']: #fill in metadata for each ID in shared[]
                    metadata += [str(getmeta(spath, libdirs[sid]['parent'], md['id'])) for sid in md['shared'] for spath in librarypaths(sid,True)]
                del md['shared'] #remove idarr from shared rootfolder in senddata
            if(sharedir): md['shared'] = "true"
            if(md['id']): metadata.append(str(md))
        self.sendOK('['+','.join(metadata)+']')

    #reflect uploaded file
    def post_echofile(self, form, userid):
        self.sendOK(form.getvalue('upfile'))

    #forward remote file
    def post_geturl(self, form, userid):
        global urldomain
        url = form.getvalue('fileurl','')
        if(urldomain and urldomain not in url):
            raise IOError(404, 'Downloads restricted to '+urldomain)
        try:
            urlfile = urlopen(url)
            fsize = int(urlfile.info().getheaders("Content-Length")[0])
            self.sendOK(urlfile.read(), fsize)
        except (ValueError, URLError) as e:
            raise IOError(404, e.reason or 'Invalid URL: '+url)

    #store form fields
    def _add_if_present(self, store, form, key):
        val = form.getvalue(key,'')
        if val:
            try: store[key] = json.loads(val)
            except ValueError: store[key] = val

    #save files to libary
    def post_save(self, form, userid):
        self.post_startalign_save(form, 'save', userid)

    #make new folder to libary
    def post_newdir(self, form, userid):
        self.post_run_save(form, 'save', userid)

    #start new background job
    def post_run(self, form, userid):
        self.post_run_save(form, 'run', userid)
    
    #write datafiles to library (and start a job)
    def post_run_save(self, form, action, userid):

        currentid = form.getvalue('id','')
        writemode = form.getvalue('writemode','new') #writemode=>target path in library
        jobname = form.getvalue('name','untitled')
        response = {}
        #set the target analysis folder
        if(currentid and (currentid not in libdirs)): raise IOError(404, 'Invalid analysis ID: '+currentid)
        if(not currentid or currentid==userid): writemode = 'new'
        if(userid and (userid not in libdirs)): raise IOError(404, 'Invalid userID: '+userid) 
        if(useraccounts and not userid): #create a new user if needed
            userid = os.path.basename(create_job_dir(newlibrary=True))
            response["userid"] = userid=''
            
        newu = "(new)" if "userid" in response else ""
        logging.debug("%s: userid=%s %s currentid=%s writemode=%s" % (action, userid, newu, currentid, writemode))

        if(writemode=='child' or writemode=='sibling'):  #add dir to existing analysis
            parentdir = getlibrary(jobid=currentid, uid=userid, checkowner=True)
            if(writemode=='sibling'): parentdir = os.path.dirname(parentdir)
            odir = create_job_dir(d=parentdir, uid=userid)
        elif(writemode=='overwrite'):  #use existing analysis dir
            odir = getlibrary(jobid=currentid, uid=userid, checkowner=True)
            try: os.remove(os.path.join(odir,"importmeta.txt"))
            except OSError: pass
        else: odir = create_job_dir(uid=userid)  #create new root analysis

        firstid = jobid = os.path.basename(odir)
        response["id"] = jobid

        #store metadata for the input dataset from Wasabi
        importdata = {}
        for p in ["idnames","ensinfo","nodeinfo","visiblecols","settings"]: self._add_if_present(importdata, form, p)
        if len(importdata):
            Metadata(jobid, filename="importmeta.txt", uid=userid).update(importdata)

        meta = Metadata(jobid, uid=userid) #store job info
        if action == 'run': #start new background job/pipeline
            pipeline = json.loads(form.getvalue('pipeline','[]'))
            for i, data in enumerate(pipeline, 1): #prepare pipeline files (i=1..len)
                if(i>1): #init datafolder for the new job step
                    previd = jobid
                    odir = create_job_dir(d=odir, uid=userid)
                    jobid = os.path.basename(odir)
                    Metadata(previd, uid=userid).update('nextstep',jobid) #link previous=>this step
                    meta = Metadata(jobid, uid=userid)
                if(len(pipeline)>1): meta['step'] = "%d/%d" % (i, len(pipeline))
                for attr in ['name','plugin','program','parameters','infile','outfile','logfile']:
                    meta[attr] = data[attr] #store metadata
                meta['status'] = ''
                meta.flush()
                if('idnames' in data):
                    Metadata(jobid, filename="importmeta.txt", uid=userid).update('idnames', data['idnames'])
                for filename in data['infile'].split(','): #store input files
                    write_file(os.path.join(odir, filename), form.getvalue(filename,''), True)
            Job(firstid) #start the pipeline

        elif action == 'save': #store a dataset to library
            for p in ["name","source","parameters"]: self._add_if_present(meta, form, p)
            meta["imported"] = time.time()
            if 'file' in form:
                filename = form.getvalue('filename','saved.xml')
                savefile = write_file(os.path.join(odir,filename), form.getvalue('file',''))
                meta["saved"] = time.time()
                response["outfile"] = meta["outfile"] = filename
            else:  #create new empty folder
                if("name" not in form): meta["name"] = "new collection"
                meta["folder"] = "yes"
            meta.flush()

        self.sendOK(json.dumps(response))

    #add data to job metadata file
    def post_writemeta(self, form, userid):
        jobid = check_id(form)
        key = form.getvalue('key', 'imported')
        value = form.getvalue('value', time.time() if key=='imported' else '')
        #prevent remote editing of user account quotas
        if(libdirs[jobid]['parent']=='analyses' and (key=='keepAccount' or key=='datalimit')):
           raise IOError(404, 'Access denied: cannot leverage user account '+jobid) #will be logged

        md = Metadata(jobid, uid=userid)
        md[key] = value
        md.flush()
        self.sendOK('['+str(md)+']')

    #send a library directory filelist
    def post_getdir(self, form, userid):
        dirid = form.getvalue('id', '') if form else userid
        if(not dirid or dirid not in libdirs):
            self.sendOK()
            return
        dirpath = librarypath(dirid)
        def listfiles(dirpath): #convert filetree to dict
            obj = {}
            for file in os.listdir(dirpath):
                if file.startswith("."): continue
                filepath = os.path.join(dirpath, file)
                if os.path.isdir(filepath):
                    if not os.path.isfile(os.path.join(filepath, 'meta.txt')):
                        obj[file] = listfiles(filepath) #add (non-analysis) subdir filelist
                else:
                    obj[file] = os.path.getsize(filepath)
            return obj
        self.sendOK(json.dumps(listfiles(dirpath)))

    #remove data dir from library
    def post_rmdir(self, form, userid):
        jobid = check_id(form)
        parentid = form.getvalue('parentid','')
        rootonly = form.getvalue('rootonly','')

        if(userid and userid!=librarypath(jobid,True)): #remove shared ID
            if(not parentid): parentid = userid
            md = Metadata(parentid)
            if 'shared' in md:
                md['shared'].remove(jobid)
                md.flush()
        else: #remove library dir
            job_queue.terminate(jobid)
            targetpath = apath(getlibrary(jobid=jobid),d=datadir) #check path
            parentpath = os.path.dirname(targetpath)
            if rootonly and libdirs[jobid]['children']: #not recursive: relocate children
                for childdir in next(os.walk(targetpath))[1]:
                    shutil.move(os.path.join(targetpath,childdir), parentpath)
            shutil.rmtree(targetpath) #remove library dir
            maplibrary(userid)
        self.sendOK('Deleted')

    #move/copy data in library
    def post_movedir(self, form, userid):
        jobid = check_id(form, userid)
        parentid = form.getvalue('parentid','')
        targetid = form.getvalue('target','') or userid or os.path.basename(datadir)
        duplicate = form.getvalue('copy','')
        sourcepath = librarypath(jobid)
        targetpath = librarypath(targetid)
        if(not duplicate and os.path.dirname(sourcepath)==targetpath):
            self.sendOK('{"id":"'+jobid+'"}')
            return
        if(userid and userid!=librarypath(jobid,getroot=True)): #item belongs to another user (shared analysis)
            if(not parentid): parentid = userid
            md = Metadata(parentid)
            if 'shared' in md:
                md['shared'].remove(jobid)
                md.flush()
            md2 = Metadata(targetid)
            idlist = md2['shared'] or []
            idlist.append(jobid)
            md2.update({'shared':idlist})
        else: #move/copy library dir
            if duplicate:
                jobid = next(tempfile._RandomNameSequence()) #tmp ID
                shutil.copytree(sourcepath, os.path.join(targetpath,jobid))
                try:
                    jobid = change_ids(os.path.join(targetpath,jobid))[0]
                except OSError as why: #cannot change IDs of copied data. delete copy
                    shutil.rmtree(apath(os.path.join(targetpath,jobid),d=datadir))
                    raise OSError(501, 'Failed to finish data copying: %s' % why)
            else: shutil.move(sourcepath, targetpath)
            maplibrary(userid)
        self.sendOK('{"id":"'+jobid+'"}') 

    #kill a running job
    def post_terminate(self, form, userid):
        jobid = check_id(form, userid)

        job_queue.terminate(jobid)
        md = Metadata(jobid) #check result
        if(md['status'] in (Job.QUEUED, Job.RUNNING)):
            md.update('status','-15')
        self.sendOK('Terminated')
        
    #restart a terminated job
    def post_restart(self, form, userid):
        jobid = check_id(form, userid)
        Job(jobid)
        self.sendOK('Resumed')
        

    #write exported file to disk and send download link
    def post_makefile(self, form, userid):
        global exportdir
        filename = form.getvalue('filename','exported_data.txt')
        filedir = tempfile.mkdtemp(prefix='', dir=exportdir)
        filepath = joinp(filedir, filename, d=exportdir)
        exportfile = open(filepath,'wb')
        exportfile.write(form.getvalue('filedata',''))
        self.sendOK(userid+'?type=binary&getexport='+os.path.basename(filedir)+'/'+filename)

        for dname in os.listdir(exportdir): #cleanup old files (>24h)
            dpath = os.path.join(exportdir, dname)
            if((time.time() - os.stat(dpath).st_mtime) > 86400):
                try: shutil.rmtree(dpath)
                except OSError: pass

    #save a client-sent errorlog
    def post_errorlog(self, form, userid=''):
        global datadir
        global userlog
        global userheader
        errorheader = '\n'+userid+' : '+(self.client_address[0] or '')+':\n'
        if(userheader!=errorheader): userheader = errorheader
        else: errorheader = ''
        errorlog = errorheader+form.getvalue('errorlog','')+'\n'
        if(userlog):
            with open(userlog,'a') as userlogfile: userlogfile.write(errorlog)
        self.sendOK('Done')

    #send a welcome email
    def post_sendmail(self, form, userid=''):
        global hostname
        hostname = self.headers.get('Host') #update
        to = form.getvalue('email',userid)
        url = form.getvalue('url','')
        msg = form.getvalue('msg','')
        if url:
            subj = 'Shared data from Wasabi'
            msg += '\n\rTo view the dataset that was shared with you, go to http://'+hostname+'?'+url.split('?')[-1]
        elif not msg:
            subj = 'Welcome to Wasabi'
            msg = 'You can access your analysis library in Wasabi server at http://'+hostname+'/'+userid
            if(userexpire): msg += '\r\nNote: Neglected user accounts will be deleted after '+str(userexpire)+' days of last visit.'
        st = sendmail(subj, msg, to)
        self.sendOK(st)

    #automated Wasabi update
    def post_update(self, form, userid=''):
        global osxbundle
        try:  #download update, with progress feedback
            if osxbundle: updname = 'Wasabi.dmg'
            else:
                osname = 'osx' if sys.platform.startswith('darwin') else 'windows' if sys.platform.startswith('win') else 'linux'
                updname = 'wasabi_'+osname+'.zip'
            urlfile = urlopen('http://wasabiapp.org/download/wasabi/'+updname)
            totalsize = int(urlfile.info().getheaders("Content-Length")[0]) or 18000000
            chunksize = 100*1024
            chunkcount = int(totalsize/chunksize)
            updpath = os.path.join(dataroot,updname)
            self.sendOK(size=chunkcount+28)
            with open(updpath,'wb') as downfile:
                for chunk in iter(lambda:urlfile.read(chunksize),''):
                    downfile.write(chunk)
                    self.wfile.write('#')
        except (URLError, shutil.Error) as why:
            raise IOError(404, 'Failed to download Wasabi: %s' % why)
        oldappdir = os.path.realpath(os.path.join(appdir,'..','..')) if osxbundle else appdir
        appname = os.path.basename(oldappdir)
        if(os.path.isdir(oldappdir) and os.listdir(oldappdir)):  #make a backup
            archive = os.path.join(dataroot,'backups')
            try:
                if(not os.path.isdir(archive)): os.makedirs(archive, 0o775)
                basepath, ext = os.path.splitext(oldappdir)
                safedir = basepath+str(len(os.listdir(archive)) or '')+ext
                os.rename(oldappdir,safedir)
            except OSError: pass
            shutil.move(safedir,archive)
        self.wfile.write('##########')
        if osxbundle: #extract new app from diskimage
            try: subprocess.check_output(['hdiutil','attach','-noverify','-nobrowse','-mountpoint','/Volumes/Wasabi',updpath], stderr=subprocess.STDOUT)
            except subprocess.CalledProcessError as e: raise IOError(404, 'Failed to mount Wasabi diskimage: %s' % e.output)
            shutil.copytree('/Volumes/Wasabi/Wasabi.app', os.path.join(wasabidir,appname))
            subprocess.call('hdiutil detach -quiet -force /Volumes/Wasabi', shell=True)
        else:  #extract new app from zipfile
            zipf = zipfile.ZipFile(updpath)
            newappname = zipf.namelist()[0][:-1]
            zipf.extractall(wasabidir)
            if(newappname is not appname): os.rename(joinp(wasabidir,newappname,d=wasabidir,uid='skip'),appdir)
        self.wfile.write('##########')
        try:
            newconfig = configparser.ConfigParser()
            newconfig.read(defaultsettings)  #read new config file
            newconfig.set('server_settings','datadir',dataroot)  #save current datadir
            with open(defaultsettings,'wb') as newconffile: newconfig.write(newconffile)
        except configparser.Error: logging.error('Wasabi update error: Could not update settings file.')
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
                except configparser.Error as e: logging.error("Could not update settings file: %s", e)
            self.sendOK('Setting updated')
        else: raise IOError(404, 'Restricted request: only for local installation.')

    #send server debug info
    def post_debug(self, form, userid=''):
        if("admin" not in Metadata(userid)): raise IOError(404, '{"error": "Access denied: userid is not admin"}')
        serverdata = {"jobs":len(job_queue.jobs), "users":{}}
        def childcount(id):
            if("children" in libdirs[id]):
                total = len(libdirs[id]["children"])
                for cid in libdirs[id]["children"]: total += childcount(cid)
                return total
            return 0

        rootname = os.path.basename(datadir)
        uids = [uid for uid in libdirs if libdirs[uid]["parent"]==rootname]
        uids.remove("example")
        for uid in uids:
            serverdata["users"][uid] = Metadata(uid).metadata
            serverdata["users"][uid]["analyses"] = childcount(uid)
            serverdata["users"][uid]["datause"] = getsize(joinp(datadir,uid,uid='skip'))
        self.sendOK(json.dumps(serverdata))

    #POST request sent to server
    def do_POST(self):
        try:
            form = cgi.FieldStorage(fp = self.rfile, headers = self.headers, environ={'REQUEST_METHOD':'POST'})
            action = form.getvalue('action','')
            userid = form.getvalue('userid','') if useraccounts else ''

            logging.debug("Post: %s, userid=%s" % (action, userid))
            if(useraccounts and action not in ['checkserver','errorlog','terminate','save','createuser','geturl']): #userid check
                if(not userid or userid not in libdirs or (action!='getlibrary' and (libdirs[userid]['parent']!=os.path.basename(datadir) or userid=='example'))):
                    raise IOError(404, 'Request '+action+' => Invalid user ID:'+(userid if userid else '[Userid required but missing]'))
   
            getattr(self, "post_%s" % action)(form, userid) #process POST request

        except IOError as e:
            if hasattr(e, 'reason'): self.sendError(404,"URL does not exist. %s" % e.reason, action)
            else: self.sendError(404, str(e), action)
        except shutil.Error as why:
            self.sendError(501,"File operation failed: %s" % why)
        except OSError as e:
            print "Got OSError"
            self.sendError(501,"System error. %s" % e.strerror, action)
        except AttributeError as e:
            self.sendError(501, "Invalid POST request. %s" % e, action)
            raise
        except Exception as e:
            logging.exception("Runtime error in POST request: %s" % e)

#class for handling metadata files in job directories
class Metadata(object):
    def __init__(self, jobid, filename="meta.txt", uid = '') :
        global datadir
        
        if(not jobid): raise IOError('No metadata file: no folder ID given');
        self.jobdir = getlibrary(jobid=jobid, uid=uid)
        self.md_file = os.path.join(self.jobdir, filename)
        
        if not os.path.exists(self.md_file):
            self.create(self.jobdir, filename)
        
        try:
            self.metadata = json.load(open(self.md_file))
        except ValueError as why:
            try:
                os.rename(self.md_file,self.md_file+".corrupted")
                logging.error("Renamed corrupt metadata file: "+self.md_file)
            except OSError as e:
                logging.error("Corrupt metadata file renaming failed: "+e)
            self.metadata = {}
    
    def __getitem__(self, key) :
        try: return self.metadata[key]
        except KeyError:
            #logging.debug(self.jobdir+': no "'+key+'" in metadata!')
            return ""
    
    def __setitem__(self, key, value) :
        self.metadata[key] = value
    
    def __delitem__(self, key):
        try: del self.metadata[key]
        except KeyError: logging.debug('cannot delete "'+key+'" from metadata!')
    
    def __len__(self):
        return len(self.metadata)
    
    def __iter__(self):
        return iter(self.metadata)
    
    def __str__(self):
        return json.dumps(self.metadata)
    
    def strings(self):  #stringify all metadata values
        mdata = {}
        for k,v in self.metadata.items(): mdata[k] = str(v)
        return mdata
    
    def update(self, data, val=None):  #edit metadata and write to file
        if val is not None: #update single value
            self[data] = val
        else: #update multiple values
            if(type(data) is not dict):
                logging.error("Unvalid value (%s) passed to Metadata.update: %s" % (type(data), data))
                return
            for k in data:
                if data[k] is not None: self[k] = data[k]
        self.flush()
    
    def flush(self):  #write metadata to file
        datafile = tempfile.NamedTemporaryFile(suffix=os.path.basename(self.md_file), prefix='', dir=self.jobdir, delete=False)
        json.dump(self.metadata, datafile, indent=2)
        datafile.close()
        os.chmod(datafile.name, 0o664)
        os.rename(datafile.name, self.md_file)
    
    def update_log(self):  #update metadata with last line from job log file
        if 'status' not in self.metadata: return #not a job
        if not job_queue.get(self['id']) and self['status'] in (Job.INIT, Job.QUEUED, Job.RUNNING): #broken job
            self.update('status', Job.FAIL)
        self['log'] = self.last_log_line(self['logfile'])
        if(os.path.isfile(os.path.join(self.jobdir, self['logfile']))):
            self['updated'] = os.stat(os.path.join(self.jobdir,self['logfile'])).st_mtime
        else:
            self['updated'] = time.time()
    
    def last_log_line(self, filename='output.log'):
        try:
            f = open(os.path.join(self.jobdir, filename))
        except IOError:
            return "No log file yet."
        
        feedback = prefix = ""
        for line in f:
            line = line.strip()
            if line == '': continue
            elif 'iteration' in line: prefix = line
            elif '\b' in line: feedback = prefix+line.split('\b')[-1]
            else: feedback = line.replace(self.jobdir, "fakePath")
        
        f.close()
        return feedback
    
    def replace(self, data):  #change metadata file key names(s)
        touched = False
        for oldkey,newkey in data.items():
            if oldkey in self.metadata:
                if newkey and self[oldkey]: self[newkey] = self[oldkey]
                del self[oldkey]
                touched = True
        if touched: self.flush()
    
    @staticmethod
    def create(dpath, filename="meta.txt", name="unnamed", imported=""):
        fpath = joinp(dpath, filename)
        f = open(fpath, 'wb')
        os.chmod(fpath, 0o664)
        curtime = str(time.time())
        f.write('{"id" : "'+os.path.basename(dpath)+'"')
        if filename == "meta.txt":
            f.write(', "name" : "'+name+'", "created" : "'+curtime+'"')
            if imported: f.write(', "imported" : "'+curtime+'"')
        f.write('}')
        f.close()
        return Metadata(dpath, filename)


#class for creating queued jobs
class Job(object):
    INIT,QUEUED,RUNNING,SUCCESS,FAIL,TERMINATED = [1, 1, 2, 0, -1, -15]

    def __init__(self, jobid):
        
        self.items = Metadata(jobid).metadata;
        self.jobdir = librarypath(jobid)
        
        self.errormsg = {
            -1  : "See log file",
            -11 : "Segmentation fault",
            -15 : "Terminated by user",
            -16 : "Terminated because of server restart",
            127 : "Executable not found"
        }
        
        if not self['infile']: #self.items['infile']
            logging.debug("No input file for job "+jobid)
        
        self.job_status = self['status'] = Job.INIT
        self.lock = threading.Lock()
        self.bin = self['program']
        self.params = self['parameters'].split(' ')
        self.popen = None
        self.postprocess = None
        
        self['created'] = self['updated'] = time.time()
        self['saved'] = self['completed'] = self['log'] = '';
        
        #validate plugin executable
        pluginfile = os.path.join(plugindir, self["plugin"]) #plugin file
        if(not os.path.isfile(pluginfile)): raise OSError(501, 'Invalid plugin file: '+self["plugin"])
        pluginexec = os.path.join(os.path.dirname(pluginfile), self.bin)
        bindir = os.path.join(plugindir, self.bin) #valid installed program name = pluginfile/plugindir name
        if(os.path.isfile(pluginexec)): self.bin = pluginexec  #prefer the executable in the plugin folder
        elif(not os.path.isfile(pluginexec+'.json') and not os.path.isdir(bindir)): raise OSError(501, 'Invalid program name: '+self.bin)
        #process parameters
        for i, param in enumerate(self.params):
            param = re.sub(r'([;~$|`\\])', r'\\\1', param) #sanitize parameter
            param = re.sub(r'/(\W)\.\//', r'\1'+self.jobdir+os.sep, param) #convert to absolute dirpath
            if(os.sep!='/'): param = re.sub(r'/\.\.\//', '..'+os.sep, param) #convert to windows path
            self.params[i] = param
        
        self["parameters"] = ' '.join(self.params)
        self.update()
        job_queue.enqueue(jobid, self) #add to the
    
    def __getitem__(self, key):
        try: return self.items[key]
        except KeyError: return ""
    
    def __setitem__(self, key, value) :
        self.items[key] = value
    
    def __delitem__(self, key):
        try: del self.items[key]
        except KeyError: pass
    
    def fullpath(self, filename):
        return os.path.join(self.jobdir, filename)
    
    def status(self, newstatus=None, end=False):
        if newstatus is not None:
            self.job_status = self["status"] = newstatus
            if end and newstatus!=0: #bad exit code
                try:
                    self["status"] = self.errormsg[newstatus]
                except KeyError:
                    self["status"] = "unknown error. Exit code: "+str(newstatus)
        return self.job_status
    
    def lock_status(self): self.lock.acquire()
    
    def unlock_status(self): self.lock.release()
    
    def terminate(self, shutdown=False):
        self.lock_status()
        if self.popen is not None: self.popen.terminate()
        self.status(Job.TERMINATED, end=True)
        if shutdown: self["status"] = self.errormsg[-16]
        self.update()
        logging.debug("Job "+self["id"]+" terminated.")
        self.unlock_status()
    
    def check_outfiles(self): #verify predefined output files
        outfiles = self["outfile"].split(',')
        for i, filename in enumerate(outfiles):
            if(not os.path.isfile(self.fullpath(filename))): del outfiles[i]
        self["outfile"] = ','.join(outfiles)

    def done(self): return self["status"] not in (Job.INIT, Job.QUEUED, Job.RUNNING)
    
    def begin(self):
        self.status(Job.RUNNING)
        self.update()

    def process(self):
        self.lock_status()
        
        if self.done():
            self.unlock_status()
            return
        
        self.begin()
        
        logfile = open(self.fullpath(self["logfile"]), "wb")
        jobcommand = self.bin + ' ' + self["parameters"]
        closef = False if sys.platform.startswith("win") else True #enable stderr/out redirection for Windows
        
        def limit_process(): #set limits for system resources (UNIX)
            try:
                if(cpulimit): resource.setrlimit(resource.RLIMIT_CPU, (cpulimit*3600, cpulimit*3600)) #limit running time
                if(datalmit): resource.setrlimit(resource.RLIMIT_FSIZE, (datalimit, datalimit)) #limit output file size
            except (ValueError, resource.error) as e:
                logging.debug("Falied to limit job resources: "+str(e))
            os.nice(5) #lower process priority
        
        try:
            self.popen = subprocess.Popen(jobcommand, stdout=logfile, stderr=logfile, close_fds=closef, cwd=self.jobdir, shell=True)
            logging.debug("Job launched: "+jobcommand) #shell=True (supports >outputfile)
        except OSError as e:
            logfile.write("Server error: "+str(e)+", when executing job: "+jobcommand)
            self.unlock_status()
            ret = -1
        else:
            self.unlock_status() 
            ret = self.popen.wait()
        finally:
            self.lock_status()
            self.end(ret)
            logfile.close()
            self.unlock_status()

    def end(self, rc):
        if self.done(): return
        self["completed"] = time.time()
        self.status(rc, end=True)
        if(rc==0): #job completed
            self.check_outfiles()
            if(self["nextstep"]):
                Job(self["nextstep"])
            elif(self["notify"]):
                msg = 'Your pipeline has successfully finished! Last step ID: '+self.jobid
                sendmail('Wasabi pipeline finished', msg, self.jobid)
                del self["notify"]
            del self["plugin"]
        self.update()
    
    def update(self, key="", value=""): #write metadata to meta.txt
        if(key and value): self[key] = value
        Metadata(self["id"]).update(self.items)

#class for creating the job queue
class Workqueue(object):
    def __init__(self, numworkers=0, qtimeout=1, qsize=0):
        self.jobs = {}
        self.queue = queue.Queue(qsize)
        self.workthreads = self._init_workers(numworkers)
        self.qtimeout = qtimeout
        self.running = False
    
    def _init_workers(self, numworkers):
        if numworkers == 0 :
            numworkers = multiprocessing.cpu_count()
        tmp = []
        
        for tnum in range(numworkers):
            t = threading.Thread(target=self._consume_queue)
            t.daemon = True
            tmp.append(t)
        return tmp
    
    def start(self):
        self.running = True
        for t in self.workthreads:
            t.start()
        logging.debug("Workqueue: started")
    
    def stop(self):
        self.running = False
        for jobid in self.jobs.keys():
            self.terminate(jobid, shutdown=True)
        self.queue.join()
        for t in self.workthreads:
            t.join()
        logging.debug("Workqueue: stopped")
    
    def enqueue(self, jobid, job):
        logging.debug("Workqueue: enqueuing %s" % jobid)
        self.jobs[jobid] = job
        self.queue.put(job)
        job.status(Job.QUEUED)
        job.update()
    
    def get(self, jobid):
        try :
            return self.jobs[jobid]
        except KeyError:
            #logging.debug("Workqueue: %s not queued" % jobid)
            return None
    
    def terminate(self, jobid, shutdown=False):
        if jobid in self.jobs:
            self.get(jobid).terminate(shutdown)
            del self.jobs[jobid]
            self.queue.task_done()
            logging.debug("Workqueue: terminated %s" % jobid)
    
    def _consume_queue(self):
        while self.running:
            try :
                job = self.queue.get(timeout=self.qtimeout)
            except queue.Empty:
                continue
            
            jobid = job["id"]
            logging.debug("Workqueue: starting %s" % jobid)
            
            try:
                job.process()
            except OSError:
                raise
            
            if jobid in self.jobs:
                del self.jobs[jobid]
                self.queue.task_done()
                logging.debug("Workqueue: completed %s (status: %s)" % (jobid, job.status()))


#HTTP server subclass for multithreading
class MultiThreadServer(ThreadingMixIn, HTTPServer):
    allow_reuse_address = True #allow restart after dirty close
    
    def __init__(self, *args):
        HTTPServer.__init__(self, *args)
    
    def process_request_thread(self, request, client_address):
        try:
            self.finish_request(request, client_address)
            self.close_request(request)
        except socket.error:
            logging.debug('Disconnected request from '+str(client_address))  


#Start Wasabi server
def main():
    global job_queue
    global serverport
    global num_workers
    global local
    global debug
    global logtofile
    global browsername
    global osxbundle
    
    parser = argparse.ArgumentParser(description="A support server for Wasabi webapp.")
    parser.add_argument("-p", "--port", type=int, metavar="N", help="set server port (default: %s)" % serverport, default=serverport)
    vgroup = parser.add_mutually_exclusive_group()
    vgroup.add_argument("-v", "--verbose", action='store_true', help="show server traffic %s" % ("(default)" if debug else ""), default=debug)
    vgroup.add_argument("-q", "--quiet", action='store_true', help="minimal feedback %s" % ("(default)" if not debug else ""))
    fgroup = parser.add_mutually_exclusive_group()
    fgroup.add_argument("-f", "--filelog", action='store_true', help="print feedback to file %s" % ("(default)" if logtofile else ""), default=logtofile)
    fgroup.add_argument("-c", "--console", action='store_true', help="print feedback to console %s" % ("(default)" if not logtofile else ""))
    lgroup = parser.add_mutually_exclusive_group()
    lgroup.add_argument("-l", "--local", action='store_true', help="autolaunch web browser %s" % ("(default)" if local else ""), default=local)
    lgroup.add_argument("-r", "--remote", action='store_true', help="just start the server %s" % ("(default)" if not local else ""))
    args = parser.parse_args()
    serverport = args.port
    debug = False if args.quiet else args.verbose
    logtofile = False if args.console else args.filelog
    local = False if args.remote else args.local
    start_logging()
    
    info('Starting server...\n') #start task queue
    job_queue = Workqueue(num_workers)
    job_queue.start()
    maplibrary() #build library index
    
    try:
        server = MultiThreadServer(('',serverport), WasabiServer)
        info("Wasabi HTTP server started at port %d\n" % serverport)
        if(not osxbundle): info("Press CRTL+C to stop the server.\n")
        logging.debug('Serving from: %s' % appdir)
        logging.debug('Hostname: %s' % socket.getfqdn()) #get server hostname
        
        if(local and browsername!='NO'): #autolaunch wasabi in a webbrowser
            if(browsername=='default'): browsername = None
            try:
                if sys.platform=='darwin': webbrowser.register("chrome", None, webbrowser.MacOSXOSAScript("Google Chrome"))
                else: webbrowser.register("chrome", "google-chrome %s", None) #register Chrome
                controller = webbrowser.get(browsername)
                controller.open("http://localhost:%d" % serverport, 1, True)
            except webbrowser.Error as e: logging.error("Failed to open a web browser: %s" % e)
        server.serve_forever()
    except socket.error as e :
        logging.error(e)
        return -1
    except KeyboardInterrupt:
        info("\nShutting down server...")
        server.socket.close()
    except Exception as e:
        logging.exception("Runtime error: %s" % e)
    
    if(len(job_queue.jobs)):
        info("Warning: %s jobs in the queue were cancelled." % len(job_queue.jobs))
    job_queue.stop()
    return 0

if __name__ == '__main__':
    sys.exit(main())
