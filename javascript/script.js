/*
Main javascript file for Wasabi webapp (http://wasabiapp.org)
Copyright Andres Veidenberg (andres.veidenberg{at}helsinki.fi), University of Helsinki (2017)
Distributed under AGPL license (http://www.gnu.org/licenses/agpl)
*/

//string class polyfills
if(!String.prototype.trim){ String.prototype.trim = function(){ return this.replace(/^\s+|\s+$/g, '');}; }
if(!String.prototype.capitalize){ String.prototype.capitalize = function(){ return this.charAt(0).toUpperCase()+this.slice(1); }; }

//== Globals ==//
var currentversion = 180530; //local version (timestamp) of Wasabi
var sequences = {}; //seq. data {name : [s,e,q]}
var treesvg = {}; //phylogenetic nodetree
var leafnodes = {}; //all leafnodes+visible ancestral leafnodes
var letters = '--..??**AaBbCcDdEeFfGgHhIiJjKkLlMmNnOoPpQqRrSsTtUuVvWwXxYyZz'.split('');
var alphabet = {protein:['A','R','N','D','C','Q','E','G','H','I','L','K','M','F','P','S','T','W','Y','V','B','Z','X'],
DNA:['A','T','G','C','N','X'], RNA:['A','G','C','U','N','X'], gaps: ['-','.','?','*'], codons:{TTT:'F', TTC:'F', TTA:'L', TTG:'L', CTT:'L', CTC:'L', CTA:'L', CTG:'L', ATT:'I', ATC:'I', ATA:'I', ATG:'M', GTT:'V', GTC:'V', GTA:'V', GTG:'V', TCT:'S', TCC:'S', TCA:'S', TCG:'S', CCT:'P',CCC:'P',CCA:'P',CCG:'P', ACT:'T',ACC:'T',ACA:'T',ACG:'T', GCT:'A', GCC:'A',GCA:'A', GCG:'A', TAT:'Y', TAC:'Y', TAA:'*',TAG:'*', CAT:'H',CAC:'H', CAA:'Q',CAG:'Q', AAT:'N',AAC:'N', AAA:'K',AAG:'K', GAT:'D', GAC:'D', GAA:'E',GAG:'E', TGT:'C',TGC:'C', TGA:'*', TGG:'W', CGT:'R',CGC:'R',CGA:'R',CGG:'R', AGT:'S',AGC:'S', AGA:'R', AGG:'R', GGT:'G', GGC:'G', GGA:'G', GGG:'G', NNN:'?', ANN:'?', TNN:'?', GNN:'?',
CNN:'?', AAN:'?', ATN:'?', AGN:'?', ACN:'?', TAN:'?', TTN:'?', TGN:'?', TCN:'?', GAN:'?', GTN:'?', GGN:'?', GCN:'?', CAN:'?', CTN:'?', CGN:'?', CCN:'?'}};
var colors = {};
var symbols = {};
var canvassymbols = {'.':'+'}; //canvas masks
var canvaslabels = {'-':'gap','.':'ins.','?':'unkn.','*':'stop'};
var canvaslist = []; //list of rendered seq. tiles
var colflags = []; //(selection-)flagged columns
var rowflags = [];
var selections = [];
var maskedcols = []; //array of columns masked via sequence menu
var importedFiles = ko.observableArray([]); //temporary container for imported raw data
importedFiles.get = function(name){ return ko.utils.arrayFirst(importedFiles(), function(item){ return item.name==name; }); };
var dom = {}; //global references to DOM elemets
var _paq = _paq || []; //list of tracked events

//== System state data. Mapping with KnockOut library ==//
//custom settings to map data from server to local datamodel
var libraryopt = {
	key: function(item){ if(!item) console.log('Duplicate library ID!'); else return item.id; },
	copy: ['id','parameters','program','infile','logfile','source','created','shared','importurl','folder'], //static items
	name: { create: function(opt){ //requires modified ko.mapping to work on nested data
		var mapped = ko.observable(opt.data);
		mapped.subscribe(function(newname){ //auto-sync on name edit
			communicate('writemeta',{id:opt.parent.id, key:'name', value:newname});
		});
		return mapped;
	}}
};
//keep state of server data
var serverdata = {import: {}, library: ko.mapping.fromJS([],libraryopt), params: ko.mapping.fromJS({},{copy:['params']})};
serverdata.library.subscribe(function(newdata){
	var cnt = 0; 
	$.each(newdata, function(i,itm){ if(!itm){ cnt++; delete serverdata.library()[i]; }});
	if(cnt){ console.log('Note: '+cnt+' duplicate IDs removed from analysis library.'); }
});

//KO library helper functions
function unwrap(v){ if(typeof(v)=='function') v = v(); return typeof(v)=='function'? v() : v; } //read from (non)observable
//update/create (non)observable
function wrap(v,newv,create){
	if(typeof(v)=='function') v(newv); else if(create) v = ko.observable(newv); 
	else if(create===false) return false; else v = newv; return true;
}
//find obj from array by its key value
function indexOfObj(objarr, key, val){
	for(var i=0; i<objarr.length; i++){ if(objarr[i][key]==val) return i; }
	return -1;
}

//extenders to KO viewmodel items
ko.extenders.format = function(obsitem, format){ //format an observable value in-place
    var formatted = ko.pureComputed({
        read: obsitem,
        write: function(newval){
			obsitem(newval);
			if(format=='trim' && typeof(newval)=='string') newval = newval.trim();
			else if(format=='nospace') newval = newval.replace(/\s/g,'_');
			else if(format=='alphanum') newval = newval.replace(/\s/g,'_').replace(/[^\w\.]/g,'');
			else if(~['number', 'float', 'int', 'posit'].indexOf(format)){
	        	if(newval=="") return;
	        	var vtype = typeof(newval);
				newval = format=='int'? parseInt(newval) : parseFloat(newval);
				if(isNaN(newval) || (format=='posit' && newval<0)) newval = 0;
				if(vtype=='string') newval = newval.toString();
				
			}
			obsitem(newval);
        }
    });
	formatted(obsitem());
	return formatted;
};
ko.extenders.enable = function(obsitem, bool){ //add filter to enable/disable an observable
    var filtered = ko.computed({
        read: obsitem,
        write: function(incoming){
			if(bool) obsitem(incoming);
        }
    });
	filtered(obsitem());
	return filtered;
};

//HTML element transitions for KO viewmodel items
ko.bindingHandlers.fadevisible = {
	init: function(element){ $(element).css('display','none') },
    update: function(element, accessor){
	var value = unwrap(accessor);
        if(value) $(element).fadeIn(); else $(element).hide();
    }
};
ko.bindingHandlers.tempfade = {
	init: ko.bindingHandlers.fadevisible.init,
	update: function(element, accessor){
	var value = unwrap(accessor);
        if(value) $(element).fadeIn(); else $(element).hide();
        setTimeout(function(){ wrap(accessor(),''); },3000); //clear value => rehide
    }
};
ko.bindingHandlers.slidevisible = {
	init: function(element){ $(element).css('display','none') },
    update: function(element, accessor){
        var value = unwrap(accessor);
        if(value) $(element).slideDown(); else $(element).slideUp();
    }
};
ko.bindingHandlers.fadeText = {
    update: function(element, accessor){
  		$(element).hide();
        ko.bindingHandlers.text.update(element, accessor);
        $(element).fadeIn(200);
    }        
};
ko.bindingHandlers.dragdrop = { //enable drag&drop for library items
	init: function(element, itemid){
		$div = $(element);
		var thisid = unwrap(itemid);
	$div.draggable({
		handle: 'div.draghandle',
		opacity: 0.9,
		helper: 'original',
		revert: 'invalid',
		revertDuration: 300,
		addClasses: false,
		zIndex: 50
	});
	$div.droppable({
   		accept: function(el){ return el.attr('itemid')&&thisid&&!unwrap(librarymodel.getitem(thisid).shared); },
   		activeClass: '',
   		addClasses: false,
   		hoverClass: 'draghover',
   		tolerance: 'pointer',
   		drop: function(e,ui){
   			var libid = ui.draggable.attr('itemid');
   			librarymodel.moveitem(libid, thisid);
   			ui.draggable.remove();
   		}
	});
    }
};
ko.bindingHandlers.default = {  //set a default value for input element (plugin API)
	update: function(element, accessor, allBindings, viewModel, bindingContext){
		var defaultval = unwrap(accessor);
		var trackname = unwrap(allBindings.get('name')); //data-bind:"name"
		if(!trackname || !defaultval) return;
		if(element.type=='text'){
			element.setAttribute('placeholder', defaultval);
			if(unwrap(allBindings.get('required')) && !unwrap(allBindings.get('value')).length) element.value = defaultval;
		}
		else bindingContext.$data[trackname](defaultval);
	}
};

var slideadd = function(el){ $(el).css('display','none'); $(el).slideDown() };
var slideremove = function(el){ $(el).slideUp(400,function(){ $(this).remove() }) };
var marginadd = function(elarr){ setTimeout(function(){ elarr[0].style.marginTop = 0; },50); };
var waitremove = function(el){ setTimeout(function(){ $(el).remove() },500) };

//== KnockOut data models to keep the state of the system ==//
//datamodel for Wasabi settings
var koSettings = function(){
	var self = this;
	self.toggle = function(obs){ if(typeof(obs)=='function') obs(!obs()); }
	self.btntxt = function(obs){ return obs()?'ON':'OFF'; }
	
	self.preflist = {tooltipclass:'', undolength:'', autosaveint:'autosave', onlaunch:'', userid:'keepuser', zoomlevel:'keepzoom', colorscheme:'', maskcolor:'', maskletter:'', anccolor:'', ancletter:'', boxborder:'', font:'', windowanim:'', allanim:'', hidebar:'', minlib:'', ladderlib:'', skipversion:'', checkupdates:'local', bundlestart:'local'};
	
	self.saveprefs = function(){ //store preferences to harddisk
		$.each(self.preflist,function(pref,checkpref){
			if(!checkpref || unwrap(self[checkpref])){ //check for enable/disable setting
				if(typeof(self[pref])!='undefined') localStorage[pref] = JSON.stringify(unwrap(self[pref]));
			}
			else if(checkpref) localStorage.removeItem(pref);
		});
	};
	
	self.loadprefs = function(){
		$.each(self.preflist,function(pref,checkpref){
			if(localStorage[pref]){
				if(checkpref && localStorage[checkpref] && !JSON.parse(localStorage[checkpref])) return true; //skip disabled settings
				try{ var prefval = JSON.parse(localStorage[pref]); } catch(e) { var prefval = localStorage[pref]; }
				if(typeof(self[pref])=='function') self[pref](prefval); else self[pref] = prefval;
			}
		});
	};
	
	//useraccount & other settings from server
	self.useraccounts = ko.observable(false); //also account expiry limit (in days)
	self.urlroot = function(){ return window.location.pathname.substring(0,window.location.pathname.lastIndexOf('/'))+'/'; };
	self.useraccounts.subscribe(function(accounts){ if(!accounts) window.history.pushState('','',self.urlroot()); });
	self.userid = ko.observable(''); //current userID
	self.userid.subscribe(function(newid){
		if(newid){ //update url, library and account settings
			window.history.pushState('','',self.urlroot()+newid);
			if(self.keepuser()) localStorage['userid'] = newid;
			communicate('getlibrary',{userid:newid});
			communicate('checkuser',{userid:newid},{retry:true, parse:'JSON',success:function(resp){
				self.username(resp.username||'anonymous');
				self.usermail(resp.email||'');
				self.datause(parseInt(resp.datause||0));
				if(resp.datalimit){ self.datalimit = parseInt(resp.datalimit)*1000000; self.datause.valueHasMutated(); }
			}});
		} else window.history.pushState('','',self.urlroot());
	});
	self.urlid = '';
	self.urlvars = ''; //startup url
	self.keepuser = ko.observable(true); //save userID
	self.keepuser.subscribe(function(keep){
		var userid = self.userid();
		if(keep && userid){ localStorage['userid'] = JSON.stringify(userid); if(self.urlid) self.urlid = ''; }
		else if(!keep && !self.urlid) localStorage.removeItem('userid');
	});
	self.tmpuser = ko.observable(false);
	self.username = ko.observable('');
	self.usermail = ko.observable('');
	self.datause = ko.observable(0); //current library size (in bytes)
	self.dataperc = ko.computed(function(){ return parseInt(self.datause()/(self.datalimit/100))+'%'; });
	self.jobtimelimit = 0; //server-side limits
	self.datalimit = 0;
	self.local = false; //Wasabi istalled as local server
	self.syncsetting = function(newval,setting,obs,params){ if(obs.sync) communicate('settings', {setting:setting, value:newval}, params||{}); }; //server settings syncing
	self.bundlestart = ko.observable(true); //feedback setting for osx bundle startup
	self.bundlestart.subscribe(function(opt){ self.syncsetting(opt,'OutputType',this._target); });
	self.browsers = [{n:'Chrome',v:'chrome'},{n:'Firefox',v:'firefox'},{n:'Safari',v:'safari'},{n:'Opera',v:'opera'},{n:'default',v:'default'},{n:'none',v:'NO'}];
	self.openbrowser = ko.observable('default');
	self.openbrowser.subscribe(function(opt){ self.syncsetting(opt,'browser',this._target); });
	self.datadir = ko.observable('wasabi/Wasabi data');
	self.datadir.subscribe(function(opt){ //sync datadir path setting to server and show feedback
		var dirinput = $('#datadir');
		self.syncsetting(opt,'datadir',this._target, {success: function(){ dirinput.css('border','1px solid green'); },
			error: function(){ dirinput.css('border','1px solid red'); }, after: function(msg){ dirinput.attr('title',msg); }});
	});
	self.linuxdesktop = ko.observable(true);
	self.linuxdesktop.subscribe(function(opt){ self.syncsetting(opt,'linuxdesktop',this._target); });
	self.email = false; //whether server can send emails
	self.joblimit = 0; //max. nr. of running jobs
	self.checkupdates = ko.observable(true);
	self.skipversion = ko.observable(0); //skip a version update
	//autosave settings
	self.undo = ko.observable(true); //save actions to history list
	self.undo.subscribe(function(enable){ if(!enable) model.clearundo(); });
	self.undolength = ko.observable(5); //max lenght of actions history
	self.storeundo = false; //autosave on undo
	self.autosave = ko.observable(false); //autosave dataset to library
	self.autosaveopt = ['modification','minute','5 minutes','15 minutes','30 minutes'];
	self.autosaveint = ko.observable();
	self.intervalid = 0;
	self.autosave.subscribe(function(val){ //set up autosave
		clearInterval(self.intervalid);
		if(val && self.autosaveint() && !librarymodel.openitem().shared){
			if(exportmodel.savename()=='Untitled analysis') exportmodel.savename('Autosaved session');
			if(~self.autosaveint().indexOf('minute')){
				var int = parseInt(self.autosaveint());
				if(isNaN(int)) int = 1;
				self.intervalid = setInterval(savefile,int*60000);
			} else { savefile(); self.storeundo = true; }
		} else self.storeundo = false;
	});
	self.launchopt = ['blank page','import dialog','demo data','last Library item','last session'];
	self.onlaunch = ko.observable(self.launchopt[2]);
	self.onlaunch.subscribe(function(val){
		if(~val.indexOf('last')){
			if(val=='last session'){
				self.autosaveint(self.autosaveopt[0]);
				self.autosave(true);
			}
			self.keepid(true);
		} else self.keepid(false);
	});
	self.keepid = ko.observable(false); //save opened analysis ID
	self.keepid.subscribe(function(val){
		openitem = librarymodel.openitem();
		keepuser = self.keepuser();
		if(val && openitem && keepuser){
		localStorage.openid = openitem.id;
		localStorage.openfile = unwrap(openitem.outfile);
	}});
	self.keepzoom = ko.observable(true); //save zoom level
	//seq display settings
	self.colorsets = {nuc: ['nucleotides','rainbow','greyscale'], aa: ['Taylor','Clustal','Zappo','hydrophobicity','rainbow','greyscale']};
	self.cs = {nuc:ko.observable(0), aa:ko.observable(0)};
	self.ctype = ko.observable('aa'); //model.isdna() will change ctype
	self.coloropt = ko.computed(function(){ return self.colorsets[self.ctype()]; });
	self.colorscheme = ko.computed({ //also checks for valid colorscheme
		read:function(){ return self.coloropt()[self.cs[self.ctype()]()]; },
		write:function(newc){ var ci=self.coloropt().indexOf(newc); if(~ci) self.cs[self.ctype()](ci); }
	}); //sequence coloring scheme
	self.colordesc = {rainbow:'Generates even-spaced vibrant colours.', greyscale:'Generates even-spaced greyscale tones.', custom:'Customize the tones of current colourscheme.', nucleotides:'Default colouring.'};
	self.colordesc.Taylor = self.colordesc.Clustal = self.colordesc.Zappo = self.colordesc.hydrophobicity ='One of commonly used colour schemes.';
	self.maskcolors = ['dark','light','white'];
	self.maskcolor = ko.observable('dark');
	self.cases = ['lowercase','uppercase'];
	self.maskletter = ko.observable('lowercase');
	self.anccolors = ko.computed(function(){
		var arr = ['colorscheme','dark','light','white']; arr.splice(arr.indexOf(self.maskcolor()),1);
		return arr;
	});
	self.anccolor = ko.observable('light');
	self.ancletter = ko.observable('uppercase');
	self.boxborder = ko.observable('border');
	self.fontopt = ['Arial','Century Gothic','Courier New','Georgia','Tahoma','Times New Roman','Verdana'];
	self.font = ko.observable(self.fontopt[1]);
	self.remakecolors = ko.computed(function(){ //refresh canvas after color settings change
		var colscheme = self.colorscheme(), border = self.boxborder(), font = self.font();
		var maskcolor = self.maskcolor(), maskletter = self.maskletter();
		var anccolor = self.anccolor(), ancletter = self.ancletter();
		if(!$('#settings,#info').length) return;
		makeColors();
		canvaslist = [];
		makeImage('','cleanup','slowfade');
		return true;
	}).extend({throttle:500});
	//tree display settings
	self.leaflabels = ['label'];
	self.leaflabel = ko.observable('label');
	self.leaflabel.subscribe(function(newlabel){ //change tree leaflabel text
		if(treesvg.data && $('#treewrap').css('display')!='none'){
			$('#tree text').each(function(i,el){
				var tnode = treesvg.data.root.getById(parseInt(el.getAttribute('nodeid')));
				el.textContent = tnode.nodeinfo[newlabel] || ' ';
			});
		}
	});
	self.nodelabels = ['none','label','branchlength'];
	self.nodelabel = ko.observable('none');
	self.nodelabel.subscribe(function(newlabel){ //change tree nodelabel text
		if(treesvg.data && $('#treewrap').css('display')!='none'){
			$('#tree text').each(function(i,el){
				var tnode = treesvg.data.root.getById(parseInt(el.getAttribute('nodeid')));
				el.textContent = tnode.nodeinfo[newlabel] || ' ';
			});
		}
	});
	self.csizes = ['hidden',3,5,7,10];
	self.csize = ko.observable(3);
	self.csize.subscribe(function(newsize){
		if(newsize=='hidden') $('#tree circle').css('display','none');
		else $('#tree circle').css({r:newsize, display:''});
	});
	//UI settings
	self.backgrounds = ['beige','white','grey'];
	self.bg = ko.observable('beige');
	self.tooltipclasses = ['white','black','beige'];
	self.tooltipclass = ko.observable('white');
	self.allanim = self.animations = ko.observable(true);
	self.allanim.subscribe(function(val){
		if(val){ $('body').removeClass('notransition'); $.fx.off = false; }
		else{ self.windowanim(val); $('body').addClass('notransition'); $.fx.off = true; }
	});
	self.windowanim = ko.observable(true);
	self.windowanim.subscribe(function(val){ if(val) self.allanim(val); });
	self.hidebar = ko.observable(false); //hidden top menubar
	self.minlib = ko.observable(false); //compact library view
	self.ladderlib = ko.observable(true); //ladderized (path) library view
	self.sharelinks = self.sharing = ko.observable(true);
	self.sharedir = ko.observable(false);
	//toggle menubar items
	self.menubar = ko.observable(true);
	self.data = ko.observable(true);
	self.tools = ko.observable(true);
	self.zoom = ko.observable(true);
	self.logo = ko.observable(true);
	//resize seq/tree area
	self.resizew = function(hide){
		var leftedge = dom.left.position().left;
		var rightedge = hide=='seq'? dom.page.width()-30 : hide=='tree'? leftedge+12 : parseInt(dom.page.width()/3);
		var namesw = Math.min(Math.max(50,parseInt(rightedge/3)),200); //tree names width 50-200px
		dom.left.css('width', rightedge-leftedge);
		dom.right.css('left', rightedge);
		$("#namesborderDragline").css('width', rightedge-leftedge);
		$("#namesborderDrag").css('left', rightedge-leftedge-namesw-12);
		dom.tree.css('right', namesw);
		dom.names.css('width', namesw);
	}
	self.seq = ko.observable(false); // =>model.seqsource
	self.tree = ko.observable(false); // =>model.treesource
	self.togglearea = ko.computed(function(){
		var seq = self.seq(); var tree = self.tree();
		if(!dom.left) return; //init run
		if(seq && !tree){ self.resizew('tree'); } //hide tree
		else if(tree && !seq){ self.resizew('seq'); } //hide seq
		else{ self.resizew(); } //show both
	}).extend({throttle:500});
}
var settingsmodel = new koSettings();
var toggle = settingsmodel.toggle;

//datamodel to represent analyses library (including running jobs)
var koLibrary = function(){
	var self = this;
	
	self.getitem = function(key, val){ //get library item by its ID
		var item = ''; if(!key) return '';
		if(!val){ val = key; key = 'id'; }
		$.each(serverdata.library(),function(i,obj){
			if(typeof(obj)=='undefined'){ delete serverdata.library()[i]; return true; }
			if(obj[key] && unwrap(obj[key])==val){ item = obj; return false; }
		});
		return item;
	};
	
	self.getpath = function(id,addself){
		var arr = addself? [id] : [];
		while(id){
			id = unwrap(self.getitem(id).parentid)||'';
			arr.unshift(id);
		}
		if(!arr.length) arr = [''];
		return arr;
	};
	
	self.dirpath = ko.observableArray(['']) //current library treepath
	self.cwd = ko.pureComputed(function(){ var arr = self.dirpath(); return arr[arr.length-1]; });
	self.updir = function(){ if(self.dirpath().length>1) self.dirpath.pop(); };
	self.navigate = function(id){ //got to some of parent dirs or add child dir
		if(id.id) id = id.id;
		var i = self.dirpath.indexOf(id);
		if(~i) self.dirpath(self.dirpath.slice(0,i+1));
		else if(unwrap(self.getitem(id).parentid)==self.cwd()) self.dirpath.push(id);
	};
	
	self.openid = ko.observable(''); //opened (own or external) library item ID
	self.openid.subscribe(function(newid){ //show opened item in library
		if(newid && !~self.dirpath.indexOf(newid)) self.dirpath(self.getpath(newid));
	});
	self.openitem = ko.pureComputed(function(){ return self.getitem(self.openid()); });
	self.openname = ko.pureComputed({
		read: function(){ return unwrap(self.openitem().name)||''; },
		write: function(newval){ var itm = self.openitem(); if(itm.name) itm.name(newval); }
	});
	self.openname.subscribe(function(newname){
		if(newname){
			exportmodel.savename(newname);
			model.modified(false);
	}});
	self.openpath = ko.pureComputed(function(){ return self.getpath(self.openid()); });
	self.openparent = ko.pureComputed(function(){ return unwrap(self.openitem().parentid)||''; });
	self.importurl = '';  //stores source of external import
	self.addanim = function(div){ $(div).hide().fadeIn(800); };
	
	self.removeitem = function(item, event, norecursive, nodelay){ //delete item/kill job
		var btn = event.currentTarget||event;
		var action = item.running&&item.running()? 'terminate' : 'rmdir';
		var rmfunc = function(){
			if(this.tagName) btn = this;
			if(btn) btn.style.opacity = 0.5;
			communicate(action,{id:item.id,rootonly:norecursive,parentid:unwrap(item.parentid)},{btn:btn});
			if(action=='rmdir' && item.id==self.openid()) self.openid('');
			$('#library div.logdiv').remove();
		}
		if(btn && !nodelay && btn.innerHTML != 'Confirm'){  //show confirmation btn
			btn = $(btn);
			var origbtn = btn.clone(true);
			var removebtn = btn.clone().html('<span style="color:red">Confirm</span>').one('click',rmfunc);
			btn.replaceWith(removebtn);
			setTimeout(function(){ removebtn.replaceWith(origbtn); },4000);
		} else rmfunc(); //remove item
	};
	
	self.moveitem = function(id, targetid, copy){
		if(!id) return;
		if(copy) targetid = '';
		var movedir = function(source,target){
			var parentid = unwrap(self.getitem(source).parentid); //for moving shared analysis
			communicate('movedir',{id:source, parentid:parentid, target:target, copy:copy},
				{success:function(){ if($('#library').length && self.cwd()) self.navigate(''); }});
		}
		if(targetid && !self.getitem(targetid).folder){ //group 2 items to a new folder (new folder,move item 1,move item 2)
			self.newdir('',function(response){ if(response.id){ movedir(id,response.id); setTimeout(function(){movedir(targetid,response.id)}, 500); }});
		} else { movedir(id,targetid); }
	};
		
	self.importitem = function(item, event, move){ //mark job as imported to library
		if(!item.outfile() || move){ communicate('writemeta',{id:item.id,key:'imported',value:'never'}); }
		else{ //also load to wasabi browser
			getfile({id:item.id, file:item.outfile(), btn:event.target||false});
		}
	}
	
	self.jobmenu = function(item, event){
		if(!event) return;
		event.stopPropagation();
		var btn = event.currentTarget;
		var menudata = {'Move to library':function(){ self.importitem(item, '', 'move') }}; 
		if(item.st().str!='Failed') menudata['Delete'] = function(){ self.removeitem(item, btn.previousSibling, '', 'nodelay') };
		tooltip('','',{target:btn, arrow:'top', data:menudata, style:'white', id:'jobmenu'});
	};
	
	self.newdir = function(e, successfunc){ //add new folder to library root
		var btn = e? e.currentTarget:'';
		communicate('newdir','',{restore:Boolean(btn), restorefunc:btn?function(){self.newdir(e)}:'', parse:true, aftersync:true, btn:btn, success:successfunc});
	};
	
	self.sharelink = function(item,file,url){ //generate sharing url
		var urlstr = filestr = '';
		if(file && typeof(file)=='string') filestr = ~file.indexOf('.')? '&file='+file : '&dir='+file;
		if(url) urlstr = 'url='+url;
		else if(item && item.id) urlstr = 'id='+item.id+filestr;
		if(urlstr) urlstr = '?'+urlstr;
		return encodeURI('http://'+window.location.host+urlstr);
	}
	
	self.shareicon = function(item,file,title,url){ //generate share link icon
		if(settingsmodel.sharelinks() && (item||url)){
			if(!item) item = {};
			var opt = url?'url:\''+url+'\'': item.id?'id:\''+item.id+'\'' :'';
			if(file) opt += ',file:\''+file+'\'';
			var itemname = title?title:file?'file':item.folder?'collection':'analysis';
			return '<span class="svgicon action share blue" title="Share the '+itemname+'" onclick="dialog(\'share\',{'+
			  opt+'})">'+svgicon('link')+'</span>';
		} else return '';
	}
	
	self.sourcetxt = function(item){
		if(!item.program && !item.source) return '';
		var title = item.parameters? 'launch parameters' : item.importurl? 'source URL' : '';
		var onclick = title? (item.parameters || makeurl(item.importurl)) : '';
		if(title){
			title = 'title="Click to see '+title+'" ';
			onclick = 'onclick="tooltip(\'\',\''+onclick+'\',{target:this,arrow:\'top\',nohide:true,id:\'paramtip\'})" ';
		}
		return '<span class="note">Data source:</span> <span '+title+onclick+(item.parameters?'class="label"':'')+'>'+
		(item.program?'Generated by '+item.program : item.source?'Imported from '+item.source:'')+'</span>';
	}
	
	self.timetip = function(item,event){
		var tipcontent = '<b>Last opened:</b> '+msectodate(item.imported())+'<br><b>Last updated:</b> '+msectodate(item.saved());
		tooltip(event,tipcontent,{arrow:'top', id:'timetip', norefresh:true, target:'elem', shiftx:-27, autohide:'no'});
	}
	
	self.infotip = function(item,event){ //mouseover on info icon
		if(!item.infotxt){ //add functions for info field to convert input<=>html and sync to server
			item.infotxt = ko.observable(item.info().replace('<br>','\n\r').replace(/(<([^>]+)>)/ig,''));
			item.infotxt.subscribe(function(newtxt){
				newtxt = newtxt.replace(urlregex,makeurl).replace(/^[\w ]{1,20}\:/mg,'<b>$&</b>').replace(/[\n\r]/g,'<br>');
				item.info(newtxt);
			});
			item.info.subscribe(function(newinfo){ communicate('writemeta',{id:item.id, key:'info', value:newinfo}); });
			if(!item.shared){ //info icon click => edit mode
				$(event.currentTarget).on('click', function(e){
					e.stopPropagation();
					var infotip = $('#infotip');
					if(!infotip.length) return;
					$(this).off('mouseleave'); //disable autohide
					var startw = infotip.width();
					infotip.addClass('edit');
					$('body').one('click',function(e){ //show new text & recenter
						e.stopPropagation();
						if(infotip.hasClass('edit')){
							infotip.removeClass('edit');
							infotip.css('left', parseInt(infotip.position().left+(startw-infotip.width())/2)+'px');
					}});
			});}
		}
		var tipcontent = '<span data-bind="css:{note:!$data.info()},html:$data.info()||\'No annotations\'"></span>'+
		'<textarea data-bind="value:infotxt"></textarea>';
		var title = item.shared?'':'<span class="note">Click on the icon to edit</span>';
		tooltip(event,title,{arrow:'top', data:tipcontent, id:'infotip', norefresh:true, target:'elem', 
			shiftx:-27, hoverhide:true, tiphover:true, maxw:250, ko:item}); //show infotip
	}
	
	self.opttip = function(item, event){  //menu for modify btn (to move/delete item)
		var open = undefined, move=[], copy= [], group=[], del=[], btn=event.currentTarget, folders=self.folders(), branch=unwrap(item.children);
		var itm = item.folder? 'collection' : branch? 'analysis branch' : 'analysis step';
		if(item.parentid()) move.push({txt:'Detach', t:'Place this '+itm+' as a new pipeline root', icon:'detach', 
			click:function(){ self.moveitem(item.id) }});
		if(!item.folder){
			copy.push({txt:'Duplicate', t:'Place a copy of this '+itm+' as a new pipeline root', icon:'duplicate', 
				click:function(){ self.moveitem(item.id,'','copy') }});
			if(branch) del.push({txt:'Delete step', t:'Remove only this step from the pipeline', icon:'delete1', 
				click:function(){ self.removeitem(item,btn,'step') }});
		}
		if(folders.length){
			var itempath = self.getpath(item.id,true);
			$.each(folders,function(i,f){
				if(~itempath.indexOf(item.id)) return true;
				group.push({txt:f.name, t:'Move this '+itm+' to the collection', icon:'folder',
					click:function(){ self.moveitem(item.id,f.id) }});
			});
		}
		del.push({txt:'Delete', t:'Remove this '+itm+' from library', icon:'delete2', click:function(){ self.removeitem(item,btn) }});
		tooltip(event,'',{arrow:'top', data:{'Detach':move, 'Duplicate':copy, 'Group':group, 'Remove':del}, id:'opttip', target:'elem', shiftx:7, shifty:2});
	}
	
	self.steplevel = function(item){ //get item step# for lib. ladder mode
		return settingsmodel.ladderlib()? self.getpath(item.id).length-1:0;
	}
	
	self.showfile = function(item, event, file){ //show logfile/library folder content from server
		var btn = $(event.target);
		var logdiv = btn.closest('div.itemdiv').next('div.logdiv');
		var rotatearr = btn.prev('span.rotateable');
		if(!logdiv.length){ //content div not yet created
			logdiv = $('<div class="insidediv logdiv">');
			btn.closest('div.itemdiv').after(logdiv);
		}
		
		if(logdiv.css('display')=='none'){ //show content div
			if(rotatearr.length) rotatearr.addClass('rotateddown');
			logdiv.slideDown();
			if($('span',logdiv).length) return false; //use cache
		}
		else{ //hide content div
			if(rotatearr.length) rotatearr.removeClass('rotateddown');
			logdiv.slideUp();
			return false;
		}

		if(file){ //show logfile content
			getfile({id:item.id, file:file, btn:logdiv, noimport:true});
		}
		else{ //show library folder content
		  communicate('getdir',{id:item.id},{success: function(data){
			var files = JSON.parse(data);
			var str = '';
			var outfile = item.outfile?item.outfile():''; //mark the results file in filelist
			$.each(files,function(fname,fsize){ //build filelist html
				if(isNaN(fsize)) return true; //skip folders
				str += '<div class="row">';
				if(~outfile.indexOf(fname)){
					str += '<span title="Main data file" style="color:darkred;cursor:default">'+fname+'</span>';
				}
				else str += fname;
				str += '<span class="note">'+numbertosize(fsize,'byte')+'</span>'+self.shareicon(item,fname);
				if(~fname.indexOf('.xml')||~fname.indexOf('.fas')){
					str += '<a class="button" style="right:60px" title="Load to browser (and set as default)" '+
					'onclick="communicate(\'writemeta\',{id:\''+item.id+'\',key:\'outfile\',value:\''+
					fname+'\'});getfile({id:\''+item.id+'\',file:\''+fname+'\',btn:this})">Open</a>';
				}
				str += '<a class="button" onclick="dialog(\'export\',{exporturl:\''+settingsmodel.userid()+
				'?type=text&getanalysis='+item.id+'&file='+fname+'\'})" title="View file content">View</a></div>';
			});
			if(!str) str = '<span class="note">No files in this folder</span>';
			logdiv.html(str);
		  }});
		}
		return false;
    }//showfile()
	
	self.childlist = function(item){ //list of children IDs (for share window selection)
		var childlist = [{id:'', name:'just the library window'}], folderid = item.id, children = {};
		$.each(serverdata.library(),function(i,itm){ //construct parent>child items
			var pid = itm.parentid();
			if(pid){
				var name = itm.name(); if(name.length>20) name = name.substr(0,17)+'...';
				name += ' ['+itm.id+']';
				if(!children[pid]) children[pid] = [];
				children[pid].push({id: itm.id, name: name}); 
		}});
		var addchildren = function(parentid){ //traverse items
			if(!$.isArray(children[parentid])) return;
			$.each(children[parentid], function(i,child){ childlist.push(child); addchildren(child.id); });
		}
		addchildren(folderid);
		return childlist;
	}
	
	self.folders = ko.pureComputed(function(){ //list of collections in library
		var folders = [];
		$.each(serverdata.library(), function(i,item){ if(item.folder) folders.push({id:item.id,name:item.name()}) });
		return folders;
	}).extend({throttle:500});
	
	self.sortopt = [{t:'Name',v:'name'},{t:'Created',v:'created'},{t:'Opened',v:'imported'},{t:'Updated',v:'saved'}];
	self.sortkey = ko.observable('name');
	self.sortasc = ko.observable(true);
	self.libraryview = ko.computed(function(){ //data items in library window
		var viewitems = [];
		var key = self.sortkey(), asc = self.sortasc(), curdir = self.cwd();
		var itemsarray = serverdata.library();
		$.each(itemsarray, function(i, item){ //add data to library items
			if(!item.parentid) item.parentid = ko.observable('');
			if(!item.info) item.info = ko.observable('');
			if(!item.saved) item.saved = ko.observable('Never');
			if(!item.imported && !item.status) item.imported = ko.observable(item.created()); //!job && !library?
			if(item.folder){
				if(!item.opendataset) item.opendataset = ko.observable('');
				if(!item.opendataset.getSubscriptionsCount()){
					item.opendataset.subscribe(function(newid){ communicate('writemeta',{id:item.id, key:'opendataset', value:newid}); });
				}
			}
			try{ if(item.parentid()!=curdir || (item.status && !item.imported())) return true; } //skip items not in current library page
			catch(e){ console.log('Skipped faulty library item '+item.id+': '+e); return true; }
			viewitems.push(item);
		});
		viewitems.sort(function(a,b){ //sort the items
			a = unwrap(a[key]); b = unwrap(b[key]);
			return a&&b? (asc?a>b:a<b)? 1:-1 :0;
		});
		if(settingsmodel.ladderlib()){ //path view: add path items
			var dirpath = self.dirpath();
			for(var i=dirpath.length-1; i>0; i--){ viewitems.unshift(self.getitem(dirpath[i])); }
		}
		return viewitems;
	}).extend({throttle:200});
	
	self.autoimport = '';
	self.parselog = function(item){
		var logline = item.log(), params = item.parameters;
		var alignst = logline.match(/# ?\((\d+)\/(\d+)\)/), html = logline;
		if(item.running()){
			if(!logline) html = 'Waiting for feedback...';
			else if(alignst){
				var iter = logline.match(/iteration \d/), iters = params.match(/iterate=\d/);
				if(iter&&iters){ var i = iter[0]+' of '+iters[0]+'. ', d = parseInt(iters[0]); }else{ var i='', d=1; }
				var t = i+'Aligning sequence '+alignst[1]+' of '+alignst[2];
				var perc = Math.round(((alignst[1]-1)/alignst[2])*(100/d));
				var mouseover = 'onmouseover="tooltip(false,\''+t+'\',{id:\'logtip\',arrow:\'bottom\',target:this,norefresh:true,autohide:2000})"';
				html = 'Aligning: <span class="progressline" style="width:250px" '+mouseover+'>'+
				'<span class="bar" style="width:'+perc+'%"></span></span>';
			}
		} else {
			if(item.st().str=='Completed') html = 'Job done on '+msectodate(item.completed())+'. Ready to import.';
			else if(item.st().inf){
				html = 'Job failed: '+item.st().inf;
				if(~logline.indexOf('Cputime limit')){
					var timelimit = settingsmodel.jobtimelimit? settingsmodel.jobtimelimit+'-hour':'time';
					html = 'Job ran over '+timelimit+' limit. Reduce the input dataset.';
		}}}
		return html;
	};
	self.jobsview = ko.computed(function(){ //data items in server jobs window
		var viewitems = [];
		var itemsarray = serverdata.library();
		var sortk = 'created';
		itemsarray.sort(function(a,b){ a=unwrap(a[sortk]); b=unwrap(b[sortk]); return a&&b? a>b?1:-1 :0; });
		$.each(itemsarray, function(i, item){ //pull job items from library data
			try{ if(item.imported()) return true; }catch(e){ console.log('Job ID '+item.id+': '+e); } //skip imported items
			if(!item.status) return true; //not a job
			if(!item.st){ item.st = ko.computed(function(){ //process status changes
				var status = item.status(); //status: 1|2|0|'errormsg'
				var translate = {1: [0,'Queued',''], 2: [1,'Running',''], 0: [2,'Completed',''], NaN: [3,'Failed',status]};
				var rt = translate[parseInt(status)] || translate[NaN];
				var ret = {'nr':rt[0], 'str':rt[1], 'inf':rt[2]};
				if(ret.nr==2 && self.autoimport && item.id==self.autoimport && item.outfile()){ //autoimport finished job
					setTimeout(function(){ getfile({id:item.id,btn:$('#job_'+item.id+' a.itembtn'),file:item.outfile()}) }, 500);
				} else if(ret.nr==3 && ~item.parameters.indexOf('-updated')){
					model.treealtered(true); //realign failed => revert tree status
				}
				return ret;
			})}
			if(!item.running){ item.running = ko.computed(function(){ return item.st().nr<2 })}
			viewitems.push(item);
		});
		return viewitems;	
	}).extend({throttle:200});
	
	self.runningjobs = ko.pureComputed(function(){
		var jlist = self.jobsview(), count = 0;
		$.each(jlist, function(i,job){ if(job.running()) count++; });
		return count;
	});
	self.jobtimer = '';
	self.runningjobs.subscribe(function(running){
		if(running){ //set up a status check loop
			if(!self.jobtimer && !model.offline()) self.jobtimer = setInterval(function(){ communicate('getlibrary'); },5000);
		}
		else{ clearInterval(self.jobtimer); self.jobtimer = ''; }
	});
	self.readyjobs = ko.pureComputed(function(){
		return self.jobsview().length - self.runningjobs();
	});
}
var librarymodel = new koLibrary();

//ensembl import settings
var koEnsembl = function(){
	var self = this;
	self.idformats = [{name:'Gene homology',url:'homology/id/',example:'ENSG00000198125'},{name:'Gene tree',url:'genetree/id/',example:'ENSGT00390000003602'},{name:'Alignment block',url:'alignment/region/',example:'13:32906000-32910000'}];
	self.idformat = ko.observable(self.idformats[1]);
	self.isblock = ko.pureComputed(function(){ return self.idformat().name=='Alignment block'});
	self.ishomol = ko.pureComputed(function(){ return self.idformat().name=='Gene homology'});
	self.ensid = ko.observable('').extend({format:'trim'});
	self.comparas = ['vertebrates','plants','fungi','pan_homology','bacteria','protists','metazoa'];
	self.compara = ko.observable(self.comparas[0]);
	self.genomes = ko.pureComputed(function(){ return self.compara()=='vertebrates'?'':'genomes'; });
	self.seqtype = ko.observable('cdna');
	self.isblock.subscribe(function(isblock){ if(isblock){ self.compara(self.comparas[0]); self.seqtype('cdna'); }}); //alignblocks restrictions
	self.homtype = ko.observable('all');
	self.aligned = ko.observable(true);
	self.target = ko.observable('');
	self.idspecies = ko.observable('');
	self.idname = ko.observable('');
	//species sets for alignment blocks: rest.ensembl.org/info/compara/species_sets/EPO?content-type=application/json
	self.alignblocks = [{type: "EPO", set: [{name: "Primates", species: ["homo_sapiens","macaca_mulatta","pongo_abelii","callithrix_jacchus","gorilla_gorilla","pan_troglodytes","papio_anubis","chlorocebus_sabaeus"]}, 
	{name: "Mammals", species: ["homo_sapiens","macaca_mulatta","pongo_abelii","equus_caballus","oryctolagus_cuniculus","callithrix_jacchus","bos_taurus","gorilla_gorilla","pan_troglodytes","sus_scrofa","mus_musculus","canis_familiaris","felis_catus","ovis_aries","papio_anubis","chlorocebus_sabaeus","rattus_norvegicus"]}, {name: "Fish", species: ["danio_rerio","gasterosteus_aculeatus","oryzias_latipes","tetraodon_nigroviridis","lepisosteus_oculatus"]}, {name: "Sauropsids", species: ["gallus_gallus","taeniopygia_guttata","anolis_carolinensis","meleagris_gallopavo"]}]}, {type: "EPO_LOW_COVERAGE", set: [{name: "Mammals", species: ["homo_sapiens","macaca_mulatta","echinops_telfairi","tupaia_belangeri","erinaceus_europaeus","sorex_araneus","microcebus_murinus","pongo_abelii","equus_caballus","ochotona_princeps","cavia_porcellus","choloepus_hoffmanni","procavia_capensis","tursiops_truncatus","tarsius_syrichta","dipodomys_ordii","vicugna_pacos","pteropus_vampyrus","loxodonta_africana","oryctolagus_cuniculus","ailuropoda_melanoleuca","nomascus_leucogenys","callithrix_jacchus","myotis_lucifugus","bos_taurus","gorilla_gorilla","otolemur_garnettii","pan_troglodytes","ictidomys_tridecemlineatus","sus_scrofa","mus_musculus","canis_familiaris","mustela_putorius_furo","felis_catus","ovis_aries","dasypus_novemcinctus","papio_anubis","chlorocebus_sabaeus","rattus_norvegicus"]}, {name: "Fish", species: ["danio_rerio","takifugu_rubripes","gasterosteus_aculeatus","oryzias_latipes","tetraodon_nigroviridis","gadus_morhua","oreochromis_niloticus","xiphophorus_maculatus","astyanax_mexicanus","lepisosteus_oculatus","poecilia_formosa"]}, {name: "Sauropsids", species: ["gallus_gallus","taeniopygia_guttata","anolis_carolinensis","meleagris_gallopavo","pelodiscus_sinensis","anas_platyrhynchos","ficedula_albicollis"]}]}, {type:"PECAN", set: [{name: "Vertebrates", species:["homo_sapiens","macaca_mulatta","ornithorhynchus_anatinus","monodelphis_domestica","pongo_abelii","equus_caballus","taeniopygia_guttata","oryctolagus_cuniculus","anolis_carolinensis","meleagris_gallopavo","callithrix_jacchus","bos_taurus","gorilla_gorilla","pan_troglodytes","sus_scrofa","mus_musculus","canis_familiaris","felis_catus","gallus_gallus","ovis_aries","papio_anubis","chlorocebus_sabaeus","rattus_norvegicus"]}]}];
	self.blocktype = ko.observable(self.alignblocks[0]);
	self.blockset = ko.observable(self.blocktype().set[0]);
	self.blockref = ko.observable(self.blockset().species[0]);
	self.mask = ko.observable('');
	//temp. options for importing multiblock alignment
	self.alnblocks = [];
	self.alnblock = ko.observable({});
	self.alnblockinfo = ko.pureComputed(function(){
		var data = self.alnblock(), list = '';
		if(data.loc) list += '<li>Location: '+data.loc+'</li>';
		if(data.spname) list += '<li>Reference: '+data.spname+'</li>';
		if(data.len) list += '<li>Block length: '+numbertosize(data.len,'bp')+'</li>';
		if(data.spcount) list += '<li>Number of species: '+data.spcount+'</li>';
		return '<ul>'+list+'</ul>';
	});
	self.importblockopts = {};
	self.importblock = function(ko,e){
		var iopts = self.importblockopts;
		var btn = e.currentTarget;
		if(!importedFiles().length || typeof(self.alnblock().index)=='undefined'){ //datafile missing
			btn.innerHTML = 'Failed!'; btn.title = 'Datafile missing'; return;
		}
		
		try{ //trim phyloxml datafile
			var blockdata = '<phyloxml><phylogeny>'+
			$($.parseXML(importedFiles()[0].data)).find('phylogeny')[self.alnblock().index].innerHTML+'</phylogeny></phyloxml>';
		} catch(e){ btn.innerHTML = 'Failed!'; btn.title = e; return; }
		 
		importedFiles([{name:self.alnblock().loc||'Alignment block', data:blockdata}]);
		iopts.closewindow = true; iopts.importbtn = $(btn);
		btn.innerHTML = 'Importing...';
		parseimport(iopts);
		self.alnblocks = {}; self.alnblock({});
		importedFiles([]); iopts = {};
	};
	self.saveblocks = function(ko,e){
		var btn = e.currentTarget;
		var iopts = self.importblockopts;
		var savename = iopts.ensinfo&&iopts.ensinfo.id?iopts.ensinfo.id:'Alignment blocks';
		if(!settingsmodel.userid()||!importedFiles().length){ btn.innerHTML = 'Failed!'; btn.title = 'No account or datafile'; return; }
		var savedata = {writemode:'new', file:importedFiles()[0].data, name: savename};
		communicate('save', savedata, {btn:btn});
	}
}
var ensemblmodel = new koEnsembl();

//main datamodel
var koModel = function(){
	var self = this;
	//system status
	self.offline = ko.observable(false);
	self.offline.subscribe(function(offline){
		if(offline){
			communicate('checkserver'); //re-check
		} else { setTimeout(function(){communicate('getlibrary')},700); }
	});
	self.helsinki = Boolean(~window.location.hostname.indexOf('helsinki.fi')||~window.location.hostname.indexOf('wasabiapp.org'));
	if(self.helsinki) settingsmodel.joblimit = 5;
	self.version = {local:currentversion, remote:ko.observable(0), lastchange:''};
	//rendering parameters
	self.zlevels = [1, 3, 5, 8, 11, 15, 20]; //zoom level = box width (px)
	self.zoomlevel = ko.observable(5); //index of the zlevel array
	self.zoomlevel.subscribe(function(val){
		if(settingsmodel.keepzoom()) localStorage.zoomlevel = JSON.stringify(val); //store new zoom level
		if(settingsmodel.nodelabel()!='none') $('#tree text').css('font-size', parseInt(self.boxh()*0.8)); //resize tree labels
	});
	self.zoomperc = ko.pureComputed(function(){
		var l = self.zoomlevel(), lc = self.zlevels.length-1;
		return l==0 ? 'MIN' : l==lc ? 'MAX' : parseInt(self.zlevels[l]/self.zlevels[lc]*100)+'%';
	});
	self.seqtype = ko.observable(''); //DNA/RNA/codons/protein
	self.isdna = ko.pureComputed(function(){
		var stype = self.seqtype();
		return stype=='DNA'||stype=='RNA';
	});
	self.isdna.subscribe(function(isdna){ settingsmodel.ctype(isdna?'nuc':'aa'); });
	self.symbolw = ko.pureComputed(function(){ return self.seqtype()=='codons'? 3 : 1; });
	self.boxw = ko.pureComputed(function(){ return parseInt(self.zlevels[self.zoomlevel()]*self.symbolw()); });
	self.boxh = ko.pureComputed(function(){ return parseInt(self.zlevels[self.zoomlevel()]*1.3); });
	self.fontsize = ko.pureComputed(function(){ return parseInt(self.zlevels[self.zoomlevel()]*1.1); });
	self.dendogram = ko.observable(false);
	self.activeid = ko.observable(''); //id of active sequence selection area
	self.activeid.subscribe(function(newid){
		$("#seq div[class^='selection']").css({'border-color':'','color':''});
		if(newid){
			$('#selection'+newid+',#vertcross'+newid+',#horicross'+newid).css({'border-color':'orange','color':'orange'});
		}
	});
	//current data
	self.modified = ko.observable(false);
	self.unsaved = ko.pureComputed(function(){
		return  self.modified() || !librarymodel.openitem()? '(unsaved)' : librarymodel.openitem().shared? '(shared)' : ''; 
	});
	self.visiblecols = ko.observableArray();
	self.visiblerows = ko.observableArray();
	self.hasdot = ko.observable(false);
	self.hasdot.subscribe(function(v){
		var label = v? 'del.' : 'gap';
		canvaslabels['-'] = label; canvaslabels['_'] = label;
	});
	//alignment parameteres (alignment window)
	self.gaprate = ko.pureComputed(function(){ return self.isdna()? 0.025 : 0.005; });
	self.gapext = ko.pureComputed(function(){ return self.isdna()? 0.75 : 0.5; });
	self.transopt = ko.pureComputed(function(){
		var opts = [{t:'codons',v:'codon',p:'codons'}];
		if(self.seqtype()=='RNA') opts.push({t:'mt protein',v:'mttranslate',p:'mt-translate'});
		else opts.push({t:'protein',v:'translate',p:'translate'});
		return opts;
	});
	self.iterate = ko.observable(false);
	//sequence + tree statistics (info window)
	self.minseqlen = ko.observable(0);
	self.minseqlength = ko.pureComputed(function(){ return numbertosize(self.minseqlen(),self.seqtype()); });
	self.maxseqlen = ko.observable(0);
	self.maxseqlength = ko.pureComputed(function(){ return numbertosize(self.maxseqlen(),self.seqtype()) });
	self.totalseqlen = ko.observable(0);
	self.totalseqlength = ko.pureComputed(function(){ return numbertosize(self.totalseqlen(),self.seqtype()) });
	self.alignlen = ko.observable(0);
	self.alignlength = ko.pureComputed(function(){ return numbertosize(self.alignlen()) });
	self.alignheight = ko.pureComputed(function(){ return self.visiblerows().length }).extend({throttle: 100});
	self.seqcount = ko.observable(0);
	self.leafcount = ko.observable(0);
	self.nodecount = ko.observable(0);
	self.hiddenlen = ko.pureComputed(function(){ return self.alignlen()-self.visiblecols().length; }).extend({throttle: 200});
	self.hiddenlength = ko.pureComputed(function(){ return numbertosize(self.hiddenlen(),self.seqtype()) });
	self.treesource = settingsmodel.tree;
	self.seqsource = settingsmodel.seq;
	self.sourcetype = ko.observable('');
	self.ensinfo = ko.observable({});
	//button menus
	self.selmodes = ['default','columns','rows'];
	self.selmode = ko.observable(self.selmodes[0]);
	self.setmode = function(mode){ self.selmode(mode); toggleselection(mode); };
	self.filemenu = [{txt:'Library',act:'library',icn:'files',inf:'Browse library of past analyses',req:['online']},
		{txt:'Import',act:'import',icn:'file_add',inf:'Open a dataset in Wasabi'},
		{txt:'Export',act:'export',icn:'file_export',inf:'Convert current dataset to a file',req:['data']},
		{txt:'Save',act:'save',icn:'floppy',inf:'Save current dataset to analysis library',req:['data','online']},
		{txt:'Share',act:'share',icn:'link',inf:'Share current dataset',req:['data','online','sharing']},
		{txt:'Info',act:'info',icn:'file_info',inf:'View summary info about current dataset',req:['data']}];
	self.toolsmenu = [{txt:'PRANK aligner',act:'align',icn:'prank',inf:'Realign current sequences using Prank',req:['seq','online']},
		{txt:'Hide gaps',act:'seqtool',icn:'seq',inf:'Collapse sequence alignment columns',req:['seq']},
		{txt:'Prune tree',act:'treetool',icn:'prune',inf:'Prune/hide tree leafs',req:['tree']},
		{txt:'Translate',act:'translate',icn:'book_open',inf:'Translate sequence data',req:['seq']},
		{txt:'Settings',act:'settings',icn:'settings',inf:'Adjust Wasabi behaviour'}];
	//notifications
	self.errors = ko.observable('').extend({enable: self.helsinki}); //error reporting only for public wasabi
	self.treealtered = ko.observable(false); //tree strcture has been modified
	self.noanc = ko.observable(false); //tree has missing ancestral nodes
	self.update = ko.pureComputed(function(){ //wasabi update available 
		return self.version.local<self.version.remote() && settingsmodel.skipversion()!=self.version.remote();
	});
	self.noaccount = ko.pureComputed(function(){ return settingsmodel.useraccounts()&&!settingsmodel.userid(); });
	self.notifications = ko.pureComputed(function(){ return self.treealtered()||self.update()||self.offline()||self.errors()||self.noanc()||self.noaccount(); });
	self.statusbtn = ko.computed(function(){ //construct notifications button
		var msgarr = [], running = librarymodel.runningjobs(), ready = librarymodel.readyjobs(), str = '';
		var jobs = running||ready;
		
		if(self.treealtered()||self.noanc()) msgarr.push({short:'<span class="red">Realign</span>', long:'<span class="red">Update alignment</span>'});
		if(self.offline()) msgarr.push({short:'<span class="red">Offline</span>', long:'<span class="red">Offline</span>'});
		if(self.errors()){ msgarr.push({short:'<span class="red">Error</span>', long:'<span class="red">Server error</span>'}); }
		if(self.update()){ msgarr.push({short:'<span class="green">Update</span>',long:'<span class="green">Update Wasabi</span>'}); }
		if(self.noaccount()){ msgarr.push({short:'<span class="red">Account</span>',long:'<span class="red">Create account</span>'}); }
		
		if(jobs){
			running = running? '<span class="nr red">'+running+'</span>' : '';
			ready = ready? '<span class="nr green">'+ready+'</span>' : '';
			msgarr.push({short:running+' '+ready, long:'Jobs'+(running?' running '+running:'')+(ready?' ready '+ready:'')});
		}
		
		//build notifications button
		if(msgarr.length == 1){ str = msgarr[0].long; }
		else if(msgarr.length == 2){ str = msgarr[0].short+'<span class="btnsection">'+(jobs?'Jobs ':'')+msgarr[1].short+'</span>'; }
		else if(msgarr.length > 2){
			str = 'Alerts <span class="nr orange">'+(jobs?msgarr.length-1:msgarr.length)+'</span>';
			if(jobs) str += '<span class="btnsection">Jobs '+msgarr.pop().short+'</span>';
		}
		
		//update window title
		var title1 = ready? ready+' jobs ready' : '', alcount = jobs? msgarr.length-1 : msgarr.length, title2 = alcount>0? alcount+' alerts' : ''; 
		window.title = 'Wasabi'+ (title1||title2?' - ':'') + title1 + (title1&&title2?', ':'') + title2;
		
		if(!msgarr.length && $("#jobstatus").length) setTimeout(function(){closewindow('jobstatus')}, 1000); //close empty status window
		return str;
	}).extend({throttle: 200});
	//undo stack
	self.dnasource = ko.observable(''); //container for source cdna
	self.treebackup = ''; //container for source tree
	self.undostack = ko.observableArray();
	self.undostack.subscribe(function(newstack){ self.modified(Boolean(newstack.length)); });
	self.clearundo = function(){
		self.undostack.removeAll();
		self.refreshundo();
		self.treebackup = '';
	};
	self.activeundo = {name:ko.observableArray(), undone:ko.observable(''), data:ko.observable('')};
	self.refreshundo = function(data,redo){
		if(!self.undostack().length){
			self.activeundo.name.removeAll(); 
			self.activeundo.data('');
		} else {
			if(!data) data = self.undostack()[0];
			var name = data.name.length>8? data.name.split(' ')[0] : data.name;
			if(redo) self.activeundo.name()[0].name(name);
			else { self.activeundo.name.removeAll(); self.activeundo.name.push({name:ko.observable(name)}); }
			self.activeundo.undone(false);
			self.activeundo.data(data);
		}
	};
	self.selectundo = function(data){
		if(data==='firsttree') data = self.gettreeundo('first');
		self.refreshundo(data,'select');
	};
	self.addundo = function(undodata,redo){
		if(!settingsmodel.undo()) return; //undo disabled
		if(undodata.type=='tree'&&undodata.info.indexOf('also')==-1) undodata.info += ' Undo also reverts any newer tree changes above.';
		else if(undodata.name=='Remove columns') self.removeundo('type','seq');
		self.undostack.unshift(undodata);
		if(self.undostack().length>settingsmodel.undolength()) self.undostack.pop();
		self.refreshundo(undodata,redo);
		if(settingsmodel.storeundo) savefile(); //auto save to library
	};
	self.removeundo = function(opt,filter){
		if(!opt||!filter) return;
		var adj = 0;
		for(var i=0; i<self.undostack().length; i++){
			if(self.undostack()[i][opt] == filter){ self.undostack.splice(i,1); i--; }
		}
	};
	self.undo = function(){
		var undone = self.activeundo.undone;
		var data = self.activeundo.data();
		if(!data||undone()) return;
		if(data.type=='tree'){
			var undoindex = self.undostack.indexOf(data);
			var restore = self.gettreeundo('prev',undoindex).data||self.treebackup;
			treesvg.loaddata(restore);
			self.gettreeundo('remove',undoindex);
		}
		else if(data.type=='seq') undoseq(data.seqtype, data.data, data.undoaction);
		self.undostack.remove(data);
		undone(true);
		if(settingsmodel.storeundo) savefile(); //store snapshot to server
	};
	self.redo = function(){
		var undone = self.activeundo.undone;
		var data = self.activeundo.data();
		if(!data||!undone()) return;
		if(data.type=='tree') treesvg.loaddata(data.data);
		else if(data.type=='seq') undoseq(data.seqtype, data.data, data.redoaction);
		self.addundo(data,'redo');
		if(settingsmodel.storeundo) savefile(); //store snapshot to server
	};
	self.gettreeundo = function(mode,index){
		var start = mode=='prev'? index+1 : 0;
		var end = mode=='remove'? index : self.undostack().length-1;
		var found = false;
		for(var i=end;i>=start;i--){
			if(self.undostack()[i].type=='tree'){
				found = self.undostack()[i];
				if(mode=='first') break;
				if(mode=='remove') self.undostack.splice(i,1);
			} 
		}
		return found;
	};
}; //koModel
var model = new koModel();

//file export settings (export window)
var koExport = function(){
	var self = this;
	self.categories = ko.computed(function(){
		var catarr = [], hastree = model.treesource(), hasseq = model.seqsource();
		
		if(hasseq) catarr.push({name:'Sequence', formats:[{name:'fasta', variants:[{name:'fasta', ext:['.fa']} ]}, {name:'phylip', variants:[{name:'phylip', ext:['.phy'], interlace:true}]} ]}); 
		
		if(hastree) catarr.push({name:'Tree', formats:[ 
			{name:'newick', variants:[
				{name:'newick', ext:['.nwk','.tre','.tree']},
				{name:'extended newick', ext:['.nhx'], desc:'Newick format with additional metadata (hidden nodes etc.)'}
			]} 
		]});
		
		if(hasseq && hastree){
			catarr.push({name:'Sequence+tree', formats:[{name:'HSAML', variants:[{name:'HSAML', ext:['.xml'], 
			desc:'XML format which supports additional data from PRANK alingments. Click for more info.', url:'http://prank-msa.googlecode.com'} ]} ]});
		}
		
		$.each(catarr, function(i,cat){ cat.formats.push({name:'NEXUS', variants:[{name:'NEXUS', ext:['.nex']}]}); });
		
		return catarr;
		//{name:'Phylip',fileext:'.phy',desc:'',interlace:true}, {name:'PAML',fileext:'.phy',desc:'Phylip format optimized for PAML',hastree:false,interlace:false}, 
		//{name:'RAxML',fileext:'.phy',desc:'Phylip format optimized for RAxML',hastree:false,interlace:false};
	});
	self.category = ko.observable({});
	self.format = ko.observable({});
	self.variant = ko.observable({});
	self.infolink = ko.computed(function(){ return self.variant().url?'window.open(\''+self.variant().url+'\')':false });
	self.filename = ko.observable('Untitled').extend({format:"alphanum"});
	self.fileexts = {'fasta':'.fa', 'phylip':'phy', 'newick':'.nwk', 'extended newick':'.nhx', 'HSAML':'.xml', 'phyloxml':'.xml', 'nexus':'.nex', 'text':'.txt'};
	self.fileext = ko.observable('.fa');
	self.fileurl = ko.observable('');
	self.includeanc = ko.observable(false);
	self.includehidden = ko.observable(false);
	self.interlaced = ko.observable(false);
	self.maskoptions = ['lowercase','N','X'];
	self.masksymbol = ko.observable('lowercase');
	self.truncsymbol = ko.observable('');
	self.trunclen = ko.observable('');
	//Save window preferences
	self.savetarget = ko.observable({});
	self.savetargets = ko.computed(function(){
		var openitem = librarymodel.openitem();
		if(openitem && !openitem.shared){
			var targets = [{name:'next step of input', type:'child'}];
			if(!unwrap(openitem.children)) targets.push({name:'overwrite of input', type:'overwrite'});
			if(unwrap(openitem.parentid)) targets.push({name:'alternative version of input', type:'sibling'});
			targets.push({name:'new root level', type:'new'});
		} else { var targets = [{name:'new root', type:'new'}]; }
		self.savetarget(targets[0]);                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   
		return targets;
	});
	self.savename = ko.observable('Untitled analysis');
}
var exportmodel = new koExport();

//Datamodel for seq. tools (hiding cols)
var koTools = function(){
	var self = this;
	self.hideaction = ko.observable();
	self.hideconserved = ko.observable(false);
	self.hidelimit = ko.observable(10);
	self.minhidelimit = ko.computed({
		read: function(){ return self.hidelimit()==1; },
		write: function(checked){ if(checked) self.hidelimit(1); }
	});
	self.hidelimitperc = ko.computed({
		read: function(){
			var limit = self.hidelimit(), rowc = model.visiblerows().length;
			if(limit<0) self.hidelimit(0); else if(limit>rowc) self.hidelimit(rowc);
			return Math.round(limit/rowc*100);
		},
		write: function(perc){
			if(perc<0) prec = 0; else if(perc>100) perc = 100;
			self.hidelimit(Math.round(perc/100*model.visiblerows().length));
		}
	});
	self.gaptype = ko.observable('indels');
	self.gaptype.subscribe(function(newg){ self.countgaps(); });
	self.gapcount = [];
	self.conscount = [];
	self.countgaps = function(){ //setup: count gaps in alignment columns
		var l = s = cc = '', gaps = [], rows = model.visiblerows(), cols = model.visiblecols();
		self.gapcount = []; self.conscount = [];
		if(~self.gaptype().indexOf('in')){ model.seqtype()=='codons'? gaps.push('...',':::') : gaps.push('.',':'); }
		if(~self.gaptype().indexOf('del')){ model.seqtype()=='codons'? gaps.push('---','___') : gaps.push('-','_'); }
		for(var c=model.alignlen(); c--;){ self.gapcount[c] = self.conscount[c] = 0; }
		$.each(rows, function(n,name){
			setTimeout(function(){
				$.each(cols, function(i,c){ //count gaps in columns
						s = sequences[name][c]; cc = self.conscount[i];
						if(~gaps.indexOf(s)) self.gapcount[i]++;
						else if(cc !== false){ //mark conserved columns
							if(self.conscount[i] === 0) self.conscount[i] = s; //first seq
							else if(self.conscount[i] != s) self.conscount[i] = false;
						} 
				}); //note: takes time on large data
				if(n==rows.length-1){ //counting finished
					$('#seqtool div.spinnercover').remove();
					setTimeout(function(){  if(self.hidelimitperc()==10) self.hidelimitperc(9); else self.hidelimitperc(10); }, 16);
				}	
			}, 16);
		});
	};
	self.gaplen = ko.observable(0);
	self.buflen = ko.observable(0);
	self.hidecolcount = ko.computed(function(){ //preview result
		var colestimate = 0, rows = model.visiblerows().length, threshold = self.hidelimit(), range = [], ranges = [];
		var cons = self.hideconserved(), addcons='', dialog = $('#seqtool').length, action = self.hideaction();
		var minlen = parseInt(self.gaplen()), buflen = parseInt(self.buflen());
		if(minlen<0){ minlen=0; self.gaplen(0); }
		if(buflen<0){ buflen=0; self.buflen(0); }else if(minlen<buflen*2){ buflen = parseInt((minlen-1)/2); self.buflen(buflen); }
		var processrange = function(c){
			range[1] = c; var rangespan = range[1]-range[0];
			if(rangespan>minlen){ range[0]+=buflen; range[1]-=buflen; ranges.push(range); colestimate += rangespan-(2*buflen); }
			range = [];
		};
		$.each(self.gapcount,function(c,gaps){
			addcons = cons && self.conscount[c];
			if(rows-gaps<=threshold || addcons){ if(!range.length) range[0] = c; }
			else if(range.length) processrange(c);
		});
		if(range.length) processrange(self.gapcount.length);
		if(dialog){ //preview, mark columns
			setTimeout(function(){
				colflags = []; clearselection(); if(model.selmode()!='columns') model.selmode('columns');
				$.each(ranges,function(i,carr){ selectionsize('','',carr); for(var r=carr[0];r<carr[1];r++){ colflags[r] = 1; }});
			}, 100);
		}
		return colestimate;
	}).extend({throttle:500});
	self.hidecolperc = ko.computed(function(){ return parseInt(self.hidecolcount()/self.gapcount.length*100) });
	
	self.prunemode = false;
	self.leafaction = ko.observable();
	self.leafsel = ko.observable();
	self.markLeafs = function(unmark){
		if(unmark){ $.each(leafnodes,function(n,node){ if(node.active) node.highlight(false); }); return; }
		registerselections();
		$.each(model.visiblerows(),function(r,name){ if(rowflags[r]&&leafnodes[name]) leafnodes[name].highlight(true); });
	};
	self.processLeafs = function(func,affected){ //hide/remove all marked/unmarked leafs
		if(typeof(func)!='string'){
			var markedcount = $('#names text[fill=orange]').length;
			var target = self.leafsel()=='unmarked'? false : true;
			var affected = target? markedcount : model.visiblerows().length-markedcount;
			var func = self.leafaction()=='prune'? 'remove':'hideToggle';
			if(!affected || model.visiblerows().length-affected<4){
				var errtxt = func=='remove'? 'Can\'t prune: ':'Can\'t hide: ';
				errtxt += !affected? 'nothing to '+self.leafaction()+'.' : 'less than 4 leafs would remain.';
				$('#treetoolerror').text(errtxt);
				setTimeout(function(){$('#treetoolerror').empty()},3000); return;
			}
		} else var target = true; //process premarked leafs
		//if(!model.treebackup) model.treebackup = treesvg.data.root.removeAnc().write('tags');
		$.each(leafnodes,function(n,node){ if(node.active==target) node[func]('hide','nocount'); });
		treesvg.refresh();
		var actdesc = func=='remove'? 'removed' : 'hidden', actname = func=='remove'? 'Remove' : 'Hide';
		if(settingsmodel.undo()){ setTimeout(function(){
			model.addundo({name:actname+' leafs',type:'tree',data:treesvg.data.root.removeAnc().write('undo'),info:affected+' leafs were '+actdesc+'.'});
		},100)}
		closewindow('treetool');
	};
};
var toolsmodel = new koTools();

//== Utility functions ==//
//prettyformat a number
function numbertosize(number,type,min){ //prettyformat a number
	if(isNaN(number)) return number;
	if(!type) type = '';
	else if(type=='dna'||type=='rna') type = 'bp';
	else if(type=='protein') type = 'residues';
    var sizes = type=='bp' ? [' bp',' kb',' Mb',' Gb'] : type=='byte' ? [' Bytes', ' KB', ' MB', ' GB'] : type=='sec'? [' sec',' min :',' h :'] : ['', '&#x2217;10<sup>3</sup>', '&#x2217;10<sup>6</sup>', '&#x2217;10<sup>9</sup>'];
    var order = type=='bp' ? 1024 : 1000;
    if(!min){ var min = type=='bp'||type=='byte'||type=='sec'? order : 1000000; }
    number = parseInt(number);
    if (number < min) return number+(sizes[0]||' '+type);
    var i = 0;
    if(type=='sec'){
	var str = '';
	while(number>=order && i<sizes.length-1){ str = (number%order)+sizes[i]+' '+str; number = number/order; i++; }  
	return str; //"3 h : 12 min : 36 sec"
    }
    else{
	while(number>=order && i<sizes.length-1){ number = number/order; i++; }  
	return number.toFixed(1).replace('.0','')+(sizes[i]||' '+type); //"2 KB"; "1.3 Mb";
    }
};

//convert datestamps to  dates
function msectodate(msec){
	msec = unwrap(msec);
	if(!msec || isNaN(msec)) return 'Never';
	var t = new Date(parseInt(msec)*1000);
	return ('0'+t.getDate()).slice(-2)+'.'+('0'+(t.getMonth()+1)).slice(-2)+'.'+t.getFullYear().toString().substr(2)+
	' at '+t.getHours()+':'+('0'+t.getMinutes()).slice(-2);
}

//parse URL parameters as Object{"param"="val"|["val1","val2"]}
function parseurl(url){
	if(!url) url = window.location.search;
	var startind = url.indexOf('?');
	if(~startind){ url = url.substring(startind+1).split('&'); }else{ return {}; }
	var urlvars = {};
	$.each(url, function(i,varpair){
		var splitind = varpair.indexOf('=');
		if(~splitind){ var key = varpair.substring(0,splitind); var v = varpair.substring(splitind+1); }
		else { console.log("urlparse error: skipped "+varpair); return true; }
		v.split(',').forEach(function(val){ //valuelist or repeated urlparams => multiple values (array)
		try{ val = JSON.parse(val); }catch(e){} //convert non-string value
		if(~key.indexOf('url')){ urlvars.url = urlvars.url? urlvars.url.concat(val) : [val]; }
		else{ urlvars[key] = urlvars[key]? [urlvars[key]].concat(val) : val; }
		});
	});
	return urlvars;
}

//url => <a>
var urlregex = /(https?\:\/\/|www\.)+(\w+\.)+[^\s\\]+/ig;
function makeurl(url,title,regextitle){  //with urlregex: (urlmatch, parenth1, parenth2)
	if(!url) return '';
	else if(url.substr(0,4)=='www.') url = 'http://'+url;
	title = regextitle||!title?url:title; 
	return '<a href="'+url+'" target="_blank">'+title+'</a>';
}

/* Server communication functions */
//send and receive(+save) data from local server fn(str,obj,[str|obj])
//options: 'saveResponseTo' || {'saveto', $form[0], $btn, error(), success(), after(), restorefunc(), nosync?, 'parse'}
function communicate(action, senddata, options){
	if(!action) return false;
	if(model.offline()){ //no backend server
		if(action == 'geturl'){ options.fileurl = senddata.fileurl; getfile(options); } //try CORS/jsonp
		if(action != 'checkserver') return false;
	}
	if(!options) options = {};
	else if(typeof(options)=='string') options = {saveto:options,retry:true}; //retry in case of error
	if(!senddata) senddata = {};
	if(!senddata.userid) senddata.userid = settingsmodel.userid();
	var missinguser = !senddata.userid && settingsmodel.useraccounts();
	
	var formdata = options.form? new FormData(options.form) : new FormData();
	formdata.append('action', action);
	$.each(senddata,function(key,val){ //convert all sent data to formdata
		if(typeof(val)=='object') val = JSON.stringify(val);
		if(typeof(val)!='undefined' && val) formdata.append(key,val);
	});
	
	if(options.btn){
		if(options.btn.jquery) options.btn = options.btn[0];
		if(!options.btntxt) options.btntxt = options.btn.innerHTML;
		if(!options.btntitle) options.btntitle = options.btn.getAttribute('title');
	}
	
	if(options.plugin){ //add input files from plugin container
		var idnames = {}, nIDs = {}, endid = '', inch = exportmodel.includehidden();
		var makeids = plugins[options.plugin]._makeids;
		$.each(plugins[options.plugin],function(poname, po){ //make seq. files & idnames
			if(po.usename){ //parseexport => filestr || {file:filestr, nameids:{name:id}, endid:idstr}
				if(~po().indexOf('tree')) return true;
				var cont = po.container? po.container()[0].imported : false;
				var exported = parseexport(po.fileformat, {makeids:makeids, nameids:nIDs, includehidden:inch, startid:endid, container:cont});
				if(cont) po.container([]);
				if(makeids){ nIDs = exported.nameids; endid = exported.endid; }
				formdata.append(po.usename, exported.file||exported);
			}
		});
		$.each(plugins[options.plugin],function(poname, po){ //make tree files
			if(po.usename){
				if(!~po().indexOf('tree')) return true;
				var cont = po.container? po.container()[0].imported : false;
				var exported = parseexport(po.fileformat, {nameids:nIDs, container:cont});
				if(cont) po.container([]);
				formdata.append(po.usename, exported.file||exported);
			}
		});
		if(makeids){
			$.each(nIDs, function(name,id){ idnames[id] = name; }); //remap
			formdata.append('idnames', JSON.stringify(idnames));
		}
	}
	
	var retryfunc = function(){ communicate(action,senddata,options) }; //resend request
	if(typeof(options.restorefunc)=='function') retryfunc = options.restorefunc;
	var restorefunc = function(){ //restore original button function
		if(options.btn){
			if(!~options.btntxt.indexOf('spinner')) options.btn.innerHTML = options.btntxt||'Retry';
			options.btn.title = options.btntitle||'Click to retry';
			$(options.btn).off('click').click(retryfunc);
		}
    };
    
    var successfunc = '';
    if(action=='save' && senddata.file){
		options.aftersync = true; //postpone successfunc after sync
		options.parse = 'json';
		successfunc = function(resp){
			if(!resp.id) return;
			librarymodel.openid(resp.id);
			if(options.btn) options.btn.innerHTML = 'Saved';
		}
	}
	else if(action=='getlibrary'){
		if(!options.saveto) options.saveto = 'library';
	}
	else if(action=='checkserver'){
		if(!options.error) options.error = function(){ model.offline(true); };
		successfunc = function(resp){
			resp = parseResp(resp,'json');
			if(resp) model.offline(false);
			else model.offline(true);
		}
    }
    
    if(typeof(options.success)=='function') successfunc = options.success;
    var errorfunc = function(errmsg){
		if(typeof(options.error)=='function') options.error(errmsg);
		else if(options.btn) options.btn.innerHTML = '<span class="label red" title="'+errmsg+'">Error</span>';
		//else dialog('error',errmsg);
		if(options.restore) setTimeout(restorefunc, 3000);
    };
    
    var afterfunc = ''; //follow-up action
    if(typeof(options.after)=='string' && options.btn){ //close window after done
		afterfunc = function(){ closewindow(options.btn) };
    } else if(typeof options.after=='function') afterfunc = options.after;
    
    var changelib = ['writemeta','terminate','save','startalign','newdir','rmdir','movedir'];
    var libaction = changelib.indexOf(action)+1;
    var userfree = ['checkserver','errorlog','createuser','geturl'];
    var nonuseraction = userfree.indexOf(action)+1;
    var noabort = ['terminate','rmdir','newdir','movedir'];
    var nonabortaction = noabort.indexOf(action)+1;
    if(missinguser && !nonuseraction){
	    if(options.after) options.after();
		console.log('Cancelled "'+action+'" request: userID missing.');
		return false;
	}
    if(libaction){ //action changes library content
      if(librarymodel.getitem(senddata.id).shared && libaction<=5 && (!senddata.writemode||senddata.writemode!='new')){
	  	dialog('error','You cannot modify shared data.<br>(Attempted to '+action+' on '+senddata.id+')');
	  	return false;
      }
      if(!options.nosync){ //do followup (refresh library)
       afterfunc = function(response, aftererror){
	   	if(options.aftersync && successfunc && !aftererror){  //postpone successfunc after datasync
		   options.success = successfunc; successfunc = afterfunc = '';
		   communicate('getlibrary','',{success:function(){options.success(response)}, after:options.after, btn:options.btn||'', nospinner:true});
		} else communicate('getlibrary','',{after:options.after||'', btn:options.btn||'', nospinner:true});
	
	    if(settingsmodel.datalimit && libaction>=3){ //files added/removed. Get new library size.
	    	communicate('checkuser','',{parse:'JSON', retry:true, success:function(resp){ settingsmodel.datause(parseInt(resp.datause)); }});
	  }}}
    }
    
    var parseResp = function(data, isJSON){ //check and parse Wasabi server response
		var errmsg = '', resp = data;
		try{ resp = JSON.parse(data); }catch(e){ if(isJSON) errmsg = 'JSON parse error: '+e; }
		if(~data.indexOf('Error response')){ errmsg = data.match(/Message:(.+)/im)[1]; }
		if(errmsg){
			console.log(action+' response error: '+errmsg);
			resp = false;
			errorfunc(errmsg);
		}
		return resp;
    }
        
	return $.ajax({
		type: "POST",
		url: 'index.html',
		beforeSend : function(xhrobj){
			if(options.btn && !options.nospinner){
				if(!nonabortaction){ //make process abortable with action/closebutton
					options.btn.innerHTML = '<span class="spinner cancel"><img src="images/spinner_thin.gif"/>'+svgicon('x')+'</span>';
					options.btn.title = 'Waiting for response. Click to abort';
					$(options.btn).off('click').click(function(){xhrobj.abort()});
					closewindow(options.btn,function(){xhrobj.abort()}); //add call aborting to closebtn
				} else options.btn.innerHTML = '<img src="images/spinner.gif" class="icn"/>';
			}
		},
	success: function(rawdata){
		response = parseResp(rawdata, options.parse||'');
		restdelay = 500;
		if(options.saveto){ //save data from server
			if(typeof(options.saveto)=='string'){ //save to 'serverdata' array
				if(typeof(serverdata[options.saveto])=='function'){ //map to datamodel
					ko.mapping.fromJS(response, serverdata[options.saveto]);
					serverdata[options.saveto].remove(undefined);
				} else { serverdata[options.saveto] = response; } //plain copy
				
			}
			else if(typeof(options.saveto)=='function'){ options.saveto(response); }//save to an observable
		}
		else if(options.btn && !successfunc){ //show feedback on button
			if(!response) return;
			if(typeof(response)=='string' && !options.successtxt){ options.btn.innerHTML = response; restdelay = 3000; }
			else if(response.file) options.btn.href = resp.file;
			if($(options.btn).css('opacity')==0) $(options.btn).css('opacity',1); //show downloadlink_btn
		}
		if(options.btn && options.successtxt){ options.btn.innerHTML = options.successtxt; restdelay = 3000; }
		
		if(parseResp(rawdata) && !options.aftersync){ //no errors
			if(successfunc) successfunc(options.parse?response:rawdata); //custom successfunc (data processing/import)
			if(action!='checkserver' && model.offline()) model.offline(false);
			if(options.restore) setTimeout(restorefunc, restdelay); //restore original button state
		}
		if(afterfunc){
			var aftdelay = typeof(options.after)=='string'? 1000 : 500; //close window
			setTimeout(function(){ afterfunc(options.parse?response:rawdata); }, aftdelay); //follow-up (data sync)
		}
	},
	timeout: options.timeout||0,
	error: function(xhrobj,status,msg){
		if(status!="abort"){
			if(status=="timeout" && options.fabtn){ closewindow(options.btn); }
		  if(msg){ //server responded with error
		  	if(~msg.indexOf('nodename nor servname provided')) msg = 'No internet connection';
		  	if(model.helsinki){ //for public Wasabi, log&send errors
		  		var date = new Date();
		  		date = date.toISOString();
		  		date = date.substr(0,date.lastIndexOf('.'));
		  		var optstr = JSON.stringify(senddata);
		  		if(optstr.length>60) optstr = optstr.substring(0,57)+'...';
		  		var errorstr = ' *'+date+' "'+msg+'" when requesting "'+action+'" with '+optstr;
		  		model.errors(model.errors()+errorstr); //notify user
		  		if(action!='errorlog') communicate('errorlog',{errorlog:errorstr}); //send error to server
		  	}
		  	console.log('Wasabi server responded to "'+action+'" with error: '+msg);
		  	errorfunc(toString(msg));
		  }
		  else{ //no response
				if(options.retry){ //allow 2 retries
					options.retry = options.retry=='take2'? false : 'take2';
					setTimeout(retryfunc, 2000); return;
				} else { //probably a server exception
					msg = 'Server communication error ("'+action+'" failed).<br>Strange stuff may follow...';
					console.log('No server response with '+action);
					if(action!='checkserver') communicate('checkserver'); //server offline?
					else errorfunc(msg);
				}
			}
		}
		else if(options.btn){
			options.btn.innerHTML = '<span class="label red" title="'+msg+'">Aborted</label>';
			setTimeout(restorefunc,3000);
		}
		
		if(afterfunc && typeof(options.after)!='string') setTimeout(function(){ afterfunc(msg||'','error'); }, 500); //follow-up (data resync)
	},
	xhr: function(){
			var xhr = $.ajaxSettings.xhr();
			if(options.btn){ //show file transfer feedback
				xhr.tick = 1;
				var desc = 'Downloading';
				var listenfunc = function(d){
				if(d.total && !(xhr.tick%2)){
					var perc = parseInt(d.loaded/(d.total/100));
					options.btn.innerHTML = '<span class="progressline"><span class="bar" style="width:'+perc+'%">'+
					'<span class="title">'+desc+'</span></span></span>';
				}
				xhr.tick++;
			};
			if(action=='geturl'||action=='update'){ //listen for file download progress
				xhr.addEventListener('progress',listenfunc,false);
			} else if(xhr.upload){ //listen for file upload progress
				desc = 'Uploading';
				xhr.upload.addEventListener('progress',listenfunc,false);
			}
			}
		return xhr;
  		},
	data: formdata,
	dataType: "text",
        cache: false,
        contentType: false,
        processData: false
    });
}

//Save current (opened) MSA data to server (library)
function savefile(btn){
	if(!$.isEmptyObject(sequences) || !$.isEmptyObject(treesvg)){
		var savetarget = btn? exportmodel.savetarget().type : exportmodel.savetargets()[1].type; //manual or session autosave[overwrite/sibing]
		var filedata = parseexport('HSAML',{includeanc:true,tags:true,includehidden:true,usedna:false});
		var nodeinfo = {};
		var savedata = {writemode:savetarget, file:filedata, source:model.sourcetype(), parentid:librarymodel.openparent(), id:librarymodel.openid()};
		$.each(leafnodes,function(name,node){ if(node.ensinfo&&node.type!='ancestral') nodeinfo[name] = node.ensinfo; });
		if(!$.isEmptyObject(nodeinfo)) savedata.nodeinfo = nodeinfo;
		if(model.hiddenlen()) savedata.visiblecols = model.visiblecols();
		if(!$.isEmptyObject(model.ensinfo())) savedata.ensinfo = model.ensinfo();
		savedata.name = $('#savename').val() || exportmodel.savename();
		var curitem = librarymodel.openitem();
		if(savetarget == 'overwrite'){
			if(curitem.parameters) savedata.parameters = curitem.parameters;
			if(curitem.importurl||librarymodel.importurl) savedata.importurl = curitem.importurl||librarymodel.importurl;
		}
		
		settings = {};
		$('#saveform > input').each(function(i,item){ //store optional visualisation settings 
			if(item.checked){
				$.each(item.name.split(","),function(j,n){ //parse: "model.t1"=>model.t1()
					if(n=="position"){  //store alignment position
						settings[n] = {left:parseInt(dom.wrap.css('left'))+'px', top:parseInt(dom.seq.css('margin-top'))+'px',
							tree: dom.tree.width(), names: dom.names.width()};
						return true;
					}
					else{
						if(settingsmodel[n]) n = "settingsmodel."+n;
						try{ settings[n] = ~n.indexOf(".")? eval(n+"()") : n; }
						catch(e){ console.log("Skipped save setting "+n+": "+e); }
					}
				});
			}
		});
		if(model.seqtype()=="codons") settings["model.seqtype"] = "codons";
		if(!$.isEmptyObject(settings)) savedata.settings = settings;
		communicate('save', savedata, {btn:btn, after:function(){ closewindow(btn); model.modified(false); }});
	}
	return false;
}

//submit an alignment job
function sendjob(options){
	var datalimit = settingsmodel.datalimit, joblimit = settingsmodel.joblimit;
	if(datalimit){
		var bplimit = datalimit*100000;
		if(model.totalseqlen()>bplimit){
			dialog('notice','Your sequence data size exceeds the server limit of '+numbertosize(bplimit,'bp')+
			'.<br>Please reduce the input dataset size and try again.');
			return false;
		}
		else if(parseInt(settingsmodel.dataperc())>98){
			dialog('notice','The '+numbertosize(datalimit,'byte')+' server space for your analysis library is used up.'+
			'<br>Please delete <a onclick="dialog(\'library\')">some</a> or <a onclick="dialog(\'settings\')">all</a> analyses and try again.');
			return false;
		}
	}
	else if(joblimit && librarymodel.runningjobs()>=joblimit){
		dialog('notice','You already have the maximum of '+joblimit+' jobs running.'+
		'<br>Terminate or wait for a job to finish before launching a new one.');
		return false;
	}

	var senddata = {};
	senddata.name = options.name||exportmodel.savename()||'Remote job';
	senddata.writemode = exportmodel.savetarget().type;
	if(librarymodel.openitem()){
		if(librarymodel.openid()) senddata.id = librarymodel.openid();
		if(librarymodel.openparent()) senddata.parentid = librarymodel.openparent();
	}
	
	var nodeinfo = {};
	$.each(leafnodes, function(name,node){ if(node.ensinfo&&node.type!='ancestral') nodeinfo[name] = node.ensinfo; });
	if(!$.isEmptyObject(nodeinfo)) senddata.nodeinfo = nodeinfo;
	if(!$.isEmptyObject(model.ensinfo())) senddata.ensinfo = model.ensinfo();
	
	var alignbtn = $(options.btn);
	alignbtn.unbind('click'); //prevent multiple clicks
	alignbtn.click(closewindow);
	alignbtn.attr('title','Click to close the window');
	
	var optdata = {btn:alignbtn[0]};
	
	if(options.plugin){ //plugin input options cleanup
		var optform = $(options.form).clone(), useopenseq = false;
		optform.find('select, input:not([name]), input[type=file], input[type=checkbox]:not(:checked)').remove();
		optform.find('input[type=checkbox]').val('true');
		optform.find('input').filter(function(){ return this.value=="false"||!this.value.trim().length; }).remove();
		optform.find('input[fileformat]').each(function(){ //prepare file input options
			var oname = this.getAttribute('name'), fformat = this.getAttribute('fileformat'), tname = this.getAttribute('trackname');
			var popt = plugins[options.plugin][tname];
			if(!popt.container && !~popt().indexOf('tree')) useopenseq = true;
			if(fformat == 'original') fformat = popt.container? (popt.container()[0].imported.ftype.split(':')[1].trim()||'text'):'text';
			var fname = 'input'+oname.replace(/\W+/g,'_')+(exportmodel.fileexts[fformat]||'.txt');
			popt.usename = fname;
			this.setAttribute('value', fname);
		});
		if(!useopenseq){ delete senddata.nodeinfo; delete senddata.ensinfo; } //drop unused metadata
		
		options.form = optform[0];
		optdata.plugin = options.plugin;
		senddata.program = plugins[options.plugin]._program;
		senddata.folder = plugins[options.plugin]._folder;
		senddata.outfile = unwrap(plugins[options.plugin]._outfile);
		senddata.prefix = plugins[options.plugin]._prefix;
		senddata.name = unwrap(plugins[options.plugin]._libraryname);
	}
	else{ //(manual or auto) prank alignment
		var exportdata = parseexport('fasta',{makeids:true,includehidden:exportmodel.includehidden()}); //{file:fastafile,nameids:{name:id}}
		senddata.fasta = exportdata.file;
		var idnames = {}, lastid = '';
		$.each(exportdata.nameids, function(name,id){ idnames[id] = name; lastid = id; });
		if(!$.isEmptyObject(treesvg) && (!options.form || !options.form['newtree']['checked'])) senddata.newick = parseexport('newick',{tags:true,nameids:exportdata.nameids});
		senddata.dots = true;
		if(options.keepalign) senddata.keep = true;
		if(options.usecodons) senddata.codon = true;
		if(!options.form) senddata.name = 'Updated '+senddata.name;
		senddata.idnames = idnames;
	}
	
	if(options.form) optdata.form = options.form;
	
	var successfunc = optdata.success = function(resp){
		alignbtn.html('Job sent');
		try{ var data = JSON.parse(resp); }catch(e){ var data = {}; }
		if(!options.form) librarymodel.autoimport = data.id||'';
		setTimeout(function(){
			if(model.treealtered()) model.treealtered(false);
			closewindow(alignbtn); //close alignment setup winow
		},2000);
	};
	
	var itemcount = serverdata.library().length;
	optdata.error = function(msg){
		if(~msg.indexOf('response')){ //no reponse. Check if job sent.
			setTimeout(function(){
				var newcount = serverdata.library().length;
				if(newcount>itemcount) successfunc();
			},2000);
		}
	};
	optdata.timeout = 4000;
	
	communicate('startalign', senddata, optdata);
	_paq.push(['trackEvent', 'align', options.plugin?'pagan':'prank']); //record event
	return false;
}

//check for a new version of a backend service
function checkversion(btn){
	if(btn) btn.innerHTML = 'checking...';
	communicate('geturl',{fileurl:'http://wasabiapp.org/download/wasabi/changelog.txt'},
	{success:function(changelog){
		var startind = changelog.indexOf('v.')+2, endind = changelog.indexOf('v.',startind+1);
		if(endind==-1) endind = changelog.length;
		var firstblock = changelog.substring(startind,endind);
		var sepind = firstblock.indexOf('* ');
		var lastver = parseInt(firstblock.substring(0,sepind-1)), lastchange = firstblock.substring(sepind+1);
		if(!isNaN(lastver)){
			model.version.remote(lastver);
			model.version.lastchange = lastchange;
			if(btn){
				if(model.version.local < model.version.remote()){
					btn.innerHTML = '<span style="color:green" title="Click for details">update available</span>';
					settingsmodel.skipversion('');
					btn.onclick = function(){ dialog('jobstatus'); };
				} else { btn.innerHTML = '<span style="color:red" title="Click to recheck">no update</span>'; }
			}
		}
	}, error:false});
}

//== File import & export ==//
//retrieve an analysis datafile from server
function getfile(opt){
	if(!opt) return;
	if(opt.aftersync){ //update library before start
		delete opt.aftersync;
		communicate('getlibrary','',{after: function(){getfile(opt)}}); return;
	}
	if(opt.btn){
		if(!opt.btn.jquery) opt.btn = $(opt.btn);
		opt.btn.html('<img class="icn" src="images/spinner.gif">');
	}
    importedFiles([]);
    var trycount = 0;
    
    var showerror = function(msg, fileopt){
	    if(fileopt && typeof(fileopt.error)=='function') fileopt.error(msg);
	    else if(typeof(opt.error)=='function') opt.error(msg);
	    else if(opt.btn) opt.btn.html('<span class="label" title="'+msg+'">Failed &#x24D8;</span>');
		else dialog('error','File download error: '+msg);
	}
    
    var download = function(fileopt){ //GET file > import/successfunc()
      if(!fileopt) fileopt = {};
      var filename = fileopt.file || opt.file || opt.name || "";
      if(~filename.indexOf(',')){ //download 2 files (from library) > import
	      var files = filename.split(',');
	      filename = fileopt.file = opt.file = files[0];
	      fileopt.success = function(data){
		      if(typeof(opt.success)=='function') opt.success(data);
		      else importedFiles.push({name:filename.replace(/^.*[\\\/]/,''), data:data});
		      fileopt.success = false;
		      fileopt.file = opt.file = files[1];
		      download();
		  }
      }
      var urlparams = opt.id?"&getanalysis="+opt.id:"";
      $.each(["file","dir","plugin"],function(i,p){ var pval = fileopt[p]||opt[p]; if(pval) urlparams += "&"+p+"="+pval; });
      if(!urlparams && !opt.fileurl){ console.log('Download error: no URL/filename/ID given'); return; }
      var fileurl = opt.fileurl || settingsmodel.userid()+"?type=text"+urlparams;
	  setTimeout(function(){ $.ajax({
	  type: "GET",
	  url: fileurl,
	  dataType: opt.datatype || "text",
	  success: function(data){
		if(typeof(fileopt.success)=='function'){ fileopt.success(data); }
		else if(typeof(opt.success)=='function'){ opt.success(data); }
		else if(!opt.noimport){ //load and parse filedata for import
			importedFiles.push({name:filename.replace(/^.*[\\\/]/,''), data:data});
			var srcurl = opt.sharedid? 'id='+opt.sharedid : '';
			var source = 'import';
			if(opt.fileurl){ opt.id=''; srcurl=opt.fileurl; source='web address'; }
			setTimeout(function(){ parseimport({source:source, id:opt.id, importbtn:opt.btn, name:opt.name, importurl:srcurl}) }, 300);
			if(settingsmodel.keepid()){
				localStorage.openid = opt.id;
				localStorage.openfile = filename;
			}
		}
		else if(opt.btn && opt.btn.prop('tagName')=='DIV') opt.btn.html('<pre>'+data+'</pre>'); //display filecontents inside a div
	  },
	  error: function(xhrobj,status,msg){
		if(status=="abort"){ msg = "Download cancelled"; }
		if(model.offline() && !~fileurl.indexOf(window.location.host)){ //cross-domain request
			if(!trycount){ fileopt.datatype = 'jsonp'; } //fallback to jsonp
			else{ msg = 'The URL source does not support cross-domain download.'; }
		}
		if(!msg){ //no reponse
			if(!trycount){ //try one more time
				trycount++;
				setTimeout(function(){download(fileopt)}, 1000);
				return;
			}
			msg = 'Server file '+(filename||opt.id)+' inaccessible.';
		}
		showerror(msg, fileopt);
      },
      xhr: function(){
		var xhr = $.ajaxSettings.xhr();
		if(!opt.noimport && opt.btn){
			xhr.tick = 1;
			xhr.addEventListener('progress',function(d){ //listen for file download progress
				if(d.total && !(xhr.tick%2)){
					var perc = parseInt(d.loaded/(d.total/100));
					opt.btn.html('<span class="progressline"><span class="bar" style="width:'+perc+'%">'+
					'<span class="title">Downloading</span></span></span>');
				}
				xhr.tick++;
			}, false);
		}
		return xhr;
	  }
	 }) }, opt.throttle?500:50);
	}; //func download
    
    var showdir = function(refreshed){
	    if(model.noaccount()){ //cannot use library
		    var hasdataset = opt.dir||opt.opendataset? 'A shared dataset was opened.' : 'The sharing URL has no default dataset to open.';
		    dialog('notice', {id:'sharenote', msg:hasdataset+'<br>In order to import the associated analysis history, please create a Wasabi account.'});
		    return;
		}
	    if(librarymodel.getitem(opt.id)){ //folder in library?
		    if(opt.folder) librarymodel.dirpath(['',opt.id]); //no dataset opened; show content of shared folder.
		    dialog('library');
		}
	    else if(!refreshed) communicate('getlibrary','',{after: function(){ showdir(true); }}); //refresh library & try again
	};
		
	var getmeta  = function(){
		var libitem = librarymodel.getitem(opt.id);
		if(libitem){ //use metadata form library
			usemeta(libitem);
		} else { //not in library (shared ID); get meta.txt
			var metasuccess = function(filedata){
				try{
					libitem = JSON.parse(filedata);
					usemeta(libitem);
				} catch(e){ metaerror(e); }
			};
			var metaerror = function(e){ //no meta.txt
				if(!e) e = 'No response';
				if(~e.indexOf('Invalid library ID')){
					console.log('Invalid analysis ID: '+opt.id);
					showerror('Analysis ID <b>'+opt.id+'</b> was not found in server.<br>'+
					'The source dataset may have been deleted or the sharing URL may be faulty.');
				} else {
					console.log('Metadata error: '+e);
					showerror('Could not get metadata for analysis '+opt.id);
				}
			};
			download({file:'meta.txt', success:metasuccess, error:metaerror});
		} 
	};
		
	var usemeta = function(libitem){
		opt.name = unwrap(libitem.name);
		if(!opt.file) opt.file = unwrap(libitem.outfile);
		if(opt.dir){
			opt.sharedid = opt.id;
			showdir();
			delete opt.dir //folder now imported: skip child ID check
			importdataset();
		} else if(libitem.folder){
			opt.sharedid = opt.id;
			opt.opendataset = unwrap(libitem.opendataset);
			if(opt.opendataset){ opt.id = opt.opendataset; getmeta(); }
			else opt.folder = true;
			showdir();
		}
		else importdataset(); //import a dataset
	};
	
	var importdataset = function(){ //get importmeta > get outfile > import
		serverdata.import = {};
		var importmetasuccess = function(filedata){ //use importmeta.txt
			try{
				serverdata.import = JSON.parse(filedata);
				if(typeof(serverdata.import.idnames)=='string') serverdata.import.idnames = JSON.parse(serverdata.import.idnames);
			} catch(e){ console.log('Importmeta parse error: '+e); }
			download();
		};
		var importmetaerror = function(){ //no importmeta. continue with import
			download();
		};
		download({file:'importmeta.txt', success:importmetasuccess, error:importmetaerror});
	}
	
	if(opt.id && !opt.noimport){ getmeta(); } //import analysis (meta>(show library)>importmeta>import)
	else{ download(); } //just download the requested file
}

// Validation of files in import dialog
function checkfiles(filearr, options){
	if(!filearr) filearr = [];
	else if(!filearr[0]) filearr = [filearr];
	if(!options) options = {};
	if(options.onefile && filearr.length>1) filearr = [filearr[0]];
	if(options.mode && options.mode=='noimport') options.noimport = true;
	if(!options.windowid) options.windowid = 'import';
	var infowindow = $('#'+options.windowid).length? $('#'+options.windowid) : makewindow("Importing data",[],{id:options.windowid, icn:'import.png', btn:false, hidden:options.silent});
	var backside = $('.back',infowindow).length;
	var infodiv = backside? $('.back .windowcontent', infowindow) : $('.windowcontent', infowindow);
	if(!infodiv.length) return;
	
	var container = options.container || importedFiles;
	
	// display list of files //
	var ajaxcalls=[], btn=false;
	var btn = $('<a class="button" style="padding-left:15px">&#x25C0; Back</a>');
	btn.click(function(){
		$.each(ajaxcalls,function(c,call){ if(call.readyState!=4){call.abort()}});
		ajaxcalls = []; //cancel hanging filetransfers
		container([]);
		infowindow.removeClass('finished flipped');
		setTimeout(function(){ infowindow.addClass('finished') },900);
	});
	if(!backside){ btn.text('Cancel'); btn = $('<div class="btndiv" style="text-align:center">').append(btn); }
	var list = $('<ul>');
	$.each(filearr,function(i,file){
		file.i = i;
		if(typeof file=='string'){ if(~file.search(/https?\:\/\//)){ file = {url:file} } else { file = {}; } }
		if(!file.name){
			if(file.url){ var furl = file.url.split('?')[0]; file.name = furl.substring(furl.lastIndexOf('/')+1)||'faulty URL!'; }
			else file.name = file.id? 'Wasabi analysis' : 'File '+(i+1);
		}
		var filesize = file.size ? '<span class="note">('+numbertosize(file.size,'byte')+')</span> ' : '';
		list.append('<li class="file">'+file.name+' '+filesize+'<span class="icon"></span></li>');
		filearr[i] = file;
	});
	var filestitle = filearr.length? '<b>Files to import:</b><br>' : '';
	infodiv.empty().append(filestitle,list,'<br><span class="errors note"></span><br>',btn);
	if(backside && !options.silent) infowindow.addClass('flipped');

	var errorspan = $('span.errors',infodiv);
	
	var seticon = function(i,icn){ //preload and show icon ('spinner'>'save'>'warning'/'tick')
		if(icn){
			var ext = icn=='spinner'?'.gif':'.png';
			var img = $('<img class="icn mall">').hide().on("load",function(){$(this).fadeIn()}).attr("src","images/"+icn+ext);
			$('li.file span.icon:eq('+i+')',infodiv).empty().append(img);
		} else { $('li.file span.icon:eq('+i+')',infodiv).empty(); }
	}
	
	var rejected = ko.observableArray(); //flag rejected files in the list
	rejected.subscribe(function(i){ seticon(i,'warning'); });
	
	var displayerror = function(msg){
		errorspan.append('<span class="red">'+msg+'</span><br>');
		if(options.silent){
			infowindow.css('display','block');
			if(backside) infowindow.addClass('flipped');
		}
	};
	
	//step 1: read files to container([]); input: filearr=[{sourceinfo},{sourceinfo}] //
	var readfiles = function(){
		container([]);
		if(!filearr.length) return showerror('Nothing to import');
		errorspan.html('Loading files...<br>');
		$.each(filearr, function(i,file){
			var loadfile = function(data){
				seticon(i, 'save');
				container.push({name:file.name, data:data, i:i});
				if(container().length+rejected().length == filearr.length) peekfiles();
			};
			var showerror = function(msg){
				displayerror(msg); rejected.push(i); 
				if(container().length+rejected().length == filearr.length) peekfiles();
			};
			seticon(i,'spinner');
			
			if(file.id){ //wasabi sharing ID
				getfile({id:file.id, file:file.file, i:file.i, error:showerror, noimport:options.noimport});
				return false; //skip datacheck, straight to import
			}
			else if(file.url){ //external url
				options.importurl = file.url;
				if(model.offline()){ //direct download (maybe cross-domain)
					getfile({fileurl:file.url, name:file.name, error:showerror, success:loadfile});
				} else { //through Wasabi server
					ajaxcalls.push(communicate('geturl', {fileurl:file.url}, {retry:true, error:showerror, success:loadfile}));
				}
			}
			else if(file.text){ //plain text
				loadfile(file.text);
			}
			else{ //local file?
				var reader = new FileReader(); 
				reader.onload = function(evt){
					loadfile(evt.target.result);
				}
				try{ reader.readAsText(file); }catch(e){ showerror('Cannot read local textfile'); }
			}
		});
	}
	
	
	//step 2: peek loaded files: check for datatype //
	var peekfiles = function(){
		if(options.nocheck || options.container){ closewindow(infowindow); } //import to (plugin) container
		else{
			if(!options.nocheck){
			  $.each(container(), function(i, item){
				item.type = parseimport({filenames:[item.name], mode:'check'});
				if(item.type) seticon(item.i,'tick'); //item.type = "sequence"|"tree"|false
				else rejected.push(item.i);
			  });
			}
			importfiles();
		}
	}
	
	//step 3: import files//
	var importfiles = function(){
		if(rejected().length){ //cancel import: errors in check phase
			var s = rejected().length>1? 's' : '';
			displayerror('Cannot recognize the marked file'+s+'.');
		}
		else if(options.noimport) closewindow(infowindow);
		else if(container().length){
			errorspan.append('Importing data...<br>');
			var source = options.source||(options.importurl?'download':'localread');
			setTimeout(function(){
				parseimport({source:source, mode:options.mode||options.windowid, importurl:options.importurl, dialog:infowindow});
				container.valueHasMutated(); 
			}, 800);
		}
	};
	
	readfiles(); //init
}

//Input file parsing
function parseimport(options){ //options{dialog:jQ,update:true,mode}
	if(!options) options = {};
	if(!options.mode) options.mode = 'import';
	var container = options.container || importedFiles;
	var errors = [], notes = [], treeoverwrite = false, seqoverwrite = false;
	var Tsequences = {}, Ttreedata = Ttreesource = Tseqsource = '';
	var idnames = {}, Tidnames = {}, nodeinfo = {}, importsettings = {}, visiblecols = [];
	var ensinfo = options.ensinfo || {};
	if(options.id){ //item imported from library. Get import metadata.
		var metadata = options.metadata || serverdata.import;
		if(metadata.id && metadata.id==options.id){ //preloaded importmeta.txt
			idnames = metadata.idnames || {};
			nodeinfo = metadata.nodeinfo || {};
			ensinfo = metadata.ensinfo || {};
			visiblecols = metadata.visiblecols || [];
			importsettings = metadata.settings || {};
		}
	}
	serverdata.import = {};
	_paq.push(['trackEvent','import',options.source||'unknown']); //record import event
	
	var parsename = function(name, option){
		name = name.trim(name);
		if(!$.isEmptyObject(idnames)){
			var mapname = name.toLowerCase();
			if(idnames[mapname]) name = idnames[mapname];
		}
		//if(~name.indexOf('#')) name = 'Node '+name.replace(/#/g,''); //replace error-prone Prank symbols
		if(option=='nospace') name = name.split(' ')[0];
		name = name.replace(/_/g,' ');
		if(option!='skipcheck'){
			var oldname = name;
			while(Tsequences[name]){ name += '1'; }
			if(oldname!=name) notes.push('Duplicate sequence name "'+oldname+'" renamed to "'+name+'".');
		}
		return name;
	}
	
	var datatype = '', name = '';
	var parseseq = function(seqtxt, filename, format, opt){
		datatype += 'sequence:'+format+' ';
		if(options.mode=='check') return;
		var prefilled = !$.isEmptyObject(Tsequences);
		Tsequences = {};
		
		if(format=='json'){
			var gotsource = false;
			$.each(seqtxt,function(j,data){
				if(!gotsource){
					var species = data.source.species.replace('_',' ');
					Tsequences[data.source.id] = data.source["align_seq"].split('');
					ensinfo.species = species;
					nodeinfo[data.source.id] = {genetype:'source gene', cladename:data.source.id, species:species, accession:data.source.protein_id};
					gotsource = true;
				}
				var species = data.target.species.replace('_',' ');
				Tsequences[data.target.id] = data.target["align_seq"].split('');
				nodeinfo[data.target.id] = {genetype:data.type.replace(/_/g,' ').replace('2',' to '), cladename:data.target.id, species:species, 
				accession:data.target.protein_id, srate:data.target.dn_ds, taxaname:data.subtype, identity:data.target.perc_id};
		});}
		else if(format=='HSAML'){
			var leafdata = $(seqtxt).find("leaf");
			leafdata.each(parsenodeseq);
			var nodedata = $(seqtxt).find("node");
			nodedata.each(parsenodeseq);
		}
		else if(format=='fasta'||format=='fastq'){
			var nameexp = /^[>@](.+)$/mg;
			var noseq = format=='fasta'?">":"+";
			while(result = nameexp.exec(seqtxt)){ //find seqnames from fasta
				var seqend = seqtxt.indexOf(noseq, nameexp.lastIndex);
				if(seqend==-1){ seqend = seqtxt.length; }
				var tmpseq = seqtxt.substring(nameexp.lastIndex, seqend); //get seq between namelines
				tmpseq = tmpseq.replace(/\s+/g,''); //remove whitespace from seq
				name = parsename(result[1], 'nospace'); //assume metadata after space
				Tsequences[name] = tmpseq.split('');
			}
		}
		else { //general import with regexp
			var iupac = 'ARNDCQEGHILKMFPSTUWYVBZX\\-?*';
			var seqstart = new RegExp('\\s(['+iupac+']{10}\\s?['+iupac+']{10}.*)$','img'); //assumes seqlen>=20
			if(format=='clustal'){ //remove clustal-specific additions
				seqstart.lastIndex = seqtxt.search(/[\n\r]+/); //skip first line
				seqtxt = seqtxt.replace(/ {1}\d+$/mg,'');
				seqtxt = seqtxt.replace(/^[ \:\.\*]+$/mg,'');
			}
			else if(format=='nexus'){
				seqtxt = seqtxt.substring(opt.starti, seqtxt.indexOf(';', opt.starti));
				seqtxt = seqtxt.replace(/\[.+\]/g,''); //remove nexus comments
				if(opt.gap && opt.gap!='-') seqtxt = seqtxt.replace(new RegExp(opt.gap,'g'),'-'); //custom gap char  
			}
			else if(format=='phylip' && opt.ntax){ //detect & reformat strict phylip
				var strictphy = false;
				var capture = seqstart.exec(seqtxt);
				if(capture){
				var linelength = capture[1].length;
				for(var s=1; s<opt.ntax; s++){
					capture = seqstart.exec(seqtxt);
					if(linelength != capture[1].length){ strictphy = true; break; }
					linelength = capture[1].length;
				}
				seqstart.lastIndex = 0;
				} else { strictphy = true; }
				if(strictphy){ seqtxt = seqtxt.replace(/^ *.{10}/gm,"$& "); }
			}
			seqtxt = seqtxt.replace(/ *[\n\r]\s*/g,'\n'); //collapse multilines+whitespace
			seqtxt = seqtxt.replace(/ {2,}/g,' ');
			var taxanames = [], bookmark = 0, interleaved = false, firstseqline = true, name = '';
			var repeatingnames = format=='phylip'? false : true;
			while(capture = seqstart.exec(seqtxt)){ //get names & first sequences
				var seqarr = capture[1].replace(/ /g,'').split('');
				if(bookmark < capture.index){ //found name between line start and sequence start
					var taxaname = seqtxt.substring(bookmark, capture.index).trim();
					name = parsename(taxaname, 'skipcheck');
					if(Tsequences[name]){ interleaved = true; repeatingnames=true; break; }
					Tsequences[name] = seqarr; taxanames.push(taxaname);
				}
				else{ //sequence line continues
					if(firstseqline){ if(taxanames.length>1){ interleaved = true; repeatingnames=false; break; } firstseqline = false; }
					Tsequences[name].push.apply(Tsequences[name], seqarr);
				}
				bookmark = seqstart.lastIndex;
			}
			if(interleaved){ //continue parsing for interleaved seq.
				var fulline = /^.+$/gm;
				fulline.lastIndex = bookmark;
				var nameind = 0, name = '', taxaname = '', curname = '', linetxt ='';
				while(capture = fulline.exec(seqtxt)){
					taxaname = taxanames[nameind];
					name = parsename(taxaname, 'skipcheck');
					linetxt = capture[0].trim();
					if(repeatingnames){
						curname = linetxt.substr(0,taxaname.length);
						if(curname!=taxaname){ errors.push("Unexpected taxaname!<br>("+curname+" instead of "+taxaname+")"); break; }
						linetxt = linetxt.substr(taxaname.length);
					}
					seqarr = linetxt.replace(/ /g,'').split('');
					Tsequences[name].push.apply(Tsequences[name],seqarr);
					nameind++;
					if(nameind==taxanames.length) nameind = 0;
				}
			}
			if(taxanames.length){
			  var snames = Object.keys(Tsequences);
			  if(opt.ntax && errors.length==0 && snames.length!=opt.ntax){
				notes.push("Number of taxa found doesn't match <br>the file metadata (expected "+opt.ntax+", found "+snames.length+" expected)");
			  }
			  /*if(opt.nchar && errors.length==0 && Tsequences[snames[0]].length!=opt.nchar){
				notes.push("The sequence length doesn't match <br>the file metadata ("+opt.nchar+" chars, but"+
				  Tsequences[snames[0]].length+" found)");
			  }*/ //compare to longesteq
			} else { notes.push("No taxa found in sequence data"); }
		}
		
		if(!$.isEmptyObject(Tsequences)){
			Tseqsource = filename;
			if(prefilled) seqoverwrite = true;
		}	
	};
	
	var parsenodeseq = function(){ //parse prank/pagan .xml
		var self = $(this);
		var id = self.attr("id");
		name = parsename(self.attr("name") || id);
		Tidnames[id] = name; //HSAML id => name (for parsing tree)
		var tmpseq = self.find("sequence").text();
		if(tmpseq.length){ Tsequences[name] = tmpseq.replace(/\s+/g,'').split(''); }
	};
	
	var parsetree = function(treetxt,filename,format){ //import tree data
		if(!format) format = 'newick';
		datatype += 'tree:'+format+' ';
		if(options.mode=='check') return;
		if(Ttreedata) treeoverwrite = true;
		Ttreedata = '';
		Ttreesource = filename;
		
		if(format=='newick'){ //remove whitespace
			treetxt = treetxt.replace(/\n+/g,'');
			var lpar = (treetxt.match(/\(/g) || []).length;
			var rpar = (treetxt.match(/\)/g) || []).length;
			if(lpar!=rpar){ errors.push("Seems like Newick but parentheses don't match"); return true; }
			if(!$.isEmptyObject(Tidnames)) idnames = Tidnames; //map treename=>seqname (from HSAML)
		}
		Ttreedata = treetxt;
		if(format=='phyloxml' && ~treetxt.indexOf('<mol_seq')){ //sequences in tree data
			if(!$.isEmptyObject(Tsequences)) seqoverwrite = true;
			Tseqsource = filename;
		}
	};
	
	var filenames = options.filenames || ko.utils.arrayMap(container(),function(item){ return item.name });
	if(!$.isArray(filenames)) filenames = [filenames];
	filenames.sort(function(a,b){ //sort filelist: [nexus,xml,phylip,...,tre]
		if(/\.tre/.test(a)) return 1; else if(/\.tre/.test(b)) return -1;
		return /\.ne?x/.test(a)? -1: /\.xml/.test(a)? /\.ne?x/.test(b)? 1:-1 : /\.ph/.test(a)? /\.ne?x|\.xml/.test(b)? 1:-1 : /\.ne?x|\.xml|\.ph/.test(b)? 1: 0;
	});

	var abort = false;
	$.each(filenames,function(i,filename){  //detect fileformat
		var file = container.get(filename).data, marr = false;
		
		if(typeof(file)=='object' && file.hasOwnProperty('data')){ //Ensembl JSON object
			if(!file.data[0].homologies) return;
			parseseq(file.data[0].homologies,filename,'json');
		}
		else if(typeof(file)!='string'){ errors.push("Unrecognized data format in "+filename); return true; }
		else if(/^<.+>$/m.test(file)){ //xml
			if(~file.indexOf("<phyloxml")){ //phyloxml tree (+seq)
				var firstbl = file.indexOf("<phylogeny")+10;
				if(~file.indexOf("<phylogeny",firstbl)){ //multiblock phyloXML
					if(options.ensinfo && options.ensinfo.type && options.ensinfo.type.split('/')[0]=='alignment' && options.ensinfo.id){
						var refspecies = options.ensinfo.id.split('/')[0];
					} else if(options.name){ var refspecies = options.name.split('/')[0] } else { var refspecies = 'homo_sapiens' };
					var alignblocks = [];
					$($.parseXML(file)).find('phylogeny').each(function(bli,blitm){ //gather metadata for all blocks
						var alnbl = {index:bli, spcount:0, spname:'', loc:'', spos:0, len: 0};
						$(this).find('clade').each(function(){
							var taxaname = $(this).children('name').text();
							var taxafullname = $(this).children('taxonomy').children('scientific_name').text();
							var seqloc = $(this).children('sequence').children('location').text();
							if(taxafullname && seqloc){
								alnbl.spcount++;
								if(~taxaname.indexOf(refspecies)){ //the block's query species
									alnbl.spname = taxafullname;
									alnbl.loc = seqloc;
									try{
										var blcoord = seqloc.split(':')[1].split('-');
										alnbl.spos = parseInt(blcoord[0]);
										alnbl.len = parseInt(blcoord[1])-parseInt(blcoord[0]);
									}catch(e){}
								}
							}
						});
						alignblocks.push(alnbl);
					});
					ensemblmodel.alnblocks = alignblocks.sort(function(l,r){ return l.spos== r.spos?0 : (l.spos<r.spos?-1 : 1); });
					ensemblmodel.alnblock(alignblocks[0]);
					options.mode = ''; options.filenames = '';
					ensemblmodel.importblockopts = options;
					dialog('alnblocks'); //show dialog for selecting a block for import 
					abort = true;
					return false;
				}
				parsetree(file,filename,'phyloxml');
			}
			else{  //HSAML
				parseseq(file,filename,'HSAML');
				var newickdata = $(file).find("newick");
				if(newickdata.length) parsetree(newickdata.text(),filename);
			}
			//if(newickdata.length!=0 && leafdata.length!=0){ return false }//got data, no more files needed
		}
		else if(/^[>@].+$/m.test(file)){ //fasta/fastq
			var format = /^@.+$/m.test(file)? 'fastq' : 'fasta';
			parseseq(file,filename,format);
		}
		else if(/^clustal/i.test(file)){ //Clustal
			var lineend = file.search(/[\n\r]/); //skip first line
			parseseq(file,filename,'clustal',{starti:lineend});
		}
		else if(marr = file.match(/^\s*(\d+) {1}(\d+) *[\n\r]/)){ //phylip alignment
			//todo: check for ntax&nchar match
			var lineend = file.search(/[\n\r]/);
			parseseq(file,filename,'phylip', {ntax:marr[1], nchar:marr[2], starti:lineend});
		}
		else if(/^#nexus/i.test(file)){ //NEXUS //todo: check for nchar&ntax&datatype match; matchchar
			var nameline, blockexp = /^begin (\w+)/igm;
			while(nameline = blockexp.exec(file)){ //parse data blocks
				var blockname = nameline[1].toLowerCase();
				//console.log(blockexp.lastIndex+': '+blockname); //double parsing?
				if(blockname=='data'||blockname=='characters'){
					var seqexp = /^\s*matrix\s/im;
					seqstart = file.search(seqexp);
					if(~seqstart){
						var datatxt = file.substring(blockexp.lastIndex, seqstart);
						var mdata = {starti:seqstart+7};
						if(~datatxt.search(/ntax=\d/i)) mdata.ntax = datatxt.match(/ntax=(\d+)/i)[1];
						if(~datatxt.search(/nchar=\d/i)) mdata.nchar = datatxt.match(/nchar=(\d+)/i)[1];
						if(~datatxt.search(/datatype=\w/i)) mdata.datatype = datatxt.match(/datatype=(\w+)/i)[1];
						if(~datatxt.search(/gap=\S/i)) mdata.gap = datatxt.match(/gap=(\S+)/i)[1];
						parseseq(file, filename, 'nexus', mdata);
					}
				}
				else if(blockname=='trees'){
					var liststart = file.search(/translate\s/i);
					var translations = [];
					if(~liststart){ //found translate command
						var listend = file.indexOf(';',liststart);
						translations = file.substring(liststart+10,listend).replace(/\s+/g,' ').split(',');
						$.each(translations, function(i,pair){ pair=pair.trim().split(' '); Tidnames[pair[0]] = pair[1]; });
						blockexp.lastIndex = listend;
					}
					var nwkstart = file.indexOf('(', blockexp.lastIndex);
					var nwkend = file.indexOf(';', nwkstart);
					var nwktxt = file.substring(nwkstart, nwkend);
					parsetree(nwktxt, filename);
					blockexp.lastIndex = nwkend;
				}
			}
		}
		else if(/^\s*\(+['"]?[\w]+.*\;\s*$/.test(file)){ //newick tree
			parsetree(file, filename);
		}
		else{
			errors.push("Unrecognized data format in "+filename);
		}
	});//for each file

	if(abort){ closewindow(options.importbtn||'import'); return; }
	if(options.mode=='check') return datatype;
	
	if(options.container) delete options.container()[0].data; //data extracted to Tsequences/Ttreedata. Clear source.
	else container([]);

	//parse Ttreedata => seq. from phyloxml & visible leaf count
	var treeopt = {skiprender:true, sequences:Tsequences, nodeinfo:nodeinfo, idnames:idnames};
	if(~datatype.indexOf('phyloxml')) treeopt.phyloxml = Ttreedata; else treeopt.newick = Ttreedata;
	var treeobj = Ttreedata ? new Smits.PhyloCanvas(treeopt) : {data:''};
	Ttreedata = '';
	
	var seqnames = Object.keys(Tsequences);
	
	//process & count sequences
	var process_seq = function(){
			var maxseqlen = 0, minseqlen = Tsequences[seqnames[0]].length, totallen = 0;
			var longestseq = '', hasdot = false, alignlen = 0, tmpseq, seqlen;
			for(var n=0;n<seqnames.length;n++){ //count sequence lengths
				tmpseq = Tsequences[seqnames[n]].join('');
				if(!hasdot && ~tmpseq.indexOf('.')) hasdot = true;
				if(tmpseq.length > alignlen) alignlen = tmpseq.length;
				tmpseq = tmpseq.replace(/[-_.:]/g,''); seqlen = tmpseq.length; totallen += seqlen;
				if(seqlen > maxseqlen){ maxseqlen = seqlen; longestseq = tmpseq; }
				if(seqlen < minseqlen){ minseqlen = seqlen; }
			}
			var dnachars = new RegExp('['+alphabet.DNA.join('')+'U?!'+']','ig');
			var trimseq = longestseq.replace(dnachars,''); //check if a sequence is (mostly) dna
			var type = trimseq.length<longestseq.length*0.2? 'DNA' : 'protein';
			if(type=='DNA') if(~longestseq.search(/U/i)) type = 'RNA';
			return {type:type, hasdot:hasdot, maxseqlen:maxseqlen, minseqlen:minseqlen, totallen:totallen, alignlen:alignlen};
		};
		
	var seqstats = seqnames.length? process_seq() : {};
	
	if(options.mode=='importcdna'){ //dna seq. needed
		if(!seqnames.length) errors.push('No sequence data found');
		else if(seqstats.type!='dna') errors.push('Provided data doesn\'t seem to be a DNA sequence');
	}
	else if(!treeobj.data && !seqnames.length) errors.push('Neither tree or sequence data found');
	
	if(errors.length){ //diplay errors. no import
		var ul = $('<ul>').css({'color':'red','white-space':'normal'});
		$.each(errors,function(j,err){ ul.append('<li>'+err+'</li>') });
		if(options.dialog) $('.errors',options.dialog).empty().append('<br><b>File import errors:</b><br>',ul,'<br>');
		else dialog('error',['File import failed:','<br>',ul,'<br>']);
		return false;
	}
	else { //no errors: use parsed data
		if(treeoverwrite) notes.push('Tree data found in multiple files. Using '+Ttreesource);
		if(seqoverwrite) notes.push('Sequence data found in multiple files. Using '+Tseqsource);

		var feedback = function(){
			if(options.dialog){ //import/translate window
				$('.errors',options.dialog).text('Import complete.');
				if(options.mode == 'importcdna'){ //flip cdna window back
					$("#translate").removeClass('finished flipped');
					setTimeout(function(){ $("#translate").addClass('finished') },800);
				}
				else setTimeout(function(){ closewindow(options.dialog) }, 1000); //close window
			}
			else if(options.importbtn){ //import/library window
				options.importbtn.text('Imported');
				if(options.closewindow || options.importbtn.closest('#import').length) setTimeout(function(){ closewindow(options.importbtn) }, 1000);
			}
			if(notes.length){
				var ul = $('<ul class="wrap">');
				$.each(notes,function(j,note){ ul.append($('<li>').append(note)); });
				setTimeout(function(){ makewindow('File import warnings',['<br>',ul,'<br>'],{btn:'OK',icn:'info.png'}); }, 1500); 
			}
		};
		
		if(options.mode=='importcdna'){ model.dnasource(Tsequences); feedback(); return true; }
		else if(options.mode=='noimport'){ feedback(); return true; }
		
		if(options.container){ //import to container
			options.container()[0].imported = {sequences: seqnames.length?Tsequences:'', tree: treeobj.data, type: seqstats.type||'', alignlen: seqstats.alignlen||'', ftype: datatype};
			feedback(); return true;
		}
	
		//import to globals & render data
		sequences = Tsequences; Tsequences = '';
		treesvg = treeobj.data? treeobj : {}; treeobj = '';
		leafnodes = {};
		model.clearundo();
		if(treesvg.data && settingsmodel.undo()){
			setTimeout(function(){ model.treebackup = treesvg.data.root.removeAnc().write('undo'); }, 100);
		}
		model.treesource(treesvg.data? Ttreesource : '');
		model.treealtered(false);
		model.noanc(false);
		model.dnasource('');
		model.ensinfo(ensinfo);
		
		var newcolors = false;
		if(seqnames.length){ //fill sequence data globals
			if(seqstats.type=='DNA') model.dnasource(sequences);
			if(seqstats.type!=model.seqtype()) newcolors = true;
			model.seqtype(seqstats.type); model.hasdot(seqstats.hasdot);
			model.totalseqlen(seqstats.totallen); model.alignlen(seqstats.alignlen); model.seqcount(seqnames.length);
			model.minseqlen(seqstats.minseqlen); model.maxseqlen(seqstats.maxseqlen);
			model.seqsource(Tseqsource); maskedcols = [];
			if(visiblecols.length) model.visiblecols(visiblecols);
			else{ //mark all columns visible
				for(var c=model.alignlen(), colarr=[]; c--;) colarr[c] = c;
				model.visiblecols(colarr);
			}
		}
				
		if(!treesvg.data && seqnames.length){ //no tree: fill tree placeholders
			var visrows = [];
			$.each(seqnames,function(indx,seqname){
				leafnodes[seqname] = {name:seqname};
				if(nodeinfo[seqname]) leafnodes[seqname].ensinfo = nodeinfo[seqname];
				visrows.push(seqname); 
			});
			model.visiblerows(visrows);
			model.leafcount(seqnames.length);
		}
		
		dom.wrap.css('left',0); dom.seq.css('margin-top',0); dom.treewrap.css('top',0); //reset scroll
		dom.tree.empty(); dom.names.empty();
		
		var redrawopt = {firstrun:true};
		$.each(importsettings,function(sn,s){ //restore library-item-specfic state settings
			if(sn=="model.seqtype" && s=="codons" && model.isdna()){ //translate dna=>codons
				Tsequences = {};
				$.each(sequences,function(name,seqarr){
					var tmpseq = [];
					for(var col=0; col<seqarr.length; col+=3){
						tmpseq.push(seqarr.slice(col,col+3).join(''));
					}
					Tsequences[name] = tmpseq;
					delete sequences[name];
				});
				sequences = Tsequences; Tsequences = '';
				model.seqtype("codons");
			}
			if(sn=="position") redrawopt.position = s;  //scroll position
			else if(~sn.indexOf(".") && eval(sn)) eval(sn+"("+JSON.stringify(s)+")");  //new model value
		});
		
		if(options.id){ //(shared) library dataset
			var libitem = librarymodel.getitem(options.id);
			if(libitem){ //analysis found in library. update timestamp
				options.name = unwrap(libitem.name);
				if(libitem.shared) options.source = 'shared data';
				else setTimeout(function(){ communicate('writemeta', {id:options.id, key:'imported'}) }, 2000);
			} else options.source = 'shared data';
		}
		var filename = filenames.length? filenames[0].split('.')[0].replace(/_/g,' ') : '';
		exportmodel.savename(options.name||filename||'Untitled analysis'); //initial name
		librarymodel.openid(options.id||''); //libitem updates name
		
		if(options.source){ //data source > model
			var src = options.source;
			var sourcetype = src=='localread'||src=='upload'? 'local computer' : ~src.indexOf('import')? 'analysis library' : src=='download'? options.importurl? 'web address' : 'text input' : src;
			model.sourcetype(sourcetype);
		}
		librarymodel.importurl = options.importurl||'';
		
		if(treesvg.data) treesvg.refresh(redrawopt); //render tree (& seq.); fill leafnodes[], visiblerows[], model.leafcount()
		else redraw(redrawopt);
		
		if(treesvg.data && seqnames.length){ //check tree<=>seq data match
			if(treesvg.data.root.children.length<3) model.noanc(true);
			var emptyleaves = [];
			$.each(leafnodes,function(name,node){
				if(!sequences[name]){ emptyleaves.push(name); node.active = true; }
				else node.active = false;
			});
			if(emptyleaves.length){
				var leafsnote = emptyleaves.length+' out of '+Object.keys(leafnodes).length+' tree leaves have no sequence';
				leafsnote += emptyleaves.length<5? ':<br>'+emptyleaves.join(', ') : '.';
				var clearbtn = $('<a class="button square small">Delete all sequences</a>');
				clearbtn.click(function(){
					librarymodel.openid(''); sequences = {}; redraw(); 
					closewindow(this);
				});
				var prunebtn = $('<a class="button square small">Prune empty leaves</a>');
				prunebtn.click(function(){
					toolsmodel.processLeafs('remove',emptyleaves.length); 
					closewindow(this);
				});
				leafsnote = $('<span>'+leafsnote+'<br><br></span>').append(clearbtn);
				if(Object.keys(leafnodes).length-emptyleaves.length>3) leafsnote.append(prunebtn);
				notes.push(leafsnote);
			}
		}
		
		feedback(); //show 'imported'
		return true;
	}//no errors => import data
}//parseimport()

//search for ensembl gene id
function ensemblid(ensdata){
	var ensbtn = document.getElementById('ensidbtn');
	if(!ensdata){ //send request
		if(!ensemblmodel.idspecies()||!ensemblmodel.idname()) return;
		var urlstring = ('http://rest.ensembl'+ensemblmodel.genomes()+'.org/xrefs/symbol/'+ensemblmodel.idspecies()+'/'+ensemblmodel.idname()+'?content-type=application/json;object=gene').replace(/ /g,'+');
		communicate('geturl',{fileurl:urlstring},{success:function(data){ensemblid(data)},btn:ensbtn,retry:true,restore:true});
		return false;
	}
	//process data
	try{ ensdata = JSON.parse(ensdata); } catch(e){
		if(~ensdata.indexOf('BaseHTTP')) ensdata = {error:'Server communication error.'};
		else ensdata = {error:'No match. Try different search.'};
	}
	if($.isArray(ensdata) && !ensdata.length) ensdata = {error:'No match. Try different search.'};
	if(ensdata.error){
		ensbtn.innerHTML = 'Error';
		$('#enserror').text(ensdata.error||'Unknown error. Try again.'); $('#enserror').fadeIn();
		setTimeout(function(){ ensbtn.innerHTML = 'Search'; $('#enserror').fadeOut(); },4000);
		return false;
	}
	else if(ensdata[0].type == 'gene'){
		ensemblmodel.ensid(ensdata[0].id);
		ensbtn.innerHTML = 'Got ID';
		setTimeout(function(){ ensbtn.innerHTML = 'Get ID'; },2000);
	}
	return false;
}

//import ensembl data
function ensemblimport(){
	importedFiles([]);
	var idformat = ensemblmodel.idformat().url;
	var ensid = ensemblmodel.ensid() || ensemblmodel.idformat().example;
	var ensbtn = document.getElementById('ensbtn');
	var showerror = function(msg){ //display error message next to import button
		ensbtn.innerHTML = 'Error';
		$('#enserror').text(msg||'Unknown error. Try again.'); $('#enserror').fadeIn();
		setTimeout(function(){ ensbtn.innerHTML = 'Import'; $('#enserror').fadeOut(); },4000);
		return false;
	}
	var urlopt = ~idformat.indexOf('homology')? '?content-type=application/json' : '?content-type=text/x-phyloxml';
		
	if(ensemblmodel.isblock()){
		ensid = ensid.replace(/-/,'..')
		var marr = ensid.match(/(\w+):(\d+)\.\.(\d+)/);
		if(!marr) return showerror('Sequence region in wrong format.');
		var start = parseInt(marr[2]), end = parseInt(marr[3]);
		if(end<start || end-start>10000000) return showerror('Max. region length is 10Mb.');
		ensid = ensemblmodel.blockref()+'/'+ensid;
		urlopt += ';method='+ensemblmodel.blocktype().type+';species_set_group='+ensemblmodel.blockset().name.toLowerCase();
		if(ensemblmodel.mask()) urlopt += ';mask='+ensemblmodel.mask();
	} else {
		if(~idformat.indexOf('homology')){
			urlopt += ';type='+ensemblmodel.homtype();
			if(ensemblmodel.target()) urlopt += ';target_species='+ensemblmodel.target();
		}
		else{
			if(!~ensid.indexOf('GT')) idformat = 'genetree/member/id/';
		}
		urlopt += ';sequence='+ensemblmodel.seqtype();
	}
	
	if(ensemblmodel.aligned()) urlopt += ';aligned=1';
	if(ensemblmodel.genomes()) urlopt += ';compara='+ensemblmodel.compara();
	
	var urlstring = ('http://rest.ensembl'+ensemblmodel.genomes()+'.org/'+idformat+ensid+urlopt).replace(/ /g,'+');
	var processdata = function(ensdata){
		try{ ensdata = JSON.parse(ensdata); } catch(e){ if(~ensdata.indexOf('BaseHTTP')) return showerror('Server communication error.'); }
		if(typeof(ensdata)=='object'){ //JSON => gene homology data
			if(!ensdata.data) return showerror('Received data is in unexpected format.');
			importedFiles.push({name:ensid+'.json', data:ensdata, type:'seq:json'});
		} else { //XHTML => genetree & alignments data
			if(!~ensdata.indexOf('phyloxml')) return showerror('Received data is in unexpected format.');
			importedFiles.push({name:ensid+'.xml', data:ensdata, type:'seq:phyloxml tree:phyloxml'});
		}
		setTimeout(function(){ parseimport({source:'Ensembl',importbtn:$(ensbtn),importurl:urlstring,ensinfo:{type:idformat,id:ensid}}) },600);
	}
	//reqest data, then process it
	communicate('geturl',{fileurl:urlstring},{success:processdata, btn:ensbtn, btntxt:'Import', restorefunc:ensemblimport, retry:true});
	return false; //for onclick
}

//Output file parsing
function parseexport(filetype, options){
	var usemodel = false;
	if(typeof(filetype)=='object'){ if(!options) options = filetype; filetype = ''; }
	if(!filetype && !options){ //use input from export window
		usemodel = true;
		exportmodel.fileurl('');
		filetype = exportmodel.format().name;
		options = {};
		options.tags = exportmodel.variant().name && (exportmodel.variant().name=='extended newick');
		$.each(['masksymbol','includeanc','includehidden','truncsymbol','trunclen'], function(i,opt){
			options[opt] = exportmodel[opt]();
		});
	} else if(!options) var options = {};

	if(filetype=='extended newick'){ filetype = 'newick'; options.tags = true; }
	var nameids = options.nameids||{};
	var seqsource = options.usedna&&translateseq('protein','check')? model.dnasource() : sequences;
	var treesource = treesvg.data;
	var output = '', ids = [], regexstr = '', dict = {}, seqtype = model.seqtype();
	var datatype = options.datatype || exportmodel.category().name || 'sequence tree';
	datatype = datatype.toLowerCase();
	
	var leafnames = [], visiblecols = model.visiblecols();
	$.each(leafnodes,function(leafname,obj){ if(obj.type!='ancestral') leafnames.push(leafname) });
	var names = options.includeanc? Object.keys(sequences) : leafnames;
	var specount = names.length, ntcount = options.includehidden? model.alignlen() : model.visiblecols().length;
	
	if(typeof(options.container)=='object'){ //IO=>plugin file container
		seqsource = options.container.sequences;
		seqtype = options.container.type;
		names = Object.keys(seqsource);
		specount = names.length;
		ntcount = options.container.alignlen;
		treesource = options.container.tree;
		visiblecols = [];
		if(ntcount){ for(var c=ntcount; c--;) visiblecols[c] = c; }
	}
	
	var parsename = function(name){ //simplify seq. names
		if(options.makeids || filetype=='HSAML') return '';
		var pat = {'space':'\\s','digit':'\\d'};
		var exp = new RegExp(options.truncsymbol?(pat[options.truncsymbol]||'[^A-Za-z0-9 ]'):'');
		var ind = name.match(exp); ind = ind? ind.index : 0;
		var maxlen = parseInt(options.trunclen) || 0;
		var len = ind && (!maxlen||ind<maxlen)? ind : maxlen;
		name = name.replace(/\s+/g, '_');
		return len? name.substring(0,len) : name;
	};
	
	//sequence letter replacements
	if(options.masksymbol && options.masksymbol!='lowercase'){ $.each(alphabet[seqtype],function(i,symbol){ //translation for masked positions
		if(seqtype=='codons') symbol = i;
		if(symbols[symbol].masked) dict[symbols[symbol].masked] = options.masksymbol;
	});}
	if(filetype!='HSAML' && model.hasdot()) dict['.'] = '-';
	if(options.gapsymbol) dict['-'] = dict['.'] = options.gapsymbol;
	$.each(dict,function(symbol){ regexstr += symbol; });
	var regex = regexstr ? new RegExp('['+regexstr+']','g') : '';
	var translate = regexstr ? function(s){ return dict[s] || s; } : '';
	
	//sequence parsing
	var parseseq = function(seqname){ //seqarr=>seqstr=>conversion
		var seqarr = seqsource[seqname], seqstr = '';
		if(!options.includehidden){ $.each(visiblecols,function(i,pos){ if(pos==seqarr.length){ return false; } seqstr += seqarr[pos]; }); }
		else seqstr = seqarr.join('');
		return regex? seqstr.replace(regex,translate) : seqstr;
	};
	
	if(filetype!='newick'){ //seq data => Map seq names
		var seqi=0, parenti=0, tempid='';
		if(options.startid) seqi = parseInt(options.startid.replace(/\D+/,''));
		$.each(names,function(j,name){
			//if(~leafnames.indexOf(name)){ seqi++; tempid = truncname || 'sequence'+seqi; }
			//else { parenti++; tempid = truncname || 'parent'+parenti; }
			seqi++;
			tempid = parsename(name) || 'seq'+seqi;
			nameids[name] = tempid; 
		});
	}
	
	//output newick
	var parsetree = function(){ return treesource? treesource.root.write(options.tags, !Boolean(options.includeanc), nameids) : ''; };
	
	
	var seqline = '';
	if(filetype=='fasta'){
		$.each(names,function(j,name){
			output += '>'+(nameids[name]||name)+"\n";
			seqline = parseseq(name);
			for(var c=0;c<seqline.length;c+=50){ output += seqline.substr(c,50)+"\n"; }
		});
	}
	else if (filetype=='HSAML'){
		output = "<ms_alignment>\n";
		if(~datatype.indexOf('tree')) output += "<newick>\n"+parsetree()+"</newick>\n";
		
		output += "<nodes>\n"; var isleaf;
		$.each(names,function(j,name){
			isleaf = ~leafnames.indexOf(name);
			seqline = parseseq(name);
		var xmlnode = isleaf? "\t<leaf " : "\t<node ";
		xmlnode += "id=\""+(nameids[name]||name)+"\" name=\""+name+"\">\n\t\t<sequence>\n\t\t"+seqline+"\n\t\t</sequence>\n"+(isleaf?"\t</leaf>\n":"\t</node>\n");
		output += xmlnode;
		});
		output += "</nodes>\n";
		output += "</ms_alignment>";
	}
	else if(filetype=='phylip'){
		output = specount+" "+ntcount+"\n";
		$.each(names,function(j,name){
			seqline = parseseq(name);
			output += (nameids[name]||name)+"\n"+seqline+"\n";	
		});
	}
	else if(filetype=='NEXUS'){
		output = "#NEXUS\n";
		if(~datatype.indexOf('sequence')){
			output += "BEGIN DATA;\n";
			output += "Dimensions NTax="+specount+" NChar="+ntcount+";\n";
			if(seqtype=='codons') seqtype = 'nucleotide';
			output += "Format DataType="+seqtype+" Gap=- Missing=?;\nMatrix\n";
			$.each(names,function(j,name){
				seqline = parseseq(name);
				output += (nameids[name]||name)+" "+seqline+"\n";	
				});
				output += ";\nEND;\n";
		}
		if(~datatype.indexOf('tree')){
			output += "BEGIN TREES;\n";
			output += "Tree tree1 = "+parsetree();
			output += "END;\n";
		}
	}
	else if(filetype=='newick'){ output = parsetree(); }
	
	if(usemodel||options.exportdata){ //export data to exportwindow & make download url
		if(options.exportdata){
			if(typeof(options.exportdata)=='object'){
				if(options.exportdata.data) output = options.exportdata.data;
				else if(typeof(options.exportdata.imported)=='object'){
					if(options.exportdata.imported.sequences){
						output = "Sequence data:\n"; var i=0;
						$.each(options.exportdata.imported.sequences,function(n,seq){
							if(i<10) output += n+": "+seq.join('')+"\n";
							else if(i==10) output += "..."+(Object.keys(options.exportdata.imported.sequences).length-10)+" sequences not shown...\n";
							else return false;
							i++;
						});
					}
					if(options.exportdata.imported.tree) output += "\nTree data:\n"+options.exportdata.imported.tree.root.write();
				}
				filename = options.exportdata.name || 'exported_data.txt'
			} else { output = options.exportdata; filename = options.filename||'exported_data.txt'; }
			exportmodel.filename(filename);
		} else filename = exportmodel.filename()+exportmodel.fileext();
		$('#exportpaper').text(output);
		$('#export').addClass('flipped');
		if(usemodel && !model.offline() && !model.noaccount()) communicate('makefile',{filename:filename.replace(' ','_'),filedata:output},{saveto:exportmodel.fileurl});
	}
	else if(options.exporturl){ //export server file to exportwindow
		$.get(options.exporturl,function(txt){$('#exportpaper').text(txt)},'text');
		$('#export').addClass('flipped');
		exportmodel.fileurl(options.exporturl);
		exportmodel.filename(parseurl(options.exporturl).file||'');
	}
	if(options.exporturl || options.snapshot || options.exportdata) $('#export a.backbtn').css('display','none');
	
	if(options.makeids) output = {file:output, nameids:nameids, endid:tempid};
	if(options.container){ delete options.container.sequence; delete options.container.tree; }
	
	_paq.push(['trackEvent','export',filetype]); //record event
	return output;
}

//== Rendrering functions for tree & sequence alignment areas ==//
//generate sequence colors according to selected colorscheme
function makeColors(){
	colors = []; symbols = {};
	if(!settingsmodel) return;
	var colorscheme = settingsmodel.colorscheme(), seqtype = model.seqtype();
	if(colorscheme!='rainbow' && colorscheme!='greyscale'){
		if(colorscheme=='nucleotides'){  //{AA:[txtColor,bgColor]}
			colors = {A:['','rgb(0,0,255)'], T:['','rgb(255,255,0)'], G:['','rgb(0,255,0)'], C:['','rgb(255,0,0)'], U:['','rgb(255,255,0)']};
		}
		else if(colorscheme=='Taylor'){
			colors = { A:['','rgb(204,255,0)'], R:['','rgb(0,0,255)'], N:['','rgb(204,0,255)'], D:['','rgb(255,0,0)'], C:['','rgb(255,255,0)'], Q:['','rgb(255,0,204)'], E:['','rgb(255,0,102)'], G:['','rgb(255,153,0)'], H:['','rgb(0,102,255)'], I:['','rgb(102,255,0)'], L:['','rgb(51,255,0)'], K:['','rgb(102,0,255)'], M:['','rgb(0,255,0)'], F:['','rgb(0,255,102)'], P:['','rgb(255,204,0)'], S:['','rgb(255,51,0)'], T:['','rgb(255,102,0)'], W:['','rgb(0,204,255)'], Y:['','rgb(0,255,204)'], V:['','rgb(153,255,0)'], B:['','rgb(255,255,255)'], Z:['','rgb(255,255,255)'], X:['','rgb(255,255,255)']};
		}
		else if(colorscheme=='Clustal'){
			colors = {A:['','rgb(128,160,240)'], R:['','rgb(240,21,5)'], N:['','rgb(0,255,0)'], D:['','rgb(192,72,192)'], C:['','rgb(240,128,128)'], Q:['','rgb(0,255,0)'], E:['','rgb(192,72,192)'], G:['','rgb(240,144,72)'], H:['','rgb(21,164,164)'], I:['','rgb(128,160,240)'], L:['','rgb(128,160,240)'], K:['','rgb(240,21,5)'], M:['','rgb(128,160,240)'], F:['','rgb(128,160,240)'], P:['','rgb(255,255,0)'], S:['','rgb(0,255,0)'], T:['','rgb(0,255,0)'], W:['','rgb(128,160,240)'], Y:['','rgb(21,164,164)'], V:['','rgb(128,160,240)'], B:['','rgb(255,255,255)'], X:['','rgb(255,255,255)'], Z:['','rgb(255,255,255)']};
		}
		else if(colorscheme=='Zappo'){
			colors = {A:['','rgb(255,175,175)'], R:['','rgb(100,100,255)'], N:['','rgb(0,255,0)'], D:['','rgb(255,0,0)'], C:['','rgb(255,255,0)'], Q:['','rgb(0,255,0)'], E:['','rgb(255,0,0)'], G:['','rgb(255,0,255)'], H:['','rgb(100,100,255)'], I:['','rgb(255,175,175)'], L:['','rgb(255,175,175)'], K:['','rgb(100,100,255)'], M:['','rgb(255,175,175)'], F:['','rgb(255,200,0)'], P:['','rgb(255,0,255)'], S:['','rgb(0,255,0)'], T:['','rgb(0,255,0)'], W:['','rgb(255,200,0)'], Y:['','rgb(255,200,0)'], V:['','rgb(255,175,175)'], B:['','rgb(255,255,255)'], X:['','rgb(255,255,255)'], Z:['','rgb(255,255,255)']};
		}
		else if(colorscheme=='hydrophobicity'){
			colors = {A:['','rgb(173,0,82)'], R:['','rgb(0,0,255)'], N:['','rgb(12,0,243)'], D:['','rgb(12,0,243)'], C:['','rgb(194,0,61)'], Q:['','rgb(12,0,243)'], E:['','rgb(12,0,243)'], G:['','rgb(106,0,149)'], H:['','rgb(21,0,234)'], I:['','rgb(255,0,0)'], L:['','rgb(234,0,21)'], K:['','rgb(0,0,255)'], M:['','rgb(176,0,79)'], F:['','rgb(203,0,52)'], P:['','rgb(70,0,185)'], S:['','rgb(94,0,161)'], T:['','rgb(97,0,158)'], W:['','rgb(91,0,164)'], Y:['','rgb(79,0,176)'], V:['','rgb(246,0,9)'], B:['','rgb(12,0,243)'], X:['','rgb(104,0,151)'], Z:['','rgb(12,0,243)']};
		}
	}
	colors['-']=['#ccc','rgb(255,255,255)'];colors['.']=['#e3e3e3','rgb(255,255,255)'];colors['?']=['#f00','rgb(255,255,255)'];
	if(model.hasdot()) colors['-'][0] = '#999'; //darker del. symbol
	var maskc = settingsmodel.maskcolor(), maskuc = settingsmodel.maskletter()=='uppercase'; //masked bg settings
	
	var shadecolor = function(color,shade){ //make colors for masked/ancestral sites
		if(shade=='white') return 'rgb(255,255,255)';
		return mixcolors(color, shade=='light'?[255,255,255]:[100,100,100]); //default shade=dark
	}
	
	for(var i=0;i<letters.length;i++){ //define colors for all alphabet letters (dna&protein, upper&lowercase)
		var symbol = letters[i], unmasked = i%2==0, color = 'rgb(255,255,255)';
		if(i>8 && !unmasked) canvassymbols[symbol] = maskuc? letters[i-1] : false; //canvas letter for masked symbols
		if(colorscheme=='rainbow' || colorscheme=='greyscale'){ //generate all colors
			color = unmasked? rainbow(letters.length,i,colorscheme) : shadecolor(rainbow(letters.length,i-1,colorscheme),maskc);
			if(!colors[symbol]) colors[symbol] = ["",color];
		}
		else if(!colors[symbol]){ //generate missing colors in predefined colorscheme
			colors[symbol] = unmasked? ['','rgb(200,200,200)'] : ['',shadecolor(colors[letters[i-1]][1],maskc)];
		}
		
		var rgb = colors[symbol][1].match(/\d{1,3}/g); //adjust letter color for bg brightness
		var brightness = Math.sqrt(rgb[0]*rgb[0]*.241 + rgb[1]*rgb[1]*.691 + rgb[2]*rgb[2]*.068);
		var fgcolor = brightness<120 ? '#eee' : '#333';
		if(!colors[symbol][0]){ colors[symbol][0] = unmasked? fgcolor : (maskc=='dark'?'#eee':'#888'); }
		
		symbols[symbol] = { 'fgcolor' : colors[symbol][0], 'bgcolor' : colors[symbol][1] };
		symbols[symbol].masked = unmasked ? letters[i+1] : symbol;
		symbols[symbol].unmasked = unmasked ? symbol : letters[i-1];
	} //Result: symbols = { A:{fgcolor:'#ccc',bgcolor:'#fff',masked:'a',unmasked:'A'}, a:{fgcolor,..}}
	
	if(seqtype=='codons'){  //remap colors to codon colors
		var codonsymbols = {};
		$.each(alphabet.codons, function(codon,aa){
			var maskaa = symbols[aa].masked, maskcodon = codon.toLowerCase();
			codonsymbols[codon] = $.extend({}, symbols[aa]); //copy data object
			codonsymbols[maskcodon] = $.extend({}, symbols[maskaa]);
			codonsymbols[codon].masked = codonsymbols[maskcodon].masked = maskcodon;
			codonsymbols[codon].unmasked = codonsymbols[maskcodon].unmasked = codon;
		});
		$.each(alphabet.gaps, function(i,gap){
			var maskgap = symbols[gap].masked, codon = gap+gap+gap;
			var maskcodon = maskgap+maskgap+maskgap;
			codonsymbols[codon] = $.extend({}, symbols[gap]);
			codonsymbols[codon].masked = maskcodon;
			codonsymbols[codon].unmasked = codon;
		});
		symbols = codonsymbols;
	}
	
	var ancc = settingsmodel.anccolor(), newc = ancc!='colorscheme', anclc = settingsmodel.ancletter()=='lowercase'; //settings
	if(newc || anclc){  //additional colors for ancestral sites
		var sym='', m='', afc=ancc=='dark'?'#eee':'#888';
		$.each(Object.keys(symbols),function(j,s){
			sym = symbols[s]; m = s==sym.masked; 
			symbols[s+'_anc'] = {fgcolor: m||!newc?sym.fgcolor:afc, bgcolor: m||!newc?sym.bgcolor:shadecolor(sym.bgcolor,ancc)};
			canvassymbols[s+'_anc'] = anclc?sym.masked:s;
		}); 
	} else { $.each(Object.keys(symbols),function(j,s){ if(~s.indexOf('_anc')) symbols[s] = canvassymbols[s] = false; }); }
	makeCanvases();
}

//Note: a color palette: http://jsfiddle.net/k8NC2/1/ jalview color schemes
//Generates vibrant, evenly spaced colors. Adapted from blog.adamcole.ca
function rainbow(numOfSteps,step,colorscheme){
    var r, g, b;
    var h = step / numOfSteps;
    var i = ~~(h * 6);
    var f = h * 6 - i;
    var q = 1 - f;
    switch(i % 6){
        case 0: r = 1, g = f, b = 0; break;
        case 1: r = q, g = 1, b = 0; break;
        case 2: r = 0, g = 1, b = f; break;
        case 3: r = 0, g = q, b = 1; break;
        case 4: r = f, g = 0, b = 1; break;
        case 5: r = 1, g = 0, b = q; break;
    }
    if(colorscheme=='greyscale') r = g = b = (r+g+b)/3;
    return 'rgb('+parseInt(r*255)+','+parseInt(g*255)+','+parseInt(b*255)+')';
}

//shade colors (masking)
function mixcolors(color,mix){
	var rgb = color.match(/\d{1,3}/g);
	var r = Math.floor((parseInt(rgb[0])+(2*mix[0]))/3);
	var g = Math.floor((parseInt(rgb[1])+(2*mix[1]))/3);
	var b = Math.floor((parseInt(rgb[2])+(2*mix[2]))/3);
	return "rgb("+r+","+g+","+b+")";
}

//(re)render sequence & tree canvas
var zoomtimer = 0;
function redraw(options){
	if(!options) options = {};
	if(!options.position) options.position = {};
	if(options.zoom){
		var zlevel = model.zoomlevel();
		if(options.zoom=='in' && zlevel<model.zlevels.length-1) model.zoomlevel(zlevel+1);
		else if(options.zoom=='out' && zlevel>0) model.zoomlevel(zlevel-1);
		else if(typeof(options.zoom)=='string') return false;
		clearTimeout(zoomtimer);
	}
	canvaslist = []; colflags = []; rowflags = []; model.activeid(''); //clear selections and its flags
	$("#seq div[id*='selection'],#seq div[id*='cross']").remove();
	$label = $("#namelabel"); $labelspan = $("#namelabel span");
	
	if(options.firstrun){ //new data imported: prepare tree area
		if(treesvg.data){ //make tree SVG
			var svg = $("#tree>svg,#names>svg");
			svg.mousedown(function(e){ //handle nodedrag on tree
				e.preventDefault();
				var draggedtag = e.target.tagName;
				if(draggedtag=='circle' || draggedtag=='text'){
					var nodeid = parseInt(e.target.getAttribute('nodeid'));
					var draggednode = treesvg.data.root.getById(nodeid);
					if(!draggednode) return;
					$("body").one('mouseup',function(){ $("body").unbind('mousemove'); });
					var startpos = {x:e.pageX,y:e.pageY}, dragmode = false, helper;
					$("body").mousemove(function(evt){
						var dx = evt.pageX-startpos.x, dy = evt.pageY-startpos.y;
						if(Math.sqrt(dx*dx+dy*dy)>7){
							if(!dragmode){
								helper = movenode('drag',draggednode,draggedtag);
								dragmode = true;
							}
							if(helper) helper.css({left:evt.pageX+15,top:evt.pageY});
						}
			}); } });
		} else { //no tree: make tree/leafname placeholders	
			$.each(model.visiblerows(),function(n,name){
				var leafname = leafnodes[name].ensinfo? leafnodes[name].ensinfo.species : name;
				var nspan = $('<span style="height:'+model.boxh()+'px;font-size:'+model.fontsize()+'px;cursor:pointer">'+leafname+'</span>');
				
				var hovertimer;
				nspan.mouseenter(function(){ //show full leaf name on mouseover
					rowborder({y:n*model.boxh()},'keep'); //show row highlight
					hovertimer = setTimeout(function(){ //show hidden part of name
						var cssobj = {'font-size': model.fontsize()+'px', 'top': nspan.offset().top+'px', 'left': $("#right").position().left-16+'px'};
						$label.css(cssobj);
						$labelspan.css('margin-left',0-dom.names.innerWidth()+6+'px'); $labelspan.text(leafname);
						$label.fadeIn(100);
					},800);
				});
				nspan.mouseleave(function(){ 
					clearTimeout(hovertimer);
					$label.fadeOut(100); 
				});
				//seq. name menu
				nspan.click(function(){
					var ens = leafnodes[name].ensinfo, mtitle = '';
					var nmenu = {'Delete': {t:'Remove this sequence', icon:'trash', 
						click:function(){ model.visiblerows.remove(name); delete leafnodes[name]; delete sequences[name]; nspan.remove(); redraw(); }}};
					if(ens){ //show ensembl metadata in the menu
						mtitle = ens.genetype;
						if(ens.taxaname) nmenu['<span class="note">Taxa</span> '+ens.taxaname] = '';
						if(ens.cladename&&ens.species) nmenu['<span class="note">Gene</span> '+
						'<a href="http://www.ensembl.org/'+ens.species.replace(' ','_')+
						'/Gene/Summary?g='+ens.cladename+'" target="_blank" title="View in Ensembl">'+ens.cladename+'</a>'] = '';
						if(ens.accession&&ens.species) nmenu['<span class="note">Protein</span> '+
						'<a href="http://www.ensembl.org/'+ens.species.replace(' ','_')+'/Transcript/ProteinSummary?p='+
						ens.accession+'" target="_blank" title="View in Ensembl">'+ens.accession+'</a>'] = '';
					}
					setTimeout(function(){ tooltip('', mtitle, {clear:true, arrow:'top', data:nmenu, 
						target:{ x:$("#names").offset().left, y:nspan.offset().top, width:$("#names").width(), height:model.boxh()}, style:'black' }) },100);
				});
				
				dom.names.append(nspan);
			});
		}
	} //afterimport
	
	var newheight = model.visiblerows().length ? model.visiblerows().length*model.boxh() : model.leafcount()*model.boxh();
	if(model.boxw()<4){ dom.treewrap.addClass('minimal'); } else { dom.treewrap.removeClass('minimal'); }
	if(!options.zoom){ dom.treewrap.css('height',newheight); $("#names svg").css('font-size',model.fontsize()+'px'); }
	if(dom.treewrap.css('display')=='none') dom.treewrap.css('display','block');
	
	var renderseq = function(){ //draws sequence canvas
		if(!$.isEmptyObject(sequences) && !options.treeonly){
			makeRuler(); makeColors(); makeImage();
		}
		else if($.isEmptyObject(sequences) && !options.zoom){ //no sequence data
			model.visiblecols.removeAll(); model.seqsource(''); model.dnasource('');
			$('#seq .tile').remove(); $('#ruler').empty();
		}
		//set up scrollbars
		if(!dom.seqwindow.data("contentWidth")) mCustomScrollbar();
		else{ $(window).trigger('resize'); }
	};
	
	//calculate new sequence/tree canvas position
	var makezoom = Boolean(options.zoom && !options.refresh);
	var oldwidth = parseInt(dom.seq.css('width'))||1;
	var seqw = dom.seqwindow.innerWidth();
	var newwidth = model.visiblecols().length*model.boxw();
	var left = parseInt(options.position.left||dom.wrap.css('left'));
	if(makezoom && !$.isEmptyObject(sequences)) left = Math.round(((newwidth/oldwidth)*(left-(seqw/2)))+(seqw/2));
	var top = parseInt(options.position.top||dom.seq.css('margin-top'));
	var oldheight = parseInt(dom.seq.css('height'))||1;
	var visibleHeight = $("#left").height();
	if(makezoom) top = Math.round(((newheight/oldheight)*(top-(visibleHeight/2)))+(visibleHeight/2));
	if(options.leftscale) left = parseInt(left*options.leftscale);
	//check boundaries
	if(top<0 && newheight>visibleHeight && Math.abs(top)>newheight-visibleHeight) top = visibleHeight-newheight; //new bottom limit
	if(top>0||newheight<visibleHeight) top = 0; //stick to top
	if(Math.abs(left)>newwidth-seqw) left = seqw-newwidth;
	if(left>0) left = 0;
	//reposition and render sequence canvas
	if(options.zoom && !options.refresh){ //keep currently visible sequence in center of viewport after zoom
		if(!$.isEmptyObject(sequences)){
			dom.seq.animate({opacity:0}, {duration:200, complete: function(){
				dom.seq.empty().append('<div id="rborder" class="rowborder">');
				dom.seq.css({'width':newwidth, 'height':newheight, 'margin-top':top, opacity:1});
				dom.wrap.css('left',left);
			}});
			$("#spinner").addClass('show');
		}
		
		dom.treewrap.animate({height:newheight, top:top},
			{duration:400, complete: function(){ zoomtimer = setTimeout(function(){ renderseq(); }, 600);}
		});
		if(!$.isEmptyObject(treesvg)) $("#names svg").css('font-size',model.fontsize()+'px');
		else $("#names span").css({height:model.boxh(),'font-size':model.fontsize()+'px'});
	}
	else { //keep current sequence position after rerender
		dom.seq.empty().append('<div id="rborder" class="rowborder">'); 
		dom.seq.css({width:newwidth, height:newheight});
		dom.seq.css('margin-top', top);
		dom.treewrap.css('top',top);
		dom.wrap.css('left', left);
		renderseq();
	}
}

//redraw tree => sequence
function refresh(e){
	if(e){ e.stopPropagation(); $('html').click(); } //hide tooltips
	if(treesvg.refresh) treesvg.refresh();
};

//make a copy of a canvas element
function cloneCanvas(oldCanvas){
	var newCanvas = document.createElement('canvas');
	if(!oldCanvas) return newCanvas;
	newCanvas.width = oldCanvas.width;
	newCanvas.height = oldCanvas.height;
    var context = newCanvas.getContext('2d');
	context.drawImage(oldCanvas,0,0);
	return newCanvas;
}

//prebuild canvas pieces (letter boxes)
function makeCanvases(){ //make canvases for sequence letters
	var x = 0, y = 0, w = model.boxw(), h = model.boxh(), r = parseInt(w/5), fontzise = model.fontsize();
	if(w>1 && settingsmodel.boxborder()=='border'){ x++; y++; w--; h--; }
	$.each(symbols,function(symbol,data){
		var tmpel = document.createElement('canvas');
		tmpel.width = model.boxw();
		tmpel.height = model.boxh();
		var tmpcanv = tmpel.getContext('2d');
		tmpcanv.fillStyle = data.bgcolor;
		tmpcanv.fillRect(x,y,w,h);
		
		if(fontzise > 7){ //draw characters
			tmpcanv.font = fontzise+'px '+settingsmodel.font();
			tmpcanv.textAlign = 'center';
			tmpcanv.textBaseline = 'middle';
			tmpcanv.fillStyle = data.fgcolor;
			if(fontzise > 12){ //font shadow
				if(data.fgcolor=="#eee"){
					tmpcanv.shadowColor = "#111";
					tmpcanv.shadowOffsetX = 0;
					tmpcanv.shadowOffsetY = 1.5;
					tmpcanv.shadowBlur = 1;
				}
				else if(data.fgcolor=="#333"){
					tmpcanv.shadowColor = "#fff";
					tmpcanv.shadowOffsetX = 0;
					tmpcanv.shadowOffsetY = -1;
					tmpcanv.shadowBlur = 1.5;
				}
			}
			var letters = canvassymbols[symbol]? [canvassymbols[symbol]] : symbol.split('');
			var colw = w/(letters.length+1);
			for(var l=0, letter=letters[l]; l<letters.length; l++, letter=letters[l]){ //print each (codon) letter
				if(canvassymbols[letter]) letter = canvassymbols[letter];
				tmpcanv.fillText(letter, colw*(l+1)+x, (h/2)+y);
			}
		}
		data['canvas'] = tmpel;
	});
	//$('#top>canvas').remove(); $.each(symbols,function(symb,data){$('#top').append(symb+':',data.canvas)}); //Debug
}

//render sequence tiles
var importstart = 0;
function makeImage(target,cleanup,slowfade,starttime){
	var d = new Date(), starttime = d.getTime();
	var targetx, targety, boxw = model.boxw(), boxh = model.boxh(), tilesize = {w:4000,h:2000};
	var colstep = parseInt(tilesize.w/boxw), rowstep = parseInt(tilesize.h/boxh); //tile size limits
	var visiblecols = model.visiblecols(), visiblerows = model.visiblerows();
	var fadespeed = slowfade? 400 : 100;
	if(target){
		var tarr = target.split(':');
		if(tarr[0]=='x'){ targetx = parseInt(tarr[1]); } else if(tarr[0]=='y'){ targety = parseInt(tarr[1]); }
	}
	if(!targetx){ if(!$("#wrap").position()) return; targetx = $("#wrap").position().left; }
	if(!targety){ targety = parseInt(dom.seq.css('margin-top')); }
	
	var colstartpix = parseInt((0-targetx)/boxw);
	var colstart = colstartpix-(colstartpix%colstep); //snap to (colstep-paced) tile grid
	var colend = parseInt((dom.seqwindow.innerWidth()-targetx)/boxw);
	if(colend>visiblecols.length) colend = visiblecols.length;
	
	var rowstartpix = parseInt((0-targety)/boxh);
	var rowstart = rowstartpix-(rowstartpix%rowstep); //snap to tile grid
	var rowend = parseInt(((dom.seqwindow.innerHeight()-$("#ruler").outerHeight())-targety)/boxh);
	if(rowend>visiblerows.length){ rowend = visiblerows.length; }
	
	if($('#seqtool').length) toolsmodel.hidelimit.valueHasMutated(); //seqtool window => update column preview
	var renderstart = 10, curcanvas = 0, lastcanvas = 0;
	var oldcanvases = $("#seq div.tile");
	var anccanvas = Boolean(symbols[Object.keys(symbols)[0]+"_anc"]);
	for(var row = rowstart; row<rowend; row+=rowstep){ //loop over canvas grid
	for(var col = colstart; col<colend; col+=colstep){
		if(canvaslist.indexOf(row+'|'+col)==-1){ //canvas not yet made
			if(curcanvas==0 && (rowend-rowstart)*(colend-colstart)>100000) $("#spinner").addClass('show'); //lots of sequence - show spinner
			canvaslist.push(row+'|'+col);
			lastcanvas++;
			
			setTimeout(function(r,c){ return function(){
				var canvasrow = r;
				var rstep = r+rowstep>visiblerows.length? visiblerows.length-r : rowstep;
				var cstep = c+colstep>visiblecols.length? visiblecols.length-c : colstep;
				var endrow = r+rstep;
				var endcol = c+cstep;
				var canvas = document.createElement('canvas');
				var tilediv = $('<div class="tile">');
				canvas.width = cstep*boxw;
				canvas.height = rstep*boxh;
				canvas.setAttribute('id', r+'|'+c);
				var canv = canvas.getContext('2d');		
				canv.fillStyle = 'white';
				canv.fillRect(0,0,canvas.width,canvas.height);
				
				while(canvasrow < endrow){ //draw rows of sequence to the tile
					var seqname = visiblerows[canvasrow], rowpx = (canvasrow - r)*boxh;
					if(!sequences[seqname]){ canvasrow++; continue; } //no sequence data: skip row
					for(var canvascol = c; canvascol<endcol; canvascol++){
						seqletter = sequences[seqname][visiblecols[canvascol]];
						if(!seqletter) continue; else if(!symbols[seqletter]) symbols[seqletter] = symbols['?']||symbols['???'];
						if(anccanvas && leafnodes[seqname].type=="ancestral") seqletter += '_anc'; //different canvas for ancestral
						canv.drawImage(symbols[seqletter]['canvas'], (canvascol - c)*boxw, rowpx); //draw the letter
					}
					canvasrow++;
				}
			
				tilediv.css({'left': c*boxw+'px', 'top': r*boxh+'px'});
				tilediv.append(canvas);
				dom.seq.append(tilediv);
				tilediv.fadeIn(fadespeed);
				curcanvas++;
				if(curcanvas==lastcanvas){ //last tile made => cleanup
					$("#spinner").removeClass('show');
					setTimeout(function(){ //remove obsolete tiles
						if(cleanup){ oldcanvases.remove(); }
					},1000);
				}
			}}(row,col),renderstart);
			renderstart += 500; //time tile renderings
			
		}//make canvas	
	}//for cols
	}//for rows
}

//make seqeuence area ruler bar
function makeRuler(){
	var $ruler = $("#ruler");
	$ruler.empty();
	var tick = 10, boxw = model.boxw(), tickw = tick*boxw-4, k = '', visiblecols = model.visiblecols();
	var markerdiv = function(scol,ecol){ //func. to make markers for hidden columns
		var gapindex = scol==0 ? 0 : visiblecols.indexOf(scol-1)+1;
		var l = gapindex*boxw-8;
		var colspan = ecol-scol;
		var sclass = colspan==1? 'small': colspan>5? 'big' : '';
		var div = $('<div class="marker '+sclass+'" style="left:'+l+'px">&#x25BC<div>|</div></div>');
		div.mouseenter(function(e){ tooltip(e,'Click to reveal '+colspan+' collapsed column'+(colspan==1?'':'s')+'.',{target:div[0]}) });
		div.click(function(){ showcolumns([[scol,ecol]],'hidetip'); redraw(); });
		div.data('colrange',[scol,ecol]); //store colrange
		return div;
	}
	
	if(visiblecols[0]!==0) $ruler.append(markerdiv(0,visiblecols[0]));
	for(var t=0;t<visiblecols.length-1;t++){
		if((visiblecols[t+1]-visiblecols[t])!=1){ //a column gap => add marker
			if(visiblecols[t+1]<=visiblecols[t]){ //columns array corrupt. clean up array. redraw.
				visiblecols.sort(function(a,b){return a-b});
				for(var i=1;i<visiblecols.length;i++){ if(visiblecols[i-1]==visiblecols[i]) visiblecols.splice(i,1); }
				redraw(); return;
			}
			$ruler.append(markerdiv(visiblecols[t]+1,visiblecols[t+1]));
		}
		if(t%tick==0){ //make ruler tickmarks
			k = t;
			if(t+tick>visiblecols.length) tickw = (visiblecols.length%tick)*boxw-4;
			if(boxw<4){ if(t%100==0){ if(t>=1000){ k = '<span>'+(t/1000)+'K</span>'; }else{ k = '<span>'+t+'</span>'; } }else{ k = '&nbsp;'; } }
			$ruler.append($('<span style="width:'+tickw+'px">'+k+'</span>'));
		}
	}
	if(visiblecols[visiblecols.length-1] != model.alignlen()-1) $ruler.append(markerdiv(visiblecols[visiblecols.length-1]+1,model.alignlen()));
}

//Drag-drop 'move tree node' mode
function movenode(drag,movednode,movedtype){
	if(!movednode) return false;
	$("#left").addClass('dragmode');
	$("#namesborderDragline").addClass('dragmode');
	movednode.highlight(true);
	setTimeout(function(){ //explanation popup
		tooltip('','Move node: '+(drag?'drop node to':'click on')+' target branch or node.', {target:$("#left"), shiftx:5, shifty:-30, arrow:'bottom', autohide:6000});
	}, 400);
	if(drag){
		$("#right").addClass('dragmode');
		setTimeout(function(){
			tooltip('','Delete node: drop node here.', {target:$("#right"), shifty:-5, arrow:'bottom', autohide:6000});
		}, 400);
		if(movedtype=='circle'){ //add drag helper (node preview)
			var helper = $(movednode.makeCanvas()).attr('id','draggedtree');
		}
		else if(movedtype=='text'){
			var helper = $('<div id="draggedlabel">'+movednode.name+'</div>');
		}
		$("body").append(helper);
	}//drag
	
	var drawtimer = 0, maxscroll = ($("#seq").height()+10)-($("#left").innerHeight()+3);
	var vertdragger = $("#verticalDragger .dragger");
	var draggerscale = maxscroll/($("#verticalDragger").height()-vertdragger.height());
	function loop(rate){ //treescroll
		var scrollto = parseInt(dom.treewrap.css('top'))+rate;
		if(scrollto > 0) scrollto = 0; else if(Math.abs(scrollto) > maxscroll) scrollto = 0-maxscroll;
	dom.treewrap.stop(1).animate({top:scrollto}, 1000, 'linear', function(){ loop(rate) });
	dom.seq.stop(1).animate({marginTop: scrollto}, 1000, 'linear');
	vertdragger.stop(1).animate({top: (0-scrollto)/draggerscale}, 1000, 'linear');
	}        
	function stop(){ $('#treewrap,#seq,#verticalDragger .dragger').stop(1); clearInterval(drawtimer); }
	$.each(['up','down'],function(i,dir){ //set up hoverable scrollbuttons
		var scrolldiv = $('<div class="treescroll '+dir+'" style="width:'+($("#right").offset().left-30)+'px">'+(dir=='up'?'\u25B2':'\u25BC')+'</div>');
		$("#page").append(scrolldiv);
		var baseline = scrolldiv.offset().top;
		scrolldiv.mouseenter(function(){ drawtimer = setInterval(function(){ makeImage() }, 2000) });
		scrolldiv.mousemove(function(event){
			var rate = dir=='up'? scrolldiv.outerHeight()-(event.pageY-baseline) : 0-(event.pageY-baseline);
			if(rate%2 != 0) loop(rate*10);
		});
		scrolldiv.mouseleave(function(){ stop() });
	});
		
	$("body").one('mouseup',function(evnt){ //mouse release
		var targettype = evnt.target.tagName;
		if(targettype=='circle'||targettype=='text'||(targettype=='line'&&$(evnt.target).attr('class')=='horizontal')){
			var targetid = parseInt(evnt.target.getAttribute('nodeid'));
			var targetnode = treesvg.data.root.getById(targetid);
			if(movednode && targetnode){ movednode.move(targetnode); refresh(); }
		}
		else if (drag && targettype=='DIV' && evnt.target.id=='treebin'){ if(movednode){ movednode.remove(); } refresh(); }
		movednode.highlight(false);
		$("#left,#right,#namesborderDragline").removeClass('dragmode');
		$("div.treescroll").remove(); stop();
		if(drag) helper.remove();
		$("#page").unbind('mousemove'); hidetooltip();
	 });
	 if(drag) return helper;
}

/* User interface building functions */
//toolbar title pop-up menu
function titlemenu(e){
	e.preventDefault();
	e.stopPropagation();
	var $input = $('#toptitle>input');
	if($input.hasClass('editable')) return false;
	var title = '', menudata = {};
	if(!librarymodel.openitem() || !librarymodel.openitem().shared) menudata['Rename'] = function(){ 
		$input.addClass('editable'); $input.focus();
	}
	menudata['Save'] = function(){ savefile($('#toptitle>span.note')) };
	menudata['Export'] = function(){ dialog('export') };
	if(librarymodel.openitem()) menudata['View in Library'] = function(){ dialog('library') };
	else title = 'Not in Library';
	tooltip('',title,{target:$('#toptitle'), arrow:'top', shifty:-5, data:menudata, style:'white greytitle', id:'titlemenu'});
}

//titlebar menus
function topmenu(e,btn,menuid){
	var $btn = $(btn);
	e.preventDefault();
	e.stopPropagation();
	var title = '', menudata = {};
	if(!menuid) menuid = $btn.attr('id')+'menu';
	var has = {
		online: !model.offline()&&!model.noaccount(),
		seq: model.seqsource(),
		tree: model.treesource(),
		data: model.seqsource()||model.treesource(),
		sharing: settingsmodel.sharelinks()
	};
	
	var modeldata = unwrap(model[menuid]) || {};
	$.each(modeldata, function(i,rdata){
		var row = {};
		if(menuid == 'undostack'){
			rdata.txt = i;
			row.txt = rdata.name;
			row.icon = rdata.type;
			row.t = rdata.info;
			row.css = {backgroundColor: rdata==model.activeundo.data()?'#ffcc66':'' };
			row.click = function(){ model.selectundo(rdata) };
		} else {
			row.icon = rdata.icn;
			row.t = rdata.inf;
			row.click = typeof(rdata.act)=='function'? rdata.act : function(){ dialog(rdata.act) };
			row.css = rdata.css||'';
			if(rdata.req){ //conditional menu items
				$.each(rdata.req,function(r,req){
					if(!has[req]){
						row.click = req=='online'? function(){dialog('jobstatus')} : '';
						row.css = {'opacity':'0.2'}; return false;
			}});}
		}
		if(!row.click) return true;
		else menudata[rdata.txt] = row;
	});
	if(!Object.keys(menudata).length) title = 'No items';
	tooltip('',title,{clear:true, target:btn, arrow:'top', data:menudata, style:'white topmenu greytitle', id:menuid});
}

//library window pop-up menu
function librarymenu(itm,e){
	if(e){ e.preventDefault(); e.stopPropagation(); }
	var btn = $('#library a.back.gear');
	var compact = settingsmodel.minlib()? 'Standard' : 'Compact';
	var ladder = settingsmodel.ladderlib()? 'Step' : 'Path';
	var menudata = {'Refresh':function(){ communicate('getlibrary','',{restore:true,btn:btn,restorefunc:librarymenu}) }, 
	'New collection': librarymodel.newdir };
	menudata[compact+' mode'] = function(){ toggle(settingsmodel.minlib); settingsmodel.saveprefs(); };
	menudata[ladder+' view'] = function(){ toggle(settingsmodel.ladderlib); settingsmodel.saveprefs(); };
	tooltip('','',{target:btn, shiftx: '3px', shifty: '5px', arrow:'top', data:menudata, style:'white', id:'librarymenu'});
}

//hide/expand toolbar
function toggletop(collapse){
	if(typeof(collapse)=='undefined') collapse = !$('body').hasClass('mintop');
	else if(collapse==$('body').hasClass('mintop')) return;
	var arrows = $('#topcollapse>span');
	if(collapse){
		localStorage.collapse = "collapse";
		$('body').addClass('mintop');
		setTimeout(function(){
			arrows.html('&#x25BC;<br>&#x25BC;');
			$('#top .toptext, #top .title, #bottom').css('display','none');
			$('#top').addClass('hidden');
			$(window).trigger('resize');
		},800);
	} else {
		localStorage.collapse = "";
		$('#top .toptext, #bottom').css('display','');
		if(!model.offline()) $('#top .title').css('display','');
		setTimeout(function(){ $('body').removeClass('mintop') },100);
		setTimeout(function(){
			arrows.html('&#x25B2;<br>&#x25B2');
			$(window).trigger('resize');
			$('#top').removeClass('hidden');
		},800);
	}
	
}

//generate contents for tree node menu
function treemenu(node){
	var hidemenu = node.parent?{'Hide this node':{icon:'hide', t:'Collapse node and its children', click:function(){node.hideToggle()}}}:{};
	$.each(node.children,function(i,child){ //build child nodes hiding submenu
	if (child.type == 'ancestral') return true; //skip anc.
	var litxt = (child.hidden?'Show ':'Hide ')+(i==0?'upper ':'lower ')+' child';
	hidemenu[litxt] = {icon:i==0?'upper':'lower', t:'(Un)collapse a child node', click:function(){child.hideToggle()}};
	if(child.children.length && child.hidden){ //preview hidden children
		var createpreview = function(){ //create treepreview on the fly
			var preview = $('<span style="margin-left:5px" class="svgicon">'+svgicon('view')+'</span>');
			preview.mouseenter(function(e){ tooltip(e,'',{target:preview[0], data:child.makeCanvas(), arrow:'left', style:'none', hoverhide:true}); });
			return preview;
		}
		hidemenu[litxt]['add'] = createpreview;
	}
    });
    hidemenu['Show subtree'] = {icon:'children', t:'Uncollapse all child nodes', click:function(){node.showSubtree()}};
    
    var menu = {'Show/hide tree nodes':{submenu:hidemenu}};
    var ancnode = node.children[node.children.length-2];
    if(ancnode.type=='ancestral'){ //ancestral nodes submenu
	menu['Ancestral sequences'] = {submenu:{
		'Show/hide ancestral seq.': {t:(ancnode.hidden?'Reveal':'Hide')+' the ancestral sequence of this node', icon:'ancestral', click:function(){ancnode.hideToggle()}},
		'Show subtree ancestors': {t:'Show ancestral sequences of the whole subtree', icon:'ancestral', click:function(){node.showSubtree('anc')}},
		'Hide subtree ancestors': {t:'Hide ancestral sequences of the whole subtree', icon:'ancestral', click:function(){node.showSubtree('anc','hide')}},
	}};
    }
    menu['Reorder subtree'] = {submenu:{'Swap children':{t:'Swap places of child nodes', icon:'swap', click:function(){node.swap()}}}};
    if(node.visibleLeafCount>2) menu['Reorder subtree']['submenu']['Ladderise subtree'] = {t:'Reorder the subtree', icon:'ladderize', click:function(){node.ladderize()}};
    if(node.parent){
	menu['Move node'] = {t:'Graft this node to another branch in the tree', icon:'move', click:function(){movenode('',node,'circle')}, noref:true};
	menu['Place root here'] = {t:'Place this node as the tree outgroup', icon:'root', click:function(){node.reRoot()}};
	menu['Remove nodes'] = {submenu:{'Remove this node': {t:'Remove this node and its children from the tree', icon:'trash', click:function(){node.remove()}}}};
	if(node.leafCount>2) menu['Remove nodes']['submenu']['Keep only subtree'] = {t:'Remove all nodes except this subtree', icon:'prune', click:function(){node.prune()}};
    }	
    menu['Export subtree'] = {t:'Export this subtree in newick format', icon:'file_export', click:function(){dialog('export',{exportdata:node.write()})}, css:{'border-top':'1px solid #999'}, noref:true};
    return menu;
}

//make tooltips & pop-up menus 
//args: (event,'title',{target:elem,style:'white',css,arrow:'top'/'bottom',data:{menudata},clear,hoverhide/nohide/clickhide,ko:koModel)
function tooltip(evt,title,options){
	if(!options) options = {};
	var tipdiv = options.id? $('#'+options.id) : [];
	if(tipdiv.length){ //use existing tooltip
		if(options.norefresh) return tipdiv;
		var tiparrow = $(".arrow",tipdiv);
		var tiptitle = $(".tooltiptitle",tipdiv);
		var tipcontentwrap = $(".tooltipcontentwrap",tipdiv);
		var tipcontent = $(".tooltipcontent",tipdiv);
		tiptitle.empty(); tipcontent.empty();
	} else { //generate new tooltip
		tipdiv = $('<div class="tooltip"></div>');
		var tiparrow = $('<div class="arrow"></div>');
		var tiptitle = $('<div class="tooltiptitle"></div>');
		var tipcontentwrap = $('<div class="tooltipcontentwrap"></div>');
		var tipcontent = $('<div class="tooltipcontent"></div>');
		tipcontentwrap.append(tipcontent);
		tipdiv.append(tiparrow,tiptitle,tipcontentwrap);
		if(options.id){
			if(options.id=='treemenu' && options.data){ tipdiv.remove(); return; }
			else tipdiv.attr('id',options.id);
		}
		var box = options.container || 'body';
		$(box).append(tipdiv);
	}
	
	if(options.clear) hidetooltip('',tipdiv,options.nodeid||''); //clear other tooltips
	$('html').off('click'); //avoid hiding of tooltip under construction
	
	var arr = options.arrow || false;
	var treetip = options.treetip||false;
	var tipstyle = options.style||settingsmodel.tooltipclass()||'none';
	if(tipstyle!='none') tipdiv.addClass(tipstyle); //custom style
	if(options.css) tipdiv.css(options.css);
	if(options.maxw) tipdiv.css({'max-width':options.maxw+'px', 'white-space':'pre-line'});
	
	if(options.target){ //place next to target element
		var target = typeof(options.target)=='object'? options.target : evt.currentTarget;
		if(target.jquery) target = target[0];	
		if(target.tagName){ //target is DOM element
			var elem = $(target);
			if(!target.width) target.width = elem.width();
			if(!target.height) target.height = elem.height();
			if(target.tagName.toLowerCase()=='circle'){ //target is treenode
				if(options.nodeid) treetip = true;
				target.x = elem.offset().left+25;
				target.y = elem.offset().top-7;
			}
		else if(target.tagName.toLowerCase()=='li'){ //target is tooltip. place as submenu
			target.x = elem.innerWidth()-2;
			target.y = elem.position().top-2;
			if(tipstyle=='white') target.y -= 1;
		}
		else{ //place tooltip next to element
			target.x = elem.offset().left;
			target.y = elem.offset().top;
			if(elem.hasClass('svgicon')){ target.x += 27; target.y -= 3; }
			if(!arr){
				target.x += 15;
				target.y += target.height+5;
			}
		}
	  }
	  if(!target.x) target.x = evt.pageX+5||0;
	  if(!target.y) target.y = evt.pageY+5||0;
    }
    else{ var target = { x: evt.pageX+5, y: evt.pageY+5 }; } //tooltip next to cursor
    target.x += parseInt(options.shiftx||0); target.y += parseInt(options.shifty||0);
    var rightedge = $('body').innerWidth()-200;
    if(!options.container && target.x > rightedge) target.x = rightedge;
    if(!target.width) target.width = 5;
	if(!target.height) target.height = 5;
    
    var node = titleadd = menutooltip = false;
	if(options.nodeid && treesvg.data){
		node = treesvg.data.root.getById(options.nodeid);
		activenode = options.nodeid;
    }
    
    if(options.data){ //make pop-up menu
      if(treetip && node){ //generate tree node popup menu title
    	var hiddencount = node.leafCount - node.visibleLeafCount;
		var titleadd = $('<span class="right">'+(hiddencount?' <span class="svgicon" style="padding-right:0" title="Hidden leaves">'+svgicon('hide')+'</span>'+hiddencount : '')+'</span>');
		if(hiddencount && title.length>10) titleadd.css({position:'relative',right:'0'});
		var infoicon = $('<span class="svgicon">'+svgicon('info')+'</span>').css({cursor:'pointer'}); //info icon
		infoicon.mouseenter(function(e){ //hover infoicon=>show info (branch node)
			var nodeinf = [];
			nodeinf.push('<span class="note">Branch length</span> '+(Math.round(node.len*1000)/1000));
			//'Length from root: '+(Math.round(node.lenFromRoot*1000)/1000);
			//if(hiddencount) nodeinf.unshift('<span class="note">Hidden leaves: '+hiddencount);
			//if(node.children.length) nodeinf.unshift('Visible leaves: '+node.visibleLeafCount);*/
			$.each(node.nodeinfo, function(title,val){ //display all metadata
				if(title=='branchlength'||title=="label") return true;
				nodeinf.push('<span class="note">'+title.capitalize().replace('_',' ')+'</span> '+val); 
			});
			tooltip(e,'',{target:infoicon[0],data:nodeinf,arrow:'left',style:'bulletmenu',hoverhide:true});
		});
		titleadd.append(infoicon);
		if(!node.parent && !node.species) title = 'Root';
		var desc = (node.parent?'':'Root node: ')+(node.species?'taxa ':'')+title;
		title = '<span class="title" title="'+desc+'">'+title+'</span>';
		options.data = treemenu(node); //generate tree menu
	  }//treetip=>options.data
    //make pop-up menu
      if(options.data.tagName || typeof(options.data)=='string'){  //non-menu(data/html) tooltip
	    tipcontent.append(options.data);
	  }
      else{ //list-type menu: {click/over/out:func(), icon:'svgicn', txt:'txt', t:'title', css/class:'css', add:'html', submenu:[items]}
		menutooltip = true;
    	var ul = $('<ul>');
		$.each(options.data,function(txt,obj){  //{item}||[items]: 'txt'||'txt':func()||'txt':item||'txt':[items]
			if(typeof(obj)=='undefined') return true;
			var li = $('<li>');
			if(!obj) obj = {};
			else if($.isArray(obj)) obj = {submenu:obj};
			else if(typeof(obj)=='string') obj = {txt:obj};
			else if(typeof(obj)=='function') obj = {click:obj};
			if(obj.txt) txt = obj.txt;
			if(obj.submenu){
				var smenu = Object.keys(obj.submenu);
				if(!smenu.length) return true; //skip empty submenus
				if(smenu.length==1){ txt = smenu[0]; obj = obj.submenu[txt]; if(obj.txt) txt = obj.txt; } //un-nest 1-item submenu
				else { //nested submenu
					txt += ' <span class="right">\u25B8</span>';
					li.addClass('arr');
					li.mouseenter(function(evt){ tooltip(evt,'',{target:li[0], data:obj.submenu, style:options.style||'', treetip:treetip}) });
				}
			}
			
			var t = obj.t?'title="'+obj.t+'">':'>';
			if(obj.icon) txt = '<span class="svgicon" '+t+svgicon(obj.icon)+'</span>'+txt;
			else if(t) txt = '<span '+t+txt+'</span>';
			li.html(txt);
			if(typeof(obj.click)=='function'){
				li.click(function(e){ e.stopPropagation(); hidetooltip(); obj.click(); });
				if(treetip && !obj.noref) li.click(refresh); //treemenu click followup
			}
			if(obj.over) li.mouseenter(obj.over);
			if(obj.out) li.mouseleave(obj.out);
			if(obj.add) li.append(obj.add);
			if(obj.css) li.css(obj.css);
			if(obj.class) li.addClass(obj.class);
			
			if(li.html()) ul.append(li);
		});
		if(ul.html()) tipcontent.append(ul);
		if(title) $('li:first-child',ul).css('border-radius',0);
		
		if(treetip && title){ //treemenu slidedown
			tipcontentwrap.css({'height':tipcontent.innerHeight()+2+'px'});
			setTimeout(function(){tipcontentwrap.css('overflow','visible')},500); //unblock submenus
		}
		
		if(target.tagName && target.tagName.toLowerCase() == 'li'){ //submenu
			$(target).append(tipdiv);
			options.hoverhide = true;
		}
	  } //if options.data
	  if(tipcontent.html()) tiptitle.css('border-bottom', '1px solid #999');
	}else{ //make simple tooltip
		if(treetip){ //title for tree node
			if(!node.parent && !node.species) title = 'Root node';
			else if(!title) title = 'Tree node. Click for options.';
		}
		if(!options.nohide){
			if(typeof(options.target)!='object' || options.target.tagName) options.hoverhide = true; //DOM target
			if(typeof(options.autohide)!='string') setTimeout(function(){hidetooltip(tipdiv)}, options.autohide||3000); //remote target
		} 
	}
	
	if(title){ tiptitle.html(title); if(titleadd) tiptitle.append(titleadd); }
	else{ tiptitle.css('display','none'); }
	
   if(options.hoverhide && target.tagName){ $(target).one('mouseleave',function(e){ //hide tooltip on mouseleave
	   var hidetip = function(){ hidetooltip(tipdiv,'',activenode); };
	   if(options.tiphover){ //cancel hide if mouse goes over tooltip
		   var leavetimer = setTimeout(hidetip, 600);
		   tipdiv.one('mouseenter',function(){ clearTimeout(leavetimer); });
		   tipdiv.one('mouseleave', hidetip);
	   }
	   else hidetip();   
   });}
   if(!menutooltip) tipdiv.click(function(e){ e.stopPropagation(); }); //don't hide when clicked on tooltip

   setTimeout(function(){$('html').one('click',function(){ hidetooltip() })}, 400);
   if(options.ko) ko.applyBindings(options.ko, tipdiv[0]);
   if(arr=='top'||arr=='bottom'){ //adjust arrowed tooltip
		target.x += (target.width-tipdiv.innerWidth())/2;
		if(arr=='top' && target.y+tipdiv.innerHeight()+20>$('#page').innerHeight()) arr = 'bottom';
		if(arr=='top') target.y += target.height+15;
		else if(arr=='bottom') target.y -= tipdiv.innerHeight()+10;
   }
   if(arr) tipdiv.addClass(arr+'arrow');
   if(!options.nomove) tipdiv.css({left:parseInt(target.x),top:parseInt(target.y)});
   setTimeout(function(){tipdiv.addClass('opaque')},34);
   return tipdiv;
}

var activenode = ''; //id of selected treenode
//Hide/remove a tooltip/pop-up menu
function hidetooltip(include,exclude,nodeid){
	if(activenode && (!nodeid || activenode!=nodeid)){
		try{ treesvg.data.root.getById(activenode).highlight(false); }catch(e){}
		activenode = '';
	}
	if(!include) model.activeid(''); //model.activeid = seq. selection id
	var tooltips = $(include||"div.tooltip").not(exclude);
	tooltips.each(function(){
		var tip = $(this);
		tip.removeClass('opaque');
		setTimeout(function(){ tip.remove(); },200);
	});
}

//make arrow+title for collapsible section in dialog windows
function expandtitle(options){
	var arrow = $('<span class="rotateable">&#x25BA;</span>'), infospan = '';
	var titlespan = $('<span class="action" title="'+(options.desc||'Click to toggle content')+'">'+(options.title||'View/hide')+'</span>');
	if(options.info){
		infospan = $('<span class="note" style="display:none;margin-left:20px">'+options.info+'</span>');
		options.onshow = function(){infospan.fadeIn()};
		options.onhide = function(){infospan.fadeOut()};
	}
	titlespan.click(function(){
		var content = options.target||$(this).parent().next(".insidediv");
		if(arrow.hasClass('rotateddown')){
			arrow.removeClass('rotateddown');
			if(options.minh) content.animate({height:options.minh});
			else content.slideUp();
			if(typeof(options.onhide)=='function') options.onhide();	
		}
		else{
			arrow.addClass('rotateddown');
			if(options.maxh){
				if(isNaN(options.maxh)) options.maxh = content[0].scrollHeight;
				content.animate({height:options.maxh});
			}
			else content.slideDown();
			if(typeof(options.onshow)=='function') options.onshow();
		}
	});
	var titlediv = $('<div>').append(arrow,titlespan);
	if(options.info) titlediv.append(infospan);
	if(options.inline) titlediv.css({'display':'inline-block','margin-left':'5px'});
	if(typeof(options.css)=='object') titlediv.css(options.css);
	return titlediv;
}

/* Generate pop-up windows */
function makewindow(title,content,options){ //(string,array(,obj{flipside:'front'|'back',backfade,btn:string|jQObj|array,id:string},jQObj))
	if(!options) options = {};
	if(!$.isArray(content)) content = [content];
	var animate = settingsmodel.windowanim();
	if($("div.popupwindow").length>10) return; //window limit
	if(options.id && $('#'+options.id).length){ //kill clones
		options.position = $('#'+options.id).position();
		if(!options.flipside||options.flipside=='front') $('#'+options.id).remove();
	}
	var container = false;
	if(options.flipside){ //we make two-sided window
		if(options.id && $('#'+options.id).length){
			container = $('#'+options.id);
		} else {
			var animclass = settingsmodel.windowanim()? 'zoomin' : '';
			container = $('<div class="popupwrap '+animclass+'">');
			$("#page").append(container);
		}
		var sideclass = 'side '+options.flipside;
		if(!animate) sideclass += ' notransition';
	} else if(animate){ var sideclass = 'zoomin'; } else { var sideclass = ''; }
	var windowdiv = $('<div class="popupwindow '+sideclass+'"></div>');
	if(options.id) (container||windowdiv).attr('id',options.id);
	var shade = $("#backfade");
	var closebtn = $('<span class="closebtn" title="Close window">'+svgicon('x')+'</span>');
	var closefunc = function(){ //close window
		var wrapdiv = container || windowdiv; 
		wrapdiv.removeClass('zoomed');
		if(animate) setTimeout(function(){ wrapdiv.remove() },600); else wrapdiv.remove();
		if(shade.css('display')!='none'){ shade.fadeOut(); }
		if(options.closefunc) options.closefunc();
	};
	closebtn.click(closefunc);
	if(options.btn){ //add buttons
		if(typeof(options.btn)=='string'||options.btn.jquery){ options.btn = [options.btn]; var align = 'center'; }//one btn
		else{ var align = 'right'; }//array of btns
		var btndiv = $('<div class="btndiv" style="text-align:'+align+'">');
		$.each(options.btn,function(b,btn){
			if(typeof(btn)=='string'){ btndiv.append($('<a class="button grey">'+btn+'</a>').click(closefunc)); }
			else{ if(btn.attr('class').split(' ').length==1) btn.addClass("grey"); btndiv.append(btn); }
		});
		btndiv.click(function(e){ e.stopPropagation() }); //fix "owner is null" error with draggable.preventClickEvent
		content.push(btndiv);
	}
	var titlediv = $('<div class="windowtitle"></div>');
	var contentdiv = $('<div class="windowcontent"></div>');
	contentdiv.css('max-height', $('#page').height()-100+'px');
	if(options.nowrap) contentdiv.css('white-space','nowrap');
	if(!options.nomaxw) contentdiv.css('max-width','500px');
	var headerdiv = $('<div class="windowheader"></div>');
	if(options.header){ $.each(options.header,function(i,val){ headerdiv.append(val) }); }
	if(options.icn){
		var imgdir = options.plugin? 'plugins/'+options.plugin : 'images';
		if(options.icn.indexOf('.')==-1) options.icn+='.png';
		title = '<img class="windowicn" src="'+imgdir+'/'+options.icn+'"> '+title;
	}
	titlediv.html(title);
	$.each(content,function(i,item){ contentdiv.append(item); });
	windowdiv.append(headerdiv,contentdiv,titlediv,closebtn);
	if(options.hidden) windowdiv.css('display','none');
	$(container||"#page").append(windowdiv); //add window to webpage
	
	var dragdiv = container||windowdiv, page = {w:$('#page').width(), h:$('#page').height()}, win = {w:windowdiv.width(), h: windowdiv.height()};
	var toFront = function(windiv,first){ //bring window on top
		var maxz = Math.max.apply(null, $.map($('#page>div.popupwindow,div.popupwrap'), function(e,i){ return parseInt($(e).css('z-index'))||1; }));
		var curz = parseInt($(windiv).css('z-index'));
		if((curz<maxz) || (curz==maxz&&first)) $(windiv).css('z-index',maxz+1);
    }
	if(options.backfade){ //place window to center
	dragdiv.css({'top':(page.h/2)-(win.h/2)+'px','left':(page.w/2)-(win.w/2)+'px'});
    }
    
    var pos = options.position || ($('#page>div.popupwindow').length? $('#page>div.popupwindow').last().position() : '');
    if(pos && (!options.flipside||options.flipside=='front')){ //place a new window to shifted overlap
		toFront(dragdiv,'first');
		dragdiv.css({'top':pos.top+20+'px','left':pos.left+20+'px'});
	}
	
	dragdiv.mousedown(function(){ toFront(dragdiv) });
	if(container && win.w>container.width()) container.css('width', win.w-50+'px');
	if(container && win.h>container.height()) container.css('height', win.h-50+'px');
	setTimeout(function(){
		dragdiv.draggable({ //make window draggable by its title
			handle : "div.windowtitle",
			containment : [10,10,page.w-dragdiv.width()-20,page.h-40]
	}); }, 800); //add lag to get window dimensions
    if(options.backfade){ //make stuff visible
	shade.fadeIn({complete:function(){ if(animate) dragdiv.addClass('zoomed'); }});
    }
    else if(animate){ setTimeout(function(){ dragdiv.addClass('zoomed') }, 100); }
    setTimeout(function(){ dragdiv.addClass('finished') }, 900); //avoid transition bugs
	return windowdiv;
}

//Delegated closing of dialog windows
function closewindow(elem, addfunc){
	if(!elem) return;
	else if(typeof(elem)=='string') elem = elem=='all'? $('div.popupwindow') : $('#'+elem);
	else if(elem.pageX) elem = $(this);
	else elem = $(elem);
	elem.each(function(){ //click the close button of associated window(s)
		var el = $(this);
		var windiv = el.hasClass('popupwindow')? el : el.hasClass('popupwrap')? $(el[0]) : el.closest('div.popupwindow');
		if(typeof(addfunc)=='function') windiv.find('.closebtn').click(addfunc);
		else windiv.find('.closebtn').click();
	});
}

//constructor for creating Wasabi plugin interfaces
var plugins = {}; //plugins container

pluginModel = function(pdata, pname){
	//initial tracked values
	this.sequence = model.seqtype;
	this.tree = model.treesource;
	//plugin state
	this._errors = [];
	this._submitted = ko.observable(false);
	this._program = '';
	this._folder = pname;
	this._prefix = '-';
	this._libraryname = ko.observable('my analysis');
	this._makeids = false;
	this._title = pname || 'Wasabi plugin';
	this._icon = {};
	this._outfile = '';
	this._json = pdata;
	this.registerPlugin();
};

pluginModel.prototype = {
	//API error feedback
	apierr: function(errtxt, iswarning){
		var addtxt = iswarning?'warning':'error';
		if(this._curopt){ addtxt += ' when parsing "'+this._curopt+'"'; }
		var errtxt = 'Wasabi plugin API '+addtxt+': '+errtxt+'!';
		if(!iswarning) this._errors.push(errtxt);
		console.log(errtxt);
		return '';
	},
	
	//find option-bound observables
	getOption: function(option){
		if(option in this) return this[option];
		for(var n in this){ if(this[n].optionname && this[n].optionname == option) return this[n]; }
		return false;
	},
	
	//translate API words to Javascript (observables/logic/quoted text)
	processValue: function(expr){
		var obsname = function(name){ //detect and format observable name
			return typeof(this[name])=='function'? (~name.indexOf(' ')||~name.indexOf('-')? "$data['"+name+"']()" : name+"()") : false;
		}.bind(this);
		var quote  = function(exp){ try{ JSON.parse(exp) }catch(e){ return "'"+exp+"'" }; return exp; } //quote strings
		var api = {'is':'==', 'is equal to':'==', 'equals':'==', 'contains':'.indexOf(', 'is not':'!=', 'is less than':'<', 
			'is more than':'>', 'not ':'!', 'no ':'!', 'invert ':'!', 'no':'false', 'off':'false', 'disable':'false', 
			'yes':'true', 'on':'true', 'ticked':'true', 'checked':'true', 'selected':'true', 'and':'&&', 'or':'||', 'imported':''};

		if(typeof(expr)=='string'){
			expr = expr.trim();
			if(obsname(expr)){ expr = obsname(expr); }
			else{  //translate the logic API words and detect observables
			  expr = expr.replace(/'.+'|is equal to|is not|is less than|is more than|no |not |invert |[\w\-]+/g, function(match, index){
			  	if(match.indexOf("'")==0){
			  		var unq = match.replace(/'/g,"");
			  		return obsname(unq) || match;
			  	}
			  	else if(match=="invert" && index>(expr.length-7) && this._curopt){
			  		return "!"+obsname(this._curopt);  //_curopt = tracking name of currently parsed option
			  	}
			  	else{ return obsname(match) || api[match] || quote(match); }
			  });
			}
			expr = expr.replace(/' '/g, " ");
			return expr;
		} else { return typeof(expr)=='undefined'? "" : JSON.stringify(expr); } //stringify numbers etc.
	},

	//Translate API conditional rules to Javascript ('yes/no/is not/{...}','result of rule',['upperLevelObsName'])
	processRule: function(rule, result, rootvar){
		if(typeof(result)=='undefined') result = "true";
		var str = "";
		
		if($.isArray(rule)){ //[rule1,rule2,...] => apply sequentially
			for(var i=0, tmp=''; i<rule.length; i++){
				tmp = this.processRule(rule[i], result, rootvar);
				if(i<rule.length-1) tmp = tmp.split(":")[0]+":";
				str += tmp;
			}
		}
		else if(typeof(rule)=='object'){ //unpack rule objects
			if(Object.keys(rule).length>1){ //{rule1:res1,rule2:res2} => [{rule1:res1},{rule2:res2}]
				var rulearr = [];
				$.each(rule,function(subrule,subresult){ var ruleobj={}; ruleobj[subrule] = subresult; rulearr.push(ruleobj); });
				str = this.processRule(rulearr, result, rootvar);
			} else {  //{'rule':result}
				varname = Object.keys(rule)[0];
				varresult = rule[varname];  //if {"varname":{varval:result}} else {"varname":result}
				if(typeof(varresult)=='object') str = this.processRule(varresult, result, varname);
				else str = this.processRule(varname, varresult, rootvar);
			}
		}
		else{  //translate preprocessed rule
			if(!isNaN(rule)){ return JSON.parse(rule); }
			else if(typeof(rule)!='string'){ return JSON.stringify(rule); }
			
			rule = this.processValue(rule);
			result = this.processValue(result);
			rootvar = this.processValue(rootvar);
							
			var compare = function(rule){ //add '==' if needed (rule is rootvarValue)
				return ~["!","=","<",">","~","."].indexOf(rule.charAt(0))? rule: "=="+rule;
			}
			str = rootvar? rootvar+compare(rule) : rule;
			if(rootvar && ~str.indexOf(".indexOf")) str = "~"+str+")";
			var negresult = (!result||result=="true")?"false":result=="false"?"true":"\'\'";
			if(result!=="true" || rootvar) str += "?"+result+":"+negresult;
		}
		return str;
	},
	
	//processRule string => function
	ruleFunc: function(rule, appendstr){
		var funcstr = this.processRule(rule).replace(/\$data/g,"this").replace(/\w+\(\)/g,"this.$&")+(appendstr||'');
		try{ var rfunc = new Function("return "+funcstr); }catch(e){ return this.apierr("Faulty rule function ("+e+"): "+rule+" => "+funcstr); }
		return rfunc.bind(this);		
	},

	//Create a plugin interface (input) element
	processOption: function(data, prefix){
		if(typeof(data)=='string'){ //string => user interface text
			data = data.replace(urlregex, makeurl);
			var box = $('<span>'+data+'</span>');
			$("a", box).each(function(i,el){ if(this.hasAttribute("href")) this.setAttribute("target","_blank"); });
			return box;
		} else if (typeof(data)!='object') return '';
		if(!prefix) prefix = data.prefix||this._prefix;
		
		var types = {"text":"", "string":"text", "textbox":"text", "number":"text", "int":"text", "float":"text", "bool":"checkbox", 
			"tickbox":"checkbox", "switch":"checkbox", "checkbox":"", "hidden":"", "output":"hidden", "select":"", "file":""};
		var t = data.type && (data.type in types)? data.type : "text", classname = ""; //option type
		
		for(var k in data){ if(k in types){ t = k; if(data[k] && !data.title) data.title = data[k]; }} //shorthand "title"
		if(!data.name) data.name = data.option||"trackName"+Object.keys(this).length; //register tracking/reference name
		var trackname = this._curopt = data.name;
		var firstrun = !(trackname in this); //first occurrence in JSON
		if(~["number","float","int"].indexOf(t)){
			if(firstrun) this[trackname] = ko.observable('').extend({format: t});
			else this[trackname].extend({format: t});
			classname = "num";
		}
		else if(firstrun) this[trackname] = ko.observable('');
		var kovar = "$data['"+trackname+"']";
		
		if(firstrun && t=="output"){ //register output file
			var outfilename = data.default||data.output||"";
			if(outfilename && !this._outfile) this._outfile = outfilename;
			data.default = "'$path$"+outfilename+"'";
		}
		if(types[t]) t = types[t]; //t="text"/"checkbox"/"hidden"/"select"/"file"
		
		var el = $("<"+(t=="select"?"select":"input")+">").attr("type", t); //create input element
		if(classname) el.addClass(classname);
		if("option" in data){
			if(/^\W/.test(data.option)) prefix = "";  //prefix already in argname
			el.attr("name", prefix+data.option); //program command-line flag
			this[trackname].optionname = data.option;
		}
		kobind = (t=="checkbox"?"checked":"value")+":"+kovar+", name:'"+trackname+"'"; //bind interface input to tracked value
		if(data.fixed) kobind += ", disable:"+this.processRule(data.fixed);
		var elems = [];
		
		if(t=="select"){ //build selectable list of options/values
			if(!$.isArray(data.selection)){ this.apierr('"select" option needs the "selection" array'); data.selection = []; }
			var selarr = trackname+"_selection";
			var defsel = false;
			var firstrunsel = !(selarr in this); //option first time defined as selection
			if(firstrunsel) this[selarr] = [];
			for(var sindex in data.selection||[]){ //parse selection list items
				var sel = data.selection[sindex];
				var selitem = {t:'', v:'', d:'', opt:{}};
				if(typeof(sel)=='string' || typeof(sel)=='number'){ selitem.t = selitem.v = sel; } //string item
				else if(typeof(sel)=='object'){ //parse object item
					if(!("value" in sel) && typeof(sel.default)=='string' && sel.default!="yes") sel.value = sel.default;
					else if(typeof(sel.value)=='object'){ this.apierr('selection item "value" in wrong type (object)'); continue; }
					if(!("title" in sel)){ //fill missing title/value
						selitem.t = typeof(sel.option)=='string'? sel.option : ("value" in sel)? sel.value : '';
					} else if(typeof(sel.title)=='object'){ this.apierr('selection item "title" in wrong type (object)'); continue; }
					selitem.v = ("value" in sel)? sel.value : selitem.t;
					if(typeof(sel.desc)=='string') selitem.d = sel.desc;
					if("default" in sel || selitem.v===''){ defsel = true; if(selitem.v) this[trackname](selitem.v); } //initial selection
					
					//if(typeof(sel.desc)=='string'){ //add description of selected item
					//	if(firstrunsel) this[selarr][this[selarr].length-1].d = sel.desc;
					//	if(!this[trackname].desc){
					//		this[trackname].desc = ko.pureComputed(function(){
					//			var val = this[trackname]();
					//			return val?(ko.utils.arrayFirst(this[selarr], function(o){ return o.v == val; }).d||''):'';
					//		}, this);
							//elems.push('<pre data-bind="text: ko.toJSON('+kovar+'.desc, null, 2)"></pre>') //debug
					//		elems.push('<div class="inputdesc" data-bind="text:'+kovar+'.desc">');
					//	}
					//}
					
					if(sel.option){ //register other options set by the selection
						if(!$.isArray(sel.option)) sel.option = [sel.option];
						for(var optindex in sel.option){
							var selopt = sel.option[optindex];
							if(typeof(selopt)=='string'){ selitem.opt[selopt] = true; }
							else if(typeof(selopt)=='object'){ $.extend(selitem.opt, selopt); }
							else{ this.apierr('selection item "option" attribute needs to be string or object'); continue; }
						}
							//var isSelected = (function(thisval){ return function(){ return this[trackname]()==thisval; }})(selval);
							//if(firstrunsel) this[selopt] = ko.pureComputed(isSelected, this);
							//elems.push('<input type="hidden" name="'+prefix+selopt+'" data-bind="value:$data[\''+selopt+'\']">');	
					}	
				}else{ this.apierr('selection item needs to be string, number or object'); }
				if(firstrunsel){ this[selarr].push(selitem); }//add selection item
			} //foreach selection item
			
			if(firstrunsel){ //add selection list description/option trackers
				this[trackname].subscribe(function(newsel){ //set dependent options on selection change
					console.log('selection value set to:'); console.log(newsel);
					console.log(this);
					//for(var optname in ){
					//	if(newsel==sopt.selval){ this[soptname](sopt.optval); console.log('dep. option '+soptname+' set to '+optval);}
					//});
				});
				this[trackname].sindex = ko.pureComputed(function(){ //track index of selected opt
				return indexOfObj(this[selarr], 'v', this[trackname]());
			  }, this);
			}
			
			if(!this[trackname].sindex){
			  
			}
			
			var dstr = "option";
			if(data.extendable){ //editable select list
			  if(firstrunsel){
				this[trackname].edit = ko.observable(false);
				this[trackname].editSave = function(){
					var editindex = this[trackname].edit();
					if(editindex===false){ //enable edit mode
						this[trackname].edit(this[trackname].sindex());
					} else { //save edits
						if(editindex==-1){ //add new
							var newv = this[trackname]();
							this[selarr].push({t:newv, v:newv});
						} else { this[selarr][editindex].v = newv; }
						this[trackname].edit(false);
					}
				};
				this[trackname].rem = function(){
					var editindex = this[trackname].edit();
					if(editindex==-1){ this[trackname](this[selarr][sindex].t); }
					else{ this[selarr].splice(editindex, 1); }
					this[selarr].edit(false);
				};
			  }	
			  if(data.extendable=="configurations"){ dstr = 'preset'; data.title = "Saved options:"; }
			  
			  elems.unshift('<input data-bind="fadevisible:!isNaN('+kovar+'.edit()),value:'+kovar+'" style="width:180px" placeholder="Type new '+dstr+'"></input>'+
			  '<a class="button small square" data-bind="click:'+kovar+'.editSave,text:isNaN('+
				kovar+'.edit())?\'Edit\':\'Save\',attr:{title:isNaN('+kovar+'.edit())?\'Edit this '+dstr+'\':\'Save changes\'"></a> '+
				'<a class="button small square" data-bind="visible:'+kovar+'.edit()>0,click:function(){'+kovar+'(\'\');'+kovar+'.edit(-1)}" title="Add new '+dstr+'">New</a>'+
				'<a class="button small square red" data-bind="visible:!isNaN('+kovar+'.edit()),click:'+kovar+'.rem"  title="Remove this '+dstr+'">Remove</a>');	
			}//if extendable
			if(firstrunsel && !defsel) this[selarr].unshift({t:"Choose "+dstr, v:""}); //no selection by default
			kobind += ", options:"+selarr+", optionsValue:'v', optionsText:'t'";
		}//if select
		else if(t=="hidden" && !data.default) data.default = data.hidden||true;
		
		if("default" in data){ kobind += ", default:"+this.processRule(data.default); } //'default' is a custom binding
		el.attr("data-bind", kobind);
		
		if(t=="file"){
		  var format = data.fileformat||"fasta";
		  el.attr({"type":"hidden", "fileformat":format, "trackname":trackname});
		  var source = data.file || data.source || "current sequence";
		  
		  if(source.substr(0,7) != "current"){ //data source: external data
		   if(![trackname].fileformat){
			this[trackname].fileformat = format;
			this[trackname].container = ko.observableArray([]);
			this[trackname].filename = ko.observable('');
			this[trackname].container.subscribe(function(newarr){
			if(newarr.length && ('imported' in newarr[0]) && ('type' in newarr[0].imported)){
				this[trackname](newarr[0].imported.type);
				this[trackname].filename(newarr[0].name||'imported data');
			} else this[trackname]('');
			}, this);
			this[trackname].container.get = function(name){ return ko.utils.arrayFirst(container(), function(item){ return item.name==name; }); };
		   }
		    var container = this[trackname].container;
		  
			if(~source.indexOf("filedrop")){ //filedrop area
				var filedrag = $('<div class="filedrag">'+(data.title||'Drop file here')+'</div>');
				filedrag.bind('dragover',function(evt){ //file drag area
					filedrag.addClass('dragover'); evt.stopPropagation(); evt.preventDefault();
					evt.originalEvent.dataTransfer.dropEffect = 'copy';
				}).bind('dragleave',function(evt){
					filedrag.removeClass('dragover'); evt.stopPropagation(); evt.preventDefault();
				}).bind('drop',function(evt){
					filedrag.removeClass('dragover'); evt.stopPropagation(); evt.preventDefault();
					var origtxt = filedrag.text(), filehandle = evt.originalEvent.dataTransfer.files;
					filedrag.text('Importing...');
					setTimeout(function(){
						checkfiles(filehandle, {onefile:true, silent:true, nocheck:format=="original", container:container});
						setTimeout(function(){ filedrag.text(origtxt); }, 1000);
					},100);
				});
			} else var filedrag = ''; 
			if(~source.indexOf("import") || ~source.indexOf("fileselect")){ //import/select button
				var impbtn = ~source.indexOf("import");
				var or = $('<span style="display:inline-block;font-size:18px;">'+(filedrag?' or ':'')+'</span>');
				var importbtn = $('<a class="button" style="vertical-align:0">'+(impbtn?'Import':'Select')+'</a>');
				if(impbtn){
					importbtn.click(function(e){ return dialog('import', {onefile:true, silent:true, nocheck:format=="original", container:container}); });
				} else {
					var fileinput = $('<input type="file" multiple style="display:none" name="upfile">');
					fileinput.change(function(){ checkfiles(this.files, {onefile:true, silent:true, nocheck:format=="original", container:container}); });
					or.append(fileinput);
					importbtn.click(function(e){ fileinput.click(); e.preventDefault(); });
				}
			} else { var or = '', importbtn = ''; }
			
			var importdiv = $('<div data-bind="visible:!'+kovar+'()">').append(filedrag, or, importbtn);
				
			var filelist = $('<div data-bind="if:'+kovar+'">'+(data.desc||'Use file')+': <img class="icn" src="images/file.png"> <span data-bind="text:'+kovar+'.filename"></span></div>');
			var filedel = $('<span class="svgicon action" title="Remove file" style="margin:0 5px;" data-bind="click:function(){'+kovar+'.container([])}">'+svgicon('close')+'</span>');
			var fileview = $('<a class="button square small" title="View file content" data-bind="click:function(){dialog(\'export\',{exportdata:'+kovar+'.container()[0]})}">View</a>');
			filelist.append(filedel, fileview);
			elems.push(importdiv,filelist);
		  } else { //data source: loaded data
			el.attr("source", source);
			if(![trackname].fileformat){
			  this[trackname] = ko.pureComputed(function(){ //foption()=> 'seqtype'||'tree'||'seqtype tree'
				var dtype = source.split(' ')[1]||'data', seq = this.sequence(), tree = this.tree()?'tree':'';
				return dtype=='sequence'? seq : dtype=='tree'? tree : (seq||tree)?seq+' '+tree : '';
			  }, this);
			  this[trackname].fileformat = format;
			}
		  }
		}
		
		if(data.required || data.check){ //input validation
			var rqch = data.required || data.check;
			if(!this[trackname].errmsg){
			  if(typeof(rqch)=="string"){ //show message when input value missing
				this[trackname].errmsg = ko.pureComputed(function(){ return !this[trackname]()?rqch:""; }, this);
			  } else {
				if(typeof(rqch)=='object'){ //rule obj: evaluate key as rule, display the value as string
					var rqchrule = Object.keys(rqch)[0];
					var retfunc = this.ruleFunc(rqchrule, "?'"+rqch[rqchrule]+"':''");
				} else { var retfunc = this.ruleFunc(rqch); }
				this[trackname].errmsg = ko.pureComputed(retfunc);
			  }
			}
			elems.push('<!-- ko if:'+(data.required?'$data._submitted()&&':'')+kovar+'.errmsg() --><p class="'+(data.required?'err':'note')+'msg" data-bind="text:'+kovar+'.errmsg"></p><!-- /ko -->');
			kobind += ', style:{borderColor:'+kovar+'.errmsg()?\'red\':\'\'}';
		}
			
		if(el.attr("type")!="hidden"){ //text next to input
			var title = data.title? $('<span>'+data.title+'</span>') : ''; //add text
			if(data.desc){ if(title) title.addClass('label'); (title||el).attr('title',data.desc); }
			if(title){ el = t=='checkbox'? el.add(title) : title.add(el); }
		}
		
		var box = $("<div>"); //wrap up
		box.append(el);
		$.each(elems,function(i,elem){ box.append(elem) }); //add any extra html
		var existrule = data.enable||data.disable;
		if(existrule) box.attr("data-bind","if"+(data.disable?"not":"")+":"+this.processRule(existrule));
		if("line" in data) box.css("display","inline-block");
		this._curopt = '';
		return box;
	},
	
	//iterate through options data, convert to HTML
	buildOptions: function(data, prefix){
		var UI = $('<div>');
		if(!data) return this.apierr('empty option','warning');
		if($.isArray(data.options)){ //group of options
			if(data.prefix) prefix = data.prefix;
			for(var o in data.options){ UI.append(this.buildOptions(data.options[o], prefix)); }
			if("group" in data){
				UI.addClass("insidediv numinput").css({"display":"none","margin-bottom":0});
				UI = $('<div>').append(expandtitle({title:data.group||'Options', desc:'Click to toggle options', info:data.desc||'', inline:true, css:{'margin-top':'5px'}}), UI);
			}
			else if("section" in data){
				UI.prepend('<div class="sectiontitle small">'+(data.section?'<span>'+data.section+'</span>':'')+'</div>');
			}
			else if("line" in data){
				if(data.line) UI.prepend('<span>'+data.line+'<span>'); $('div',UI).css('display','inline-block');
			}
			var existrule = data.enable||data.disable;
			if(existrule) UI.attr("data-bind","if"+(data.disable?"not":"")+":"+this.processRule(existrule));
		} else { UI = this.processOption(data, prefix); } //single option
		return UI;
	},
	
	//build the window and menu entry
	buildUI: function(data){
		if(!data) data = this._json;
		var desc = data.desc? this.processOption(data.desc):''; delete data.desc;
		var nameinput = $('<input type="text" class="hidden" data-bind="value:_libraryname" title="Click to edit">');
		var namespan = $('<span class="note">Name the results: </span>').append(nameinput);
		var writetarget = '<br><!-- ko if:exportmodel.savetargets().length>1 --><span class="label" title="Choose a library slot '+
		'for the new analysis, relative the to the input (currently open) dataset">Save as</span> '+
		'<select data-bind="options:exportmodel.savetargets, optionsText:\'name\', value:exportmodel.savetarget"></select><!-- /ko -->'+
		'<!-- ko if:exportmodel.savetargets().length==1 -->The result will be stored as new root<!-- /ko -->'+
		' analysis in the <a onclick="dialog(\'library\')">library</a>.';
		exportmodel.savetarget(exportmodel.savetargets()[0]);
		var inclhidden = '<!-- ko if:model.hiddenlen --><br><input name="includehidden" type="checkbox" data-bind="checked: exportmodel.includehidden">'+
		'<span class="label" data-bind="attr:{title:\'Include \'+model.hiddenlen()+\' collapsed alignment columns in analysis\'}">'+
		'include hidden alignment columns</span><!-- /ko -->';
		var header = $('<div class="insidediv incontent">').append(namespan, writetarget, inclhidden);
		
		var optformUI = this.buildOptions(data);
		if(this.selectoptions){
			$.each(this.selectoptions, function(soptname, sopt){
				if(!this[soptname]){ //add unregistered options from selection lists
					this[soptname] = ko.pureComputed();
					optformUI.append('<input type="hidden" name="'+sopt.prefix+soptname+'" data-bind="value:$data[\''+soptname+'\']">');
				}
			});
		}
		
		var optform = $('<form id="'+this._title+'form" onsubmit="return false"></form>').append(optformUI);
		var submitbtn = $('<a class="button orange" title="Launch '+this._program+'" data-bind="text:'+(data.submit?this.processRule(data.submit):'\'Send job\'')+'"></a>');
		submitbtn.click($.proxy(function(){
			this._submitted(true);
			var errors = $("p.errmsg",optform);
			if(errors.length){ //got form errors
				var origtxt = submitbtn.text();
				submitbtn.text("Check form errors!");
				setTimeout(function(){ errors.filter(':hidden').parents('.insidediv').slideDown(); },1000);
				setTimeout(function(){ submitbtn.text(origtxt); }, 2000);
				return;
			}
			sendjob({form:optform[0], btn:submitbtn, name:nameinput.val(), plugin:this._title}); //send job
		}, this));
		
		return {header: desc, content:[header,optform], btn:submitbtn}; //DOM elements
	},
	
	//prepare plugin
	checkPlugin: function(){
		//parse input
		data = this._json;
		if(!data) return this.apierr('input JSON missing');
		if(typeof(data)=='string'){ //JSON or native JS
			try{ data = JSON.parse(data); }
			catch(e){
				this.apierr('failed to parse plugin file as JSON: '+e,'warning');
				try{ eval("data = "+data); }
				catch(e){ return this.apierr('failed to parse plugin file as javascript object: '+e); }
			}
		}
		if($.isArray(data)) data = {options:data};
		else if(typeof(data)!='object') return this.apierr('plugin file in wrong format: '+typeof(data)+' (JSON/object/array expected)');
		this._json = data;
		
		if(!data.program) return this.apierr('program name missing');
		this._program = data.program;
		if(data.prefix) this._prefix = data.prefix;
		if(data.translate_names) this._makeids = true;
		if(data.libraryname) this._libraryname(data.libraryname);
		this._title = data.name || data.program;
		this._outfile = data.outfile || '';
		if(typeof(data.outfile)=='object'){ //dynamic output file naming
			this._outfile = ko.pureComputed(this.ruleFunc(data.outfile));
		}
		//make icon file
		var svgicon = "gear", icon = "../../images/gear.png", imgarr = [];
		if(typeof(data.icon)=='string') imgarr = [data.icon];
		else if($.isArray(data.icon)) imgarr = data.icon;
		$.each(imgarr,function(i,imgstr){
			if(typeof(imgstr)!='string') return true;
			if(imgstr.substr(0,10)=='data:image'||~['.png','.jpg','.gif'].indexOf(imgstr.substr(-4))) icon = imgstr;
			else svgicon = imgstr;
		});
		if(svgicon.length>10){ svgpaths[this._title] = svgicon; svgicon = this._title; } //add new svgicon
		else if(!svgpaths[svgicon]) svgicon = "gear";
		this._icon = {img:icon, svg:svgicon};
		
		if(!data.options) return this.apierr('no options found');
		return true;
	},
	
	//wire up
	registerPlugin: function(){
		this.checkPlugin();
		if(this._errors.length){  //add error dialog to tools menu
			console.log("Plugin datamodel dump:"); console.log(this);
			this._icon.svg = 'error';
			var errmsg = "<b>Plugin interface building failed for "+this._title+":</b><br><ul><li>"+this._errors.join("</li><li>")+"</li></ul>";
			var menuclick = dialog.bind(this, "error", errmsg);
			var menudesc = "This plugin failed to load. Click to see the errors.";
		} else {  //add plugin to tools menu
			var menuclick = this._title;
			var menudesc = data.menudesc||"Launch plugin for "+this._program;
			plugins[this._title] = this;
			this.buildUI();
		}
		model.toolsmenu.unshift({txt:this._title, act:menuclick, icn:this._icon.svg, inf:menudesc, req:['online']});
	}
};

//Generate content for pop-up windows
function dialog(type,options){
	//if(typeof(type.act)!='undefined') type = type.act;
	if(!options) options = {};
	//window laready created. bring it to front.
	if($('#'+type).length){ $('#'+type).trigger('mousedown');  return; }
// file/data import window
	if(type=='import'){
		if(!options) options = {};
		var alt = options.mode || options.noimport || options.container;
		var winid = options.windowid = 'import'+(alt?'_alt':''); var fade = !alt;
		if(fade) $('div.popupwindow').remove(); //close other windows
		
		var localhelp = 'Select file(s) that contain aligned or unaligned sequence (and tree) data. Supported filetypes: fasta(q), (extended)newick, HSAML, NEXUS, phylip, ClustalW, phyloXML etc.';
		var localheader = '<div class="sectiontitle"><img src="images/hdd.png"><span>Import local files</span><span class="svg" title="'+localhelp+'">'+svgicon('info')+'</span></div><br>';
		
		var filedrag = $('<div class="filedrag">Drag files here</div>');
		filedrag.bind('dragover',function(evt){ //file drag area
			filedrag.addClass('dragover');
			evt.stopPropagation();
			evt.preventDefault();
			evt.originalEvent.dataTransfer.dropEffect = 'copy';
		}).bind('dragleave',function(evt){
			filedrag.removeClass('dragover');
			evt.stopPropagation();
			evt.preventDefault();
		}).bind('drop',function(evt){
			evt.stopPropagation();
			evt.preventDefault();
			filedrag.removeClass('dragover');
			//var d = new Date(); importstart = d.getTime();
			checkfiles(evt.originalEvent.dataTransfer.files, options);
		});
	
		var fileinput = $('<input type="file" multiple style="opacity:0" name="upfile">');
		var form = $('<form enctype="multipart/form-data" style="position:absolute">');
		form.append(fileinput);
		filedrag.append(form);
		fileinput.change(function(){ checkfiles(this.files, options) });
		
		var selectbtn = $('<a class="button" style="vertical-align:0">Select files</a>');
		selectbtn.click(function(e){ fileinput.click(); e.preventDefault(); });
		var or = $('<div style="display:inline-block;font-size:18px;"> or </div>');
		
		var otherhelp = 'Type a web address of a remote data file or Wasabi share link/ID, or paste a raw text of sequence/tree data';
		var remoteheader = '<br><br><div class="sectiontitle"><img src="images/web.png"><span>Import from other sources</span><span class="svg" title="'+otherhelp+'">'+svgicon('info')+'</span></div><br>';
		var urladd = $('<a title="Add another input field" class="button urladd">+</a>'); //url inputs+buttons
		var urlinput = $('<textarea type="url" class="url" placeholder="Type a web address, Wasabi ID or raw data">');
		var expbtn = $('<span class="action icon" style="margin-left:-4px;vertical-align:7px" title="Expand/collapse the input field">&#x25BC;</span>');
		expbtn.click(function(){
			var self = $(this), field = self.prev("textarea");
			if(self.html()=='\u25BC'){ field.css('height','80px'); setTimeout(function(){self.html('\u25B2')},400); }
			else{ field.css('height',''); setTimeout(function(){self.html('\u25BC')},400); }
		});
		urladd.click(function(){
			var rmvbtn = $('<a title="Remove this input" class="button urladd" style="padding:2px 2px 6px">-</a>');
			rmvbtn.click(function(){
				var curbtn = $(this), curinput = curbtn.next("textarea");
				var rmvarr = [curbtn.prev("br"),curbtn,curinput,curinput.next("span.icon")];
				$.each(rmvarr,function(i,el){ el.remove() });
			});
			var lastel =  $('#'+winid+' span.action.icon').last();
			lastel.after("<br>",rmvbtn,urlinput.clone().css('height','').val(''),expbtn.clone(true).html('\u25BC'));
		});
		
		var dwnlbtn = $('<a class="button">Import</a>');
		dwnlbtn.click(function(){
			var urlarr = [];
			$('#'+winid+' .front .windowcontent textarea.url').each(function(i,input){
				var val = $(input).val();
				if(!val) return true;
				if(val.length==6){ //urlbox: analysis ID
					urlarr.push({name: 'Wasabi analysis', id:val});
				}
				else if(~val.search(/https?\:\/\//)){
					if(~val.indexOf(window.location.host) && ~val.indexOf('id=')){ //wasabi shareurl
						urlarr.push(parseurl(val));
					} else { urlarr.push({url:val}); } //external url
				}
				else if(val.length>20){ urlarr.push({name:'Text input', text:val}); } //raw data	
			});
			options.source = 'download';
			if(urlarr.length) checkfiles(urlarr, options); 
		});
		
		var ensheader = '<br><br><div class="sectiontitle"><img src="images/ensembl.png"><span>Import from <a href="http://www.ensembl.org" target="_blank">Ensembl</a></span>'+
		'<span class="svg" title="Retrieve a set of homologous sequences corresponding to Ensembl Gene ID, GeneTree ID or a region from an alignment block. Click for more info.">'+
		'<a href="http://www.ensembl.org/info/website/tutorials/compara.html" target="_blank">'+svgicon('info')+'</a></span></div><br>';
		
		var enscontent = '<div style="padding:0 10px"><select data-bind="options:idformats, optionsText:\'name\', value:idformat"></select>'+
		' <input style="width:210px" type="text" data-bind="attr:{placeholder:idformat().example},value:ensid"><br>'+
		'Use <select data-bind="options:comparas, value:compara, disable:isblock"></select> genomes database<br>'+
		
		'<div data-bind="slidevisible:!isblock()"><span style="color:#888">Search for Ensembl gene ID:</span><br>'+
		'species <input type="text" data-bind="value:idspecies"/> gene name <input type="text" data-bind="value:idname" style="width:80px"/> '+
		'<a id="ensidbtn" class="button square"  style="margin:0" onclick="ensemblid()">Get ID</a></div>'+
		'<div data-bind="slidevisible:isblock()&&!genomes()"><span class="cell">Pipeline type<hr><select data-bind="options:alignblocks,optionsText:\'type\',value:blocktype"></select></span>'+
		'<span class="cell" data-bind="with:blocktype">Species set<hr><select data-bind="options:set,optionsText:\'name\',value:$parent.blockset"></select></span>'+
		'<span class="cell" data-bind="with:blockset">Reference species<hr><select data-bind="options:species,optionsText:function(itm){return itm.capitalize().replace(\'_\',\' \')},value:$parent.blockref"></select></div>'+
		
		'<span style="color:#888">Options:</span><br>'+
		'<ul>'+
		'<li>Import '+
			'<select data-bind="value:aligned"><option value="true">aligned</option><option value="">unaligned</option></select>'+
			' <select data-bind="disable:isblock, value:seqtype"><option value="cdna">cDNA</option><option value="protein">protein</option></select> sequences</li>'+
		'<li data-bind="slidevisible:ishomol"><span class="label" title="Select type of homology. Projections are orthology calls defined between alternative assemblies and the genes shared between them">Include</span> <select data-bind="value:homtype" style="margin-top:5px"><option value="all">all homologous</option>'+
			'<option value="orthologues">orthologous</option><option value="paralogues">paralogous</option><option value="projections">projected</option></select> genes</li>'+
		'<li data-bind="slidevisible:ishomol">Restrict to a target species <input type="text" data-bind="value:target" style="width:100px"/></li>'+
		'<li data-bind="slidevisible:isblock"><select data-bind="value:mask"><option value="">Unmask</option><option value="hard">Hard-mask</option><option value="soft">Soft-mask</option></select> repeat sequences</li>'+
		'</ul></div>'+
		'<a id="ensbtn" class="button" onclick="ensemblimport()">Import</a> <span id="enserror" class="note" style="color:red"></span>';
		
		var dialogwindow = makewindow("Import data",[localheader,filedrag,or,selectbtn,ensheader,enscontent,remoteheader,urladd,urlinput,expbtn,'<br>',dwnlbtn],{backfade:fade,flipside:'front',icn:'import.png',nowrap:true,id:winid});
		ko.applyBindings(ensemblmodel,dialogwindow[0]);
		
		setTimeout(function(){
			makewindow("Import data",[],{backfade:false,flipside:'back',icn:'import.png',id:winid});
		},1000);
	}
// import multiblock ensembl alignment (selection dialog)
	else if(type=='alnblocks'){
		var content = '<div>Imported data contains multiple alignment blocks.<br>Select the one to import.<br><br>'+
		'<span class="buttongroup" data-bind="foreach:alnblocks">'+
		'<a class="button" data-bind="css:{pressed:$parent.alnblock()==$data, left:$index()==0, right:$index()==$parent.alnblocks.length-1, middle:$index()>0&&$index()<$parent.alnblocks.length-1}, text:\'Block \'+($index()+1), click:function(){$parent.alnblock($data)}"></a></span>'+
		'<br><div style="color:#555" data-bind="html:alnblockinfo"></div>'+
		'<hr><span data-bind="visible:settingsmodel.userid">Unselected blocks will be discarded, '+
		'<a class="button square small blue" data-bind="click:saveblocks">Save to library</a><br>'+
		'but the full dataset can be stored for later access.</span></div>';
		var importbtn = $('<a class="button orange" data-bind="click:importblock">Import selected block</a>');
		var importwindow = makewindow("Import alignment block", content, {icn:'import.png', id:type, btn:importbtn});
		ko.applyBindings(ensemblmodel, importwindow[0]);
	}
// file export window	
	else if(type=='export'){
		exportmodel.filename(exportmodel.savename().replace(' ','_'));
		var flipexport = function(){
			$('#'+type).removeClass('finished flipped');
			setTimeout(function(){ $('#'+type).addClass('finished') },900); //avoid firefox transition bugs
		};
		if($('#'+type).length){ //use existing window
			$('#'+type).click();
			$('#'+type+' a.backbtn').css('display','inline-block');
			flipexport();
			if(options) parseexport(options);
			return;
		}
		
		var hasancestral = treesvg.data && treesvg.data.root.children.length==3?true:false;
		var frontcontent = $('<div class="sectiontitle" style="min-width:320px"><img src="images/file.png"><span>File</span></div>'+
		'<span class="cell">Data<hr><select data-bind="options:categories, optionsText:\'name\', value:$data.category"></select></span>'+
		'<span class="cell" data-bind="fadevisible:category().formats.length,with:category">Format<hr><span data-bind="visible:formats.length==1,text:formats[0].name"></span><select data-bind="visible:formats.length>1, options:formats, optionsText:\'name\', value:$parent.format"></select></span>'+
		'<span class="cell" data-bind="with:format,fadevisible:format().variants.length>1">Variant<hr><select data-bind="options:variants, optionsText:\'name\', value:$parent.variant"></select></span> '+
		'<span class="svgicon" style="margin-left:-8px" data-bind="fadevisible:variant().desc,attr:{title:variant().desc,onclick:infolink()}">'+svgicon('info')+'</span>'+
		'<br>&nbsp;Name: <input type="text" class="faded" style="width:200px;text-align:right;margin:0" title="Click to edit" data-bind="value:filename">'+
			'<span style="font-size:17px" data-bind="visible:variant().ext.length<2,text:variant().ext[0]"></span>'+
			'<select data-bind="visible:variant().ext.length>1, options:variant().ext, value:fileext"></select>'+
		'<br><br><div class="sectiontitle"><img src="images/gear.png"><span>Options</span></div>'+
		(hasancestral?'<input type="checkbox" data-bind="checked:includeanc"> Include ancestors':'')+
		//'  <input type="checkbox" data-bind="visible:curitem().interlace,checked:interlaced"><span class="label" title="Interlace sequence data rows" data-bind="visible:curitem().interlace">Interlaced</span>'+
		'<div data-bind="slidevisible:~category().name.indexOf(\'Seq\')">'+
		'<input type="checkbox" data-bind="checked:includehidden">Include hidden columns<br>'+
		'&nbsp;&nbsp;Mark masked sequence with <select data-bind="options:maskoptions,value:masksymbol"></select></div>'+
		'<br data-bind="visible:!~category().name.indexOf(\'Seq\')">&nbsp;&nbsp;Cut names to first <select data-bind="options:[\'\',\'space\',\'digit\',\'punct.\'],value:truncsymbol"></select>, max. <input type="text" class="num" data-bind="value:trunclen" style="margin-top:5px">letters</div>');
		
		var makebtn = $('<a class="button orange" data-bind="visibility:format">Make file</a>');
		makebtn.click(function(){ parseexport(); });
		var frontwindow = makewindow("Export data",frontcontent,{icn:'export.png',id:type,flipside:'front',btn:makebtn,nowrap:true});
		
		var backcontent = $('<div class="sectiontitle"><img src="images/file.png"><span data-bind="text:filename()+(~filename().indexOf(\'.\')?\'\':fileext())"></span></div>'+
		'<div class="insidediv" style="max-width:400px;max-height:150px;overflow:auto"><div id="exportpaper" class="paper"></div></div>');
		var backbtn = $('<a class="button backbtn" style="padding-left:17px;margin-top:25px"><span style="vertical-align:2px">&#x25C0;</span> Options</a>');
		backbtn.click(function(){ flipexport(); exportmodel.filename(exportmodel.savename().replace(' ','_')); });
		
		var downloadbtn = $('<a class="button" style="margin-left:40px;margin-top:25px" data-bind="visible:fileurl,attr:{href:fileurl}">Download</a>');
		var backwindow = makewindow("Export data",[backcontent,backbtn,downloadbtn],{icn:'export.png', flipside:'back', id:type});
		
		ko.applyBindings(exportmodel,$('#'+type)[0]);
		if(options) parseexport(options);
	}
// save data to library	
	else if(type=='save'){
		var content = 'Store current data as <span data-bind="visible:savetargets().length==1,text:savetarget().name"></span><select data-bind="visible:savetargets().length>1, options:savetargets, optionsText:\'name\', value:savetarget"></select> analysis in the library.<br><br>'+
		'<span data-bind="fadevisible:savetarget().type!=\'overwrite\'">Name: <input type="text" class="hidden" id="savename" title="Click to edit" value="'+exportmodel.savename()+'"></span>';
		var opttitle = expandtitle({title:'Store visualisation settings', desc:'Attach optional metadata'}).css('margin-top','5px');
		var optdiv = $('<div class="insidediv" style="display:none;margin-bottom:0"><form id="saveform" onsubmit="return false">'+
		'<input type="checkbox" name="model.zoomlevel" id="zlbox"> zoom level '+
		'<input type="checkbox" name="position" onclick="getElementById(\'zlbox\').checked=this.checked"> alignment position<br>'+
		'<input type="checkbox" name="colorscheme,boxborder,font,maskcolor,maskletter,anccolor,ancletter"> sequence colors'+
		//(model.dnasource()&&!model.isdna()?'<input type="checkbox" name="model.seqtype"> sequence translation':'')+
		'</form></div>');
		var savebtn = $('<a class="button orange" onclick="savefile(this)">Save</a>');
		var savewindow = makewindow("Save to libray",[content,opttitle,optdiv],{icn:'save.png', id:type, btn:savebtn});
		ko.applyBindings(exportmodel,savewindow[0]);
	}
// stats about current data
	else if(type=='info'){
		var lib = librarymodel;
		var sharelink = ~model.sourcetype().indexOf('local')? '':lib.shareicon(lib.openitem(),'','source data',lib.importurl);
					
		var list = '<ul>'+
		'<li data-bind="visible:treesource">Number of tree nodes: <span data-bind="text:nodecount"></span></li>'+
		'<li data-bind="visible:treesource">Number of tree leafs: <span data-bind="text:leafcount"></span></li>'+
		'<li data-bind="visible:seqsource()">Sequence type: <select data-bind="options:[\'DNA\',\'RNA\',\'codons\',\'protein\'],value:seqtype"></select></li>'+
		'<li>Number of sequences: <span data-bind="text:seqcount"></span>, in total of <span data-bind="html:totalseqlength"></span></li>'+
		'<li>Sequence length: from <span data-bind="html:minseqlength"></span> to <span data-bind="html:maxseqlength"></span></li>'+
		'<li>Sequence matrix length: <span data-bind="html:alignlength"></span> columns '+
		'<span data-bind="visible:hiddenlen,text:\'(\'+hiddenlen()+\' columns hidden)\'"></span></li>'+
		'<li>Sequence matrix height: <span data-bind="text:alignheight"></span> rows</li>'+
		'<li data-bind="visible:sourcetype">Data source: <span data-bind="text:sourcetype"></span> '+sharelink+'</li>'+
		'<li data-bind="visible:treesource()&&!ensinfo().type">Tree file: <span data-bind="text:treesource"></span></li>'+
		'<li data-bind="visible:seqsource()&&!ensinfo().type">Sequence file: <span data-bind="text:seqsource"></span></li>'+
		'</ul>';
		
		var enslist = '<div data-bind="if:ensinfo().type" style="margin-top:5px"><span style="color:#666">About Ensembl dataset:</span><br>'+
		'<ul data-bind="with:ensinfo"><!-- ko if: type==\'homology\' -->'+
		'<li>Homologs to <span data-bind="text:species"></span> gene '+
		'<a data-bind="attr:{href:\'http://www.ensembl.org/\'+species.replace(\' \',\'_\')+\'/Gene/Summary?g=\'+id,target:\'_blank\',title:\'View in Ensembl\'},text:id"></a></li>'+
		'<!-- /ko --><!-- ko if: ~type.indexOf(\'genetree\') -->'+
		'<li>Genetree <a data-bind="attr:{href:\'http://www.ensembl.org/\'+(~id.indexOf(\'ENSGT\')?\'Multi/GeneTree?gt=\':\'Gene/Summary?g=\')+id,target:\'_blank\',title:\'View in Ensembl\'},text:id"></a></li>'+
		'<!-- /ko --><!-- ko if: ~type.indexOf(\'alignment\') -->'+
		'<li>EPO alignment: <span data-bind="text:id.replace(\'/\',\': \').replace(\'_\',\' \')"></span></li>'+
		'<!-- /ko --></ul></div>';
		
		var dialogwindow = makewindow("Data information",[list,enslist],{btn:'OK',icn:'info.png',id:type});
		ko.applyBindings(model,dialogwindow[0]);
	}
// start new Prank alignment job
	else if(type=='align'){
		var nameinput = $('<input type="text" class="hidden" value="'+exportmodel.savename()+'" title="Click to edit">');
		var namespan = $('<span class="note">Descriptive name: </span>').append(nameinput);
		var opttitle = expandtitle({title:'Alignment options', desc:'Click to toggle options', info:'Hover option labels for description'});
		var tunetitle = expandtitle({title:'Fine-tuning', desc:'Click to toggle additional parameters', css:{'margin-top':'5px'}});
		var treecheck = $.isEmptyObject(treesvg)?'checked="" disabled=""':''; //new tree needed
		var writetarget = (exportmodel.savetargets().length>1? '<span class="label" title="Specify the saving place for the new analysis in the library, relative the to the input '+
		'(currently open) analysis">Save as</span> <select data-bind="options:exportmodel.savetargets, optionsText:\'name\', value:exportmodel.savetarget"></select>':
		'The result will be saved as new root')+' analysis in the <a onclick="dialog(\'library\')">library</a>.<br>';
		exportmodel.savetarget(exportmodel.savetargets()[0]); //default: child||silbing||root
		
		
		var optform = $('<form id="alignoptform" onsubmit="return false">'+writetarget+'<br>'+
		(model.hiddenlen()?'<input name="includehidden" type="checkbox" data-bind="checked:exportmodel.includehidden">'+
			'<span class="label" title="Align also '+model.hiddenlen()+' collapsed sequence columns">include collapsed columns</span>':'')+'<hr>'+
		'<input type="checkbox" name="newtree" '+treecheck+'><span class="label" title="Create a new NJ tree to guide the sequence alignment process (uncheck to use the current tree)">create a guidetree</span>'+
		'<br><input type="checkbox" checked="checked" name="anchor"><span class="label" title="Use Exonerate anchoring to speed up alignment">alignment anchoring</span> '+
		'<br><input type="checkbox" name="iterate" data-bind="checked:iterate"><span class="label" title="Iterating re-alignment cycles can improve tree phylogeny. Uncheck this option to keep the input tree intact">'+
			'iterate alignment for</span> <select name="rounds"><option>2</option><option>3</option><option>4</option><option selected="selected">5</option></select> cycles'+
		'<br><div class="sectiontitle small"><span class="grey">or</span></div>'+
		'<input type="checkbox" name="keep"><span class="label" title="Keep current alignment intact and just add sequences for ancestral nodes">keep current alignment</span></form>');
		var tunediv = $('<div class="insidediv numinput" style="display:none;margin-bottom:0">'+
		'<input type="checkbox" checked="checked" name="F"><span class="label" title="Force insertions to be always skipped. Enabling this option is generally beneficial but may cause an excess of gaps if the guide tree is incorrect">trust insertions (+F)</span>'+
		'<br><input type="checkbox" name="nomissing"><span class="label" title="Do not treat gaps as missing data. Use +F for terminal gaps">no missing data</span>'+
		'<div class="sectiontitle small"><span>alignment model parameters</span></div>'+
		'<div data-bind="visible:isdna"><input type="checkbox" name="translate">'+
		  '<span class="label" title="Translate and align cdna with protein or codon model">align as</span>'+
		    ' <select name="translateto" data-bind="options:transopt,optionsText:\'t\',optionsValue:\'v\'"></select>'+
			'<br><span class="label" title="Default values are empirical, based on the input data">dna base frequencies</span>'+
			' <input type="text" name="A" placeholder="A"><input type="text" name="C" placeholder="C"><input type="text" name="G" placeholder="G"><input type="text" name="T" placeholder="T">'+
			'<br><span class="label" title="Transition/transversion rate ratio in substitution model">K</span> <input type="text" name="kappa" class="num" placeholder="2">'+
			' <span class="label" title="Purine/pyrimidine rate ratio in substitution model">P</span> <input type="text" name="rho" class="num" placeholder="1"></div>'+
		'<span class="label" title="Gap opening rate">gap opening</span> <input type="text" name="gaprate" style="width:45px" data-bind="attr:{placeholder:gaprate}">'+
			' <span class="label" title="Gap extension probability">gap extension</span> <input type="text" name="gapext" data-bind="attr:{placeholder:gapext}" style="width:40px">'+
		'<div data-bind="visible:iterate" class="sectiontitle small"><span class="label" title="The optimization score is used to assess an alignment iteration result">optimization scoring</span></div>'+
		'<div data-bind="visible:iterate"><span class="label" title="Indel penalties for alginment scoring (with substitution penalty as 1)">indels with length</span> 1:'+
		  '<input type="text" name="ind1" placeholder="6" class="num"> 2:<input type="text" name="ind2" placeholder="8" class="num"> 3:<input type="text" name="ind3" placeholder="9" class="num"> 4+:<input type="text" name="ind4" placeholder="10" class="num"></div>'+
		'<hr><span class="label" title="Specifing a seed number allows reproducing alignment results">random number seed</span> <input type="text" name="seed">'+
		'<br><input type="checkbox" name="uselogs"><span class="label" title="Slow, but may be needed for very large number of sequences">use log space</span></div>');
		optform.append(tunetitle,tunediv);
		var optdiv = $('<div class="insidediv" style="display:none">').append(optform);
		
		var alignbtn = $('<a class="button orange">Start alignment</a>');
		alignbtn.click(function(){ sendjob({form:$('form',optdiv)[0],btn:alignbtn,name:nameinput.val()}); });
		
		var dialogwindow = makewindow("Make alignment",['Current sequence data will be aligned with <a href="http://prank-msa.googlecode.com" target="_blank">Prank</a> aligner.<br><hr>',namespan,opttitle,optdiv,'<br>'],{id:type, btn:alignbtn, icn:'icon_prank', nowrap:true});
		
		ko.applyBindings(model,dialogwindow[0]);
	}
// notifications & submitted job status window
	else if(type=='jobstatus'){
		communicate('getlibrary'); //refresh data
		var sections = [];
		//set up sections of notifications window
		var notifheader = $('<div class="sectiontitle" data-bind="visible:notifications"><img src="images/info.png"><span>Notifications</span></div>');
		
		var realignnotif = $('<div data-bind="visible:treealtered()||noanc()" class="sectiontext"><b>Update the alignment</b><br>'+
		'Current sequence alignment needs to be updated to <span data-bind="visible:treealtered">reflect the modifications in phylogenetic tree and </span>calculate ancestral sequences.<br>'+
		'<div class="insidediv">'+(exportmodel.savetargets().length>1?'<span class="label" title="Choose a library slot '+
		'for the updated alignment, relative the to the input (currently open) analysis">Store update as</span> '+
		'<select data-bind="options:exportmodel.savetargets, optionsText:\'name\', value:exportmodel.savetarget"></select>':
		'The update is stored as new root')+' analysis in the <a onclick="dialog(\'library\')">library</a>.<hr>'+
		'<input id="keepalign" type="checkbox" data-bind="checked:!treealtered()"><span class="label" title="Freeze alignment, only '+
		'calculate the ancestral sequences (fast update)">keep current alignment</span>'+
		'<span data-bind="visible:isdna"><br><input type="checkbox" checked="checked" id="usecodons">use codon model</span></div><br>'+
		'<a class="button square" onclick="model.treealtered(false);model.noanc(false);" title="Hide this notification">Dismiss</a>'+
		'<a class="button square red" data-bind="visible:treealtered()&&treebackup" onclick="model.selectundo(\'firsttree\');model.undo();" title="Undo tree modifications">Revert tree</a></div>');
		exportmodel.savetarget(exportmodel.savetargets()[0]);
		var realignbtn = $('<a class="button square orange" title="Update current dataset using PRANK">Update alignment</a>');
		realignbtn.click(function(){
			if(model.noaccount()) realignbtn.text('Account required!');
			else sendjob({btn:realignbtn, keepalign:$('#keepalign').val(), usecodons:$('#usecodons').val()});
		});
		realignnotif.append(realignbtn,'<br>',writetarget,'<hr>');
		
		var offlinenotif = $('<div data-bind="visible:offline" class="sectiontext"><b>Wasabi is offline</b><br>'+
		'The Wasabi server is currently out of reach, so some functions may not work.<br>'+
		'<a class="button square orange" onclick="communicate(\'checkserver\',\'\',{btn:this,restore:true})" title="Check server connection">Reconnect</a>'+
		'<a class="button square" href="http://wasabiapp.org/feedback">Contact us</a> <hr></div>');
		
		var accountnotif = $('<div data-bind="visible:noaccount" class="sectiontext"><b>Wasabi is working in basic mode</b><br>For '+
		'<span class="label" title="Storage of analysis files on server, launching realignment jobs, sharing etc.">Wasabi features</span>'+
		' using remote storage and tools, you need a user account.<br>'+
		'<div data-bind="slidevisible:settingsmodel.email&&!settingsmodel.tmpuser()"><input style="width:300px;margin-top:5px" '+
		  'type="email" id="usermail" placeholder="e-mail address for Wasabi notifications" title="Your e-mail address is needed '+
		  'for core Wasabi functions and will not be shared with 3rd parties."></div>'+
		'<div class="insidediv"><span class="label" title="When this option is used, the new account and its content will be removed after 24 hours.">Create temporary (1-day) account</span> '+
		'<a class="button toggle" data-bind="css:{on:settingsmodel.tmpuser},click:settingsmodel.toggle.bind($data,settingsmodel.tmpuser)">'+
		'<span class="light"></span><span class="text" data-bind="text:settingsmodel.btntxt(settingsmodel.tmpuser)"></span></a></div><br></div>');
		var accountbtn = $('<a class="button square orange" title="Create new Wasabi user account">Create account</a>');
		accountbtn.click(function(){
			if(settingsmodel.email && !unwrap(settingsmodel.tmpuser)){
				var usermail = $('#usermail').val();
				if(!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(usermail)){ $('#usermail').val('Please enter your e-mail address!'); return false; }
			} else { var usermail = ''; }
			var addid = librarymodel.importurl.substr(0,3)=='id='? librarymodel.importurl.substr(3) : '';
			communicate('createuser',{email:usermail, tmpuser:unwrap(settingsmodel.tmpuser), addshared:addid, username:usermail.split('@')[0].replace(/[\.\_]/g,' ')},{btn:accountbtn, restore:true, parse:true, success:function(resp){
				if(resp.userid){
					if(usermail){
						communicate('sendmail',{email:usermail,userid:resp.userid});
						settingsmodel.usermail(usermail);
					}
					settingsmodel.userid(resp.userid);
					if(resp.userexpire) settingsmodel.useraccounts(parseInt(resp.userexpire));
					dialog('newuser');
				}
		}})});
		accountnotif.append(accountbtn,'<hr>');
		
		var errornotif = $('<div data-bind="visible:errors" class="sectiontext">An error occured when communicating with Wasabi server, so some functions may not work.<br>'+
		'The list of errors has been saved. In addition, your feedback would help us to fix the issue.<br>'+
		'<a class="button square" onclick="model.errors(\'\');">Dismiss</a> <a class="button square" onclick="dialog(\'errorlog\')">View errors</a> '+
		'<a class="button square" href="http://wasabiapp.org/feedback" target="_blank">Contact us</a> <hr></div>');
		
		var newver = model.version.remote();
		var updatenotif = $('<div data-bind="visible:update" class="sectiontext">'+
		'There is an update available for Wasabi (current v.'+model.version.local+').<div class="insidediv incontent">Wasabi version '+newver+':'+
		'<br><ul><li>'+model.version.lastchange.replace(/\* /g,'</li><li>')+'</li></ul></div></div>');
		var skipbtn = $('<a class="button square red" title="Skip this version">Skip</a>');
		skipbtn.click(function(){ settingsmodel.skipversion(newver); settingsmodel.saveprefs(); });
		updatebtn = $('<a class="button square orange" data-bind="visible:settingsmodel.autoupdate" title="Auto-update Wasabi">Update</a>');
		updatebtn.click(function(){ communicate('update','',{btn:updatebtn, success:function(resp){
			if(~resp.indexOf('Updated')){
				updatebtn.text('Update complete');
				setTimeout(function(){ model.version.remote(model.version.local); closewindow('all'); }, 2000);
				setTimeout(function(){ makewindow('Wasabi updated','Wasabi is now updated to version '+newver+
				'.<br> To continue, close the web browser window and restart Wasabi.',{icn:'info',backfade:true}); }, 3000);
		}}});});
		var dwnldbtn = $('<a class="button square" href="http://wasabiapp.org/download/wasabi" target="_blank" title="Manually download and update Wasabi">Download</a>');
		dwnldbtn.click(function(){
			updatenotif.html('To complete the update, replace the current Wasabi application with the downloaded app and relaunch Wasabi.');
			setTimeout(function(){ model.version.remote(model.version.local); }, 7000);
		});
		updatenotif.append(skipbtn,updatebtn,dwnldbtn,'<hr>');
		
		sections.push(notifheader, accountnotif, realignnotif, offlinenotif, errornotif, updatenotif);
		$.each(sections,function(i,section){
			ko.applyBindings(model, section[0]); //bind notifications html with the main datamodel
		});
		//HTML for representing running server jobs:
		var jobslist = $('<div><div class="sectiontitle" data-bind="visible:jobsview().length"><img src="images/run.png">'+
		'<span>Status of background tasks</span></div><div class="insidediv incontent" data-bind="visible:jobsview().length,'+
		'foreach:{data:jobsview, afterAdd:addanim}"><div class="itemdiv" data-bind="attr:{id:\'job_\'+id}">'+
		'<span class="note">Name:</span> <span class="logline" data-bind="text:name"></span><br>'+
		'<span class="note">Status:</span> <span data-bind="text:st().str, css:{red:st().str==\'Failed\',label:st().inf},'+
		'attr:{title:st().inf}"></span><br>'+
		'<span class="note">Job type:</span> <span data-bind="text:$data.type?type():\'Realignment\'"></span>'+
		'<a class="button itembtn" data-bind="text:[\'Cancel\',\'Kill\',\'Open\',\'Delete\'][st().nr], css:{red:st().nr!=2},'+
		  'attr:{title:[\'Cancel job\',\'Terminate job\',\'Import and open the results\',\'Delete files\'][st().nr]},'+
		  'click:st().nr==2?$parent.importitem:$parent.removeitem"></a>'+
		'<a class="button itembtn round gear" title="Click for more options" style="right:0" data-bind="visible:!running(),'+
		  'click:$parent.jobmenu"><span class="svgicon" style="padding:4px">'+svgicon('gear')+'</span></a><br>'+
		'<span class="note">Created:</span> <span data-bind="text:msectodate(unwrap(created))"></span><br>'+
		'<span class="note">Job ID:</span> <span data-bind="text:id"></span><br>'+
		'<span class="note">Feedback:</span> <span class="logline action" '+
		  'data-bind="click:function(itm,evt){ $parent.showfile(itm,evt,itm.logfile) },'+
		  'attr:{title:\'Last update \'+msectodate(updated)+\'. Click for full log.\'},html:$parent.parselog($data)"></span>'+
		'</div><div class="insidediv logdiv" style="display:none"></div><hr></div></div>');
		ko.applyBindings(librarymodel, jobslist[0]); //bind html with data from the library datamodel
		
		makewindow("Status overview",[sections,jobslist],{id:type,icn:'status'});
	}
// analyses library
	else if(type=='library'){
	var afterf = options.after? {after:options.after} : {};	
	communicate('getlibrary', '', afterf); //refresh data
	
	var header = $('<a class="button round back" title="View previous step" data-bind="fadevisible:cwd,click:updir"><span class="svgicon">'+svgicon('left')+'</span></a>'+
	'<a class="button round back gear" title="Click for options" data-bind="fadevisible:!cwd(),click:librarymenu"><span class="svgicon">'+svgicon('gear')+'</span></a>'+
	'<span class="dirtrail"><span data-bind="foreach:dirpath"><a class="button" title="Go to this step" data-bind="click:$parent.navigate"><span data-bind="html:$data?$parent.getitem($data).name():svgicon(\'home\')"></span></a></span></span>'+
	' <span style="position:absolute;top:6px;right:15px;">Sort:<select data-bind="options:sortopt,optionsText:\'t\',optionsValue:\'v\',value:sortkey"></select> '+
	'<span class="icon action" style="font:20px/16px sans-serif;vertical-align:-2px" data-bind="html:sortasc()?\'\u21A7\':\'\u21A5\',click:function(){sortasc(!sortasc())},'+
	'attr:{title:sortasc()?\'ascending\':\'descending\'}"></span></span>');
		
	var content = $('<div class="insidediv" data-bind="foreach:{data:libraryview,afterAdd:addanim,afterMove:function(){$(\'#library div.logdiv\').remove()}}">'+
	'<div class="itemdiv" data-bind="dragdrop:id,css:{activeitem:id==$parent.openid(),compact:settingsmodel.minlib,shared:$data.shared},style:{marginLeft:20*$parent.steplevel($data)+\'px\'},attr:{itemid:id}">'+  //item container
	'<div class="draghandle" data-bind="visible:!$parent.cwd()" title="Drag & drop to group analysis to collections"><span>&#x22EE;</span></div><div class="itemcontent">'+  //drag-drop handle
	'<span class="note">Name:</span> <input type="text" class="hidden" data-bind="value:name,disable:$data.shared,attr:{title:$data.shared?\'You cannot modify the name of shared analysis\':\'Click to edit name\'}"><br>'+   //NAME txt
		'<span class="note">Created:</span> <span data-bind="text:msectodate(created)"></span> '+   //TIME txt
		'<span class="svgicon abs hover blue" style="top:29px;right:180px" data-bind="visible:unwrap($data.outfile),event:{mouseover:$parent.timetip}">'+svgicon('time')+'</span><br>'+   //TIME icon
		'<span class="note" data-bind="text:($data.folder?\'Collection\':\'Analysis\')+\' ID:\'"></span> '+  //ID txt
		'<span class="rotateable">&#x25BA;</span><span class="action" title="Browse data files" data-bind="click:$parent.showfile, text:id"></span> '+  //filebrowse arrow
		'<span class="svgicon abs hover" style="top:29px; right:157px" data-bind="visible:!$data.shared||$data.info,css:{blue:$data.info,light:!$data.info()},event:{mouseover:$parent.infotip}">'+svgicon('info')+'</span><br>'+   //INFO icon
		'<span data-bind="visible:unwrap($data.outfile)||unwrap($data.children),html:$parent.shareicon($data)"></span>'+  //SHARE icon
		'<a class="button itembtn" data-bind="visible:unwrap($data.outfile)||unwrap($data.opendataset),click:function(item,e){getfile({id:item.id,btn:e.target})}, text:id==$parent.openid()?\'Restore\':\'Open\', '+
		  'attr:{title:id==$parent.openid()?\'Revert back to saved state\':\'Load data\'}"></a>'+  //OPEN btn
		  '<span data-bind="html:$parent.sourcetxt($data)"></span>'+  //data SOURCE txt
		  '<span data-bind="visible:$data.shared" class="label" style="color:#6D98B6;margin-left:5px" title="You can read or (re)move this dataset in your library but only the owner can modify its content">(shared)</span>'+   //shared txt
		'<a class="button itembtn childbtn arrow" data-bind="visible:children, click:$root.navigate,'+
		  'css:{activeitem:~$parent.openpath().indexOf(id),expanded:~$parent.dirpath().indexOf(id)},attr:{title:\'View \'+($data.folder?\'analyses in this collection\':\'next analysis step\')}"></a>'+  //children btn
		'<a class="button itembtn optbtn red" data-bind="visible:$data.shared&&!$parent.getitem($data.parentid()).shared, click:$parent.removeitem, attr:{title:\'Remove this analysis from your library\'}">Delete</a>'+   //DELETE btn
		'<a class="button itembtn optbtn" data-bind="visible:!$data.shared, click:$parent.opttip, attr:{title:\'Click to delete or move this analysis\'}">Modify</a>'+    //OPTIONS btn
		'<span class="action itemexpand" onclick="$(this).closest(\'div.itemdiv\').toggleClass(\'expanded\')" title="Reveal/hide more options"></span>'+   //expand arrow
		'</div></div></div>');
		
		var librarywindow = makewindow("Library of analyses",content,{id:type, header:header, icn:'library.png', nomaxw:true});
		ko.applyBindings(librarymodel,librarywindow[0]);
    }
// shortcut for error dialogs
	else if(type=='error'||type=='warning'||type=='notice'){
		if(typeof(options)=='string') options = { msg: options };
		if($('div.popupwindow').length>5 || (options.id && $('#'+options.id).length)){
			console.log('Skipped notice window: '+options.msg); return;
		}
		if(options.msg) makewindow(type.charAt(0).toUpperCase()+type.slice(1), options.msg ,{btn:'OK',icn:'warning',id:options.id});
		else{ console.log('Empty error dialog'); console.trace(); }
	}
// batch filter/collapse for sequence area
	else if(type=='seqtool'){
		var content = $('<div class="spinnercover"><span>Counting gaps...</span></div>'+
		'<div class="sectiontitle"><span>Filter alignment columns</span></div><div class="sectiontext">'+
		'<select data-bind="options:[\'Hide\',\'Mask\'],value:hideaction"></select> all sequence alignment columns with: '+
		'<ul><li><input type="checkbox" data-bind="checked:hideconserved"> fully conserved sequences,</li>'+
		'<li><input type="checkbox" data-bind="checked:minhidelimit"> unaligned sequences, or</li>'+
		'<li><input id="hidecolinp" type="text" class="num nogap" data-bind="value:hidelimit,valueUpdate:\'afterkeydown\'"> '+
		  '<span class="note" data-bind="text:\'(\'+hidelimitperc()+\'%)\'"></span> or less rows of sequence.<br>'+
		'<span class="note">0%</span><span class="draggerline"></span><span class="note">100%</span></li><hr>'+
		'<li>consider <span data-bind="visible:!model.hasdot()">gaps</span><select data-bind="visible:model.hasdot, options:[\'indels\',\'insertions\',\'deletions\'],value:gaptype"></select></span> longer than '+
		  '<input type="text" class="num nogap" data-bind="value:gaplen,valueUpdate:\'afterkeydown\'"> columns.</li>'+
		'<li data-bind="slidevisible:hideaction()==\'Hide\'">exclude <input type="text" class="num nogap" data-bind="value:buflen,valueUpdate:\'afterkeydown\'"> columns from each gap edge.</li></ul>'+
		'</div><div>&nbsp;This will <span class="label" data-bind="visible:hideaction()==\'Hide\'" title="Use (right-click) menu in alignment area to remove collapsed columns from dataset">collapse</span>'+
		'<span class="label" data-bind="visible:hideaction()==\'Mask\'" title="Use (right-click) menu in alignment area to to hide masked columns">mask</span> <span data-bind="text:hidecolcount"></span> '+
		'<span class="note" data-bind="text:\'(\'+hidecolperc()+\'% of)\'"></span> alignment columns.</div>');
		_paq.push(['trackEvent','tools','gap_hiding']); //record event
		
		var slider = $('<span class="dragger" data-bind="style:{marginLeft:\'-7px\',left:hidelimitperc()+\'%\'}"></span>');
		var sliderline = $('.draggerline',content);
		sliderline.append(slider);
		
		var applybtn = $('<a class="button orange">Apply</a>');
		applybtn.click(function(){ 
			closewindow(applybtn);
			setTimeout(function(){ toolsmodel.hideaction()=='Mask'? maskdata('columns','skip') : hidecolumns(); },500);
		});
		
		var dialogwindow = makewindow('Sequence tools',content,{id:type,icn:'seq',btn:['Cancel',applybtn],closefunc:function(){clearselection()}});
		var slidew = sliderline.width();
		slider.draggable({ //slider for adjusting affected column cutoff
			axis: "x", 
			containment: 'parent',
			drag: function(e,elem){ toolsmodel.hidelimitperc((elem.position.left+4)/slidew*100) }
		});
		ko.applyBindings(toolsmodel,dialogwindow[0]);
		setTimeout(function(){toolsmodel.countgaps()},500);
	}
//batch edit/hide for tree area
	else if(type=='treetool'){
		var title = $('<div class="sectiontitle"><span>Prune tree leafs</span></div>');
		var content = $('<div class="sectiontext">You can mark/unmark tree leafs by clicking on a leaf name<br>or by dragging in the sequence area.<br><br></div>');
		_paq.push(['trackEvent','tools','tree_pruning']); //record event
		
		var emptyleaves = [];
		$.each(leafnodes,function(name,node){ if(!sequences[name]) emptyleaves.push(name); });
		if(emptyleaves.length){
			var markbtn = $('<a class="button square small">Mark empty leafs</a>');
			markbtn.click(function(){
				$.each(leafnodes,function(name,node){ 
					if(!sequences[name]) node.highlight(true); else node.highlight(false);
			});});
			var s = emptyleaves.length>1? ['s','ve'] : ['','s'];
			content.append(emptyleaves.length+' leaf'+s[0]+' ha'+s[1]+' no sequence data.',markbtn,'<br><br>');
		}
		
		content.append('Then click "Apply" to <select data-bind="options:[\'hide\',\'prune\'],value:leafaction"></select> '+
		'<select data-bind="options:[\'marked\',\'unmarked\'],value:leafsel"></select> tree leafs.<br>'+
		'<span id="treetoolerror" style="color:red"></span>');
		
		var applybtn = $('<a class="button orange">Apply</a>');
		applybtn.click(toolsmodel.processLeafs);
		var closefunc = function(){ clearselection(); toolsmodel.markLeafs('unmark'); toolsmodel.prunemode = false; };
		
		var dialogwindow = makewindow('Tree tools',[title,content],{id:type,icn:'tree',btn:['Cancel',applybtn],closefunc:closefunc});
		clearselection(); toolsmodel.markLeafs('unmark'); toolsmodel.prunemode = true;
		if(model.selmode()!='rows') model.selmode('rows');
		ko.applyBindings(toolsmodel,dialogwindow[0]);
	}
//system preferences
	else if(type=='settings'){
		var content = $('<div class="insidediv" style="margin:0;padding:5px;">');
		content.append('<div class="row" style="width:380px" data-bind="visible:!model.offline()">'+
			'<span class="label" title="Session data is saved to analysis library">Autosave after every</span> <select data-bind="options:autosaveopt,value:autosaveint"></select>'+
			'<a class="button toggle" data-bind="css:{on:autosave},click:toggle.bind($data,autosave)"><span class="light"></span><span class="text" data-bind="text:btntxt(autosave)"></span></a></div>'+
		'<div class="row">Keep up to <select data-bind="options:[1,5,15,30],value:undolength"></select> <span class="label" title="Actions history enables to undo/redo previous data edits. With large datasets, it may affect the application performance.">actions in undo list</span>'+
		'<a class="button toggle" data-bind="css:{on:undo},click:toggle.bind($data,undo)"><span class="light"></span><span class="text" data-bind="text:btntxt(undo)"></span></a></div>');
		
		var seqwrap = $('<div class="rowwrap" data-bind="visible:model.seqsource()">');
		var seqrows = $('<div class="row bottombtn">').append(expandtitle({title:'Colour sequences:', desc:'Click for additional settings', target:seqwrap, minh:'34px', maxh:'auto'}).css('display','inline-block'));
		seqrows.append(' <select data-bind="options:coloropt,value:colorscheme"></select> colour scheme<br>'+
		//'<span class="note" data-bind="text:colordesc[colorscheme()]"></span><br>'+
			'<span>Show letters in <select style="margin-top:10px" data-bind="options:fontopt,value:font"></select> with '+
			'<select data-bind="options:[\'border\',\'no border\'],value:boxborder"></select></span><br>'+
			'<span>Masked sites in <select data-bind="options:cases,value:maskletter"></select> with '+
			'<select style="margin-top:10px" data-bind="options:maskcolors,value:maskcolor"></select> background</span><br>'+
			'<span>Ancestral sites in <select data-bind="options:cases,value:ancletter"></select> with '+
			'<select style="margin-top:10px" data-bind="options:anccolors,value:anccolor"></select> backg.</span>');
		seqwrap.append(seqrows);
		
		var treewrap = $('<div class="rowwrap" data-bind="visible:model.treesource()">');
		var treerows = $('<div class="row bottombtn">').append(expandtitle({title:'Tree leaf labels:', desc:'Click for additional settings', target:treewrap, minh:'34px', maxh:'auto'}).css('display','inline-block'));
		treerows.append(' <select data-bind="options:leaflabels,value:leaflabel"></select><br>'+
			'<span>Tree node labels <select style="margin-top:10px" data-bind="options:nodelabels,value:nodelabel"></select></span><br>'+
			'<span>Node spot size <select style="margin-top:10px" data-bind="options:csizes,value:csize"></select></span>');
		treewrap.append(treerows);
			
		var launchwrap = $('<div class="rowwrap">');
		var launchrows = $('<div class="row bottombtn">').append(expandtitle({title:'When Wasabi launches:', desc:'Click for additional settings. These settings take effect after reloading the web page'+(settingsmodel.local?' and/or restarting Wasabi server':''), target:launchwrap, minh:'34px', maxh:'auto'}).css('display','inline-block'));
		launchrows.append(' open <select style="margin-bottom:10px" data-bind="options:launchopt,value:onlaunch"></select><br>'+
			'Restore zoom level <a class="button toggle" data-bind="css:{on:keepzoom},click:toggle.bind($data,keepzoom)">'+
			'<span class="light"></span><span class="text" data-bind="text:btntxt(keepzoom)"></span></a>');
		launchwrap.append(launchrows);
		if(settingsmodel.local){
			launchwrap.append('<div class="row">Check for updates <a class="button square small" style="margin:-5px 20px 0;font-size:14px" onclick="checkversion(this)">check now</a> <a class="button toggle" data-bind="css:{on:checkupdates},click:toggle.bind($data,checkupdates)">'+
			'<span class="light"></span><span class="text" data-bind="text:btntxt(checkupdates)"></span></a></div>'+
			'<div class="row"><span class="label" title="Which browser to use when Wasabi server starts. Chrome usually has the fastest performance">Autolaunch Wasabi in</span> <select data-bind="options:browsers,optionsText:\'n\',optionsValue:\'v\',value:openbrowser"></select> web browser</div>'+
			'<div class="row"><span class="label" title="This folder will hold the analysis library and other data. Click to edit the folder path">Keep Wasabi data in</span> <input id="datadir" type="text" class="hidden" style="margin:0;width:220px" data-bind="value:datadir" title="Click to edit folder path"></div>');
			if(settingsmodel.local=='osxbundle'){
				launchwrap.append('<div class="row"><span class="label" title="Wasabi server will use a new window instead of the Console app to show its status">'+
					'Show server feedback</span> <a class="button toggle" data-bind="css:{on:bundlestart},click:toggle.bind($data,bundlestart)">'+
					'<span class="light"></span><span class="text" data-bind="text:btntxt(bundlestart)"></span></a></div>');
			}
			else if(settingsmodel.local=='linux'){
				launchwrap.append('<div class="row"><span class="label" title="Places a double-clickable shortcut to desktop for easy launching">'+
					'Create desktop launcher</span> <a class="button toggle" data-bind="css:{on:linuxdesktop},click:toggle.bind($data,linuxdesktop)">'+
					'<span class="light"></span><span class="text" data-bind="text:btntxt(linuxdesktop)"></span></a></div>');
			}
		}
			
		var uiwrap = $('<div class="rowwrap">');
		var uirows = $('<div class="row bottombtn">').append(expandtitle({title:'User interface:', desc:'Click for additional settings', target:uiwrap, minh:'34px', maxh:'171px'}).css('display','inline-block'));
		uirows.append(' all animations <a class="button toggle" data-bind="css:{on:allanim},click:toggle.bind($data,allanim)"><span class="light"></span><span class="text" data-bind="text:btntxt(allanim)">'+
			'</span></a><br><span class="label" style="margin-top:10px" title="Disable window animations in case of blurry text">Dialog window animations</span>'+
			'<a class="button toggle" style="margin-top:8px;" data-bind="css:{on:windowanim},click:toggle.bind($data,windowanim)"><span class="light"></span>'+
			'<span class="text" data-bind="text:btntxt(windowanim)"></span></a>');
		uiwrap.append(uirows, '<div class="row bottombtn"><span class="label" title="Click on bottom-left edge of menubar to toggle the display mode">Auto-hide menubar in minimized mode</span>'+
			'<a class="button toggle" data-bind="css:{on:hidebar},click:toggle.bind($data,hidebar)"><span class="light"></span><span class="text" data-bind="text:btntxt(hidebar)"></span></a><br>'+
			'<span style="display:inline-block;margin-top:10px">Compact viewmode of analysis library</span>'+
			'<a class="button toggle" style="margin-top:8px;" data-bind="css:{on:minlib},click:toggle.bind($data,minlib)"><span class="light"></span><span class="text" data-bind="text:btntxt(minlib)"></span></a><br>'+
			'<span style="display:inline-block;margin-top:10px">Show analysis path in library</span>'+
			'<a class="button toggle" style="margin-top:8px;" data-bind="css:{on:ladderlib},click:toggle.bind($data,ladderlib)"><span class="light"></span><span class="text" data-bind="text:btntxt(ladderlib)"></span></a>'+
			'</div>'+
		'<div class="row"><span class="label" title="The analysis sharing links are only useful when Wasabi server is accessible to other computers">Library data sharing links</span>'+
			'<a class="button toggle" data-bind="css:{on:sharelinks},click:toggle.bind($data,sharelinks)"><span class="light"></span><span class="text" data-bind="text:btntxt(sharelinks)"></span></a></div>');
		
		content.append(launchwrap, seqwrap, treewrap, uiwrap);
		content.append('<div class="row bottombtn" data-bind="visible:userid"><span class="label" data-bind="attr:{title:\'User ID: \'+userid()}">User account</span> <span class="progressline" style="width:150px;margin-left:20px" '+
			'data-bind="visible:datalimit, attr:{title:dataperc()+\' of \'+numbertosize(datalimit,\'byte\')+\' server space in use\'}">'+
			'<span class="bar" data-bind="style:{width:dataperc}"></span><span class="title" data-bind="html:\'Library size: \'+numbertosize(datause(),\'byte\')"></span></span>'+
			'<a class="button toggle" style="margin-top:-2px;padding-bottom:2px" onclick="dialog(\'account\')">Settings</a><br><br>'+
			'<span class="label" title="This web browser remembers and opens your account URL when you go to Wasabi web page. Disable on public computers">Remember me on this computer</span> '+
			'<span class="svgicon share" style="margin-left:35px" title="View/share your account URL" onclick="dialog(\'share\',{library:true})">'+svgicon('link')+'</span>'+
			'<a class="button toggle" data-bind="css:{on:keepuser},click:toggle.bind($data,keepuser)"><span class="light"></span><span class="text" data-bind="text:btntxt(keepuser)"></span></a></div>');
				
		var dialogwindow = makewindow('Settings',content,{id:type, icn:type, btn:'OK', closefunc:settingsmodel.saveprefs});
		ko.applyBindings(settingsmodel,dialogwindow[0]);
	}
//translate sequnces
	else if(type=='translate'){
		var header = '<div style="width:420px;margin-bottom:20px">Display the sequences as <span class="buttongroup">'+
		'<a class="button left" onclick="translateseq(\'DNA\')" data-bind="css:{pressed:isdna,disabled:!dnasource()}">nucleotides</a>'+
		'<a class="button middle" onclick="translateseq(\'codons\')" data-bind="css:{pressed:seqtype()==\'codons\',disabled:!dnasource()}">codons</a>'+
		'<a class="button right" onclick="translateseq(\'protein\')" data-bind="css:{pressed:seqtype()==\'protein\'}">protein</a></span><div>';
		_paq.push(['trackEvent','tools','translate']); //record event
		
		var dnaimport = $('<div data-bind="visible:!dnasource()">To backtranslate a protein sequence, Wasabi needs the cdna sequences used for the protein alignment.<br>'+
		'Drag or select data file(s) with the source cdna.<br></div>');
		var filedrag = $('<div class="filedrag">Drag cdna file here</div>');
		filedrag.bind('dragover',function(evt){ //file drag area
			filedrag.addClass('dragover'); evt.stopPropagation(); evt.preventDefault();
		evt.originalEvent.dataTransfer.dropEffect = 'copy';
	}).bind('dragleave',function(evt){
			filedrag.removeClass('dragover'); evt.stopPropagation(); evt.preventDefault();
	}).bind('drop',function(evt){
		filedrag.removeClass('dragover'); evt.stopPropagation(); evt.preventDefault();
		checkfiles(evt.originalEvent.dataTransfer.files,{windowid:type,mode:'importcdna'});
	});
		var fileinput = $('<input type="file" multiple style="opacity:0" name="file">');
		var form = $('<form enctype="multipart/form-data" style="position:absolute">');
		fileinput.change(function(){ checkfiles(this.files,{windowid:type,mode:'importcdna'}) });
		var selectbtn = $('<a class="button" style="vertical-align:0">Select files</a>');
		selectbtn.click(function(e){ fileinput.click(); e.preventDefault(); });
		var or = $('<span style="display:inline-block;font-size:18px;"> or </span>');
		form.append(fileinput); filedrag.append(form); dnaimport.append([filedrag,or,selectbtn]);
		var windowdiv = makewindow("Translate sequences",[header,dnaimport],{backfade:false,flipside:'front',icn:'translate.png',btn:'OK',id:type})[0];
		makewindow("Importing cdna",[],{backfade:false,flipside:'back',icn:'import.png',id:type});
		ko.applyBindings(model,windowdiv);
	}
//about/help/contact window
	else if(type=='about'){
		var content = $('<div class="sectiontitle"><span class="label" title="Current version: '+model.version.local+'">About Wasabi</span></div><div class="sectiontext">'+
		'Wasabi is a browser-based application for the visualisation and analysis of multiple alignment molecular sequence data.<br>'+
		'Its multi-platform user interface is built on most recent HTML5 and Javascript standards and it is recommended to use the latest version of '+
		'<a href="http://www.mozilla.org/firefox" target="_blank">Firefox</a>, <a href="http://www.apple.com/safari" target="_blank">Safari</a> '+
		'or <a href="http://www.google.com/chrome" target="_blank">Chrome</a> web browser to run Wasabi. <a href="http://wasabi.biocenter.helsinki.fi" target="_blank">Learn more about Wasabi &gt;&gt;</a></div>'+
		'<div class="sectiontitle"><span>Support</span></div><div class="sectiontext">'+
		'<a class="logo" href="http://www.biocenter.fi" target="_blank"><img src="images/logo_bf.png"></a>'+
		'<a class="logo" href="http://www.biocenter.helsinki.fi/bi" target="_blank"><img src="images/logo_uh.png"></a>'+
		'<a class="logo" href="http://ec.europa.eu/research/mariecurieactions" target="_blank"><img src="images/logo_mc.jpg"></a>'+
		'<a class="logo" href="http://www.helsinki.fi/biocentrum" target="_blank"><img style="height:30px" src="images/logo_bch.gif"></a></div>'+
		'<div class="sectiontitle"><span>Contact</span></div><div class="sectiontext">'+
		'Wasabi is being developed by Andres Veidenberg from the <a href="http://loytynojalab.biocenter.helsinki.fi" target="_blank">Löytynoja lab</a> in Institute of Biotechnology, University of Helsinki.<br>'+
		'You can contact us via our <a href="http://wasabiapp.org/feedback" target="_blank">feedback webpage &gt;&gt;</a></div>');
		var dialogwindow = makewindow('About',content,{id:type, icn:'info', btn:'OK'});
	}
//welcome dialog for a new (previously) created user
	else if(type=='newuser'){
		var expires = !isNaN(settingsmodel.useraccounts)? settingsmodel.useraccounts : '';
		var note = unwrap(settingsmodel.tmpuser)?'Your temporary account is removed after 24 hours':expires?'Neglected user accounts are removed after '+expires+' days of last visit':'';
		var str = '<div class="sectiontitle"><span>Welcome to Wasabi</span></div>'+
		(options.newid?'The current user account <b>'+options.newid+'</b> is a new visitor on this computer.<br>'+
		'Should we use this account when you launch Wasabi in the future?':'You now have a personal Wasabi account.<br>'+
		'<a href="'+window.location+'" title="'+window.location+'" onclick="return false;">Current web page address</a> '+
		'is the access key to your account'+
		(unwrap(settingsmodel.usermail)?' and was sent to your e-mail address for future reference.':'.'))+'<br>'+
		'<div class="insidediv"><span class="label" title="This web browser remembers and opens your account URL when you go to Wasabi web page. Disable on public computers">Remember me on this computer</span> '+
		'<a class="button toggle" data-bind="css:{on:keepuser},click:toggle.bind($data,keepuser)"><span class="light"></span><span class="text" data-bind="text:btntxt(keepuser)"></span></a></div><br>'+
		'<span class="note"><a onclick="dialog(\'account\')">User account settings</a> are accessbile from "Tools" menu.</span><br>'+
		(note?'<span class="note">Note: '+note+'.</span><br>':'');
		var dialogwindow = makewindow('Welcome',str,{id:type, icn:'info', btn:'OK'})[0];
		ko.applyBindings(settingsmodel,dialogwindow);
	}
//user account settings window
	else if(type=='account'){
		communicate('checkuser','',{parse:'JSON', retry:true, success:function(resp){settingsmodel.username(resp.username||'anonymous'); settingsmodel.usermail(resp.email||''); }});
		var content = $('<div><div class="sectiontitle"><span>Wasabi user account</span></div><span data-bind="visible:datalimit">You currently use <span data-bind="text:dataperc"></span> of <span data-bind="html:numbertosize(datalimit,\'byte\')"></span> server disk space<br>allocated to your analysis library.<br></span><br>'+
		'<span class="label" title="Username is used to indicate the owner of shared data in other libraries.">Username:</span>'+
			'<input style="width:250px;margin-left:5px" id="username" placeholder="Username" data-bind="value:username">'+
		'<div data-bind="visible:email"><span class="label" title="Your e-mail address is needed for core Wasabi functions and will not be shared with 3rd parties.">E-mail:</span>'+
		'<input style="width:275px;margin-left:5px" type="email" id="usermail" placeholder="e-mail address for Wasabi notifications" data-bind="value:usermail"></div></div>');
		var erasediv = $('<div class="insidediv" style="padding:15px 0 10px 10px;"><span class="label" title="Delete the account including contents of your analysis library.">Delete my Wasabi user account</span></div>');
		var erasebtn = $('<a class="button red toggle">Erase data</a>');
		erasebtn.click(function(){
			if(erasebtn.text()!='Confirm'){ erasebtn.text('Confirm'); setTimeout(function(){ erasebtn.text('Erase data'); },3000); }
			else{ communicate('rmdir', {id:settingsmodel.userid()},{btn:erasebtn, nosync:true, after:function(){
				localStorage.removeItem('userid');
				settingsmodel.userid('');
				window.location = window.location.pathname;
			}}); }
		});
		erasediv.append(erasebtn); content.append(erasediv);
		var savebtn = $('<a class="button orange">Save</a>');
		savebtn.click(function(){
			if(settingsmodel.email){
				var usermail = $('#usermail').val();
				if(!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(usermail)){ $('#usermail').val('Please enter your e-mail address!'); return false; }
				communicate('writemeta',{id:settingsmodel.userid(),key:'email',value:usermail});
			}
			communicate('writemeta',{id:settingsmodel.userid(),key:'username',value:$('#username').val()},{btn:savebtn, restore:true, parse:'JSON', success:function(resp){
				savebtn.text('Saved'); closewindow(savebtn); settingsmodel.username(resp.username||'anonymous'); settingsmodel.usermail(resp.email||'');
			}});
		});
		var windowdiv = makewindow('Account settings',content,{id:type, icn:'info', btn:[savebtn,'Cancel']})[0];
		ko.applyBindings(settingsmodel,windowdiv);
	}
//display local error log content
	else if(type=='errorlog'){
		var errorlog = '<div class="insidediv"><ul class="wrap"><li>'+model.errors().replace(/ \*/g,'</li><li>')+'</li></ul></div>';
		makewindow('Error log',['Wasabi server errors:',errorlog],{id:type, icn:'info', btn:'OK'});
	}
//data sharing window
	else if(type=='share'){
		var opt = options || {};
		if(!opt.id) opt.id = librarymodel.openid();
		if(!opt.item) opt.item = librarymodel.getitem(opt.id);
		var url = librarymodel.sharelink(opt.item, opt.file||'', opt.url||'');
		var ckey = navigator.userAgent.match(/Mac/i)? '&#x2318;' : 'crtl';
		var dirtoggle = dirurl = '';
		var children = unwrap(opt.item.children);
		var dironly = opt.item.folder || (!opt.file && !unwrap(opt.item.outfile));
		settingsmodel.sharedir(dironly);
		_paq.push(['trackEvent','share',opt.id]); //record sharing event

		if(opt.library){
			var desc = '<br>to launch Wasabi with your analysis library';
			url = librarymodel.sharelink()+'/'+settingsmodel.userid();
		} else {
			var desc = '<br><span data-bind="visible:sharedir">to have the shared item imported to the library</span>'+
			'<span data-bind="visible:!sharedir()">or into Wasabi import dialog to display the shared data</span>';
			if(opt.url){ url = opt.url; }
			else if(opt.item && children){ //folder share btn
				dirurl = opt.item.folder? url : librarymodel.sharelink(opt.item,librarymodel.getitem('parentid',opt.id).id); //getitem=>child id
				var dirtoggle = '<span class="label" title="The share link will add a '+
				'read-only reference of this '+(opt.item.folder?'collection':'analysis')+' to the recipient\'s library '+
				'and will include the connected datasets.">Also share the subsequent analysis steps</span> '+
				'<a class="button toggle" data-bind="css:{on:sharedir'+(dironly?',disabled:true}':'},click:toggle.bind($data,sharedir)')+
				'"><span class="light"></span><span class="text" data-bind="text:btntxt(sharedir)"></span></a>';
				var selectdataset = '';
				if(opt.item.folder && !opt.item.shared){ //set "opendataset" for a folder 
					selectdataset = '<div style="margin-top:10px" data-bind="with:librarymodel.getitem(\''+opt.id+'\')"><span class="label" title="You may choose '+
					  'a \'cover\' dataset that will be opened when this sharing link is used">Upon import, open </span>'+
					  '<select data-bind="options: librarymodel.childlist($data), optionsText: \'name\', optionsValue: \'id\', '+
					  'value: $data.opendataset"></select></div>';
				}
				var shareopt = '<div class="insidediv">'+dirtoggle+selectdataset+'</div><br>';
			}
		}
		
		var content = ['<div>Paste this URL to a web browser address bar'+desc+'.</div><br>'];
		var input = $('<input class="transparent" style="width:350px;padding:0" onclick="this.select()" data-bind="value:sharedir()?\''+dirurl+'\':\''+url+'\'"></input>');
		setTimeout(function(){input[0].select()},500);
		var email = $('<input style="width:183px" type="email" placeholder="e-mail address">');
		var emailbtn = $('<a class="button square" style="margin-left:3px">Send</a>');
		var sendmail = function(){ if(~email.val().indexOf('@')) communicate('sendmail',{email:email.val(),url:input.val()},{btn:emailbtn,restore:true}); }
		emailbtn.click(sendmail);
		content.push(input, '<div class="inputdesc">Press '+ckey+'+C to copy the link to clipboard</div>', shareopt);
		if(settingsmodel.email) content.push('Share the link: ', email, emailbtn);
		var openbtn = $('<a class="button blue" href="'+url+'" target="_blank">Open link</a>');
		var windowdiv = makewindow('Share data',content,{id:type, icn:'info', btn:['OK',openbtn]})[0];
		ko.applyBindings(settingsmodel,windowdiv);
	}
//plugin window
	else if(plugins[type]){
		var pmodel = plugins[type];
		pmodel._submitted(false);
		var html = pmodel.buildUI();
		var pwindow = makewindow(pmodel._title, html.content, {id:type, btn:html.btn, icn:pmodel._icon.img, header:html.header, plugin:pmodel._folder});
		try{ ko.applyBindings(pmodel, pwindow[0]); }catch(e){
			console.log('Wasabi plugin error when binding datamodel to HTML: '+e);
			console.log("Plugin datamodel dump:"); console.log(pmodel);
		}
	}
	return false;
}

//== functions for sequence manipulation ==//
//make or resize a sequence selection box
function selectionsize(e,id,type){
	if(typeof(type)=='undefined'){ var type = 'rb', start = {}; }
	else if(typeof(type)=='object'){ //type => mouse startpos{x,y} || columns [start,end]
		var start = type.length? {x:type[0]*model.boxw(),w:type[1]-type[0]} : type.x&&type.y? {x:type.x,y:type.y} : {x:0,y:0};
		if(type.length && (type[1]*model.boxw()<Math.abs(dom.wrap.position().left) || type[0]*model.boxw()>Math.abs(dom.wrap.position().left)+dom.seqwindow.innerWidth())) return; //outside of seqwindow
		if(e){
			var dx = e.pageX-type.x, dy = e.pageY-type.y;
			if(dx<10||dy<10) return; else type = 'rb';
		}
	}
	id = id || model.activeid();
	if(!id){ //create new selectionbox
		id = $("div[id^='selection']").length+1;
		var x=0, y=0, w=1, h=1;
		dom.seq.append('<div id="selection'+id+'" class="selection"><div class="description"></div><div class="ltresize"></div><div class="rbresize"></div></div>\
			<div id="vertcross'+id+'" class="selectioncross"><div class="lresize"></div><div class="rresize"></div></div>\
			<div id="horicross'+id+'" class="selectioncross"><div class="tresize"></div><div class="bresize"></div></div>');
		if(typeof(type)=='object'){ //coordinates given
			x = start.x||x;
			y = start.y||model.boxh()*model.visiblerows().length-model.boxh();
			w = start.w||w;
		}else{ //coordinates from mouse
			x = (start.x||e.pageX)-dom.seq.offset().left-2;
			y = (start.y||e.pageY)-dom.seq.offset().top;
			model.activeid(id);
		}
		x = x-(x%model.boxw()); y = y-(y%model.boxh()); //snap to grid
		if(x<0) x=0; if(y<0) y=0;
		$("#selection"+id).css({'left':x,'top':y,'width':model.boxw()*w,'height':model.boxh()*h,'display':'block'});
		$("#vertcross"+id).css({'left':x,'top':'0','width':model.boxw()*w,'height':dom.seq.innerHeight(),'display':model.selmode()=='columns'?'block':'none'});
		$("#horicross"+id).css({'left':'0','top':y,'width':dom.seq.innerWidth(),'height':model.boxh()*h,'display':model.selmode()=='rows'?'block':'none'});
		dom.seqwindow.mouseup(function(){ //attach resize handles
			$("#selection"+id).mouseenter(function(){ $("#selection"+id+" div.rbresize, #selection"+id+" div.ltresize").css('opacity','1'); });
			$("#selection"+id).mouseleave(function(){ $("#selection"+id+" div.rbresize, #selection"+id+" div.ltresize").css('opacity','0'); });
			$("#vertcross"+id).mouseenter(function(){ $("#vertcross"+id+" div.lresize, #vertcross"+id+" div.rresize").css('opacity','1'); });
			$("#vertcross"+id).mouseleave(function(){ $("#vertcross"+id+" div.lresize, #vertcross"+id+" div.rresize").css('opacity','0'); });
			$("#horicross"+id).mouseenter(function(){ $("#horicross"+id+" div.tresize, #horicross"+id+" div.bresize").css('opacity','1'); });
			$("#horicross"+id).mouseleave(function(){ $("#horicross"+id+" div.tresize, #horicross"+id+" div.bresize").css('opacity','0'); });
			$("#selection"+id+" div.rbresize").mousedown(function(){
				dom.seqwindow.mousemove(function(evt){ selectionsize(evt,id,'rb'); });
			});
			$("#selection"+id+" div.ltresize").mousedown(function(){
				dom.seqwindow.mousemove(function(evt){ selectionsize(evt,id,'lt'); });
			});
			$("#vertcross"+id+" div.rresize").mousedown(function(){
				dom.seqwindow.mousemove(function(evt){ selectionsize(evt,id,'r'); });
			});
			$("#vertcross"+id+" div.lresize").mousedown(function(){
				dom.seqwindow.mousemove(function(evt){ selectionsize(evt,id,'l'); });
			});
			$("#horicross"+id+" div.bresize").mousedown(function(){
				dom.seqwindow.mousemove(function(evt){ selectionsize(evt,id,'b'); });
			});
			$("#horicross"+id+" div.tresize").mousedown(function(){
				dom.seqwindow.mousemove(function(evt){ selectionsize(evt,id,'t'); });
			});
		});
	} else { //resize existing selection
		var over = e.target.id ? e.target : e.target.parentNode;
		if(over.tagName=='DIV'&&id!=over.id.substr(0-id.toString().length)){ return false; }//avoid overlap
		var seldiv = $("#selection"+id);
		if(!seldiv.length) return;
		if(type!='b'&&type!='t'){
			if(type=='r'||type=='rb'){
				var w = e.pageX-seldiv.offset().left-5;
				w = w-(w%model.boxw())+model.boxw();
			} else if(type=='l'||type=='lt'){
				var l = e.pageX-seldiv.parent().offset().left+5;
				l = l-(l%model.boxw());
				var redge = seldiv.position().left+seldiv.innerWidth();
				if(l>redge-model.boxw()){ l=redge-model.boxw(); }
				var w = redge-l;
				seldiv.css('left',l);
				$("#vertcross"+id).css('left',l);
			}
			if(w<model.boxw()){ w = model.boxw(); }
			seldiv.css('width',w);
			$("#vertcross"+id).css('width',w);
		}
		if(type!='r'&&type!='l'){
			if(type=='b'||type=='rb'){
				var h = e.pageY-seldiv.offset().top-5;
				h = h-(h%model.boxh())+model.boxh();
			} else if(type=='t'||type=='lt'){
				var t = e.pageY-seldiv.parent().offset().top+5;
				t = t-(t%model.boxh());
				var bedge = seldiv.position().top+seldiv.innerHeight();
				if(t>bedge-model.boxh()){ t=bedge-model.boxh(); }
				var h = bedge-t;
				seldiv.css('top',t);
				$("#horicross"+id).css('top',t);
			}
			if(h<model.boxh()){ h = model.boxh(); }
			seldiv.css('height',h);
			$("#horicross"+id).css('height',h);
		}
		if(seldiv.innerHeight()>20 && seldiv.innerWidth()>40){//show selection size
			if(seldiv.innerWidth()>140){ var r=' rows | ',c=' columns';}else{ var r='x',c=''; }
			$("#selection"+id+' div.description').css('display','block'); 
			$("#selection"+id+' div.description').text(parseInt(seldiv.innerHeight()/model.boxh())+r+parseInt(seldiv.innerWidth()/model.boxw())+c);
		} else { $("#selection"+id+' div.description').css('display','none'); }
	}
}

//save positions of selection areas
function registerselections(id){
	if(id&&id=='skip') return;
	colflags = []; rowflags=[]; selections = [];
	var selector = id ? '#selection'+id : 'div[id^="selection"]';
	$(selector).each(function(){
		var sel = $(this);
		var colstart = parseInt(sel.position().left/model.boxw());
		var colend = parseInt((sel.position().left + sel.width())/model.boxw());
		var rowstart = parseInt(sel.position().top/model.boxh());
		var rowend = parseInt((sel.position().top + sel.height())/model.boxh());
		for(var c=colstart;c<colend;c++){ colflags[c] = 1; }
		for(var r=rowstart;r<rowend;r++){ rowflags[r] = 1; }
		selections.push({'rowstart':rowstart,'rowend':rowend,'colstart':colstart,'colend':colend});
	});
}

//delete a selection area
function clearselection(id){
	id = typeof(id)=='undefined' ? false : id;
	if(id){ $("#selection"+id).remove(); $("#vertcross"+id).remove(); $("#horicross"+id).remove(); }
	else{ $("#seq div[id*='selection'],#seq div[id*='cross']").remove(); }
	model.activeid('');
}

//toggle coulmn/row selection mode
function toggleselection(type,id,exclude){
	if(typeof(id)=='undefined') id=''; if(typeof(exclude)=='undefined') exclude='';
	if(~type.indexOf('tmp') && model.selmode()!='default') return;
	if(type=='default'){ toggleselection('hide rows',id); type='hide columns'; } //actions for selection mode change
	else if(type=='columns'){ toggleselection('hide rows',id); type='show columns'; }
	else if(type=='rows'){ toggleselection('show rows',id); type='hide columns'; }
	var divs = ~type.indexOf('rows')? $('div[id^="horicross'+id+'"]') : ~type.indexOf('columns')? $('div[id^="vertcross'+id+'"]') : $('div[id$="cross'+id+'"]');
	if(exclude) divs = divs.not('div[id$="cross'+exclude+'"]'); //filter out some divs
	$(divs).each(function(){ if(~type.indexOf('show')) $(this).stop().fadeIn(200); else $(this).fadeOut(200); }); 
}

//create content for sequence position info tooltip
function seqinfo(e){ 
	if(!e.pageX||!e.pageY) return false;
	var x = e.pageX-dom.seq.offset().left-2;
	x = parseInt(x/model.boxw());
	var y = e.pageY-dom.seq.offset().top-2;
	y = parseInt(y/model.boxh());
	if(x<0){ x=0; } if(y<0){ y=0; }
	var col = model.visiblecols()[x]; var name = model.visiblerows()[y];
	if(!sequences[name]) return false;
	var suppl = col==x ? '' : '<br>(column '+(col+1)+' if uncollapsed)';
	var seqpos = sequences[name].slice(0,col+1).join('').replace(/[_\-.:]/g,'').length;
	var symb = typeof(sequences[name][col])=='undefined' ? '' : sequences[name][col];
	symb = canvaslabels[symb]||symb;
	var symbcanvas = model.boxh()>12 && typeof(symbols[symb])!='undefined'? cloneCanvas(symbols[symb]['canvas']) : '<span style="color:orange">'+symb+'</span>';
	if(leafnodes[name]) name = leafnodes[name].species||name;
	var content = $('<span style="color:orange">'+name+'</span><br>').add(symbcanvas).add('<span> position '+seqpos+' column '+(x+1)+suppl+'</span>');
	return {content:content, col:x, row:y, x:x*model.boxw(), y:y*model.boxh(), width:model.boxw(), height:model.boxh()}
}

//collapse MSA columns (based on [selections =>]columnflags)
function hidecolumns(selectionid, skipundo){
	if(typeof(selectionid)=='string') registerselections(selectionid);
	var undodata = (skipundo || !settingsmodel.undo())? false : [];
	var range = [], col = 0;
	for(var c=0,adj=0; c<colflags.length; c++){
		if(undodata){
			col = model.visiblecols()[c-adj];
			if(colflags[c]){ if(!range.length) range[0] = col; }
			else if(range.length){ range[1] = col; undodata.push(range); range = []; } 
		}
		if(colflags[c]){ model.visiblecols.splice(c-adj,1); adj++; } //remove columns from rendering pipeline
	}
	if(undodata){
		if(range.length){ range[1] = col+1; undodata.push(range); }
		if(undodata.length){
			var s = undodata.length==1? ' was' : 's were';
			var undodesc = undodata.length+' alignment column range'+s+' collapsed.';
			model.addundo({name:'Collapse columns',seqtype:model.seqtype(),type:'seq',data:undodata,info:undodesc,
			undoaction:'show columns',redoaction:'hide columns'});
		}
	}
	redraw();
}

//make collapsed columns visible again (based on input ranges)
function showcolumns(gaparr, hidetip, seqtype){ 
	if(hidetip) hidetooltip();
	if(gaparr=='all'){
		for(var c=model.alignlen(), colarr=[]; c--;) colarr[c] = c;
		model.visiblecols(colarr); //mark all columns as visible
		redraw(); return;
	}
	var visiblecols = model.visiblecols();
	$.each(gaparr, function(i,gapcols){
		if(gapcols.length!=2) return true;
		if(seqtype) gapcols = translatecolumns(seqtype, model.seqtype(), gapcols);
		var scol = gapcols[0], ecol = gapcols[gapcols.length-1], start = 0, del = 0, fill = [];
		$.each(visiblecols,function(i,c){ if(c>=scol){ //indexes to fill in
				if(i&&!start) start = i;
				if(c<ecol) del++; else return false;
		}});
		for(var f=scol;f<ecol;f++){ fill.push(f); }
		if(scol>=visiblecols.length) start = visiblecols.length;
		model.visiblecols.splice.apply(model.visiblecols,[start,del].concat(fill));
	});
}

//remove collapsed alignment columns from dataset
function removecolumns(removecols){
	var undodata = (removecols||!settingsmodel.undo())? false : {};
	if(!removecols){
		var removecols = [], range = [];
		$("#right div.marker").each(function(){
			range = $(this).data('colrange');
			for(var i=range[0]; i<range[1]; i++){ removecols.push(i); }
		});
	}
	if(!removecols.length) return;
	if(undodata) undodata.removecols = removecols;
	for(var name in sequences){
		var seqdata = [];
		for(var c=0; c<removecols.length; c++){
			seqdata.push(sequences[name].splice(removecols[c]-c,1)[0]);
		}
		if(undodata) undodata[name] = seqdata;
	}
	if(undodata) model.addundo({name:'Remove columns', type:'seq', seqtype:model.seqtype(), undoaction:'addcolumns', redoaction:'removecolumns', data: undodata, info:removecols.length+' alignment columns were removed'});
	showcolumns('all');
}

//restore removed alignment columns
function addcolumns(data, seqtype){
	if(!data||!seqtype) return;
	if(model.seqtype() != seqtype) translateseq(seqtype);
	for(var name in data){
		if(!sequences[name]) continue;	
		for(var c=0; c<data.removecols.length; c++){
			sequences[name].splice(data.removecols[c], 0, data[name][c]);
		}
	}
	redraw();
}

//collapse MSA rows
function hiderows(selectionid){
	var namearr = [];
	action = 'hide';
	registerselections(selectionid);
	for(var r=0;r<rowflags.length;r++){ if(rowflags[r]){ namearr.push(model.visiblerows()[r]); }}
	$.each(namearr,function(n,name){ if(leafnodes[name]) leafnodes[name].hideToggle('hide'); });
	refresh();
}

//mask a MSA block
function maskdata(action,selectionid){
	var target = ~action.indexOf('rows')? 'rows' : ~action.indexOf('columns')? 'columns' : 'selections';
	if(~action.indexOf('unmask')){ var symboltype = 'unmasked'; var flag = false; } else { var symboltype = 'masked'; var flag = 1; }
	registerselections(selectionid);
	var undodata = {}, undodesc = '';
	
	if(~action.indexOf('all')){
		for(var name in sequences){ for(var c=0;c<sequences[name].length;c++) sequences[name][c] = symbols[sequences[name][c]][symboltype]; }
	}
	else if(action=='hidemaskedcols'){
		for(var c=0;c<maskedcols.length;c++){ 
			if(maskedcols[c]){
				var colind = model.visiblecols.indexOf(c);
				if(~colind){ model.visiblecols.splice(colind,1); }
			} 
		}
	}
	else if(target=='columns'){
		undodata._columns = []; var firstrow = true, colid = false;
		for(var name in sequences){ if(~model.visiblerows.indexOf(name)){
			if(flag) undodata[name] = 'columns';
			for(var c=0;c<colflags.length;c++){ if(colflags[c]){
					colid = model.visiblecols()[c];
					sequences[name][colid] = symbols[sequences[name][colid]][symboltype];
					maskedcols[colid] = flag;
					if(flag && firstrow) undodata._columns.push(colid);
			}}
			firstrow = false;
		}}
		undodesc = undodata._columns.length+' '+model.seqtype()+' alignment columns were masked.';
	}
	else if(target=='rows'){
		for(var r=0;r<rowflags.length;r++){ if(rowflags[r]){
				var name = model.visiblerows()[r];
				if(flag) undodata[name] = 'all';
				for(var c=0;c<sequences[name].length;c++){ sequences[name][c] = symbols[sequences[name][c]][symboltype]; }
		}}
		undodesc = Object.keys(undodata).length+' sequences were masked.';
	}
	else if(target=='selections'){
		for(var s=0;s<selections.length;s++){
			var sel = selections[s];
			for(var r=sel.rowstart;r<sel.rowend;r++){
				var name = model.visiblerows()[r];
				if(!undodata[name]) undodata[name] = [];
				for(var c=sel.colstart;c<=sel.colend;c++){
					var colid = model.visiblecols()[c];
					sequences[name][colid] = symbols[sequences[name][colid]][symboltype];
					if(flag) undodata[name].push(colid);
					else maskedcols[colid] = false;
				}
			}
		}
		undodesc = selections.length+' alignment blocks were masked.';
	}
	if(!$.isEmptyObject(undodata)){
		model.addundo({name:'Mask '+target,seqtype:model.seqtype(),type:'seq',data:undodata,info:undodesc,undoaction:'unmask',redoaction:'mask'});
	}
	redraw();
}

//undo/redo sequence manipulation actions
function undoseq(seqtype, undodata, action){
	if(~action.indexOf('mask')){ //(un)mask seq. areas/rows/columns
		var symboltype = ~action.indexOf('unmask')? 'unmasked' : 'masked';
		var columns = undodata._columns? undodata._columns : [];
		for(name in undodata){
			if(!sequences[name]) continue;
			if(undodata[name]==='all'){
				for(var c=0;c<sequences[name].length;c++) sequences[name][c] = symbols[sequences[name][c]][symboltype];
			} else {
				if(undodata[name]!=='columns') columns = undodata[name];
				columns = translatecolumns(seqtype, model.seqtype(), columns);
				for(var c=0;c<columns.length;c++) sequences[name][columns[c]] = symbols[sequences[name][columns[c]]][symboltype];
			}
		}
	}
	else if(~action.indexOf('show')){ showcolumns(undodata, false, seqtype); }
	else if(~action.indexOf('hide')){ //rehide columns
		colflags = [];
		var c = 0, i = 0; visiblecols = model.visiblecols();
		$.each(undodata,function(i,range){
			if(range.length!=2) return true;
			range = translatecolumns(seqtype, model.seqtype(), range);
			var scol = range[0], ecol = range[range.length-1];
			for(;i<visiblecols.length;i++){ //column range=>colflags
				c = visiblecols[i];
				if(c>=scol){ if(c<ecol) colflags[i] = 1; else break; }
			}
		});
		hidecolumns(false,'skipundo');
	}
	else if(~action.indexOf('add')){ addcolumns(undodata, seqtype); } //restore removed columns
	else if(~action.indexOf('remove')){ removecolumns(translatecolumns(seqtype, model.seqtype(), undodata.removecols)); }
	redraw();
}

//sequence row highlight
var hideborder = false;
function rowborder(data,hiding){
	if(hideborder) clearTimeout(hideborder);
	var rborder = $("#rborder");
	var hidefunc = function(){ rborder.css('opacity',0); setTimeout(function(){ rborder.css('display','none') },300); };
	if(hiding=='hide'){ hidefunc(); return; }
	var top = data.y||seqinfo(data).y||0;
	rborder.css('top',top);
	if(rborder.css('display')=='none') rborder.css({display:'block', opacity:1, height:model.boxh()-1});
	if(hiding!='keep') hideborder = setTimeout(hidefunc,3000);
}

//translate sequences and column flags (dna<=>codons<=>protein)
function translatecolumns(from,to,colarr){
	if(!from||!to) return;
	if(from=='RNA') from = 'DNA'; if(to=='RNA') to = 'DNA';
	if(!colarr) colarr = model.visiblecols();
	var colarr2 = [];
	var wrate = from=='DNA'? (1/3) : to=='DNA'? 3 : 1;
	if(from==to || wrate==1) return colarr;
	if(wrate==3){ //translate column flags (expand to dna)
		for(var c=0, c2=0; c<colarr.length; c++){ c2 = colarr[c]*3; colarr2.push(c2,c2+1,c2+2); }	
	} else { //(compress to codons)
		for(var c=0; c<colarr.length; c++){ if(colarr[c]%3==0) colarr2.push(colarr[c]/3); }
	}
	return colarr2;
}

//translate sequence data (dna<=>codons<=>protein)
function translateseq(totype,check,skipdraw){
	var fromtype = model.seqtype(), cdna = model.dnasource();
	if((!check && fromtype==totype) || !cdna) return false;
	var errors = [], nuc, midnuc, codon, aa, step, Tsequences = {}, missinganc = false, tocase, n=0;
	var gaps = /[-_.:]+/g;
	var trimgap = function(m){ return m.length%3? m.substring(0,0-m.length%3) : m };
	$.each(sequences,function(name,seqarr){
		n++;
		if(check && n>20) return false;
		if(!cdna[name]){
			if(leafnodes[name] && leafnodes[name].type!='ancestral') errors.push('No cdna sequence for <span class="grey">'+name+'<span>');
			else missinganc = true;
			return n<5;
		}
		var curdna = cdna[name].join('').replace(gaps,trimgap);
		var tmpseq = [];
		if(fromtype=='protein'){ //backtranslation
			curdna = curdna.replace(gaps,'');
			var curlen = seqarr.join('').replace(gaps,'').length, seqpos = 0;
			if(curlen*3 != curdna.length){ errors.push('cdna sequence has wrong length for <span class="grey">'+name+'<span>'); return n<5; }
			else if(check) return true;
			$.each(seqarr,function(col,aa){
				if(gaps.test(aa)){ codon = aa+aa+aa; gaps.lastIndex = 0; }
				else{
					tocase = aa==symbols[aa].masked? 'toLowerCase' : 'toUpperCase';
					codon = curdna.substr(seqpos*3,3)[tocase]();
					seqpos++;
				}
				if(totype=='codons') tmpseq.push(codon); else tmpseq = tmpseq.concat(codon.split(''));
			});
		}
		else if(totype=='protein'){ //translation
			step = fromtype=='codons'? 1 : 3;
			if(step==3 && curdna.length%3){ errors.push('cDNA for <span class="grey">'+name+'</span> doesn\'t divide to 3-base codons'); return n<5; }
			else if(check) return true;
			for(var col=0; col<seqarr.length; col+=step){
				codon = step==3? seqarr.slice(col,col+3).join('') : seqarr[col]; //codon
				midnuc = codon.substr(1,1);
				tocase = letters.indexOf(midnuc)%2? 'toLowerCase' : 'toUpperCase';
				aa = /[-_.:]{3}/.test(codon)? midnuc : alphabet.codons[codon.toUpperCase()]? alphabet.codons[codon.toUpperCase()][tocase]() : '?';
				tmpseq.push(aa);
			}
		}
		else{ //dna<=>codons
			step = fromtype=='codons'? 1 : 3;
			if(step==3 && curdna.length%3){ errors.push('cDNA for <span class="grey">'+name+'</span> doesn\'t divide to 3-base codons'); return true; }
			else if(check) return true;
			for(var col=0; col<seqarr.length; col+=step){
				if(step==3) tmpseq.push(seqarr.slice(col,col+3).join('')); //dna=>codon
				else tmpseq = tmpseq.concat(seqarr[col].split('')); //codon=>dna
			}
		}
		Tsequences[name] = tmpseq;
	});
	
	if(check) return !errors.length;
	if(errors.length){
		var ul = $('<ul class="wrap">');
		$.each(errors,function(i,error){ 
			if(i>4) error = '...(not showing all errors)';
			ul.append('<li>'+error+'</li>');
			if(i>4) return false;
		});
		var desc = '';
		if(fromtype=='protein'){ model.dnasource(''); desc = '<br>Please use a cdna file that matches the current data.'; }
		dialog('error',['Sequence translation failed:',ul,desc]); return;
	}
	var applytrans = function(){
		if($.isEmptyObject(Tsequences)) return false;
		sequences = Tsequences;
		var oldw = model.symbolw();
		model.seqtype(totype);
		var wrate = fromtype=='DNA'? (1/3) : totype=='DNA'? 3 : 1;
		if(wrate!=1){
			model.minseqlen(Math.round(model.minseqlen()*wrate));
			model.maxseqlen(Math.round(model.maxseqlen()*wrate));
			model.totalseqlen(Math.round(model.totalseqlen()*wrate));
			model.alignlen(Math.round(model.alignlen()*wrate));
			model.visiblecols(translatecolumns(fromtype,totype)); //translate column flags
		}
		if(!skipdraw) redraw({zoom:true,refresh:true,leftscale:wrate});
	};
	if(missinganc){
		var applybtn = $('<a class="button">Translate</a>').click(function(){
			applytrans();
			closewindow(this);
		});
		var content = 'The cdna source is missing the ancestral sequences present in current alignment.<br>'+
		'Sequence translation will remove the ancestral sequences. Translate anyway?';
		makewindow("Warning",[content],{id:'transwarn',btn:['Cancel',applybtn],icn:'warning'});
	}
	else applytrans();
	return false;
}

//generate content for sequence area pop-up menu
function seqmenu(selectid){
	var maskcount = 0, menu = {};
	for(var c=0;c<maskedcols.length;c++){ if(maskedcols[c]) maskcount++; }
	var mode = model.selmode();
	var actid = model.activeid();
	var selectcount = $('div[id^="selection"]').length;
	var modemenu = {}, curmode = model.selmode();
	$.each(model.selmodes,function(i,mode){
		modemenu[mode] = {click:function(){model.setmode(mode)}, icon:mode};
		if(mode==curmode) modemenu[mode]['class'] = 'active';
	});
		
	if(actid){ //right-click on selection
		var target = mode=='default'? 'selection area' : mode;
		var maskmenu = {};
		maskmenu['Mask '+target] = {click:function(){maskdata('mask'+target,actid)}, icon:'mask'};
		maskmenu['Unmask '+target] = {click:function(){maskdata('unmask'+target,actid)}, icon:'unmask'};
		if(selectcount>1){
			maskmenu['Mask all '+selectcount+' selections'] = {click:function(){maskdata('mask'+target)}, icon:'mask'};
			maskmenu['Unmask all '+selectcount+' selections'] = {click:function(){maskdata('unmask'+target)}, icon:'unmask'};
		}
		
		var colmenu = {};
		if(mode!='rows'){
			colmenu['Collapse columns'] = {click:function(){hidecolumns(actid)}, over:function(){toggleselection('show columns tmp',actid)}, icon:'collapse',
			out:function(){toggleselection('hide columns tmp',actid)}};
			if(selectcount>1){
				colmenu['Collapse all selected columns'] = {click:function(){hidecolumns('')}, over:function(){toggleselection('show columns tmp')}, icon:'collapse',
				out:function(){toggleselection('hide columns tmp')}};
			}
		}
		var rowmenu = {};
		if(mode!='columns' && model.treesource()){
			rowmenu['Collapse rows'] = {click:function(){hiderows(actid)}, over:function(){toggleselection('show rows tmp',actid)}, icon:'collapse',
			out:function(){toggleselection('hide rows tmp',actid)}};
			if(selectcount>1){
				rowmenu['Collapse all selected rows'] = {click:function(){hiderows()}, over:function(){toggleselection('show rows tmp')}, icon:'collapse',
				out:function(){toggleselection('hide rows tmp')}};
			}
		}
		
		var clearmenu = {};
		clearmenu['Clear selection'] = {click:function(){clearselection(actid)}, icon:'selection'};
  		if(selectcount>1) clearmenu['Clear all selections'] = {click:function(){clearselection()}, icon:'selections'};
		
		menu = {'Sequence masking':{submenu:maskmenu}, 'Sequence columns':{submenu:colmenu}, 'Sequence rows':{submenu:rowmenu}, 'Selections':{submenu:clearmenu}};	
	}else{ //right-click outside of selection
		menu = {'Unmask all sequences':{click:function(){maskdata('unmaskall')}, icon:'unmask'}};
		if(model.hiddenlen()){
			menu['Reveal '+model.hiddenlen()+' hidden columns'] = {click:function(){showcolumns('all','hidetip')}, icon:'expand'};
			menu['Remove '+model.hiddenlen()+' hidden columns'] = {click:function(){removecolumns()}, icon:'trash'};
		}
		if(maskcount) menu['Collapse '+maskcount+' masked columns'] = {click:function(){maskdata('hidemaskedcols')}, icon:'collapse'};
		if(selectcount) menu['Clear '+selectcount+' selections'] = {click:function(){clearselection()}, icon:'selections'};
	}
	menu['Selection mode'] = {submenu:modemenu, icon:model.selmode(), class:'active'};
	return menu;
}

//== Launch Wasabi ==//
//load startup data from server
var startupdone = false;
function startup(response){
	if(startupdone){ return false; } else { startupdone = true; }
	if(typeof(localStorage.collapse)!='undefined') toggletop(localStorage.collapse);
	var launchact = settingsmodel.onlaunch();
	var urlstr = settingsmodel.urlvars, urlvars = parseurl(settingsmodel.urlvars);
	setTimeout(function(){window.history.pushState('', '', window.location.pathname)}, 1000); //clear urlvars
	
	if(urlvars.disable){ //disable interface items with URL parameters
		var darr = $.isArray(urlvars.disable)? urlvars.disable : [urlvars.disable];
		$.each(['menubar','data','tools','zoom','undo','logo','tree','seq','animations','sharing'], function(i,d){
			if(~darr.indexOf(d)) urlvars[d] = false;
		});
		$.each(['filemenu','toolsmenu'], function(i,menu){ //disable items from file/toolsmenu
			$.map(model[menu], function(menucontent){
				return ~darr.indexOf(menucontent.txt.toLowerCase)? undefined : menucontent;
			});
		});
	}
	
	$.each(urlvars, function(pref,val){ //load settings from URL parameters
		if(typeof(settingsmodel[pref])!='undefined'){ if(typeof(settingsmodel[pref])=='function') settingsmodel[pref](val); else settingsmodel[pref] = val; }
	});
	
	try{ var data = JSON.parse(response); }catch(e){ //offline mode
		console.log('Startup: Wasabi server offline.');
		model.offline(true);
		if(urlvars.file){ urlvars.url = {url:'http://'+window.location.host+window.location.pathname+urlvars.file}; }
		if(urlvars.url){ checkfiles(urlvars.url); }
		return;
	}
	
	if(data.email) settingsmodel.email = true; //server can send emails
	if(data.useraccounts){ //server has useraccounts
		settingsmodel.useraccounts(!isNaN(data.useraccounts)?parseInt(data.useraccounts):true); //stores max account age
		var localid = settingsmodel.urlid||settingsmodel.userid()||''; //local: given by URL or localStorage
		if(data.userid && data.userid==localid){ //valid proposed user (data.userid comes from server)
			if(settingsmodel.urlid && (settingsmodel.urlid!==settingsmodel.userid())){ //new userID from URL
				settingsmodel.keepuser(false);
				launchact = 'demo data';
				dialog('newuser',{newid:settingsmodel.urlid}, 2000);
			}
			settingsmodel.userid(data.userid);
		} else { //start without useraccount
			userexpire = !isNaN(settingsmodel.useraccounts)?'<br>Please note that neglected accounts are deleted after '+
				settingsmodel.useraccounts+' days.':'';
			if(localid && !data.userid) dialog('warning','User ID '+localid+' was not found on Wasabi server.'+userexpire);
			settingsmodel.keepuser(false);
			settingsmodel.userid('');
			//setTimeout(function(){dialog('jobstatus')},5000);
		}
	}
	if(data.cpulimit) settingsmodel.jobtimelimit = data.cpulimit;
	if(data.datalimit){ settingsmodel.datalimit = parseInt(data.datalimit)*1000000; settingsmodel.datause.valueHasMutated(); }
	if(data.local){ //local server. wire up UI for server-side settings
		settingsmodel.local = true;
		settingsmodel.sharelinks(false);
		if(data.browser){ settingsmodel.openbrowser(data.browser); settingsmodel.openbrowser.sync = true; }
		if(data.datadir){ settingsmodel.datadir(data.datadir); settingsmodel.datadir.sync = true;  }
		if(data.osxbundle){ settingsmodel.local = 'osxbundle'; settingsmodel.bundlestart.sync = true; }
		else if('linuxdesktop' in data){ settingsmodel.local = 'linux'; settingsmodel.linuxdesktop(data.linuxdesktop); settingsmodel.linuxdesktop.sync = true; }
	} else { settingsmodel.checkupdates(false); }
	if(data.autoupdate) settingsmodel.autoupdate = true;
	
	if((localStorage.zoomlevel && settingsmodel.keepzoom()) || urlvars.zoomlevel){ //custom zoomlevel
		var zlevel = parseInt(urlvars.zoomlevel) || JSON.parse(localStorage.zoomlevel);
		if(zlevel<1 || zlevel>=model.zlevels.length) zlevel = 1;
		model.zoomlevel(zlevel);
	}
	
	communicate('getlibrary');
	
	if(urlvars.id||urlvars.wasabiID||urlvars.share){ //import from library
		getfile({id:urlvars.id||urlvars.wasabiID||urlvars.share, file:urlvars.file||'', dir:urlvars.dir||'', aftersync:true});
	}
	else if(urlvars.file){ getfile({file:urlvars.file, aftersync:true}); } //import local file
	else if(urlvars.url){ //import remote file(s): urlvars.url = Array [url,url]
		checkfiles(urlvars.url);
	}
	else if(launchact=='demo data'){ getfile({id:'example', file:'out.xml'}); } //or load demo data (default)
	else if(settingsmodel.userid() && settingsmodel.keepid() && localStorage.openid && localStorage.openfile){ //or load last data
		getfile({id:localStorage.openid, file:localStorage.openfile});
	}
	else if(launchact=='import dialog'){ dialog('import'); } //show import dialog
	
	if(data.plugins){  //donwload & process plugins
		$.each(data.plugins, function(i,pluginname){
			getfile({plugin:pluginname, throttle:true, success:function(pjson){ new pluginModel(pjson, pluginname); }});
		})
	}

	if(settingsmodel.checkupdates()) checkversion(); //check for updates
}

//Initiation on page load
$(function(){
	if(/iPad|iPhone|iPod/.test(navigator.userAgent)) setTimeout(function(){window.scrollTo(0,1)},15); //scroll 1px (hides scrollbar in iOS)
	
	if(!document.createElement('canvas').getContext){ //old browser => stop loading
		dialog('warning','Your web browser does not support running Wasabi.<br>Please upgrade to a <a onclick="dialog(\'about\')">modern browser</a>.');
		return;
	}
	
	var divids = ["page", "content", "left", "right", "top", "bottom", "seq", "seqwindow", "seqwrap", "wrap", "tree", "treewrap", "ruler", "names", "namelabel", "namelabelspan"];
	$.each(divids, function(i,id){ dom[id] = $("#"+id); }); //add references to Wasabi DOM elements
	
	ko.applyBindings(model);
	
	/* set up interface-event bindings */
	$("#treebin div").append(svgicon('trash'));
	var $left = $("#left"), $right = $("#right"), $dragline = $("#namesborderDragline"), $namedragger = $("#namesborderDrag"), draggerpos;
	
	$("#borderDrag").draggable({ //make sequence/tree width resizable
		axis: "x", 
		containment: [12, 0, dom.page.width()-30, 0],
		start: function(e, dragger){ draggerpos = dragger.offset.left-$namedragger.offset().left+5; },
		drag: function(event, dragger) {
			$left.css('width',dragger.offset.left);
			$right.css('left',dragger.offset.left+10);
			$dragline.css('width',dragger.offset.left);
			$namedragger.css('left',dragger.offset.left-draggerpos);
		},
		stop: function(){
			$(window).trigger('resize');
		}
	});
	$namedragger.draggable({ //make names width resizable
		axis: "x", 
		containment: 'parent',
		drag: function(event, dragger) {
			dom.tree.css('right',$left.width()-dragger.offset.left-5);
			dom.names.css('width',$left.width()-dragger.offset.left-5);
		}
	});
	$("#namesborderDrag").hover(
		function(){$("#names").css('border-color','#aaa')},
		function(){$("#names").css('border-color','white')}
	);
	
	$("#names").mouseleave(function(e){ rowborder(e,'hide'); });
	
	//Add mouse click/move listeners to sequence window
	dom.seqwindow.mousedown(function(e){
	 e.preventDefault(); //disable image drag etc.
	 var startpos = {x:e.pageX,y:e.pageY};
	 if(e.pageY>dom.seqwindow.offset().top+30){ //in seq area
	if(e.which==1 && e.target.tagName!='DIV'){ //act on left mouse button, outside of selections
		model.activeid('');
		dom.seqwindow.mousemove(function(evt){ selectionsize(evt,'',startpos); });
		dom.seqwindow.one('mouseup',function(e){
			model.activeid('');
			if(e.pageY>dom.seqwindow.offset().top+30){ //in seq area
				if(e.which==1 && e.target.tagName!='DIV' && $("div.canvasmenu").length==0){ //outside of selections
					var dx = e.pageX-startpos.x; var dy = e.pageY-startpos.y; 
					if(Math.sqrt(dx*dx+dy*dy)<10 && !$('#seqmenu').length){ //no drag => higligh row and show position info
						var sdata = seqinfo(e);
						var bottom = Math.abs(parseInt(dom.seq.css('margin-top')))+dom.seqwindow.innerHeight()-90;
						if(model.alignheight()*model.boxh()<bottom) bottom = model.alignheight()*model.boxh()-60;
						var arrowtype = sdata.y>bottom? 'bottom' : 'top';
						rowborder(sdata);
						tooltip(e,sdata.content,{container:"#seq",arrow:arrowtype,target:sdata,shifty:-5});
					}
				}
			}
		});
	}
	$('html').one('mouseup',function(){
		dom.seqwindow.unbind('mousemove');
		if(toolsmodel.prunemode) toolsmodel.markLeafs();
	});
	 }
	});
	
	var icon = function(type,title){
		title = title? 'title="'+title+'"' : '';
		return '<span class="svgicon" '+title+'>'+svgicon(type)+'</span>';
	}
	
	dom.seqwindow.bind('contextmenu',function(e){ //sequence area right click (pop-up menu)
		e.preventDefault(); //disable default right-click menu
		if($.isEmptyObject(sequences)) return false;
		var target = e.target.id==''? e.target.parentNode : e.target;
		var actid = ~target.id.indexOf('selection')||~target.id.indexOf('cross')? target.id.substr(9) : '';
		model.activeid(actid);
		tooltip(e,'',{data:seqmenu(),id:'seqmenu'}); //show popup menu
	}); //seq. area right-click
	
	function touchHandler(event){ //map touch events to mouseclicks
	var fingers = event.touches.length, finger = event.changedTouches[0], btn = 0, types = [], 
	pass = true, t = finger.target, id = t.getAttribute('id'), el = t.tagName, cl = t.className.split(' ')[0];
	
	if(fingers>1) return;
	
	if(el=='CANVAS' || el=='circle' || cl.indexOf('selection')==0 || cl=='dragger' || cl=='ui-draggable' || cl=='description' || t.parentNode.getAttribute('id')=='ruler') pass = false;
	
	if(pass) return;
	
	switch(event.type){
		case "touchstart": types = ["mouseover","mousedown"]; break;
		case "touchmove": types = ["mousemove"]; break;        
		case "touchend": types = ["mouseup","mouseout"]; break;
		default: return;
	}
	
	event.preventDefault();
	
	if(cl.indexOf('selection')==0 || cl=='description'){
		if(event.type=="touchstart"){ types.shift(); types.push("contextmenu"); }
		btn = 2;
	}
	
	var simulateMouse = function(type){
		var mouseTrigger = document.createEvent("MouseEvent");
		mouseTrigger.initMouseEvent(type, true, true, window, 1, finger.screenX, finger.screenY, 
			finger.clientX, finger.clientY, false, false, false, false, btn, null);
			finger.target.dispatchEvent(mouseTrigger);
	};
	
	$.each(types,function(i,type){ simulateMouse(type); });
	}
	
	if('ontouchend' in document){
		document.addEventListener("touchstart", touchHandler, true);
	document.addEventListener("touchmove", touchHandler, true);
	document.addEventListener("touchend", touchHandler, true);
	}
	
	//Startup
	var urlpath = window.location.pathname.substring(window.location.pathname.lastIndexOf('/')+1);
	var urlvars = window.location.search;
	settingsmodel.loadprefs(); //load settings from localStorage
	settingsmodel.urlvars = urlvars;
	if(urlpath.length && !~urlpath.indexOf('.')) settingsmodel.urlid = urlpath; //launched with account URL

	var showbuttons = function(){ setTimeout(function(){
		$('#top').removeClass('away');
		$('#startup').fadeOut({complete:function(){ setTimeout(function(){
			$('#left,#right').css('opacity',1);
			$('#namesborderDragline').removeClass('dragmode');
		}, 400); }});
	}, 700); };
	if(~window.location.host.indexOf('localhost')||window.location.protocol=='file:') settingsmodel.sharelinks(false);
	communicate('checkserver',{userid:settingsmodel.urlid||settingsmodel.userid()||''},{success:startup, error:startup, after:showbuttons}); //ping server
});
