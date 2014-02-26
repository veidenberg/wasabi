/*
Renders interactive phylogenetic trees on SVG canvas.
Built upon jsPhyloSVG (jsphylosvg.com) and JStree (lh3lh3.users.sourceforge.net/jstree.shtml) javascript libraries
Written for Wasabi webapp by Andres Veidenberg //andres.veidenberg{at}helsinki.fi//, University of Helsinki [2011]
Requires a modified Raphael library (to support %-based units)
*/

Smits = {
	/// Global functions accessible by all data objects ///
	Common : {
	nodeIdIncrement : 0,
	activeNode: 0,
	//Round float to a defined number of decimal places
	roundFloat : function(num, digits){
		if(!digits) digits = 4;
		var result = Math.round(num * Math.pow(10,digits))/Math.pow(10,digits);
		return isNaN(result)? 0.0001 : result; 
	},
	//Copy properties from one object to another
	apply : function(obj, extObj){
		if (obj && typeof extObj == 'object') {
			for (var key in extObj) {
				obj[key] = extObj[key];
			}
		}
		return obj;	
	},
	
	addRaphEventHandler : function(el, eventType, fn, paramsObj){
		try{
			el[eventType](function(fn, paramsObj){
				return function(e,o){
					var params = paramsObj;
					params.e = e;
					fn(params);
				};
			}(fn, paramsObj));
		} catch (err){}	
	},
	//Process nodetree lengths & levels, add metadata. Used (rescoped) in fileparsing classes.
	processNodes : function(tree){
		var node = tree || this.root || ''; //'this' will be a data object from ...Parse()
		if(!node) return;
		for(var i in node.children){
			var child = node.children[i];
			if(model.dendogram()) child.len = 1;
			child.lenFromRoot = Smits.Common.roundFloat(node.lenFromRoot+child.len); //node total length from root
			child.level = node.level+1;
			if(child.level > this.mLevel) this.mLevel = child.level; //record max values
			if(child.lenFromRoot > this.mLenFromRoot) this.mLenFromRoot = child.lenFromRoot;
			if(child.children.length) this.processNodes(child);
			else if(this.nodeinfo && this.nodeinfo[child.name]){ //add external metadata
				$.each(this.nodeinfo[child.name],function(k,v){ child[k] = v; });
				if(child.species) child.displayname = child.species;
			}				
		}
		return node;
	}
  }//Smits.Common
};

/// Master data object. Contains tree data, SVG canvas and rendered tree objects. ///
Smits.PhyloCanvas = function(inputData){
	
	this.scale = function(multiplier){
		this.svg.svg.scale(multiplier);
	};
	this.getSvgSource = function(){
		if(Raphael.svg && typeof(XMLSerializer)=='function'){
			var serialize = new XMLSerializer();
			return serialize.serializeToString(svg.svg.canvas);
		} else { return false; }
	};
	this.refresh = function(options){ //re-render tree canvas
		if(!options) options = {};
		var self = this;
		self.phylogram = new Smits.PhyloCanvas.Render.Phylogram(self.svg, self.data);
		model.leafcount(self.data.root.leafCount); model.nodecount(self.data.root.nodeCount);
		if(!options.treeonly) redraw(options);
	}
	this.loaddata = function(dataobj){ //turn data file to object-tree
		Smits.Common.nodeIdIncrement = 0;
		if(typeof(dataobj)!='object') dataobj = {newick: dataobj};
		if(dataobj.phyloxml) this.data = new Smits.PhyloCanvas.PhyloxmlParse(dataobj);
		else if(dataobj.newick) this.data = new Smits.PhyloCanvas.NewickParse(dataobj);
		else dialog('error','Got empty data for tree drawing.<br>No changes made to the tree.');
		this.refresh(dataobj);
	}

	// Process dataset - assume newick format
	if(inputData){
		if(typeof(inputData)=='string') inputData = {newick: inputData};
		if(inputData.phyloxml) this.data = new Smits.PhyloCanvas.PhyloxmlParse(inputData);
		else if(inputData.newick) this.data = new Smits.PhyloCanvas.NewickParse(inputData);
		else  dialog('error','Tree data in wrong format.<br>Cannot draw a tree.');
	} else dialog('error','No input data to draw a tree.');
	this.svg = new Smits.PhyloCanvas.Render.SVG();
	//build stuff to tree canvas
	this.phylogram = new Smits.PhyloCanvas.Render.Phylogram(this.svg, this.data);	
};

/// Node Class. Allows tree data objects to be traversed across children ///
Smits.PhyloCanvas.Node = function(parentNode){
	//initiate node object
	this.id = ++Smits.Common.nodeIdIncrement;
	this.level = parentNode? parentNode.level+1 : 0;
	this.nwlevel = 0;
	this.len = 0.0001;
	this.lenFromRoot = 0;
	this.name = '';
	this.active = false;
	this.type = '';
	this.hidden = false;
	this.canvx = 0;
	this.canvy = 0;
	this.miny = 0;
	this.maxy = 0;
	this.children = [];
	this.parent = parentNode || false;

	//Calculations cache
	this.leafCount = 0;
	this.nodeCount = 0;
	this.visibleLeafCount = 0;
	this.visibleChildCount = 0;
	this.midBranchPosition = 0;
};

/// Functions for every node instance ///
Smits.PhyloCanvas.Node.prototype = {
	getById : function(id){
		if(this.id == id) return this;
		for(var i in this.children){
			var node = this.children[i].getById(id);
			if(node) return node;
		}
	},
	
	countChildren : function(hiddenbranch){
		this.leafCount = 0; this.visibleLeafCount = 0; this.visibleChildCount = 0;
		this.nodeCount = this.children.length? 1 : 0;
		for(var i in this.children){
			var child = this.children[i];
			if(!child.hidden) this.visibleChildCount++;
			if(child.children.length){
				child.countChildren(hiddenbranch||child.hidden);
				this.nodeCount += child.nodeCount;
				this.leafCount += child.leafCount;
				if(!hiddenbranch) this.visibleLeafCount += child.visibleLeafCount;
			}
			else{
				if(child.hidden){ if(child.type!='ancestral') this.leafCount++; } 
				else{ this.leafCount++; if(!hiddenbranch) this.visibleLeafCount++; }
				child.edgeCircleHighlight = false;
			}
		}
	},
	
	getVisibleParentBranch : function(){
		if(this.parent.visibleChildCount > 1){ return this; }
		else{ return this.parent.getVisibleParentBranch(); }
	},
	
	hideToggle : function(action){ //hide/show a node
		if(!this.parent) return;
		var ishidden = action ? action=='hide' ? false : true : this.hidden;
		if(!ishidden){
			if(this.parent.visibleChildCount<2){ //if only 1 visible child
				this.getVisibleParentBranch().hidden = true;
			}
			else{ this.hidden = true; }
		}
		else{ this.hidden = false; }
		this.getRoot().countChildren(); //recount hidden/visible nodes
	},
	
	showSubtree : function(ancestral,hide){ //show all descendants or show/hide all ancestral leaves
		for (var i in this.children) {
			var child = this.children[i];
			if(child.children && child.children.length > 0) child.showSubtree(ancestral,hide);
			else if((ancestral && child.type=='ancestral')||(!ancestral && child.type!='ancestral')){
				child.hidden = hide? true : false;
			}			
		}
		this.hidden = false;
		this.getRoot().countChildren();
	},
	
	getMidbranchPosition : function(firstBranch){
		this.midBranchPosition = firstBranch ? this.children[0].visibleLeafCount-0.5 : this.children[0].visibleLeafCount+0.5;
		if(this.children[0].visibleLeafCount==0){ this.midBranchPosition += 1; }
		if(this.children[1] && this.children[1].type=='ancestral' && !this.children[1].hidden){ 
			this.midBranchPosition += 0.5; 
			if((this.children[0].hidden && !this.children[2].hidden)||this.visibleChildCount==1){ this.midBranchPosition -= 1; }
		} else if(this.visibleChildCount==1){ this.midBranchPosition -= 0.5; }
		return this.midBranchPosition;
	},
	
	highlight : function(mark){
		var node = this;
		node.active = typeof(mark)!='undefined'? mark : !node.active;
		if(node.active){ var fill='orange', op=1, txtfill='orange'; } else { var fill='red', op=0, txtfill=''; }
		if(node.type=='stem') node.svgEl.attr({'fill':fill,'fill-opacity':op});
		else{ node.svgEl.attr({'fill':'black'}); $(node.svgEl.node.firstChild).attr('fill',txtfill); }
	},
	
	removeAnc : function(){ //strip all ancestral seq. leaves
		var carr = this.children, anci;
		for(var i in carr){
			if(carr[i].children.length > 0) carr[i].removeAnc(); 
			else if(carr[i].type=='ancestral') anci = i;
		}
		if(anci) carr.splice(anci,1);
		return this;
	},
	
	restoreAnc : function(){ //insert leaves (sequences) for ancestral nodes
		var node = this;
		for(var i in node.children) if(node.children[i].children.length > 0) node.children[i].restoreAnc();
		if(node.children.length > 1 && node.children[node.children.length-2].type != 'ancestral' && node.name && sequences[node.name]){
			var lastchild = node.children.pop();
			var ancnode = new Smits.PhyloCanvas.Node(node);
			ancnode.lenFromRoot = node.lenFromRoot;
			ancnode.type = 'ancestral';
			ancnode.name = node.name;
			ancnode.hidden = true;
			node.children.push(ancnode,lastchild);
		}
	},
	
	nodeArray : function(){ //returns flattened array of nested nodetree
		var node = this.removeAnc(), nodearr = [], stack = [];
		stack.push({node:node, i:0});
		for(;;){
			while(stack[stack.length-1].i != stack[stack.length-1].node.children.length){
				var lastobj = stack[stack.length-1];
				stack.push({node:lastobj.node.children[lastobj.i], i:0});
			}
			nodearr.push(stack.pop().node);
			if (stack.length > 0) stack[stack.length-1].i++;
			else break;
		}
		this.restoreAnc();
		return nodearr;
	},
	
	getRoot : function(flag){
		var node = this;
		var root = treesvg.data.root;
		if(flag && node!=root){
			while(node.parent){ node = node.parent; node.altered = true; }
			model.treealtered(true);
		}
		return root;
	},
	
	setRoot : function(new_root,norealign){
		new_root.parent.children = []; new_root.parent = false; new_root.id = 1;
		if(!new_root.name) new_root.name = 'Root';
		new_root.len = 0.0001; new_root.level = 1; new_root.lenFromRoot = 0;
		if(!norealign){
			new_root.altered = true; //mark tree for realignment
			if(!model.treealtered()) model.treealtered(true);
		}
		new_root.countChildren(); //update children count
		treesvg.data.root = new_root;
		treesvg.data.mLevel = treesvg.data.mLenFromRoot = 0;
		treesvg.data.processNodes(); //update levels/lengths
		return treesvg.data.root;
	},
	
	reRoot : function(dist){ //place node as tree outgroup
		var i, plen, nodelen, pnode, newnode, gpnode, ggpnode, new_root;
		var node = this, root = node.getRoot().removeAnc();
		if(node.type == 'ancestral') node = node.parent;
		if(node == root) return root;
		if(isNaN(dist) || dist<0 || dist>node.len) dist = node.len/2.0;
		nodelen = node.len;
		node.getRoot('flag');
		
	  	//construct new root node
		newnode = new_root = new Smits.PhyloCanvas.Node();
		newnode.children[0] = node;
		newnode.children[0].len = dist;
		pnode = node.parent;
		newnode.children[0].parent = newnode;
		for(i = 0; i < pnode.children.length; ++i)
			if (pnode.children[i] == node) break;
		newnode.children[1] = pnode;
		plen = pnode.len;
		pnode.len = nodelen - dist;
		gpnode = pnode.parent;
		pnode.parent = newnode;
		while(gpnode){ //travel down to current root (gather subtrees)
			ggpnode = gpnode.parent;
			pnode.children[i] = gpnode;
			for (i = 0; i < gpnode.children.length; ++i) //i=current travelbranch
				if (gpnode.children[i] == pnode) break;
			gpnode.parent = pnode;
			nodelen = gpnode.len; gpnode.len = plen; plen = nodelen;
			newnode = pnode; pnode = gpnode; gpnode = ggpnode; //go up one level
		}
		if(pnode.children.length == 2){ //remove old root from its branch and link the other branch
			var otherchild = pnode.children[1 - i];
			for (i = 0; i < newnode.children.length; i++) // i=branch of current root
				if (newnode.children[i] == pnode) break;
			otherchild.len += pnode.len||0;
			otherchild.parent = newnode;
			newnode.children[i] = otherchild; //link the child from root-detached branch
		} else { //multifurcating node. Just remove old root.
			pnode.children.splice(i,1);
		}
		node.setRoot(new_root);
		model.addundo({name:'Reroot',type:'tree',data:node.getRoot().write('undo'),info:'Tree rerooted.'});
	},
	
	ladderize : function(skipundo){
		if(!this.children.length) return;
		var node = this;
		if(node.children[0].visibleLeafCount<node.children[node.children.length-1].visibleLeafCount) node.swap('skipundo');
		for(var i in node.children){
			if(node.children[i].visibleLeafCount>2) node.children[i].ladderize('skipundo');
		}
		if(!skipundo) model.addundo({name:'Ladderise',type:'tree',data:this.getRoot().write('undo'),info:'The subtree of \''+node.name+'\' was reordered.'});
	},
	
	swap : function(skipundo){ //swap children
		var swapnode = this.children[0];
		this.children[0] = this.children[this.children.length-1];
		this.children[this.children.length-1] = swapnode;
		if(!skipundo) model.addundo({name:'Swap nodes',type:'tree',data:this.getRoot().write('undo'),info:'Tree node \''+swapnode.name+'\' swapped places with its sibling.'});
	},
	
	//Move: prune the subtree descending from this node and regragh it to the edge between targetnode and its parent
	move : function(target){
		var root = this.getRoot().removeAnc();
		var node = this;
		if (node === root || node.parent === root) return false; //can't move root
		for (var r = target; r.parent; r = r.parent){
			if (r === node) return false; //moving node is an ancestor of target. Can't move.
		}
		if(target.parent === node.parent){ node.parent.swap(); return false; } //node is a sister of target. Swap siblings.
		else if(target === node.parent){ return false; } //moving to node's original place
		node.remove('skipundo');

		var placeholder = new Smits.PhyloCanvas.Node();
		placeholder.children.push(root); root.parent = placeholder;

		var i, pnode = target.parent;
		for (i in pnode.children){ if (pnode.children[i] === target) break; }
		var newnode = new Smits.PhyloCanvas.Node();
		newnode.parent = pnode; pnode.children[i] = newnode;
		pnode.altered = true;
		if (target.len > 0) {
			newnode.len = target.len/2;
			target.len /= 2;
		}
		newnode.children.push(node); node.parent = newnode;
		newnode.children.push(target); target.parent = newnode;
		node.setRoot(placeholder.children[0]);
		node.getRoot('mark');
		model.addundo({name:'Move node',type:'tree',data:node.getRoot().write('undo'),info:'Tree node \''+this.name+'\' was attached to node "'+target.name+'".'});
	},
	
	remove : function(skipundo,skipcount){ //remove node+descendants from tree
		var node = this, root = node.getRoot().removeAnc(), pnode = node.parent;
		if(node == root) return;
		if(pnode != root){
			node.getRoot('flag'); //flag path to root
			var placeholder = new Smits.PhyloCanvas.Node(); //attach root to temp. buffer node
			placeholder.children.push(root); root.parent = placeholder;
		}

		if (pnode.children.length == 2){
			var otherbranch, gpnode = pnode.parent;
			var i = (pnode.children[0] == node)? 0 : 1;
			otherbranch = pnode.children[1 - i];
			if(pnode == root){ //special case - replace root
				if(otherbranch.children.length > 1) otherbranch.prune();
				return;
			} else { //connect the other branch with grandparent
				otherbranch.len = Smits.Common.roundFloat(otherbranch.len+pnode.len);
				otherbranch.parent = gpnode;
				for(i in gpnode.children) if(gpnode.children[i] == pnode) break;
				gpnode.children[i] = otherbranch;
			}
		} else { //multifurcating parent
			for(i in pnode.children) if (pnode.children[i] == node) break;
			pnode.children.splice(i,1);
		}
		
		//remove node+parent
		pnode.parent = false; pnode.children = []; node.parent = false; root.parent = false;
		if(!skipcount) root.countChildren();
		if(!skipundo){ //add undo, unless part of node move or batch remove
			delete leafnodes[node.name];
			model.nodecount(root.nodeCount); model.leafcount(root.leafCount);
			model.addundo({name:'Remove node',type:'tree',data:root.write('undo'),info:'Node \''+node.name+'\' was removed from the tree.'});
		}
	},
	
	prune : function(){ //keep node+subtree, remove the rest
		var node = this, nodename = node.name, root = node.getRoot().removeAnc();
		node.setRoot(node,'norealign');
		model.addundo({name:'Prune subtree',type:'tree',data:node.getRoot().write('undo'),info:'Subtree of node \''+nodename+'\' was pruned from main tree.'});
	},
	
	write : function(tags,noparents,nameids){ //convert nodetree to newick string
		if(tags=='undo' && !settingsmodel.undo()) return '';
		var nameids = nameids||{};
		var nodearr = this.nodeArray();
		//update levels
		nodearr[nodearr.length-1].nwlevel = 0;
		for (var i = nodearr.length-2; i>=0 ;i--) {
			var node = nodearr[i];
			node.nwlevel = node.parent.nwlevel+1;
		}
		//generate newick
		var str = '';
		var curlevel = 0, isfirst = true;
		for(var i in nodearr){
			var node = nodearr[i];
			var n_bra = node.nwlevel - curlevel;
			if (n_bra > 0) {
				if (isfirst) isfirst = false;
				else str += ",";
				for (var j = 0; j < n_bra; ++j) str += "(";
			} else if (n_bra < 0) str += ")";
			else str += ",";
			if(!noparents||node.type!='stem') str += (nameids[node.name]||node.name).replace(/ /g,'_');
			if(node.len >= 0 && node.nwlevel > 0) str += ":" + node.len;
			if(tags){ //write metadata
				node.meta = (node.confidence?':B='+node.confidence:'')+(node.hidden?':Co=Y':'')+(node.altered?':XN=realign':'')+(node.species?':S='+node.species:'')+
				(node.events?':Ev='+(node.events.duplications||'0')+'>'+(node.events.speciations||'0'):'')+(node.cladename?':ND='+node.cladename:'')+
				(node.ec?':E='+node.ec:'')+(node.accession?':AC='+node.accession:'')+(node.gene?':GN='+node.gene:'')+(node.taxaid?':T='+node.taxaid:'');
				if(node.meta) str += '[&&NHX'+node.meta.replace(/[\s\(\)\[\]&;,]/g,'_')+']';
			}
			curlevel = node.nwlevel;
		}
		str += ";\n";
		return str;
	},
	
	calcxy : function(){ //calculate coords for tree preview canvas
		var i,j;
		var nodearr = this.nodeArray();
		var scale = this.leafCount-1; //nr. of all leafs
		for(i = j = 0; i < nodearr.length; i++){ //calculate y
			var node = nodearr[i];
			node.canvy = node.children.length>0? (node.children[0].canvy + node.children[node.children.length-1].canvy)/2 : (j++)/scale;
			if (node.children.length == 0) node.miny = node.maxy = node.canvy;
			else node.miny = node.children[0].miny, node.maxy = node.children[node.children.length-1].maxy;
		}
		// calculate x
		nodearr[nodearr.length-1].canvx = 0;
		scale = 0;
		for(i = nodearr.length-2; i >= 0; i--){
			var node = nodearr[i];
			node.canvx = node.parent.canvx + node.len;
			if(node.canvx > scale) scale = node.canvx;
		}
		for (i = 0; i < nodearr.length; i++) nodearr[i].canvx /= scale;
		return nodearr;
	},
	
	makeCanvas : function(){ //draw tree preview canvas
		var nodearr = this.calcxy();
		var conf = {width:100,height:150,xmargin:4,ymargin:2,fontsize:5,c_line:"rgb(60,60,60)"};
		if(nodearr.length<10) conf.width = conf.height = 8*nodearr.length;
		var canvas = document.createElement('canvas');
		canvas.width = conf.width; canvas.height = conf.height;
		var ctx = canvas.getContext("2d");
		ctx.strokeStyle = ctx.fillStyle = "white";
		ctx.fillRect(0, 0, conf.width, conf.height);
	
		var real_x = conf.width-2 * conf.xmargin;
		var real_y = conf.height-2 * conf.ymargin - conf.fontsize;
		var shift_x = conf.xmargin;
		var shift_y = conf.ymargin + conf.fontsize/2;
	
		// horizontal lines
		var y;
		ctx.strokeStyle = conf.c_line;
		ctx.beginPath();
		y = nodearr[nodearr.length-1].canvy * real_y + shift_y;
		ctx.moveTo(shift_x, y); ctx.lineTo(nodearr[nodearr.length-1].canvx * real_x + shift_x, y);
		for (var i = 0; i < nodearr.length - 1; i++) {
			var node = nodearr[i];
			y = node.canvy * real_y + shift_y;
			ctx.moveTo(node.parent.canvx * real_x + shift_x, y);
			ctx.lineTo(node.canvx * real_x + shift_x, y);
		}
		// vertical lines
		var x;
		for (var i = 0; i < nodearr.length; i++) {
			var node = nodearr[i];
			if (node.children.length == 0) continue;
			x = node.canvx * real_x + shift_x;
			ctx.moveTo(x, node.children[0].canvy * real_y + shift_y);
			ctx.lineTo(x, node.children[node.children.length-1].canvy * real_y + shift_y);
		}
		ctx.stroke();
		ctx.closePath();
		canvas.style.borderRadius = '2px';
		return canvas;
	}	
};//Node prototype functions

/// Parse (extended) Newick formatted text to a tree data object ///
Smits.PhyloCanvas.NewickParse = function(data){
	var text, ch, pos=0, mLevel=0, mLenFromRoot=0.0001, treealtered,
		
	object = function (parentNode,node){  //fill node with data
		if(!node) node = new Smits.PhyloCanvas.Node(parentNode);
		while (ch && ch!==')' && ch!==','){
			if (ch === '['){ //read metadata
				var meta = quotedString(']');
				if(~meta.indexOf(':Co=Y')) node.hidden = true;
				if(~meta.indexOf(':XN=realign')){ node.altered = true; treealtered = true; }
				if(~meta.indexOf(':B=')) node.confidence = meta.match(/:B=(\w+)/)[1];
				if(~meta.indexOf(':Ev=')){
					var evol = meta.match(/:Ev=(\d+)>(\d+)/);
					node.events = {duplications:parseInt(evol[1]), speciations:parseInt(evol[2])};
				}
				if(~meta.indexOf(':S=')) node.species = node.displayname = meta.match(/:S=(\w+)/)[1].replace(/_/g,' ');
				if(~meta.indexOf(':T=')) node.taxaid = meta.match(/:T=(\w+)/)[1];
				if(~meta.indexOf(':E=')) node.ec = meta.match(/:E=(\w+)/)[1];
				if(~meta.indexOf(':GN=')) node.gene = meta.match(/:GN=(\w+)/)[1]; //ens. gene name
				if(~meta.indexOf(':ND=')) node.cladename = meta.match(/:ND=(\w+)/)[1]; //ens. gene id
				if(~meta.indexOf(':AC=')) node.accession = meta.match(/:AC=(\w+)/)[1]; //ens. protein id
			} else if (ch===':'){ //read branchlength
				next();
				node.len = Smits.Common.roundFloat(string(), 4);
				if(node.len == 0) node.len = 0.0001;
			} else if (ch==="'" || ch==='"') node.name = quotedString(ch); //read name
			else node.name = string();
		}
		if(node.name){
			if(idnames[node.name]) node.name = idnames[node.name];
			node.name = node.name.replace(/_/g,' ');
			node.name = node.name.trim(node.name);
		}
		if(node.children.length) node.type = 'stem';
		else node.type = 'label';
		return node;
	},
	
	objectIterate = function(parentNode){ //make stem nodes
		while(ch && ch!=='(') next(); //search for first '('
		var node = new Smits.PhyloCanvas.Node(parentNode);
		while(ch && ch!==')'){ //build node tree
			next();
			if( ch==='(' ) { node.children.push(objectIterate(node)); } //go deeper 
			else { node.children.push(object(node)); } //add leaf
		}
		next(); //one subtree made [found ')'] 
		object(parentNode,node); //add data to node
		return node;		
	},
	
	string = function(){
		var string = '';
		while (ch && ch!==':' && ch!==')' && ch!==',' && ch!=='['){
			string += ch;
			next();
		}
		return string;
	},

	quotedString = function(quoteEnd){
		var string = '';
		next();
		while (ch && ch !== quoteEnd){
			string += ch;
			next();
		}
		next();
		return string;
	},	
	
	next = function(){
		ch = text.charAt(pos);
		if(ch===';') ch = '';
		pos++;
		return ch;
	};

	this.processNodes = Smits.Common.processNodes;
	//initiate
	text = data.newick;
	pos = 0;
	this.mLevel = 0;
	this.mLenFromRoot = 0.0001;
	next();
	treealtered = false;
	this.root = objectIterate(); //read text to nodetree
	model.treealtered(treealtered);
	this.root.len = 0.0001;
	this.root.countChildren();
	model.leafcount(this.root.leafCount); model.nodecount(this.root.nodeCount);
	this.nodeinfo = data.nodeinfo || {};
	this.processNodes(); //process nodetree
};

/// Parse PhyloXML text format to a tree data object ///
Smits.PhyloCanvas.PhyloxmlParse = function(data){
	var mLevel = 0,
	mLenFromRoot = 0.0001,
	root,
		
	recursiveParse = function(clade, parentNode){
		var node = new Smits.PhyloCanvas.Node(parentNode);
		
		clade.children('clade').each(function(){ node.children.push(recursiveParse($(this), node)); });
		
		var nodelen = clade.attr('branch_length')||clade.children('branch_length').text()||0;
		node.len = Smits.Common.roundFloat(nodelen, 4);
		if(node.len == 0) node.len = 0.0001;
		
		node.cladename = clade.children('name').text(); //name. ensembl=>gene ID
		node.confidence = clade.children('confidence').text(); //bootstrap value
		var taxonomy = clade.children('taxonomy'); //species name+id
		if(taxonomy.length){
			node.species = taxonomy.children('scientific_name').text() || taxonomy.children('common_name').text() || '';
			node.species = node.species.replace(/_/g,' ');
			node.taxaid = taxonomy.children('id').text();
		}
		node.name = node.cladename || node.species || (node.children.length? 'Node '+node.id : 'Sequence '+node.id);
		node.name = node.name.trim(node.name);
		
		var cladeseq = clade.children('sequence');
		if(cladeseq.length){
			node.gene = cladeseq.children('name').text(); //ensembl=>gene name
			if(cladeseq.children('mol_seq').length && node.name){
				sequences[node.name] = cladeseq.children('mol_seq').text().split('');
			}
			node.accession = cladeseq.children('accession').text();
		}
		
		var eventinfo = clade.children('events');
		if(eventinfo.length){ //ensembl info for duplication/speciation node
			node.events = {};
			node.events.type = eventinfo.children('type').text().replace(/_/g,' ');
			node.events.duplications = eventinfo.children('duplications').text();
			node.events.speciations = eventinfo.children('speciations').text();
		}
		
		if(node.species) node.displayname = node.species;
		if(node.children.length) node.type = 'stem';
		else node.type = 'label';
		
		return node;
	};
	
	this.getRoot = function(){ return root; };
	this.getMaxLevel = function(){ return mLevel; };
	this.getMaxLen = function(){ return mLenFromRoot; };
	this.processNodes = Smits.Common.processNodes;
	this.mLevel = 0;
	this.mLenFromRoot = 0.0001;
	//initiate	
	xmldata = $($.parseXML(data.phyloxml)).find('phylogeny>clade'); //get root clade (jQuery) object
	if(xmldata.length){
		this.root = recursiveParse(xmldata);
		this.root.len = 0.0001;
		this.root.countChildren();
		model.leafcount(this.root.leafCount); model.nodecount(this.root.nodeCount);
		this.nodeinfo = data.nodeinfo || {};
		this.processNodes(); //process nodetree
	}
};

Smits.PhyloCanvas.Render = {
	Style: {
	/* Default SVG element styles */
	line: {},
	stemline: {},
	text: {
		"font-family":	'Verdana',
		"text-anchor":	'start'
	},
	
	path: {
		"stroke": 'rgb(0,0,0)',
		"stroke-width":	1	
	},
	
	connectedDash : { "stroke-dasharray": "1,4" },
	
	textSecantBg : {
		"fill": '#EEE',
		"stroke": '#DDD'
	},
	
	highlightedEdgeCircle : {
		"stroke": 'red',
		"fill": 'none'
	},
	
	nodeCircle : {
		"fill": "red",
		"fill-opacity": 0,
		"stroke": "red",
		"stroke-opacity": 0,
		"z-index": "10"
	},
	
	getStyle : function(requestStyle, fallbackStyle){
		if(this[requestStyle]) return this[requestStyle];
		else if(this[fallbackStyle]) return this[fallbackStyle];
		else return {};
	}
  },
  
  Parameters: { // Style & mouse event parameters for tree SVG elements
	Rectangular : {
		bufferX			: 5, 		//Padding on tree right side
		paddingX		: 10,		//Padding on tree left side
		bufferInnerLabels : 2, 		//label left side padding, pixels
		minHeightBetweenLeaves : 3,  	// Should be set low, to avoid clipping when implemented
		alignRight		: true,
		showScaleBar	: false		// (STRING,  e.g. "0.05") Shows a scale bar on tree canvas
	},
	
	/*  Rollover Events. Params: {svg,node,x,y,textEl} */
	mouseRollOver : function(params) {
		if(params.node.edgeCircleHighlight){ if(!params.node.active) params.node.edgeCircleHighlight.show(); }
		else {
			var circleObject = params.svg.draw(
				new Smits.PhyloCanvas.Render.Circle(params.x, params.y, 5, {attr: Smits.PhyloCanvas.Render.Style.highlightedEdgeCircle}
			));
			params.node.edgeCircleHighlight = circleObject;
		}					
		if(params.textEl){ //hover on leaf label
		  if(!params.node.active) params.textEl.setAttribute('fill','red');
		  var topy = $(params.textEl).offset().top;
		  var seqy = topy-$('#seq').offset().top;
		  var rowh = model.boxh();
		  seqy = Math.round(seqy/rowh)*rowh; //snap to rowgrid
		  rowborder({y:seqy},'keep'); //highlight seq row
		  params.node.rolltimer = setTimeout(function(){ //show full name on mouse hover
		  	var adj = Boolean(window.webkitRequestAnimationFrame)? 1: 0;//webkit adjustment hack
		  	var cssobj = {'font-size': model.fontsize()+'px', 'color': 'red', 'top': topy+adj+'px', 'left': $("#right").position().left-16+'px'};
			$("#namelabel").css(cssobj);
			$("#namelabel span").css('margin-left',0-$('#names').innerWidth()+6+'px');
			$("#namelabel span").text(params.node.displayname||params.node.name);
			if($(params.textEl).offset().top){ $("#namelabel").fadeIn(100); }
		  },800);
		}
	},
	mouseRollOut : function(params){
		if(params.node.edgeCircleHighlight) params.node.edgeCircleHighlight.hide();
		if(params.textEl){ //mouse out from leaf label
			clearTimeout(params.node.rolltimer);
			$("#namelabel").fadeOut(100);
			if(!params.node.active) params.textEl.setAttribute('fill','black');
		}
	},
	onClickAction : function(params){
		if(params.node.edgeCircleHighlight) params.node.edgeCircleHighlight.hide();		
		if(params.textEl){ //click on leaf label => popup menu
			if(toolsmodel.prunemode){ params.node.highlight(); return; } //toggle highlight
			params.textEl.setAttribute('fill','red');
			var node = params.node;
			node.active = true;
			var menudata = {};
			if(!$.isEmptyObject(model.ensinfo())){ //submenu for leaf (ensembl) metadata
				var ensmenu = {};
				if(node.genetype) ensmenu[node.genetype] = '';
				if(node.taxaname) ensmenu['<span class="note">Taxa</span> '+node.taxaname] = '';
    			if(node.species && node.cladename) ensmenu['<span class="note">Gene</span> '+
    				'<a href="http://www.ensembl.org/'+node.species.replace(' ','_')+'/Gene/Summary?g='+
    				node.cladename+'" target="_blank" title="View in Ensembl">'+(node.gene||node.cladename)+'</a>'] = '';
    			if(node.species && node.accession) ensmenu['<span class="note">Protein</span> '+
    				'<a href="http://www.ensembl.org/'+node.species.replace(' ','_')+'/Transcript/ProteinSummary?p='+
    				node.accession+'" target="_blank" title="View in Ensembl">'+node.accession+'</a>'] = '';
    			if(!$.isEmptyObject(ensmenu)) menudata['<span class="svgicon" title="Data from Ensembl database">'+svgicon('info')+'</span>Ensembl'] = {submenu:ensmenu};
    		} else if(node.species||node.gene){
    			var infomenu = {};
    			if(node.species) infomenu['<span class="note">Species</span> '+node.species] = '';
    			if(node.gene) infomenu['<span class="note">Gene</span> '+node.gene] = '';
    			if(!$.isEmptyObject(infomenu)) menudata['<span class="svgicon" title="View metadata">'+svgicon('info')+'</span>Metadata'] = {submenu:infomenu};
    		}
			menudata['<span class="svgicon" title="Hide node and its sequence">'+svgicon('hide')+'</span>Hide leaf'] = function(){ node.hideToggle(); refresh(); };
			menudata['<span class="svgicon" title="Graft this node to another branch in the tree">'+svgicon('move')+'</span>Move leaf'] = function(){ setTimeout(function(){ node.highlight(true) },50); movenode('',node,'tspan'); };
    		menudata['<span class="svgicon" title="Place this node as the tree outgroup">'+svgicon('root')+'</span>Place root here'] = function(){ node.reRoot(); refresh(); };
    		menudata['<span class="svgicon" title="Remove this node from the tree">'+svgicon('trash')+'</span>Remove leaf'] = function(){ node.remove(); refresh(); };
    		setTimeout(function(){ tooltip('','',{clear:true, arrow:'top', data:menudata, style:'none', nodeid:node.id, style:"leafmenu",
    		target:{ x:$("#names").offset().left, y:$(params.textEl).offset().top, height:model.boxh(), width:$("#names").width() }}) },100);
    	}
	},

	set : function(param, value, treeType){
		if(treeType) this['Rectangular'][param] = parseFloat(value);
		else this[param] = parseFloat(value);
	}
  }//Render.Parameters
};

Smits.PhyloCanvas.Render.Line = function(x1, y1, x2, y2, params){
	this.type = 'line';
	this.attr = Smits.PhyloCanvas.Render.Style.line;
	this.x1 = x1;
	this.x2 = x2;
	this.y1 = y1;
	this.y2 = y2;
	if(params) {
		Smits.Common.apply(this, params);
		if(params.attr) this.attr = params.attr;
	}
};
Smits.PhyloCanvas.Render.Text = function(x, y, text, params){
	this.type = 'text';
	this.attr = Smits.PhyloCanvas.Render.Style.text;
	this.x = x;
	this.y = y;
	this.text = text;
	if(params) {
		Smits.Common.apply(this, params);
		if(params.attr) this.attr = params.attr;
	}
};
Smits.PhyloCanvas.Render.Path = function(path, params){
	this.type = 'path';
	this.attr = Smits.PhyloCanvas.Render.Style.path;
	this.path = path;
	if(params) {
		Smits.Common.apply(this, params);
		if(params.attr) this.attr = params.attr;
	}
};
Smits.PhyloCanvas.Render.Circle = function(x, y, radius, params){
	this.type = 'circle';
	this.x = x;
	this.y = y;
	this.radius = radius;
	if(params) {
		Smits.Common.apply(this, params);
		if(params.attr) this.attr = params.attr;
	}
};

//create SVG canvas elements on first tree render
Smits.PhyloCanvas.Render.SVG = function(){
	this.canvasSize = [50,100]; //will be updated in render.phylogram()
	this.svg1 = Raphael('tree', "100%", "100%");
	this.svg2 = Raphael('names', "100%", "100%");
	$(this.svg2.canvas).css('font-size',model.fontsize()+'px');
	this.percX = function(num){ return (num/this.canvasSize[0]*100).toFixed(4)+'%'; };
	this.percY = function(num){ return (num/this.canvasSize[1]*100).toFixed(4)+'%'; };
};

Smits.PhyloCanvas.Render.SVG.prototype = {
	//Functions for svg object (has multiple svgs)
	draw : function(instruct){
		var obj = {};
		if(instruct.type == 'line'){
			obj = this.svg1.line(this.percX(instruct.x1), this.percY(instruct.y1), this.percX(instruct.x2), this.percY(instruct.y2)).attr(instruct.attr);
		} else if(instruct.type == 'path'){
			obj = this.svg1.path(instruct.path).attr(instruct.attr);			
		} else if(instruct.type == 'circle'){
			obj = this.svg1.circle(this.percX(instruct.x), this.percY(instruct.y), instruct.radius).attr(instruct.attr);
		} else if(instruct.type == 'text'){
			if(instruct.attr.svg == 'svg1'){ obj = this.svg1.text(instruct.x, this.percY(instruct.y), instruct.text).attr(Smits.PhyloCanvas.Render.Style.text); }
			else { obj = this.svg2.text(instruct.x, this.percY(instruct.y), instruct.text).attr(Smits.PhyloCanvas.Render.Style.text); }
			if(instruct.attr){
				obj.attr(instruct.attr);
			}
		}
		return obj;
	}
};

/// Draw a new tree. Input: tree data object + svg canvas ///
Smits.PhyloCanvas.Render.Phylogram = function(svg, data){
	var sParams = Smits.PhyloCanvas.Render.Parameters.Rectangular,
	canvasWidth, canvasHeight, scaleX, scaleY, maxBranch,
	minHeightBetweenLeaves, firstBranch = true, absoluteY = 0,
	x1, x2, y, positionX, positionY, visiblerows = [],
	bufferX, paddingX, namecounter = 0;
	
	var calculateNodePositions = function (node, positionX){
		//set baseline of current row
		if(node.len && !firstBranch && !node.visibleChildCount && !node.hidden) absoluteY = absoluteY + scaleY;
		
		if(node.children.length > 0){ //draw stemlines
			var nodeCoords = [], x1, x2, y;
			node.restoreAnc();
			
			if(node.hidden || !node.len) return [];
			
			x1 = positionX;
			x2 = positionX = positionX + (scaleX * node.len);
			y = absoluteY + (node.getMidbranchPosition(firstBranch) * scaleY);
			//horizontal line
			var lineattr = Smits.PhyloCanvas.Render.Style.getStyle('stemline', 'line'); //set style, fallback style
			lineattr.svg = 'svg1'; lineattr.class = 'horizontal';
			var circleattr = Smits.PhyloCanvas.Render.Style.nodeCircle;
			var stem = svg.draw(new Smits.PhyloCanvas.Render.Line(x1, y, x2, y, { attr: lineattr }));
			stem.node.setAttribute("title","Branch length: "+node.len);
			stem.node.setAttribute("nodeid",node.id);
			
			//traverse to children and draw vertical line
			if(node.visibleChildCount>0){
				for(var i = 0; i < node.children.length; i++){
					var child = node.children[i];
					if(child.hidden) continue;
					nodeCoords.push(calculateNodePositions(child, positionX));
				}
				nodeCoords.push(y);
			  	if(node.visibleLeafCount>1){ //get vertical bounds of children
			  		var verticalY1 = Math.min.apply(null, nodeCoords);
			  		var verticalY2 = Math.max.apply(null, nodeCoords);
			  		var vline = svg.draw(new Smits.PhyloCanvas.Render.Line(positionX, verticalY1, positionX, verticalY2, { attr : Smits.PhyloCanvas.Render.Style.line }));
			  		vline.toBack();
				}
			}
			
			//draw injunction spot circle
			var tipnote = '';
			var cradius = 2;
			var spotattr =  {fill:'black',stroke:'black'};
			if(node.children[node.children.length-2].type=='ancestral') spotattr.fill = 'white'; //has ancestral seq.
			var first = node.children[0].hidden;
			var last = node.children[node.children.length-1].hidden;
			if(first || last){ //has hidden branch(es)
				spotattr.fill = 'white';
				var hastree = (first&&node.children[0].type!='label')||(last&&node.children[node.children.length-1].type!='label');
				if(first && last){ //anc. shown, both branches hidden
					spotattr.stroke = 'orange';
					tipnote = 'Only node seq. shown';
				}else{ //one branch hidden
					tipnote = hastree? 'Subtree hidden' : 'One leaf hidden';
				}
				if(hastree) cradius = 4; else cradius = 3;
			}
			if(node.altered){
				spotattr.fill = 'red';
				tipnote = 'Needs realignment';
			}
			if(node.events&&node.events.duplications){
				spotattr.fill = 'lightblue'; spotattr.stroke = 'blue';
				if(!tipnote) tipnote = 'Duplication node';
			}
			svg.draw(new Smits.PhyloCanvas.Render.Circle((x2 || positionX), y, cradius, { attr: spotattr }));
			
			//draw injuction spot hover circle
			var circle = svg.draw(new Smits.PhyloCanvas.Render.Circle((x2 || positionX), y, 5, { attr: circleattr }));
			node.edgeCircleHighlight = node.svgEl = circle;
			circle.node.setAttribute("nodeid",node.id);
			tipnote = $('#right').hasClass('dragmode')? '' : (node.name.length>5?'<br>':' ')+'<span class="note">'+(tipnote||'Click or drag')+'</span>';
			var name = node.displayname || node.name || 'no name';
			
			circle.mouseover(function(e){
				if(!$('#treemenu .tooltipcontent').text()){ 
					//circle.toFront(); 
					circle.attr({'fill-opacity':'1'});
					tooltip(e, name+tipnote, {target:'circle', id:"treemenu", arrow:'left', style:'black', nodeid:node.id, nohide:true});
				}
			});
			circle.mouseout(function(){ if(!$('#treemenu .tooltipcontent').text()) hidetooltip("#treemenu") });
			circle.click(function(e){
				if(!$('#treemenu .tooltipcontent').text()){
					e.stopPropagation();
					tooltip(e, name, {clear:true, target:'circle', id:"treemenu", style:'black', data:{}, nodeid:node.id, nomove:true});
					e.stopPropagation();
				}
			});
		} else { //draw leaflines and labels
			if(node.hidden){ if(node.type!='ancestral') leafnodes[node.name] = node; return []; }
			else leafnodes[node.name] = node;
			
			x1 = positionX;
			x2 = positionX + (scaleX * node.len);
			if(x2 > maxBranch) x2 = maxBranch;
			y = absoluteY;			
				
			//horizontal endline
			var leafline = svg.draw(new Smits.PhyloCanvas.Render.Line(x1, y, x2, y));
			leafline[0].setAttribute("class","horizontal");
			leafline[0].setAttribute("nodeid",node.id);
			leafline[0].setAttribute("title","Branch length: "+node.len);
			if(sParams.alignRight && maxBranch>(x2+5)){ //dotline
				var dotline = svg.draw(new Smits.PhyloCanvas.Render.Line( x2, y, maxBranch, y, { attr : Smits.PhyloCanvas.Render.Style.connectedDash }));
				dotline[0].setAttribute("class","horizontal");
				dotline[0].setAttribute("nodeid",node.id);	
			}
			
			if(node.name){
				visiblerows.push(node.name);
				var attr = {};
				var labely = y+(scaleY*0.3);
				
				// leaf label
				if(node.style) attr = Smits.PhyloCanvas.Render.Style.getStyle(node.style, 'text');
				attr["text-anchor"] = 'start';
				if(node.description){ attr.title = node.description };
				node.count = namecounter;
				var leaflabel = svg.draw(new Smits.PhyloCanvas.Render.Text(sParams.bufferInnerLabels, labely, node.displayname||node.name, {attr: attr}));
				leaflabel[0].childNodes[0].setAttribute("nodeid",node.id);
				node.svgEl = leaflabel;
				
				// hover and click events for label element
				if(Smits.PhyloCanvas.Render.Parameters.mouseRollOver){
					Smits.Common.addRaphEventHandler(
						leaflabel, 
						'mouseover', 
						Smits.PhyloCanvas.Render.Parameters.mouseRollOver, 
						{ svg: svg, node: node, x: x2, y: y, textEl: leaflabel[0] }
					);
				}
				if(Smits.PhyloCanvas.Render.Parameters.mouseRollOut){
					Smits.Common.addRaphEventHandler(
						leaflabel, 
						'mouseout', 
						Smits.PhyloCanvas.Render.Parameters.mouseRollOut, 
						{ node: node, x: x2, y: y, textEl: leaflabel[0] }
					);				
				}
				if(Smits.PhyloCanvas.Render.Parameters.onClickAction){
					Smits.Common.addRaphEventHandler(
						leaflabel, 
						'click', 
						Smits.PhyloCanvas.Render.Parameters.onClickAction, 
						{ svg: svg, node: node, x: x2, y: y, textEl: leaflabel[0], data: data }
					);				
				}
			}
			
			if(firstBranch){
				firstBranch = false;
			}
			namecounter ++;
		
		}
		return y;
	};
	
	var drawScaleBar = function (){
		//y = absoluteY + scaleY;
		y = 20;
		x1 = 10;
		x2 = x1 + (sParams.showScaleBar * scaleX);
		svg.draw(new Smits.PhyloCanvas.Render.Line(x1, y, x2, y));
		svg.draw(new Smits.PhyloCanvas.Render.Text((x1+x2)/2, y-8, sParams.showScaleBar));
	};
		
	//reset environment
	$('#treewrap').css('display','none');
	svg.svg1.clear(); svg.svg2.clear();
	model.visiblerows.removeAll(); visiblerows = [];
	leafnodes = {};
		
	data.root.countChildren();
	seqcount = data.root.visibleLeafCount; //tree height estimation.
	if(!seqcount){
		dialog('error','Found no leafs to show when rendering the tree canvas.<br>Probably a data parsing error.');
		return;
	}
		
	canvasWidth = $("#treewrap").width(); //update canvas dimensions
	canvasHeight = seqcount*model.boxh();
	svg.canvasSize = [canvasWidth,canvasHeight];
			
	bufferX = sParams.bufferX;
	paddingX = sParams.paddingX;
	scaleX = Math.round((canvasWidth - bufferX - paddingX) / data.mLenFromRoot);
	maxBranch = Math.round(canvasWidth - bufferX); //pixel width of tree drawing area
		
	scaleY = model.boxh(); //height of row
	minHeightBetweenLeaves = sParams.minHeightBetweenLeaves;
	if(scaleY < minHeightBetweenLeaves) scaleY = minHeightBetweenLeaves;
		
	absoluteY = scaleY*0.6;
	firstBranch = true;
	calculateNodePositions(data.root, paddingX); //build up tree SVG elements
	model.visiblerows(visiblerows);
	$('#treewrap').css('display','block');
	
	// Draw Scale Bar
	if(sParams.showScaleBar) drawScaleBar();
};