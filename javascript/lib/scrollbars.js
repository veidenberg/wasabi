/*
Scrollbar library to make sequence & tree areas scrollable
Based on malihu custom scrollbar plugin - http://manos.malihu.gr
Rebuilt for Wasabi web application by Andres Veidenberg //andres.veidenberg{at}helsinki.fi//, University of Helsinki [2012]
*/
function mCustomScrollbar(){
	var $verticalDragger_container = $("#verticalDragger");
	var $verticalDragger = $("#verticalDragger .dragger");
	var $scrollUpBtn = $("#verticalDragger .scrollUpBtn");
	var $scrollDownBtn = $("#verticalDragger .scrollDownBtn");
	var $horizontalDragger_container = $("#horizontalDragger");
	var $horizontalDragger = $("#horizontalDragger .dragger");
	var $scrollLeftBtn = $("#horizontalDragger .scrollLeftBtn");
	var $scrollRightBtn = $("#horizontalDragger .scrollRightBtn");
	
	//get & store minimum dragger height & width (defined in css)
	if(!dom.seqwindow.data("minDraggerHeight")){
		dom.seqwindow.data("minDraggerHeight",$verticalDragger.height());
	}
	if(!dom.seqwindow.data("minDraggerWidth")){
		dom.seqwindow.data("minDraggerWidth",$horizontalDragger.width());
	}
	
	//get & store original content height & width
	if(!dom.seqwindow.data("contentHeight")){
		dom.seqwindow.data("contentHeight",dom.seq.height());
	}
	if(!dom.seqwindow.data("contentWidth")){
		dom.seqwindow.data("contentWidth",dom.wrap.width());
	}
	
	CustomScroller();
	
	function CustomScroller(reloadType){
		///  horizontal scrolling  ///
		var visibleWidth = dom.seqwindow.innerWidth();
		var totalContentWidth = $("#seq").width();
		if(totalContentWidth>visibleWidth){ //enable scrollbar if content is long
			$horizontalDragger.css("display","block");
			if(reloadType!="resize" && totalContentWidth!=dom.seqwindow.data("contentWidth")){
				$horizontalDragger.css("left", 0);
				dom.wrap.css("left", 0);
				dom.seqwindow.data("contentWidth", totalContentWidth);
			}
			$horizontalDragger_container.css("display","block");
			$scrollLeftBtn.css("display","block");
			$scrollRightBtn.css("display","block");
			var minDraggerWidth = dom.seqwindow.data("minDraggerWidth");
			var draggerContainerWidth = $horizontalDragger_container.width();

			//adjust dragger width by content
			var adjDraggerWidth = Math.round((visibleWidth/totalContentWidth)*draggerContainerWidth);
			//minimum dragger width
			if(adjDraggerWidth<=minDraggerWidth) $horizontalDragger.css("width",minDraggerWidth+"px");
			else $horizontalDragger.css("width",adjDraggerWidth+"px");
			var draggerWidth = $horizontalDragger.width();
			var draggerXMax = draggerContainerWidth-draggerWidth;
			
			$horizontalDragger.draggable({ 
				axis: "x", 
				containment: [$horizontalDragger_container.offset().left, 0, $horizontalDragger_container.offset().left+draggerXMax], 
				drag: function(){ ScrollX(false,'drag') }, 
				stop: function() { $horizontalDragger.removeClass('pressed') }
			});
			
			$horizontalDragger_container.off('click').click(function(e){ //scroll line click => scroll to clicked spot
				var mouseCoord=(e.pageX - $(this).offset().left);
				if(mouseCoord<$horizontalDragger.position().left || mouseCoord>($horizontalDragger.position().left+draggerWidth)){
					var targetPos = mouseCoord+draggerWidth;
					if(targetPos < draggerContainerWidth){
						$horizontalDragger.css("left",mouseCoord);
						ScrollX(false,'click');
					} else {
						$horizontalDragger.css("left",draggerXMax);
						ScrollX(false,'click');
					}
				}
			});
				
			//scroll button click => scroll one page
			$scrollLeftBtn.off('click').click(function(e){ e.stopPropagation(); ScrollX(0-visibleWidth,'leftbtn'); });
			$scrollRightBtn.off('click').click(function(e){ e.stopPropagation(); ScrollX(visibleWidth,'rightbtn'); });
			//arrow keys => scroll half page
			$(document).off('keydown').on('keydown',function(e){
				if(e.target.tagName!='INPUT'){
    				if (e.keyCode==37){ e.preventDefault(); ScrollX(0-(visibleWidth/2),'leftbtn'); }
        			else if (e.keyCode==39){ e.preventDefault(); ScrollX(visibleWidth/2,'rightbtn'); }
        		}
    		});
			//scroll
			var scrollXAmount = (totalContentWidth-visibleWidth)/draggerXMax;
			$horizontalDragger.css("left", (0-dom.wrap.position().left)/scrollXAmount);
				
			//drag by ruler
			var wrapoffset = dom.wrap.offset().left;
			dom.wrap.draggable({
				handle: "#ruler",
				axis: "x",
				start: function(e,ui){ draginertia.start(0-totalContentWidth+visibleWidth, scrollXAmount, ui.position.left, e.timeStamp) },
				drag: function(e,ui){
					draginertia.add(ui.position.left, e.timeStamp);
					$horizontalDragger.css("left",(0-ui.position.left)/scrollXAmount); 
				},
       			stop: function(e,ui){ draginertia.end(e.timeStamp); } 
			});
		} else { //disable scrollbar if content is short
			$horizontalDragger.css("left",0).css("display","none"); //reset content scroll
			dom.wrap.css("left",0);
			$horizontalDragger_container.css("display","none");
			$scrollLeftBtn.css("display","none");
			$scrollRightBtn.css("display","none");
		}
			
		///  vertical scrolling  ///
		var visibleHeight = dom.seqwindow.innerHeight()-$("#ruler").outerHeight()-parseInt($("#seqwrap").css('margin-top'));
		//var totalContentHeight = $("#seq").height()+10;
		var totalContentHeight = model.visiblerows().length ? model.visiblerows().length*model.boxh()+10 : model.leafcount()*model.boxh()+10;
		if(totalContentHeight>visibleHeight){ //enable scrollbar if content is long
			$verticalDragger.css("display","block");
			if(reloadType!="resize" && totalContentHeight!=dom.seqwindow.data("contentHeight")){
				$verticalDragger.css("top",0);
				dom.seq.css("margin-top",0);
				dom.seqwindow.data("contentHeight",totalContentHeight);
			}
			$verticalDragger_container.css("display","block");
			$scrollDownBtn.css("display","block");
			$scrollUpBtn.css("display","block");
			var minDraggerHeight = dom.seqwindow.data("minDraggerHeight");
			var draggerContainerHeight = $verticalDragger_container.height();
	
			//adjust dragger height by content
			var adjDraggerHeight = Math.round((visibleHeight/totalContentHeight)*draggerContainerHeight);
			//minimum dragger height
			if(adjDraggerHeight<=minDraggerHeight) $verticalDragger.css("height",minDraggerHeight+"px").css("line-height",minDraggerHeight+"px");
			else $verticalDragger.css("height",adjDraggerHeight+"px").css("line-height",adjDraggerHeight+"px");
			var draggerHeight = $verticalDragger.height();
			var draggerYMax = draggerContainerHeight - draggerHeight;

			$verticalDragger.draggable({ 
				axis: "y", 
				containment: [0,$verticalDragger_container.offset().top,0,$verticalDragger_container.offset().top+draggerYMax], 
				drag: function(){ ScrollY(false,'drag') }, 
				stop: function() { $verticalDragger.removeClass('pressed') }
			});
				
			$verticalDragger_container.off('click').click(function(e) {
				var mouseCoord = (e.pageY - $(this).offset().top);
				if(mouseCoord < $verticalDragger.position().top || mouseCoord>($verticalDragger.position().top+draggerHeight)){
					var targetPos = mouseCoord+draggerHeight;
					if(targetPos < draggerContainerHeight){
						$verticalDragger.css("top",mouseCoord);
						ScrollY(false,'click');
					} else {
						$verticalDragger.css("top",draggerYMax);
						ScrollY(false,'click');
					}
				}
			});

			//scroll buttons
			$scrollDownBtn.off('click').click(function(e){ e.stopPropagation(); ScrollY(visibleHeight,'downbtn'); });
			$scrollUpBtn.off('click').click(function(e){ e.stopPropagation(); ScrollY(0-visibleHeight,'upbtn'); });
			//arrow keys => scroll half page
			$('body').off('keydown').on('keydown',function(e){
    			if (e.keyCode==38){ e.preventDefault(); ScrollY(0-(visibleHeight/2),'upbtn'); }
        		else if (e.keyCode==40){ e.preventDefault(); ScrollY(visibleHeight/2,'downbtn'); }
    		});

			var scrollYAmount = (totalContentHeight-visibleHeight)/draggerYMax;
			$verticalDragger.css("top", (0-parseInt(dom.seq.css('margin-top')))/scrollYAmount);
		} else { //disable scrollbar if content is short
			$verticalDragger.css("top",0).css("display","none"); //reset content scroll
			dom.seq.css("margin-top",0);
			$("#treewrap").css("top",0);
			$verticalDragger_container.css("display","none");
			$scrollDownBtn.css("display","none");
			$scrollUpBtn.css("display","none");
		}
		
		var scrollXTimer;
		// do horizontal scrolling ([specific point to scroll],[scroll source (debug)]) //
		function ScrollX(shift,id){
			var draggerX = $horizontalDragger.position().left;
			var posX = parseInt(dom.wrap.css('left'));
			if(shift){
				var target = posX-shift;
				var draggerPos = (0-target)/scrollXAmount;
				if(draggerPos<0){ draggerPos = 0; }else if(draggerPos>draggerXMax){ draggerPos = draggerXMax; }
				draggerPos = Math.round(draggerPos);
				$horizontalDragger.css('left',draggerPos);
			} else { var target = Math.round(-draggerX*scrollXAmount); }
			
			if(target>0){ target = 0; }
			else if(Math.abs(target)>totalContentWidth-visibleWidth){ target = visibleWidth-totalContentWidth; }
			clearTimeout(scrollXTimer);
			scrollXTimer = setTimeout(function(){ makeImage('x:'+target) },100);
			dom.wrap.css('left',target);
		}
		var scrollYTimer;
		// do vertical scrolling //
		function ScrollY(shift,id){
			var draggerY = $verticalDragger.position().top;
			var marginY = parseInt(dom.seq.css('margin-top'));
			clearTimeout(scrollYTimer);
			scrollYTimer = setTimeout(makeImage,100);
			if(shift){
				var target = marginY-shift;
				var draggerPos = (0-target)/scrollYAmount;
				if(draggerPos<0){ draggerPos = 0; }else if(draggerPos>draggerYMax){ draggerPos = draggerYMax; }
				draggerPos = Math.round(draggerPos);
				$verticalDragger.css('top',draggerPos);
			}
			else{
				var target = Math.round(-draggerY*scrollYAmount);
			}
			clearTimeout(scrollYTimer);
			scrollYTimer = setTimeout(function(){ makeImage('y:'+target) },100);
			if(target>0){ target = 0; } else if(Math.abs(target)>totalContentHeight-visibleHeight){ target = visibleHeight-totalContentHeight; }
			dom.seq.css('margin-top',target);
			dom.treewrap.css('top',target);
			$.each([$("#namelabel"),$("#treemenu"),$("div.tooltip.leafmenu")],function(m,menu){ //move tree tooltips
				if(menu.length) menu.css('top',menu.position().top+target-marginY);
			});
		}
				
		//mousewheel
		$("#left, #seqwindow").off("mousewheel");
		$("#left, #seqwindow").on("mousewheel", function(event, delta, deltaX, deltaY){
			event.preventDefault();
			if(deltaX && $horizontalDragger.length){
				var velX = Math.abs(deltaX*10);
				$horizontalDragger.css("left", $horizontalDragger.position().left+(deltaX*velX));
				if($horizontalDragger.position().left < 0) $horizontalDragger.css("left", 0);
				else if($horizontalDragger.position().left > draggerXMax) $horizontalDragger.css("left", draggerXMax);
				ScrollX(false,'scroll');
			} else if(deltaY && $verticalDragger.length){
				var velY = Math.abs(deltaY*10);
				$verticalDragger.css("top", $verticalDragger.position().top-(deltaY*velY));
				if($verticalDragger.position().top < 0) $verticalDragger.css("top", 0);
				else if($verticalDragger.position().top > draggerYMax) $verticalDragger.css("top", draggerYMax);
				ScrollY(false,'scroll');
			}
		});
		
		var pressaction = function(){ $(this).addClass('pressed') };
		var releaseaction = function(){ $(this).removeClass('pressed') };
		$horizontalDragger.mousedown(pressaction).mouseup(releaseaction);
		$verticalDragger.mousedown(pressaction).mouseup(releaseaction);
	}
	//recalculate scrollbars after window resize
	var resizeTimer
	$(window).resize(function() {
		if($horizontalDragger.position().left>$horizontalDragger_container.width()-$horizontalDragger.width()){
			$horizontalDragger.css("left", $horizontalDragger_container.width()-$horizontalDragger.width());
		}
		if($verticalDragger.position().top>$verticalDragger_container.height()-$verticalDragger.height()){
			$verticalDragger.css("top", $verticalDragger_container.height()-$verticalDragger.height());
		}
		clearTimeout(resizeTimer);
		resizeTimer = setTimeout(function(){ CustomScroller("resize"); },100);
	});
}//mCustomScrollbar()

//add inertia for the sequence area ruler drag
var draginertia = new function(){  
    var amplify = 500;  //adjust momentum
    var stamps = [];
    var limit = 0;
    var draggeradj = 0;
    
    this.start = function(lim,adj,pos,time){ limit = lim; draggeradj = adj; stamps = [{pos:pos,time:time}]; };
    
    this.add = function(pos,time){ stamps.push({pos:pos,time:time}); if(stamps.length > 2){ stamps.shift() } };

    this.end = function(time){
    	stamps[1].time = time;        
        var distance = Math.abs(stamps[1].pos - stamps[0].pos);
        var time = stamps[1].time - stamps[0].time;
        var speed = distance/time;
        var inertia = speed > 0.02 ? Math.round(speed*amplify) : 0;
		var curpos = dom.wrap.position().left;
        var endstop = stamps[0].pos>stamps[1].pos ? curpos-inertia : curpos+inertia;
        
        var easetype = 'easeOutCirc';
        if(endstop>0){ endstop = 0; easetype = 'easeOutBack'; }
        else if(endstop<limit){ endstop = limit; easetype = 'easeOutBack'; }
        $("#horizontalDragger .dragger").animate({ left:(0-endstop)/draggeradj+'px' }, 800, easetype);
        dom.wrap.animate({ left:endstop+'px' }, 800, easetype);
        setTimeout(makeImage,850);
    };

};