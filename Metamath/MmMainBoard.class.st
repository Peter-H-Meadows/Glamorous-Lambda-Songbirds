"
this is the main workspace. basicUsableThings go in leftmost box. ultimate wanted thing on right.
middle is for stuff were using.

usable things at top half.
"
Class {
	#name : #MmMainBoard,
	#superclass : #BlElement,
	#instVars : [
		'controller',
		'currentlySelectedElement',
		'mainWorkspace',
		'usableList',
		'proofToDo',
		'aList',
		'workingOnList',
		'aPannableElement'
	],
	#category : #'Metamath-Game'
}

{ #category : #adding }
MmMainBoard >> addBasicUsableThing: el [ 

basicUsableThings addChild: el
]

{ #category : #adding }
MmMainBoard >> addMiddleThing: el [ 

middleThings addChild: el
]

{ #category : #adding }
MmMainBoard >> addOnBoardUsableEHypoths [

| el aEventListener |
el := BlElement new constraintsDo: [ :c | 
	c horizontal fitContent .
	c vertical fitContent  ].

el layout: BlLinearLayout vertical "alignCenter" .
"el clipChildren: false ."

proofToDo eHypoths do: [ :ea | | eee |
	
	"ea setCompleted ."
	eee := MmOnBoardEssentialHypothesisElement new model: ea .
	
	aEventListener := MmOnBoardHypothEventListener new gameController: controller .
	eee addEventHandler: aEventListener .
	el addChild: eee .
	
] .

el constraintsDo: [ :c |

		c frame horizontal alignLeft.
		c frame vertical alignTop .
].

self addChild: el .
]

{ #category : #adding }
MmMainBoard >> addToBoard: assertion [

| usable el |

self error .

usable := assertion copy .
assertion clean .

"if it has no ehypoths, add to right section. "

el := usable assertionAndEssentialHypothesisElement: controller .

usable hasEhypoths ifTrue: [  
	self  addMiddleThing: el .
] ifFalse: [  
	self addBasicUsableThing: el
] . 

]

{ #category : #adding }
MmMainBoard >> addToList: m [
| c |
c := workingOnList items asOrderedCollection  .
c add: m .
workingOnList items: c 
]

{ #category : #adding }
MmMainBoard >> addToMain: mod [ 

			mainWorkspace addChild: (mod  copy "AndClean"  assertionAndEssentialHypothesisElement: controller) .	
]

{ #category : #adding }
MmMainBoard >> addToWorkingBoard: assertion [

| usable el aPullable aContainer |
"usable := assertion copy .
assertion clean .
usable setAllVariablesToFree ."

"if it has no ehypoths, add to right section. "

"assertion clean ."

usable := assertion copyAndClean .

"self addToList: usable ."

"workingOnList" 

mainWorkspace addChild: ((usable assertionAndEssentialHypothesisElement: controller) addEventHandler: BlPullHandler new allowOutOfBounds ).

	"aPullable := BlElement new
		border: (BlBorder paint: Color lightGray width: 2);
		background: Color veryLightGray;
		size: 100@100;
		addEventHandler: BlPullHandler new allowOutOfBounds.
		
	aContainer := BlElement new
		background: Color veryVeryLightGray;
		size: 400@300;
		addChild: aPullable.

self addChild: aContainer."

"el := usable assertionAndEssentialHypothesisElement: controller .

self  addMiddleThing: el ."


]

{ #category : #adding }
MmMainBoard >> addUsable [ 
"| mm |
mm := proofToDo prevAssertions  asOrderedCollection .
mm addAll: proofToDo prevProofs   asArray ."


(proofToDo assertionsUsed  findTokens: Character separators ) reverseDo: [ :each | | thing |
	
	thing := proofToDo prevAssertions at: each ifAbsent: [proofToDo prevProofs at: each] .

	thing body isWFF ifTrue: [
			

	] ifFalse: [ 
	

"self addToList: usable ."

"workingOnList" 

			"mainWorkspace addChild: (thing copyAndClean  assertionAndEssentialHypothesisElement: controller) .	"
				
				self addToMain: thing 
	
		"thing setAllVariablesToFree.
		usableTurnstiles add: thing ."	
				
	]. 
] .
]

{ #category : #accessing }
MmMainBoard >> addUsableThingsLists [
| usableTurnstiles usableWFFs aEventListener el wffPane wffScroll anAccordion tPane tScroll anAccordiont anAccordionw |
usableTurnstiles := proofToDo eHypoths . 
usableWFFs := OrderedCollection new.
proofToDo assertionsUsed reverseDo: [ :each | | thing |
	
	"each name = 'mp2' ifTrue: [ self halt ]." "self halt."
	
	"thing :=" "controller universe assertionNamed:" "ProofDict at: each copyAndClean"  .
	
	thing := proofToDo prevAssertions at: each .

	thing body isWFF ifTrue: [
			usableWFFs add: thing .

	] ifFalse: [ 
	
		"blah hasEhypoths ifFalse: [ blah setAllVariablesToFixed . ] ."
	
		thing setAllVariablesToFree.
				
		usableTurnstiles add: thing .	
				
	]. 
] .

"wffPane := BlElement new constraintsDo: [ :c | 
	c horizontal fitContent .
	c vertical fitContent 
];
background: BlTransparentBackground new;
layout: BlLinearLayout horizontal .				

usableWFFs do: [ :ea | 

	aEventListener := MmListUsableEventListener new gameController: controller  .
	el := ea elementForStartingList addEventHandler: aEventListener .
	(el background: Color lightGray).
	wffPane addChild: el .

].

wffScroll := BrScrollPane new
		look: MmScrollPaneLook + MmScrollbarLook .
wffScroll content: wffPane .

anAccordionw := BrAccordion new.
	anAccordionw hMatchParent; vFitContent.

	anAccordionw look: BrGlamorousAccordionLook new.
	anAccordionw header: [
		BrButton new
			look: BrGlamorousAccordionHeaderLook new;
			label: 'wffs';
			action: [ anAccordionw toggle ] ].
	anAccordionw content: [
		wffScroll.	
	]."
	

"self addChild: anAccordion ."


tPane := BlElement new constraintsDo: [ :c | 
	c horizontal fitContent "matchParent" .
	c vertical fitContent "matchParent"
];
background: BlTransparentBackground new;
layout: BlLinearLayout horizontal .				

usableTurnstiles do: [ :ea | 

	aEventListener := MmListUsableEventListener new gameController: controller  .
	el := ea elementForStartingList addEventHandler: aEventListener .
	"el background: Color lightGray."
	tPane addChild: el .

].

"tScroll := BrScrollPane new
		look: MmScrollPaneLook + MmScrollbarLook .
tScroll content: tPane ."


self addChild: tPane .

"anAccordiont := BrAccordion new.
	anAccordiont hMatchParent; vFitContent.

	anAccordiont look: BrGlamorousAccordionLook new.
	anAccordiont header: [
		BrButton new
			look: BrGlamorousAccordionHeaderLook new;
			label: 'provables';
			action: [ anAccordiont toggle ] ].
	anAccordiont content: [
		tScroll.	
	].
anAccordiont toggle ."
	
"anAccordion := BrAccordion new.
	anAccordion hMatchParent; vFitContent.

	anAccordion look: BrGlamorousAccordionLook new.
	anAccordion header: [
		BrButton new
			look: BrGlamorousAccordionHeaderLook new;
			label: 'usables';
			action: [ anAccordion toggle ] ].
	anAccordion content: [
		(BrVerticalPane new addChildren: { anAccordiont. anAccordionw })
	].
	
self addChild: anAccordion .
anAccordion toggle "
]

{ #category : #accessing }
MmMainBoard >> controller: c [

controller := c
]

{ #category : #accessing }
MmMainBoard >> createUsableThingsList [
"ehypoths and assertions/proofs  that we can click to use and make a wanted thing"
| usableAssertions  aEventListener aPager pp ppx elx spane |

usableAssertions := proofToDo eHypoths . 

"proofToDo assertions collect: [ :ea | ] thenReject: " 

proofToDo assertionsUsed reverseDo: [ :each | | blah |
	
"		each name = 'mp2' ifTrue: [ self halt ]."
	blah := (controller universe assertionNamed: each) copyAndClean .
	
	"blah body isWFF ifTrue: [ self halt ] ."
	
	"blah body isWFF ifFalse: [ " 
	
	
	"blah hasEhypoths ifFalse: [ blah setAllVariablesToFixed . ] ."
	
	"( { 'wi' . 'wn' . 'ax-3' } includes: blah name ) ifFalse: [ "
		
				blah setAllVariablesToFree.
				
				usableAssertions add: blah .
				
			"]."
				
				
	"] . "
] .

"usableList dataSource: (MmUsableDataSource new controller: controller ; proofs: usableThings) ."

"usableEhypoths := proofToDo eHypoths collect: [ :each | topBoard addChild: ( each pcopy usableElement: controller ) ] ."


"aList := BrSimpleList new.
aList stencil: [ :each :index | 
			aEventListener := MmListUsableEventListener new gameController: controller  .
			each elementForStartingList addEventHandler: aEventListener .
]."
			
"aList items: usableAssertions ."
		
"aList when: BrSelectionChanged
			do: [ :anEvent | 
			anEvent
				selectedDo: [ :anInterval | self halt ].
			anEvent
				deselectedDo: [ :anInterval | self halt ] ]."
		
"aList hFitContent ."

aPager := BrPager new. 

pp := (BrButton new
			beHuge; size: 300@100 ;
			look: BrGlamorousButtonWithLabelLook new;
			label: 'Nexxxxxxxxxxxxxxxxxx xxxxxxxxxxxxxxxxxxxxxxxxxxxxxt';
			action: [
				aPager addPage: (BrPagerPageElementMM new
					"layout: BlLinearLayout vertical alignCenter;"
					background: (Color random );
					
					addChild: (BrLabel new
						look: (BrGlamorousLabelLook new fontSize: 30; foreground: Color random);
						text: 'New page')).
				aPager scrollToLast ]).


ppx := BlElement new constraintsDo: [ :c | 
	c horizontal fitContent "matchParent" .
	c vertical fitContent "matchParent"
]; "clipChildren: false ;"
background: BlTransparentBackground new;
layout: BlLinearLayout horizontal .				

usableAssertions do: [ :eaaa | 

	aEventListener := MmListUsableEventListener new gameController: controller  .
	elx := eaaa elementForStartingList addEventHandler: aEventListener .
	ppx addChild: elx .
	
	"aPager addPage: (BrPagerPageElementMM new"
		"weight: 0.5;"
		"layout: BlLinearLayout vertical ;"
		"background: (Color random);"
		"mm: ea controller: controller ). "
].



spane := BrScrollPane new
		look: MmScrollPaneLook + MmScrollbarLook .
		
self halt.
	spane content: ppx .
	
^ spane
]

{ #category : #accessing }
MmMainBoard >> createWorkingOnList [

"workingOnList := BrSimpleList new.
workingOnList stencil: [ :each :index | each assertionAndEssentialHypothesisElement: controller .].
workingOnList hFitContent ."

| mmodel look |
workingOnList := BlElement new constraintsDo: [ :c | 
	c horizontal "matchParent" fitContent  .
	c vertical "matchParent"  fitContent
]; clipChildren: false ;
background: BlTransparentBackground new;
layout: BlLinearLayout vertical .

aPannableElement := BlPannableElement new clipChildren: false .
aPannableElement constraintsDo: [ :c | 
	c horizontal "matchParent" fitContent  .
	c vertical "matchParent"  fitContent
].
	aPannableElement contentElement: workingOnList.

"aPannableElement constraintsDo: [ :c|
			c frame horizontal alignRight . ] ."
		
		

	mmodel := BrWithContextMenuModel new
		stencil: [ BlElement new
				look:
					(BrGlamorousContextMenuLook new
						content:
							(BrGlamorousSimpleContextMenuContent new
								items:
{
('zoom in'  -> [ :e | aPannableElement zoomIn ]).
									
('zoom out' -> [ :e | aPannableElement zoomOut ]).

('inspect self' -> [ :e | self inspect	"e background: Color green" ])
};

								yourself);
						yourself);
				yourself ];
		yourself.


	look := BrWithContextMenuLook new.

	aPannableElement viewModel: mmodel.
	aPannableElement look: look .

^ aPannableElement

]

{ #category : #initialization }
MmMainBoard >> initialize [ 

super initialize .

self constraintsDo: [ :c | 
	c horizontal matchParent .
	c vertical matchParent ].

self layout: BlFrameLayout new .

"self layout: BlLinearLayout vertical ."

"sc := BlScrollableElement new .
sc addChild: middleThings .
sc constraintsDo: [ :c | 
	c horizontal matchParent  .
	c vertical matchParent ].

mainWorkspace addChild:  sc ."

]

{ #category : #'opening/closing' }
MmMainBoard >> openInWindow: anElement [ 
	| aSpace |
	aSpace := BlSpace new
		extent: 400@600;
		title: 'mm'.
	
	"aSpace root background: Color darkGray ."
	aSpace root addChild: anElement.

	aSpace show
]

{ #category : #'instance creation' }
MmMainBoard >> openOn: aProofModel [ 

|  aEventListener el |

proofToDo := aProofModel copy "AndClean" setAllVariablesToFixed .
"proofToDo setEhypothsAsCompleted ."


self background: "BlTransparentBackground new" Color veryVeryDarkGray .

controller := MmGameController new  board: self .


"proofSpace := BlElement  new constraintsDo: [ :c | 
	c horizontal matchParent  .
	c vertical fitContent
];
background: Color veryVeryDarkGray ;
layout: BlLinearLayout vertical ."


mainWorkspace := BlElement  new constraintsDo: [ :c | 
	c horizontal "matchParent" fitContent .
	c vertical fitContent 
]; "clipChildren: false ;"
background: BlTransparentBackground new "Color veryVeryDarkGray" ;
layout: BlLinearLayout vertical alignCenter .



"mainWorkspace constraintsDo: [ :c |
		c frame horizontal alignCenter.
]."









"addEventHandler: BlPullHandler new allowOutOfBounds" .


el := BlElement new constraintsDo: [ :c | 
	c horizontal fitContent .
	c vertical fitContent  ].

el layout: BlLinearLayout vertical "alignCenter" .
el clipChildren: false .

proofToDo eHypoths do: [ :ea | | eee |
	
	"ea setCompleted ."
	eee := MmOnBoardEssentialHypothesisElement new model: ea .
	
	aEventListener := MmOnBoardHypothEventListener new gameController: controller .
	eee addEventHandler: aEventListener .
	
	el addChild: eee .
	
] .

"el constraintsDo: [ :c |

		c frame horizontal alignLeft.
		c frame vertical alignTop .
]."

"currentlySelectedElement addChildFirst: el ."


"proofSpace  addChild: el ."


aEventListener := MmProofResultListener new gameController: controller .

currentlySelectedElement := (MmWantedResultElement new initializeWith: proofToDo)  addEventHandler: aEventListener .

"currentlySelectedElement constraintsDo: [ :c |
		c linear horizontal alignRight.
]."


mainWorkspace addChild: currentlySelectedElement .

"proofSpace  addChild: currentlySelectedElement ."




"self addChild: mainWorkspace asScalableElement ."

"self addChild: proofSpace asScalableElement."

"mainWorkspace addChild: proofSpace ."

self addUsable .

self addChild: mainWorkspace asScalableElement.

self addOnBoardUsableEHypoths .

"self addEventHandler: MmBoardListener new  ."



"	aSpace := BlSpace new
		extent: 1400@800;
		title: proofToDo name .
	aSpace root addChild: self .
	aSpace show."


]

{ #category : #setup }
MmMainBoard >> setupForProving: aProofModel [

| mmodel look aEventListener el |

proofToDo := aProofModel copyAndClean setAllVariablesToFixed .

self background: Color veryVeryDarkGray .


"workingOnList := BlElement new constraintsDo: [ :c | 
	c horizontal fitContent .
	c vertical fitContent
]; 
background: BlTransparentBackground new;
layout: BlLinearLayout vertical .

aPannableElement := workingOnList asPannableElement clipChildren: false.

aPannableElement constraintsDo: [ :c | 
	c horizontal  fitContent  .
	c vertical   fitContent
]."


	"mmodel := BrWithContextMenuModel new
		stencil: [ BlElement new
				look:
					(BrGlamorousContextMenuLook new
						content:
							(BrGlamorousSimpleContextMenuContent new
								items:
{
('zoom in'  -> [ :e | aPannableElement zoomIn ]).
									
('zoom out' -> [ :e | aPannableElement zoomOut ]).

('inspect self' -> [ :e | self inspect ])
};

								yourself);
						yourself);
				yourself ];
		yourself.


	look := BrWithContextMenuLook new.

	self viewModel: mmodel.
	self look: look ."


"xx look:  BrGlamorousWithVerticalResizerLook + BrGlamorousWithHorizontalResizerLook."

"self addChild: aPannableElement."

mainWorkspace := BlElement  new constraintsDo: [ :c | 
	c horizontal fitContent  .
	c vertical fitContent 
]; clipChildren: false ;
background: Color veryVeryDarkGray ;
layout: BlLinearLayout vertical .

mainWorkspace constraintsDo: [ :c |
		c frame horizontal alignCenter.
		c frame vertical alignCenter ].

"mainWorkspace addChild: topBoard ."

self addChild: mainWorkspace "asScalableElement" .

"self addUsableThingsLists."



"usableTurnstiles := proofToDo eHypoths . 
usableWFFs := OrderedCollection new."

proofToDo assertionsUsed reverseDo: [ :each | | thing |
	
	thing := proofToDo prevAssertions at: each .

	thing body isWFF ifTrue: [
			

	] ifFalse: [ 
	

"self addToList: usable ."

"workingOnList" 

			mainWorkspace addChild: (thing copyAndClean  assertionAndEssentialHypothesisElement: controller) .	
	
		"thing setAllVariablesToFree.
		usableTurnstiles add: thing ."	
				
	]. 
] .





aEventListener := MmListUsableEventListener new gameController: controller  .
"el := proofToDo eHypoths first elementForStartingList addEventHandler: aEventListener ."

"el := BrVerticalPane new ."
el := BlElement new constraintsDo: [ :c | 
	c horizontal fitContent .
	c vertical fitContent  ].

el layout: BlLinearLayout vertical alignCenter .
el clipChildren: false .

"proofToDo eHypoths do: [ :ea | el addChild: (ea elementForStartingList addEventHandler: aEventListener ) ] ."

proofToDo eHypoths do: [ :ea | el addChild: (ea  assertionAndEssentialHypothesisElement: controller ) ] .

el constraintsDo: [ :c |

		c frame horizontal alignLeft.
		c frame vertical alignTop .
			"c horizontal fitContent .
	c vertical fitContent"
].



"middleThings := BlElement new constraintsDo: [ :c | 
	c horizontal fitContent .
	c vertical fitContent  ].

middleThings layout: BlLinearLayout vertical alignCenter .

mainWorkspace addChild: middleThings asPannableElement ."


aEventListener := MmProofResultListener new gameController: controller .

"currentlySelectedElement := proofToDo onBoardGameElement addEventHandler: aEventListener ."

currentlySelectedElement := (MmEssentialHypothesisElement new initializeWith: proofToDo)  addEventHandler: aEventListener .

currentlySelectedElement constraintsDo: [ :c |

		c frame horizontal alignRight.
		c frame vertical alignTop.
].


"mainWorkspace addChild: currentlySelectedElement"  "addEventHandler: BlPullHandler new allowOutOfBounds" .

self  addChild: currentlySelectedElement .

self addChild: el .

	"parent := self parentWithFrameLayoutAndFixedSize.	
	parent size: 300@300.
	parent addChild: child.
	
	parent forceLayout."

]

{ #category : #setup }
MmMainBoard >> setupForProvingx: aProofModel [

| aEventListener xx mmodel look anAccordion |
proofToDo := aProofModel copyAndClean setAllVariablesToFixed .

self background: Color white .

workingOnList := BlElement new constraintsDo: [ :c | 
	c horizontal fitContent .
	c vertical fitContent
]; 
background: BlTransparentBackground new;
layout: BlLinearLayout vertical .

aPannableElement := workingOnList asPannableElement clipChildren: false.

aPannableElement constraintsDo: [ :c | 
	c horizontal  fitContent  .
	c vertical   fitContent
].

"clipChildren: false ;"

	mmodel := BrWithContextMenuModel new
		stencil: [ BlElement new
				look:
					(BrGlamorousContextMenuLook new
						content:
							(BrGlamorousSimpleContextMenuContent new
								items:
{
('zoom in'  -> [ :e | aPannableElement zoomIn ]).
									
('zoom out' -> [ :e | aPannableElement zoomOut ]).

('inspect self' -> [ :e | self inspect	"e background: Color green" ])
};

								yourself);
						yourself);
				yourself ];
		yourself.


	look := BrWithContextMenuLook new.

	self viewModel: mmodel.
	self look: look .


"xx look:  BrGlamorousWithVerticalResizerLook + BrGlamorousWithHorizontalResizerLook."

self addChild: aPannableElement.

self addUsableThingsLists.



"mainWorkspace := BlElement  new constraintsDo: [ :c | 
	c horizontal matchParent  .
	c vertical matchParent 
];
background: Color veryVeryDarkGray ;
layout: BlLinearLayout vertical ."

"mainWorkspace addChild: topBoard .

self addChild: mainWorkspace ."

"middleThings := BlElement new constraintsDo: [ :c | 
	c horizontal fitContent .
	c vertical fitContent  ].

middleThings layout: BlLinearLayout vertical alignCenter .

mainWorkspace addChild: middleThings asPannableElement ."

aEventListener := MmProofResultListener new gameController: controller .
currentlySelectedElement := proofToDo onBoardGameElement addEventHandler: aEventListener .
"currentlySelectedElement constraintsDo: [ :c | 
c frame horizontal alignRight.
	  ] ."
currentlySelectedElement controller: controller . currentlySelectedElement background: Color white .

workingOnList  addChild: currentlySelectedElement .

"aPannableElement translateBy: 600@400 ."
aPannableElement transform
		"inherit;"
		origin: (BlAffineTransformationPositionOrigin position: 0@0);
		translateBy: (BlVector x: 200 y: 400 z: 0);
		apply .
		
"self halt ."
aEventListener := MmBoardListener new  .
self addEventHandler: aEventListener .

]
