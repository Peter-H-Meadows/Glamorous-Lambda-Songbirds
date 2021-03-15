"
show ehypoths in box and proof on right.
"
Class {
	#name : #AssertionAndEssentialHypothesisElement,
	#superclass : #MmAbstractThingElement,
	#instVars : [
		'hypothBox',
		'resultElement',
		'anAccordion'
	],
	#category : #'Metamath-Bloc'
}

{ #category : #'as yet unclassified' }
AssertionAndEssentialHypothesisElement class >> onModel: assertion [ 


]

{ #category : #accessing }
AssertionAndEssentialHypothesisElement >> addHandlersController: con [

| aEventListener |
aEventListener := MmOnBoardWantedEventListener new gameController: con .

hypothBox childrenDo: [ :el | el controller: con . el addEventHandler: aEventListener . ].

aEventListener := MmOnBoardUsableEventListener new gameController: con .
self addEventHandler: aEventListener .



]

{ #category : #adding }
AssertionAndEssentialHypothesisElement >> addHypoths [

model eHypoths reverse do: [ :ea | 
	
	hypothBox addChild: (ea gameElementInCont: controller  pmod: model )  .
	
] .
]

{ #category : #accessing }
AssertionAndEssentialHypothesisElement >> addMenu [

| menuModel |
	menuModel := BrWithContextMenuModel new
		stencil: [ BrAnchoredElement new
				look:
					(BrGlamorousContextMenuLook new
						content:
							(BrGlamorousSimpleContextMenuContent new
								items:
									{
									('model inspect' -> [ :e | model inspect ]).
									('free' -> [ :e | model setAllVariablesToFixed   ]).
									('color' -> [ :e | model reColor   ]).
									('bg' -> [ :e | e background: Color red   ]).
									('inspect vars' -> [ :e | model allVariables inspect ]).
									
(model name printString  -> [ :e | MmGame new openGame: model name. ]).
									
('browse' -> [ :e | MmGame new openGame: model  name ]).
									
									"('aaa' -> [ :e | " 
									
									"model fHypoths reverse do: [ :ea | | el |
	
	el := MmFloatingHypothesisElement new initializeWith: ea  .

	el constraintsDo: [ :co |
			co horizontal matchParent ];
		background: BlTransparentBackground new .
	
	hypothBox addChild: el" 
	"] ."
									"])."
									
									
									};
								yourself);
						yourself);
				yourself ];
		yourself.
		
	
self viewModel: menuModel .

self look: BrWithContextMenuLook new.
]

{ #category : #accessing }
AssertionAndEssentialHypothesisElement >> all [ 
^ self 
]

{ #category : #highlighting }
AssertionAndEssentialHypothesisElement >> highlightAsSelected [
selectedMarkerElement background: Color gray .
selected := true 
]

{ #category : #accessing }
AssertionAndEssentialHypothesisElement >> initialize [ 

| menuModel |
super initialize .

"self border: (BlBorder paint: Color gray width: 2 ) ."

hypothBox := BlElement new layout: BlLinearLayout  vertical .

self padding: (BlInsets all: 4).
self margin: (BlInsets all: 4).

hypothBox constraintsDo: [ :c | 
					c horizontal fitContent.
					c vertical fitContent ].

"anAccordion := BrAccordion new.
	anAccordion hMatchParent; vFitContent.

	anAccordion look: BrGlamorousAccordionLook new.

	anAccordion content: [
		hypothBox
	].
	
									
self addChild: anAccordion ."

self addChild: hypothBox


]

{ #category : #accessing }
AssertionAndEssentialHypothesisElement >> initializeWith: assertion [

| el divElement |

model := assertion .

self addMenu.
"model fHypoths reverse do: [ :ea | 
	
	el := MmFloatingHypothesisElement new initializeWith: ea  .

	el constraintsDo: [ :co |
			co horizontal matchParent ];
		background: BlTransparentBackground new .
	
	hypothBox addChild: el .
	
] ."

model eHypoths reverse do: [ :ea | 
	
	el := MmEssentialHypothesisElement new initializeWith: ea  .

	el constraintsDo: [ :co |
			co horizontal matchParent ];
		background: BlTransparentBackground new .
	
	hypothBox addChild: el  "(ea gameElementInCont: con pmod: model )"  .
	
] .

divElement := BlElement new
		constraintsDo: [ :co |
			co horizontal exact: 1.
			co vertical matchParent ];
		background: Color veryDarkGray .

self addChild: divElement.

resultElement := assertion gameElement constraintsDo: [ :c | c linear vertical alignCenter ] .
"aEventListener := MmOnBoardUsableEventListener new gameController: con .
self addEventHandler: aEventListener ."
self addChild: resultElement.

selectedMarkerElement := BlElement new
		constraintsDo: [ :co |
			co horizontal exact: 4.
			co vertical matchParent ];
		background: BlTransparentBackground new.

self addChild: selectedMarkerElement.

"anAccordion toggle."

	"anAccordion header: [
		BrButton new
			look: BrGlamorousAccordionHeaderLook new;
			label: model name printString;
			action: [ anAccordion toggle ] ].
			
	anAccordion expand."
	
	"self halt ."
]

{ #category : #accessing }
AssertionAndEssentialHypothesisElement >> model: assertion [ 

"add ehypoths to left container"

| mand  el |

self error .

model := assertion .

el := assertion gameElement constraintsDo: [ :c | c linear vertical  alignCenter ] .

model eHypoths reverse do: [ :ea | 
	
	mand := ea gameElement .
	
	mand constraintsDo: [ :c | c linear horizontal  alignCenter ].
	
	hypothBox addChild: mand
	
] .

self addChild: el.
]

{ #category : #accessing }
AssertionAndEssentialHypothesisElement >> model: assertion controller2: con [

"add ehypoths to left container"

| el |

model := assertion .

controller := con .

model eHypoths reverse do: [ :ea | 
	
	"aEventListener := MmOnBoardWantedEventListener new gameController: controller .
	mand := ea gameElement addEventHandler: aEventListener .
	mand constraintsDo: [ :c | c linear horizontal  alignCenter ].
	cont addChild: mand"
	
	hypothBox addChild: (ea gameElementInCont: con pmod: model )  .
	
] .

el := assertion gameElement constraintsDo: [ :cc | cc linear vertical  alignCenter ] .
"aEventListener := MmOnBoardUsableEventListener new gameController: con ."
"self addEventHandler: aEventListener ."
self addChild: el.

selectedMarkerElement := BlElement new
		constraintsDo: [ :co |
			co horizontal exact: 8.
			co vertical matchParent ];
		background: ( Color veryDarkGray  ).


self addChild: selectedMarkerElement


]

{ #category : #accessing }
AssertionAndEssentialHypothesisElement >> model: assertion controller: con [

| el aEventListener erElement |

self error .

model := assertion .

controller := con .

model eHypoths reverse do: [ :ea | 
	
	hypothBox addChild: (ea gameElementInCont: con pmod: model )  .
	
] .

erElement := BlElement new
		constraintsDo: [ :co |
			co horizontal exact: 1.
			co vertical matchParent ];
		background: Color veryDarkGray .

self addChild: erElement.

el := assertion gameElement constraintsDo: [ :cc | cc linear vertical  alignCenter ] .
aEventListener := MmOnBoardUsableEventListener new gameController: con .
self addEventHandler: aEventListener .
self addChild: el.

selectedMarkerElement := BlElement new
		constraintsDo: [ :co |
			co horizontal exact: 8.
			co vertical matchParent ];
		background: BlTransparentBackground new.

self addChild: selectedMarkerElement.

]
