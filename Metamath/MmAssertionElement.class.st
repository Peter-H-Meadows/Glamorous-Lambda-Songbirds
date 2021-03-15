Class {
	#name : #MmAssertionElement,
	#superclass : #MmAbstractThingElement,
	#instVars : [
		'hypothBox'
	],
	#category : #'Metamath-Bloc'
}

{ #category : #'instance creation' }
MmAssertionElement class >> on: a [
	^ self new initializeWith: a
]

{ #category : #accessing }
MmAssertionElement >> all [ 
^ self parent 
]

{ #category : #initialization }
MmAssertionElement >> body: b [

self addChild: b
]

{ #category : #accessing }
MmAssertionElement >> borderColor [

^ Color veryVeryDarkGray  
]

{ #category : #testing }
MmAssertionElement >> canMap: ann [

self markSuccess 
]

{ #category : #'as yet unclassified' }
MmAssertionElement >> failedToMap: ann [ 

"self background: Color red ."
"textElement removeFromParent ."

| aText |
aText := ' fail ' asRopedText .
aText fontSize: 30.
aText foreground: Color red .
textElement := (BlTextElement text: aText) constraintsDo: [ :c |c linear vertical alignCenter ].
self addChild: textElement .


"| aText textElement |
aText := ann reason asRopedText .

aText fontSize: 18.
aText foreground: Color red .

textElement := (BlTextElement text: aText) constraintsDo: [ :c | 
					c linear vertical alignCenter ].

self addChild: textElement ."
]

{ #category : #accessing }
MmAssertionElement >> forUsing [
^ self parent removeFromParent 
]

{ #category : #accessing }
MmAssertionElement >> hi: f [
| aText |
"textElement removeFromParent ."

aText := ' done ' asRopedText .
aText fontSize: 30.
aText foreground: Color green .
textElement := (BlTextElement text: aText) constraintsDo: [ :c |c linear vertical alignCenter ].
self addChildFirst: textElement .

self requestParentLayout .
]

{ #category : #accessing }
MmAssertionElement >> highlight [ 

self border: (BlBorder paint: self borderColor width: 4 )
]

{ #category : #accessing }
MmAssertionElement >> highlightAsSelected [ 

"self background: self backgroundColor lighter ."

"self border: (BlBorder paint: Color gray width: 6 )."

| aText |
aText := ':' asRopedText.
aText fontSize: 50.
aText foreground: Color white .
selectedMarkerElement := (BlTextElement text: aText) constraintsDo: [ :c | c linear vertical alignCenter ].

self addChild: selectedMarkerElement 
]

{ #category : #initialization }
MmAssertionElement >> initialize [
	| mmodel look |
	super initialize.
	"self border: (BlBorder paint: Color gray width: 2)."
	hypothBox := BlElement new layout: BlLinearLayout vertical.
	self padding: (BlInsets all: 4).
	self margin: (BlInsets all: 4).
	hypothBox
		constraintsDo: [ :c | 
			c horizontal fitContent.
			c vertical fitContent ].
	self addChild: hypothBox.

	"self layout: BlLinearLayout vertical ."

	"self margin: (BlInsets all: 10) ."

	"self padding: (BlInsets all: 20) ."
	

]

{ #category : #initialization }
MmAssertionElement >> initializeOld [

| mmodel look |
super initialize .

	mmodel := BrWithContextMenuModel new
		stencil: [ BlElement new
				look:
					(BrGlamorousContextMenuLook new
						content:
							(BrGlamorousSimpleContextMenuContent new
								display:
									{
									
									('remove' -> [ :e | "self halt ." "model remove" "gameModel tryUse: self" ]).
									('remove' -> [ :e | e removeFromParent ]).
									('inspect copy' -> [ :e | self copy inspect "e background: Color green" ])
									
									
									};
								yourself);
						yourself);
				yourself ];
		yourself.
	self assert: mmodel visible equals: false.
	
	look := BrWithContextMenuLook new.
	self assert: look visible equals: false.
	self assert: (look stencil asStencil asElement isKindOf: BlElement).
	
	self viewModel: mmodel.
	self look: look.
	
]

{ #category : #initialization }
MmAssertionElement >> initializeWith: aAssertion [
| aText el mmodel look |

model := aAssertion .

model announcer when: MmHighlightAnnouncement send: #highlight to: self.

model announcer when: MmFailedToMapAnnouncement send: #failedToMap: to: self.

model announcer when: MmCanMapAnnouncement send: #canMap: to: self.

"aText := aAssertion name asRopedText .
aText fontSize: 18.
aText foreground: Color gray  .
textElement := (BlTextElement text: aText). 
self addChild: textElement ."

el := aAssertion body gameElement . 
el constraintsDo: [ :c | c linear horizontal alignCenter ].

self addChild: el .
]

{ #category : #accessing }
MmAssertionElement >> model: m [

model := m .

model announcer when: MmHighlightAnnouncement send: #highlight to: self.

model announcer when: MmFailedToMapAnnouncement send: #failedToMap: to: self.

model announcer when: MmCanMapAnnouncement send: #canMap: to: self.
]

{ #category : #initialization }
MmAssertionElement >> name: n [

| aText  |
aText := n asRopedText .

aText fontSize: 30.
aText foreground: Color veryLightGray .

textElement := (BlTextElement text: aText) constraintsDo: [ :c | 
					"c horizontal fitContent.
					c vertical fitContent . "
					c linear vertical alignCenter ].

"self addChild: textElement ."
]

{ #category : #'as yet unclassified' }
MmAssertionElement >> showEssential [

model eHypoths reverse do: [ :ea | 
		
	hypothBox addChild: (ea gameElementInCont: nil "controller")  .
	
] .


]
