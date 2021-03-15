Class {
	#name : #MmAbstractThingElement,
	#superclass : #MmRawElement,
	#instVars : [
		'textElement',
		'controller',
		'selected'
	],
	#category : #'Metamath-Bloc'
}

{ #category : #accessing }
MmAbstractThingElement >> body: b [

self addChild: b
]

{ #category : #accessing }
MmAbstractThingElement >> borderWidth [ 

^ 0
]

{ #category : #emulating }
MmAbstractThingElement >> clicked [ 

selected := selected not .

selected ifTrue: [ self highlightAsSelected ] ifFalse: [ self unhighlightAsSelected ]
]

{ #category : #accessing }
MmAbstractThingElement >> controller: c [
controller := c
]

{ #category : #accessing }
MmAbstractThingElement >> highlightAsSelected [ 
 
selectedMarkerElement background: Color gray .
selected := true 
]

{ #category : #accessing }
MmAbstractThingElement >> initialize [
"| mmodel look |"
super initialize .

selected := false .

selectedMarkerElement := BlElement new
		constraintsDo: [ :c |
			c horizontal exact: 4.
			c vertical matchParent ];
		background: BlTransparentBackground new.

self geometry: BlRectangle new .

"self background: Color veryVeryDarkGray ."

self padding: (BlInsets all: 4).

"self margin: (BlInsets top: 10 bottom: 10)"




	"mmodel := BrWithContextMenuModel new
		stencil: [ BlElement new
				look:
					(BrGlamorousContextMenuLook new
						content:
							(BrGlamorousSimpleContextMenuContent new
								items:
{
(model name  -> [ :e | MmGame new openGame: model name. ]).
									
('green' -> [ :e | e background: Color green ]).

('inspect self' -> [ :e | self inspect ])
};

								yourself);
						yourself);
				yourself ];
		yourself.
		
	look := BrWithContextMenuLook new."

	"self viewModel: mmodel.
	self look: look"
]

{ #category : #testing }
MmAbstractThingElement >> isSelected [ 
^ selected 
]

{ #category : #accessing }
MmAbstractThingElement >> markFail [
| aText |
"textElement removeFromParent ."

aText := 'no  ' asRopedText .
aText fontSize: 30.
aText foreground: Color red .
textElement := (BlTextElement text: aText) constraintsDo: [ :c |c linear vertical alignCenter ].
self addChildFirst: textElement .

self requestParentLayout .
]

{ #category : #accessing }
MmAbstractThingElement >> markSuccess [
| aText |
"textElement removeFromParent ."

"aText := 'ok  ' asRopedText .
aText fontSize: 30.
aText foreground: Color green .
textElement := (BlTextElement text: aText) constraintsDo: [ :c |c linear vertical alignCenter ].
self addChildFirst: textElement .

self requestParentLayout ."
]

{ #category : #accessing }
MmAbstractThingElement >> name: n [

| aText |
aText := n asRopedText .

aText fontSize: 30.
aText foreground: Color veryLightGray .

textElement := (BlTextElement text: aText) constraintsDo: [ :c | 
					"c horizontal fitContent.
					c vertical fitContent . "
					c linear vertical alignCenter ].

"self addChild: textElement ."
]

{ #category : #removing }
MmAbstractThingElement >> remove [ 

self graph nodesAlongOutgoingEdges do: #remove .

self removeFromParent 
]

{ #category : #'as yet unclassified' }
MmAbstractThingElement >> toggleSelected [ 

selectedMarkerElement ifNil: [ self highlightAsSelected . ^ true ] ifNotNil: [ 
	
	self unhighlightAsSelected .
	^ false
	
 ]
]

{ #category : #'api - highlighting' }
MmAbstractThingElement >> unhighlightAsSelected [  
 
selectedMarkerElement background: BlTransparentBackground new .
selected := false 

]
