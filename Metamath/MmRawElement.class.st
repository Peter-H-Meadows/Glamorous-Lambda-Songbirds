Class {
	#name : #MmRawElement,
	#superclass : #BlElement,
	#instVars : [
		'model',
		'boardElement',
		'selectedMarkerElement'
	],
	#category : #'Metamath-Bloc'
}

{ #category : #'instance creation' }
MmRawElement class >> on: foo [ 

^ self new initalizeWith: foo
]

{ #category : #adding }
MmRawElement >> addEdgeTo: anElement [ 

| edge |


edge := GtGraphEdge connecting: self to: anElement .
self constraints graph addConnectedEdge: edge.
anElement constraints graph addConnectedEdge: edge.
]

{ #category : #adding }
MmRawElement >> addStartingBracket [

"| aText textElement |
aText := '{ ' asRopedText.
aText fontSize: 20.
aText foreground: Color gray .
textElement := (BlTextElement text: aText) constraintsDo: [ :c | c linear vertical alignCenter ]."

| startBracketElement |
startBracketElement := BlElement new
		constraintsDo: [ :c |
			c horizontal exact: 8.
			c vertical matchParent ];
		background: ( Color blue muchDarker ).

self addChildFirst: startBracketElement .
]

{ #category : #accessing }
MmRawElement >> backgroundColor [

^ Color veryVeryDarkGray
]

{ #category : #accessing }
MmRawElement >> backgroundPaint [

^ Color lightGray
]

{ #category : #'setter as yet unclassified' }
MmRawElement >> boardElement: aMmGameMainElement [ 
	boardElement := aMmGameMainElement 
]

{ #category : #accessing }
MmRawElement >> borderColor [

^ Color veryVeryDarkGray
]

{ #category : #accessing }
MmRawElement >> borderWidth [ 

^ 0
]

{ #category : #'api - accessing' }
MmRawElement >> currentTarget [ 
^ self
]

{ #category : #'as yet unclassified' }
MmRawElement >> failedToMap: ann [ 

self background: Color red .
]

{ #category : #accessing }
MmRawElement >> hi: col [

self border: (BlBorder paint: col width: 4 )
]

{ #category : #accessing }
MmRawElement >> highlight [ 

self border: (BlBorder paint: self borderColor width: 4 )
]

{ #category : #accessing }
MmRawElement >> initialize [

super initialize .


		
		self background: BlTransparentBackground new "self backgroundColor" ;
		"border: (BlBorder paint: self borderColor width: self borderWidth );"
		constraintsDo: [ :c | 
					c horizontal fitContent.
					c vertical fitContent .
					c linear vertical alignCenter ];
		"padding: (BlInsets all: 0);
		margin: (BlInsets all: 0);"
		layout: BlLinearLayout horizontal  .
]

{ #category : #'as yet unclassified' }
MmRawElement >> lineElementFrom: aSourceElement to: aTargetElement [

	| aLineElement |
	aLineElement := BlParabollaArcElement new.
	aLineElement curvatureFraction: 0.2.
	aLineElement zIndex: 10.
	aLineElement toHead: (BlArrowheadSimpleArrow new
					border: (BlBorder builder paint: (Color gray alpha: 0.2); width: 5; build)).
	aLineElement constraints ignoreByLayout.
	aLineElement
		border: (BlBorder paint: (Color red alpha: 0.8) width: 5);
		fromAnchor: (BlElementBottomCenterAnchor element: aSourceElement);
		toAnchor: (BlElementTopCenterAnchor  element: aTargetElement).
		
	^ aLineElement
]

{ #category : #accessing }
MmRawElement >> model [

^ model
]

{ #category : #accessing }
MmRawElement >> model: m [

model := m .

model announcer when: MmHighlightAnnouncement send: #highlight to: self.

model announcer when: MmFailedToMapAnnouncement send: #failedToMap: to: self.

model announcer when: MmCanMapAnnouncement send: #canMap: to: self.
]

{ #category : #'instance creation' }
MmRawElement >> success [ 

self hi: Color green
]

{ #category : #'api - highlighting' }
MmRawElement >> unhighlightAsSelected [  
 
selectedMarkerElement background: BlTransparentBackground new .
 


]
