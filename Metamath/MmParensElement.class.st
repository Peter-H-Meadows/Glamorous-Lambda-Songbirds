"
( )
"
Class {
	#name : #MmParensElement,
	#superclass : #MmAbstractBrackets,
	#category : #'Metamath-Bloc'
}

{ #category : #'instance creation' }
MmParensElement class >> on: aParen [
	^ self new initializeWithParen: aParen
]

{ #category : #accessing }
MmParensElement >> borderColor [ 

^ Color darkGray  
]

{ #category : #accessing }
MmParensElement >> borderWidth [

^ 0
]

{ #category : #'as yet unclassified' }
MmParensElement >> failedToMap: ann [ 

self hi: Color red
]

{ #category : #accessing }
MmParensElement >> highlight [ 

self background: Color darkGray .

HighlightedElements add: self .


]

{ #category : #initialization }
MmParensElement >> initialize [

super initialize .

self geometry: BlEllipseGeometry new.

self padding: (BlInsets all: 20).

self border: (BlBorder paint: self borderColor width: 1 ).

]

{ #category : #initialization }
MmParensElement >> initializeWith: bracket [ 

model := bracket .

"model announcer when: MmHighlightAnnouncement send: #highlight to: self .
model announcer when: MmFailedToMapAnnouncement send: #failedToMap: to: self."

"bracket body do: [ :ea | self addChild: ea gameElement  ]."

self addChild: model body gameElement
]

{ #category : #initialization }
MmParensElement >> initializeWithParen: aParen [

self error .

model := aParen .

model announcer when: MmHighlightAnnouncement send: #highlight to: self .

model announcer when: MmFailedToMapAnnouncement send: #failedToMap: to: self.


aParen body do: [ :ea | self addChild: ea gameElement  ].

"self addChild: aParen left gameElement .

self addChild: aParen right gameElement ."
]

{ #category : #accessing }
MmParensElement >> unHighlight [ 

self background: Color veryVeryDarkGray .


]
