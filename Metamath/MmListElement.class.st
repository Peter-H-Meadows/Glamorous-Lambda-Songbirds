Class {
	#name : #MmListElement,
	#superclass : #MmRawElement,
	#category : #'Metamath-Bloc'
}

{ #category : #accessing }
MmListElement >> initialize [

super initialize .

self geometry: BlEllipseGeometry new.

self padding: (BlInsets all: 20).

self border: (BlBorder paint: Color darkGray   width: 1 ).
]

{ #category : #initialization }
MmListElement >> initializeWith: aModel [ 

model := aModel .

"model announcer when: MmHighlightAnnouncement send: #highlight to: self .
model announcer when: MmFailedToMapAnnouncement send: #failedToMap: to: self."

"model body do: [ :ea | self addChild: ea gameElement  ]."

self addChild: model first gameElement.

self addChild: model second  gameElement.
]
