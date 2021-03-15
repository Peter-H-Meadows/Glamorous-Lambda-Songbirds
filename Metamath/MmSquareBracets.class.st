"
used for substitution
"
Class {
	#name : #MmSquareBracets,
	#superclass : #MmAbstractBrackets,
	#category : #'Metamath-Bloc'
}

{ #category : #accessing }
MmSquareBracets >> initialize [

super initialize .

self padding: (BlInsets all: 20).

self border: (BlBorder paint: Color yellow width: 2 ).

]

{ #category : #accessing }
MmSquareBracets >> initializeWith: bracket [ 

model := bracket .

"model announcer when: MmHighlightAnnouncement send: #highlight to: self .
model announcer when: MmFailedToMapAnnouncement send: #failedToMap: to: self."

"bracket body do: [ :ea | self addChild: ea gameElement  ]."


self addChild: model body gameElement
]
