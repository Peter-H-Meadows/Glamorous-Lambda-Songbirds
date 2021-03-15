Class {
	#name : #MmCurlyBracesElement,
	#superclass : #MmAbstractBrackets,
	#category : #'Metamath-Bloc'
}

{ #category : #accessing }
MmCurlyBracesElement >> initialize [

super initialize .

self padding: (BlInsets all: 20).

self border: (BlBorder paint: Color blue width: 2 ).

]

{ #category : #initialization }
MmCurlyBracesElement >> initializeWith: bracket [ 

model := bracket .

"model announcer when: MmHighlightAnnouncement send: #highlight to: self .
model announcer when: MmFailedToMapAnnouncement send: #failedToMap: to: self.
"
"bracket body do: [ :ea | self addChild: ea gameElement  ]."


self addChild: model body gameElement
]
