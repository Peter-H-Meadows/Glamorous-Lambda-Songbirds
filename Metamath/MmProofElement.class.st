Class {
	#name : #MmProofElement,
	#superclass : #MmAssertionElement,
	#instVars : [
		'proof'
	],
	#category : #'Metamath-Bloc'
}

{ #category : #'instance creation' }
MmProofElement class >> on: aProof [
	^ self new initializeWithProof: aProof
]

{ #category : #accessing }
MmProofElement >> highlightAsSelected [ 

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
MmProofElement >> initializeWithProof: aAssertion [

| aText el box comment |

self model: aAssertion .

"aText := aAssertion name asRopedText .
aText fontSize: 18.
aText foreground: Color white   .
textElement := (BlTextElement text: aText) .
self addChild: textElement ."


box := BlElement new layout: BlLinearLayout vertical .

"
self padding: (BlInsets all: 4).
self margin: (BlInsets all: 4)."

box constraintsDo: [ :c | 
					c horizontal fitContent.
					c vertical fitContent ].


el := aAssertion body gameElement . 
el constraintsDo: [ :c | c linear horizontal alignCenter ].

box addChild: el .

"comment := MmCommentElement new createFromString: aAssertion lastComment body .
box addChild: comment ."
self addChild: box .



]

{ #category : #accessing }
MmProofElement >> model: m [

model := m .

model announcer when: MmHighlightAnnouncement send: #highlight to: self.

model announcer when: MmFailedToMapAnnouncement send: #failedToMap: to: self.

model announcer when: MmCanMapAnnouncement send: #canMap: to: self.
]
