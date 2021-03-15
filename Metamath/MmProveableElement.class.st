Class {
	#name : #MmProveableElement,
	#superclass : #MmRawElement,
	#instVars : [
		'body'
	],
	#category : #'Metamath-Bloc'
}

{ #category : #'instance creation' }
MmProveableElement class >> on: aProof [
	^ self new initializeWithProof: aProof
]

{ #category : #initialization }
MmProveableElement >> body: b [

body := b
]

{ #category : #initialization }
MmProveableElement >> initialize [

super initialize .

self geometry: BlRectangle new
]

{ #category : #initialization }
MmProveableElement >> initializeWith: proveableModel [

| aText textElement |

self model: proveableModel . 

"aText := '|- ' asRopedText .
aText fontSize: 18.
aText foreground: Color white   .
textElement := (BlTextElement text: aText) constraintsDo: [ :c | c linear vertical alignCenter ].
self addChild: textElement ."

"proveableModel body do: [ :ea | self addChild: ea gameElement . ]" 

self addChild: proveableModel body gameElement .
]
