Class {
	#name : #MmSetVizSymbol,
	#superclass : #Object,
	#instVars : [
		'symbol'
	],
	#classVars : [
		'Mon'
	],
	#category : #'Metamath-experiment'
}

{ #category : #accessing }
MmSetVizSymbol >> = ax [
^ symbol = ax symbol
]

{ #category : #accessing }
MmSetVizSymbol >> asBlElement [
| aText textElement |
	aText := symbol asRopedText .

aText fontSize: 20.
"aText foreground: col ."

textElement := (BlTextElement text: aText) constraintsDo: [ :c | c linear vertical  alignCenter ].
textElement margin: (BlInsets all: 4).
^ textElement
]

{ #category : #accessing }
MmSetVizSymbol >> draw [ 
Mon topStep addChildren: { self el }.
]

{ #category : #accessing }
MmSetVizSymbol >> el [
| aText textElement |
	aText := symbol asRopedText .

aText fontSize: 18.
"aText foreground: col ."

textElement := (BlTextElement text: aText) constraintsDo: [ :c | c linear vertical  alignCenter ].
textElement margin: (BlInsets all: 2).
^ textElement
]

{ #category : #accessing }
MmSetVizSymbol >> hash [
^ symbol hash
]

{ #category : #accessing }
MmSetVizSymbol >> printOn: aStream [
	aStream nextPutAll: symbol printString .
]

{ #category : #accessing }
MmSetVizSymbol >> symbol [
^ symbol
]

{ #category : #accessing }
MmSetVizSymbol >> with: x [
symbol := x
]
