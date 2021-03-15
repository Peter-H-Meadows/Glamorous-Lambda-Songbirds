Class {
	#name : #MmNotElement,
	#superclass : #MmRawElement,
	#instVars : [
		'body',
		'name'
	],
	#category : #'Metamath-Bloc'
}

{ #category : #initialization }
MmNotElement >> initializeWith: aModel [ 

| aText textElement col fs content |

model := aModel .

fs := 18 .
 name := 'X'. col := Color red  .

aText := name asRopedText .

aText fontSize: fs.
aText foreground: col .

textElement := (BlTextElement text: aText) constraintsDo: [ :c | c linear vertical  alignCenter ].
textElement margin: (BlInsets all: 4).
self addChild: textElement.
self addChild: model  body gameElement .
]
