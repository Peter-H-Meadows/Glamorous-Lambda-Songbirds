Class {
	#name : #MmConstantElement,
	#superclass : #MmRawElement,
	#instVars : [
		'body',
		'name'
	],
	#category : #'Metamath-Bloc'
}

{ #category : #initialization }
MmConstantElement >> initializeWith: aModel [ 

| aText textElement col fs content |

model := aModel .

col := Color black . 
fs := 18 .

	content := BrLabel new
		"look: (BrGlamorousLabelLook new glamorousRegularFontAndSize);
		padding: (BlInsets all: 20);
		text: '..';"
		alignCenter.
	
	self look: (BrGlamorousWithTooltipLook2 content: content) .

"name = '=/=' ifTrue: [ name := ' != '. col := Color white. fs := 18 ] .

name = '<->' ifTrue: [ name := '<>'. col := Color white. fs := 18 ] .
name = '->' ifTrue: [ name := '>'. col := Color white. fs := 18 ] ."

name := model name .
name = '-.' ifTrue: [ name := 'X'. col := Color red ] .

aText := name asRopedText .

aText fontSize: fs.
aText foreground: col .

textElement := (BlTextElement text: aText) constraintsDo: [ :c | c linear vertical  alignCenter ].
textElement margin: (BlInsets all: 4).
self addChild: textElement
]
