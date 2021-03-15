Class {
	#name : #MmCommentElement,
	#superclass : #MmRawElement,
	#instVars : [
		'body'
	],
	#category : #'Metamath-Bloc'
}

{ #category : #accessing }
MmCommentElement >> createFromString: str [ 

| aText textElement |
str linesDo: [ :line | 

	aText := line asRopedText .

	aText fontSize: 18.
	aText foreground: Color veryLightGray .
	textElement := (BlTextElement text: aText) "constraintsDo: [ :c | c linear horizontal alignCenter ]".
	self addChild: textElement .

] .
]

{ #category : #accessing }
MmCommentElement >> initialize [

| clickHandler |
super initialize .

self geometry: BlRectangle new.

self layout: BlLinearLayout  vertical .

self padding: (BlInsets all: 4).
self margin: (BlInsets all: 4).

self constraintsDo: [ :c | 
					c horizontal fitContent.
					c vertical fitContent ].
				
clickHandler := BlEventHandler
		on: BlClickEvent
		do: [ self removeFromParent
			"container removeEventHandler: clickHandler.
			container addAnimation: animation" ].
self addEventHandler: clickHandler.
	
]
