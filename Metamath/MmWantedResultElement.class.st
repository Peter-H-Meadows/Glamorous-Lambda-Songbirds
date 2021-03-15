Class {
	#name : #MmWantedResultElement,
	#superclass : #MmAbstractThingElement,
	#category : #'Metamath-Bloc'
}

{ #category : #initialization }
MmWantedResultElement >> initializeWith: aProofModel [

| startBracketElement |
model := aProofModel .

self margin: (BlInsets all: 2).

self addChildFirst: selectedMarkerElement .

self addChild: model body gameElement .

startBracketElement := BlElement new
		constraintsDo: [ :c |
			c horizontal exact: 8.
			c vertical matchParent ];
		background: ( Color black  ).

self addChild: startBracketElement .
]

{ #category : #accessing }
MmWantedResultElement >> tryMakeWithEl: el [ 

el removeFromParent .
self addChildFirst: el .	
				
			"1 seconds asDelay wait."
				
			(el model canMapTo: model) ifFalse: [ self background: Color red ].
			
			"1 seconds asDelay wait."
			
			model isComplete ifTrue: [ self background: Color veryDarkGray ].
]
