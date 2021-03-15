Class {
	#name : #MmFloatingHypothesisElement,
	#superclass : #AbstractHypothesisElement,
	#category : #'Metamath-Bloc'
}

{ #category : #'instance creation' }
MmFloatingHypothesisElement class >> on: aHypoth [
	^ self new initializeWithHypoth: aHypoth
]

{ #category : #accessing }
MmFloatingHypothesisElement >> borderColor [

^ Color purple
]

{ #category : #initialization }
MmFloatingHypothesisElement >> initializeWith: aHypothModel [

model := aHypothModel .

self margin: (BlInsets all: 2).

selectedMarkerElement := BlElement new
		constraintsDo: [ :c |
			c horizontal exact: 4.
			c vertical matchParent ];
		background: BlTransparentBackground new.


self addChild: selectedMarkerElement .

self addChild: model gameElement .
]

{ #category : #initialization }
MmFloatingHypothesisElement >> initializeWithHypoth: aHypoth [
]

{ #category : #'as yet unclassified' }
MmFloatingHypothesisElement >> tryMakeWithEl: el [ 

el removeFromParent .
self addChildFirst: el .

"el model canMapTo: model."

model canMapTo: el model.
]
