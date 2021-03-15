Class {
	#name : #AbstractHypothesisElement,
	#superclass : #MmAbstractThingElement,
	#category : #'Metamath-Bloc'
}

{ #category : #accessing }
AbstractHypothesisElement >> highlightAsSelected [ 
 
selectedMarkerElement background: ( Color red ).
selected := true 

]
