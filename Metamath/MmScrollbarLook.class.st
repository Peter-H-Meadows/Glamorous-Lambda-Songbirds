Class {
	#name : #MmScrollbarLook,
	#superclass : #BrLook,
	#instVars : [
		'scrollbar'
	],
	#category : #Metamath
}

{ #category : #initialization }
MmScrollbarLook >> initialize [
	super initialize.

	scrollbar := BrScrollbar new beHorizontal 
		look: BrScrollbarLook new;
		thumb: (BrScrollbarThumb new look: BrGlamorousScrollbarThumbLook new);
		track: (BrScrollbarTrack new look: BrGlamorousScrollbarTrackLook new);
		constraintsDo: [ :c |
			c ignoreByLayout.
			c margin: (BlInsets top: 2).
			c ignored vertical alignTop ].

	self addChangeAddChildAs: #(content horizontalScrollbar) with: [ scrollbar scrollable: (self widget childNamed: #scrollable) ]
]
