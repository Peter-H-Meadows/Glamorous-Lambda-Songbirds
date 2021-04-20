"
birds use this simulator to work out what happens when x hears y.

code is the operator.
data is the operand.

so we can give the sim code and data,
when the sim is activated it does code hearSong: data .
"
Class {
	#name : #SimModel,
	#superclass : #SbModelAbstract,
	#instVars : [
		'dataSlot',
		'codeSlot'
	],
	#category : #LambdaCalcModel
}

{ #category : #comparing }
SimModel >> = x [
	self class = x class
		ifFalse: [ ^false ].
	^codeSlot = x codeSlot and: [ dataSlot = x dataSlot ]
]

{ #category : #'as yet unclassified' }
SimModel >> activate [
	codeSlot payload payload ifNotNil: [
		[ codeSlot payload payload animating ]
			whileTrue: [ codeSlot payload payload el space pulse ].
	
	
	^ codeSlot payload payload hearSong: dataSlot payload payload
	].
	
	^self
]

{ #category : #accessing }
SimModel >> children [
	^{codeSlot. dataSlot}
]

{ #category : #comparing }
SimModel >> codeSlot [
	^codeSlot 
]

{ #category : #accessing }
SimModel >> connects [ 
	^{}
]

{ #category : #comparing }
SimModel >> dataSlot [
	^dataSlot 
]

{ #category : #testing }
SimModel >> depth: x [
	depth := x.
	dataSlot depth: depth.
	codeSlot depth: depth
]

{ #category : #testing }
SimModel >> depthd [
	dataSlot depthd.
	codeSlot depthd
]

{ #category : #accessing }
SimModel >> elementClass [
	^SimGlob 
]

{ #category : #accessing }
SimModel >> hide [
	self announce: #hide.
]

{ #category : #'as yet unclassified' }
SimModel >> initEmpty [
	depth := 1.
	dataSlot := DataSlotModel new initEmpty .

	dataSlot parent: self.

	codeSlot := CodeSlotModel new initEmpty.
		
	codeSlot parent: self.
]

{ #category : #'as yet unclassified' }
SimModel >> initFromSymbols: list ears: ears depth: d [
	depth := d.
	dataSlot := DataSlotModel new
		initFromSymbols: list last
		ears: ears
		depth: depth.

	dataSlot parent: self.

	codeSlot := CodeSlotModel new
		initFromSymbols: list allButLast
		ears: ears
		depth: depth.
		
	codeSlot parent: self.
]

{ #category : #testing }
SimModel >> isSim [
	^true
]

{ #category : #testing }
SimModel >> name [ 
^'sim'
]

{ #category : #copying }
SimModel >> postCopy [
	announcer := Announcer new.
	dataSlot := dataSlot copy.
	dataSlot parent: self.
	codeSlot := codeSlot copy.
	codeSlot parent: self
]

{ #category : #printing }
SimModel >> printOn: aStream [
	"aStream nextPutAll: ' SIM '.
	aStream nextPutAll: depth asString.
	aStream nextPutAll: ' : '."
	aStream nextPutAll: '('.
	aStream print: dataSlot.
	aStream nextPutAll: ' : '.
	aStream print: codeSlot.
aStream nextPutAll: ')'.
]

{ #category : #deprecated }
SimModel >> simp [
	codeSlot isEmpty ifFalse: [ 
		
		
		dataSlot isEmpty ifTrue: [  
			
			"ear dataSlot connects from?"
			
			dataSlot payload inputingEar  . self halt 
			
			].
		
		
		
		
		 ] ifTrue: [  ]. " payload: codeSlot payload simplify2."
]

{ #category : #deprecated }
SimModel >> simplify [ 
	codeSlot payload: codeSlot payload simplify2.
]

{ #category : #deprecated }
SimModel >> simplify2 [
	codeSlot hide .
	dataSlot hide .
	"codeSlot content hide .
	dataSlot content hide ."

	^codeSlot payload payload simplifyHearSong: dataSlot 




]

{ #category : #acccessing }
SimModel >> simpp [
	codeSlot isEmpty
		ifTrue: [ ^ self ].
		
	codeSlot payload isSim
		ifTrue: [ codeSlot payload simpp.
			^ self ].
		
		
	codeSlot "payload" depth: depth - 1 .
	
	
	dataSlot inputingEar clear.
	
	codeSlot earModel connects
		do: [ :cc | dataSlot payload inputingEar connectTo: cc ].
		
	parent payload: codeSlot payload payload brain.
	
	self root simpp2
]

{ #category : #acccessing }
SimModel >> simpp2 [
	codeSlot isEmpty
		ifTrue: [ ^ self ].
		
	codeSlot payload isSim
		ifTrue: [ codeSlot payload simpp.
			^ self ].
		
	codeSlot "payload" depth: depth - 1 .
	
	
	"dataSlot inputingEar clear.
	
	codeSlot earModel connects
		do: [ :cc | dataSlot payload inputingEar connectTo: cc ]."
		
	parent payload: codeSlot payload payload brain.
	
	"self root simpp"
]
