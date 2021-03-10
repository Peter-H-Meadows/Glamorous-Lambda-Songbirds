"
birds use this simulator to work out what happens when x hears y.

code is the operator.
data is the operand.

so we can give the sim code and data,
when the sim is activated it does code hearSong: data .
"
Class {
	#name : #SimModel,
	#superclass : #SbModelAbstact,
	#instVars : [
		'dataSlot',
		'codeSlot'
	],
	#category : #LambdaCalcModel
}

{ #category : #comparing }
SimModel >> = x [
	self class = x class
		ifFalse: [ ^ false ].
	^ codeSlot = x codeSlot and: [ dataSlot = x dataSlot ]
]

{ #category : #'as yet unclassified' }
SimModel >> activate [
	[ codeSlot payload payload animating ]
		whileTrue: [ codeSlot payload payload el space pulse ].
	^ codeSlot payload payload hearSong: dataSlot payload payload
]

{ #category : #'as yet unclassified' }
SimModel >> children [

^ { codeSlot . dataSlot }
]

{ #category : #comparing }
SimModel >> codeSlot [
^ codeSlot 
]

{ #category : #'as yet unclassified' }
SimModel >> connects [ 

^ {  }
]

{ #category : #comparing }
SimModel >> dataSlot [
^ dataSlot 
]

{ #category : #testing }
SimModel >> depth: x [
depth := x .

dataSlot depth: depth .

codeSlot depth: depth


]

{ #category : #testing }
SimModel >> depthd [

dataSlot depthd.
codeSlot depthd


]

{ #category : #accessing }
SimModel >> elementClass [
^ SimGlob 
]

{ #category : #accessing }
SimModel >> hide [

self announcer announce: #hide .
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
	aStream nextPutAll: ' SIM '.
	aStream nextPutAll: depth asString.
	aStream nextPutAll: ' : '.
	aStream print: dataSlot.
	aStream nextPutAll: ' : '.
	aStream print: codeSlot
]

{ #category : #deprecated }
SimModel >> simplify [ 

codeSlot payload: codeSlot payload simplify2 .


]

{ #category : #deprecated }
SimModel >> simplify2 [

codeSlot hide .
dataSlot hide .
"codeSlot content hide .
dataSlot content hide ."

^ codeSlot payload payload simplifyHearSong: dataSlot 




]
