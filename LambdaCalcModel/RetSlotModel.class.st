"
this type of slot just stores a song and returns it when activated 
"
Class {
	#name : #RetSlotModel,
	#superclass : #SbModelAbstract,
	#instVars : [
		'eardist',
		'connected',
		'inputingEar'
	],
	#classVars : [
		'EarStack'
	],
	#category : #LambdaCalcModel
}

{ #category : #accessing }
RetSlotModel class >> addEar: x [
	EarStack add: x 
]

{ #category : #accessing }
RetSlotModel class >> ears [
	^EarStack 
]

{ #category : #accessing }
RetSlotModel class >> initialize [ 
	EarStack := Stack new  
]

{ #category : #accessing }
RetSlotModel class >> newEarStack [
	EarStack := Stack new  
]

{ #category : #accessing }
RetSlotModel class >> pushEar: x [
	EarStack push: x 
]

{ #category : #comparing }
RetSlotModel >> = x [
	self class = x class
		ifFalse: [ ^false ].
	payload ifNil: [ 
	
	x payload ifNotNil: [^false].
	^eardist = x eardist ].
	^payload = x payload
]

{ #category : #activation }
RetSlotModel >> activate [
	self announce: #resultOut.
	^payload
]

{ #category : #'api - graph' }
RetSlotModel >> addEmptySim [ 

payload := SimModel new initEmpty
]

{ #category : #accessing }
RetSlotModel >> brain [
	^nil
]

{ #category : #accessing }
RetSlotModel >> children [
	payload ifNil: [ ^ {} ].
	^{payload}
]

{ #category : #accessing }
RetSlotModel >> connects [ 
	^{}
]

{ #category : #testing }
RetSlotModel >> depthd [
	eardist := eardist - 1
]

{ #category : #accessing }
RetSlotModel >> eardist [
	^eardist 
]

{ #category : #accessing }
RetSlotModel >> elementClass [
	^RetGlob 
]

{ #category : #accessing }
RetSlotModel >> hide [
	self announce: #hide .
]

{ #category : #accessing }
RetSlotModel >> highlight [
	self announce: #highlight
]

{ #category : #'initialization - activities' }
RetSlotModel >> initFromSymbols: array ears: ears depth: d [
	depth := d.
	array isSymbol
		ifTrue: [ name := array.
			(ears at: name) connectTo: self.
			^ self ].
	array size = 1
		ifTrue: [ array first size = 1
				ifTrue: [ name := array first.
					(ears at: name) connectTo: self.
					^ self ] ]
]

{ #category : #initialization }
RetSlotModel >> initialize [
	super initialize .
	color := Color veryDarkGray  .
	eardist := 0.
	connected := false .
	name := '?'
]

{ #category : #accessing }
RetSlotModel >> inputingEar [
	^inputingEar 
]

{ #category : #accessing }
RetSlotModel >> inputingEar: x [
connected := true .
eardist := depth - x depth .
eardist < 0 ifTrue: [self halt] .
inputingEar := x.
color := inputingEar color .
"self announcer announce: #changed ."
]

{ #category : #initialization }
RetSlotModel >> isConnected [
	^connected 
]

{ #category : #accessing }
RetSlotModel >> isEmpty [
^ payload isNil 
]

{ #category : #accessing }
RetSlotModel >> payload [
	^payload
]

{ #category : #accessing }
RetSlotModel >> payload: x depth: d [
	payload := x .
	depth := d
]

{ #category : #copying }
RetSlotModel >> postCopy [
	announcer := Announcer new.
	depth := EarStack size .
	payload := payload copy.
	payload
		ifNil: [ connected
				ifTrue: [ (EarStack at: eardist + 1) connectTo: self ] ]
		ifNotNil: [ payload parent: self ]
]

{ #category : #printing }
RetSlotModel >> printOn: aStream [
	payload
		ifNotNil: [ aStream print: payload ]
		ifNil: [ aStream nextPutAll: name.
			aStream nextPutAll: eardist asString ].
		
	aStream nextPutAll: ' '
]

{ #category : #accessing }
RetSlotModel >> setPayloadAndAnnounce: x [
	payload := x .
	self announce: ( SbEarCopyAdded new model: x ) .
]

{ #category : #deprecated }
RetSlotModel >> simpp [

payload ifNotNil: [ payload simpp ]
]

{ #category : #actions }
RetSlotModel >> simpp2 [

payload ifNotNil: [ payload simpp2 ]
]

{ #category : #'api - graph' }
RetSlotModel >> swapFor: x [

payload := x .
]
