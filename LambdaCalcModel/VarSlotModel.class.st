"
var
"
Class {
	#name : #VarSlotModel,
	#superclass : #SbModelAbstact,
	#category : #LambdaCalcModel
}

{ #category : #comparing }
VarSlotModel >> = x [

self class = x class ifFalse: [ ^ false ] .

^ payload = x payload
]

{ #category : #accessing }
VarSlotModel >> brain [
^ nil 
]

{ #category : #accessing }
VarSlotModel >> children [ 
payload  ifNil: [ ^ {  } ].
^ { payload }
]

{ #category : #'as yet unclassified' }
VarSlotModel >> connects [ 

^ {  }
]

{ #category : #testing }
VarSlotModel >> depth: x [
depth := x .
payload ifNotNil: [ payload depth: depth ]
]

{ #category : #testing }
VarSlotModel >> depthd [
payload depthd
]

{ #category : #accessing }
VarSlotModel >> elementClass [
^ SlotGlob 
]

{ #category : #accessing }
VarSlotModel >> hide [

self announcer announce: #hide .
]

{ #category : #'initialization - activities' }
VarSlotModel >> initFromSymbols: array ears: ears depth: d [
	| xx |
	xx := array.
	depth := d.

	array isSymbol
		ifTrue: [ name := array.
			payload := RetSlotModel new
				name: name depth: d.
			payload parent: self .
			(ears at: name) connectTo: payload.
			^ self ].
		
	array size = 1
		ifTrue: [ array first size = 1
				ifTrue: [ name := array first.
					payload := RetSlotModel new
						name: name depth: d.
					payload parent: self .
					(ears at: name) connectTo: payload.
					^ self ]
				ifFalse: [ xx := array first ] ].

	"in this case, this slot is a sim or bird. "
	payload := xx first = #\
		ifTrue: [ SongbirdModel new
				initFromSymbols: xx allButFirst
				ears: ears
				depth: depth + 1 ]
		ifFalse: [ SimModel new initFromSymbols: xx ears: ears depth: depth ].
		
	payload parent: self .
]

{ #category : #deprecated }
VarSlotModel >> inputingEar [
"^ inputingEar"
]

{ #category : #deprecated }
VarSlotModel >> inputingEar: x [
"inputingEar := x.
color := inputingEar color .
self announcer announce: #changed ."
]

{ #category : #testing }
VarSlotModel >> isCodeSlot [
^ false
]

{ #category : #testing }
VarSlotModel >> isDataSlot [
^ false
]

{ #category : #testing }
VarSlotModel >> isEmpty [ 
^ payload payload isNil 
]

{ #category : #accessing }
VarSlotModel >> payload [
	^ payload
]

{ #category : #accessing }
VarSlotModel >> payload: x [

payload := x .

x depth: depth.

x parent: self .
]

{ #category : #copying }
VarSlotModel >> postCopy [
	announcer := Announcer new.
	payload := payload copy.
	payload parent: self
]

{ #category : #accessing }
VarSlotModel >> setPayloadAndAnnounce: x [

payload  := x .

self announcer announce: (SbEarCopyAdded new model: x ) .
]
