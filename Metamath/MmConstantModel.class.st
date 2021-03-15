Class {
	#name : #MmConstantModel,
	#superclass : #MmAbstractModel,
	#category : #'Metamath-Model'
}

{ #category : #adding }
MmConstantModel >> addInScope: verse [

]

{ #category : #accessing }
MmConstantModel >> body [ 

^ OrderedCollection new
]

{ #category : #accessing }
MmConstantModel >> canMapTo: other [ 

"( other isKindOf: MMVariable ) ifTrue: [  
	
	^ other canMapTo: self .
] .

( other isKindOf: MMVariableMapped ) ifTrue: [  
	self halt .
	^ other canMapTo: self .
] ."

other isVar ifTrue: [  
	
	^ other canMapTo: self .
] .
other isConst ifTrue: [
	
	^ name = other name 
	
	"iTrue: [ ^ true ] ifFalse: [ self halt ] ."
	
	] .

^ false
]

{ #category : #accessing }
MmConstantModel >> canMapTo: other level: lvl [

( other isKindOf: MmAbstractVariableModel ) ifTrue: [  
	
	^ other canMapTo: self level: lvl - 1 .
] . 


( other isKindOf: MmConstantModel ) ifFalse: [ ^ false ] .

^ name = other name
]

{ #category : #accessing }
MmConstantModel >> canMapTo: other stepCount: step [

other isVar ifTrue: [  
	
	^ other canMapTo: self stepCount: step .
] .

	name = other name ifTrue: [  
		
		other isConst ifTrue: [ ^ #success ] ifFalse: [ self halt ] .
	
	] .

self announcer announce: ( MmFailedToMapAnnouncement new reason: 'const' ) .

^ #fail
]

{ #category : #accessing }
MmConstantModel >> canMapTogui: other [ 

"( other isKindOf: MMVariable ) ifTrue: [  
	
	^ other canMapTo: self .
] .

( other isKindOf: MMVariableMapped ) ifTrue: [  
	self halt .
	^ other canMapTo: self .
] ."

other isVar ifTrue: [  
	
	^ other canMapTo: self .
] .

	name = other name ifTrue: [  
		
		other isConst ifTrue: [ ^ true ] ifFalse: [ self halt ] .
	
	] .

^ false
]

{ #category : #accessing }
MmConstantModel >> gameElement [

^ MmConstantElement new initializeWith: self

]

{ #category : #accessing }
MmConstantModel >> initializeWith: anObject [
	name := anObject
]

{ #category : #accessing }
MmConstantModel >> isConst [
^ true
]

{ #category : #accessing }
MmConstantModel >> name [
	^ name
]

{ #category : #accessing }
MmConstantModel >> name: anObject [
	name := anObject
]

{ #category : #printing }
MmConstantModel >> printOn: aStream [
	aStream nextPutAll: name .
]

{ #category : #accessing }
MmConstantModel >> variables [ 

^ {  }
]
