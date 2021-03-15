Class {
	#name : #MmAbstractVariableModel,
	#superclass : #MmAbstractModel,
	#instVars : [
		'fixed',
		'mapped',
		'mappedTo',
		'target',
		'isSuccess',
		'highlightStepDone',
		'workingOn',
		'copy',
		'count',
		'color',
		'abDict',
		'mapCount',
		'real'
	],
	#category : #'Metamath-Model'
}

{ #category : #adding }
MmAbstractVariableModel >> addInScope: verse [
self halt
]

{ #category : #accessing }
MmAbstractVariableModel >> body [ 

^ {  }
]

{ #category : #printing }
MmAbstractVariableModel >> canMapTo: stuff [

"if I'm free, easy, map to stuff and return true.

if I'm mapped, return mappedTo canMapTo: stuff .

if I'm fixed, return stuff canMapToFixedVariable: stuff."

"^ real canMapTo: stuff ."

count := count + 1 .

count > 20 ifTrue: [ count := 0 . self halt ] .

self isFreeVar ifTrue: [  
		
	mappedTo := stuff .
	mapped := true .
	fixed := false .
	
	self announcer announce: (MmVariableMappedAnnouncement new mappedTo: stuff ) .
	
	^ true	
] .

fixed ifTrue: [  
	
	stuff fixed ifTrue: [ ^ name = stuff name ] .
	
	^ stuff canMapToFixed: self

] .

^ mappedTo canMapTo: stuff
]

{ #category : #testing }
MmAbstractVariableModel >> canMapToFixed: stuff [

self isFreeVar ifTrue: [  
		
	mappedTo := stuff .
	mapped := true .
	fixed := false .
	
	self announcer announce: (MmVariableMappedAnnouncement new mappedTo: stuff ) .
	
	^ true	
] .

fixed ifTrue: [  
	
	stuff fixed ifTrue: [ ^ true ] .
	^ true
	"^ stuff canMapToFixed: self"

] .


^ mappedTo canMapTo: stuff 

]

{ #category : #accessing }
MmAbstractVariableModel >> canMapToParens: aMMParens [ 
	self halt.
]

{ #category : #'as yet unclassified' }
MmAbstractVariableModel >> checkLoop [

"mapCount := mapCount + 1 .

mapCount > 40 ifTrue: [ mapCount := 0 . self halt ] ."
]

{ #category : #accessing }
MmAbstractVariableModel >> clean [ 

copy := nil
]

{ #category : #accessing }
MmAbstractVariableModel >> color [ 
| ab |
"fixed ifFalse: [^ Color random]."
ab := Dictionary newFromPairs: {'ph' . Color red . 'ps' . Color green . 'ch' . Color blue  } .

^ ab at: name ifAbsent: Color random

"^ color ifNil: [ color := Color random  ]"
]

{ #category : #copying }
MmAbstractVariableModel >> copy [ 

fixed ifTrue: [ ^ self ] .

copy ifNotNil: [ ^ copy ] .

copy := self shallowCopy postCopy .

^ copy
]

{ #category : #printing }
MmAbstractVariableModel >> exx [

self isFreeVar ifTrue: [  
		
	^ self	
] .

fixed ifTrue: [  
	
	^ self

] .

^ mappedTo body
]

{ #category : #'as yet unclassified' }
MmAbstractVariableModel >> fixed [
	^ fixed
]

{ #category : #printing }
MmAbstractVariableModel >> gameElement [

^ MmVariableElement on: self .
]

{ #category : #accessing }
MmAbstractVariableModel >> getVarSyms [

^ name asSymbol 
]

{ #category : #accessing }
MmAbstractVariableModel >> highlight [

blocElement border: (BlBorder paint: Color black width: 4).


]

{ #category : #accessing }
MmAbstractVariableModel >> initialize [ 
super initialize .

fixed := false .
mapped := false .

"isSuccess := false .
highlightStepDone := false ."

count := 0.
mapCount := 0.

]

{ #category : #'as yet unclassified' }
MmAbstractVariableModel >> isFixed [ 
	^ fixed
]

{ #category : #accessing }
MmAbstractVariableModel >> isFreeVar [
^ fixed not and: [ mapped not ]
]

{ #category : #accessing }
MmAbstractVariableModel >> isMapped [
	^ mapped
]

{ #category : #accessing }
MmAbstractVariableModel >> isVar [
^ true
]

{ #category : #accessing }
MmAbstractVariableModel >> mapped [
	^ mapped
]

{ #category : #accessing }
MmAbstractVariableModel >> mappedTo [
	^ mappedTo
]

{ #category : #accessing }
MmAbstractVariableModel >> name [
	^ name
]

{ #category : #accessing }
MmAbstractVariableModel >> name: anObject [
	name := anObject
]

{ #category : #copying }
MmAbstractVariableModel >> postCopy [ 

"copy ifNotNil: [ self halt ] ."

announcer := Announcer new .
color := Color random.
"name := 'oETYuAZFHXVMisn%~#*+' atRandom asString "
]

{ #category : #printing }
MmAbstractVariableModel >> printOn: aStream [
	aStream nextPutAll: name .
	aStream nextPutAll: ' ' .
	
	fixed ifTrue: [ aStream nextPutAll: 'FIX ' . ] .
	mapped ifTrue: [ aStream nextPutAll: 'MAP ' . ] .
	
	aStream nextPutAll: self identityHash printString .
	
	"aStream nextPutAll: fullname printString ."
	
	"fixed ifTrue: [ aStream nextPutAll: 'FIXED.' ] .
	mapped ifTrue: [ aStream nextPutAll: 'MAPPED.' ] ."
	
	"aStream nextPutAll: level printString .
	aStream nextPutAll: '.' ."
	
"	Vars ifNotNil: [  
	
(Vars contains: self) ifTrue: [ aStream nextPutAll: ' MAPPED ' ] ifFalse: [ aStream nextPutAll: ' free ' ] .

] ."
]

{ #category : #'setter as yet unclassified' }
MmAbstractVariableModel >> reset [
	
	workingOn := nil .
]

{ #category : #accessing }
MmAbstractVariableModel >> resetFlags [

isSuccess := false .

highlightStepDone := false .
]

{ #category : #'as yet unclassified' }
MmAbstractVariableModel >> setFixed [

fixed := true 
]

{ #category : #accessing }
MmAbstractVariableModel >> setFree [

fixed := false .
self unmap
]

{ #category : #'as yet unclassified' }
MmAbstractVariableModel >> unmap [ 

	mappedTo := nil .
	mapped := false .
]

{ #category : #accessing }
MmAbstractVariableModel >> variables [

^ self
]

{ #category : #accessing }
MmAbstractVariableModel >> vars: v [

real := v at: name .

"vars := v."

"body do: [ :ea | ea vars: v  ]"

"body vars: v"
]
