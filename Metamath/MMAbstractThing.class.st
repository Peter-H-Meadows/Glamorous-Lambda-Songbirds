Class {
	#name : #MMAbstractThing,
	#superclass : #Object,
	#instVars : [
		'name',
		'body',
		'vars',
		'announcer',
		'varDict',
		'lastComment',
		'owner',
		'canMap',
		'isComplete',
		'mappedTo',
		'rawString',
		'varNames',
		'parser'
	],
	#category : #'Metamath-Model'
}

{ #category : #accessing }
MMAbstractThing >> announcer [
^ announcer ifNil: [ announcer := Announcer new ]
]

{ #category : #accessing }
MMAbstractThing >> canMapTo: thing [

"body size = thing body size ifFalse: [ ^ false ] .
body with: thing body do: [ :eame :eastuff | ( eame canMapTo: eastuff ) ifFalse: [ ^ false ] ] .
self announcer announce: MmCanMapAnnouncement new ."

^ body canMapTo: thing body

]

{ #category : #cleaning }
MMAbstractThing >> clean [ 

self localVariables do: [ :ea | ea clean ]
]

{ #category : #cleaning }
MMAbstractThing >> copyAndClean [

| cp |
cp := self copy .

self allVariables do: [ :ea | ea clean ] .

^ cp
]

{ #category : #accessing }
MMAbstractThing >> gameElement [ 

self subclassResponsibility 
]

{ #category : #testing }
MMAbstractThing >> hasEhypoths [

^ false
]

{ #category : #accessing }
MMAbstractThing >> initialize [

isComplete := false

]

{ #category : #testing }
MMAbstractThing >> isComment [ 
^ false
]

{ #category : #accessing }
MMAbstractThing >> isComplete [
^ isComplete
]

{ #category : #testing }
MMAbstractThing >> isEhypoth [

^ false
]

{ #category : #accessing }
MMAbstractThing >> lastComment [

^ lastComment
]

{ #category : #accessing }
MMAbstractThing >> lastComment: c [

lastComment := c
]

{ #category : #names }
MMAbstractThing >> localVariableNames [

^ (self localVariables collect: #name) asSet .


]

{ #category : #accessing }
MMAbstractThing >> localVariables [ 

^ body variables


]

{ #category : #deprecated }
MMAbstractThing >> makeControllers: other [

| controllers |

self error .


controllers := OrderedCollection new .

body with: other body do: [ :eame :eastuff | 

	controllers add: (eame controllorFor: eastuff) .   "(MmMapToController new myModel: eame ; targetModel: eastuff )."

] .


^ controllers .

]

{ #category : #accessing }
MMAbstractThing >> mappedTo [
^ mappedTo
]

{ #category : #accessing }
MMAbstractThing >> mappedTo: h [
mappedTo := h
]

{ #category : #accessing }
MMAbstractThing >> name [
	^ name
]

{ #category : #accessing }
MMAbstractThing >> name: anObject [
	name := anObject
]

{ #category : #accessing }
MMAbstractThing >> owner [
^ owner
]

{ #category : #accessing }
MMAbstractThing >> owner: o [
owner := o
]

{ #category : #parsing }
MMAbstractThing >> parse [ 

]

{ #category : #accessing }
MMAbstractThing >> parser: p [

parser := p
]

{ #category : #cleaning }
MMAbstractThing >> pcopy [

| cp |
cp := self copy .

self localVariables do: [ :ea | ea clean ] .

^ cp
]

{ #category : #accessing }
MMAbstractThing >> rawString: x [
rawString := x
]

{ #category : #initialization }
MMAbstractThing >> resetVars [

self allVariables do: #reset
]

{ #category : #accessing }
MMAbstractThing >> setAsCompleted [
isComplete := true
]

{ #category : #accessing }
MMAbstractThing >> setVarSyms [

self error .

vars := (body collect: [ :ea | ea getVarSyms ]) flattened .

vars := vars asSet .
]

{ #category : #accessing }
MMAbstractThing >> varDict [

self error .

^ varDict
]

{ #category : #accessing }
MMAbstractThing >> varDict: v [

varDict := v .
]

{ #category : #accessing }
MMAbstractThing >> varNames: x [
varNames := x
]

{ #category : #deprecated }
MMAbstractThing >> vars [ 
self error .
^ vars 
]

{ #category : #accessing }
MMAbstractThing >> vars: v [

"vars := v."

"body do: [ :ea | ea vars: v  ]"

body vars: v
]
