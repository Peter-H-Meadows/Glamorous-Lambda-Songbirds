Class {
	#name : #MmAbstractModel,
	#superclass : #Object,
	#instVars : [
		'name',
		'body',
		'announcer',
		'varNames'
	],
	#category : #'Metamath-Model'
}

{ #category : #accessing }
MmAbstractModel >> = ob [ 

"^ self canMapTo: ob"
^ name = ob name
]

{ #category : #accessing }
MmAbstractModel >> announcer [
^ announcer ifNil: [ announcer := Announcer new ]
]

{ #category : #accessing }
MmAbstractModel >> body [

^ body
]

{ #category : #accessing }
MmAbstractModel >> body: b [

body := b
]

{ #category : #testing }
MmAbstractModel >> canMapToFixed: x [

self announcer announce: ( MmFailedToMapAnnouncement new reason: 'no match paren' ) .

^ false 
]

{ #category : #copying }
MmAbstractModel >> copyWithVars: vs [

self halt .

^ self shallowCopy postCopyWith: vs .
]

{ #category : #accessing }
MmAbstractModel >> exx [
^ self
]

{ #category : #'instance creation' }
MmAbstractModel >> fixed [ 

^ false
]

{ #category : #accessing }
MmAbstractModel >> getVarSyms [

^ {  }
]

{ #category : #accessing }
MmAbstractModel >> isComment [
^ false
]

{ #category : #accessing }
MmAbstractModel >> isConst [
^ false
]

{ #category : #accessing }
MmAbstractModel >> isFreeVar [
^ false
]

{ #category : #accessing }
MmAbstractModel >> isList [
^ false
]

{ #category : #accessing }
MmAbstractModel >> isParens [
^ false
]

{ #category : #testing }
MmAbstractModel >> isProvable [ 

^ false .
]

{ #category : #accessing }
MmAbstractModel >> isVar [
^ false
]

{ #category : #testing }
MmAbstractModel >> isWFF [

^ false
]

{ #category : #parsing }
MmAbstractModel >> parse [ 

]

{ #category : #parsing }
MmAbstractModel >> parser: p [

]

{ #category : #accessing }
MmAbstractModel >> varNames: x [
varNames := x
]

{ #category : #accessing }
MmAbstractModel >> variables [

^ body variables flattened asSet .
]

{ #category : #accessing }
MmAbstractModel >> vars: v [

"vars := v."

"body do: [ :ea | ea vars: v  ]"

body vars: v
]
