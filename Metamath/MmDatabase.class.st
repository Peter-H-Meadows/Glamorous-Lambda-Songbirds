Class {
	#name : #MmDatabase,
	#superclass : #Object,
	#instVars : [
		'proofs',
		'assertions',
		'fHypoths',
		'varSymbolSet',
		'scoped',
		'proofDict',
		'varDict',
		'assertionsDictionary',
		'varNameSet',
		'typeDict',
		'typeToClassDict',
		'lastComment',
		'allThings',
		'count',
		'sections'
	],
	#classInstVars : [
		'varSymbolSet'
	],
	#category : #'Metamath-Parsing'
}

{ #category : #adding }
MmDatabase >> addAssertion: a [

count := count + 1 .

a setupMandatoryFloatingHypothesis .

assertions add: a .

"a setupMandatoryFloatingHypothesis: fHypoths ."

"a varDict: varDict ."

"varDict := Dictionary new ."

"varDict := varDict deepCopy ."

allThings add: a .

assertionsDictionary at: a name put: a . 


]

{ #category : #adding }
MmDatabase >> addAssertionInScope: a [

scoped do: [ :ea | a addThing: ea ] .

"a setupMandatoryFloatingHypothesis: fHypoths ."
"a hasEhypoths ifFalse: [ a setAllVariablesToFixed  ] ."


"varDict := Dictionary new ."
]

{ #category : #adding }
MmDatabase >> addEhypothInScope: h [

scoped add: h
]

{ #category : #adding }
MmDatabase >> addFhypoth: h [

| aClass |
"h name = 'c.po' ifTrue: [ self halt ] ."
fHypoths add: h .
typeDict at: h varName put: h type .
aClass := typeToClassDict at: h type .

varDict at: h varName put: (aClass new name: h varName) .

"make dict of types"


]

{ #category : #accessing }
MmDatabase >> addNewScopeWith: things [
self halt .
]

{ #category : #adding }
MmDatabase >> addProof: p [

count := count + 1 .

p assertions: assertions copy .

"p varDict: varDict ."

proofs add: p .

assertions add: p .

allThings add: p .

proofDict at: p name put: p .
]

{ #category : #adding }
MmDatabase >> addProofInScope: p [

scoped do: [ :ea | p addThing: ea ] .

"p setupMandatoryFloatingHypothesis: fHypoths ."
]

{ #category : #adding }
MmDatabase >> addThingInScope: t [
t class = OrderedCollection ifFalse: [ t addInScope: self ]

]

{ #category : #deprecated }
MmDatabase >> addVarSymbol: v [

self error .

varDict at: v asString ifAbsentPut: [ MmAbstractVariableModel new name: v asString ] . 


varSymbolSet add: v
]

{ #category : #adding }
MmDatabase >> addVariable: name [ 

"if adding for first time, check type"

| aClass |
varNameSet add: name .


]

{ #category : #accessing }
MmDatabase >> allThings [

^ allThings 
]

{ #category : #adding }
MmDatabase >> assertionNamed: str [ 

^ assertionsDictionary at: str ifAbsent: [ self proofNamed: str ]
]

{ #category : #adding }
MmDatabase >> assertions [

^ assertions


]

{ #category : #adding }
MmDatabase >> fHypoths [

^ fHypoths
]

{ #category : #adding }
MmDatabase >> initialize [

typeToClassDict := Dictionary newFromPairs: { 

	'wff' . MmWffVariableModel . 
	'setvar' . MmSetvarVariableModel .
	'class' . MmClassVariableModel .

} .

count := 0 .

sections := OrderedCollection new .

varDict := Dictionary new .

typeDict := Dictionary new .

fHypoths := OrderedCollection new .

allThings := OrderedCollection new .

proofs := OrderedCollection new .

assertions := OrderedCollection new .

varSymbolSet := IdentitySet new .

varNameSet := Set new .

scoped := OrderedCollection new .

proofDict := Dictionary new .

assertionsDictionary := Dictionary new .

]

{ #category : #accessing }
MmDatabase >> lastComment [

^ lastComment
]

{ #category : #accessing }
MmDatabase >> lastComment: c [

lastComment := c .

count := count + 1 .

(c body first "second" = $= ) ifTrue: [ sections add: count ] .

allThings add: c .
]

{ #category : #adding }
MmDatabase >> proofNamed: str [ 

^ proofDict at: str ifAbsent: [ proofDict at: 'a1i' "self error: 'cant find'" ]
]

{ #category : #accessing }
MmDatabase >> proofs [
^ proofs 
]

{ #category : #adding }
MmDatabase >> scopeEnded [

scoped := OrderedCollection new .
]

{ #category : #accessing }
MmDatabase >> sections [ 
^ sections 
]

{ #category : #adding }
MmDatabase >> varNames [

^ varNameSet 
]

{ #category : #'as yet unclassified' }
MmDatabase >> varOrConst: n [

(self varNames includes: n) ifTrue: [  
	
	^ varDict at: n ifAbsentPut: [ MmAbstractVariableModel new name: n ]

] .

^ MmConstantModel new name: n 
]

{ #category : #deprecated }
MmDatabase >> varSymbols [

self error .

^ varSymbolSet 
]
