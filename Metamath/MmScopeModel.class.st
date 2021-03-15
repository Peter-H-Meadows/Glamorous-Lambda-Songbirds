Class {
	#name : #MmScopeModel,
	#superclass : #MmAbstractModel,
	#instVars : [
		'proofs',
		'assertions',
		'ehypoths',
		'comments',
		'scopes',
		'title',
		'stuff',
		'assertionsDict',
		'allProofs',
		'allRawThings',
		'allAssertions'
	],
	#category : #'Metamath-Model'
}

{ #category : #accessing }
MmScopeModel >> addAssertionInScope: aMMAssertion [ 
aMMAssertion essentialHypoths: ehypoths.
	assertions add: aMMAssertion .
	stuff add: aMMAssertion .
	"ProofDict at: aMMAssertion name put: aMMAssertion ."
	assertionsDict at: aMMAssertion name put: aMMAssertion .
]

{ #category : #adding }
MmScopeModel >> addComment: c [
comments add: c.
title := c body.
stuff add: c
"self halt."
]

{ #category : #'as yet unclassified' }
MmScopeModel >> addEhypothInScope: aMMEHypoth [ 
	"self shouldBeImplemented."
	ehypoths add: aMMEHypoth 
]

{ #category : #accessing }
MmScopeModel >> addInScope: aMmScopeModel [ 
	aMmScopeModel addScope: self
]

{ #category : #accessing }
MmScopeModel >> addProofInScope: aMMProof [ 
aMMProof essentialHypoths: ehypoths.
	proofs add: aMMProof .
	stuff add: aMMProof.
	
	"ProofDict at: aMMProof name put: aMMProof ."
	assertionsDict at: aMMProof name put: aMMProof .
	
]

{ #category : #accessing }
MmScopeModel >> addScope: s [
scopes add: s.
stuff add: s
]

{ #category : #accessing }
MmScopeModel >> allAssertions [

^ allAssertions
]

{ #category : #accessing }
MmScopeModel >> allAssertions: x [

allAssertions := x
]

{ #category : #accessing }
MmScopeModel >> allProofs [

^ allProofs
]

{ #category : #accessing }
MmScopeModel >> allProofs: x [

allProofs := x
]

{ #category : #accessing }
MmScopeModel >> eel [
^ MmScopeElement2 new with: self
]

{ #category : #'as yet unclassified' }
MmScopeModel >> ehypoths [
	^ ehypoths
]

{ #category : #initialization }
MmScopeModel >> initialize [ 
super initialize .
proofs := OrderedCollection new .
assertions := OrderedCollection new .
ehypoths := OrderedCollection new .
comments := OrderedCollection new .
scopes  := OrderedCollection new .
stuff  := OrderedCollection new .
title := 'global'.
assertionsDict := Dictionary new .
]

{ #category : #parsing }
MmScopeModel >> parse [ 

| parser |
MmPP2ParserBody2 varNames: varNames .
parser := MmPP2ParserBody2 new .

allRawThings do: [ :ea | 
	ea parser: parser .
	ea parse . 
	ea addInScope: self 
]
]

{ #category : #printing }
MmScopeModel >> printOn: aStream [

aStream nextPutAll: 'Scope. size: '.
aStream nextPutAll: allRawThings size printString   .

]

{ #category : #accessing }
MmScopeModel >> scopes [
^ scopes
]

{ #category : #accessing }
MmScopeModel >> stuff [
^ stuff 
]

{ #category : #accessing }
MmScopeModel >> title [
^ title
]

{ #category : #accessing }
MmScopeModel >> with: rawThings [

rawThings do: [:ea | ea addInScope: self ]
]

{ #category : #accessing }
MmScopeModel >> withr: rawThings [

allRawThings := rawThings 
]
