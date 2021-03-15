Class {
	#name : #MMFHypoth,
	#superclass : #MMHypoth,
	#instVars : [
		'type',
		'varName',
		'var'
	],
	#category : #'Metamath-Model'
}

{ #category : #accessing }
MMFHypoth >> addInScope: verse [


]

{ #category : #accessing }
MMFHypoth >> addTo: x [

x addFHypoth: self
]

{ #category : #accessing }
MMFHypoth >> body [
	^ var
]

{ #category : #accessing }
MMFHypoth >> body: anObject [

	body := anObject
]

{ #category : #copying }
MMFHypoth >> copyWithVars: vs [

^ self shallowCopy postCopyWith: vs .
]

{ #category : #accessing }
MMFHypoth >> createFrom: v [

body := MmWffModel new body: v
]

{ #category : #accessing }
MMFHypoth >> gameElement [

^ body gameElement .

]

{ #category : #'as yet unclassified' }
MMFHypoth >> hasVarFrom: pvars [

"vars := body flatCollect: [ :ea | ea setLevel: 1 ] .
^ vars includesAny: li"

^ self localVariableNames includesAny: pvars
]

{ #category : #accessing }
MMFHypoth >> name [
	^ name
]

{ #category : #accessing }
MMFHypoth >> name: anObject [
	name := anObject
]

{ #category : #'as yet unclassified' }
MMFHypoth >> postCopyWith: vs [

body := body collect: [ :ea | ea copyWithVars: vs ] .

announcer := Announcer new
]

{ #category : #'as yet unclassified' }
MMFHypoth >> setAllVarsLevel: n [

vars do: [ :e | e level: n ]
]

{ #category : #'as yet unclassified' }
MMFHypoth >> type [

^ type
]

{ #category : #'as yet unclassified' }
MMFHypoth >> type: t varName: vn [

type := t .
varName := vn .
]

{ #category : #'as yet unclassified' }
MMFHypoth >> varName [ 

^ varName
]

{ #category : #accessing }
MMFHypoth >> vars: v [

vars := v.

vars do: [ :ea | ea fullname: ea name , '-' , name  ]
]
