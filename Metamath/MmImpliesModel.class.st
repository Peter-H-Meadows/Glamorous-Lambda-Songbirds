Class {
	#name : #MmImpliesModel,
	#superclass : #MmAbstractModel,
	#instVars : [
		'first',
		'second'
	],
	#category : #'Metamath-Model'
}

{ #category : #testing }
MmImpliesModel >> canMapTo: stuff [

stuff isVar ifTrue: [  
	
	^ stuff canMapTo: self .
] .

( first canMapTo: stuff first ) ifFalse: [ ^ false ] .

^ second canMapTo: stuff second 
]

{ #category : #accessing }
MmImpliesModel >> first [
^ first 
]

{ #category : #accessing }
MmImpliesModel >> first: x second: y [
first := x .
second := y
]

{ #category : #accessing }
MmImpliesModel >> gameElement [
^ MmListElement  new initializeWith: self "first gameElement".
]

{ #category : #copying }
MmImpliesModel >> postCopy [ 

first := first copy .
second := second copy
]

{ #category : #accessing }
MmImpliesModel >> second [
^ second 
]

{ #category : #accessing }
MmImpliesModel >> vars: v [

first vars: v .
second  vars: v .
]
