Class {
	#name : #MmFreeVariable,
	#superclass : #MmAbstractVariableModel,
	#category : #'Metamath-Model'
}

{ #category : #printing }
MmFreeVariable >> canMapTo: whatever [  

self becomeForward: (MmClassVariableModel new mappedTo: whatever ).

^ true
]
