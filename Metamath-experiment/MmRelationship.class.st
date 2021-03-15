Class {
	#name : #MmRelationship,
	#superclass : #MmSetVizSet,
	#type : #variable,
	#category : #'Metamath-experiment'
}

{ #category : #adding }
MmRelationship >> add: x [
self assert: x class  equals: MmPairp .
super add: x . 

]
