Class {
	#name : #MmAbstractBracketsModel,
	#superclass : #MmAbstractModel,
	#category : #'Metamath-Model'
}

{ #category : #copying }
MmAbstractBracketsModel >> postCopy [ 

"body := body collect: [ :ea | ea copy ] ."
body := body copy.
announcer := Announcer new
]
