Class {
	#name : #MmCurlyBracesModel,
	#superclass : #MmAbstractBracketsModel,
	#category : #'Metamath-Model'
}

{ #category : #accessing }
MmCurlyBracesModel >> gameElement [
^ MmCurlyBracesElement new initializeWith: self .

]
