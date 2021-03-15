Class {
	#name : #MmSquareBracetsModel,
	#superclass : #MmAbstractBracketsModel,
	#category : #'Metamath-Model'
}

{ #category : #accessing }
MmSquareBracetsModel >> gameElement [
^ MmSquareBracets new initializeWith: self .

]
