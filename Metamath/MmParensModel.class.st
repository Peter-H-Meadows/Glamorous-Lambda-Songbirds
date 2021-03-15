Class {
	#name : #MmParensModel,
	#superclass : #MmAbstractBracketsModel,
	#category : #'Metamath-Model'
}

{ #category : #testing }
MmParensModel >> canMapTo: stuff [

stuff isVar ifTrue: [  
	
	^ stuff canMapTo: self .
] .

stuff isList ifTrue: [  
	
	self halt .

	^ self canMapTo: stuff body first .	
] .

stuff isParens ifFalse: [ self announcer announce: ( MmFailedToMapAnnouncement new reason: 'no match paren' ) . ^ false ] .

^ body canMapTo: stuff body .


]

{ #category : #accessing }
MmParensModel >> gameElement [
^ MmParensElement new initializeWith: self .
]

{ #category : #accessing }
MmParensModel >> isParens [
^ true
]

{ #category : #accessing }
MmParensModel >> printOn: aStream [

aStream nextPutAll: 'parens ' .
aStream nextPutAll: body printString .
]
