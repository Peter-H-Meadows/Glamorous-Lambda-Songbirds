Class {
	#name : #MmWffModel,
	#superclass : #MmAbstractModel,
	#category : #'Metamath-Model'
}

{ #category : #accessing }
MmWffModel >> borderColor [ 

^ Color purple 
]

{ #category : #testing }
MmWffModel >> canMapTo: stuff [

stuff isVar ifTrue: [  
	self error .
	^ stuff canMapTo: self .
] .

"stuff isProvable ifFalse: [ self announcer announce: ( MmFailedToMapAnnouncement new reason: 'no match provable' ) . ^ false ] ."


body canMapTo: stuff body .

^ true .
]

{ #category : #accessing }
MmWffModel >> gameElement [
^ MmWffElement new initializeWith: self .
]

{ #category : #testing }
MmWffModel >> isWFF [

^ true
]

{ #category : #copying }
MmWffModel >> postCopy [ 

body := body copy .

announcer := Announcer new
]
