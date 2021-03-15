Class {
	#name : #MmNotModel,
	#superclass : #MmAbstractModel,
	#category : #'Metamath-Model'
}

{ #category : #testing }
MmNotModel >> canMapTo: stuff [

stuff isVar ifTrue: [  
	self error .
	^ stuff canMapTo: self .
] .

^ body canMapTo: stuff body .
]

{ #category : #accessing }
MmNotModel >> gameElement [
^ MmNotElement new initializeWith: self .
]

{ #category : #copying }
MmNotModel >> postCopy [ 

body := body copy . "llect: [ :ea | ea copy ] ."

announcer := Announcer new
]
