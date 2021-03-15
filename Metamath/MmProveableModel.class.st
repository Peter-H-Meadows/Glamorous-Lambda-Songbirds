Class {
	#name : #MmProveableModel,
	#superclass : #MmAbstractModel,
	#category : #'Metamath-Model'
}

{ #category : #accessing }
MmProveableModel >> body: b [

body := b
]

{ #category : #testing }
MmProveableModel >> canMapTo: stuff [

stuff isVar ifTrue: [  
	self error .
	^ stuff canMapTo: self .
] .

stuff isProvable ifFalse: [ self announcer announce: ( MmFailedToMapAnnouncement new reason: 'no match provable' ) . ^ false ] .

"body size = stuff body size ifFalse: [ ^ false ] .
body with: stuff body do: [ :eame :eastuff | ( eame canMapTo: eastuff ) ifFalse: [ ^ false ] ] ."

"self halt."

^ body canMapTo: stuff body .


]

{ #category : #accessing }
MmProveableModel >> gameElement [
^ MmProveableElement new initializeWith: self .
]

{ #category : #testing }
MmProveableModel >> isProvable [ 

^ true .
]

{ #category : #copying }
MmProveableModel >> postCopy [ 

body := body copy . "llect: [ :ea | ea copy ] ."

announcer := Announcer new
]

{ #category : #accessing }
MmProveableModel >> printOn: aStream [

aStream nextPutAll: body printString .
]
