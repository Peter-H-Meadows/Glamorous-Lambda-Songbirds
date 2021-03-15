Class {
	#name : #MmListModel,
	#superclass : #MmAbstractModel,
	#category : #'Metamath-Model'
}

{ #category : #testing }
MmListModel >> canMapTo: stuff [

| targetStream myst my aList |

stuff isList ifFalse: [ self error ] .

"body size > 1 ifTrue: [
	
	stuff body size = 1 ifTrue: [ self halt . ^ stuff canMapTo: self ]
	
]."

"body size = 1 ifTrue: [

	^ body first canMapTo: stuff
].

body size = stuff body size ifTrue: [

body with: stuff body do: [ :m :i |
	m canMapTo: i .
	^ true 

].

].

self halt ."


body size = 1 ifTrue: [ ( body first canMapTo: stuff body first ) ifFalse: [ ^ false ] . ] .

targetStream := ReadStream on: stuff body "expandMappedVars flattened"  .

myst := ReadStream on: body .


(myst skipTo:  (MmConstantModel new initializeWith: '->') ) ifTrue: [
	
	
myst := ReadStream on: body .
	
	aList := MmListModel new body: (myst upTo: (MmConstantModel new initializeWith: '->')) .
	
	stuff body first canMapTo: aList .
	
	stuff body third canMapTo: myst upToEnd first.
	
	 self halt . 
	
	
	
	
	
	
	
	
	] ifFalse: [  

targetStream := ReadStream on: stuff body "expandMappedVars flattened"  .

myst := ReadStream on: body .

[ myst atEnd ] whileFalse: [
	
	my := myst next .
	
	my isVar ifTrue: [

		aList := myst atEnd ifTrue: [ 
			MmListModel new body: targetStream upToEnd .
			
		] ifFalse: [
		
			myst peek isConst ifTrue: [
				MmListModel new body: (targetStream upTo: myst next) .
			] ifFalse: [ self halt. targetStream next ].			
					
		].
	
		(my canMapTo: aList) ifFalse: [ ^ false ] .

	] ifFalse: [ 

		targetStream atEnd ifTrue: [ ^ false ] .
		(my canMapTo: (targetStream next)) ifFalse: [ ^ false ] .	
		
	].
	
	
] .
^ true .
].
^ true
]

{ #category : #testing }
MmListModel >> canMapToFixed: stuff [
"body size < 1 ifTrue: [ self halt . ^ false ]."

body size > 1 ifTrue: [ self halt . ^ false ].

^ body first canMapToFixed: stuff


]

{ #category : #testing }
MmListModel >> canMapToXstreamOLD: stuff [

| targetStream myst my aList |

stuff isList ifFalse: [ self error ] .

"body size > 1 ifTrue: [
	
	stuff body size = 1 ifTrue: [ self halt . ^ stuff canMapTo: self ]
	
].

body size = 1 ifTrue: [

body first isParens ifFalse: [
	stuff body size = 1 ifTrue: [ self halt . ^ true ]]
	
]."

targetStream := ReadStream on: stuff expandMappedVars flattened  .

myst := ReadStream on: body .

[ myst atEnd ] whileFalse: [
	
	my := myst next .
	
	my isVar ifTrue: [

		aList := myst atEnd ifTrue: [ 
			MmListModel new body: targetStream upToEnd .
			
		] ifFalse: [
		
			myst peek isConst ifTrue: [
				MmListModel new body: (targetStream upTo: myst next) .
			] ifFalse: [ self halt. targetStream next ].			
					
		].
	
		(my canMapTo: aList) ifFalse: [ ^ false ] .

	] ifFalse: [ 

		targetStream atEnd ifTrue: [ ^ false ] .
		(my canMapTo: (targetStream next)) ifFalse: [ ^ false ] .	
		
	].
	
	
] .

^ true
]

{ #category : #accessing }
MmListModel >> expandMappedVars [

"^ MmListModel new body: (body collect: [ :ea | ea exx ])."

^ (body collect: [ :ea | ea exx ]).
]

{ #category : #accessing }
MmListModel >> gameElement [
^ MmListElement new initializeWith: self .
]

{ #category : #accessing }
MmListModel >> isList [
^ true
]

{ #category : #copying }
MmListModel >> postCopy [ 

body := body collect: [ :ea | ea copy ] .

announcer := Announcer new
]

{ #category : #accessing }
MmListModel >> printOn: aStream [
aStream nextPutAll: 'list ' .
aStream nextPutAll: body size printString .
aStream nextPutAll: ' ' .

body do: [ :ea |

	aStream nextPutAll: ea printString .
	aStream nextPutAll: ' ' .

]
]

{ #category : #accessing }
MmListModel >> variables [

^ (body collect: [ :ea | ea variables ]) flattened asSet .
]
