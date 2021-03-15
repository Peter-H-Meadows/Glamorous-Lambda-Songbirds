Class {
	#name : #MmPP2ParserBody2,
	#superclass : #PP2CompositeNode,
	#instVars : [
		'stuff',
		'parentheses',
		'label',
		'not',
		'main',
		'implies',
		'proveable',
		'wff'
	],
	#classVars : [
		'VarDict',
		'VarNames',
		'VarsUsed'
	],
	#category : #'Metamath-Parsing'
}

{ #category : #accessing }
MmPP2ParserBody2 class >> varNames: x [

VarNames := x
]

{ #category : #'as yet unclassified' }
MmPP2ParserBody2 class >> varsUsed [
^ VarsUsed 
]

{ #category : #accessing }
MmPP2ParserBody2 >> implies [

^ $( asPParser trim , (implies / label / not) , '->' asPParser trim  ,  (implies / label / not)  , $) asPParser trim  ==> 

	[ :x | 
	
		MmImpliesModel new first: x second second: x fourth   
	
	] 
]

{ #category : #initialization }
MmPP2ParserBody2 >> initialize [ 

	super initialize .
	"AllAssertions := Dictionary new.
	AllProofs := OrderedCollection new."

	VarsUsed := Set new .

	"VarDict := Dictionary new"
]

{ #category : #accessing }
MmPP2ParserBody2 >> label [

"^ #word asPParser plus flatten trim ==> "

^ (#word asPParser plus, ( $- asPParser / $. asPParser, #word asPParser plus ) plus optional) flatten ==>

	[ :x | " Db varOrConst: x" 
	
		(VarNames includes: x) ifTrue: [  
	
			 "VarDict at: x ifAbsentPut: [ MmAbstractVariableModel new name: x ]"
			VarsUsed add: x .
			MmVarModel new name: x

		] ifFalse: [

 			MmConstantModel new name: x .
		]
	]
]

{ #category : #accessing }
MmPP2ParserBody2 >> main [
^ parentheses / label "/ not"
]

{ #category : #accessing }
MmPP2ParserBody2 >> not [

^ '-.' asPParser trim  , (implies / label / not) ==> 

	[ :x | 
	
		MmNotModel new body: x second 
	
	] 
]

{ #category : #accessing }
MmPP2ParserBody2 >> parentheses [
	^ $( asPParser trim , stuff , $) asPParser trim ==> 

		[ :x | MmParensModel new body: x second . ]
]

{ #category : #accessing }
MmPP2ParserBody2 >> proveable [

^ '|-' asPParser trim , (implies / label / not)  ==> 

	[ :x |
	
		MmProveableModel new body: x second 
	
	] 
]

{ #category : #accessing }
MmPP2ParserBody2 >> start [

^ proveable / wff
]

{ #category : #accessing }
MmPP2ParserBody2 >> stuff [
^ parentheses  "/ not" / implies "/ label"
]

{ #category : #accessing }
MmPP2ParserBody2 >> wff [

^ 'wff' asPParser trim  , (implies / label / not) ==> 

	[ :x | 
	
		MmWffModel new body: x second 
	
	] 
]
