Class {
	#name : #MmPP2ParserFirst,
	#superclass : #PP2CompositeNode,
	#instVars : [
		'scope',
		'comment',
		'constant',
		'variable',
		'label',
		'floatingHypothesis',
		'essentialHypothesis',
		'distinct',
		'assertion',
		'proof'
	],
	#classVars : [
		'AllAssertions',
		'AllProofs',
		'VarNames'
	],
	#category : #'Metamath-Parsing'
}

{ #category : #generated }
MmPP2ParserFirst >> assertion [

| thing |
^  label , '$a' asPParser trim ,  #any asPParser starLazy flatten  , '$.' asPParser trim ==> 

	[ :x | thing := MMAssertion new  name: x first ; rawString: x third  ; varNames: VarNames copy .
	
			AllAssertions  at: x first put: thing .
		
		thing
		
	]
]

{ #category : #accessing }
MmPP2ParserFirst >> comment [

^ '$(' asPParser trim , #any asPParser starLazy flatten  , '$)' asPParser trim ==> 

	[ :x | 
	
		
	
		"com :=" MmCommentModel new body: x second . 
		"Db lastComment: com .
		com."
	]


]

{ #category : #accessing }
MmPP2ParserFirst >> constant [

^ '$c' asPParser trim , #any asPParser starLazy flatten , '$.' asPParser trim ==> 

	[ :x | MmConstantModel new name: x second ]
]

{ #category : #accessing }
MmPP2ParserFirst >> distinct [

^ '$d' asPParser trim , #any asPParser starLazy flatten , '$.' asPParser trim ==> 

	[ :x | MmConstantModel new name: x second ]
]

{ #category : #generated }
MmPP2ParserFirst >> essentialHypothesis [

^  label , '$e' asPParser trim ,  #any asPParser starLazy flatten  , '$.' asPParser trim ==> 

	[ :x | MMEHypoth new name: x first ; rawString: x third  ; varNames: VarNames copy .
		
	]
]

{ #category : #generated }
MmPP2ParserFirst >> floatingHypothesis [

^  label , '$f' asPParser trim ,  #any asPParser starLazy flatten  , '$.' asPParser trim ==> 

	[ :x | MMFHypoth new name: x first ; rawString: x third  ; varNames: VarNames copy .
		
	]
]

{ #category : #initialization }
MmPP2ParserFirst >> initialize [ 

	super initialize .
	AllAssertions := OrderedDictionary new.
	
	AllProofs := OrderedDictionary new.

	VarNames := Set new .

	"VarDict := Dictionary new"
]

{ #category : #generated }
MmPP2ParserFirst >> label [

"^ #word asPParser plus flatten trim ==> "

^ (#word asPParser plus, ( $- asPParser / $. asPParser, #word asPParser plus ) plus optional) flatten ==>

	[ :x | "Transcript show: x ; cr" x
		
	]

]

{ #category : #generated }
MmPP2ParserFirst >> proof [

| thing |
^  label , '$p' asPParser trim ,  #any asPParser starLazy flatten , '$=' asPParser trim , $( asPParser trim , #any asPParser starLazy flatten , "label star ," $) asPParser trim , #any asPParser starLazy flatten , '$.' asPParser trim ==> 

	[ :x | thing := MMProof new  name: x first ; rawString: x third  ; varNames: VarNames copy ; prevAssertions: AllAssertions copy ; prevProofs: AllProofs  copy  ;  assertionsUsed: (x at: 6) .
	
		AllProofs at: x first put: thing .
		
		thing
		
	]
]

{ #category : #accessing }
MmPP2ParserFirst >> scope [

^ '${' asPParser trim , ( scope / comment / constant / variable / floatingHypothesis / essentialHypothesis / distinct / assertion / proof )  star , '$}' asPParser trim ==> 

	[ :x | 
		MmScopeModel new withr: x second ; varNames: VarNames copy ; allProofs: AllProofs copy ; allAssertions: AllAssertions copy .
		
		]
]

{ #category : #accessing }
MmPP2ParserFirst >> start [

^ scope star end
]

{ #category : #generated }
MmPP2ParserFirst >> variable [

^ '$v' asPParser trim , #any asPParser starLazy flatten  , '$.' asPParser trim ==> 

	[ :x | 
			"Db addVariable: x second ."
	
		 	"self halt ."
	
		VarNames add: x second.
		
		MmCommentModel new body: x second .
		
	]
]
