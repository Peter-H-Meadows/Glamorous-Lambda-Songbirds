Class {
	#name : #MmPP2Parser,
	#superclass : #PP2CompositeNode,
	#instVars : [
		'comment',
		'constant',
		'variable',
		'label',
		'floatingHypothesis',
		'scope',
		'assertion',
		'essentialHypothesis',
		'proof',
		'primary',
		'parentheses',
		'squareBrackets',
		'label2',
		'distinct',
		'curlyBraces',
		'proveable',
		'wff',
		'la',
		'list',
		'emptySet',
		'label3'
	],
	#classVars : [
		'AllAssertions',
		'AllProofs',
		'VarDict',
		'VarNames'
	],
	#category : #'Metamath-Parsing'
}

{ #category : #accessing }
MmPP2Parser >> assertion [

| mma |
	^  label , '$a' asPParser trim , ( wff / proveable ) trim , '$.' asPParser trim ==> 

	[ :x | 
	
		mma := MMAssertion new name: x first ; body: x third ; prevAssertions: AllAssertions copy .
		AllAssertions at: mma name put: mma . 
		"Db addAssertion: mass ."
		
		]
]

{ #category : #accessing }
MmPP2Parser >> comment [

| com |
^ '$(' asPParser trim , #any asPParser starLazy flatten  , '$)' asPParser trim ==> 

	[ :x | 
	
		x second first = $= ifTrue: [ 
		
			"self halt .
		
			x second lines second ."
		
		] .
		
	
		"com :=" MmCommentModel new body: x second . 
		"Db lastComment: com .
		com."
	]


]

{ #category : #accessing }
MmPP2Parser >> constant [

^ '$c' asPParser trim , #any asPParser starLazy flatten , '$.' asPParser trim ==> 

	[ :x | MmConstantModel new name: x second ]
]

{ #category : #accessing }
MmPP2Parser >> curlyBraces [
	^ ${ asPParser trim , list , $} asPParser trim ==> 

		[ :x | MmCurlyBracesModel new body: x second ]
]

{ #category : #accessing }
MmPP2Parser >> distinct [

^ '$d' asPParser trim , #any asPParser starLazy flatten , '$.' asPParser trim ==> 

	[ :x | MmConstantModel new name: x second ]
]

{ #category : #accessing }
MmPP2Parser >> emptySet [
	^ "$( asPParser , $/ asPParser , $)" '(/)' asPParser flatten  trim ==> 

		[ :x | "Db varOrConst:" x ]
]

{ #category : #accessing }
MmPP2Parser >> essentialHypothesis [

^  label , '$e' asPParser trim , proveable trim , '$.' asPParser trim ==> 

	[ :x | MMEHypoth new name: x first ; body: x third .
		
	]
]

{ #category : #accessing }
MmPP2Parser >> floatingHypothesis [

^  label , '$f' asPParser trim , label , label , '$.' asPParser trim ==> 

	[ :x | MMFHypoth new name: x first ; type: x third varName: x fourth .

		"Db addFhypoth: ee .
		
		ee . "
	]
]

{ #category : #initialization }
MmPP2Parser >> initialize [ 

	super initialize .
	AllAssertions := Dictionary new.
	AllProofs := OrderedCollection new.
	"Db := MmDatabase new ."
	
	VarNames := Set new .
	VarDict := Dictionary new
	
]

{ #category : #accessing }
MmPP2Parser >> la [

"^ #word asPParser plus trim , #any asPParser starLazy flatten  , #space asPParser trim "

"^ (#word asPParser plus , #space asPParser negate plus optional) trim flatten / '->' asPParser trim ."

"this should just parse any alphanumeric? but (+) can be label and they can have dots etc"

"^ ( #space asPParser / $$ asPParser / $( asPParser / $) asPParser ) negate plus flatten trim ==> "

^ ( #space asPParser negate , #space asPParser negate plus ) flatten trim ==>



	[ :x | Db varOrConst: x ]


]

{ #category : #accessing }
MmPP2Parser >> label [

"^ #word asPParser plus flatten trim "

^ ( #space asPParser  / $$ asPParser / $( asPParser / $) asPParser ) negate plus flatten trim

"^ (#word asPParser plus, ( $- asPParser / $. asPParser, #word asPParser plus ) plus optional) flatten "

"^ (#word asPParser ,	( #space asPParser ) negate plus flatten trim ) flatten"
	
"^ #word asPParser plus trim flatten"

"^ (#word asPParser plus trim , ( $- asPParser / $. asPParser ) optional) trim flatten"

"( ( $- asPParser / $. asPParser ) , #word asPParser plus) optional , ( ( $- asPParser / $. asPParser ) , #word asPParser plus) optional) flatten 
"

]

{ #category : #accessing }
MmPP2Parser >> label2 [

"^ #word asPParser plus trim , #any asPParser starLazy flatten  , #space asPParser trim "

"^ (#word asPParser plus , #space asPParser negate plus optional) trim flatten / '->' asPParser trim ."

"this should just parse any alphanumeric? but (+) can be label and they can have dots etc"

^ ( #space asPParser / $$ asPParser / $( asPParser / $) asPParser / ${ asPParser / $} asPParser / $[ asPParser / $] asPParser) negate plus flatten trim ==>


	[ :x | " Db varOrConst: x" 
	
		(VarNames includes: x) ifTrue: [  
	
			 VarDict at: x ifAbsentPut: [ MmAbstractVariableModel new name: x ]

		] ifFalse: [

 			MmConstantModel new name: x .
		]
	]


]

{ #category : #accessing }
MmPP2Parser >> label3 [

"^ #word asPParser plus trim , #any asPParser starLazy flatten  , #space asPParser trim "

"^ (#word asPParser plus , #space asPParser negate plus optional) trim flatten / '->' asPParser trim ."

"this should just parse any alphanumeric? but (+) can be label and they can have dots etc"

"^ ( #space asPParser / $$ asPParser / $( asPParser / $) asPParser ) negate plus flatten trim ==>" 

"^ #word asPParser plus flatten trim ==>"

^  (#space asPParser ) negate plus flatten trim ==>

	[ :x | Db varOrConst: x ]


]

{ #category : #accessing }
MmPP2Parser >> list [
	^ primary plus trim ==> 

		[ :x | MmListModel new body: x ]
]

{ #category : #accessing }
MmPP2Parser >> parentheses [
	^ $( asPParser trim ", #space asPParser trim" , list , $) asPParser ", #space asPParser" trim ==> 

		[ :x | MmParensModel new body: x second . ]

]

{ #category : #accessing }
MmPP2Parser >> primary [
	^  emptySet / parentheses / squareBrackets / curlyBraces / label2 
]

{ #category : #accessing }
MmPP2Parser >> proof [

| mproof |
	^ label , '$p' asPParser , ( wff / proveable ) trim , '$=' asPParser trim, $( asPParser , label star , $) asPParser, #any asPParser starLazy flatten , '$.' asPParser trim ==> 

	[ :x |

"self halt ."
		
		mproof := MMProof new name: x first ; body: x third ; prevAssertions: AllAssertions copy ;  assertionsUsed: (x at: 6) .
		
		"mproof lastComment: Db lastComment ."
		
		AllAssertions at: mproof name put: mproof .
		AllProofs add: mproof .
		
		mproof  ]
]

{ #category : #accessing }
MmPP2Parser >> proveable [

^ '|-' asPParser trim , list ==> 

	[ :x |
	
		MmProveableModel new body: x second 
	
	] 
]

{ #category : #accessing }
MmPP2Parser >> scope [

^ '${' asPParser trim , ( constant / variable / floatingHypothesis / essentialHypothesis / distinct / assertion / proof / variable / comment / scope ) star , '$}' asPParser trim ==> 

	[ :x | 
		MmScopeModel new with: x second ; allProofs: AllProofs  copy ]
]

{ #category : #accessing }
MmPP2Parser >> squareBrackets [
	^ $[ asPParser trim , list , $] asPParser trim ==> 

		[ :x | MmSquareBracetsModel new body: x second . ]
]

{ #category : #accessing }
MmPP2Parser >> start [

"^ (comment / constant / variable / floatingHypothesis / assertion / proof / scope) star end ==> [ :x | Db ]"
^ scope star end "==> [ :x | Db ]"
]

{ #category : #accessing }
MmPP2Parser >> variable [

^ '$v' asPParser trim , #any asPParser starLazy flatten  , '$.' asPParser trim ==> 

	[ :x | 
			"Db addVariable: x second ."
	
		 	"self halt ."
	
		VarNames add: x second.
		MmCommentModel new body: x second .
		
	]
]

{ #category : #accessing }
MmPP2Parser >> wff [

^ ('wff' asPParser trim / 'class' asPParser trim) , list ==> 

	[ :x | 
	
		MmWffModel new body: x second 
	
	] 
]
