Class {
	#name : #MMAssAndProof,
	#superclass : #MMAbstractThing,
	#instVars : [
		'mandFhypoths',
		'essentialHypoths',
		'fHypoths',
		'mmxx',
		'prevAssertions',
		'varsUsed',
		'prevProofs'
	],
	#category : #'Metamath-Model'
}

{ #category : #'as yet unclassified' }
MMAssAndProof >> allVariableNames [

^ (self allVariables collect: [ :ea | ea name ] ) asSet .


]

{ #category : #accessing }
MMAssAndProof >> allVariables [ 

^ self localVariables , self hypothVariables
]

{ #category : #accessing }
MMAssAndProof >> assertionAndEssentialHypothesisElement [
self halt .
^ AssertionAndEssentialHypothesisElement new model: self
]

{ #category : #initialization }
MMAssAndProof >> assertionAndEssentialHypothesisElement: c [
"self halt ."
^ (AssertionAndEssentialHypothesisElement new initializeWith: self) addHandlersController: c "controller: c"
]

{ #category : #cleaning }
MMAssAndProof >> clean [ 

self allVariables do: [ :ea | ea clean ]
]

{ #category : #accessing }
MMAssAndProof >> eel [
"MmGame new openGame: anEvent currentTarget model name."
| aEventListener el |
el := AssertionAndEssentialHypothesisElement new initializeWith: self .
	aEventListener := MmStartEventListener new .

				el addEventHandler: aEventListener .
^ el
]

{ #category : #accessing }
MMAssAndProof >> elementForStartingList [
"self halt ."
^ AssertionAndEssentialHypothesisElement new initializeWith: self ; background: Color white "model: self controller2: c"
]

{ #category : #accessing }
MMAssAndProof >> elementForStartingList: c [
self halt .
^ AssertionAndEssentialHypothesisElement new initializeWith: self "model: self controller2: c"
]

{ #category : #accessing }
MMAssAndProof >> essentialHypoths [
^ essentialHypoths 
]

{ #category : #accessing }
MMAssAndProof >> essentialHypoths: h [

essentialHypoths := h.
essentialHypoths do: [ :ea | ea owner: self ]
]

{ #category : #accessing }
MMAssAndProof >> fHypoths [ 
^ fHypoths 
]

{ #category : #testing }
MMAssAndProof >> hasEhypoths [

^ essentialHypoths size > 0
]

{ #category : #accessing }
MMAssAndProof >> hypothIsComplete: h [
"if all e? hypoths r complete, tell owner.."


( essentialHypoths inject: true into: [ :sum :ea | ea isComplete & sum ] ) ifTrue: [

	"if we make the result we wanted, announce"
	
	"if we have owner tell them were complete"
	
	"self halt ."
	
	isComplete := true .
	
	mappedTo ifNotNil: [ mappedTo makerIsComplete ]

].

]

{ #category : #'as yet unclassified' }
MMAssAndProof >> hypothVariableNames [

^ (self hypothVariables collect: [ :ea | ea name ] ) asSet .


]

{ #category : #'as yet unclassified' }
MMAssAndProof >> hypothVariables [

"mandFhypoths ." 

| varSet |
varSet := Set new .

essentialHypoths do: [ :ea | varSet addAll: ea localVariables  ] .

^ varSet

]

{ #category : #initialization }
MMAssAndProof >> initialize [ 

super initialize .

essentialHypoths := OrderedCollection new .

fHypoths := OrderedCollection new .
]

{ #category : #deprecated }
MMAssAndProof >> makeElements [

"
aEventListener := MmOnBoardUsingEventListener new gameController: controller  ."

| myElement mand elements |

self error .


myElement := self gameElement "addEventHandler: aEventListener" .

elements := OrderedCollection with: myElement .
	
self mands reverse do: [ :ea | 
	
		mand := ea gameElement "addEventHandler: aEventListener" .
		elements add: mand .
		myElement graph connectTo: mand.

 ] .	


^ elements 

]

{ #category : #parsing }
MMAssAndProof >> parse [

body  := parser  parse: rawString .

varsUsed := parser class varsUsed copy .

"body class = PP2Failure ifTrue: [self halt]"
]

{ #category : #copying }
MMAssAndProof >> postCopy [ 

"body := body collect: [ :ea | ea copy ] ."

| nd |

"vars ifNil: ["  
	
	vars := Dictionary new .

	varsUsed do: [ :ea | vars at: ea put: (MmAbstractVariableModel  new name: ea )]	.
	
"]."

"nd := Dictionary new .
vars keysAndValuesDo: [ :kk :vv | nd at: kk put: vv copy ].
vars := nd ."

body := body copy vars: vars .



essentialHypoths := essentialHypoths collect: [ :ea | ea copy owner: self ; vars: vars  ] .

"fHypoths := fHypoths collect: [ :ea | ea copy ] ."

"mandFhypoths := mandFhypoths collect: [ :ea | ea copy ] ."

announcer := Announcer new
]

{ #category : #accessing }
MMAssAndProof >> prevAssertions [
^ prevAssertions
]

{ #category : #accessing }
MMAssAndProof >> prevAssertions: a [
prevAssertions := a
]

{ #category : #accessing }
MMAssAndProof >> prevProofs [
^ prevProofs 
]

{ #category : #accessing }
MMAssAndProof >> prevProofs: a [
prevProofs := a
]

{ #category : #initialization }
MMAssAndProof >> reColor [
]

{ #category : #initialization }
MMAssAndProof >> setAllVariablesToFixed [

vars do: #setFixed
]

{ #category : #initialization }
MMAssAndProof >> setAllVariablesToFree [

self allVariables do: #setFree
]

{ #category : #initialization }
MMAssAndProof >> setEhypothsAsCompleted [

essentialHypoths do: #setAsCompleted
]

{ #category : #'as yet unclassified' }
MMAssAndProof >> setupMandatoryFloatingHypothesis [

fHypoths := self allVariables asArray collect: [ :ea | MMFHypoth new createFrom: ea ] .
]

{ #category : #'as yet unclassified' }
MMAssAndProof >> setupMandatoryFloatingHypothesis: allFHypoths [

| tmpvars |
tmpvars := self allVariableNames .

"need to replace vars in fhypoths with new ones"

mandFhypoths := allFHypoths select: [ :ea | ea hasVarFrom: tmpvars  ] .

mandFhypoths := mandFhypoths collect: [ :ea | ea copyWithVars: self allVariables ]
]

{ #category : #accessing }
MMAssAndProof >> usableElement [
self halt .
^ AssertionAndEssentialHypothesisElement new initializeWith: self .


]

{ #category : #accessing }
MMAssAndProof >> usableElement: c [
"make element for usableThingsList."
| aEventListener el cc |

"cc := MmGameController new setupProof: self ."

self hasEhypoths ifTrue: [ 

	aEventListener := MmUsableEventListener new gameController: c .

	el := self gameElement addEventHandler: aEventListener .

	^ el showEssential .

] .

aEventListener := MmListUsableEventListener new gameController: c .

el := self gameElement addEventHandler: aEventListener .
el addStartingBracket .
^ el  .

]
