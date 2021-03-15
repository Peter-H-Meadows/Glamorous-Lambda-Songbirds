Class {
	#name : #MMEHypoth,
	#superclass : #MMHypoth,
	#instVars : [
		'pmod'
	],
	#category : #'Metamath-Model'
}

{ #category : #accessing }
MMEHypoth >> addInScope: scope [

scope addEhypothInScope: self
]

{ #category : #'as yet unclassified' }
MMEHypoth >> addTo: proof [
	proof addEHypoth: self
]

{ #category : #'as yet unclassified' }
MMEHypoth >> assertionAndEssentialHypothesisElement: c [


self error .

^ self usableElement: c
]

{ #category : #accessing }
MMEHypoth >> body [
	^ body
]

{ #category : #accessing }
MMEHypoth >> body: anObject [
	body := anObject
]

{ #category : #accessing }
MMEHypoth >> canMapTo2: thing [

body size = thing body size ifFalse: [ ^ false ] .

body with: thing body do: [ :eame :eastuff | ( eame canMapTo: eastuff ) ifFalse: [ ^ false ] ] .

^ true .


]

{ #category : #accessing }
MMEHypoth >> canMapTo: thing [

"if complete tell owner"
thing mappedTo: self .
canMap := body canMapTo: thing body . 

canMap ifTrue: [
	
	isComplete := thing isComplete .

	thing isEhypoth  ifTrue: [ isComplete := true ].

"assertion without ehypoths could also make complete"

].

isComplete ifTrue: [ 
	
	owner hypothIsComplete: self .
] .

^ canMap


]

{ #category : #'as yet unclassified' }
MMEHypoth >> elementForStartingList [

^ MmOnBoardEssentialHypothesisElement new model: self .
]

{ #category : #'as yet unclassified' }
MMEHypoth >> elementForStartingList: c [

^ self usableElement: c
]

{ #category : #accessing }
MMEHypoth >> gameElement [

^ MmEssentialHypothesisElement new initializeWith: self 

"^ MmEssentialHypothesisElement new model: self ; name: name ; body: body last gameElement ."

"^ body last gameElement  "
]

{ #category : #accessing }
MMEHypoth >> gameElementInCont [

^ MmEssentialHypothesisElement new model: self ; name: name ; body: body last gameElement .

"^ body last gameElement  "
]

{ #category : #accessing }
MMEHypoth >> gameElementInCont: controller [

| el aEventListener |
"el := MmEssentialHypothesisElement new model: self ; name: name ; body: body gameElement ."

el := MmEssentialHypothesisElement new initializeWith: self .
el controller: controller .

aEventListener := MmOnBoardWantedEventListener new gameController: controller .
el addEventHandler: aEventListener .
	
"el constraintsDo: [ :c | c linear horizontal  alignCenter ]."


^ el
]

{ #category : #accessing }
MMEHypoth >> gameElementInCont: controller pmod: p [

| el aEventListener |

pmod := p .

"el := MmEssentialHypothesisElement new model: self ; name: name ; body: body gameElement ."

el := MmEssentialHypothesisElement new initializeWith: self .
el controller: controller .

aEventListener := MmOnBoardWantedEventListener new gameController: controller .
el addEventHandler: aEventListener .
	
"el constraintsDo: [ :c | c linear horizontal  alignCenter ]."

el constraintsDo: [ :co |
			co horizontal matchParent ];
		background: BlTransparentBackground new .


^ el
]

{ #category : #testing }
MMEHypoth >> isEhypoth [

^ true
]

{ #category : #'as yet unclassified' }
MMEHypoth >> makeElements: aMmGameController [ 
	^ { self gameElement }
]

{ #category : #'as yet unclassified' }
MMEHypoth >> makerIsComplete [

isComplete := true .

owner hypothIsComplete: self .
]

{ #category : #accessing }
MMEHypoth >> onBoardGameElement [

"^ MmEssentialHypothesisElement new model: self ; name: name ; body: body last gameElement ."

^ MmOnBoardEssentialHypothesisElement new model: self
]

{ #category : #parsing }
MMEHypoth >> parse [

body  := parser  parse: rawString .

]

{ #category : #accessing }
MMEHypoth >> pmod [
^ pmod 
]

{ #category : #printing }
MMEHypoth >> printOn: aStream [
	aStream nextPutAll: rawString  .
]

{ #category : #accessing }
MMEHypoth >> setAllVarsLevel: n [

vars do: [ :e | e level: n ]
]
