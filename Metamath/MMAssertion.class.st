Class {
	#name : #MMAssertion,
	#superclass : #MMAssAndProof,
	#instVars : [
		'allFhypoths'
	],
	#category : #'Metamath-Model'
}

{ #category : #accessing }
MMAssertion >> addEHypoth: h [
self error .
essentialHypoths add: h.


"vars addAll: (h setLevel: 1)"
]

{ #category : #accessing }
MMAssertion >> addInScope: scope [ 
essentialHypoths := scope ehypoths . 
	scope addAssertionInScope: self .
	"self setupMandatoryFloatingHypothesis ."

]

{ #category : #accessing }
MMAssertion >> addThing: h [

essentialHypoths add: h .

"h setVarSyms ."
]

{ #category : #accessing }
MMAssertion >> allFhypoths [ 

^ allFhypoths 
]

{ #category : #accessing }
MMAssertion >> announcer [
^ announcer ifNil: [ announcer := Announcer new ]
]

{ #category : #'as yet unclassified' }
MMAssertion >> assertion [
	^ self
]

{ #category : #accessing }
MMAssertion >> body [
	^ body
]

{ #category : #accessing }
MMAssertion >> body: anObject [
	body := anObject
]

{ #category : #accessing }
MMAssertion >> calcMandFhypoths [

mandFhypoths := Array new .

mandFhypoths := allFhypoths select: [ :ea | ea hasVarFrom: vars  ] .
]

{ #category : #accessing }
MMAssertion >> calcMandFhypoths: fs [

self error .

allFhypoths := fs copy .

mandFhypoths := Array new .

self setVarSyms  .

mandFhypoths := allFhypoths select: [ :ea | ea hasVarFrom: vars  ] .
]

{ #category : #deprecated }
MMAssertion >> canMapTogui: thing [

| aSpace mainBox |
body size = thing body size ifFalse: [ ^ false ] .

	aSpace := BlSpace new
		extent: 600@600;
		title: 'metamath'.
	
	"aSpace root background: self spaceBackground."

	"aSpace root addEventHandler:
			(BlEventHandler
				on: BlDoubleClickEvent
				do: [ :evt | BlElementSelection on: evt target ])."
	
	aSpace show .

mainBox := BlElement new .

mainBox constraintsDo: [ :c | 
					c horizontal fitContent.
					c vertical fitContent ];
		"padding: (BlInsets all: 2);"
		margin: (BlInsets left: 18) ;
		layout: BlLinearLayout vertical   .

aSpace root addChild: mainBox .

mainBox addChild: self blocElement .
mainBox addChild: thing blocElement .

body with: thing body do: [ :eame :eastuff | ( eame canMapTogui: eastuff ) ifFalse: [ ^ false ] ] .

^ true .


]

{ #category : #accessing }
MMAssertion >> eHypoths [

^ essentialHypoths
]

{ #category : #accessing }
MMAssertion >> gameElement [

^ MmAssertionElement new initializeWith: self.

]

{ #category : #accessing }
MMAssertion >> initialize [ 

super initialize  .

essentialHypoths := OrderedCollection new .


]

{ #category : #accessing }
MMAssertion >> mandFhypoths [


"mandFhypoths := allFhypoths select: [ :ea | ea hasVarFrom: vars  ] ."

^ mandFhypoths
]

{ #category : #accessing }
MMAssertion >> mands [

^ essentialHypoths reverse , mandFhypoths  
]

{ #category : #accessing }
MMAssertion >> printOn: aStream [
	aStream nextPutAll: rawString  .
]

{ #category : #accessing }
MMAssertion >> resetFlags [

body last resetFlags
]

{ #category : #accessing }
MMAssertion >> scopeContent: x [

x do: [ :ea |
	
	ea addTo: self .
	
	 ]
]

{ #category : #deprecated }
MMAssertion >> setAllVarsLevel: n [

self error .

vars do: [ :e | e level: n ]
]
