Class {
	#name : #MmOnBoardProofElement,
	#superclass : #MmProofElement,
	#category : #'Metamath-Bloc'
}

{ #category : #accessing }
MmOnBoardProofElement >> highlightAsSelected [ 

selectedMarkerElement := BlElement new
		constraintsDo: [ :c |
			c horizontal exact: 8.
			c vertical matchParent ];
		background: ( Color gray ).
		
self addChildFirst: selectedMarkerElement .
		
]

{ #category : #initialization }
MmOnBoardProofElement >> iiinitializeWithProof: aAssertion [

| aText el box |

self model: aAssertion .

box := BlElement new layout: BlLinearLayout vertical .

"self padding: (BlInsets all: 4).
self margin: (BlInsets all: 4)."

box constraintsDo: [ :c | 
					c horizontal fitContent.
					c vertical fitContent ].


el := aAssertion body gameElement . 
el constraintsDo: [ :c | c linear horizontal alignCenter ].

box addChild: el .

aAssertion lastComment body linesDo: [ :line | 

aText := line asRopedText .

aText fontSize: 18.
aText foreground: Color veryLightGray .
textElement := (BlTextElement text: aText) "constraintsDo: [ :c | c linear horizontal alignCenter ]".
box addChild: textElement .

] .

self addChild: box .

]

{ #category : #accessing }
MmOnBoardProofElement >> tryMakeWith: mod [
| el |
 mod isEhypoth ifTrue: [ ^ self ] .

"selectedUsableElement all removeFromParent ."

el := mod pcopy assertionAndEssentialHypothesisElement: controller .

self addChildFirst: el .

el model canMapTo: model.
]

{ #category : #accessing }
MmOnBoardProofElement >> tryMakeWithEl: el [ 
el removeFromParent .
self addChildFirst: el .
model canMapTo: el model.

			"self background:
			((model canMapTo: el model) ifTrue: [Color green] ifFalse: [Color red] )."
			
"1 seconds asDelay wait."

"self halt ."

]
