Class {
	#name : #MmEssentialHypothesisElement,
	#superclass : #AbstractHypothesisElement,
	#category : #'Metamath-Bloc'
}

{ #category : #'instance creation' }
MmEssentialHypothesisElement class >> on: aHypoth [
	^ self new initializeWithHypoth: aHypoth
]

{ #category : #accessing }
MmEssentialHypothesisElement >> borderColor [

^ Color veryVeryDarkGray  
]

{ #category : #accessing }
MmEssentialHypothesisElement >> borderWidth [ 

^ 0
]

{ #category : #testing }
MmEssentialHypothesisElement >> canMap: ann [

self markSuccess 
]

{ #category : #initialization }
MmEssentialHypothesisElement >> initializeWith: aHypothModel [

model := aHypothModel .

self margin: (BlInsets all: 2).

self addChildFirst: selectedMarkerElement .

self addChild: model body gameElement 
]

{ #category : #deprecated }
MmEssentialHypothesisElement >> initializeWithHypoth: aHypoth [

| aText |

self error .

model := aHypoth .

self margin:  (BlInsets all: 4).

"aText := aHypoth name asRopedText .

aText fontSize: 30.
aText foreground: Color veryLightGray .

textElement := (BlTextElement text: aText) constraintsDo: [ :c | 
					c linear vertical alignCenter ]."

"self addChild: textElement ."

self addChild: aHypoth body gameElement 
]

{ #category : #accessing }
MmEssentialHypothesisElement >> initializef [

| mmodel look |
super initialize .

	mmodel := BrWithContextMenuModel new
		stencil: [ BlElement new
				look:
					(BrGlamorousContextMenuLook new
						content:
							(BrGlamorousSimpleContextMenuContent new
								display:
									{
									
									('inspect' -> [ :e | self inspect . "model remove" "gameModel tryUse: self" ]).
									('remove' -> [ :e | e removeFromParent ]).
									('Change to green' -> [ :e | e background: Color green ])
									
									
									};
								yourself);
						yourself);
				yourself ];
		yourself.
	self assert: mmodel visible equals: false.
	
	look := BrWithContextMenuLook new.
	self assert: look visible equals: false.
	self assert: (look stencil asStencil asElement isKindOf: BlElement).
	
	self viewModel: mmodel.
	self look: look.
]

{ #category : #'instance creation' }
MmEssentialHypothesisElement >> success [

| aText |
aText := ' done ' asRopedText .
aText fontSize: 30.
aText foreground: Color green .
textElement := (BlTextElement text: aText) constraintsDo: [ :c |c linear vertical alignCenter ].
self addChildFirst: textElement .

self requestParentLayout .
]

{ #category : #accessing }
MmEssentialHypothesisElement >> tryMakeFromOnBoardeHypothEl: el [ 

| animation dum diff |
"we r an ehypoth element  of ax-mp . try to map to onBoardehypoth (fixed)"


self halt .
			
dum := BlElement new size: el size .
dum background: BlTransparentBackground new.
self addChildFirst: dum .

"1 seconds asDelay wait."

diff := dum positionInSpace - el positionInSpace.

"self halt ."

animation := BlTransformAnimation new.
	animation transform
		translateBy: diff ;
		apply. 
		
		animation onFinishedDo: [ 
		
			"1 seconds asDelay wait."
			
			
			
			dum removeFromParent .
			el removeFromParent .
			el transformation: (el defaultTransformation "owner: el") .
			self addChildFirst: el .			
			
			"self halt ."
			
		"ion := BlTransformAnimation new.
		animation transform
		translateBy: diff negated ;
		apply. el addAnimation: ion."

			"self halt ."

			self background:
			((model canMapTo:  el model) ifTrue: [Color green] ifFalse: [Color red]).
	 ].
		
el addAnimation: animation .

"1 seconds asDelay wait."

"self halt ."


]

{ #category : #'as yet unclassified' }
MmEssentialHypothesisElement >> tryMakeWith2: mod [
| el |

self halt .

mod isEhypoth ifTrue: [  
	el := mod assertionAndEssentialHypothesisElement: controller .
] ifFalse: [  
	el := mod copyAndClean assertionAndEssentialHypothesisElement: controller .
] .

self addChildFirst: el .

model canMapTo: el model.

]

{ #category : #'as yet unclassified' }
MmEssentialHypothesisElement >> tryMakeWith: mod [
| el |

self halt .

"usable el could be: 
ehypoth from proof were doing,
assertion from list,
assertion on board.

make sure it;s not in the same thing."

"parent parent = selectedUsableElement parent ifTrue: [ self error . ^ self ] ."

"we are ehypoth. usable could be proof,hypoth,assertion.."

"only remove if .."

"selectedUsableElement all removeFromParent ."

"add as trying thing"

"self addChildFirst: selectedUsableElement ."

"selectedUsableElement model canMapTo: model."

"el := mod pcopy assertionAndEssentialHypothesisElement: controller .
self addChildFirst: el .
model canMapTo: el model."

el := mod pcopy assertionAndEssentialHypothesisElement: controller .
self addChildFirst: el .
el model canMapTo: model.

"el model canMapTo: model."

]

{ #category : #accessing }
MmEssentialHypothesisElement >> tryMakeWithEl: el [ 


			el removeFromParent .
			self addChildFirst: el .	
				
			"1 seconds asDelay wait."
				
			(el model canMapTo: model) ifFalse: [ "self background: Color red" self border: (BlBorder paint: Color red width: 4 ). ].
			
			"1 seconds asDelay wait."
			
			model isComplete ifTrue: [ self background: Color veryDarkGray ].

			"self background:
			((model canMapTo:  el model) ifTrue: [Color green] ifFalse: [Color red])."
			
			"el model canMapTo: model."
			
"1 seconds asDelay wait."

"self halt ."

]

{ #category : #accessing }
MmEssentialHypothesisElement >> tryMakeWithElAnime: el [ 

| animation dum diff |

"we r an ehypoth element  of ax-mp . try to map to AssertionAndEssentialHypothesisElement "
"animate el moving into me. then (model canMapTo:  el model)"

dum := BlElement new size: el size .
dum background: BlTransparentBackground new.
self addChildFirst: dum .

"1 seconds asDelay wait."

diff := dum positionInSpace - el positionInSpace.

"self halt ."

animation := BlTransformAnimation new.
	animation transform
		translateBy: diff ;
		apply. 
		
		animation onFinishedDo: [ 
		
			"1 seconds asDelay wait."
			
			dum removeFromParent .
			el removeFromParent .
			el transformation: el defaultTransformation .
			self addChildFirst: el .	
				
				1 seconds asDelay wait.
				
			(model canMapTo: el model) ifFalse: [ self background: Color red ].
			
			model isComplete ifTrue: [ self background: Color veryDarkGray ].

			"self background:
			((model canMapTo:  el model) ifTrue: [Color green] ifFalse: [Color red])."
			
			"el model canMapTo: model."
	 ].
		
el addAnimation: animation .

"1 seconds asDelay wait."

"self halt ."

]

{ #category : #'as yet unclassified' }
MmEssentialHypothesisElement >> tryMakeWithFromBoard: selectedUsableElement [

self error.

"usable el could be: 
ehypoth from proof were doing,
assertion from list,
assertion on board.

make sure it;s not in the same thing."

parent parent = selectedUsableElement parent ifTrue: [ self error . ^ self ] .

"we are ehypoth. usable could be proof,hypoth,assertion.."

"only remove if .."

selectedUsableElement all removeFromParent .

"add as trying thing"

self addChildFirst: selectedUsableElement all .

selectedUsableElement model canMapTo: model.
]
