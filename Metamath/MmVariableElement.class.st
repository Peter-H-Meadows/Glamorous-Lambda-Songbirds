Class {
	#name : #MmVariableElement,
	#superclass : #MmRawElement,
	#instVars : [
		'textElement',
		'blob',
		'lineElement'
	],
	#classVars : [
		'Colors'
	],
	#category : #'Metamath-Bloc'
}

{ #category : #'class initialization' }
MmVariableElement class >> initialize [ 

		
Colors := Dictionary new 
				at: 'A' put: Color red ;
				at: 'B' put: Color green ;
				at: 'C' put: Color blue ; 
				at: 'D' put: Color gray ;
				at: 'E' put: Color purple ;
				at: 'F' put: Color random ;
				yourself.
]

{ #category : #'instance creation' }
MmVariableElement class >> on: aVariable [ 
	^ self new initializeWithVariable: aVariable
]

{ #category : #mapping }
MmVariableElement >> failedToMap: ann [ 
| aText |
"self inform: ann reason."

self hi: Color red.

"textElement removeFromParent .

aText := (model abname, ann reason) asRopedText .
aText fontSize: 18.
aText foreground: Color red .
textElement := (BlTextElement text: aText) constraintsDo: [ :c | c linear horizontal alignCenter ].
self addChild: textElement ."


"self addChild: ann mappedTo gameElement "
]

{ #category : #highlighting }
MmVariableElement >> highlight [ 

self background: Color veryDarkGray .

]

{ #category : #accessing }
MmVariableElement >> initialize [

super initialize .

self "geometry: BlRectangle new;"
		
		background: BlTransparentBackground new ;
		constraintsDo: [ :c | 
					c horizontal fitContent.
					c vertical fitContent .
					c linear vertical alignCenter ];
		
		layout: BlLinearLayout  vertical .

				
]

{ #category : #initialization }
MmVariableElement >> initializeWithVariable: aVariableModel [
| aText col box geometryClass abDict |

model := aVariableModel .

"model checkLoop ."

model announcer when: MmHighlightAnnouncement send: #highlight to: self.
model announcer when: MmVariableMappedAnnouncement send: #mapped: to: self.
model announcer when: MmFailedToMapAnnouncement send: #failedToMap: to: self.

self  margin: (BlInsets all: 4).

"aVariable identityHash printString"

	
	"col := Colors at: aVariable name ifAbsentPut: [ Color random ] ."
	
	geometryClass := model fixed ifTrue: [ BlRoundedRectangleGeometry ] ifFalse: [ BlCircle ] .
	
	blob := BlElement new
		"geometry: BlSquare new;"
		geometry: geometryClass new;
		background: model color " col"
		"border: (BlBorder paint: (Color blue alpha: 0.5) width: 6)" ;
		"size: 30@30;"
		constraintsDo: [ :c | 
					c horizontal exact: 30 . "fitContent".
					c vertical exact: 30 . "fitContent" .
					c linear "vertical" horizontal  alignCenter .
					c linear vertical alignCenter ].
				

abDict := Dictionary newFromPairs: {'ph' . 'R' . 'ps' . 'G' . 'ch' . 'B' . 'th' . 'D'. 'ta' . 'E' . 'et' . 'F' . 'G' . 'ze'} .

"aText := (model name , model identityHash printString) asRopedText ."

aText := (abDict at: model name) asRopedText .
aText fontSize: 18.
aText foreground: Color black .

textElement := (BlTextElement text: aText) constraintsDo: [ :c | c linear vertical alignCenter . c linear horizontal  alignCenter ].
textElement  margin: (BlInsets all: 8).

blob layout: BlLinearLayout horizontal  .

blob addChild: textElement .

				
self addChild: blob .

model mapped ifTrue: [ 
	
	
	"box := BlElement new layout: BlLinearLayout horizontal .

	box constraintsDo: [ :c | 
						c horizontal fitContent.
						c vertical fitContent ].

	model mappedTo do: [ :ea |
		box addChild: ea gameElement
	]."


	self addChild: model mappedTo gameElement.
	
	
] .


	"textElement := (BlTextElement text: aText) constraintsDo: [ :c | c linear horizontal alignCenter ].
	self addChild: textElement ."
	



	"model fixed ifTrue: [  
			
		
		aText := '+' asRopedText .
		aText fontSize: 20.
		aText foreground: Color black   .
		textElement := (BlTextElement text: aText) constraintsDo: [ :c | c linear vertical alignCenter ]."

		"textElement := BlElement new background: (Color black) ; constraintsDo: [ :c | 
		c vertical exact: 4. 
		c horizontal matchParent . 
		c linear vertical alignCenter ].


		blob layout: BlLinearLayout horizontal  .
		blob addChild: textElement .	
			
	] ."




]

{ #category : #initialization }
MmVariableElement >> mapped [
]

{ #category : #mapping }
MmVariableElement >> mapped: ann [ 

"blob border: ( BlBorder paint: Color black width: 4 )."

lineElement := BlElement new
		constraintsDo: [ :c |
			c horizontal matchParent.
			c vertical exact: 1 ];
		background: Color lightGray .

self addChild: lineElement .

self addChild: ann mappedTo gameElement.

]

{ #category : #accessing }
MmVariableElement >> unHighlight [ 

self background: Color veryVeryDarkGray .


]
