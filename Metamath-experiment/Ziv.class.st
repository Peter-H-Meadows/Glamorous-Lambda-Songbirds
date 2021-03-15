Class {
	#name : #Ziv,
	#superclass : #Object,
	#instVars : [
		'width',
		'places'
	],
	#classVars : [
		'Mon',
		'Zivs'
	],
	#category : #'Metamath-experiment'
}

{ #category : #accessing }
Ziv >> allCombinations [
| x |
x := OrderedCollection new .
	1 to: places size do:
				[ :take | places combinations: take atATimeDo: [ :combination | x add: ( Ziv new with: combination ) ] ] .
	"self halt ."
^ x

]

{ #category : #accessing }
Ziv >> allEnvCombinations [
Zivs := { } .
self halt .
self col: {} pos: 1 .
^ Zivs
]

{ #category : #accessing }
Ziv >> col: col pos: pos [

| diff nn |
	pos = (places size + 1) ifTrue: [ ^ col ] .

diff := places size - pos.
nn := self envPlace: pos times: diff .
Zivs addAll: nn .
nn do: [ :ea | ea col: col pos: pos - 1 ].

]

{ #category : #accessing }
Ziv >> draw [


	Mon topStep addChildren: { self el }.

]

{ #category : #accessing }
Ziv >> el [

| el |
el := BlElement new border: (BlBorder paint: Color black) .
el constraintsDo: [ :c | 
					c horizontal fitContent.
					c vertical fitContent .
					c linear vertical alignCenter ];
		"padding: (BlInsets all: 0);
		margin: (BlInsets all: 0);"
		layout: BlLinearLayout horizontal  .
el geometry: BlEllipse new.

el padding: (BlInsets all: 8).

el border: (BlBorder paint: Color black width: 1 ).
	"el := BrHorizontalPane new border: (BlBorder paint: Color black) ."
	places do: [ :ea | el addChild: ea el ].
	^ el
]

{ #category : #accessing }
Ziv >> env [
^ Ziv new with: self
]

{ #category : #accessing }
Ziv >> envPlace: pp [
^ places at: pp put: ((places at: pp) env)

]

{ #category : #accessing }
Ziv >> envPlace: pp times: xx [
^ xx timesCollect: [ self copy envPlace: pp ]
]

{ #category : #accessing }
Ziv >> mon: m [
Mon := m
]

{ #category : #accessing }
Ziv >> subsets [

]

{ #category : #accessing }
Ziv >> with: list [
places := list copy . 
]

{ #category : #accessing }
Ziv >> with: aa with: bb [
places := { aa . bb}
]

{ #category : #accessing }
Ziv >> with: aa with: bb with: cc [
places := { aa . bb. cc }
]

{ #category : #accessing }
Ziv >> xx [
| times col |

times := width.
	
1 to: width do: [ :pp | 
	col := self envPlace: pp times: times.
	col last draw .	
		
	times := times - 1 .	
	].
	
]

{ #category : #accessing }
Ziv >> xxx: pos [
| times col |

pos = width ifTrue: [ ^ #( ) ] .
	
col := self envPlace: pos + 1 times: times - 1 .

col isEmpty ifTrue: [ ^ self ] .

]
