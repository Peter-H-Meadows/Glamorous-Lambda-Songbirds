"
Collection extend [
    power [
        ^(0 to: (1 bitShift: self size) - 1) readStream collect: [ :each || i |
            i := 0.
            self select: [ :elem | (each bitAt: (i := i + 1)) = 1 ] ]
    ]
].

https://rosettacode.org/wiki/Power_set#Smalltalk
"
Class {
	#name : #MmSetVizSet,
	#superclass : #Set,
	#category : #'Metamath-experiment'
}

{ #category : #converting }
MmSetVizSet >> asBlElement [ 

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
	self do: [ :ea | el addChild: ea asBlElement ].
	^ el
]

{ #category : #'as yet unclassified' }
MmSetVizSet >> drOn: v [

self do: [ :ea |  v topStep addChildren: { ea asBlElement } ].
]

{ #category : #accessing }
MmSetVizSet >> isWellFoundedByR: r [
	"for each of my subsets there must exist member that for all other members not zRy"

	"for each y, does all z conform to not zRy. if yes, highlite   y?"

	| powerSet z y |
	powerSet := self powerSet.
	"powerSet do: [ :ea | r includes: z @ y ]."
	^ true
]

{ #category : #accessing }
MmSetVizSet >> powerSet [
	| x list aa |
	list := self asArray.
	x := MmSetVizSet new.
	aa := MmSetVizSet new.
	1 to: self size do: [ :take | 
		list
			combinations: take
			atATimeDo: [ :combination | 
				"self halt."
				x := MmSetVizSet new.
				combination do: [ :each | x add: each ].
				aa add: x ] ].
	^ aa
]

{ #category : #accessing }
MmSetVizSet >> xwith: set [
self add: set
]
