"
!Set viz


Collection extend [
    power [
        ^(0 to: (1 bitShift: self size) - 1) readStream collect: [ :each || i |
            i := 0.
            self select: [ :elem | (each bitAt: (i := i + 1)) = 1 ] ]
    ]
].

*https://rosettacode.org/wiki/Power_set#Smalltalk*

a binary relation R is called well-founded on a class X 
if every non-empty subset S U. X 
has a minimal element with respect to R, 
t
hat is, an element m not related by sRm (for instance, ""s is not smaller than m"") for any s e. S.

show examples of sets and relationships

a relation is well founded if

In order theory, a partial order is called well-founded if the corresponding strict order is a well-founded relation. If the order is a total order then it is called a well-order.

In set theory, a set x is called a well-founded set if the set membership relation is well-founded on the transitive closure of x. The axiom of regularity, which is one of the axioms of Zermelo–Fraenkel set theory, asserts that all sets are well-founded.

{\displaystyle (\forall S\subseteq X)\;[S\neq \emptyset \implies (\exists m\in S)(\forall s\in S)\lnot (sRm)].}{\displaystyle (\forall S\subseteq X)\;[S\neq \emptyset \implies (\exists m\in S)(\forall s\in S)\lnot (sRm)].}

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
