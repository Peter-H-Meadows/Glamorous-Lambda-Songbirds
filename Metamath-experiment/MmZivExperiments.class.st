Class {
	#name : #MmZivExperiments,
	#superclass : #Object,
	#instVars : [
		'prev',
		'view'
	],
	#category : #'Metamath-experiment'
}

{ #category : #accessing }
MmZivExperiments >> add [
	| child pp pset |
	pp := OrderedCollection new.


	"prev do: [ :ea | pp addAll: ea allEnvCombinations ] ."
	pp := prev powerSet.
	"prev addAll:"

	"pp := (Ziv new with: prev) allCombinations  ."

	"pset := MmSetVizSet new .
pset add: prev ."
	pp drOn: view.

	"pp do: [:ea |  view topStep addChildren: { ea asBlElement }.  ]."

	"prev do: [:ea | ea draw .]"
	prev := pp
]

{ #category : #accessing }
MmZivExperiments >> go [
	<gtExample>
	| mmodel look elements zz |
	view := GtMondrian new.
	"Ziv new mon: view ."
	"zz := ZivEmpty new mon: view ."
	self iii.
	mmodel := BrWithContextMenuModel new
		stencil: [ BlElement new
				look:
					(BrGlamorousContextMenuLook new
						content:
							(BrGlamorousSimpleContextMenuContent new
								items:
									{('star'
										-> [ :e | 
											self add.
											view layout rectanglePack	"grid"

											"elements := #( 1 2 ) collect: [ :each |
		| child |
		child := view nodes nodeElementFor: each.
		view nodeAt: each put: child.
		child ].
	view topStep addChildren: elements asOrderedCollection. " ]).
									('zoom out'
										->
											[ :e | "view edges" "connectFrom: [ :x | x // 2 ]." view layout grid	"horizontalTree" ]).
									('inspect self'
										-> [ :e | view nodes inspect	"e background: Color green" ])};
								yourself);
						yourself);
				yourself ];
		yourself.
	look := BrWithContextMenuLook new.
	view root viewModel: mmodel.
	view root look: look.


	"view nodes
		shape: [ :x | 
			BlElement new 
				border: (BlBorder paint: Color black);
				geometry: BlEllipse new; 
				size: (x * 2) @ (x * 2) ];
		with: (1 to: 9)."
	"self assert: view topStep root graph nodeChildren size = 9."
	^ view
]

{ #category : #accessing }
MmZivExperiments >> iii [
prev := MmSetVizSet new .
"prev add: ( Ziv new with: { ZivEmpty new } ) ."
"prev add: ( MmSetVizSymbol new with: 'A' )."
prev add: ( MmSetVizSymbol new with: 'x' ).
prev add: ( MmSetVizSymbol new with: 'o' ).
prev do: [:ea |  view topStep addChildren: { ea asBlElement }.  ].
]
