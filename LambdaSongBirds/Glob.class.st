Class {
	#name : #Glob,
	#superclass : #BlElement,
	#instVars : [
		'model',
		'announcer',
		'animating'
	],
	#classVars : [
		'ModeBlock',
		'SelectedElements'
	],
	#category : #'LambdaSongBirds-GUI'
}

{ #category : #'class initialization' }
Glob class >> initialize [
	self startSingMode.
	SelectedElements := Set new
]

{ #category : #'class initialization' }
Glob class >> startSingMode [
	ModeBlock := [ :sb1 :sb2 | sb2 hearSong: sb1 ].
	SelectedElements := Set new
]

{ #category : #adding }
Glob >> addRightclickMenu [
	| menumodel |
	menumodel := BrWithContextMenuModel new
		stencil: [ BrAnchoredElement new
				look:
					(BrGlamorousContextMenuLook new
						content:
							(BrGlamorousSimpleContextMenuContent new
								items:
									{('' -> [ :e | "self doStep ." ]).
									('delete' -> [ :e | self removeFromParent ]).
									('make a clone of me' -> [ :e | self makeClone ]).
									('inspect self' -> [ :e | self inspect ])};
								yourself);
						yourself);
				yourself ];
		yourself.
	self addViewModel: menumodel.
	self addLook: BrWithContextMenuLook new
]

{ #category : #'event handling' }
Glob >> click [
	SelectedElements isEmpty
		ifTrue: [ ^ SelectedElements add: self ].

	"( SelectedElements includes: self ) ifTrue: [ ^ false ] ."
	ModeBlock value: SelectedElements anyOne value: self.
	SelectedElements := Set new
]

{ #category : #'api - graph' }
Glob >> hearSong: xel [
	| el |
	el := self class new initFromModel: xel model pcopy.
	el model animating: true.
	el model el: el.

	"self space pulse ."
	el relocate: xel positionInSpace.
	xel visibility: BlVisibility hidden.

	"self removeChildren ."
	self space addChild: el.
	self space pulse.
	model hearSong: el model
]

{ #category : #initialization }
Glob >> initialize [
	super initialize.
	self geometry: (BlRoundedRectangleGeometry cornerRadius: 10).	"BlRectangleGeometry"

	"self border: (BlBorder paint: Color gray width: 2 )."
	self padding: (BlInsets all: 20).
	self
		constraintsDo: [ :c | 
			c horizontal fitContent.
			c vertical fitContent.
			c linear vertical alignCenter ];
		"padding: ( BlInsets top: 10 bottom: 10 );"
			"padding: (BlInsets all: 10);
margin: (BlInsets all: 10);"
			clipChildren: false;
		layout: BlLinearLayout horizontal


	"self addEventHandler: (BlEventHandler
	on: BlClickEvent
	do: [ :evt |
		self click.	
		evt consumed: true	.
	])."
]

{ #category : #'as yet unclassified' }
Glob >> makeClone [
	| el |
	el := model elementClass new initFromModel: model pcopy.
	el relocate: 500 atRandom @ 200 atRandom.
	self space addChild: el.
	el addEventHandler: BlPullHandler new
]

{ #category : #accessing }
Glob >> model [ 
^ model
]
