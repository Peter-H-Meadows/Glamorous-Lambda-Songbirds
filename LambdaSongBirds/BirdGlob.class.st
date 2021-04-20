Class {
	#name : #BirdGlob,
	#superclass : #Glob,
	#category : #'LambdaSongBirds-GUI'
}

{ #category : #adding }
BirdGlob >> addRightclickMenu [
	| menumodel |
	menumodel := BrWithContextMenuModel new
		stencil: [ BrAnchoredElement new
				aptitude:
					(BrGlamorousContextMenuAptitude new
						content:
							(BrGlamorousSimpleContextMenuContent new
								items:
									{('delete' -> [ :e | self removeFromParent ]).


									"('simp' -> [ :e | model simp .])."
									"('ddd' -> [ :e | self model simpp2  ])."
									
									('make a clone of me' -> [ :e | self makeClone ]).
									
									('simpp'
										-> [ :e | | el |
											
											el := model elementClass new initFromModel: self model pcopy simpp simpp2 pcopy.
											el relocate: 500 atRandom @ 400 atRandom.
											self space addChild: el.
											el addEventHandler: BlPullHandler new ]).
										
									('inspect model' -> [ :e | model inspect ])};
								yourself);
						yourself);
				yourself ];
		yourself.
	self addViewModel: menumodel.
	self addAptitude: BrWithContextMenuAptitude new
]

{ #category : #'event handling' }
BirdGlob >> click [
	SelectedElements isEmpty
		ifTrue: [ SelectedElements add: self.
			^ self ].

	"( SelectedElements includes: self ) ifTrue: [ ^ false ] ."
	ModeBlock value: SelectedElements anyOne value: self.
	SelectedElements := Set new
]

{ #category : #'api - graph' }
BirdGlob >> hearSong: xel [
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

{ #category : #accessing }
BirdGlob >> initFromModel: m [
	model := m.
	model announcer when: #resultOut send: #resultOut to: self.
	model announcer when: SbResultOut send: #resultOut: to: self.
	self addChild: (EarGlob new initFromModel: model earModel).
	self
		addChild: (model brain elementClass new initFromModel: model brain).
	self
		when: BlMouseOverEvent
		do:
			[ :anEvent | "anEvent currentTarget markConnectedSlots" self border: (BlBorder paint: Color random width: 1) ].
	self
		when: BlMouseOutEvent
		do: [ :anEvent | self border: (BlBorder paint: Color gray width: 0) ].

]

{ #category : #initialization }
BirdGlob >> initialize [
	super initialize.
	animating := false.
	"self border: (BlBorder paint: Color gray width: 1)."
	self addRightclickMenu
]
