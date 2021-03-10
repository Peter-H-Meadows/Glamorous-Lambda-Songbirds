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
				look:
					(BrGlamorousContextMenuLook new
						content:
							(BrGlamorousSimpleContextMenuContent new
								items:

{

('delete' -> [ :e | 
	self removeFromParent .
]).


"('simp' -> [ :e |
	 
	model simp .

])."


('make a clone of me' -> [ :e | 
	
	self makeClone .

]).


('inspect model' -> [ :e | 
	
	model inspect .

]).


};

								yourself);
						yourself);
				yourself ];
		yourself.	

	self addViewModel: menumodel .
	self addLook: BrWithContextMenuLook new .
	
]

{ #category : #'event handling' }
BirdGlob >> hearSong: xel [

| el |

el := self class new initFromModel: xel model pcopy .

el model animating: true .

el model el: el .

"self space pulse ."

el relocate: xel positionInSpace .

xel visibility: BlVisibility hidden .

"self removeChildren ."

self space addChild: el .
self space pulse .

model hearSong: el model .

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
	self
		addEventHandler:
			(BlEventHandler
				on: BlClickEvent
				do: [ :evt | 
					self click.
					evt consumed: true ])
]

{ #category : #initialization }
BirdGlob >> initialize [
	super initialize.
	animating := false.
	"self border: (BlBorder paint: Color gray width: 1)."
	self addRightclickMenu
]

{ #category : #'as yet unclassified' }
BirdGlob >> resultOut [


]

{ #category : #'as yet unclassified' }
BirdGlob >> resultOut: ann [

| el |
el := "BirdGlob" ann model elementClass new initFromModel: ann model .

"ann model animating: true .
ann model el: el ."

el relocate: self children first positionInSpace + (400@0).

"self children first visibility: BlVisibility hidden ."

self space addChild: el .
]
