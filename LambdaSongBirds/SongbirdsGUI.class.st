Class {
	#name : #SongbirdsGUI,
	#superclass : #Object,
	#instVars : [
		'blocSpace',
		'pannable'
	],
	#category : #'LambdaSongBirds-GUI'
}

{ #category : #adding }
SongbirdsGUI >> addCardinal [

| sb |

sb := BirdGlob new initFromModel: ( SongbirdModel new parse: #( \ a b c . a c b )  ) .

sb relocate: 900 atRandom @ 700 atRandom  .

sb 	addEventHandler: BlPullHandler new.

pannable addChild: sb .

^ sb
]

{ #category : #adding }
SongbirdsGUI >> addIdiot [

| sb |

sb := BirdGlob new initFromModel: ( SongbirdModel new parse: #( \ a . a ) ) .

sb relocate: 900 atRandom @ 800 atRandom  .

sb 	addEventHandler: BlPullHandler new.

"blocSpace" pannable  addChild: sb .

^ sb
]

{ #category : #adding }
SongbirdsGUI >> addJay [

| sb |

sb := BirdGlob new initFromModel: ( SongbirdModel new parse: #( \ a b c d . a b #( a c b ) ) ) .

"sb relocate: 20 atRandom @ 60 atRandom  ."

sb 	addEventHandler: BlPullHandler new.

pannable addChild: sb .

^ sb
]

{ #category : #adding }
SongbirdsGUI >> addKestrel [

| sb |

sb := BirdGlob new initFromModel: ( SongbirdModel new parse: #( \ a b . a ) ) .

sb relocate: 900 atRandom @ 600 atRandom  .

sb 	addEventHandler: BlPullHandler new.

pannable addChild: sb .

^ sb
]

{ #category : #adding }
SongbirdsGUI >> addKite [

| sb |

sb := BirdGlob new initFromModel: ( SongbirdModel new parse: #( \ a b . b ) ) .

sb relocate: 900 atRandom @ 800 atRandom  .

sb 	addEventHandler: BlPullHandler new.

pannable addChild: sb .

^ sb
]

{ #category : #adding }
SongbirdsGUI >> addKx [

| sb |

sb := BirdGlob new initFromModel: ( SongbirdModel new parse: #( \ a b . a ) ) .

sb relocate: 900 atRandom @ 600 atRandom  .

sb 	addEventHandler: BlPullHandler new.

pannable addChild: sb .

^ sb
]

{ #category : #adding }
SongbirdsGUI >> addMockingbird [

| sb |

sb := BirdGlob new initFromModel: ( SongbirdModel new parse: #( \ a . a a ) ) .

"sb relocate: 500 atRandom @ 200 atRandom  ."

sb 	addEventHandler: BlPullHandler new.

pannable addChild: sb .

^ sb
]

{ #category : #adding }
SongbirdsGUI >> addRightclickMenu [

| model |
model := BrWithContextMenuModel new
		stencil: [ BrAnchoredElement new
				look:
					(BrGlamorousContextMenuLook new
						content:
							(BrGlamorousSimpleContextMenuContent new
								items:

{

('zoom out' -> [ :e | 
	pannable zoomOut .
]).

('zoomToFit' -> [ :e | 
	pannable zoomToFit  .
]).

('add Idiot' -> [ :e | 
	self addIdiot .
]).

('add Kite' -> [ :e | 
	self addKite .
]).

('add Kestrel' -> [ :e | 
	self addKestrel .
]).

('add Mockingbird' -> [ :e | 
	self addMockingbird  .
]).

('add Thrush' -> [ :e | 
	self addThrush .
]).

('add Cardinal' -> [ :e | 
	self addCardinal .
]).

('add Jay' -> [ :e | 
	self addJay .
]).

('enter sing mode' -> [ :e |
	"self startSingMode ."
]).

('enter connect mode' -> [ :e |
	 
	"self startConnectMode ."
	"plumbing. re-wiring.."

]).

('enter eat mode' -> [ :e | 
	
	"self startEatMode ."

]).

};

								yourself);
						yourself);
				yourself ];
		yourself.	
	
	
	
	
	blocSpace root viewModel: model.
	blocSpace root look: BrWithContextMenuLook new .
	
]

{ #category : #adding }
SongbirdsGUI >> addThrush [

| sb |

sb := BirdGlob new initFromModel: ( SongbirdModel new parse: #( \ a b . b a ) ) .

sb relocate: 700 atRandom @ 600 atRandom  .

sb 	addEventHandler: BlPullHandler new.

pannable addChild: sb .

^ sb
]

{ #category : #adding }
SongbirdsGUI >> cardinalModel [

| thrushModel cardinalModel cardinal thrush |
blocSpace root removeChildren .

thrushModel := SongbirdModel new parse: #( \ a b . b a ) .
cardinalModel := SongbirdModel new parse: #( \ a b c . a c b ) .

thrush := BirdGlob new initFromModel: thrushModel .
cardinal := BirdGlob new initFromModel: cardinalModel .

thrush relocate: 300 "atRandom" @ 500 "atRandom"  .
thrush 	addEventHandler: BlPullHandler new.
blocSpace addChild: thrush .

blocSpace addChild: cardinal .


cardinal hearSong: thrush .
]

{ #category : #'instance creation' }
SongbirdsGUI >> open [
	blocSpace := BlSpace new
		extent: 1400 @ 800;
		title: 'Songbirds'.
	blocSpace root background: Color black.
	pannable := BlCanvassableElement new.
	pannable
		constraintsDo: [ :c | 
			c horizontal matchParent.
			c vertical matchParent ].
	pannable clipChildren: false.
	self addRightclickMenu.
	blocSpace root
		addEventHandler:
			(BlEventHandler
				on: BlMouseWheelEvent
				do: [ :evt | 
					evt isScrollDown
						ifTrue: [ pannable zoomIn ]
						ifFalse: [ pannable zoomOut ] ]).
	blocSpace root addChild: pannable.
	blocSpace show maximize
]

{ #category : #'as yet unclassified' }
SongbirdsGUI >> startConnectMode [

" startConnectMode"
]

{ #category : #'as yet unclassified' }
SongbirdsGUI >> startEatMode [

" startEatMode"
]

{ #category : #'as yet unclassified' }
SongbirdsGUI >> startSingMode [

" startSingMode"
]
