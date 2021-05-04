Class {
	#name : #SongbirdsGUI,
	#superclass : #Object,
	#instVars : [
		'blocSpace',
		'pannable',
		'sb'
	],
	#classVars : [
		'MyPullHandler'
	],
	#category : #'LambdaSongBirds-GUI'
}

{ #category : #'as yet unclassified' }
SongbirdsGUI class >> initialize [ 
MyPullHandler := BlPullHandler new
]

{ #category : #'as yet unclassified' }
SongbirdsGUI class >> myPullHandler [
^ MyPullHandler
]

{ #category : #deprecated }
SongbirdsGUI >> addCardinal [

| sb |

sb := BirdGlob new initFromModel: ( SongbirdModel new parse: #( \ a b c . a c b )  ) .

sb relocate: 900 atRandom @ 700 atRandom  .

sb 	addEventHandler: BlPullHandler new.

pannable addChild: sb .

^ sb
]

{ #category : #deprecated }
SongbirdsGUI >> addIdiot [
	| sb |
	"
sb := BirdGlob new initFromModel: ( SongbirdModel new parse: #( \ a . a ) ) ."
	sb := BirdGlob new initFromModel: (SongbirdModel newModelOf: 'idiot').
	sb relocate: 900 atRandom @ 800 atRandom.
	sb addEventHandler: BlPullHandler new.
	pannable addChild: sb.
	^ sb
]

{ #category : #deprecated }
SongbirdsGUI >> addJay [

| sb |

sb := BirdGlob new initFromModel: ( SongbirdModel new parse: #( \ a b c d . a b #( a c b ) ) ) .

"sb relocate: 20 atRandom @ 60 atRandom  ."

sb 	addEventHandler: BlPullHandler new.

pannable addChild: sb .

^ sb
]

{ #category : #deprecated }
SongbirdsGUI >> addKestrel [

| sb |

sb := BirdGlob new initFromModel: ( SongbirdModel new parse: #( \ a b . a ) ) .

sb relocate: 900 atRandom @ 600 atRandom  .

sb 	addEventHandler: BlPullHandler new.

pannable addChild: sb .

^ sb
]

{ #category : #deprecated }
SongbirdsGUI >> addKite [

| sb |

sb := BirdGlob new initFromModel: ( SongbirdModel new parse: #( \ a b . b ) ) .

sb relocate: 900 atRandom @ 800 atRandom  .

sb 	addEventHandler: BlPullHandler new.

pannable addChild: sb .

^ sb
]

{ #category : #deprecated }
SongbirdsGUI >> addKx [

| sb |

sb := BirdGlob new initFromModel: ( SongbirdModel new parse: #( \ a b . a ) ) .

sb relocate: 900 atRandom @ 600 atRandom  .

sb 	addEventHandler: BlPullHandler new.

pannable addChild: sb .

^ sb
]

{ #category : #deprecated }
SongbirdsGUI >> addMockingbird [

| sb |

sb := BirdGlob new initFromModel: ( SongbirdModel new parse: #( \ a . a a ) ) .

"sb relocate: 500 atRandom @ 200 atRandom  ."

sb 	addEventHandler: BlPullHandler new.

pannable addChild: sb .

^ sb
]

{ #category : #deprecated }
SongbirdsGUI >> addRightclickMenu [

| model |
model := BrWithContextMenuModel new
		stencil: [ BrAnchoredElement new
				look:
					(BrGlamorousContextMenuAptitude new
						content:
							(BrGlamorousSimpleContextMenuContent new
								items:

{
('startConnectMode'-> [ :e | 
	self startConnectMode
]).

('i'-> [ :e | 
sb := BirdGlob new initFromModel: (SongbirdModel newModelOf: 'i').
sb relocate: 999 atRandom @ 400 atRandom.
sb addEventHandler: self class myPullHandler.
pannable addChild: sb. 
]).

('ki'-> [ :e | 
sb := BirdGlob new initFromModel: (SongbirdModel newModelOf: 'ki').
sb relocate: 999 atRandom @ 400 atRandom.
sb addEventHandler: self class myPullHandler.
pannable addChild: sb. 
]).

('kx'-> [ :e | 
sb := BirdGlob new initFromModel: (SongbirdModel newModelOf: 'kx').
sb relocate: 999 atRandom @ 400 atRandom.
sb addEventHandler: self class myPullHandler.
pannable addChild: sb. 
]).

('M'-> [ :e | 
sb := BirdGlob new initFromModel: (SongbirdModel newModelOf: 'M').
sb relocate: 999 atRandom @ 400 atRandom.
sb addEventHandler: self class myPullHandler.
pannable addChild: sb. 
]).

};

								yourself);
						yourself);
				yourself ];
		yourself.	
			
	blocSpace root viewModel: model.
	blocSpace root look: BrWithContextMenuAptitude new .
]

{ #category : #deprecated }
SongbirdsGUI >> addRightclickMenu2 [
	blocSpace root viewModel: self createMenuModel.
	blocSpace root aptitude: BrWithContextMenuAptitude new
]

{ #category : #deprecated }
SongbirdsGUI >> addThrush [

| sb |

sb := BirdGlob new initFromModel: ( SongbirdModel new parse: #( \ a b . b a ) ) .

sb relocate: 700 atRandom @ 600 atRandom  .

sb 	addEventHandler: BlPullHandler new.

pannable addChild: sb .

^ sb
]

{ #category : #deprecated }
SongbirdsGUI >> cardinalHearThrush [

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

{ #category : #'as yet unclassified' }
SongbirdsGUI >> createMenuModel [
	| model |
	model := BrWithContextMenuModel new
		stencil: [ BrAnchoredElement new
				aptitude:
					(BrGlamorousContextMenuAptitude new
						content:
							(BrGlamorousSimpleContextMenuContent new
								items:
									{('start Connect Mode' -> [ :e |  ]).
									('start sing Mode' -> [ :e |  ]).
									('start swap Mode' -> [ :e |  ]).
									('i'
										-> [ :e | 
											sb := BirdGlob new initFromModel: (SongbirdModel newModelOf: 'i').
											sb relocate: 999 atRandom @ 400 atRandom.
											sb addEventHandler: self class myPullHandler.
											pannable addChild: sb ]).
									('ki'
										-> [ :e | 
											sb := BirdGlob new initFromModel: (SongbirdModel newModelOf: 'ki').
											sb relocate: 999 atRandom @ 400 atRandom.
											sb addEventHandler: self class myPullHandler.
											pannable addChild: sb ]).
									('kx'
										-> [ :e | 
											sb := BirdGlob new initFromModel: (SongbirdModel newModelOf: 'kx').
											sb relocate: 999 atRandom @ 400 atRandom.
											sb addEventHandler: self class myPullHandler.
											pannable addChild: sb ]).
									('M'
										-> [ :e | 
											sb := BirdGlob new initFromModel: (SongbirdModel newModelOf: 'M').
											sb relocate: 999 atRandom @ 400 atRandom.
											sb addEventHandler: self class myPullHandler.
											pannable addChild: sb ])};
								yourself);
						yourself);
				yourself ];
		yourself.
	^ model
]

{ #category : #initialization }
SongbirdsGUI >> initialize [

	super initialize.
	self macroCreateNewMenuModelMethod .
	self macro
]

{ #category : #initialization }
SongbirdsGUI >> macro [ 
| st |
st := '
addRightclickMenu

| model |
model := BrWithContextMenuModel new
		stencil: [ BrAnchoredElement new
				look:
					(BrGlamorousContextMenuAptitude new
						content:
							(BrGlamorousSimpleContextMenuContent new
								items:

{
(''startConnectMode''-> [ :e | 
	self startConnectMode
]).

'.
	SongbirdModel names do: [ 
		:name 
		":model" | 
		| tmp |
		tmp := '(' , '''' , name , '''' , '-> [ :e | 
sb := BirdGlob new initFromModel: (SongbirdModel newModelOf: ' , ''''
		       , name , '''' , ').
sb relocate: 999 atRandom @ 400 atRandom.
sb addEventHandler: self class myPullHandler.
pannable addChild: sb. 
]).

'.
		st := st , tmp ].
	st := st , '};

								yourself);
						yourself);
				yourself ];
		yourself.	
			
	blocSpace root viewModel: model.
	blocSpace root look: BrWithContextMenuAptitude new .'.
	self class compile: st
	
]

{ #category : #initialization }
SongbirdsGUI >> macroCreateNewMenuModelMethod [ 
"(''start Connect Mode''-> [ :e | 
	self startConnectMode
]).

(''start sing Mode''-> [ :e | 
	self startSingMode
]).

(''start swap Mode''-> [ :e | 
	self startXMode
])."
| st |
st := '
createMenuModel

| model |
model := BrWithContextMenuModel new
		stencil: [ BrAnchoredElement new
				look:
					(BrGlamorousContextMenuAptitude new
						content:
							(BrGlamorousSimpleContextMenuContent new
								items:

{
(''start Connect Mode''-> [ :e | 
	
]).

(''start sing Mode''-> [ :e | 
	
]).

(''start swap Mode''-> [ :e | 
	
]).

'.
	SongbirdModel names do: [ 
		:name 
		":model" | 
		| tmp |
		tmp := '(' , '''' , name , '''' , '-> [ :e | 
sb := BirdGlob new initFromModel: (SongbirdModel newModelOf: ' , ''''
		       , name , '''' , ').
sb relocate: 999 atRandom @ 400 atRandom.
sb addEventHandler: self class myPullHandler.
pannable addChild: sb. 
]).

'.
		st := st , tmp ].
	st := st , '};

								yourself);
						yourself);
				yourself ];
		yourself.	
			
	^ model	'.
	self class compile: st
	
]

{ #category : #'instance creation' }
SongbirdsGUI >> open [
	| t |
	t := 'Songbirds 3    GT ' , GtImage instance version versionString.
	Glob initialize.
	blocSpace := BlSpace new
		extent: 1400 @ 800;
		title: t.
	blocSpace root background: Color black.
	pannable := BlPannableElement new.	"BlCanvassableElement"	"BlZoomableElement"
	pannable
		constraintsDo: [ :c | 
			c horizontal matchParent.
			c vertical matchParent ].
	pannable clipChildren: false.
	pannable zoomableElement clipChildren: false.
	self addRightclickMenu2.
	blocSpace root
		addEventHandler:
			(BlEventHandler
				on: BlMouseWheelEvent
				do: [ :evt | 
					evt isScrollDown
						ifTrue: [ pannable zoomIn ]
						ifFalse: [ pannable zoomOut ] ]).
	blocSpace root addChild: pannable.
	blocSpace show maximize.
	GlutinWindowsRegistry default
		windowsDo:
			[ :w | w title: t	"'Songbirds 2    ' , GtImage instance version versionString" ]
]

{ #category : #'instance creation' }
SongbirdsGUI >> open2 [
	<gtExample>
	| view |
	view := GtMondrian new.
	Glob initialize.
	pannable := view root.
	view root background: Color black.
	view root viewModel: self createMenuModel.
	view root aptitude: BrWithContextMenuAptitude new.

	"sb := BirdGlob new initFromModel: (SongbirdModel newModelOf: 'idiot').
sb relocate: 999 atRandom @ 400 atRandom.
sb addEventHandler: self class myPullHandler.
view root addChild: sb. "
	GlutinWindowsRegistry default
		windowsDo: [ :w | w title: GtImage instance version versionString ].
	^ view




	"
	blocSpace := BlSpace new
		extent: 1400 @ 800;
		title: 'Songbirds'.
	blocSpace root background: Color black.
	
	pannable := BlPannableElement new.
	pannable
		constraintsDo: [ :c | 
			c horizontal matchParent.
			c vertical matchParent ].
	pannable clipChildren: false.
	pannable zoomableElement clipChildren: false.
	self addRightclickMenu."

	"blocSpace root
		addEventHandler:
			(BlEventHandler
				on: BlMouseWheelEvent
				do: [ :evt | 
					evt isScrollDown
						ifTrue: [ pannable zoomIn ]
						ifFalse: [ pannable zoomOut ] ]).
	blocSpace root addChild: pannable.
	blocSpace show maximize.
	"
]

{ #category : #'instance creation' }
SongbirdsGUI >> open3 [
	"self new open3"

	| view |
	Glob initialize.
	blocSpace := BlSpace new
		extent: 1400 @ 800;
		title: 'Songbirds'.
	blocSpace root background: Color black.
	view := GtMondrian new.
	pannable := view root.	"asScalableElement"
	view root background: Color black.

	"view root viewModel: self createMenuModel .
	view root look: BrWithContextMenuLook new."
	blocSpace root viewModel: self createMenuModel.
	blocSpace root aptitude: BrWithContextMenuAptitude new.
	blocSpace root
		addEventHandler:
			(BlEventHandler
				on: BlMouseWheelEvent
				do: [ :evt | 
					evt isScrollDown
						ifTrue: [ pannable zoomIn ]
						ifFalse: [ pannable zoomOut ] ]).
	blocSpace root addChild: view root.
	blocSpace show maximize.
	GlutinWindowsRegistry default
		windowsDo: [ :w | w title: GtImage instance version versionString ]





	"
	blocSpace := BlSpace new
		extent: 1400 @ 800;
		title: 'Songbirds'.
	blocSpace root background: Color black.
	
	pannable := BlPannableElement new.
	pannable
		constraintsDo: [ :c | 
			c horizontal matchParent.
			c vertical matchParent ].
	pannable clipChildren: false.
	pannable zoomableElement clipChildren: false.
	self addRightclickMenu."

	"blocSpace root
		addEventHandler:
			(BlEventHandler
				on: BlMouseWheelEvent
				do: [ :evt | 
					evt isScrollDown
						ifTrue: [ pannable zoomIn ]
						ifFalse: [ pannable zoomOut ] ]).
	blocSpace root addChild: pannable.
	blocSpace show maximize.
	"
]

{ #category : #deprecated }
SongbirdsGUI >> startConnectMode [

Glob startConnectMode
]

{ #category : #deprecated }
SongbirdsGUI >> startEatMode [

" startEatMode"
]

{ #category : #deprecated }
SongbirdsGUI >> startSingMode [

Glob startSingMode
]

{ #category : #deprecated }
SongbirdsGUI >> startXMode [

Glob startXMode
]
