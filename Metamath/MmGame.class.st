Class {
	#name : #MmGame,
	#superclass : #Object,
	#instVars : [
		'level',
		'mainBox',
		'universe',
		'nodes',
		'controller',
		'rs'
	],
	#classVars : [
		'Database',
		'Scopes'
	],
	#category : #'Metamath-Game'
}

{ #category : #accessing }
MmGame class >> bl [ 
^ BlElement new
]

{ #category : #accessing }
MmGame >> bl [
^ BlElement new
]

{ #category : #'accessing - datasets' }
MmGame >> clearScopes [
Scopes := nil 
]

{ #category : #'accessing - datasets' }
MmGame >> database [

| pp |
^ Database ifNil: [ 
	pp := MmPP2Parser new .
	pp parse: MmRawFileDataPartOne comment.
	Database := pp database .
	
	"pp parse: MmRawFileDataPartOne comment.
	pp parse: MmRawFileDataPartTwo comment.
	pp parse: MmRawFileDataPartThree comment.
	pp parse: MmRawFileDataPartFour comment.
	Database :=  pp parse: MmRawFileDataPartFive comment."
	
]
]

{ #category : #accessing }
MmGame >> database: d [
Database := d
]

{ #category : #'accessing - datasets' }
MmGame >> databaseNew [
"MmGame new databaseNew"
^ Database := nil "self parseRawa"
]

{ #category : #accessing }
MmGame >> initialize [ 
super initialize 


]

{ #category : #'as yet unclassified' }
MmGame >> mm [ 
| fff str |

"MmGame new mm"
fff := (File named: 'set.mm') readStream.
fff := (ZnCharacterReadStream on: fff) .

str := WriteStream with: ''.

[ fff position < 888888 ] whileTrue: [  
	
	fff nextLine .
	
	] .

[ fff position < 2904999 ] whileTrue: [  
	
	str nextPutAll: fff nextLine .
	str nextPutAll: String cr .
	] .


"xorexmid"

MmRawFileDataPartFive  comment: str contents .
]

{ #category : #accessing }
MmGame >> openAll [
<gtExample>
| aList aEventListener  aDocument aFigureFile editor txt text ed runner anAccordion |

self clearScopes .  

aList := BrSimpleList new.

aList stencil: [ :ea :index | ea eel ].
		
aList items: self scopes first stuff . 
	
^ aList

]

{ #category : #accessing }
MmGame >> openAllInDoc [

| aList aEventListener  aDocument aFigureFile |
<gtExample>
	
	"aFigureFile := self figureFileReference."
	
	"aDocument := self defaultDocument fileReference: self fileReferenceWithFigure."
	
	aDocument := GtDocumenter new.
	aDocument editor useSyncStylerStrategy.	
	"documents add: aDocument."
	
	
	aDocument text: '${example:MmGame>>#bl}$'.
	
	
	aDocument read.
	
	

rs := ReadStream on: self database sections .

"aList := BrSimpleList new.

aList stencil: [ :each :index | 
			each isComment ifTrue: [ each gameElement ] ifFalse: [  

				aEventListener := MmStartEventListener new .
				each usableElement addEventHandler: aEventListener .
			]
		].
aList items: self database allThings ."
	
^ aDocument

]

{ #category : #accessing }
MmGame >> openAllInEditor [

| aList aEventListener  aDocument aFigureFile editor txt text ed runner anAccordion |
<gtExample>
	
	editor := BrTextEditor new. " beLineBased"
	
	"aFigureFile := self figureFileReference."
	
	"aDocument := self defaultDocument fileReference: self fileReferenceWithFigure."
	
	txt := BlRopedText string: 'first', String cr, 'second', String cr, 'third'.
	
	
editor text: txt.
	
	txt append: 'moooo' asRopedText .
	"
	 self database sections inspect ."
	 

ed := BrEditorElement new 
				editor: editor;
				padding: (BlInsets all: 10);
				constraintsDo: [ :c | 
					c horizontal matchParent.
					c vertical matchParent ] ; yourself .

text := 'You can click on this.' asRopedText.
	(text from: 9 to: 13)
		attributes:
			{(BlTextForegroundAttribute new paint: Color blue).
			(BrTextHoverStylableAttribute new
				attribute: (BlTextUnderlineAttribute new color: Color blue)).
			(BrTextClickAttribute new
				action:
					[ :aTBrTextEditorTextualPiece :aTarget :aTextEditor :anEvent | 
					"GtInspector openOn: aTBrTextEditorTextualPiece text" 
					"aTextEditor scrollToPosition: 444"
					"aTextEditor select: 4440 to: 4450 ."
					"aTextEditor navigator moveDown" .
					
					"self scrollToPosition: self editor segmentCollector computedSegmentsCount."
					
					"ed scrollToLast" "scrollToPosition: 3333" .
					ed scrollToPosition: 333.
					])}.
	 
	 txt append: text .
	

runner := TKTLocalProcessTaskRunner new.

"runner exceptionHandler: (TKTTestExceptionHandler new)."
	
runner schedule: [ "10 milliSeconds wait. finished := true" 
	 
self scopes do: [:ea | 
	 
	 "self halt."
	 
	 "just use simp list on scopes"
	 
	 
	 "ea isComment ifTrue: [ 
	 	 txt append: (String cr , ea body , String cr, '.') asRopedText .
	 ] ifFalse: [
	 	 
	 (txt from: txt size to: txt size) attribute:
		(BrTextAdornmentDynamicAttribute new
			beAppend;
			stencil: [
				aEventListener := MmStartEventListener new .
				ea usableElement addEventHandler: aEventListener ]).
	]."
	 
].


] "timeout: 50 milliSeconds".

"
rs := ReadStream on: self database sections ."


aList := BrSimpleList new.

aList stencil: [ :eachScope :index |

	anAccordion := MmScopeElement2 new with: eachScope .
	

			"anAccordion"

			"each isComment ifTrue: [ each gameElement ] ifFalse: [  

				aEventListener := MmStartEventListener new .
				each usableElement addEventHandler: aEventListener .
			]"
		].
		
aList items: self scopes .
	
^ aList

]

{ #category : #accessing }
MmGame >> openGame [
"self new openGame "

	| aSpace model levels |
	aSpace := BlSpace new
		extent: 1400@800;
		title: 'GlamorousMetamath' .
	
	aSpace root background: Color darkGray .
	
	"aSpace root addChild: self ."
	
	levels := ReadStream on: self scopes allProofs asArray  "reversed" .
	
	levels next: 111 .
	
	aSpace root addChild: ( MmMainBoard new openOn:  levels next ) .
	
	model := BrWithContextMenuModel new
		stencil: [ BrAnchoredElement new
				look:
					(BrGlamorousContextMenuLook new
						content:
							(BrGlamorousSimpleContextMenuContent new
								items:
									{('next level' -> [ :e | e removeChildren. e addChild: ( MmMainBoard new openOn:  levels next ) .  ]).
									('reset' -> [ :e | e removeChildren. e addChild: ( MmMainBoard new openOn:  levels peekBack  ) ]).
									('green' -> [ :e | e background: Color green ])};
								yourself);
						yourself);
				yourself ];
		yourself.	
	
	
	
	
	aSpace root viewModel: model.
	aSpace root look: BrWithContextMenuLook new .

	"aSpace root addEventHandler:
			(BlEventHandler
				on: BlDoubleClickEvent
				do: [ :evt | BlElementSelection on: evt target ])."
	
	aSpace show.
]

{ #category : #accessing }
MmGame >> openGame: proof [

MmMainBoard new openOn: proof .

"controller := MmGameController new .
controller setupProof: proofName ."

]

{ #category : #accessing }
MmGame >> openGameiii [

| aList aEventListener |

rs := ReadStream on: self database sections .

aList := BrSimpleList new.

aList stencil: [ :each :index | 
			each isComment ifTrue: [ each gameElement ] ifFalse: [  

				aEventListener := MmStartEventListener new .

				each usableElement addEventHandler: aEventListener .
			
			]
		].
			
aList items: self database allThings .
		
aList when: BrSelectionChanged
		do: [ :anEvent | 
				
				"anEvent target look listElement scrollToPosition: anEvent selectedInterval last ."
			
			anEvent target look listElement scrollToPosition: rs next .
			
			"anEvent
				selectedDo: [ :anInterval | anEvent target look listElement scrollToPosition: anInterval last ]."
				
				"
			anEvent
				deselectedDo: [ :anInterval | self inform: 'Deselected: ' , anInterval asString ]" 
				
].
		
aList background: Color veryVeryDarkGray .

^ aList


]

{ #category : #opening }
MmGame >> openInWindow: anElement named: aTitleString extent: aPoint [
	"Open a given element in a window of a provided extent and specified title"
	| aSpace |
	aSpace := BlSpace new
		extent: aPoint;
		title: aTitleString.
	
	aSpace root background: Color darkGray .
	aSpace root addChild: anElement.

	"aSpace root addEventHandler:
			(BlEventHandler
				on: BlDoubleClickEvent
				do: [ :evt | BlElementSelection on: evt target ])."
	
	aSpace show
]

{ #category : #parsing }
MmGame >> parseRaw [

| pp | 

"MmDatabaseGlob := MmDatabase new ."

pp := MmPP2Parser new .

pp parse: MmRawFileDataPartOne comment.

MmPP2Parser new parse: MmRawFileDataPartTwo comment.
MmPP2Parser new parse: MmRawFileDataPartThree comment.
MmPP2Parser new parse: MmRawFileDataPartFour comment.
MmPP2Parser new parse: MmRawFileDataPartFive comment.

MmGame new openGameiii .

MmGame new openGame: 'poss'.

MmGame new openGame: 'axext3'.


MmGame new openGame: 'trel'.

MmGame new openGame: 'nnsuc'.


MmGame new openGame: 'dfsbcq2'.
MmRawFileDataPartOne  comment copyFrom: 15820 to: 15988.

"MmDatabaseGlob proofs reverse  ."
]

{ #category : #parsing }
MmGame >> parseRawa [

| pp | 

pp := MmPP2Parser new .
pp parse: MmRawFileDataPartOne comment.
pp parse: MmRawFileDataPartTwo comment.
pp parse: MmRawFileDataPartThree comment.
pp parse: MmRawFileDataPartFour comment.
^ pp parse: MmRawFileDataPartFive comment.

]

{ #category : #'accessing - datasets' }
MmGame >> scopes [

| pp |
^ Scopes ifNil: [ 
	pp := MmPP2ParserFirst  new .
	Scopes :=  pp parse: MmRawFileDataPartOne comment.
	Scopes := Scopes first parse
	
	"pp parse: MmRawFileDataPartOne comment.
	pp parse: MmRawFileDataPartTwo comment.
	pp parse: MmRawFileDataPartThree comment.
	pp parse: MmRawFileDataPartFour comment.
	Database :=  pp parse: MmRawFileDataPartFive comment."
	
]
]

{ #category : #accessing }
MmGame >> universe: m [
universe := m
]
