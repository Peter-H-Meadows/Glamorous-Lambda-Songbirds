"
knows which thing we're trying to make (working on / selected), and which thing we're using to try and make it. (working with / using).
"
Class {
	#name : #MmGameController,
	#superclass : #Object,
	#instVars : [
		'announcer',
		'universe',
		'using',
		'proofToDo',
		'currentlySelectedElement',
		'mondrian',
		'currentlySelectedHypothElement',
		'currentlySelectedUsingElement',
		'selectedUsing',
		'selectedUsableElement',
		'selectedWantedElement',
		'board',
		'usableAssertionsBoard'
	],
	#category : #'Metamath-Game'
}

{ #category : #accessing }
MmGameController >> addToBoard: assertion [

board addToBoard: assertion 
]

{ #category : #accessing }
MmGameController >> addToWorkingBoard: assertion [

board addToWorkingBoard: assertion 
]

{ #category : #accessing }
MmGameController >> announcer [
^ announcer ifNil: [ announcer := Announcer new ]
]

{ #category : #accessing }
MmGameController >> announcer: anObject [
	announcer := anObject
]

{ #category : #accessing }
MmGameController >> board: b [

board := b

]

{ #category : #accessing }
MmGameController >> eHypothClicked: el [

selectedUsableElement := el .

selectedUsableElement highlightAsSelected .
	
selectedWantedElement ifNotNil: [  
	
	selectedWantedElement tryMakeWithEl: selectedUsableElement "model" "forUsing" .
	
	selectedUsableElement unhighlightAsSelected  .
	selectedWantedElement unhighlightAsSelected .
	
	selectedUsableElement := nil .
	selectedWantedElement := nil .
	
] .
]

{ #category : #initialization }
MmGameController >> initialize [

super initialize .

selectedUsableElement := AssertionAndEssentialHypothesisElement new .

selectedWantedElement  := AssertionAndEssentialHypothesisElement new .

"mondrian := GtMondrian new .
mondrian root background: Color veryVeryDarkGray ."



]

{ #category : #deprecated }
MmGameController >> mondrian: m [

| aEventListener |
mondrian := m .

"thing := controller proofToDo ."

]

{ #category : #accessing }
MmGameController >> onBoardeHypothClicked: el [
selectedUsableElement unhighlightAsSelected .
selectedUsableElement := el .
	
selectedWantedElement isSelected  ifFalse: [  ^ self ] .
	
selectedUsableElement unhighlightAsSelected .
selectedWantedElement unhighlightAsSelected .

board addToMain: selectedWantedElement model owner .
	
"selectedWantedElement tryMakeFromOnBoardeHypothEl: selectedUsableElement  ."
selectedWantedElement tryMakeWithEl: selectedUsableElement  .
]

{ #category : #opening }
MmGameController >> openInWindow: anElement named: aTitleString extent: aPoint [
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

{ #category : #accessing }
MmGameController >> proofToDo [

^ proofToDo
]

{ #category : #main }
MmGameController >> resultClicked: el [ 
	
selectedWantedElement := el .
	
selectedUsableElement isSelected  ifFalse: [  ^ self ] .
	
	selectedUsableElement unhighlightAsSelected .
	selectedWantedElement unhighlightAsSelected .
	
	board addToMain: selectedUsableElement model .
	
	"selectedWantedElement tryMakeWithEl: selectedUsableElement .	"
		
		(selectedUsableElement model canMapTo: selectedWantedElement model) "ifFalse: [ self background: Color red ]".
	
	"selectedUsableElement := nil .
	selectedWantedElement := nil ."
	


]

{ #category : #'as yet unclassified' }
MmGameController >> setupBoard [

self error .

board setupForProving: proofToDo .




]

{ #category : #deprecated }
MmGameController >> setupMondrian [

| aEventListener el |

self error .

aEventListener := MmOnBoardWantedEventListener  new gameController: self .

currentlySelectedElement := proofToDo onBoardGameElement addEventHandler: aEventListener .

mondrian nodes 
	stencil: [ :x | x ] ;
	with: { currentlySelectedElement  } .


proofToDo eHypoths do: [ :hypoth |  | hyy |
	
	hyy := hypoth copy .
	hypoth clean . 
	
	aEventListener := MmOnBoardHypothEventListener new gameController: self "; myModel: as" .
	el := hyy onBoardGameElement addEventHandler: aEventListener .
	
	mondrian nodes 
	stencil: [ :x | x ] ;
	with: { el } .
		
	mondrian layout horizontalTree .
	
	
	].
]

{ #category : #accessing }
MmGameController >> setupProof: proofName [ 
"open workspace for proving"
"proofToDo := (universe proofNamed: proofName) copyAndClean ."

proofToDo := "ProofDict at:" proofName .

"proofToDo setAllVariablesToFixed ."
"proofToDo setAllVariablesToFree."

"self setupMondrian ."

board := MmMainBoard new .
board controller: self .
board setupForProving: proofToDo .

"add usable assertions to board"

self openInWindow: board named: proofName name extent: 800@600 .

]

{ #category : #accessing }
MmGameController >> tryWithHypoth: el [

self error .



"currentlySelected ifNil: [ ^ self ] ."

using := el .
"ann currentTarget model clean ."

selectedWantedElement ifNotNil: [  
	
	selectedWantedElement graph connectTo: using .
	using model canMapTo: selectedWantedElement model.
	mondrian layout horizontalTree .
].

using highlightAsSelected .

" currentlySelectedHypothElement  graph connectTo: using ."

"self announcer announce: (MmTryHypothToCurrent new model: using  ) ."

	"( using model canMapTo: currentlySelectedHypothElement model ) ifTrue: [ ] ifFalse: [ ] ."




]

{ #category : #'as yet unclassified' }
MmGameController >> unSelectUsable [

"selectedWantedElement := el toggleSelected .
	
selectedWantedElement ifNil: [ ^ self ] ."
	
	
selectedUsableElement ifNotNil: [  
		
	selectedUsableElement unhighlightAsSelected  .
	
	selectedUsableElement := nil .
	
	] .


]

{ #category : #'as yet unclassified' }
MmGameController >> unSelectWanted [

"selectedWantedElement := el toggleSelected .
	
selectedWantedElement ifNil: [ ^ self ] ."
	
	
selectedWantedElement ifNotNil: [  
		
	selectedWantedElement unhighlightAsSelected  .
	
	selectedWantedElement := nil .
	
	] .


]

{ #category : #accessing }
MmGameController >> universe [
	^ universe
]

{ #category : #accessing }
MmGameController >> universe: anObject [
	universe := anObject
]

{ #category : #accessing }
MmGameController >> usableBasicAssertionFromListClicked: mod [

board addToWorkingBoard: mod.


"selectedWantedElement ifNil: [ 
	
	self addToWorkingBoard: mod copyAndClean . 
	
] ifNotNil: [
	
	selectedWantedElement tryMakeWith2: mod copyAndClean .
	selectedWantedElement unhighlightAsSelected .
	
	selectedUsableElement := nil .
	selectedWantedElement := nil .
	
]."
]

{ #category : #main }
MmGameController >> usableClickedFromBoard: el [ 
selectedUsableElement unhighlightAsSelected .
selectedUsableElement := el .

selectedWantedElement isSelected  ifFalse: [  ^ self ] .
	
	selectedUsableElement unhighlightAsSelected .
	selectedWantedElement unhighlightAsSelected .
	board addToMain: el model .	
	selectedWantedElement tryMakeWithEl: selectedUsableElement .
	

	


]

{ #category : #main }
MmGameController >> wantedClicked: el [

"wanted thing could be the final result, or an ehypoth we want to make."
selectedWantedElement unhighlightAsSelected .
selectedWantedElement := el .
	
selectedUsableElement  isSelected  ifFalse: [  ^ self ] .
	
selectedUsableElement unhighlightAsSelected .
selectedWantedElement unhighlightAsSelected .

board addToMain: selectedWantedElement model owner .

selectedWantedElement tryMakeWithEl: selectedUsableElement .

	



]

{ #category : #main }
MmGameController >> wantedResultClicked: el [ 
	
selectedWantedElement := el .
	
selectedUsableElement isSelected  ifFalse: [  ^ self ] .
	
selectedUsableElement unhighlightAsSelected .
selectedWantedElement unhighlightAsSelected .

selectedUsableElement class = MmOnBoardEssentialHypothesisElement ifFalse: [
	
"board addToMain: selectedUsableElement model ."

] .

selectedWantedElement tryMakeWithEl: selectedUsableElement .
	
"selectedWantedElement tryMakeWithEl: selectedUsableElement .	"
		
"(selectedUsableElement model canMapTo: selectedWantedElement model)" 
"ifFalse: [ self background: Color red ]".
	
"selectedUsableElement := nil .
selectedWantedElement := nil ."
	


]
