"
bird
song

Martin Erwig [5] proposes a general approach to visual languages. He presents a 
framework based on a rather general notion of abstract visual syntax and defines 
an abstract visual syntax of a visual language notation as a set of directed labeled 
graphs, where nodes represent visual objects and edges represent relationships 
between objects. In this section we describe four existing approaches to visualize 
lambda expressions, compare them in the framework of abstract visual syntax and 
note their benefits and drawbacks. 

First consider the expression λf.( λx.f( xx ))( λx.f( x x )). Figure 2 shows 
its structure. We can see that there are three types of nodes (application node, 
lambda node and variable node) and two types of edges such as tree edges (parentchild) 
and binding edges (variable-lambda). Erwig considers such a structure as the 
abstract syntax graph of a lambda calculus visual notation. 
"
Class {
	#name : #SongbirdModel,
	#superclass : #SbModelAbstract,
	#instVars : [
		'earModel',
		'brain',
		'ears'
	],
	#classVars : [
		'BirdNameToBirdModelObjectDictionary',
		'BirdNameToCurryNotationDictionary',
		'BirdSymbols'
	],
	#category : #LambdaCalcModel
}

{ #category : #'instance creation' }
SongbirdModel class >> birdNameToBirdModelObjectDictionary [
	^BirdNameToBirdModelObjectDictionary
]

{ #category : #accessing }
SongbirdModel class >> birdNameToCurryNotationDictionary [
	^BirdNameToCurryNotationDictionary 
]

{ #category : #accessing }
SongbirdModel class >> initBirdNameToCurryNotationDictionary [
	^Dictionary newFromPairs: {
	
	'idiot'. #( \ A . A ).
	'kite'. #( \ A B . B ). 
	'kestrel'. #( \ A B . A ).
	'mockingbird'. #( \ A . A A ).
	
	
	
	
	'thrush'.#( \ a b . b a ).
	'lark'.#( \ a b . a b ).
	'cardinal'. #( \ a b c . a c b ).
	'robin'. #( \ a b c . b c a ) .
	
	'jay'. #( \ a b c d . a b #( a c b ) ).
	'why'. #( \ a . #( \ b . a #( b b ) ) #( \ b . a #( b b ) ) ).
	
	
}
]

{ #category : #initialization }
SongbirdModel class >> initialize [ 
	BirdNameToBirdModelObjectDictionary := Dictionary new.
	BirdNameToCurryNotationDictionary := self initBirdNameToCurryNotationDictionary .
]

{ #category : #generated }
SongbirdModel class >> names [

	^ BirdNameToCurryNotationDictionary keys
]

{ #category : #'instance creation' }
SongbirdModel class >> newModelOf: birdname [

	^ (BirdNameToBirdModelObjectDictionary at: birdname ifAbsentPut: [ 
		   SongbirdModel new parse:
			   (BirdNameToCurryNotationDictionary at: birdname) ]) pcopy
]

{ #category : #'api - graph' }
SongbirdModel >> = x [
	x ifNil: [ ^false ].
	x isBird ifFalse: [ ^false ].

	^brain = x brain 
]

{ #category : #activation }
SongbirdModel >> activate [ 
	| copy |
	copy := self copy .
	self announce: ( SbResultOut new model: copy ) .
	^copy 
]

{ #category : #accessing }
SongbirdModel >> brain [
	^brain
]

{ #category : #accessing }
SongbirdModel >> brain: x [
	brain := x.
	x parent: self
]

{ #category : #accessing }
SongbirdModel >> children [
	^{brain}
]

{ #category : #accessing }
SongbirdModel >> connects [ 
	^earModel connects
]

{ #category : #testing }
SongbirdModel >> depth: x [
	depth := x + 1.
	earModel depth: depth.
	brain depth: depth.
]

{ #category : #accessing }
SongbirdModel >> earModel [
^ earModel
]

{ #category : #accessing }
SongbirdModel >> elementClass [
	^BirdGlob 
]

{ #category : #'gt-extension' }
SongbirdModel >> gtTreeFor: aView [
	<gtView>
	^ aView mondrian
		title: 'Tree';
		painting: [ :aMondrian | self paintTreeWith: aMondrian ]
]

{ #category : #'api - graph' }
SongbirdModel >> hearSong: x [

	| cp |
	cp := x pcopy.

	earModel announce: (SbEarInput new model: cp).

	"wait for animation to finish. "
	[ cp animating ] whileTrue: [ cp el space pulse ].

	earModel doCopyStep: cp.

	^ brain activate
]

{ #category : #'as yet unclassified' }
SongbirdModel >> initFromSymbols: list [
	animating := false.
	ears := Dictionary new.
	self initFromSymbols: list ears: ears depth: 0
]

{ #category : #accessing }
SongbirdModel >> initFromSymbols: list ears: earz depth: d [
	| sb ret |
	"symbols := list."
	depth := d + 1.

	earModel := EarModel new name: list first ; depth: depth.
	earz at: earModel name put: earModel.
	brain := list second = #'.'
		ifTrue: [ self parseSims: (list allButFirst: 2) ears: earz ]
		ifFalse: [ 
			sb := self class new initFromSymbols: list allButFirst ears: earz depth: depth.
			
			ret := RetSlotModel new payload: sb depth: depth. 
			
			sb parent: ret.
			ret].
		
	brain parent: self .
]

{ #category : #'api - graph' }
SongbirdModel >> isBird [
	^true
]

{ #category : #'as yet unclassified' }
SongbirdModel >> messageName [

]

{ #category : #'gt-extension' }
SongbirdModel >> paintTreeWith: view [
	view nodes
		shape: [ :x | 
			| elly textElement |
			elly := BlElement new
				geometry: BlEllipseGeometry new;
				border: (BlBorder paint: Color black);
				constraintsDo: [ :c | 
					"c horizontal fitContent.
					c vertical fitContent."
					"c linear vertical alignCenter.
					c padding: (BlInsets all: 10)" ].
			"elly padding: (BlInsets all: 20).
			elly margin: (BlInsets all: 10)."
			textElement := BlTextElement new.
			textElement
				text:
					(x depth asString asRopedText
						fontSize: 50;
						foreground: Color blue).
			elly addChild: textElement.
			elly ];
		with: (self withDeepCollect: #children).
	view edges
		fromCenterBottom;
		toCenterTop;
		connectToAll: [ :ea | ea children ].
	view edges
		shape: [ :x | 
			BlLineElement new
				border: (BlBorder paint: (Color red alpha: 0.5) width: 5) ];
		passive;
		connectToAll: [ :ea | ea connects ].
	view layout tree.
	^ view
]

{ #category : #accessing }
SongbirdModel >> parse: list [
	list first = #\
		ifTrue: [ ^ SongbirdModel new initFromSymbols: list allButFirst ]
		ifFalse: [ self error ]
]

{ #category : #'as yet unclassified' }
SongbirdModel >> parseSims: list ears: earz [
	list size = 1
		ifTrue: [ ^ RetSlotModel new initFromSymbols: list ears: earz depth: depth  ]
		ifFalse: [ ^ SimModel new initFromSymbols: list ears: earz depth: depth ]
]

{ #category : #accessing }
SongbirdModel >> payload: x [
	brain := x.
	x parent: self
]

{ #category : #'api - graph' }
SongbirdModel >> pcopy [
	RetSlotModel newEarStack .
	^self copy
]

{ #category : #copying }
SongbirdModel >> postCopy [
	announcer := Announcer new.
	earModel := earModel copy.
	RetSlotModel pushEar: earModel.
	depth := RetSlotModel ears size.
	brain := brain copy.
	brain parent: self
]

{ #category : #printing }
SongbirdModel >> printOn: aStream [
	aStream nextPutAll: 'Song '.
	"symbols do: [ :sym | aStream print: sym asString ] ."
	aStream nextPutAll: depth asString.
	aStream nextPutAll: ' '.
	aStream print: earModel.
	aStream nextPutAll: ' ('.
	aStream print: brain.
	aStream nextPutAll: ') '
]

{ #category : #'as yet unclassified' }
SongbirdModel >> simp [
	| codeslot codesbird dataslot |
	dataslot := earModel connects last parent.
	dataslot isDataSlot
		ifTrue: [ codeslot := earModel connects last parent parent codeSlot.
			codeslot isEmpty
				ifFalse: [ dataslot payload hide.
					dataslot parent hide.
					codesbird := codeslot payload payload .
					codesbird earModel hide.
					self halt.
					"codesbird brain depth: codesbird brain depth ."
					
					"codeslot payload payload brain payload depth: 3 ."
					"codeslot payload payload brain depth: 2."
					codeslot payload: codesbird brain.
					
					codeslot depthd .
					
					earModel rconnectTo: codesbird earModel connects last.
					dataslot parent parent payload: codeslot payload ] ]
	"codeslot payload hide ."
]

{ #category : #accessing }
SongbirdModel >> simplify [ 

	"if my ear connects to another ear, we can simplify by dropping second ear. and connecting my ear directly."

	earModel connects last isEar ifTrue: [  
	
		earModel connects last hide .
		earModel rconnectTo: earModel connects last connects last
	] ifFalse: [  
		brain := brain simplify2]. 
	"dataSlot inputingEar" 

	"(earModel announcer announce: #changed)."

	"dataSlot hide ."
]

{ #category : #'api - graph' }
SongbirdModel >> simplifyHearSong: dataSlot [
	dataSlot payload inputingEar rconnectTo: earModel .
]
