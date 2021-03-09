"
bird
song
"
Class {
	#name : #SongbirdModel,
	#superclass : #SbModelAbstact,
	#instVars : [
		'earModel',
		'brain',
		'ears'
	],
	#classVars : [
		'BirdSymbols',
		'ModelObjects'
	],
	#category : #LambdaCalcModel
}

{ #category : #'as yet unclassified' }
SongbirdModel class >> birdNames [
^ Dictionary newFromPairs: {
'idiot'. 
#( \ A . A ).

'kite'.
#( \ A . B B ). 

'kestrel'. 
#( \ A B . A ).

'mockingbird'.
#( \ A . A B ).

'jay'.
#( \ a b c d . a b #( a c b ) ).

'cardinal'.
#( \ a b c . a c b ).

'thrush'.
#( \ a b . b a ).

}
]

{ #category : #'as yet unclassified' }
SongbirdModel class >> idiotModel [
^ self new parse: self idiotSymbols 
]

{ #category : #'as yet unclassified' }
SongbirdModel class >> idiotSymbols [
^ #( \ a . a )
]

{ #category : #initialization }
SongbirdModel class >> initialize [ 
ModelObjects := Dictionary new.
BirdSymbols := Dictionary newFromPairs: {

'idiot'. 
#( \ A . A ).

'kite'.
#( \ A B . B ). 

'kestrel'. 
#( \ A B . A ).

'mockingbird'.
#( \ A . A A ).

'jay'.
#( \ a b c d . a b #( a c b ) ).

'cardinal'.
#( \ a b c . a c b ).

'thrush'.
#( \ a b . b a ).

}
]

{ #category : #generated }
SongbirdModel class >> names [ 
^ BirdSymbols keys
]

{ #category : #'instance creation' }
SongbirdModel class >> newModelOf: birdname [
	^ (ModelObjects
		at: birdname
		ifAbsentPut: [ SongbirdModel new parse: (BirdSymbols at: birdname) ]) pcopy
]

{ #category : #'api - graph' }
SongbirdModel >> = x [
x ifNil: [^false].
 x isBird ifFalse: [ ^ false  ] .

^ brain = x brain 
]

{ #category : #activation }
SongbirdModel >> activate [ 
| copy |
copy := self copy .
self announcer announce: ( SbResultOut new model: copy ) .
^ copy 
]

{ #category : #accessing }
SongbirdModel >> brain [
^ brain
]

{ #category : #accessing }
SongbirdModel >> brain: x [
brain := x.
x parent: self
]

{ #category : #'as yet unclassified' }
SongbirdModel >> children [

^ { brain }
]

{ #category : #'as yet unclassified' }
SongbirdModel >> connects [ 

^ earModel connects
]

{ #category : #testing }
SongbirdModel >> depth: x [
depth := x + 1 .
earModel depth: depth .
brain depth: depth .
]

{ #category : #accessing }
SongbirdModel >> earModel [
^ earModel
]

{ #category : #accessing }
SongbirdModel >> elementClass [
^ BirdGlob 
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
	"1 seconds asDelay wait."
	"self halt ."
	
	| cp |
	"Earz := OrderedCollection new . 
	SbDepth := 1 ."
	cp := x pcopy .
	
	earModel announcer announce: ( SbEarInput new model: cp ) .
	
	"wait for animation to finish. "
	[ cp animating ] whileTrue: [ cp el space pulse ].

	earModel doCopyStep: cp .
	
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
	depth := d + 1 .

	earModel := EarModel new name: list first ; depth: depth .
	earz at: earModel name put: earModel.
	brain := list second = #'.'
		ifTrue: [ self parseSims: (list allButFirst: 2) ears: earz ]
		ifFalse: [ 
			sb := self class new initFromSymbols: list allButFirst ears: earz depth: depth .
			
			ret := RetSlotModel new payload: sb depth: depth . 
			
			sb parent: ret .
			ret
			
 ].
		
	brain parent: self .
]

{ #category : #'api - graph' }
SongbirdModel >> isBird [

^ true
]

{ #category : #'gt-extension' }
SongbirdModel >> paintTreeWith: view [
	view nodes
		shape: [ :x | | elly textElement |
			elly := BlElement new
				geometry: BlEllipseGeometry new;
				border: (BlBorder paint: Color black);
				constraintsDo: [ :c | c padding: (BlInsets all: 10) ] .
				
			textElement := BlTextElement new.
			textElement text: ( x depth asString asRopedText fontSize: 50; foreground: Color blue).
			elly addChild: textElement .
			
			elly 	
				
			];
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
	^ self copy
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

{ #category : #'as yet unclassified' }
SongbirdModel >> simplify [ 

"if my ear connects to another ear, we can simplify by dropping second ear. and connecting my ear directly."

earModel connects last isEar ifTrue: [  
	
	earModel connects last hide .
	earModel rconnectTo: earModel connects last connects last .
	
] ifFalse: [  

	brain := brain simplify2 .

]. 


"dataSlot inputingEar" 

"(earModel announcer announce: #changed)."

"dataSlot hide ."
]

{ #category : #'api - graph' }
SongbirdModel >> simplifyHearSong: dataSlot [

dataSlot payload inputingEar rconnectTo: earModel .
]
