"
bird
song

All we need is function abstraction and application. ""Abstracted from what and applied to what?"", you may ask. Other such functions! Actually when they are not applied to anything except each other we refer to them as combinators rather than functions. This is called the pure lambda calculus.

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


  (define sage-bird
    (Î» (x) ((Î» (y) (x (Î» (x) ((y y) x))))
              (Î» (y) (x (Î» (x) ((y y) x)))))))

  ;; ""Bluebirds"" pp. 95-96
  (define bluebird      (Î» (x y z) (x (y z))))

  ;; ""Some Derivatives of the Bluebird"" pp. 96-98
  (define dove          (Î» (x y z w) ((x y) (z w))))
  (define blackbird     (Î» (x y z w) (x ((y z) w))))
  (define eagle         (Î» (x y z w v) ((x y) ((z w) v))))
  (define bunting       (Î» (x y z w v) (x (((y z) w) v))))
  (define dickcissel    (Î» (x y z w v) (((x y) z) (w v))))
  (define becard        (Î» (x y z w) (x (y (z w)))))
  (define dovekies      (Î» (x y z w v) ((x (y z)) (w v))))
  (define bald-eagle    (Î» (x y z w v u t)
                          ((x ((y z) w)) ((v u) t))))

  ;; ""Some Other Birds"" pp. 99-101
  (define warbler       (Î» (x y) ((x y) y)))
  (define cardinal      (Î» (x y z) ((x z) y)))
  (define thrush        (Î» (x y) (y x)))

  ;; ""Bluebirds and Thrushes"" pp. 101-103
  (define robin         (Î» (x y z) ((y z) x)))
  (define finch         (Î» (x y z) ((z y) x)))
  (define vireo         (Î» (x y z) ((z x) y)))

  ;; ""Some Relatives"" pp. 103-105
  (define cardinal*     (Î» (x y z w) (((x y) w) z)))
  (define robin*        (Î» (x y z w) (((x z) w) y)))
  (define finch*        (Î» (x y z w) (((x w) z) y)))
  (define vireo*        (Î» (x y z w) (((x w) z) y)))
  (define cardinal**    (Î» (x y z w v) ((((x y) z) w) v)))
  (define robin**       (Î» (x y z w v) ((((x y) w) v) z)))
  (define finch**       (Î» (x y z w v) ((((x y) v) w) z)))
  (define vireo**       (Î» (x y z w v) ((((x y) z) w) v)))

  ;; ""Queer Birds"" pp. 105-108
  (define queer-bird       (Î» (x y z) (y (x z))))
  (define quixotic-bird    (Î» (x y z) (x (z y))))
  (define quizzical-bird   (Î» (x y z) (y (z x))))
  (define quirky-bird      (Î» (x y z) (z (x y))))
  (define quacky-bird      (Î» (x y z) (z (y x))))
  (define goldfinch        (Î» (x y z w) ((x w) (y z))))

  ;; ""More on Mockingbirds"" pp. 117-118
  (define double-mockingbird  (Î» (x y) ((x y) (x y))))

  ;; ""Warblers"" pp. 118-120
  (define converse-warbler (Î» (x y) ((y x) x)))
  (define warbler*         (Î» (x y z) (((x y) z) z)))
  (define warbler**        (Î» (x y z w) ((((x y) z) w) w)))
  (define hummingbird      (Î» (x y z) (((x y) z) y)))

  ;; ""Starlings"" pp. 120-121
  (define starling         (Î» (x y z) ((x z) (y z))))

  ;; ""Starlings in Action"" pp. 121-125
  (define phoenix          (Î» (x y z w) ((x (y w)) (z w))))
  (define psi-bird         (Î» (x y z w) ((x (y z)) (y w))))

  ;; ""The Turing Bird"" pp. 132-133
  (define turing-bird      (Î» (x y) (y ((x x) y))))

  ;; ""Owls"" p. 133
  (define owl              (Î» (x y) (y (x y))))

  ;; ""Aristocratic Birds"" pp. 179-181
  (define jay              (Î» (x y z w) ((x y) ((x w) z))))

  ;; Aliases
  (define oracle-bird sage-bird)
  (define idiot-bird identity-bird)

  ;; A few birds and aliases not necessarily given in the book
  ;; but discussed in David Keenan's http://dkeenan.com/Lambda/
  (define identity-bird*   (Î» (x y) (x y)))
  (define kite             (Î» (x y) y))
  (define konstant-mocker  (Î» (x y) (y y)))
  (define crossed-konstant-mocker (Î» (x y) (x x)))
  (define idiot-bird* identity-bird*)
  (define pairing vireo))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The single-letter names of the various combinators
;; as given in ""Who's Who Among The Birds"", pp. 244-246
(module combinator-letters *
  (import scheme combinator-birds)
  (define B bluebird)
  (define C cardinal)
  (define D dove)
  (define E eagle)
  (define F finch)
  (define G goldfinch)
  (define H hummingbird)
  (define I identity-bird)
  (define J jay)
  (define K kestrel)
  (define L lark)
  (define M mockingbird)
  ;; P is used in ""Russell's Forest"" pp. 151-153
  (define O owl)
  ;; N is used in ""Curry's Lively Bird Forest"" pp. 143-147
  (define Q queer-bird)
  (define R robin)
  (define S starling)
  (define T thrush)
  (define U turing-bird)
  (define V vireo)
  (define W warbler)
  ;; X is used in ""The Master Forest"" pp. 167-178
  (define Y sage-bird))


"
Class {
	#name : #SongbirdModel,
	#superclass : #SbModelAbstract,
	#instVars : [
		'earModel',
		'brain',
		'ears',
		'fullName'
	],
	#classVars : [
		'BirdNameToBirdModelObjectDictionary',
		'BirdNameToCurryNotationDictionary',
		'BirdSymbols'
	],
	#category : #LambdaCalcModel
}

{ #category : #'instance creation' }
SongbirdModel class >> addNewModel: m name: birdname [
	^ BirdNameToBirdModelObjectDictionary
		at: birdname
		ifAbsentPut: [ m fullName: birdname.
			m ]
]

{ #category : #generated }
SongbirdModel class >> all [

	^ BirdNameToBirdModelObjectDictionary  values 
]

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
	
	'i'.			#( \ A . A ).
	'ki'.			#( \ A B . B ). 
	'kx'.		#( \ A B . A ).
	'M'.	 	#( \ A . A A ).
	
	"'thrush'.			#( \ a b . b a ).
	'lark'	.			#( \ A B . A B ).
	'cardinal'.		#( \ a b c . a c b ).
	'robin'.			#( \ a b c . b c a ) .
	
	'jay'.				#( \ a b c d . a b #( a c b ) )."

	"'why'. 			#( \ a . #( \ b . a #( b b ) ) #( \ b . a #( b b ) ) )."
	
	
}
]

{ #category : #initialization }
SongbirdModel class >> initialize [ 
	BirdNameToBirdModelObjectDictionary := StandardOrderedDictionary  new.
	BirdNameToCurryNotationDictionary := self initBirdNameToCurryNotationDictionary .
	
	
	{ 'i'. 'ki'. 'kx' . 'M'} do: [ :ea | self newModelOf: ea].
	
	
	
	"self names do: [ :ea | self newModelOf: ea ]."
	
GlutinWindowsRegistry default windowsDo: [ :w | w title:  GtImage instance version versionString ]
]

{ #category : #generated }
SongbirdModel class >> names [

	^ "BirdNameToCurryNotationDictionary keys" { 'i'. 'ki'. 'kx' . 'M'}
]

{ #category : #'instance creation' }
SongbirdModel class >> newModelOf: birdname [
	| sb |
	"BirdNameToBirdModelObjectDictionary at: birdname put: sb ."
	^ (BirdNameToBirdModelObjectDictionary
		at: birdname
		ifAbsentPut: [ "SongbirdModel new parse:
			   (BirdNameToCurryNotationDictionary at: birdname); fullName: birdname "
			sb := SongbirdModel new
				parse: (BirdNameToCurryNotationDictionary at: birdname).
			sb fullName: birdname.
			sb ]) pcopy
]

{ #category : #initialization }
SongbirdModel class >> xxx [ 
	BirdNameToBirdModelObjectDictionary := Dictionary new.
	
]

{ #category : #'api - graph' }
SongbirdModel >> = x [
	x ifNil: [ "self halt." ^false ].
	
	self == x ifTrue: [ ^ true ].
	
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

{ #category : #accessing }
SongbirdModel >> fullName [
^ fullName
]

{ #category : #accessing }
SongbirdModel >> fullName: x [
fullName := x
]

{ #category : #'gt-extension' }
SongbirdModel >> gtTreeFor2: aView [
	<gtView>
	| xx sb in bb dd anEdge |
	^ aView mondrian
		title: 'Tree2';
		painting: [ :aMondrian | 
			"self paintTreeWith: aMondrian"
			"aMondrian nodes
				shape: [ :x | BirdGlob new initFromModel: x ]."
			xx := OrderedCollection new.
			dd := Dictionary new.
			SongbirdModel names
				do: [ :ea | 
					| new |
					sb := SongbirdModel newModelOf: ea.
					SongbirdModel names
						do: [ :inputName | 
							in := SongbirdModel newModelOf: inputName.
							dd at: in put: sb.

							"(sb fullName = 'M' and: [ in fullName = 'M' ])
								ifFalse: [ new := sb hearSong: in ]."

							"aMondrian nodes shape: [ :x | BirdGlob new initFromModel: x ]; with: { new } ."

							"sb graph connectTo: new ."

							"mm := SongbirdModel all
						detect: [ :eab | eab = new ]
						ifNone: [ new  ]."
							"xx add: new. "
							"xx add: sb.
							xx add: in."
							xx := aMondrian nodes
								shape: [ :x | BirdGlob new initFromModel: x ];
								with: { sb . in } ] .
							
							"xx first  graph connectTo: xx second ."
							
							
				"aMondrian edges connect: dd associations from: #key to: #value."	
					
					aMondrian edges connect: { sb -> in } from: #key to: #value.		
							
							
		"xx first addConnectedEdge: anEdge.
		xx second addConnectedEdge: anEdge."	
							
].
		
			"bb := aMondrian topStep root graph nodeChildren."

			"collect: [ :each | each graph model ]."

			""
			
			"dd keysAndValuesDo: [ :key :val | key graph connectTo: val ]."

			"bb first graph connectTo: bb last.
					
			self halt ."


			"aMondrian edges connectToAll: bb last ."

			""

			"aMondrian edges"
			"fromCenterBottom;
				toCenterTop;"
			"connectFrom: [ :ea | in ] to: [ :ea | sb ]"
			"connectToAll: [ :ea | {bb first } ]."
			aMondrian layout "grid"	tree ]
]

{ #category : #'gt-extension' }
SongbirdModel >> gtTreeFor: aView [
	<gtView>
	^ aView mondrian
		title: 'Tree';
		painting: [ :aMondrian | self paintTreeWith: aMondrian ]
]

{ #category : #'gt-extension' }
SongbirdModel >> gtTreexxFor: aView [
	<gtView>
	^ aView mondrian
		title: 'Treexxxxxxxxxxxxxx';
		painting: [ :aMondrian | "self paintTreeWith: aMondrian"
		
		aMondrian nodes
		shape: [ :x | 
			| elly textElement | 
			elly := BlElement new
				geometry: BlEllipseGeometry new;
				border: (BlBorder paint: Color black);
				layout: BlLinearLayout horizontal;
				constraintsDo: [ :c | 
					c horizontal fitContent.
					c vertical fitContent.
					"c linear vertical alignCenter.
					c padding: (BlInsets all: 10)" ].
				
			elly padding: (BlInsets all: 20).
			elly margin: (BlInsets all: 10).
			
			textElement := BlTextElement new.
			"x isSim  ifTrue: [ self halt ]."
			"x name = nil ifTrue: [ x name: x earModel name ]."
			textElement
				text:
					((x name ", ' ' , depth asString") asRopedText
						fontSize: 20;
						foreground: Color blue).
			elly addChild: textElement.
			elly ];
		with: (self withDeepCollect: #children).
	aMondrian edges
		fromCenterBottom;
		toCenterTop;
		connectToAll: [ :ea | ea children ].
	aMondrian edges
		shape: [ :x | 
			BlLineElement new
				border: (BlBorder paint: (Color red alpha: 0.5) width: 5) ];
		passive;
		connectToAll: [ :ea | ea connects ].
	aMondrian layout tree.	
			
			
			 ]
]

{ #category : #'gt-extension' }
SongbirdModel >> gtTreexxzzFor: aView [
	<gtView> "sing all birds to me, show outputs"
	^ aView mondrian
		title: 'Tzzzzx';
		painting: [ :aMondrian | 
			
			SongbirdModel all do: [ :ea | "self halt." self hearSong: ea.
				
				
				"show output results. experiment. grok...."
				
				 ].

			aMondrian nodes
				shape: [ :x | 
					| elly textElement |
					elly := BlElement new
						geometry: BlEllipseGeometry new;
						border: (BlBorder paint: Color black);
						layout: BlLinearLayout horizontal;
						constraintsDo: [ :c | 
							c horizontal fitContent.
							c vertical fitContent ].
					elly padding: (BlInsets all: 20).
					elly margin: (BlInsets all: 10).
					textElement := BlTextElement new.
					"x isSim  ifTrue: [ self halt ]."
					"x name = nil ifTrue: [ x name: x earModel name ]."
					textElement
						text:
							(x fullName asRopedText
								fontSize: 20;
								foreground: Color blue).	", ' ' , depth asString"
					elly addChild: textElement.
					elly ];
				with: SongbirdModel all "(self withDeepCollect: #children)".
		
			aMondrian layout tree ]
]

{ #category : #'api - graph' }
SongbirdModel >> hearSong: x [

	| cp |
	
	(fullName = 'M' and: [x fullName = 'M']) ifTrue: [ "self halt." "^omega" ^ self ].
	
	
	cp := x pcopy.
	

	earModel announce: (SbEarInput new model: cp).

	"wait for animation to finish. "
	[ cp animating ] whileTrue: [ cp el space pulse ].

	earModel doCopyStep: cp.

	^ brain activate
]

{ #category : #initialization }
SongbirdModel >> initFromSymbols: list [
	"fullName := ' ? '.
	animating := false.
	ears := Dictionary new."
	self initFromSymbols: list ears: ears depth: 0
]

{ #category : #accessing }
SongbirdModel >> initFromSymbols: list ears: earz depth: d [
	| sb ret |
	"symbols := list."
	depth := d + 1.
	
	name := ' _ ' .

	earModel := EarModel new name: list first ; depth: depth.
	earz at: earModel name put: earModel.
	name := earModel name .
	brain := list second = #'.'
		ifTrue: [ self parseSims: (list allButFirst: 2) ears: earz ]
		ifFalse: [ 
			sb := self class new initFromSymbols: list allButFirst ears: earz depth: depth.
			
			ret := RetSlotModel new payload: sb depth: depth. 
			
			sb parent: ret.
			ret].
		
	brain parent: self .
]

{ #category : #initialization }
SongbirdModel >> initialize [
	super initialize .
	
	"fullName := ' ? '."
	animating := false.
	ears := Dictionary new.
	
]

{ #category : #'api - graph' }
SongbirdModel >> isBird [
	^true
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
	aStream nextPutAll: ' '.
	"symbols do: [ :sym | aStream print: sym asString ] ."
	fullName
		ifNotNil: [ aStream nextPutAll: fullName.
			^ self ].
	"aStream nextPutAll: ' '.
	aStream nextPutAll: depth asString.
	aStream nextPutAll: ' '."
	aStream print: earModel.
	aStream nextPutAll: '('.
	aStream print: brain.
	aStream nextPutAll: ')'
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
