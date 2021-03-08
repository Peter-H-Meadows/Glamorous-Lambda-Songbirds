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
self startSingMode .
SelectedElements := Set new .

]

{ #category : #'class initialization' }
Glob class >> startConnectMode [ 

ModeBlock := [ :sb1 :sb2 | sb1 connectTo: sb2 ] .
SelectedElements := Set new .

]

{ #category : #'class initialization' }
Glob class >> startEatMode [ 
ModeBlock := [ :sb1 :sb2 | sb2 eatBird: sb1 ] .
SelectedElements := Set new .

]

{ #category : #'class initialization' }
Glob class >> startSingMode [ 

ModeBlock := [ :sb1 :sb2 | sb2 hearSong: sb1 ] .
SelectedElements := Set new .

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

{

('' -> [ :e |
	 
	"self doStep ."

]).


"('delete' -> [ :e | 
	self removeFromParent .
])."




('make a clone of me' -> [ :e | 
	
	self makeClone .

]).





('inspect self' -> [ :e | 
	
	self inspect .

]).


};

								yourself);
						yourself);
				yourself ];
		yourself.	
	
	
	
	
	self addViewModel: menumodel .
	self addLook: BrWithContextMenuLook new .
	
]

{ #category : #accessing }
Glob >> animating [
^ animating
]

{ #category : #accessing }
Glob >> animating: x [
animating := x
]

{ #category : #accessing }
Glob >> announcer [
^ announcer ifNil: [ announcer := Announcer new ]
]

{ #category : #'event handling' }
Glob >> click [

"self border: (BlBorder paint:  Color black  width: 2 ) ."

SelectedElements isEmpty ifTrue: [ ^ SelectedElements add: self ] .

"( SelectedElements includes: self ) ifTrue: [ ^ false ] ."

ModeBlock value: SelectedElements anyOne  value: self .

SelectedElements := Set new .
]

{ #category : #deprecated }
Glob >> eatBird: x [

"x removeFromParent .
self addChild: x before: mouthSlot .
eatenBird := x ."

]

{ #category : #accessing }
Glob >> hide [ 

"self visibility: BlVisibility hidden ."

"self border: (BlBorder paint: Color random width: 0) ."

self border width: 0

]

{ #category : #initialization }
Glob >> initialize [

super initialize .

self geometry: "BlRectangleGeometry" ( BlRoundedRectangleGeometry  cornerRadius: 10 ).

"self border: (BlBorder paint: Color gray width: 2 )."

self padding: (BlInsets all: 20).

self constraintsDo: [ :c | 
					c horizontal fitContent.
					c vertical fitContent .
					c linear vertical alignCenter ];

"padding: ( BlInsets top: 10 bottom: 10 );"
"padding: (BlInsets all: 10);
margin: (BlInsets all: 10);"
clipChildren: false ;
layout: BlLinearLayout horizontal .


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

el :=  model elementClass new initFromModel: model pcopy .

el relocate: 500 atRandom @ 200 atRandom  .

self space addChild: el .

el 	addEventHandler: BlPullHandler new.

]

{ #category : #accessing }
Glob >> model [ 
^ model
]
