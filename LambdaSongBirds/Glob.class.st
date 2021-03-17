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
		'SelectedElements',
		'SelectedElementsX'
	],
	#category : #'LambdaSongBirds-GUI'
}

{ #category : #'class initialization' }
Glob class >> initialize [
	self "startConnectMode" startXMode.
	SelectedElements := Set new
]

{ #category : #'class initialization' }
Glob class >> startConnectMode [
	ModeBlock := [ :sb1 :sb2 | sb2 connectTo: sb1 ].
	SelectedElements := Set new
]

{ #category : #'class initialization' }
Glob class >> startSingMode [
	ModeBlock := [ :sb1 :sb2 | sb2 hearSong: sb1 ].
	SelectedElements := Set new
]

{ #category : #'class initialization' }
Glob class >> startXMode [
	ModeBlock := [ :sb1 :sb2 | sb2 swapFor: sb1 ].
	SelectedElements := Set new
]

{ #category : #initialization }
Glob >> initialize [
	super initialize.
	self geometry: (BlRoundedRectangleGeometry cornerRadius: 10).	"BlRectangleGeometry"

	"self border: (BlBorder paint: Color gray width: 2 )."
	self padding: (BlInsets all: 20).
	self
		constraintsDo: [ :c | 
			c horizontal fitContent.
			c vertical fitContent.
			c linear vertical alignCenter ];
		"padding: ( BlInsets top: 10 bottom: 10 );"
			"padding: (BlInsets all: 10);
margin: (BlInsets all: 10);"
			clipChildren: false;
		layout: BlLinearLayout horizontal.
	self
		addEventHandler:
			(BlEventHandler
				on: BlClickEvent
				do: [ :evt | 
					self click.
					evt consumed: true ])
]

{ #category : #'as yet unclassified' }
Glob >> makeClone [
	| el |
	el := model elementClass new initFromModel: model pcopy.
	el relocate: 500 atRandom @ 200 atRandom.
	self space addChild: el.
	el addEventHandler: BlPullHandler new
]

{ #category : #accessing }
Glob >> model [ 
^ model
]
