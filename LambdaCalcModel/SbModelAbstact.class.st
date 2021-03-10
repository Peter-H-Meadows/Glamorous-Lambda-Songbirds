"
a
"
Class {
	#name : #SbModelAbstact,
	#superclass : #Object,
	#instVars : [
		'announcer',
		'name',
		'parent',
		'depth',
		'el',
		'animating',
		'color',
		'payload'
	],
	#category : #LambdaCalcModel
}

{ #category : #accessing }
SbModelAbstact >> animating [
^ animating
]

{ #category : #accessing }
SbModelAbstact >> animating: x [
animating := x
]

{ #category : #accessing }
SbModelAbstact >> announcer [
^ announcer ifNil: [ announcer := Announcer new ]
]

{ #category : #initialization }
SbModelAbstact >> color [

"connects isEmpty ifTrue: [ ^ Color veryDarkGray  ] ."

^ color
]

{ #category : #accessing }
SbModelAbstact >> color: c [
color := c

]

{ #category : #testing }
SbModelAbstact >> depth [
^ depth
]

{ #category : #testing }
SbModelAbstact >> depth: x [
depth := x .
payload ifNotNil: [ payload depth: depth ]
 
]

{ #category : #accessing }
SbModelAbstact >> el [
^ el
]

{ #category : #accessing }
SbModelAbstact >> el: x [

el := x
]

{ #category : #initialization }
SbModelAbstact >> initialize [
super initialize .
announcer := Announcer new
]

{ #category : #testing }
SbModelAbstact >> isBird [
^ false
]

{ #category : #testing }
SbModelAbstact >> isEar [
^ false
]

{ #category : #testing }
SbModelAbstact >> name [
^ name
]

{ #category : #testing }
SbModelAbstact >> name: x [
name := x
]

{ #category : #testing }
SbModelAbstact >> name: x depth: d [
depth := d .
name := x
]

{ #category : #accessing }
SbModelAbstact >> parent [
^ parent
]

{ #category : #accessing }
SbModelAbstact >> parent: x [
parent := x.
]
