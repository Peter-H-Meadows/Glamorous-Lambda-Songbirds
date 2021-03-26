"
a
"
Class {
	#name : #SbModelAbstract,
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
SbModelAbstract >> animating [
	^animating
]

{ #category : #accessing }
SbModelAbstract >> animating: x [
	animating := x
]

{ #category : #accessing }
SbModelAbstract >> announce: anAnnouncement [

	self announcer announce: anAnnouncement
]

{ #category : #accessing }
SbModelAbstract >> announcer [
	^announcer ifNil: [ announcer := Announcer new ]
]

{ #category : #initialization }
SbModelAbstract >> color [
	"connects isEmpty ifTrue: [ ^ Color veryDarkGray  ] ."
	^color
]

{ #category : #accessing }
SbModelAbstract >> color: c [
	color := c
]

{ #category : #testing }
SbModelAbstract >> depth [
	^depth
]

{ #category : #testing }
SbModelAbstract >> depth: x [
	depth := x .
	payload ifNotNil: [ payload depth: depth ]
]

{ #category : #accessing }
SbModelAbstract >> el [
	^el
]

{ #category : #accessing }
SbModelAbstract >> el: x [
	el := x
]

{ #category : #initialization }
SbModelAbstract >> initialize [
	super initialize .
	announcer := Announcer new
]

{ #category : #testing }
SbModelAbstract >> isBird [
	^false
]

{ #category : #testing }
SbModelAbstract >> isEar [
	^false
]

{ #category : #testing }
SbModelAbstract >> isSim [
	^false
]

{ #category : #testing }
SbModelAbstract >> name [
	^name
]

{ #category : #testing }
SbModelAbstract >> name: x [
	name := x
]

{ #category : #testing }
SbModelAbstract >> name: x depth: d [
	depth := d .
	name := x
]

{ #category : #accessing }
SbModelAbstract >> parent [
	^parent
]

{ #category : #accessing }
SbModelAbstract >> parent: x [
	parent := x.
]
