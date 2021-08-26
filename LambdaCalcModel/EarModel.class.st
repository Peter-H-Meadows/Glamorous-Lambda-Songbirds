"
bird's ear.
is connected to slots.
puts a copy of payload in each slot it's connected to.

"
Class {
	#name : 'EarModel',
	#superclass : 'SbModelAbstract',
	#instVars : [
		'connects'
	],
	#category : 'LambdaCalcModel'
}

{ #category : 'initialization' }
EarModel >> clear [
	connects := OrderedCollection new .
	color := Color random.
	"name := '_'"
]

{ #category : 'as yet unclassified' }
EarModel >> connectTo [
]

{ #category : 'accessing' }
EarModel >> connectTo: slot [
	slot inputingEar: self.
	connects add: slot
]

{ #category : 'accessing' }
EarModel >> connects [
	^connects
]

{ #category : 'testing' }
EarModel >> depth: x [
	depth := x .
]

{ #category : 'accessing' }
EarModel >> doCopyStep: x [
	connects
		do: [ :ea | 
			| cp |
			cp := x pcopy.
			self announce: (SbEarCopyAdded new model: cp).
			ea setPayloadAndAnnounce: cp.
			[ cp animating ] whileTrue: [ x el space pulse ] ]
]

{ #category : 'accessing' }
EarModel >> hide [
	self announce: #hide
]

{ #category : 'initialization' }
EarModel >> initialize [
	super initialize .
	connects := OrderedCollection new .
	color := Color random.
	name := ''
]

{ #category : 'accessing' }
EarModel >> inputingEar: x [
	"| last |
	inputingEar := x .
	color := inputingEar color .
	self announce: #changed .
	last := connects last .
	connects := OrderedCollection new .
	self connectTo: last ."
]

{ #category : 'testing' }
EarModel >> isEar [
	^true
]

{ #category : 'copying' }
EarModel >> postCopy [
	depth := RetSlotModel ears size + 1.
	announcer := Announcer new.
	connects := OrderedCollection new.
	color := Color random
]

{ #category : 'testing' }
EarModel >> printOn: aStream [

aStream nextPutAll: name .
aStream nextPutAll: depth asString.
aStream nextPutAll: '. '
]

{ #category : 'as yet unclassified' }
EarModel >> rconnectTo: slot [ 

connects := OrderedCollection new .
self connectTo: slot .

]
