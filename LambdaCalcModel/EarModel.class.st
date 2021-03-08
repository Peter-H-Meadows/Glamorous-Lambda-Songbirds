"
bird's ear.
is connected to slots.
puts a copy of payload in each slot it's connected to.

"
Class {
	#name : #EarModel,
	#superclass : #SbModelAbstact,
	#instVars : [
		'connects'
	],
	#category : #LambdaCalcModel
}

{ #category : #'as yet unclassified' }
EarModel >> connectTo [
]

{ #category : #'as yet unclassified' }
EarModel >> connectTo: slot [
slot inputingEar: self .
connects add: slot
]

{ #category : #'as yet unclassified' }
EarModel >> connects [
^connects
]

{ #category : #testing }
EarModel >> depth: x [
depth := x .
]

{ #category : #'as yet unclassified' }
EarModel >> doCopyStep: x [
	| cp |
	connects reverse
		do: [ :ea | 
			cp := x pcopy.
			self announcer announce: (SbEarCopyAdded new model: cp).
			ea setPayloadAndAnnounce: cp.
			[ cp animating ] whileTrue: [ x el space pulse ] ]
]

{ #category : #accessing }
EarModel >> hide [

self announcer announce: #hide .
]

{ #category : #initialization }
EarModel >> initialize [
super initialize .
connects := OrderedCollection new .
color := Color random.
name := '_'
]

{ #category : #accessing }
EarModel >> inputingEar: x [
"| last |
inputingEar := x .
color := inputingEar color .
self announcer announce: #changed .
last := connects last .
connects := OrderedCollection new .
self connectTo: last ."
]

{ #category : #testing }
EarModel >> isEar [
^ true
]

{ #category : #copying }
EarModel >> postCopy [ 
depth := RetSlotModel ears size + 1. 
announcer := Announcer new .
connects := OrderedCollection new .
]

{ #category : #testing }
EarModel >> printOn: aStream [

aStream nextPutAll: '@ ' .
aStream nextPutAll: depth asString.
aStream nextPutAll: ' ' .
aStream nextPutAll: name .
]

{ #category : #'as yet unclassified' }
EarModel >> rconnectTo: slot [ 

connects := OrderedCollection new .
self connectTo: slot .

]

{ #category : #'as yet unclassified' }
EarModel >> simp [ 

"if ear is connected to data, and code is a bird.."
]
