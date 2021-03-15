Class {
	#name : #MmAbstractEventListener,
	#superclass : #BlEventListener,
	#instVars : [
		'gameController',
		'myModel'
	],
	#category : #'Metamath-Bloc-Listeners'
}

{ #category : #accessing }
MmAbstractEventListener >> gameController [
	^ gameController
]

{ #category : #accessing }
MmAbstractEventListener >> gameController: anObject [
	gameController := anObject
]

{ #category : #'mouse handlers' }
MmAbstractEventListener >> mouseEnterEvent: anEvent [

anEvent target border: (BlBorder paint: (Color gray alpha: 0.8) width: 1).
]

{ #category : #'mouse handlers' }
MmAbstractEventListener >> mouseLeaveEvent: anEvent [

anEvent target border: (BlBorder paint: (Color veryVeryDarkGray ) width: 0).
]

{ #category : #accessing }
MmAbstractEventListener >> myModel: m [

myModel := m
]
