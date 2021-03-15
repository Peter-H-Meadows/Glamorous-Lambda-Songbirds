Class {
	#name : #MmUsableEventListener,
	#superclass : #MmAbstractEventListener,
	#instVars : [
		'model',
		'gameModel',
		'element'
	],
	#category : #'Metamath-Bloc-Listeners'
}

{ #category : #accessing }
MmUsableEventListener >> clickEvent: anEvent [

gameController addToWorkingBoard: anEvent currentTarget model .
]

{ #category : #accessing }
MmUsableEventListener >> element: e [

element := e
]

{ #category : #accessing }
MmUsableEventListener >> gameModel: m [

gameModel := m
]

{ #category : #accessing }
MmUsableEventListener >> model: m [

model := m
]
