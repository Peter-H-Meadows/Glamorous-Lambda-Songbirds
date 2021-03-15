Class {
	#name : #MmStartEventListener,
	#superclass : #MmAbstractEventListener,
	#instVars : [
		'model',
		'gameModel',
		'element'
	],
	#category : #'Metamath-Bloc-Listeners'
}

{ #category : #'mouse handlers' }
MmStartEventListener >> clickEvent: anEvent [

"so we want to try and use this assertion to make wanted "

MmGame new openGame: anEvent currentTarget model .
]
