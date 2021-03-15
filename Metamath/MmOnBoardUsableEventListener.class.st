Class {
	#name : #MmOnBoardUsableEventListener,
	#superclass : #MmAbstractEventListener,
	#instVars : [
		'model',
		'gameModel',
		'element'
	],
	#category : #'Metamath-Bloc-Listeners'
}

{ #category : #'mouse handlers' }
MmOnBoardUsableEventListener >> clickEvent: anEvent [

anEvent currentTarget clicked .
anEvent currentTarget isSelected ifTrue: [  gameController usableClickedFromBoard: anEvent currentTarget ]
]
