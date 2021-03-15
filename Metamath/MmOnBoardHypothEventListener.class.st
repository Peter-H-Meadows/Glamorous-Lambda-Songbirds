Class {
	#name : #MmOnBoardHypothEventListener,
	#superclass : #MmAbstractEventListener,
	#instVars : [
		'model',
		'gameModel',
		'element'
	],
	#category : #'Metamath-Bloc-Listeners'
}

{ #category : #'mouse handlers' }
MmOnBoardHypothEventListener >> clickEvent: anEvent [
anEvent currentTarget clicked .
anEvent currentTarget isSelected ifTrue: [
gameController onBoardeHypothClicked: anEvent currentTarget .]
]
