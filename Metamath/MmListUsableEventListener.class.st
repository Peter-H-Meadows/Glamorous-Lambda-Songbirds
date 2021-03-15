Class {
	#name : #MmListUsableEventListener,
	#superclass : #MmAbstractEventListener,
	#instVars : [
		'model',
		'gameModel',
		'element'
	],
	#category : #'Metamath-Bloc-Listeners'
}

{ #category : #'mouse handlers' }
MmListUsableEventListener >> clickEvent: anEvent [

"this is always assertion from usable list. so make new element."

"| cp |
cp := anEvent currentTarget model copy gameElement ."

gameController usableBasicAssertionFromListClicked: anEvent currentTarget model .

]
