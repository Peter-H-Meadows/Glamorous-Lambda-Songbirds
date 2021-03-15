Class {
	#name : #MmProofResultListener,
	#superclass : #MmAbstractEventListener,
	#category : #'Metamath-Bloc-Listeners'
}

{ #category : #accessing }
MmProofResultListener >> clickEvent: anEvent [

anEvent currentTarget clicked .


gameController wantedResultClicked: anEvent currentTarget .

anEvent consumed: true.
]
