Class {
	#name : #MmNextAnnouncement,
	#superclass : #Announcement,
	#instVars : [
		'next'
	],
	#category : #'Metamath-Bloc'
}

{ #category : #accessing }
MmNextAnnouncement >> next [
	^ next
]

{ #category : #accessing }
MmNextAnnouncement >> next: anObject [
	next := anObject
]
