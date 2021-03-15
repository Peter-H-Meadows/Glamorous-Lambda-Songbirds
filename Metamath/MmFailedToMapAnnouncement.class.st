Class {
	#name : #MmFailedToMapAnnouncement,
	#superclass : #Announcement,
	#instVars : [
		'reason'
	],
	#category : #'Metamath-Bloc-Announcements'
}

{ #category : #accessing }
MmFailedToMapAnnouncement >> reason [
	^ reason
]

{ #category : #accessing }
MmFailedToMapAnnouncement >> reason: anObject [
	reason := anObject
]
