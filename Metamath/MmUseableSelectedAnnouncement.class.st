Class {
	#name : #MmUseableSelectedAnnouncement,
	#superclass : #Announcement,
	#instVars : [
		'element',
		'model'
	],
	#category : #'Metamath-Bloc-Announcements'
}

{ #category : #accessing }
MmUseableSelectedAnnouncement >> element [
^ element
]

{ #category : #accessing }
MmUseableSelectedAnnouncement >> element: e [
element := e
]

{ #category : #accessing }
MmUseableSelectedAnnouncement >> model [
^ model
]

{ #category : #accessing }
MmUseableSelectedAnnouncement >> model: m [
model := m
]
