Class {
	#name : #MmGameEventListener,
	#superclass : #BlEventListener,
	#instVars : [
		'model'
	],
	#category : #'Metamath-Bloc'
}

{ #category : #accessing }
MmGameEventListener >> clickEvent: anEvent [

self error .

"model makeStep"

anEvent currentTarget lay .

"self inform: 'board clicked'"
]

{ #category : #accessing }
MmGameEventListener >> model: m [

model := m
]

{ #category : #accessing }
MmGameEventListener >> mouseEnterEvent: anEvent [

"anEvent target border: (BlBorder paint: (Color gray alpha: 0.8) width: 4)."
]

{ #category : #accessing }
MmGameEventListener >> mouseLeaveEvent: anEvent [

"anEvent target border: (BlBorder paint: (Color gray alpha: 0.4) width: 1)."
]
