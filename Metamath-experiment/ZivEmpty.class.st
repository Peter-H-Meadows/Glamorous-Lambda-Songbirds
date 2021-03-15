Class {
	#name : #ZivEmpty,
	#superclass : #Object,
	#instVars : [
		'prev'
	],
	#classVars : [
		'Mon'
	],
	#category : #'Metamath-experiment'
}

{ #category : #accessing }
ZivEmpty >> el [
^ BlElement new 
				border: (BlBorder paint: Color black);
				geometry: BlEllipse new; 
				size: 6@8.
]

{ #category : #accessing }
ZivEmpty >> env [
^ Ziv new
]

{ #category : #accessing }
ZivEmpty >> go [

]

{ #category : #accessing }
ZivEmpty >> mon: m [
Mon := m
]
