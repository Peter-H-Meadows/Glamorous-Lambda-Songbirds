Class {
	#name : #SimGlob,
	#superclass : #Glob,
	#instVars : [
		'animating'
	],
	#category : #'LambdaSongBirds-GUI'
}

{ #category : #accessing }
SimGlob >> animating [
^ animating
]

{ #category : #accessing }
SimGlob >> animating: x [
animating := x
]

{ #category : #'event handling' }
SimGlob >> click [

model simplify 

]

{ #category : #'as yet unclassified' }
SimGlob >> initFromModel: m [
	model := m.
	model el: self.
	
	model announcer when: #hide send: #hide to: self.

	animating := false.
	
	self border: (BlBorder paint: Color red width: 1).
	dataSlot := SlotGlob new initFromModel: model dataSlot.
	self addChild: dataSlot.
	codeSlot := SlotGlob new initFromModel: model codeSlot.
	self addChild: codeSlot.
	
	self
		addEventHandler:
			(BlEventHandler
				on: BlClickEvent
				do: [ :evt | 
					self click.
					evt consumed: true ])
]
