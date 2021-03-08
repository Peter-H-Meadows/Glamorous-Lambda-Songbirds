Class {
	#name : #SimGlob,
	#superclass : #Glob,
	#category : #'LambdaSongBirds-GUI'
}

{ #category : #'event handling' }
SimGlob >> click [

model simplify 

]

{ #category : #abstract }
SimGlob >> initFromModel: m [
	model := m.
	model el: self.
	model announcer when: #hide send: #hide to: self.
	animating := false.
	self border: (BlBorder paint: Color red width: 1).
	self addChild: (SlotGlob new initFromModel: model dataSlot).
	self addChild: (SlotGlob new initFromModel: model codeSlot).
	self
		addEventHandler:
			(BlEventHandler
				on: BlClickEvent
				do: [ :evt | 
					self click.
					evt consumed: true ])
]
