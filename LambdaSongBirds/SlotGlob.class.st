Class {
	#name : 'SlotGlob',
	#superclass : 'Glob',
	#category : 'LambdaSongBirds-GUI'
}

{ #category : 'updating' }
SlotGlob >> changed [  

self border: (BlBorder paint: model color width: 8)
]

{ #category : 'event handling' }
SlotGlob >> click [ 

"self space enqueueTask: animation" 
]

{ #category : 'accessing' }
SlotGlob >> hide [ 

"self  visibility: BlVisibility hidden ."

self border: (BlBorder paint: Color random "model color" width: 0) .

"self childrenDo: [ :ea | ea hide ]."

"self parent hide ."
]

{ #category : 'as yet unclassified' }
SlotGlob >> initFromModel: m [
	model := m.
	model announcer when: #hide send: #hide to: self.
	model payload ifNil: [ ^ self ].
	self
		addChild: (model payload elementClass new initFromModel: model payload)
]

{ #category : 'initialization' }
SlotGlob >> initialize [
	super initialize.
	self geometry: BlEllipseGeometry new.
	self border: (BlBorder paint: Color gray width: 0)
]
