Class {
	#name : #EarGlob,
	#superclass : #Glob,
	#category : #'LambdaSongBirds-GUI'
}

{ #category : #'as yet unclassified' }
EarGlob >> initFromModel: m [
	model := m.
	model announcer when: SbEarCopyAdded send: #earCopyTo: to: self.
	model announcer when: SbEarInput send: #earInput: to: self.
	model announcer when: #changed send: #changed to: self.
	model announcer when: #hide send: #hide to: self.
	model connects isEmpty
		ifTrue: [ self border: (BlBorder paint: Color veryDarkGray width: 1) ]
		ifFalse: [ self border: (BlBorder paint: model color width: 8) ].

	"textElement := BlTextElement new.
textElement text: (model depth asString asRopedText fontSize: 20;foreground: Color green).
self addChild: textElement ."


	"	self
		addEventHandler:
			(BlEventHandler
				on: BlClickEvent
				do: [ :evt | 
					self click.
					evt consumed: true ])."
	self
		when: BlMouseOverEvent
		do: [ :anEvent | anEvent currentTarget markConnectedSlots ].
	self
		when: BlMouseOutEvent
		do: [ :anEvent | anEvent currentTarget unmarkConnectedSlots ]
]

{ #category : #'as yet unclassified' }
EarGlob >> markConnectedSlots [

	model connects do: [ :ea | ea highlight ]
]

{ #category : #'as yet unclassified' }
EarGlob >> unmarkConnectedSlots [
	model connects do: [ :ea | ea announcer announce: #unhighlight ]
]
