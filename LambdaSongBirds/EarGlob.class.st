Class {
	#name : #EarGlob,
	#superclass : #Glob,
	#category : #'LambdaSongBirds-GUI'
}

{ #category : #'event handling' }
EarGlob >> click [
	SelectedElements isEmpty
		ifTrue: [ SelectedElements add: self.
			^ self ].
	ModeBlock value: SelectedElements anyOne value: self.
	SelectedElements := Set new
]

{ #category : #'api - graph' }
EarGlob >> connectTo: x [
]

{ #category : #'as yet unclassified' }
EarGlob >> earCopyTo: ann [
	| el |
	el := ann model elementClass new initFromModel: ann model.
	ann model animating: true.
	ann model el: el.
	el relocate: self children first positionInSpace.
	self children first visibility: BlVisibility hidden.
	self space addChild: el
]

{ #category : #'as yet unclassified' }
EarGlob >> earInput: ann [
	| el song dummy delta animation |
	self removeChildren.
	el := ann model elementClass new initFromModel: ann model.
	el relocate: ann model el positionInSpace.
	song := el.
	song model el: song.
	self space addChild: song.
	self space pulse.
	dummy := BlElement new size: song size.
	self addChild: dummy.
	self space pulse.

	"1 seconds asDelay wait."
	delta := dummy positionInSpace - song positionInSpace.
	animation := BlTransformAnimation new.
	animation transform
		translateBy: delta;
		apply.	
	animation absolute.
	animation duration: 1 seconds.
	animation delay: 1 seconds.
	animation
		onFinishedDo: [ song transform apply.
			song removeFromParent.
			dummy removeFromParent.
			self addChild: song.
			self space pulse.
			1 seconds asDelay wait.
			song model animating: false ].
	song model animating: true.
	song addAnimation: animation
]

{ #category : #'as yet unclassified' }
EarGlob >> initFromModel: m [
	model := m.
	model announcer when: SbEarCopyAdded send: #earCopyTo: to: self.
	model announcer when: SbEarInput send: #earInput: to: self.
	"model announcer when: #changed send: #changed to: self.
	model announcer when: #hide send: #hide to: self."
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
