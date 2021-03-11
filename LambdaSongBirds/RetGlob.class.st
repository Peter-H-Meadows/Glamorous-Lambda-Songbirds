Class {
	#name : #RetGlob,
	#superclass : #Glob,
	#instVars : [
		'content'
	],
	#category : #'LambdaSongBirds-GUI'
}

{ #category : #accessing }
RetGlob >> initFromModel: m [
	model := m.
	model announcer when: SbEarCopyAdded send: #earCopyTo: to: self.
	model announcer when: #resultOut send: #resultOut to: self.
	model announcer when: #hide send: #hide to: self.
	model announcer when: #changed send: #changed to: self.
	model announcer when: #highlight send: #highlight to: self.
	model announcer when: #unhighlight send: #unhighlight to: self.
	self geometry: BlEllipseGeometry new.
	model isConnected
		ifTrue: [ self border: (BlBorder paint: model color width: 8) ]
		ifFalse: [ self border: (BlBorder paint: Color veryDarkGray width: 1) ].

	"textElement := BlTextElement new.
textElement text: (model depth asString asRopedText fontSize: 20; foreground: Color green).
self addChild: textElement ."
	model payload ifNil: [ ^ self ].
	self
		addChild: (model payload elementClass new initFromModel: model payload)
]
