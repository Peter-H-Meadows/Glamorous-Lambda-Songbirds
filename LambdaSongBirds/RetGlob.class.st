Class {
	#name : #RetGlob,
	#superclass : #Glob,
	#instVars : [
		'content'
	],
	#category : #'LambdaSongBirds-GUI'
}

{ #category : #updating }
RetGlob >> changed [  

self border: (BlBorder paint: model color width: 8)
]

{ #category : #'event handling' }
RetGlob >> click [
	SelectedElements isEmpty
		ifTrue: [ SelectedElements add: self.
			^ self ].

	"( SelectedElements includes: self ) ifTrue: [ ^ false ] ."
	
	"ModeBlock := [ :sb1 :sb2 | sb2 swapFor: sb1 ].
	ModeBlock value: SelectedElements anyOne value: self."
	
	self swapFor: SelectedElements anyOne .
	
	SelectedElements := Set new
]

{ #category : #'as yet unclassified' }
RetGlob >> earCopyTo: ann [
	| dummy delta animation |
	content := ann model el.
	self removeChildren.

	"el relocate: self positionInSpace ."
	self space pulse.
	dummy := BlElement new size: content size.
	self addChild: dummy.
	self space pulse.

	"1 seconds asDelay wait."
	delta := dummy positionInSpace - content positionInSpace.
	animation := BlTransformAnimation new.
	animation transform
		translateBy: delta;
		apply.	"inherit"
	animation absolute.
	animation duration: 1 seconds.
	animation delay: 1 seconds.
	animation
		onFinishedDo: [ content transform apply.
			content removeFromParent.
			dummy removeFromParent.
			self addChild: content.
			self space pulse.
			1 seconds asDelay wait.
			content model animating: false ].
	content model animating: true.
	content addAnimation: animation
]

{ #category : #accessing }
RetGlob >> highlight [

self background: Color gray  
]

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

{ #category : #'as yet unclassified' }
RetGlob >> resultOut [
	| bg animation |
	animation := BlTransformAnimation new.
	animation transform
		translateBy: 300 @ 0;
		apply.
	animation duration: 1 seconds.
	animation
		onFinishedDo: [ "pos := content positionInSpace .
	content removeFromParent .
	content relocate: pos .
	content transform  apply.""dummy := BlElement new size: payload size .
	self addChild: dummy ." ].

	"self children last  visibility: BlVisibility hidden ."
	bg := BirdGlob new initFromModel: model payload pcopy.
	bg relocate: self children last positionInSpace.
	self space addChild: bg.
	bg addEventHandler: BlPullHandler new.
	bg addAnimation: animation


	"self children last  addAnimation: animation ."

	"content addAnimation: animation ."
]

{ #category : #'api - graph' }
RetGlob >> swapFor: el [
"tell model"
	model swapFor: el model
]

{ #category : #accessing }
RetGlob >> unhighlight [
self background: BlTransparentBackground new 
]
