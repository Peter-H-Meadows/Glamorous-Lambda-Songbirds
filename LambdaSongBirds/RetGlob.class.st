Class {
	#name : #RetGlob,
	#superclass : #Glob,
	#instVars : [
		'slot',
		'animation',
		'content'
	],
	#category : #'LambdaSongBirds-GUI'
}

{ #category : #updating }
RetGlob >> changed [  

self border: (BlBorder paint: model color width: 8)
]

{ #category : #'as yet unclassified' }
RetGlob >> earCopyTo: ann [
| dummy delta  |

content := ann model el .

self removeChildren .

"el relocate: self positionInSpace ."

self space pulse .

dummy := BlElement new size: content size.
self addChild: dummy .


self space pulse .

"1 seconds asDelay wait."

delta := dummy "self" positionInSpace - content positionInSpace.
								
animation := BlTransformAnimation new.			
animation transform "inherit" translateBy: delta ; apply.
animation absolute.

animation duration: 1 seconds.

animation delay: 1 seconds.

animation  onFinishedDo: [

	content transform  apply.
	
	content removeFromParent .
	dummy removeFromParent .
	self addChild: content .
	
	self space pulse .
	
	1 seconds asDelay wait.

	content model animating: false .
	
].

content model animating: true .

content addAnimation: animation

]

{ #category : #accessing }
RetGlob >> highlight [

self background: Color gray  
]

{ #category : #accessing }
RetGlob >> initFromModel: m [
| textElement |
model := m .
model announcer when: SbEarCopyAdded send: #earCopyTo: to: self.
model announcer when: #resultOut send: #resultOut to: self.
model announcer when: #hide send: #hide to: self.
model announcer when: #changed  send: #changed to: self.

model announcer when: #highlight  send: #highlight to: self.
model announcer when: #unhighlight send: #unhighlight to: self.

self geometry: BlEllipseGeometry new .

self border: (BlBorder paint: model color width: 8) .

"textElement := BlTextElement new.
textElement text: (model depth asString asRopedText fontSize: 20; foreground: Color green).
self addChild: textElement ."

model content ifNil: [ ^ self ].
self addChild: (model content elementClass new initFromModel: model content) .

]

{ #category : #'as yet unclassified' }
RetGlob >> resultOut [

| bg |
animation := BlTransformAnimation new.			
animation transform "inherit"  translateBy: 300@0 ; apply.
"animation absolute."
animation duration: 1 seconds.

animation  onFinishedDo: [

	"pos := content positionInSpace .
	content removeFromParent .
	content relocate: pos .
	content transform  apply."
	
	"dummy := BlElement new size: content size .
	self addChild: dummy ."
	
].

"self children last  visibility: BlVisibility hidden ."

"Earz := OrderedCollection new ."

bg := BirdGlob new initFromModel: model content pcopy .
bg  relocate: self children last positionInSpace .
self space addChild: bg .

bg addEventHandler: BlPullHandler new.

bg  addAnimation: animation .


"self children last  addAnimation: animation ."

"content addAnimation: animation ."

]

{ #category : #accessing }
RetGlob >> unhighlight [
self background: BlTransparentBackground new 
]
