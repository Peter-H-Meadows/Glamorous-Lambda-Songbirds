Class {
	#name : #EarGlob,
	#superclass : #Glob,
	#category : #'LambdaSongBirds-GUI'
}

{ #category : #updating }
EarGlob >> changed [  

self border: (BlBorder paint: model color width: 8)
]

{ #category : #'event handling' }
EarGlob >> click [ 

model simp
]

{ #category : #'as yet unclassified' }
EarGlob >> earCopyTo: ann [ 

| el  |

el := ann model elementClass new initFromModel: ann model .

ann model animating: true .

ann model el: el .

el relocate: self children first positionInSpace .

self children first visibility: BlVisibility hidden .

self space addChild: el .


]

{ #category : #utils }
EarGlob >> earInput: ann [ 

| el  song dummy delta animation |

self removeChildren .

"self children size > 1 ifTrue: [ self  halt ]."

el := "BirdGlob" ann model elementClass  new initFromModel: ann model "copy" .

"song := ann model el ."

el relocate: ann model el positionInSpace .

song := el .

song model el: song .

self space addChild: song .

self space pulse .

dummy := BlElement new size: song size.
self addChild: dummy .

self space pulse .

"1 seconds asDelay wait."

delta := dummy "self" positionInSpace - song positionInSpace.
								
animation := BlTransformAnimation new.			
animation transform "inherit" translateBy: delta ; apply.
animation absolute.

animation duration: 1 seconds.

animation delay: 1 seconds.

animation  onFinishedDo: [

	song transform  apply.
	
	song removeFromParent .
	dummy removeFromParent .
	self addChild: song .
	
	self space pulse .
	
	1 seconds asDelay wait.

	song model animating: false .
	
].

song model animating: true .

song addAnimation: animation .


"ann model animating: true .

ann model el: el .

el relocate: self positionInSpace + (40@40)."


]

{ #category : #'as yet unclassified' }
EarGlob >> earInputx: ann [ 

| el  song dummy delta animation |

"el := BirdGlob new initFromModel: ann model ."

song := ann model el .

"el relocate: self positionInSpace ."

self space pulse .

dummy := BlElement new size: song size.
self addChild: dummy .

self space pulse .

"1 seconds asDelay wait."

delta := dummy "self" positionInSpace - song positionInSpace.
								
animation := BlTransformAnimation new.			
animation transform "inherit" translateBy: delta ; apply.
animation absolute.

animation duration: 3 seconds.

animation delay: 1 seconds.

animation  onFinishedDo: [

	song transform  apply.
	
	song removeFromParent .
	dummy removeFromParent .
	self addChild: song .
	
	self space pulse .
	
	2 seconds asDelay wait.

	song model animating: false .
	
].

song model animating: true .

song addAnimation: animation .


"ann model animating: true .

ann model el: el .

el relocate: self positionInSpace + (40@40)."


]

{ #category : #accessing }
EarGlob >> hide [ 

self visibility: BlVisibility hidden .

"self border: (BlBorder paint: Color random width: 0) ."
]

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

{ #category : #'api - running' }
EarGlob >> markConnectedSlots [
	model connects do: [ :ea | ea highlight ]
]

{ #category : #'api - running' }
EarGlob >> unmarkConnectedSlots [
	model connects do: [ :ea | ea announcer announce: #unhighlight ]
]
