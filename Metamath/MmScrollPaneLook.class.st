Class {
	#name : #MmScrollPaneLook,
	#superclass : #BrLook,
	#instVars : [
		'scrollable'
	],
	#category : #Metamath
}

{ #category : #initialization }
MmScrollPaneLook >> initialize [
	super initialize.

	scrollable := MmScrollableElement  new.	
	self add: (BrLayoutResizerLook inherit inherit: scrollable).
	self addChangeAddChildAs: #(content scrollable) with: [ scrollable ].

	self
		addChangeProperty: #(widgetContent layout)
		with: [ BlLinearLayout vertical ]
]

{ #category : #initialization }
MmScrollPaneLook >> initializeListeners [
	super initializeListeners.
	
	self when: BrScrollableContentChanged do: [ :anEvent | self onContentChanged: anEvent contentStencil ].
	self when: BrScrollByWish do: [ :anEvent | self onScrollBy: anEvent ].
	self when: BrScrollToItemWish do: [ :anEvent | self onScrollToChild: anEvent ].
]

{ #category : #initialization }
MmScrollPaneLook >> initializeRequests [
	super initializeRequests.
	
	self request: BrScrollableContentRequest new
]

{ #category : #'private - hooks' }
MmScrollPaneLook >> onContentChanged: aContentStencil [
	| aContentElement |
	
	aContentElement := aContentStencil asElement.
	aContentElement removeFromParent.
	
	scrollable scrolledElementDo: [ :aPreviousContent | aPreviousContent removeFromParent ].
	scrollable addChildFirst: aContentElement
]

{ #category : #'private - hooks' }
MmScrollPaneLook >> onScrollBy: aScrollByWish [
	aScrollByWish smooth
		ifTrue: [ scrollable smoothScrollBy: aScrollByWish delta ]
		ifFalse: [ scrollable scrollBy: aScrollByWish delta ]
]

{ #category : #'private - hooks' }
MmScrollPaneLook >> onScrollToChild: aScrollToItemWish [
	
]
