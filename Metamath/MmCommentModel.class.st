Class {
	#name : #MmCommentModel,
	#superclass : #MmAbstractModel,
	#category : #'Metamath-Model'
}

{ #category : #accessing }
MmCommentModel >> addInScope: scope [ 

scope addComment: self


]

{ #category : #accessing }
MmCommentModel >> addTo: x [
]

{ #category : #accessing }
MmCommentModel >> eel [

	| anAccordion |
	anAccordion := BrAccordion new.
	anAccordion hMatchParent; vFitContent.

	anAccordion look: BrGlamorousAccordionLook new.
	anAccordion header: [
		BrButton new
			look: BrGlamorousAccordionHeaderLook new;
			label: body;
			action: [ anAccordion toggle ] ].
	anAccordion content: [
		BrEditor new
			look: BrGlamorousEditorLook new;
			text: body  ].

	^ anAccordion

]

{ #category : #accessing }
MmCommentModel >> gameElement [ 

^ MmCommentElement new createFromString: body
]

{ #category : #testing }
MmCommentModel >> isComment [
^ true
]

{ #category : #accessing }
MmCommentModel >> name [
	^ name
]

{ #category : #accessing }
MmCommentModel >> name: anObject [
	name := anObject
]

{ #category : #accessing }
MmCommentModel >> variables [ 

^ {  }
]
