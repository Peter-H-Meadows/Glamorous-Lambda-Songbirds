Class {
	#name : #MmScopeElement2,
	#superclass : #BrAccordion,
	#instVars : [
		'model'
	],
	#category : #'Metamath-Bloc'
}

{ #category : #accessing }
MmScopeElement2 >> with: aScopeModel [
| aList |

model := aScopeModel . 
	
self  hMatchParent; vFitContent.

self look: BrGlamorousAccordionLook new.

self header: [
		BrButton new
			look: BrGlamorousAccordionHeaderLook new;
			label: model title;
			action: [ self toggle ] ].
			
	self content: [
	
		"BrEditor new
			look: BrGlamorousEditorLook new;
			text: (String loremIpsum: 200) trimBoth "
			
		aList := BrSimpleList new.

			aList stencil: [ :ea :index |

				"anAccordion :=" "MmScopeElement2 new with: ea ."
				ea eel.
	
			].
		
		aList items: model stuff  .
		
		aList
		
			
			
	].
	
"self toggle ."
]
