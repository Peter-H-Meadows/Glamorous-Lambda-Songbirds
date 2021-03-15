"
The set of mandatory variables associated with an assertion is the set
of (zero or more) variables in the assertion and in any active $e statements.
The (possibly empty) set of mandatory hypotheses is the set of all active
$f statements containing mandatory variables, together with all active $e
statements. The set of mandatory $d statements associated with an
assertion are those active $d statements whose variables are both among the
assertion’s mandatory variables.


A proof is scanned in order of its label sequence. If the label refers to an
active hypothesis, the expression in the hypothesis is pushed onto a stack.
If the label refers to an assertion, a (unique) substitution must exist that,
when made to the mandatory hypotheses of the referenced assertion, causes
them to match the topmost (i.e. most recent) entries of the stack, in order
of occurrence of the mandatory hypotheses, with the topmost stack entry
matching the last mandatory hypothesis of the referenced assertion. As many
stack entries as there are mandatory hypotheses are then popped from the
stack. The same substitution is made to the referenced assertion, and the
result is pushed onto the stack. After the last label in the proof is processed,
the stack must have a single entry that matches the expression in the $p
statement containing the proof.
"
Class {
	#name : #MMProof,
	#superclass : #MMAssAndProof,
	#instVars : [
		'assertions',
		'trying',
		'allFhypoths',
		'assertionsUsed'
	],
	#category : #'Metamath-Model'
}

{ #category : #accessing }
MMProof >> addEHypoth: h [
self error .
essentialHypoths add: h.

h setVarSyms 
]

{ #category : #accessing }
MMProof >> addInScope: scope [

essentialHypoths := scope ehypoths . 

scope addProofInScope: self .
"self setupMandatoryFloatingHypothesis ."
]

{ #category : #accessing }
MMProof >> addThing: h [

essentialHypoths add: h .

"h setVarSyms ."
]

{ #category : #'as yet unclassified' }
MMProof >> allFhypoths [
	^ allFhypoths
]

{ #category : #'as yet unclassified' }
MMProof >> assertion [
	^ self
]

{ #category : #accessing }
MMProof >> assertions [

^ assertions
]

{ #category : #accessing }
MMProof >> assertions: x [

assertions := x
]

{ #category : #accessing }
MMProof >> assertionsUsed [
^assertionsUsed
]

{ #category : #accessing }
MMProof >> assertionsUsed: a [


assertionsUsed := a .

"assertionsUsed := MmDatabaseGlob assertions select: [:ea | a includes: ea name ] ."

"assertionsUsed do: [:ea | 
	ao := MmDatabaseGlob assertionNamed: ea ]"
]

{ #category : #accessing }
MMProof >> body [
	^ body
]

{ #category : #accessing }
MMProof >> body: anObject [
	body := anObject
]

{ #category : #accessing }
MMProof >> calcMandFhypoths: fs [

allFhypoths := fs copy .

mandFhypoths := Array new .

self setVarSyms  .

mandFhypoths := allFhypoths select: [ :ea | ea hasVarFrom: vars  ] .
]

{ #category : #accessing }
MMProof >> eHypoths [

^ essentialHypoths
]

{ #category : #accessing }
MMProof >> gameElement [

^ MmProofElement new initializeWithProof: self 

]

{ #category : #accessing }
MMProof >> gtDependenciesMapFor: aView [
	<gtView>
	^ aView mondrian
	title: 'Map';
	priority: 10;
	painting: [ :mondrian | 
		mondrian nodes 
			shape: [ :each |
				| textElement |
				textElement := BlTextElement new.
				textElement text: each name asRopedText.
				textElement.
				
			];
		  with: (self withDeepCollect: #body).
		
		mondrian edges connectToAll: #body .
		
		"mondrian edges 
			shape: [ 
				BlParabollaArcElement new 
					zIndex: 0;
					curvatureFraction: 0.2;
					border: (BlBorder paint: (Color gray alpha: 0.2) width:2 );
					toHead: (BlArrowheadSimpleArrow new
						border: (BlBorder builder paint: (Color gray alpha: 0.2); width:2; build)) ];
			fromRightCenter;
			toLeftCenter;
			connectFrom: #yourself
			toAll: [ :each | |usedPackages | 
				usedPackages := each body]."
		
		mondrian layout tree "custom: (GtGradHorizontalTreeLayout new)".
	]
]

{ #category : #accessing }
MMProof >> gtNestingFor: aView [
	<gtView>
	^ aView pannable 
		title: 'GtNestedTreeMap';
		stencil: [
			| treemap |
			treemap := GtNestedTreeMap new
				roots: {self};
				deep: [ :folder | folder body];
				leaves: [ :folder | { $a } ];
				leavesSize: [ :file | 20 ];
				
				containerEllipse: [ :ellipse :namespace | 
					| label scaledLabel |
					label := BlTextElement new 
						text: (namespace name asRopedText
							foreground: (Color white alpha: 0.7)).
					scaledLabel := label asScalableElement 
						zIndex: 10; 
						constraintsDo: [:c | 
							c horizontal matchParent. 
							c vertical matchParent. 
							c ignoreByLayout.
							c ignored horizontal weight: 0.2.
							c ignored horizontal alignCenter].
					ellipse addChild: scaledLabel.
					"ellipse addChild: bb ."
					ellipse background: (Color gray alpha: 0.2) ].
			treemap asElement
		]
]

{ #category : #accessing }
MMProof >> gtTreeFor: aView [
	<gtView>
	
	^ aView mondrian
		title: 'Tree';
		painting: [ :aMondrian | self paintTreeWith: aMondrian ]
]

{ #category : #accessing }
MMProof >> mandFhypoths [


mandFhypoths := allFhypoths collect: [ :ea | ea hasVarFrom: vars  ] .

^ mandFhypoths
]

{ #category : #accessing }
MMProof >> mands [

^ essentialHypoths reverse , mandFhypoths  
]

{ #category : #gui }
MMProof >> onBoardGameElement [

^ MmOnBoardProofElement new initializeWithProof: self 

]

{ #category : #printing }
MMProof >> printOn: aStream [

aStream nextPutAll: 'proof '.
aStream nextPutAll: name  .
aStream nextPutAll: ' ' .
aStream nextPutAll: rawString  .

"self allVariables do: [ :ea |  aStream nextPutAll: ea printString  . ]"


	
]

{ #category : #'as yet unclassified' }
MMProof >> scopeContent: x [

x do: [ :ea |
	
	ea addTo: self .
	
	 ]
]

{ #category : #accessing }
MMProof >> setAllVarsLevel: n [

self error .

vars do: [ :e | e level: n ]
]

{ #category : #accessing }
MMProof >> setVarSyms [



vars := (body collect: [ :ea | ea getVarSyms ]) flattened .

vars := vars asSet .


essentialHypoths do: [ :ea | vars addAll: ea vars ] .

vars := vars asSet .
]
