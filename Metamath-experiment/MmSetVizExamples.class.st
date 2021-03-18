Class {
	#name : #MmSetVizExamples,
	#superclass : #Object,
	#category : #'Metamath-experiment'
}

{ #category : #accessing }
MmSetVizExamples >> oSymbol [
<gtExample>
^ MmSetVizSymbol new with: 0
]

{ #category : #accessing }
MmSetVizExamples >> oxSet [
<gtExample>
| aSet |
	aSet := self setWithOneO.
	aSet add:  self xSymbol .
	self assert: aSet size = 2 .
	^ aSet
]

{ #category : #accessing }
MmSetVizExamples >> pair00 [
	<gtExample>
	| pair |
	pair := MmPairp x: 0 y: 0.
	^ pair
]

{ #category : #accessing }
MmSetVizExamples >> pair01 [
<gtExample>
| pair |

pair := MmPairp x: 0 y: 1 .
^ pair

]

{ #category : #accessing }
MmSetVizExamples >> pair10 [
<gtExample>
| pair |

pair := MmPairp x: 1 y: 0 .
^ pair

]

{ #category : #accessing }
MmSetVizExamples >> pair11 [
<gtExample>
| pair |

pair := MmPairp x: 1 y: 1 .
^ pair

]

{ #category : #accessing }
MmSetVizExamples >> powerSet [
<gtExample>
| powerSet |
self assert: self oSymbol equals: self oSymbol .
self assert: self setWithOneX equals: self setWithOneX .
self assert: (self setWithOneX = self setWithOneO) equals: false .
(self assert: self setWithOneO powerSet size equals: 1) .
self assert: self setWithOneX powerSet size equals: 1.
self assert: self oxSet equals: self xoSet .
powerSet := self oxSet powerSet .
self assert: powerSet size equals: 3 .
powerSet := powerSet powerSet .
self assert: powerSet size equals: 7 .
^ powerSet





]

{ #category : #accessing }
MmSetVizExamples >> rel [
	<gtExample>
	"efrn2lp 4801	A set founded by epsilon contains no 2-cycle loops. (Contributed by NM, 19-Apr-1994.)
		
	df-eprel 4730*	Define the epsilon relation. Similar to Definition 6.22 of [TakeutiZaring] p. 30. 
		The epsilon relation and set membership are the same, that is,  
		( A  _E  B  <->  A  e.  B ) when  B is a set by epelg 4731. 
		Thus,  5  _E  { 1 ,  5 } (ex-eprel 25919). (Contributed by NM, 13-Aug-1995.)
		
		Non-well-founded set theories are variants of axiomatic set theory that allow sets to be elements of themselves and otherwise violate the rule of well-foundedness. In non-well-founded set theories, the foundation axiom of ZFC is replaced by axioms implying its negation.
		
		
		https://en.wikipedia.org/wiki/Well-founded_relation
		
			
		"
	| ree s1 r10 |
	ree := MmRelationship new.
	self assert: (ree includes: self pair10) equals: false.
	ree add: self pair10.
	self assert: (ree includes: self pair10) equals: true.
	ree add: self pair10.
	self assert: ree size equals: 1.
	self assert: (ree includes: self pair10) equals: true.
	self assert: (ree includes: self pair01) equals: false.
	ree add: self pair01.
	self assert: ree size equals: 2.
	self assert: (ree includes: self pair01) equals: true.
	"self should: [ ree add: 1 ] raise: ZeroDivide ."
	s1 := self setWithOneX.
	self assert: (s1 isWellFoundedByR: ree) equals: true.

	"if r is empty, s must be wellfounded"
	r10 := MmRelationship new.
	r10 add: self pair10.
	self assert: (s1 isWellFoundedByR: r10) equals: false.
	^ ree
]

{ #category : #accessing }
MmSetVizExamples >> setWith3Symbols [
<gtExample>
| aSet powerSet |
	aSet := MmSetVizSet new .
	aSet add: self oSymbol.
	aSet add: self xSymbol.
	aSet add: self ySymbol.
	self assert: aSet size equals: 3 .
	powerSet := aSet powerSet .
	self assert: powerSet size equals: 7 .
	^ powerSet
]

{ #category : #accessing }
MmSetVizExamples >> setWithOneO [
<gtExample>
| aSet |
	aSet := MmSetVizSet new .
	aSet add: self oSymbol.
	self assert: aSet size equals: 1 .
	^ aSet
]

{ #category : #accessing }
MmSetVizExamples >> setWithOneX [
<gtExample>
| aSet |
	aSet := MmSetVizSet new .
	self assert: aSet isEmpty .
	aSet add: self xSymbol.
	self assert: aSet size equals: 1 .
	^ aSet
]

{ #category : #accessing }
MmSetVizExamples >> setWithOneY [
<gtExample>
| aSet |
	aSet := MmSetVizSet new .
	aSet add: self ySymbol.
	self assert: aSet size equals: 1 .
	^ aSet
]

{ #category : #accessing }
MmSetVizExamples >> setWithSetWithOneX [
<gtExample>
| aSet |
	aSet := MmSetVizSet new .
	aSet add: self setWithOneX .
	self assert: aSet size equals: 1 .
	^ aSet
]

{ #category : #accessing }
MmSetVizExamples >> testeq [
<gtExample>
self assert: self oSymbol equals: self oSymbol .
self assert: self setWithOneX equals: self setWithOneX .
self assert: (self setWithOneX = self setWithOneO) equals: false .

self assert: self oxSet equals: self xoSet .

]

{ #category : #accessing }
MmSetVizExamples >> xSymbol [
<gtExample>
^ MmSetVizSymbol new with: 1
]

{ #category : #accessing }
MmSetVizExamples >> xoSet [
<gtExample>
| aSet |
	aSet := self setWithOneX. .
	aSet add:  self oSymbol .
	self assert: aSet size = 2 .
	^ aSet
]

{ #category : #accessing }
MmSetVizExamples >> ySymbol [
<gtExample>
^ MmSetVizSymbol new with: 2
]
