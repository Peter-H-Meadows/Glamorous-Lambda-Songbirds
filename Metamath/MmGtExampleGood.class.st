Class {
	#name : #MmGtExampleGood,
	#superclass : #Object,
	#category : #'Metamath-GtExamples'
}

{ #category : #basic }
MmGtExampleGood >> metamath1 [
<gtExample>

| scope axmp axmp2 axmpc |

scope := self metamathUniverse .

axmp := (scope allAssertions at: 'ax-mp') copy .

axmp2 := (scope allAssertions at: 'ax-mp') copy .

axmp canMapTo: axmp2 essentialHypoths first .

"axmpc := axmp copy ."

^ axmp

]

{ #category : #basic }
MmGtExampleGood >> metamathUniverse [ 
<gtExample>

| parser verse scope |
parser := self parser .
scope := parser parse: MmRawFileDataPartOne comment "self mmSourceFileSetDotMM1" .
scope first parse .
"self assert: verse varNames equals: { 'ph' . 'ps' } asSet .

self assert: verse assertions size equals: 3 .

self assert: verse proofs size equals: 1 ."

^ scope first

]

{ #category : #'as yet unclassified' }
MmGtExampleGood >> mmSourceFileSetDotMM1 [
<gtExample>

^ '
 ${ 
 $( boo
 $) $v varvar $. $c constconst $. ${ $} $}

 '
]

{ #category : #basic }
MmGtExampleGood >> parser [ 
<gtExample>
^ MmPP2ParserFirst new .
]
