Class {
	#name : #MmGtExample,
	#superclass : #Object,
	#category : #'Metamath-GtExamples'
}

{ #category : #example }
MmGtExample >> a1i [
<gtExample>

| a1i |

a1i := (self metamathUniverse proofNamed: 'a1i') copy .

self assert: a1i name equals: 'a1i' .

self assert: a1i mands size equals: 3 .
self assert: a1i essentialHypoths size equals: 1 .

self assert: a1i essentialHypoths first name equals: 'a1i.1' .

self assert: a1i localVariableNames equals: { 'ph' . 'ps' } asSet .

self assert: a1i hypothVariableNames equals: { 'ph' } asSet .

a1i setAllVariablesToFixed .

self assert: a1i localVariables anyOne isFixed equals: true .

self assert: (self metamathUniverse proofNamed: 'a1i') localVariables anyOne isFixed equals: false .

^ a1i

]

{ #category : #example }
MmGtExample >> axMpFirst [
<gtExample>

| axmp |
axmp := (self metamathUniverse assertionNamed: 'ax-mp') copy .

self assert: axmp name equals: 'ax-mp' .

self assert: axmp mands size equals: 4 .
self assert: axmp essentialHypoths size equals: 2 .

self assert: axmp mands first name equals: 'maj' .

self assert: axmp mands second name equals: 'min' .

self assert: axmp localVariableNames equals: { 'ps' } asSet .

self assert: axmp hypothVariableNames equals: { 'ph' . 'ps' } asSet .

^ axmp

]

{ #category : #example }
MmGtExample >> axmpMapToa1i [
<gtExample>

| axmp a1i |
axmp := self axMpFirst .

a1i := self a1i .

self assert: (axmp canMapTo: a1i) equals: true .

self assert: axmp localVariables anyOne isMapped equals: true .

^ axmp
]

{ #category : #example }
MmGtExample >> metamathUniverse [ 
<gtExample>

| parser verse |
parser := self parser .
verse := parser parse: self mmSourceFileSetDotMM .

self assert: verse varNames equals: { 'ph' . 'ps' } asSet .

self assert: verse assertions size equals: 3 .

self assert: verse proofs size equals: 1 .

^ verse

]

{ #category : #example }
MmGtExample >> mmSourceFileSetDotMM [
<gtExample>

^ '
$c ( $.
$c ) $.
$c -> $.
$c -. $.
$c wff $.
$c |- $. 

$v ph $.
$v ps $.
wph $f wff ph $.
wps $f wff ps $.

${
min $e |- ph $.
maj $e |- ( ph -> ps ) $.
ax-mp $a |- ps $.
$}

ax-1 $a |- ( ph -> ( ps -> ph ) ) $.

${
a1i.1 $e |- ph $.
a1i $p |- ( ps -> ph ) $=
( wi ax-1 ax-mp ) ABADCABEF $.
$}'
]

{ #category : #example }
MmGtExample >> parser [ 
<gtExample>
^ MmPP2Parser new .
]

{ #category : #'as yet unclassified' }
MmGtExample >> testStepping [
<gtExample>


| using |
"using := self axMpFirst setupForStepMappingWith: self a1i ."

self assert: using makeStep equals: #inProgress  .

^ using
]
