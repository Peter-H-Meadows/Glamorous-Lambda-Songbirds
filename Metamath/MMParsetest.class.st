Class {
	#name : #MMParsetest,
	#superclass : #TestCase,
	#instVars : [
		'browser',
		'parser',
		'mmdbstr'
	],
	#category : #'Metamath-Tests'
}

{ #category : #running }
MMParsetest >> setUp [ 

parser := MmPP2Parser new .

]

{ #category : #tests }
MMParsetest >> test1 [

| verse |

verse := parser parse: '
$(m$) $( $) $(  m $)
$(  x $)
$c ( $.  $( Left parenthesis $)
  $c ) $.  $( Right parenthesis $)
  $c -> $. $( Right arrow (read:  implies) $)
  $c -. $. $( Right handle (read:  not) $)
  $c wff $. $( Well-formed formula symbol (read:  the following symbol
               sequence is a wff) $)
  $c |- $. 


  $c & $. $( Ampersand (read: and-also) $)
  $c => $. $( Big-to (read: proves) $)

  $( wff variable sequence:  ph ps ch th ta et ze si rh mu la ka $)
  $( Introduce some variable names we will use to represent well-formed
     formulas (wffs). $)

  $v ph $.  $( Greek phi $)
  $v ps $.  $( Greek psi $)

 wph $f wff ph $.
  wps $f wff ps $.


  ${
    $( Minor premise for modus ponens. $)
    min $e |- ph $.
    $( Major premise for modus ponens. $)
    maj $e |- ( ph -> ps ) $.

    ax-mp $a |- ps $.
  $}' .

self assert: verse assertions size equals: 1 .

self assert: verse assertions first name equals: 'ax-mp' .

self assert: verse assertions first mands size equals: 2 .

self assert: verse assertions first mands first name equals: 'maj' .

self assert: verse assertions first mands second name equals: 'min' .

]

{ #category : #tests }
MMParsetest >> testProveA1i [

| verse a1iProof |

verse := parser parse: '
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
$}

'.

self assert: verse assertions size equals: 3 . "axioms and proofs"

self assert: verse assertions first name equals: 'ax-mp' .

self assert: verse assertions first mands size equals: 2 .

self assert: verse assertions first mands first name equals: 'maj' .

self assert: verse assertions first mands second name equals: 'min' .

self assert: verse assertions last name equals: 'a1i' .

a1iProof := verse assertions last .

self assert: a1iProof mands size equals: 1 .

"self assert: a1iProof findProofOneStep equals: false .

self assert: a1iProof rootTryingSlot tryingThings size equals: 1 . "

"first step can only use ax-mp"



]
