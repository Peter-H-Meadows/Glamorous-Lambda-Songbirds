"
model tests.

These should run without doin any GUI stuff, so should run in plain pharo (without needing GT)
"
Class {
	#name : #LambdaTests,
	#superclass : #Object,
	#category : #'LambdaCalcModel-Tests'
}

{ #category : #accessing }
LambdaTests >> cardinal [
<gtExample>
"abc.acb"

| cardinal cardinal2 sim1 sim2 cardinalCopy |
cardinal := SongbirdModel new parse: #( \ a b c . a c b ) .

sim1 := cardinal brain payload brain payload brain .

self assert: sim1 class equals: SimModel .

sim2 := sim1 codeSlot payload .

"self assert:  content  equals: 0 ."

self assert: sim1 dataSlot payload eardist equals: 1 .

self assert: sim2 codeSlot payload eardist equals: 2 .

self assert: sim2 dataSlot payload eardist equals: 0 .

cardinalCopy := cardinal pcopy .

self assert: cardinalCopy  equals: cardinal .



cardinal2 := SongbirdModel new parse: #( \ x y z . x z y ) .
"
self assert: cardinal2  equals: cardinal .

self assert: (cardinal hearSong: self thrush ) equals: self idOnceRemoved ."

^ cardinal

]

{ #category : #accessing }
LambdaTests >> idOnceRemoved [
<gtExample>
| idOnceRemoved |
idOnceRemoved := SongbirdModel new parse: #( \ a b . a b ) .
self assert: idOnceRemoved brain payload brain codeSlot payload eardist equals: 1 .

self assert: idOnceRemoved brain payload brain dataSlot payload eardist equals: 0 .
^ idOnceRemoved
]

{ #category : #accessing }
LambdaTests >> idiot [
<gtExample>

| idiot id2 mm |
idiot := SongbirdModel new parse: #( \ A . A ) .

Transcript show: idiot .

"idiot brain eardist = 0 ."
self assert: idiot brain eardist equals: 0 .

id2 := idiot pcopy .

self assert: idiot class equals: SongbirdModel  .

id2 := SongbirdModel new parse: #( \ a . a ) .

self assert: idiot equals:  id2 .

mm := SongbirdModel new parse: #( \ a . a a ) .

self assert: idiot ~= mm .

"self assert: (idiot hearSong: id2) equals:  id2 ."

^ idiot
]

{ #category : #accessing }
LambdaTests >> jay [
<gtExample>

"The Jay was discovered in 1935 by J. Barkley Rosser and has the property that it can be used in association with the Idiot bird to derive all birds except those which ignore or eliminate one or more of their inputs (such as the Kestrel and Kite)."

| jay |
jay := SongbirdModel new parse: #( \ a b c d . a b #( a c b ) ) .

^ jay

]

{ #category : #accessing }
LambdaTests >> kestrel [
<gtExample>

| kestrel kestrel2 kite2 rez idiot kes mockingbir |

idiot := (SongbirdModel new parse: #( \ a . a )) .
kite2 := SongbirdModel new parse: #( \ a b . b ) .

kestrel := SongbirdModel new parse: #( \ a b . a ) .
self assert: kestrel brain payload brain eardist equals: 1 .
self assert: kestrel pcopy equals: kestrel .

kes := SongbirdModel new parse: #( \ a b . a ) .
mockingbir := SongbirdModel new parse: #( \ a . a a ) .

"self assert:  ( kestrel hearSong: mockingbir ) equals: self konstantMockingbird."
"self assert:  (kestrel hearSong: kes  ) equals: self konstantMockingbird."

kestrel2 := kestrel pcopy .

self assert: ( kestrel2 hearSong: self idiot ) equals: self kite.
self assert: ( kestrel2 hearSong: self mockingbird ) equals: self konstantMockingbird.

^ kestrel 

]

{ #category : #accessing }
LambdaTests >> kite [
<gtExample>

| kite kite2 |

kite := SongbirdModel new initFromSymbols: #( a b . b ) .

self assert: kite brain class equals: RetSlotModel .

self assert: kite brain payload brain eardist equals: 0 .

kite2 := SongbirdModel new parse: #( \ a b . b ) .

self assert: kite equals: kite2 .

self assert: kite pcopy equals: kite2  .

self assert: (kite hearSong: self idiot) equals: (SongbirdModel new parse: #( \ b . b ) ) .

^ kite
]

{ #category : #accessing }
LambdaTests >> konstantMockingbird [
<gtExample>

| km |
km := SongbirdModel new parse: #( \ a b . b b ) .

self assert: km brain payload brain codeSlot payload eardist equals: 0 .

self assert: km brain payload brain dataSlot payload eardist equals: 0 .

self assert: (km hearSong: self idiot) equals:  self mockingbird .

^ km 
]

{ #category : #accessing }
LambdaTests >> mockingbird [
<gtExample>

| mockingbird mockingbird2 kite2 mbcp |

mockingbird := SongbirdModel new parse: #( \ a . a a ) .

self assert: mockingbird brain  codeSlot payload eardist equals: 0 .
self assert: mockingbird brain  dataSlot payload eardist equals: 0 .
self assert: mockingbird class equals: SongbirdModel  .

"mockingbird2 := SongbirdModel new parse: #( \ x . x x ) ."

mockingbird2 := mockingbird pcopy .

self assert: mockingbird2 equals: mockingbird .

mbcp := mockingbird pcopy .

self assert: mockingbird equals: mbcp  .

self assert: mockingbird ~= self idiot .




self assert: (mockingbird2 hearSong: self idiot) equals:  self idiot .

kite2 := SongbirdModel new parse: #( \ a b . b ) .

self assert: (mockingbird2 hearSong: self kite) equals: ( SongbirdModel new parse: #( \ b . b  ) ) .

"self assert: (mockingbird hearSong: self kestrel) equals:  (SongbirdModel new parse: #( \ a b . a ) ). ."

^ mockingbird 
]

{ #category : #accessing }
LambdaTests >> robin [
<gtExample>

| robin |
robin := SongbirdModel new parse: #( \ a b c . b c a ) .

^ robin

]

{ #category : #'accessing structure variables' }
LambdaTests >> testModelCreation [
	<gtExample>
	| sb in st mm |
	SongbirdModel initialize.
	"SongbirdModel names do: [ :ea | SongbirdModel newModelOf: ea ]."
	
	st := {'kki'. 'kkx' . 'kM'} readStream .
	
	SongbirdModel names
		do: [ :outter | 
			
			| new |
			
			SongbirdModel names
				do: [ :eaa | 
					in := SongbirdModel newModelOf: eaa.
					sb := SongbirdModel newModelOf: outter.
					Transcript cr.
					Transcript show: in.
					Transcript show: sb.
					
					(sb fullName = 'M'and: [in fullName = 'M']) ifFalse: [
					(sb fullName = 'kx'and: [in fullName = 'M']) ifTrue: [ "self halt" ].
					new := sb hearSong: in.].
					
					Transcript
						show:
							(SongbirdModel all
								detect: [ :eab | eab = new ]
								ifNone: ["self halt." mm :=  SongbirdModel addNewModel: new name: st next.  ]).
					Transcript cr ] ]
]

{ #category : #'accessing structure variables' }
LambdaTests >> testModelCreatioxn [
	<gtExample>
	| sb in st mm new name bb |
	SongbirdModel initialize.
	"SongbirdModel names do: [ :ea | SongbirdModel newModelOf: ea ]."
	st := {'kki' . 'kkx' . 'kM' . } readStream.
	
	bb := SongbirdModel all copy .
	
	SongbirdModel all copy
		do: [ :outter | 
			bb
				do: [ :eaa | 
					in := eaa pcopy.
					sb := outter pcopy.
					new := sb hearSong: in.
					name := SongbirdModel all
						detect: [ :eab | eab = new ]
						ifNone: [ SongbirdModel addNewModel: new name: st next ].
					Transcript
						show: in;
						show: sb;
						show: ' ';
						show: name;
						cr ] ].
	"self halt."
	st := { 'kkki' . 'kkkx' . 'kkM' } readStream.
	
	bb := SongbirdModel all copy .
	
	SongbirdModel all copy
		do: [ :outter | 
			bb
				do: [ :eaa | 
					in := eaa pcopy.
					sb := outter pcopy.
					new := sb hearSong: in.
					name := SongbirdModel all
						detect: [ :eab | eab = new ]
						ifNone: [ self halt . SongbirdModel addNewModel: new name: st next ].
					Transcript
						show: in;
						show: sb;
						show: ' ';
						show: name;
						cr ] ].
]

{ #category : #accessing }
LambdaTests >> thrush [
<gtExample>
| thrush |
thrush := SongbirdModel new parse: #( \ a b . b a ) .
^ thrush
]

{ #category : #accessing }
LambdaTests >> why [
<gtExample>

"#( λf.( λx.f( xx ))( λx.f( x x )) )"

"SongbirdModel new parse: #( \ f . #( \ x . f #( x x ) ) #( \ x . f #( x x ) ) )"

^ SongbirdModel new parse: #( \ a . #( \ b . a #( b b ) ) #( \ b . a #( b b ) ) )
]
