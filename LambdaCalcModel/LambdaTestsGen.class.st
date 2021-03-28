Class {
	#name : #LambdaTestsGen,
	#superclass : #Object,
	#category : #'LambdaCalcModel-Tests'
}

{ #category : #'accessing structure variables' }
LambdaTestsGen >> x [
	<gtExample>
	| numberOfTwoLayerBirdsThatHaveTwoApplicators |
	"You may have noticed that a rhythm section corresponds to a binary tree. 
The number of rhythms using a applicators is the a-th Catalan number which can be found by 
taking the number of rhythms using a-1 applicators and multiplying by (4a-2)/(a + 1). 

Of course there is only one rhythm with zero applicators. 
The series starts, 1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, ... ."
	numberOfTwoLayerBirdsThatHaveTwoApplicators := 0.
	self assert: numberOfTwoLayerBirdsThatHaveTwoApplicators equals: 16
]

{ #category : #accessing }
LambdaTestsGen >> xxx [
	<gtExample>
	| view |
	view := GtMondrian new.
	view nodes
		shape: [ :x | 
			BlElement new 
				border: (BlBorder paint: Color black);
				geometry: BlEllipseGeometry new; 
				size: (x * 2) @ (x * 2) ];
		with: (1 to: 9).
	self assert: view topStep root graph nodeChildren size = 9.
	^ view
]

{ #category : #accessing }
LambdaTestsGen >> xxxx [
	<gtExample>
	| sb in st mm view xx |
	SongbirdModel initialize.
	st := {'kki' . 'kkx'} readStream.
	xx := OrderedCollection new.
	SongbirdModel names
		do: [ :ea | 
			| new |
			sb := SongbirdModel newModelOf: ea.
			SongbirdModel names
				do: [ :inputName | 
					in := SongbirdModel newModelOf: inputName.



					"sb := sb pcopy."

					"(sb fullName = 'kx'and: [in fullName = 'M']) ifTrue: [ self halt ]."
					(sb fullName = 'M' and: [ in fullName = 'M' ])
						ifFalse: [ new := sb hearSong: in ].
					(sb fullName = 'kx' and: [ in fullName = 'ki' ])
						ifTrue: [ "self halt" ].
					mm := SongbirdModel all
						detect: [ :eab | eab = new ]
						ifNone: [ "self halt." SongbirdModel addNewModel: new name: st next ].
					xx add: mm ] ].
			
	view := GtMondrian new.
	view nodes
		shape: [ :x | BirdGlob new initFromModel: x ];
		with: xx.	
			view edges
		fromCenterBottom;
		toCenterTop;
		connectFrom: [ :ea | in ] to: [ sb ] .
	"self assert: view topStep root graph nodeChildren size = 9."
	^ view
]
