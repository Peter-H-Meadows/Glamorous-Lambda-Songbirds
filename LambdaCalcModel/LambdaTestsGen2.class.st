Class {
	#name : #LambdaTestsGen2,
	#superclass : #Object,
	#category : #'LambdaCalcModel-Tests'
}

{ #category : #'accessing structure variables' }
LambdaTestsGen2 >> x [
	<gtExample>

	"SongbirdModel initialize.
	 SongbirdModel all ."
	
	#(A B C) permutationsDo: [:ea | 
	
	
	  SongbirdModel new initFromSymbols: ea , #(  . ) , ea .
	
	].
	
	
"gen all 1 applicator songs.
aa
ab
ba
bb
"
]
