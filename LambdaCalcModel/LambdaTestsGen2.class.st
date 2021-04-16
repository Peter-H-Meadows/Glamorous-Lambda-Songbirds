Class {
	#name : #LambdaTestsGen2,
	#superclass : #Object,
	#category : #'LambdaCalcModel-Tests'
}

{ #category : #examples }
LambdaTestsGen2 >> c [
"The Cardinal might have been called the crossing bird because it always responds with the crossed cousin of whatever bird it hears. For example if it hears the Warbler song it will respond with the Crossed Warbler and vice versa. Its response to the Thrush song is the Idiot bird once removed, and vice versa. The word converse is often used instead of crossed in this context. If it hears a song which has more than two layers the Cardinal will cross the connections from the two outermost layers only. The Cardinal has the effect of altering the rhyme of whatever bird it is applied to, but it will never alter the rhythm."
<gtExample>
| c t l z warb warbc |
c := SongbirdModel newModelOf: 'C'.
t := SongbirdModel newModelOf: 'T'.
"l := SongbirdModel newModelOf: 'lark'."

z := SongbirdModel new initFromSymbols: #( A B . A B ).

"warb := SongbirdModel new initFromSymbols: #( A B . #( A B ) B ).
warbc := SongbirdModel new initFromSymbols: #( A B . B #( A A ) )."


self assert: ( c hearSong: t ) equals: z .

^ c hearSong: t
]

{ #category : #'accessing structure variables' }
LambdaTestsGen2 >> x [
	<gtExample>

	"SongbirdModel initialize.
	 SongbirdModel all ."
	
	| xx |
	xx := Bag new .
	#(A B C) permutationsDo: [:ea | 
	
	xx add:
	  (SongbirdModel new initFromSymbols: ea , #(  . ) , ea) .
	
	].
	
	^xx
	
	
"gen all 1 applicator songs.
aa
ab
ba
bb
"
]
