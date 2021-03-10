Class {
	#name : #LambdaTestsGen,
	#superclass : #Object,
	#category : #'LambdaCalcModel-Tests'
}

{ #category : #'accessing structure variables' }
LambdaTestsGen >> x [
	<gtExample>
	| twoLayerBirdsThatHaveTwoApplicators |
	"You may have noticed that a rhythm section corresponds to a binary tree. 
The number of rhythms using a applicators is the a-th Catalan number which can be found by 
taking the number of rhythms using a-1 applicators and multiplying by (4a-2)/(a + 1). 

Of course there is only one rhythm with zero applicators. 
The series starts, 1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, ... ."
	twoLayerBirdsThatHaveTwoApplicators := 0.
	self assert: twoLayerBirdsThatHaveTwoApplicators equals: 16
]
