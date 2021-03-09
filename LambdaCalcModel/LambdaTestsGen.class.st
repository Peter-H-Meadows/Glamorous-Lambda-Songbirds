Class {
	#name : #LambdaTestsGen,
	#superclass : #Object,
	#category : #'LambdaCalcModel-Tests'
}

{ #category : #'accessing structure variables' }
LambdaTestsGen >> x [
<gtExample>

| twoLayerBirdsThatHaveTwoApplicators |
twoLayerBirdsThatHaveTwoApplicators := 0 .

self assert: twoLayerBirdsThatHaveTwoApplicators class equals: 16
]
