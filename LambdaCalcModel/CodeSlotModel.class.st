"
code
"
Class {
	#name : #CodeSlotModel,
	#superclass : #VarSlotModel,
	#category : #LambdaCalcModel
}

{ #category : #testing }
CodeSlotModel >> isCodeSlot [
^ true
]

{ #category : #printing }
CodeSlotModel >> printOn: aStream [
"aStream nextPutAll: ' Code: '."
"aStream nextPutAll: depth asString.
aStream nextPutAll: ' : '."

aStream print: payload 

	
]
