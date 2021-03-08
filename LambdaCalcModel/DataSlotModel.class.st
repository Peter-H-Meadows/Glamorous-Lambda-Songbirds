"
data
"
Class {
	#name : #DataSlotModel,
	#superclass : #VarSlotModel,
	#category : #LambdaCalcModel
}

{ #category : #testing }
DataSlotModel >> isDataSlot [
^ true
]

{ #category : #printing }
DataSlotModel >> printOn: aStream [
aStream nextPutAll: ' DataSlot '.
aStream nextPutAll: depth asString .
aStream nextPutAll: ' : '.
aStream print: payload

	
]
