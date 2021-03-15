Class {
	#name : #MmVarModel,
	#superclass : #MmAbstractModel,
	#instVars : [
		'real'
	],
	#category : #'Metamath-Model'
}

{ #category : #testing }
MmVarModel >> canMapTo: stuff [

"if I'm free, easy, map to stuff and return true.

if I'm mapped, return mappedTo canMapTo: stuff .

if I'm fixed, return stuff canMapToFixedVariable: stuff."

^ real canMapTo: stuff .
]

{ #category : #testing }
MmVarModel >> canMapToFixed: stuff [

"if I'm free, easy, map to stuff and return true.

if I'm mapped, return mappedTo canMapTo: stuff .

if I'm fixed, return stuff canMapToFixedVariable: stuff."

^ real canMapToFixed: stuff .
]

{ #category : #testing }
MmVarModel >> gameElement [ 

^ real gameElement
]

{ #category : #accessing }
MmVarModel >> isVar [ 
^ true
]

{ #category : #testing }
MmVarModel >> name: x [
name := x
]

{ #category : #testing }
MmVarModel >> vars: v [

real := v at: name .

]
