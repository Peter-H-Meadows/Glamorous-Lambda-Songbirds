"
In mathematics (specifically set theory), a binary relation over sets X and Y is a subset of the Cartesian product X × Y; 
that is, it is a set of ordered pairs (x, y) consisting of elements x in X and y in Y.

It encodes the common concept of relation: an element x is related to an element y, 
if and only if the pair (x, y) belongs to the set of ordered pairs that defines the binary relation. 

A binary relation is the most studied special case n = 2 of an n-ary relation over sets X1, ..., Xn, which is a subset of the Cartesian product X1 × ... × Xn.



An example of a binary relation is the ""divides"" relation over the set of prime numbers 
{\displaystyle \mathbb {P} }\mathbb {P}  and the set of integers {\displaystyle \mathbb {Z} }\mathbb {Z} , 
in which each prime p is related to each integer z that is a multiple of p, but not to an integer that is not a multiple of p. 
In this relation, for instance, the prime number 2 is related to numbers such as −4, 0, 6, 10, but not to 1 or 9, just as the prime number 3 is related to 0, 6, and 9, but not to 4 or 13.
"
Class {
	#name : #MmRelationship,
	#superclass : #MmSetVizSet,
	#type : #variable,
	#category : #'Metamath-experiment'
}

{ #category : #adding }
MmRelationship >> add: x [
self assert: x class  equals: MmPairp .
super add: x . 

]
