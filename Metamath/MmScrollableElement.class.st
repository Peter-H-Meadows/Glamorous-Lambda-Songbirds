Class {
	#name : #MmScrollableElement,
	#superclass : #BlScrollableElement,
	#category : #'Metamath-scroll'
}

{ #category : #'api - scrolling thumb' }
MmScrollableElement >> computeHorizontalScrollExtent [
^ self width
]

{ #category : #'api - scrolling thumb' }
MmScrollableElement >> computeHorizontalScrollOffset [ 

^ scrollPosition x negated
]

{ #category : #'api - scrolling thumb' }
MmScrollableElement >> computeHorizontalScrollRange [

^ self scrolledElement width
]

{ #category : #initialization }
MmScrollableElement >> initialize [ 

super initialize .
self addEventHandler: MmScrollHandler new .
self constraintsDo: [ :c |
					c horizontal matchParent.
					c vertical matchParent  ]
]
