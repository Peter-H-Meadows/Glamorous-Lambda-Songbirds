Class {
	#name : #BrPagerPageElementMM,
	#superclass : #BlElement,
	#instVars : [
		'weight',
		'aWidthSpec',
		'aHeightSpec'
	],
	#category : #Metamath
}

{ #category : #initialization }
BrPagerPageElementMM >> initialize [
self error.
	super initialize.
	
	self viewModel: BrPagerPageModel new.
	self beInSeparateCompositionLayer.
	"weight := 0.5."
	
	self constraintsDo: [ :c |
		c horizontal matchParent.
		c vertical matchParent ].
	
aWidthSpec := BlMeasurementSpec exact: 1 "(66 * 5 atRandom)" .
aHeightSpec := BlMeasurementSpec exact: 1 "(66 * 7 atRandom)".
]

{ #category : #layout }
BrPagerPageElementMM >> mm: x [

self addChild: x elementForStartingList .
self children first forceLayout .
aWidthSpec := BlMeasurementSpec exact: self children first width .
aHeightSpec := BlMeasurementSpec exact: self children first height .
]

{ #category : #layout }
BrPagerPageElementMM >> mm: x controller: c [
| el aEventListener |
aEventListener := MmListUsableEventListener new gameController: c  .
			el := x elementForStartingList addEventHandler: aEventListener .
self addChild: el .
el forceLayout .
aWidthSpec := BlMeasurementSpec exact: self children first width .
aHeightSpec := BlMeasurementSpec exact: self children first height .
]

{ #category : #layout }
BrPagerPageElementMM >> onMeasure: anExtentMeasurementSpec [
	"| aWidthSpec aHeightSpec |
	
	aWidthSpec := anExtentMeasurementSpec widthSpec.
	aHeightSpec := anExtentMeasurementSpec heightSpec.
	
	self constraints horizontal resizer isMatchParent
		ifTrue: [ aWidthSpec := BlMeasurementSpec exact: (66 * 4 atRandom) ].
		
aHeightSpec := BlMeasurementSpec exact: (66 * 4 atRandom)."

	super onMeasure: aWidthSpec @ aHeightSpec.
]
