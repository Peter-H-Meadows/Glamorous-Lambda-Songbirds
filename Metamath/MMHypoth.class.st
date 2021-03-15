Class {
	#name : #MMHypoth,
	#superclass : #MMAbstractThing,
	#category : #'Metamath-Model'
}

{ #category : #accessing }
MMHypoth >> allVariables [ 

^ self localVariables
]

{ #category : #accessing }
MMHypoth >> eHypoths [

^ {  }
]

{ #category : #accessing }
MMHypoth >> mands [

^ {  }
]

{ #category : #copying }
MMHypoth >> postCopy [ 

"body := body collect: [ :ea | ea copy ] ."

body := body copy.

announcer := Announcer new
]

{ #category : #accessing }
MMHypoth >> usableElement: controller [
"make element for usableThingsList."
| aEventListener el |

self error .

aEventListener := MmOnBoardHypothEventListener  new gameController: controller  .

"el := self gameElement addEventHandler: aEventListener ."

el := MmOnBoardEssentialHypothesisElement new model: self .

el addEventHandler: aEventListener .

^ el .

]
