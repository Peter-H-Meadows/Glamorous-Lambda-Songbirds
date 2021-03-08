"
!Songbirds
trying to implement *http://dkeenan.com/Lambda/* (animated lambda calculus).
Learning GT  *https://gtoolkit.com*


!!Features wanted
GUI should let us set the animation speed and pause the animation at any time.

Do we ever need care about reversing the animation so we can go forwards and backwards in time?
Prob don't need this.

 type in a formal lambda expression , parse it and draw a graphical representation of it.
e.g λn.λf.λx.n (λg.λh.h (g f)) (λu.x) (λu.u)

Use SKI and curry syntax interchangably and convert from one to the other.
e.g S(SI(KF))(KT) (as S(SI(KF))(KT)x = SI(KF)x(KTx) = Ix(KFx)T = xFT)

I want to be able to enter/create different lambda expressions with the GUI, then 'run' the expression and animate what is happening.

so for example; 

1) I can click on our graphical representation of an idiot/identity bird, sing the idiot/identity bird song to him, and show the output of the idiot song/bird/SongBird

example 
2) Any song sung to the Konstant Idiot/Id will show the input being ignored/disappearing and the output of an Idiot bird

3) If I select a Mocking Bird in the gui, then click on another mocking bird, I want the gui to animate the song moving into the ear of the mocking bird,
then showing the input (the mocking bird song) moving to the mocking birds brain/applicator, (so the visual element is cloned, one for each slot, and slide animated to slot, then applicator/brain is applied/activated.

in Keenan's 'Graphical Notation for the Lambda Calculus with Animated Reduction' The Mocking bird is showns forever looping through one cycle.

We can see that an applicator receives information from above and from its left and responds to its right.
 
It is called an applicator because of what it does with the information it receives; 
it applies the bird whose description it receives from above, to the song which it receives from its left, in order to determine its response. 

The song arriving at the top is called the operator and the one from the left, the operand. 
You might think of the circle as representing an ear and throat with nothing between them, but waiting to have a song map introduced between them from above.

You might also think of the applicator as a sort of universal bird since all it requires is the description of a bird in order to become that bird.

for list of pros cons for a sample of graphical notations see bubbles paper. he looks at keenan's crocodial game, and implements new one in python.
how much overlap is there between all those systems? 
!!Links
 *http://www.cs.ru.nl/~henk/Reflection-Use.pdf*
 
 
*https://youtu.be/7HKbjYqqPPQ* 2017 ACM PPoPP Keynote: It's Time for a New Old Language. GT
+ growing a lang from 1998

*http://dkeenan.com/Lambda/index.htm*

*https://en.wikipedia.org/wiki/To_Mock_a_Mockingbird*

*https://www.angelfire.com/tx4/cus/combinator/birds.html*

"
Class {
	#name : #ManifestLambdaSongBirds,
	#superclass : #PackageManifest,
	#category : #'LambdaSongBirds-Manifest'
}
