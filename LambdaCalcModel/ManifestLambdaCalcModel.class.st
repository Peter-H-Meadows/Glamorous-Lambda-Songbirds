"
todo: 
more pure bootstrap.
	use petit Parser instead of 
	write MACROs to gen all tests . Do I _need_ Macro for this? (i thought smalltalk didn't use Macros but i never understood why not.)
make screen capture video for github page.
use fixed color set instead of random colours.

Merge / abstract with metamath stuff??

add GUI that uses Mondrian more.

add GUI that is closer to Keenan's animations.

add GUI that is like Viktor Massalõgin bubbles / Visual Lambda Calculus.

Alligator Eggs?


auto generate first x birds

story puzzle game. introduce idiot. she repeats anything she hears . she loves all birds.
it has a big heart and is fond of every bird.

a bird can use a sim. a sim has code and data slot. when activated.. code is a bird return what it would sing if it hears dataslot .

mockingbird connects her ear to both the code and data slots of a sim (applicator). looper.
singing mockingbird to a mockingbird causes neverending loop.

kite always sings idiot song no matter what she hears.

kestrel returns a bird that always returns what kes hears. konstant x.

to gen birds. eat bird, rewire/plum ears connect to slots.

There are sixteen two-layer birds that have two applicators and not all of them have English names.

Now that we have birds with more than one layer and more than one applicator we can distinguish two major sections of any song map, 
the rhyme and the rhythm. The rhyme is the section at the leftmost end of a box, where all the fan-outs and crossings occur. 
For example the Lark and the Warbler have the same rhyme. 
If we assign the letter 'a' to the outermost ear and 'b' to the inner one and follow the pipes to the right past the sloping sections until they run parallel again, we can write the Lark and Warbler's rhyme as ""abb"" corresponding to the downward direction on the song map. The Crossed Warbler then has ""baa"" and the Owl has ""bab"". For birds with two layers and two applicators there are eight possible rhyme schemes. The general rule is for birds with l layers and a applicators there are l a+1 rhyme schemes.

The rhythm section is the section immediately to the right of the rhyme, containing the applicators. Notice that there are no fan-outs or crossings in the rhythm section, only pipes being reduced in pairs, via applicators, until only one pipe remains. This pipe then connects to the throat. You can see that the Lark and the Owl have the same rhythm but this is different from the rhythm shared by the Warbler and the Crossed Warbler. The first we write as ""(-(- -))"" and the second ""((- -) -)"", although in future we can omit the outer brackets without ambiguity. These are the only possible rhythms for a bird with two applicators. It could be that the duration of the notes is halved each time we enter parentheses and doubled again when we leave. Figure 14 shows a Lark and a Crossed Warbler annotated to show the correspondence between textual and graphical notations.

You may have noticed that a rhythm section corresponds to a binary tree. 
The number of rhythms using a applicators is the a-th Catalan number which can be found by taking the number of rhythms using a-1 applicators and multiplying by (4a-2)/(a + 1). 

Of course there is only one rhythm with zero applicators. 
The series starts, 1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, ... .


We can determine the number of possible birds with a given number of layers and applicators by multiplying these two numbers together (rhymes x rhythms). 
We can combine the textual notations used above for rhyme and rhythm to give song schemes like ""(ab)b"" for the Warbler and ""b(ab)"" for the owl. 
However, this is not enough to uniquely describe a bird textually since for example the Idiot bird and the Kestrel would both be ""a"". 
We must also indicate how many layers the bird has. 
We do this by prefixing the rhyme and rhythm with a complete list of the layers involved from outside to inside, preceded traditionally by a lambda (λ) and followed by a dot. So the Idiot bird is ""λa.a"", the Mockingbird is ""λa.aa"", the Kestrel is ""λab.a"" and the Kite is ""λab.b"".

There is no limit to the number of applicators a bird can have. It does not depend on the number of layers. For example, the multiple-mockingbird family consists of all birds with only one layer. There are two different double-mockingbirds (having two applicators), five triple-mockingbirds (three applicators), fourteen quadruple-mockingbirds and so on. Under this scheme, the Idiot bird may be considered as the zeruple-mockingbird. [Note: This is different to the sense in which Smullyan uses ""double mockingbird""]

Of the 80 two-layer birds which have three applicators, I show only the Turing bird, named after its discoverer the logician and computer scientist Alan Turing. See figure 15. I will tell you more later about the importance of the Turing bird in connection with fixed-point birds.




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The combinator birds of Raymond Smullyan's
;; ""To Mock a Mockingbird"" (Knopf, 1985)
;; ISBN 0-394-53491-3
;;
;; Note that some birds (Î˜, Î©, P, ...) are excluded, either
;; because their definitions are impossible or because the
;; author hasn't gotten around to it. Contributions and
;; corrections are welcome at <evhan@thunktastic.com>.
(module combinator-birds *
  (import scheme)

  ;; Implicit currying
  (define-syntax Î»
    (syntax-rules ()
      ((_ (<arg> ...) <body> ...)
       (let ((fn (lambda (<arg> ...) <body> ...))
             (len (length '(<arg> ...))))
         (let loop ((i 0) (lst '()))
           (lambda args
             (let ((i (+ (length args) i))
                   (lst (append lst args)))
               (if (< i len)
                 (loop i lst)
                 (apply fn lst)))))))))

  ;; ""To Mock a Mockingbird"" pp. 73-74
  (define mockingbird   (Î» (x) (x x)))

  ;; ""Hopeless Egocentricity"" pp. 76-78
  (define kestrel       (Î» (x y) x))

  ;; ""Identity Birds"" pp. 78-80
  (define identity-bird (Î» (x) x))

  ;; ""Larks"" pp. 80-81
  (define lark          (Î» (x y) (x (y y))))

  ;; ""Is There a Sage Bird?"" pp. 89-92
  ;; Unfortunately without a lazy scheme the naive
  ;; definition here doesn't work. We can fake it with
  ;; a proper Y for call-by-value, though obviously
  ;; the various derivations given in the text
  ;; (SLL, BML, etc.) will still not work.
  (define sage-bird
    (Î» (x) ((Î» (y) (x (Î» (x) ((y y) x))))
              (Î» (y) (x (Î» (x) ((y y) x)))))))

  ;; ""Bluebirds"" pp. 95-96
  (define bluebird      (Î» (x y z) (x (y z))))

  ;; ""Some Derivatives of the Bluebird"" pp. 96-98
  (define dove          (Î» (x y z w) ((x y) (z w))))
  (define blackbird     (Î» (x y z w) (x ((y z) w))))
  (define eagle         (Î» (x y z w v) ((x y) ((z w) v))))
  (define bunting       (Î» (x y z w v) (x (((y z) w) v))))
  (define dickcissel    (Î» (x y z w v) (((x y) z) (w v))))
  (define becard        (Î» (x y z w) (x (y (z w)))))
  (define dovekies      (Î» (x y z w v) ((x (y z)) (w v))))
  (define bald-eagle    (Î» (x y z w v u t)
                          ((x ((y z) w)) ((v u) t))))

  ;; ""Some Other Birds"" pp. 99-101
  (define warbler       (Î» (x y) ((x y) y)))
  (define cardinal      (Î» (x y z) ((x z) y)))
  (define thrush        (Î» (x y) (y x)))

  ;; ""Bluebirds and Thrushes"" pp. 101-103
  (define robin         (Î» (x y z) ((y z) x)))
  (define finch         (Î» (x y z) ((z y) x)))
  (define vireo         (Î» (x y z) ((z x) y)))

  ;; ""Some Relatives"" pp. 103-105
  (define cardinal*     (Î» (x y z w) (((x y) w) z)))
  (define robin*        (Î» (x y z w) (((x z) w) y)))
  (define finch*        (Î» (x y z w) (((x w) z) y)))
  (define vireo*        (Î» (x y z w) (((x w) z) y)))
  (define cardinal**    (Î» (x y z w v) ((((x y) z) w) v)))
  (define robin**       (Î» (x y z w v) ((((x y) w) v) z)))
  (define finch**       (Î» (x y z w v) ((((x y) v) w) z)))
  (define vireo**       (Î» (x y z w v) ((((x y) z) w) v)))

  ;; ""Queer Birds"" pp. 105-108
  (define queer-bird       (Î» (x y z) (y (x z))))
  (define quixotic-bird    (Î» (x y z) (x (z y))))
  (define quizzical-bird   (Î» (x y z) (y (z x))))
  (define quirky-bird      (Î» (x y z) (z (x y))))
  (define quacky-bird      (Î» (x y z) (z (y x))))
  (define goldfinch        (Î» (x y z w) ((x w) (y z))))

  ;; ""More on Mockingbirds"" pp. 117-118
  (define double-mockingbird  (Î» (x y) ((x y) (x y))))

  ;; ""Warblers"" pp. 118-120
  (define converse-warbler (Î» (x y) ((y x) x)))
  (define warbler*         (Î» (x y z) (((x y) z) z)))
  (define warbler**        (Î» (x y z w) ((((x y) z) w) w)))
  (define hummingbird      (Î» (x y z) (((x y) z) y)))

  ;; ""Starlings"" pp. 120-121
  (define starling         (Î» (x y z) ((x z) (y z))))

  ;; ""Starlings in Action"" pp. 121-125
  (define phoenix          (Î» (x y z w) ((x (y w)) (z w))))
  (define psi-bird         (Î» (x y z w) ((x (y z)) (y w))))

  ;; ""The Turing Bird"" pp. 132-133
  (define turing-bird      (Î» (x y) (y ((x x) y))))

  ;; ""Owls"" p. 133
  (define owl              (Î» (x y) (y (x y))))

  ;; ""Aristocratic Birds"" pp. 179-181
  (define jay              (Î» (x y z w) ((x y) ((x w) z))))

  ;; Aliases
  (define oracle-bird sage-bird)
  (define idiot-bird identity-bird)

  ;; A few birds and aliases not necessarily given in the book
  ;; but discussed in David Keenan's http://dkeenan.com/Lambda/
  (define identity-bird*   (Î» (x y) (x y)))
  (define kite             (Î» (x y) y))
  (define konstant-mocker  (Î» (x y) (y y)))
  (define crossed-konstant-mocker (Î» (x y) (x x)))
  (define idiot-bird* identity-bird*)
  (define pairing vireo))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The single-letter names of the various combinators
;; as given in ""Who's Who Among The Birds"", pp. 244-246
(module combinator-letters *
  (import scheme combinator-birds)
  (define B bluebird)
  (define C cardinal)
  (define D dove)
  (define E eagle)
  (define F finch)
  (define G goldfinch)
  (define H hummingbird)
  (define I identity-bird)
  (define J jay)
  (define K kestrel)
  (define L lark)
  (define M mockingbird)
  ;; P is used in ""Russell's Forest"" pp. 151-153
  (define O owl)
  ;; N is used in ""Curry's Lively Bird Forest"" pp. 143-147
  (define Q queer-bird)
  (define R robin)
  (define S starling)
  (define T thrush)
  (define U turing-bird)
  (define V vireo)
  (define W warbler)
  ;; X is used in ""The Master Forest"" pp. 167-178
  (define Y sage-bird))
"
Class {
	#name : #ManifestLambdaCalcModel,
	#superclass : #PackageManifest,
	#category : #'LambdaCalcModel-Manifest'
}
