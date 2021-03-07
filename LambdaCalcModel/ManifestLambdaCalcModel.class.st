"
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
