"
$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                True and false constants
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
       Universal quantifier for use by df-tru
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Even though it isn't ordinarily part of propositional calculus, the universal
  quantifier ` A. ` is introduced here so that the soundness of definition
  ~ df-tru can be checked by the same algorithm that is used for predicate
  calculus.  Its first real use is in definition ~ df-ex in the predicate
  calculus section below.  For those who want propositional calculus to be
  self-contained i.e. to use wff variables only, the alternate definition
  ~ dftru2 may be adopted and this subsection moved down to the start of the
  subsection with ~ wex below.  However, the use of ~ dftru2 as a definition
  requires a more elaborate definition checking algorithm that we prefer to
  avoid.

$)

  $( Declare new symbols needed for predicate calculus. $)
  $c A. $. $( ""inverted A"" universal quantifier (read:  ""for all"") $)
  $c setvar $. $( Individual variable type (read:  ""the following is an
             individual (set) variable"" $)

  $( Add 'setvar' as a typecode for bound variables. $)
  $( $j syntax 'setvar'; bound 'setvar'; $)


  ${
    $v xxx $.
    $( Let ` x ` be an individual variable (temporary declaration). $)
    vx.wal $f setvar x $.
    $( Extend wff definition to include the universal quantifier ('for all').
       ` A. x ph ` is read "" ` ph ` (phi) is true for all ` x ` .""  Typically,
       in its final application ` ph ` would be replaced with a wff containing
       a (free) occurrence of the variable ` x ` , for example ` x = y ` .  In
       a universe with a finite number of objects, ""for all"" is equivalent to a
       big conjunction (AND) with one wff for each possible case of ` x ` .
       When the universe is infinite (as with set theory), such a
       propositional-calculus equivalent is not possible because an infinitely
       long formula has no meaning, but conceptually the idea is the same. $)
    wal $a wff A. x ph $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
        Equality predicate for use by df-tru
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Even though it isn't ordinarily part of propositional calculus, the equality
  predicate ` = ` is introduced here so that the soundness of definition
  ~ df-tru can be checked by the same algorithm as is used for predicate
  calculus.  Its first real use is in theorem ~ equs3 in the predicate calculus
  section below.  For those who want propositional calculus to be
  self-contained i.e. to use wff variables only, the alternate definition
  ~ dftru2 may be adopted and this subsection moved down to just above ~ weq
  below.  However, the use of ~ dftru2 as a definition requires a more
  elaborate definition checking algorithm that we prefer to avoid.
$)

  $c class $.

  $( Add 'class' as a typecode. $)
  $( $j syntax 'class'; $)

  ${
    $v x $.
    $( Let ` x ` be an individual variable (temporary declaration). $)
    vx.cv $f setvar x $.
    $( This syntax construction states that a variable ` x ` , which has been
       declared to be a setvar variable by $f statement vx, is also a class
       expression.  This can be justified informally as follows.  We know that
       the class builder ` { y | y e. x } ` is a class by ~ cab .  Since (when
       ` y ` is distinct from ` x ` ) we have ` x = { y | y e. x } ` by
       ~ cvjust , we can argue that the syntax "" ` class x ` "" can be viewed as
       an abbreviation for "" ` class { y | y e. x } ` "".  See the discussion
       under the definition of class in [Jech] p. 4 showing that ""Every set can
       be considered to be a class.""

       While it is tempting and perhaps occasionally useful to view ~ cv as a
       ""type conversion"" from a setvar variable to a class variable, keep in
       mind that ~ cv is intrinsically no different from any other
       class-building syntax such as ~ cab , ~ cun , or ~ c0 .

       For a general discussion of the theory of classes and the role of ~ cv ,
       see ~ http://us.metamath.org/mpeuni/mmset.html#class .

       (The description above applies to set theory, not predicate calculus.
       The purpose of introducing ` class x ` here, and not in set theory where
       it belongs, is to allow us to express i.e.  ""prove"" the ~ weq of
       predicate calculus from the ~ wceq of set theory, so that we don't
       overload the ` = ` connective with two syntax definitions.  This is done
       to prevent ambiguity that would complicate some Metamath parsers.) $)
    cv $a class x $.
  $}

  $( Declare the equality predicate symbol. $)
  $c = $.  $( Equal sign (read:  'is equal to') $)

  ${
    $v A $.
    $v B $.
    $( Temporary declarations of ` A ` and ` B ` . $)
    cA.wceq $f class A $.
    cB.wceq $f class B $.
    $( Extend wff definition to include class equality.

       For a general discussion of the theory of classes, see
       ~ http://us.metamath.org/mpeuni/mmset.html#class .

       (The purpose of introducing ` wff A = B ` here, and not in set theory
       where it belongs, is to allow us to express i.e.  ""prove"" the ~ weq of
       predicate calculus in terms of the ~ wceq of set theory, so that we
       don't ""overload"" the ` = ` connective with two syntax definitions.  This
       is done to prevent ambiguity that would complicate some Metamath
       parsers.  For example, some parsers - although not the Metamath program
       - stumble on the fact that the ` = ` in ` x = y ` could be the ` = ` of
       either ~ weq or ~ wceq , although mathematically it makes no
       difference.  The class variables ` A ` and ` B ` are introduced
       temporarily for the purpose of this definition but otherwise not used in
       predicate calculus.  See ~ df-cleq for more information on the set
       theory usage of ~ wceq .) $)
    wceq $a wff A = B $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
                Define the true and false constants
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c T. $.

  $( ` T. ` is a wff. $)
  wtru $a wff T. $.

  ${
    $v x $.
    $v y $.
    $( Temporary declarations of ` x ` and ` y ` for local use by ~ df-tru .
       These will be redeclared globally in the predicate calculus section. $)
    vx.tru $f setvar x $.
    vy.tru $f setvar y $.
    $( Soundness justification theorem for ~ df-tru .  (Contributed by Mario
       Carneiro, 17-Nov-2013.)  (Revised by NM, 11-Jul-2019.) $)
    trujust $p |- ( ( A. x x = x -> A. x x = x )
              <-> ( A. y y = y -> A. y y = y ) ) $=
      ( cv wceq wal wi id 2th ) ACZIDAEZJFBCZKDBEZLFJGLGH $.

    $( Definition of the truth value ""true"", or ""verum"", denoted by ` T. ` .
       This is a tautology, as proved by ~ tru .  In this definition, an
       instance of ~ id is used as the definiens, although any tautology, such
       as an axiom, can be used in its place.  This particular ~ id instance
       was chosen so this definition can be checked by the same algorithm that
       is used for predicate calculus.  This definition should be referenced
       directly only by ~ tru , and other proofs should depend on ~ tru
       (directly or indirectly) instead of this definition, since there are
       many alternative ways to define ` T. ` .  (Contributed by Anthony Hart,
       13-Oct-2010.)  (Revised by NM, 11-Jul-2019.)
       (New usage is discouraged.) $)
    df-tru $a |- ( T. <-> ( A. x x = x -> A. x x = x ) ) $.

    $( The truth value ` T. ` is provable.  (Contributed by Anthony Hart,
       13-Oct-2010.) $)
    tru $p |- T. $=
      ( vx.tru wtru cv wceq wal wi id df-tru mpbir ) BACZJDAEZKFKGAHI $.
  $}

  $c F. $.

  $( ` F. ` is a wff. $)
  wfal $a wff F. $.

  $( Definition of the truth value ""false"", or ""falsum"", denoted by ` F. ` .
     See also ~ df-tru .  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  df-fal $a |- ( F. <-> -. T. ) $.

  $( The truth value ` F. ` is refutable.  (Contributed by Anthony Hart,
     22-Oct-2010.)  (Proof shortened by Mel L. O'Cat, 11-Mar-2012.) $)
  fal $p |- -. F. $=
    ( wfal wtru wn tru notnoti df-fal mtbir ) ABCBDEFG $.

  $( An alternate definition of ""true"".  (Contributed by Anthony Hart,
     13-Oct-2010.)  (Revised by BJ, 12-Jul-2019.)
     (New usage is discouraged.) $)
  dftru2 $p |- ( T. <-> ( ph -> ph ) ) $=
    ( wtru wi tru id 2th ) BAACDAEF $.

  ${
    trud.1 $e |- ( T. -> ph ) $.
    $( Eliminate ` T. ` as an antecedent.  A proposition implied by ` T. ` is
       true.  (Contributed by Mario Carneiro, 13-Mar-2014.) $)
    trud $p |- ph $=
      ( wtru tru ax-mp ) CADBE $.
  $}

  $( A proposition is equivalent to itself being equivalent to ` T. ` .
     (Contributed by Anthony Hart, 14-Aug-2011.) $)
  tbtru $p |- ( ph <-> ( ph <-> T. ) ) $=
    ( wtru tru tbt ) BACD $.

  $( The negation of a proposition is equivalent to itself being equivalent to
     ` F. ` .  (Contributed by Anthony Hart, 14-Aug-2011.) $)
  nbfal $p |- ( -. ph <-> ( ph <-> F. ) ) $=
    ( wfal fal nbn ) BACD $.

  ${
    bitru.1 $e |- ph $.
    $( A theorem is equivalent to truth.  (Contributed by Mario Carneiro,
       9-May-2015.) $)
    bitru $p |- ( ph <-> T. ) $=
      ( wtru tru 2th ) ACBDE $.
  $}

  ${
    bifal.1 $e |- -. ph $.
    $( A contradiction is equivalent to falsehood.  (Contributed by Mario
       Carneiro, 9-May-2015.) $)
    bifal $p |- ( ph <-> F. ) $=
      ( wfal fal 2false ) ACBDE $.
  $}

  $( The truth value ` F. ` implies anything.  Also called the principle of
     explosion, or ""ex falso quodlibet"".  (Contributed by FL, 20-Mar-2011.)
     (Proof shortened by Anthony Hart, 1-Aug-2011.) $)
  falim $p |- ( F. -> ph ) $=
    ( wfal fal pm2.21i ) BACD $.

  $( The truth value ` F. ` implies anything.  (Contributed by Mario Carneiro,
     9-Feb-2017.) $)
  falimd $p |- ( ( ph /\ F. ) -> ps ) $=
    ( wfal falim adantl ) CBABDE $.

  $( Anything implies ` T. ` .  (Contributed by FL, 20-Mar-2011.)  (Proof
     shortened by Anthony Hart, 1-Aug-2011.) $)
  a1tru $p |- ( ph -> T. ) $=
    ( wtru tru a1i ) BACD $.

  $( True can be removed from a conjunction.  (Contributed by FL,
     20-Mar-2011.)  (Proof shortened by Wolf Lammen, 21-Jul-2019.) $)
  truan $p |- ( ( T. /\ ph ) <-> ph ) $=
    ( wtru wa tru biantrur bicomi ) ABACBADEF $.

  $( Obsolete proof of ~ truan as of 21-Jul-2019.  (Contributed by FL,
     20-Mar-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  truanOLD $p |- ( ( T. /\ ph ) <-> ph ) $=
    ( wtru wa simpr a1tru ancri impbii ) BACABADABAEFG $.

  $( Given falsum ` F. ` , we can define the negation of a wff ` ph ` as the
     statement that ` F. ` follows from assuming ` ph ` .  (Contributed by
     Mario Carneiro, 9-Feb-2017.)  (Proof shortened by Wolf Lammen,
     21-Jul-2019.) $)
  dfnot $p |- ( -. ph <-> ( ph -> F. ) ) $=
    ( wfal wn wi wb fal mtt ax-mp ) BCACABDEFBAGH $.

  $( Obsolete proof of ~ dfnot as of 21-Jul-2019.  (Contributed by Mario
     Carneiro, 9-Feb-2017.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  dfnotOLD $p |- ( -. ph <-> ( ph -> F. ) ) $=
    ( wn wfal wi pm2.21 id falim ja impbii ) ABZACDACEACJJFJGHI $.

  ${
    inegd.1 $e |- ( ( ph /\ ps ) -> F. ) $.
    $( Negation introduction rule from natural deduction.  (Contributed by
       Mario Carneiro, 9-Feb-2017.) $)
    inegd $p |- ( ph -> -. ps ) $=
      ( wfal wi wn ex dfnot sylibr ) ABDEBFABDCGBHI $.
  $}

  ${
    efald.1 $e |- ( ( ph /\ -. ps ) -> F. ) $.
    $( Deduction based on reductio ad absurdum.  (Contributed by Mario
       Carneiro, 9-Feb-2017.) $)
    efald $p |- ( ph -> ps ) $=
      ( wn inegd notnotrd ) ABABDCEF $.
  $}

  ${
    pm2.21fal.1 $e |- ( ph -> ps ) $.
    pm2.21fal.2 $e |- ( ph -> -. ps ) $.
    $( If a wff and its negation are provable, then falsum is provable.
       (Contributed by Mario Carneiro, 9-Feb-2017.) $)
    pm2.21fal $p |- ( ph -> F. ) $=
      ( wfal pm2.21dd ) ABECDF $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Truth tables
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Some sources define operations on true/false values using truth tables.
  These tables show the results of their operations for all possible
  combinations of true ( ` T. ` ) and false ( ` F. ` ).
  Here we show that our definitions and axioms produce equivalent results for
  ` /\ ` (conjunction aka logical 'and') ~ df-an ,
  ` \/ ` (disjunction aka logical inclusive 'or') ~ df-or ,
  ` -> ` (implies) ~ wi ,
  ` -. ` (not) ~ wn ,
  ` <-> ` (logical equivalence) ~ df-bi ,
  ` -/\ ` (nand aka Sheffer stroke) ~ df-nan , and
  ` \/_ ` (exclusive or) ~ df-xor .
$)

  $( A ` /\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  truantru $p |- ( ( T. /\ T. ) <-> T. ) $=
    ( wtru anidm ) AB $.

  $( A ` /\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  truanfal $p |- ( ( T. /\ F. ) <-> F. ) $=
    ( wfal truan ) AB $.

  $( A ` /\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  falantru $p |- ( ( F. /\ T. ) <-> F. ) $=
    ( wfal wtru wa fal intnanr bifal ) ABCABDEF $.

  $( A ` /\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  falanfal $p |- ( ( F. /\ F. ) <-> F. ) $=
    ( wfal anidm ) AB $.

  $( A ` \/ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  truortru $p |- ( ( T. \/ T. ) <-> T. ) $=
    ( wtru oridm ) AB $.

  $( A ` \/ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  truorfal $p |- ( ( T. \/ F. ) <-> T. ) $=
    ( wtru wfal wo tru orci bitru ) ABCABDEF $.

  $( A ` \/ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  falortru $p |- ( ( F. \/ T. ) <-> T. ) $=
    ( wfal wtru wo tru olci bitru ) ABCBADEF $.

  $( A ` \/ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  falorfal $p |- ( ( F. \/ F. ) <-> F. ) $=
    ( wfal oridm ) AB $.

  $( A ` -> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  truimtru $p |- ( ( T. -> T. ) <-> T. ) $=
    ( wtru wi id bitru ) AABACD $.

  $( A ` -> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  truimfal $p |- ( ( T. -> F. ) <-> F. ) $=
    ( wfal wtru wi tru a1bi bicomi ) ABACBADEF $.

  $( A ` -> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  falimtru $p |- ( ( F. -> T. ) <-> T. ) $=
    ( wfal wtru wi falim bitru ) ABCBDE $.

  $( A ` -> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  falimfal $p |- ( ( F. -> F. ) <-> T. ) $=
    ( wfal wi id bitru ) AABACD $.

  $( A ` -. ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
  nottru $p |- ( -. T. <-> F. ) $=
    ( wfal wtru wn df-fal bicomi ) ABCDE $.

  $( A ` -. ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  notfal $p |- ( -. F. <-> T. ) $=
    ( wfal wn fal bitru ) ABCD $.

  $( A ` <-> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  trubitru $p |- ( ( T. <-> T. ) <-> T. ) $=
    ( wtru wb biid bitru ) AABACD $.

  $( A ` <-> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  trubifal $p |- ( ( T. <-> F. ) <-> F. ) $=
    ( wtru wfal wb wn nottru nbbn mpbi bifal ) ABCZADBCIDEABFGH $.

  $( A ` <-> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  falbitru $p |- ( ( F. <-> T. ) <-> F. ) $=
    ( wfal wtru wb bicom trubifal bitri ) ABCBACAABDEF $.

  $( A ` <-> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  falbifal $p |- ( ( F. <-> F. ) <-> T. ) $=
    ( wfal wb biid bitru ) AABACD $.

  $( A ` -/\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  trunantru $p |- ( ( T. -/\ T. ) <-> F. ) $=
    ( wtru wnan wn wfal nannot nottru bitr3i ) AABACDAEFG $.

  $( A ` -/\ ` identity.  (Contributed by Anthony Hart, 23-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  trunanfal $p |- ( ( T. -/\ F. ) <-> T. ) $=
    ( wtru wfal wnan wa wn df-nan truanfal notbii notfal 3bitri ) ABCABDZEBEAAB
    FKBGHIJ $.

  $( A ` -/\ ` identity.  (Contributed by Anthony Hart, 23-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  falnantru $p |- ( ( F. -/\ T. ) <-> T. ) $=
    ( wfal wtru wnan nancom trunanfal bitri ) ABCBACBABDEF $.

  $( A ` -/\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
  falnanfal $p |- ( ( F. -/\ F. ) <-> T. ) $=
    ( wfal wnan wn wtru nannot notfal bitr3i ) AABACDAEFG $.

  $( A ` \/_ ` identity.  (Contributed by David A. Wheeler, 8-May-2015.) $)
  truxortru $p |- ( ( T. \/_ T. ) <-> F. ) $=
    ( wtru wxo wn wfal wb df-xor trubitru xchbinx nottru bitri ) AABZACDKAAEAAA
    FGHIJ $.

  $( A ` \/_ ` identity.  (Contributed by David A. Wheeler, 8-May-2015.) $)
  truxorfal $p |- ( ( T. \/_ F. ) <-> T. ) $=
    ( wtru wfal wxo wn wb df-xor trubifal xchbinx notfal bitri ) ABCZBDAKABEBAB
    FGHIJ $.

  $( A ` \/_ ` identity.  (Contributed by David A. Wheeler, 9-May-2015.) $)
  falxortru $p |- ( ( F. \/_ T. ) <-> T. ) $=
    ( wfal wtru wxo wb wn df-xor falbitru notbii notfal 3bitri ) ABCABDZEAEBABF
    KAGHIJ $.

  $( A ` \/_ ` identity.  (Contributed by David A. Wheeler, 9-May-2015.) $)
  falxorfal $p |- ( ( F. \/_ F. ) <-> F. ) $=
    ( wfal wxo wtru wn wb df-xor falbifal xchbinx nottru bitri ) AABZCDAKAAECAA
    FGHIJ $.

  $( Add support for natural deduction, indicating the constants used to
     indicate implication, context conjunction, and empty context. $)
  $( $j natded_init 'wi' 'wa' 'wtru'; $)

  $( These are variations on the assumption rule of natural deduction.
     They have the form ` Gamma -> ph ` where ` Gamma ` is composed entirely
     of (binary) conjunctions and one of the conjuncts is ` ph ` . $)
  $( $j natded_assume 'id' 'simpl' 'simpr'
          'simpll' 'simplr' 'simprl' 'simprr'
          'simplll' 'simpllr' 'simplrl' 'simplrr'
          'simprll' 'simprlr' 'simprrl' 'simprrr'
          'simp-4l' 'simp-4r' 'simp-5l' 'simp-5r'
          'simp-6l' 'simp-6r' 'simp-7l' 'simp-7r'
          'simp-8l' 'simp-8r' 'simp-9l' 'simp-9r'
          'simp-10l' 'simp-10r' 'simp-11l' 'simp-11r'; $)

  $( These are variations on the weakening lemma of natural deduction.
     They have the form ` _D -> ph |- _G -> ph ` where ` _G `
     and ` _D ` are composed entirely of (binary) conjunctions and
     ` _D C_ _G ` . $)
  $( $j natded_weak 'a1i' 'adantl' 'adantr'
          'adantll' 'adantlr' 'adantrl' 'adantrr'
          'adantlll' 'adantllr' 'adantlrl' 'adantlrr'
          'adantrll' 'adantrlr' 'adantrrl' 'adantrrr'
          'ad2antll' 'ad2antlr' 'ad2antrl' 'ad2antrr'
          'ad2ant2l' 'ad2ant2lr' 'ad2ant2rl' 'ad2ant2r'
          'ad3antlr' 'ad3antrrr' 'ad4antlr' 'ad4antr'
          'ad4antlr' 'ad4antr' 'ad5antlr' 'ad5antr'
          'ad6antlr' 'ad6antr' 'ad7antlr' 'ad7antr'
          'ad8antlr' 'ad8antr' 'ad9antlr' 'ad9antr'
          'ad10antlr' 'ad10antr'
          'anidms' 'ancoms' 'anasss' 'anassrs' 'an12s'  'ancom2s' 'an13s'
          'an32s' 'ancom1s' 'an31s' 'anass1rs' 'anabsan'  'anabss1' 'anabss4'
          'anabss5' 'anabss7' 'anabsan2' 'anabss3' 'an4s' 'an42s'
          'anandis' 'anandirs'; $)

  $( These are variations on the cut axiom (modus ponens) of natural deduction.
     All assumptions and the consequent have the form ` ph ` or ` _G -> ph `
     where ` _G ` is composed entirely of (binary) conjunctions, and possibly
     some intermediate statements are cancelled. (This does not include the
     ""natded_assume"" and ""natded_weak"" lists, which also count in this
     category.) $)
  $( $j natded_cut 'mp2b' 'mp1i' 'syl' '3syl' '4syl' 'syldan' 'sylan' 'sylan2'
          'syl2an' 'syl2anr' 'sylanl1' 'sylanl2' 'sylanr1' 'sylanr2' 'syl2anc'
          'sylancl' 'sylancr' 'sylancom' 'mpdan' 'mpancom' 'mpan' 'mpan2'
          'mp2an' 'mp4an' 'mpanl1' 'mpanl2' 'mpanl12' 'mpanr1' 'mpanr2'
          'mpanr12' 'mpanlr1' 'syl12anc' 'syl21anc' 'syl22anc'; $)

  $( Natural deduction rules for the logical connectives, defining the
     connective itself and natural deduction rules pertaining to it.
     These don't have a fixed form, except that all the statements should be
     parseable as natural deduction statements, i.e. ` ph ` or ` _G -> ph `
     where _G is a nested conjunction. $)
  $( $j natded_true 'wtru' with 'trud' 'tru' 'a1tru';
        natded_imp 'wi' with 'ex' 'imp' 'mpd' 'ax-mp' 'syl' 'mpi';
        natded_and 'wa' with 'jca' 'pm3.2i' 'jca31' 'jca32' 'jctil' 'jctir'
          'jctl' 'jctr' 'ancli' 'ancri';
        natded_or 'wo' with 'olc' 'orc' 'olci' 'orci' 'olcd' 'orcd' 'olcs'
          'orcs' 'jaoi' 'jaod' 'jaodan' 'mpjaodan';
        natded_not 'wn' 'wfal' with 'falim' 'falimd' 'inegd' 'mtand' 'pm2.65da'
          'pm2.01da' 'pm2.18da' 'pm2.21dd' 'pm2.21fal' 'efald' 'pm2.18da'
          'notnot2' 'notnotrd'; $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Half adder and full adder in propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Propositional calculus deals with truth values, which can be interpreted as
  bits. Using this, we can define the half adder and full adder in pure
  propositional calculus, and show their basic properties.

  Here is a short description. We code the bit 0 by ` F. ` and 1 by ` T. ` .
  Even though ` hadd ` and ` cadd ` are invariant under permutation of their
  arguments, assume for the sake of concreteness that ` ph ` (resp. ` ps ` ) is
  the i^th bit of the first (resp. second) number to add (with the convention
  that the i^th bit is the multiple of 2^i in the base-2 representation), and
  that ` ch ` is the i^th carry (with the convention that the 0^th carry is 0).
  Then, ` hadd ( ph , ps , ch ) ` gives the i^th bit of the sum, and
  ` cadd ( ph , ps , ch ) ` gives the (i+1)^th carry.
  Then, addition is performed by iteration from i = 0 to
  i = 1 + (max of the number of digits of the two summands) by ""updating"" the
  carry.
$)

  $c hadd cadd $.
  $c , $.  $( Comma (also used for unordered pair notation later) $)

  $( Define the half adder (triple XOR).  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  whad $a wff hadd ( ph , ps , ch ) $.

  $( Define the half adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  wcad $a wff cadd ( ph , ps , ch ) $.

  $( Define the half adder (triple XOR).  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  df-had $a |- ( hadd ( ph , ps , ch ) <-> ( ( ph \/_ ps ) \/_ ch ) ) $.

  $( Define the half adder carry, which is true when at least two arguments are
     true.  (Contributed by Mario Carneiro, 4-Sep-2016.) $)
  df-cad $a |- ( cadd ( ph , ps , ch ) <->
    ( ( ph /\ ps ) \/ ( ch /\ ( ph \/_ ps ) ) ) ) $.

  ${
    hadbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    hadbid.2 $e |- ( ph -> ( th <-> ta ) ) $.
    hadbid.3 $e |- ( ph -> ( et <-> ze ) ) $.
    $( Equality theorem for half adder.  (Contributed by Mario Carneiro,
       4-Sep-2016.) $)
    hadbi123d $p |- ( ph ->
      ( hadd ( ps , th , et ) <-> hadd ( ch , ta , ze ) ) ) $=
      ( wxo whad xorbi12d df-had 3bitr4g ) ABDKZFKCEKZGKBDFLCEGLAPQFGABCDEHIMJM
      BDFNCEGNO $.

    $( Equality theorem for adder carry.  (Contributed by Mario Carneiro,
       4-Sep-2016.) $)
    cadbi123d $p |- ( ph ->
      ( cadd ( ps , th , et ) <-> cadd ( ch , ta , ze ) ) ) $=
      ( wa wxo wo wcad anbi12d xorbi12d orbi12d df-cad 3bitr4g ) ABDKZFBDLZKZMC
      EKZGCELZKZMBDFNCEGNATUCUBUEABCDEHIOAFGUAUDJABCDEHIPOQBDFRCEGRS $.
  $}

  ${
    hadbii.1 $e |- ( ph <-> ps ) $.
    hadbii.2 $e |- ( ch <-> th ) $.
    hadbii.3 $e |- ( ta <-> et ) $.
    $( Equality theorem for half adder.  (Contributed by Mario Carneiro,
       4-Sep-2016.) $)
    hadbi123i $p |- ( hadd ( ph , ch , ta ) <-> hadd ( ps , th , et ) ) $=
      ( whad wb wtru a1i hadbi123d trud ) ACEJBDFJKLABCDEFABKLGMCDKLHMEFKLIMNO
      $.

    $( Equality theorem for adder carry.  (Contributed by Mario Carneiro,
       4-Sep-2016.) $)
    cadbi123i $p |- ( cadd ( ph , ch , ta ) <-> cadd ( ps , th , et ) ) $=
      ( wcad wb wtru a1i cadbi123d trud ) ACEJBDFJKLABCDEFABKLGMCDKLHMEFKLIMNO
      $.
  $}

  $( Associative law for triple XOR. (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  hadass $p |- ( hadd ( ph , ps , ch ) <-> ( ph \/_ ( ps \/_ ch ) ) ) $=
    ( whad wxo df-had xorass bitri ) ABCDABECEABCEEABCFABCGH $.

  $( The half adder is the same as the triple biconditional.  (Contributed by
     Mario Carneiro, 4-Sep-2016.) $)
  hadbi $p |- ( hadd ( ph , ps , ch ) <-> ( ( ph <-> ps ) <-> ch ) ) $=
    ( wxo wb wn whad df-xor df-had xnor bibi1i nbbn bitri 3bitr4i ) ABDZCDOCEFZ
    ABCGABEZCEZOCHABCIROFZCEPQSCABJKOCLMN $.

  $( Commutative law for triple XOR. (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  hadcoma $p |- ( hadd ( ph , ps , ch ) <-> hadd ( ps , ph , ch ) ) $=
    ( wxo whad xorcom biid xorbi12i df-had 3bitr4i ) ABDZCDBADZCDABCEBACEKLCCAB
    FCGHABCIBACIJ $.

  $( Commutative law for triple XOR. (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  hadcomb $p |- ( hadd ( ph , ps , ch ) <-> hadd ( ph , ch , ps ) ) $=
    ( wxo whad biid xorcom xorbi12i hadass 3bitr4i ) ABCDZDACBDZDABCEACBEAAKLAF
    BCGHABCIACBIJ $.

  $( Rotation law for triple XOR. (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  hadrot $p |- ( hadd ( ph , ps , ch ) <-> hadd ( ps , ch , ph ) ) $=
    ( whad hadcoma hadcomb bitri ) ABCDBACDBCADABCEBACFG $.

  $( Write the adder carry in disjunctive normal form.  (Contributed by Mario
     Carneiro, 4-Sep-2016.) $)
  cador $p |- ( cadd ( ph , ps , ch ) <->
    ( ( ph /\ ps ) \/ ( ph /\ ch ) \/ ( ps /\ ch ) ) ) $=
    ( wcad wa wxo wo df-cad wn wi xor2 rbaib anbi1d ancom andir 3bitr3g pm5.74i
    w3o df-or bitri 3orass 3bitr4i ) ABCDABEZCABFZEZGZUCACEZBCEZRZABCHUCIZUEJUJ
    UGUHGZJZUFUIUJUEUKUJUDCEABGZCEUEUKUJUDUMCUDUMUJABKLMUDCNABCOPQUCUESUIUCUKGU
    LUCUGUHUAUCUKSTUBT $.

  $( Write the adder carry in conjunctive normal form.  (Contributed by Mario
     Carneiro, 4-Sep-2016.)  (Proof shortened by Wolf Lammen, 25-Sep-2018.) $)
  cadan $p |- ( cadd ( ph , ps , ch ) <->
    ( ( ph \/ ps ) /\ ( ph \/ ch ) /\ ( ps \/ ch ) ) ) $=
    ( wcad wo wa w3a df-3or cador andi orbi1i 3bitr4i ordir ordi orcom wi simpl
    w3o wb bitr4i orcd pm4.72 mpbi anbi12i 3bitri df-3an ) ABCDZABEZACEZFZBCEZF
    ZUHUIUKGUGAUKFZBCFZEZAUNEZUKUNEZFULABFZACFZUNRURUSEZUNEUGUOURUSUNHABCIUMUTU
    NABCJKLAUKUNMUPUJUQUKABCNUQUNUKEZUKUKUNOUNUKPUKVASUNBCBCQUAUNUKUBUCTUDUEUHU
    IUKUFT $.

  $( The half adder distributes over negation.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  hadnot $p |- ( -. hadd ( ph , ps , ch ) <->
    hadd ( -. ph , -. ps , -. ch ) ) $=
    ( wxo wn whad xorneg biid xorbi12i xorneg2 bitr2i df-had notbii 3bitr4i ) A
    BDZCDZEZAEZBEZDZCEZDZABCFZERSUAFUBOUADQTOUAUAABGUAHIOCJKUCPABCLMRSUALN $.

  $( The adder carry distributes over negation.  (Contributed by Mario
     Carneiro, 4-Sep-2016.) $)
  cadnot $p |- ( -. cadd ( ph , ps , ch ) <->
    cadd ( -. ph , -. ps , -. ch ) ) $=
    ( wa w3o wn wo wcad 3ioran ianor 3anbi123i bitri cador notbii cadan 3bitr4i
    w3a ) ABDZACDZBCDZEZFZAFZBFZGZUCCFZGZUDUFGZQZABCHZFUCUDUFHUBRFZSFZTFZQUIRST
    IUKUEULUGUMUHABJACJBCJKLUJUAABCMNUCUDUFOP $.

  $( Commutative law for adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  cadcoma $p |- ( cadd ( ph , ps , ch ) <-> cadd ( ps , ph , ch ) ) $=
    ( wa wxo wo wcad ancom xorcom anbi2i orbi12i df-cad 3bitr4i ) ABDZCABEZDZFB
    ADZCBAEZDZFABCGBACGNQPSABHORCABIJKABCLBACLM $.

  $( Commutative law for adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  cadcomb $p |- ( cadd ( ph , ps , ch ) <-> cadd ( ph , ch , ps ) ) $=
    ( wa w3o wcad 3orcoma biid ancom 3orbi123i bitri cador 3bitr4i ) ABDZACDZBC
    DZEZONCBDZEZABCFACBFQONPESNOPGOONNPROHNHBCIJKABCLACBLM $.

  $( Rotation law for adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  cadrot $p |- ( cadd ( ph , ps , ch ) <-> cadd ( ps , ch , ph ) ) $=
    ( wcad cadcoma cadcomb bitri ) ABCDBACDBCADABCEBACFG $.

  $( If one parameter is true, the adder carry is true exactly when at least
     one of the other parameters is true.  (Contributed by Mario Carneiro,
     8-Sep-2016.) $)
  cad1 $p |- ( ch -> ( cadd ( ph , ps , ch ) <-> ( ph \/ ps ) ) ) $=
    ( wa wxo wo wcad ibar bicomd orbi2d df-cad wn pm5.63 olc orc adantr id jaoi
    impbii xor2 ancom bitri orbi2i 3bitr4i 3bitr4g ) CABDZCABEZDZFUFUGFZABCGABF
    ZCUHUGUFCUGUHCUGHIJABCKUFUJFZUFUFLZUJDZFUJUIUFUJMUJUKUJUFNUFUJUJAUJBABOPUJQ
    RSUGUMUFUGUJULDUMABTUJULUAUBUCUDUE $.

  $( If two parameters are true, the adder carry is true.  (Contributed by
     Mario Carneiro, 4-Sep-2016.) $)
  cad11 $p |- ( ( ph /\ ps ) -> cadd ( ph , ps , ch ) ) $=
    ( wa wxo wo wcad orc df-cad sylibr ) ABDZKCABEDZFABCGKLHABCIJ $.

  $( If one parameter is false, the adder carry is true exactly when both of
     the other two parameters are true.  (Contributed by Mario Carneiro,
     8-Sep-2016.) $)
  cad0 $p |- ( -. ch -> ( cadd ( ph , ps , ch ) <-> ( ph /\ ps ) ) ) $=
    ( wcad wa wxo wo wn df-cad idd pm2.21 adantrd jaod orc impbid1 syl5bb ) ABC
    DABEZCABFZEZGZCHZQABCIUATQUAQQSUAQJUACQRCQKLMQSNOP $.

  $( Rotation law for adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  cadtru $p |- cadd ( T. , T. , ph ) $=
    ( wtru wcad tru cad11 mp2an ) BBBBACDDBBAEF $.

  $( If the first parameter is true, the half adder is equivalent to the
     equality of the other two inputs.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  had1 $p |- ( ph -> ( hadd ( ph , ps , ch ) <-> ( ps <-> ch ) ) ) $=
    ( whad wb hadbi biass bitri id biidd 2thd sylibr syl5bb ) ABCDZABCEZEZAONAB
    ECEPABCFABCGHAAOOEZEPOEAAQAIAOJKAOOGLM $.

  $( If the first parameter is false, the half adder is equivalent to the XOR
     of the other two inputs.  (Contributed by Mario Carneiro, 4-Sep-2016.) $)
  had0 $p |- ( -. ph -> ( hadd ( ph , ps , ch ) <-> ( ps \/_ ch ) ) ) $=
    ( wn whad wxo wb had1 hadnot df-xor xorneg bitr3i con1bii 3bitr4g con4bid )
    ADZABCEZBCFZPPBDZCDZESTGZQDRDPSTHABCIUARUADSTFRSTJBCKLMNO $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
      Other axiomatizations of classical propositional calculus
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Derive the Lukasiewicz axioms from Meredith's sole axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Carew Meredith's sole axiom for propositional calculus.  This amazing
     formula is thought to be the shortest possible single axiom for
     propositional calculus with inference rule ~ ax-mp , where negation and
     implication are primitive.  Here we prove Meredith's axiom from ~ ax-1 ,
     ~ ax-2 , and ~ ax-3 .  Then from it we derive the Lukasiewicz axioms
     ~ luk-1 , ~ luk-2 , and ~ luk-3 .  Using these we finally re-derive our
     axioms as ~ ax1 , ~ ax2 , and ~ ax3 , thus proving the equivalence of all
     three systems.  C. A. Meredith, ""Single Axioms for the Systems (C,N),
     (C,O) and (A,N) of the Two-Valued Propositional Calculus,"" _The Journal of
     Computing Systems_ vol. 1 (1953), pp. 155-164.  Meredith claimed to be
     close to a proof that this axiom is the shortest possible, but the proof
     was apparently never completed.

     An obscure Irish lecturer, Meredith (1904-1976) became enamored with logic
     somewhat late in life after attending talks by Lukasiewicz and produced
     many remarkable results such as this axiom.  From his obituary:  ""He did
     logic whenever time and opportunity presented themselves, and he did it on
     whatever materials came to hand: in a pub, his favored pint of porter
     within reach, he would use the inside of cigarette packs to write proofs
     for logical colleagues.""  (Contributed by NM, 14-Dec-2002.)  (Proof
     shortened by Andrew Salmon, 25-Jul-2011.)  (Proof shortened by Wolf
     Lammen, 28-May-2013.) $)
  meredith $p |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) ->
       ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $=
    ( wi wn pm2.21 ax-3 imim12i com13 con1d com12 a1d ax-1 imim1d ja ) ABFZCGDG
    FZFZCFZEEAFZDAFZFUAGZUCUBDUDADAUATAGZDCUERSDCFABHCDIJKLMNEDEAEDOPQ $.

  $( Alias for ~ meredith which ""verify markup *"" will match to
     ~ ax-meredith .  (Contributed by NM, 21-Aug-2017.)
     (New usage is discouraged.) $)
  axmeredith $p |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) ->
       ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $=
    ( meredith ) ABCDEF $.

  $( Theorem ~ meredith restated as an axiom.  This will allow us to ensure
     that the rederivation of ~ ax1 , ~ ax2 , and ~ ax3 below depend only on
     Meredith's sole axiom and not accidentally on a previous theorem above.
     Outside of this section, we will not make use of this axiom.  (Contributed
     by NM, 14-Dec-2002.)  (New usage is discouraged.) $)
  ax-meredith $a |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) ->
       ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $.
  $( $j restatement 'ax-meredith' of 'axmeredith'; $)

  $( Step 3 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (The step numbers refer to Meredith's original paper.)  (Contributed by
     NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem1 $p |- ( ( ( ch -> ( -. ph -> ps ) ) -> ta ) -> ( ph -> ta ) ) $=
    ( wn wi ax-meredith ax-mp ) DAEZFIBFZEZIFFZJFCJFZFZMDFADFFJDECEFZEKEFZFOFDF
    LFNIBOKDGJPDCLGHDIJAMGH $.

  $( Step 4 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem2 $p |- ( ( ( ph -> ph ) -> ch ) -> ( th -> ch ) ) $=
    ( wi wn merlem1 ax-meredith ax-mp ) BBDZAECEZDDADAADZDKBDCBDDAJIAFBBACKGH
    $.

  $( Step 7 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem3 $p |- ( ( ( ps -> ch ) -> ph ) -> ( ch -> ph ) ) $=
    ( wi wn merlem2 ax-mp ax-meredith ) AADZCEZJDZDZCDBCDZDZMADCADZDOBEZPDDBDZL
    DZNKKDLDRJKIFKLQFGCABBLHGAACCMHG $.

  $( Step 8 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem4 $p |- ( ta -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $=
    ( wi wn ax-meredith merlem3 ax-mp ) AADBEZIDDBDZCDCADBADDZDCKDAABBCFKJCGH
    $.

  $( Step 11 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem5 $p |- ( ( ph -> ps ) -> ( -. -. ph -> ps ) ) $=
    ( wi wn ax-meredith merlem1 merlem4 ax-mp ) BBCZBDZJCCBCBCIICCZABCZADZDZBCC
    ZBBBBBEIJNDCCBCZACZOCZKOCZBBBNAEOKDZCMTCCZACQCZRSCUAUBMBLTFAPUAGHOTAKQEHHH
    $.

  $( Step 12 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem6 $p |- ( ch -> ( ( ( ps -> ch ) -> ph ) -> ( th -> ph ) ) ) $=
    ( wi merlem4 merlem3 ax-mp ) BCEZIAEDAEEZECJEADIFJBCGH $.

  $( Between steps 14 and 15 of Meredith's proof of Lukasiewicz axioms from his
     sole axiom.  (Contributed by NM, 22-Dec-2002.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merlem7 $p |- ( ph -> ( ( ( ps -> ch ) -> th ) -> ( ( ( ch -> ta ) ->
                  ( -. th -> -. ps ) ) -> th ) ) ) $=
    ( wi wn merlem4 merlem6 ax-meredith ax-mp ) BCFZLDFZCEFDGBGFFZDFZFZFZAPFZDN
    LHPAGZFCGZSFFZCFLFZQRFOUAFUBSMOTICEDBUAJKPSCALJKK $.

  $( Step 15 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem8 $p |- ( ( ( ps -> ch ) -> th ) -> ( ( ( ch -> ta ) ->
                  ( -. th -> -. ps ) ) -> th ) ) $=
    ( wph wi wn ax-meredith merlem7 ax-mp ) EEFZEGZLFFEFEFKKFFZABFCFBDFCGAGFFCF
    FEEEEEHMABCDIJ $.

  $( Step 18 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem9 $p |- ( ( ( ph -> ps ) -> ( ch -> ( th -> ( ps -> ta ) ) ) ) ->
                    ( et -> ( ch -> ( th -> ( ps -> ta ) ) ) ) ) $=
    ( wi wn merlem6 merlem8 ax-mp ax-meredith ) CDBEGZGZGZFHZGBHZPGGZBGABGZGZSO
    GFOGGMRHDHGZHAHGZGUAGRGZTNRGUCPCNQIDMRUBJKBEUAARLKOPBFSLK $.

  $( Step 19 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem10 $p |- ( ( ph -> ( ph -> ps ) ) -> ( th -> ( ph -> ps ) ) ) $=
    ( wi wn ax-meredith merlem9 ax-mp ) AADZAEZJDDADADIIDDZAABDZDZCLDDZAAAAAFLA
    DJCEDDADZADNDKNDLAACAFOAMCBKGHH $.

  $( Step 20 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem11 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wi wn ax-meredith merlem10 ax-mp ) AACZADZICCACACHHCCZAABCZCZKCZAAAAAELMC
    JMCABLFLKJFGG $.

  $( Step 28 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem12 $p |- ( ( ( th -> ( -. -. ch -> ch ) ) -> ph ) -> ph ) $=
    ( wn wi merlem5 merlem2 ax-mp merlem4 merlem11 ) CBDDBEZEZAEZMAEZEZNLOBBEKE
    LBBFBKCGHAMLIHMAJH $.

  $( Step 35 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem13 $p |- ( ( ph -> ps ) ->
              ( ( ( th -> ( -. -. ch -> ch ) ) -> -. -. ph ) -> ps ) ) $=
    ( wi wn merlem12 merlem5 ax-mp merlem6 ax-meredith merlem11 ) BBEZAFZDCFFCE
    EZNFZEZFZEZEAEZAEZABEQBEETUAEZUASUBOREZREZSRCDGRBEZRFPEZEREUCEZUDSEUFUGQPEU
    FPCDGQPHIRUEUFOJIRBRNUCKIIAMSTJITALIBBAQAKI $.

  $( 1 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom.  (Contributed by NM, 14-Dec-2002.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  luk-1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wi wn ax-meredith merlem13 ax-mp ) CCDZAEZEZEJDDKDBDZBCDACDDZDZABDZMDZCCK
    ABFMADZOEZEZERDDSDLDZNPDOLDTABJIGOLRQGHMASOLFHH $.

  $( 2 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom.  (Contributed by NM, 14-Dec-2002.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  luk-2 $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wn wi merlem5 merlem4 ax-mp merlem11 ax-meredith ) ABZACZJACZCZKAJBZCIBMC
    CZICZICZLOPCZPNQAMDIONEFOIGFAMIJIHFJAGF $.

  $( 3 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom.  (Contributed by NM, 14-Dec-2002.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  luk-3 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wn wi merlem11 merlem1 ax-mp ) ACZHBDZDIDAIDHBEABHIFG $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Derive the standard axioms from the Lukasiewicz axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    luklem1.1 $e |- ( ph -> ps ) $.
    luklem1.2 $e |- ( ps -> ch ) $.
    $( Used to rederive standard propositional axioms from Lukasiewicz'.
       (Contributed by NM, 23-Dec-2002.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    luklem1 $p |- ( ph -> ch ) $=
      ( wi luk-1 ax-mp ) BCFZACFZEABFIJFDABCGHH $.
  $}

  $( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  luklem2 $p |- ( ( ph -> -. ps ) ->
                ( ( ( ph -> ch ) -> th ) -> ( ps -> th ) ) ) $=
    ( wn wi luk-1 luk-3 ax-mp luklem1 ) ABEZFZBACFZFZMDFBDFFLKCFZMFZNAKCGBOFPNF
    BCHBOMGIJBMDGJ $.

  $( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  luklem3 $p |- ( ph -> ( ( ( -. ph -> ps ) -> ch ) -> ( th -> ch ) ) ) $=
    ( wn wi luk-3 luklem2 luklem1 ) AAEZDEZFJBFCFDCFFAKGJDBCHI $.

  $( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  luklem4 $p |- ( ( ( ( -. ph -> ph ) -> ph ) -> ps ) -> ps ) $=
    ( wn wi luk-2 luklem3 ax-mp luk-1 luklem1 ) ACADADZBDZBCZBDZBLJDZKMDJCJDJDZ
    NJEJONDAEJJJLFGGLJBHGBEI $.

  $( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  luklem5 $p |- ( ph -> ( ps -> ph ) ) $=
    ( wn wi luklem3 luklem4 luklem1 ) AACADADBADZDHAAABEAHFG $.

  $( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  luklem6 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wi luk-1 wn luklem5 luklem2 luklem4 luklem1 ax-mp ) AABCZCKBCZKCZKAKBDKEZ
    KCZKCMKCZCZPMOCZQNLCRNBEZNCZLNSFTSBCBCLCLSKBBGBLHIINLKDJMOKDJKPHJI $.

  $( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  luklem7 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi luk-1 luklem5 luklem1 luklem6 ax-mp ) ABCDZDJCDZACDZDZBLDZAJCEBKDMNDBJ
    KDZKBJBDOBJFJBCEGJCHGBKLEIG $.

  $( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  luklem8 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
    ( wi luk-1 luklem7 ax-mp ) CADZABDZCBDZDDIHJDDCABEHIJFG $.

  $( Standard propositional axiom derived from Lukasiewicz axioms.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax1 $p |- ( ph -> ( ps -> ph ) ) $=
    ( luklem5 ) ABC $.

  $( Standard propositional axiom derived from Lukasiewicz axioms.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax2 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $=
    ( wi luklem7 luklem8 luklem6 ax-mp luklem1 ) ABCDDBACDZDZABDZJDZABCEKLAJDZD
    ZMBJAFNJDOMDACGNJLFHII $.

  $( Standard propositional axiom derived from Lukasiewicz axioms.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax3 $p |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $=
    ( wn wi luklem2 luklem4 luklem1 ) ACZBCDHADADBADZDIHBAAEAIFG $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           Derive Nicod's axiom from the standard axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

Prove Nicod's axiom and implication and negation definitions.

$)

  $( Define implication in terms of 'nand'.  Analogous to
     ` ( ( ph -/\ ( ps -/\ ps ) ) <-> ( ph -> ps ) ) ` .  In a pure
     (standalone) treatment of Nicod's axiom, this theorem would be changed to
     a definition ($a statement).  (Contributed by NM, 11-Dec-2008.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nic-dfim $p |- ( ( ( ph -/\ ( ps -/\ ps ) ) -/\ ( ph -> ps ) ) -/\
                   ( ( ( ph -/\ ( ps -/\ ps ) ) -/\ ( ph -/\ ( ps -/\ ps ) ) )
                          -/\
                     ( ( ph -> ps ) -/\ ( ph -> ps ) ) ) ) $=
    ( wnan wi wb nanim bicomi nanbi mpbi ) ABBCCZABDZEJKCJJCKKCCCKJABFGJKHI $.

  $( Define negation in terms of 'nand'.  Analogous to
     ` ( ( ph -/\ ph ) <-> -. ph ) ` .  In a pure (standalone) treatment of
     Nicod's axiom, this theorem would be changed to a definition ($a
     statement).  (Contributed by NM, 11-Dec-2008.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nic-dfneg $p |- ( ( ( ph -/\ ph ) -/\ -. ph ) -/\
                    ( ( ( ph -/\ ph ) -/\ ( ph -/\ ph ) ) -/\
                      ( -. ph -/\ -. ph ) ) ) $=
    ( wnan wn wb nannot bicomi nanbi mpbi ) AABZACZDIJBIIBJJBBBJIAEFIJGH $.

  ${
    $( Minor premise. $)
    nic-jmin $e |- ph $.
    $( Major premise. $)
    nic-jmaj $e |- ( ph -/\ ( ch -/\ ps ) ) $.
    $( Derive Nicod's rule of modus ponens using 'nand', from the standard
       one.  Although the major and minor premise together also imply ` ch ` ,
       this form is necessary for useful derivations from ~ nic-ax .  In a pure
       (standalone) treatment of Nicod's axiom, this theorem would be changed
       to an axiom ($a statement).  (Contributed by Jeff Hoffman,
       19-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-mp $p |- ps $=
      ( wnan wa wi nannan mpbi simprd ax-mp ) ABDACBACBFFACBGHEABCIJKL $.

    $( A direct proof of ~ nic-mp .  (Contributed by NM, 30-Dec-2008.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    nic-mpALT $p |- ps $=
      ( wa wi wn wnan df-nan anbi2i xchbinx mpbi iman mpbir simprd ax-mp ) ABDA
      CBACBFZGARHZFZHZACBIZIZUAEUCAUBFTAUBJUBSACBJKLMARNOPQ $.
  $}

  $( Nicod's axiom derived from the standard ones.  See _Introduction to
     Mathematical Philosophy_ by B. Russell, p. 152.  Like ~ meredith , the
     usual axioms can be derived from this and vice versa.  Unlike ~ meredith ,
     Nicod uses a different connective ('nand'), so another form of modus
     ponens must be used in proofs, e.g. ` { ` ~ nic-ax , ~ nic-mp ` } ` is
     equivalent to ` { ` ~ luk-1 , ~ luk-2 , ~ luk-3 , ~ ax-mp ` } ` .  In a
     pure (standalone) treatment of Nicod's axiom, this theorem would be
     changed to an axiom ($a statement).  (Contributed by Jeff Hoffman,
     19-Nov-2007.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  nic-ax $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\
                   ( ( ta -/\ ( ta -/\ ta ) ) -/\
                     ( ( th -/\ ch ) -/\
                       ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $=
    ( wnan wa wi nannan biimpi simpl imim2i wn imnan df-nan bitr4i imim2d con2b
    con3 mpbir 3bitr4ri syl6ibr syl5bir nanim sylib 3syl pm4.24 jctil ) ACBFFZE
    EEFFZDCFZADFZULFFZFFUIUJUMGHUIUMUJUIACBGZHZACHZUMUIUOABCIJUNCACBKLUPUKULHUM
    UKDCMZHZUPULURDCGMUKDCNDCOPUPURDAMZHZULUPUQUSDACSQADMHADGMUTULADNDARADOUAUB
    UCUKULUDUEUFUJEEEGZHEVAEUGJEEEITUHUIUMUJIT $.

  $( A direct proof of ~ nic-ax .  (Contributed by NM, 11-Dec-2008.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nic-axALT $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\ ( ( ta -/\ ( ta -/\ ta ) )
          -/\ ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $=
    ( wnan wa wn anidm df-nan anbi2i notbii iman 3bitr4i bitr4i xchbinx anbi12i
    wi imnan mpbir simpl imim2i con3 imim2d biimpri jctil con2b bitr3i 3bitri
    syl ) ACBFZFZEEEFZFZDCFZADFZUPFZFZFZFULUSGZHZVAACBGZRZEEEGZRZDCHZRZDAHZRZRZ
    GZRZVCVJVEVCACRZVJVBCACBUAUBVMVFVHDACUCUDUJVDEEIUEUFVAVCVKHZGZHVLUTVOULVCUS
    VNAUKGZHAVBHZGZHULVCVPVRUKVQACBJKLAUKJAVBMNUSUNURGVKUNURJUNVEURVJEUMGZHEVDH
    ZGZHUNVEVSWAUMVTEEEJKLEUMJEVDMNUOUQGZHVGVIHZGZHURVJWBWDUOVGUQWCUODCGHVGDCJD
    CSOUQUPUPGZVIUPUPJWEUPADGHZVIUPIADJWFADHRVIADSADUGUHUIPQLUOUQJVGVIMNQPQLVCV
    KMOTULUSJT $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Derive the Lukasiewicz axioms from Nicod's axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $( Minor premise. $)
    nic-imp.1 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
    $( Inference for ~ nic-mp using ~ nic-ax as major premise.  (Contributed by
       Jeff Hoffman, 17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-imp $p |- ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) $=
      ( wta wnan nic-ax nic-mp ) ACBGGDCGADGZJGGFFFGGEABCDFHI $.
  $}

  $( Lemma for ~ nic-id .  (Contributed by Jeff Hoffman, 17-Nov-2007.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nic-idlem1 $p |- ( ( th -/\ ( ta -/\ ( ta -/\ ta ) ) ) -/\
                 ( ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) -/\
                   ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) ) ) $=
    ( wnan nic-ax nic-imp ) ACBFFACFAAFZIFFEEEFFDABCAEGH $.

  ${
    nic-idlem2.1 $e |- ( et -/\ ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) ) $.
    $( Lemma for ~ nic-id .  Inference used by ~ nic-id .  (Contributed by Jeff
       Hoffman, 17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-idlem2 $p |- ( ( th -/\ ( ta -/\ ( ta -/\ ta ) ) ) -/\ et ) $=
      ( wnan nic-ax nic-imp nic-mp ) FACBHHZDHZHDEEEHHZHZFHZPGOMMFLACHAAHZQHHND
      ABCAEIJJK $.
  $}

  $( Theorem ~ id expressed with ` -/\ ` .  (Contributed by Jeff Hoffman,
     17-Nov-2007.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  nic-id $p |- ( ta -/\ ( ta -/\ ta ) ) $=
    ( wph wps wch wth wnan nic-ax nic-idlem2 nic-idlem1 nic-mp ) BCFZCBFZLFFZDD
    DFZFZFZCCCFFZFAAAFFZOEEEMDQCCCBEGHMNDPCORFKLLOAIHJ $.

  $( ` -/\ ` is symmetric.  (Contributed by Jeff Hoffman, 17-Nov-2007.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nic-swap $p |- ( ( th -/\ ph ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) $=
    ( wta wnan nic-id nic-ax nic-mp ) AAADDBADABDZHDDCCCDDAEAAABCFG $.

  ${
    nic-isw1.1 $e |- ( th -/\ ph ) $.
    $( Inference version of ~ nic-swap .  (Contributed by Jeff Hoffman,
       17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-isw1 $p |- ( ph -/\ th ) $=
      ( wnan nic-swap nic-mp ) BADABDZGCABEF $.
  $}

  ${
    nic-isw2.1 $e |- ( ps -/\ ( th -/\ ph ) ) $.
    $( Inference for swapping nested terms.  (Contributed by Jeff Hoffman,
       17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-isw2 $p |- ( ps -/\ ( ph -/\ th ) ) $=
      ( wnan nic-swap nic-imp nic-mp nic-isw1 ) BACEZBCAEZEJBEZLDJKKBCAFGHI $.
  $}

  ${
    nic-iimp1.1 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
    nic-iimp1.2 $e |- ( th -/\ ch ) $.
    $( Inference version of ~ nic-imp using right-handed term.  (Contributed by
       Jeff Hoffman, 17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-iimp1 $p |- ( th -/\ ph ) $=
      ( wnan nic-imp nic-mp nic-isw1 ) DADCGADGZKFABCDEHIJ $.
  $}

  ${
    nic-iimp2.1 $e |- ( ( ph -/\ ps ) -/\ ( ch -/\ ch ) ) $.
    nic-iimp2.2 $e |- ( th -/\ ph ) $.
    $( Inference version of ~ nic-imp using left-handed term.  (Contributed by
       Jeff Hoffman, 17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-iimp2 $p |- ( th -/\ ( ch -/\ ch ) ) $=
      ( wnan nic-isw1 nic-iimp1 ) CCGZBADJABGEHFI $.
  $}

  ${
    nic-idel.1 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
    $( Inference to remove the trailing term.  (Contributed by Jeff Hoffman,
       17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-idel $p |- ( ph -/\ ( ch -/\ ch ) ) $=
      ( wnan nic-id nic-isw1 nic-imp nic-mp ) CCEZCEAJEZKJCCFGABCJDHI $.
  $}

  ${
    nic-ich.1 $e |- ( ph -/\ ( ps -/\ ps ) ) $.
    nic-ich.2 $e |- ( ps -/\ ( ch -/\ ch ) ) $.
    $( Chained inference.  (Contributed by Jeff Hoffman, 17-Nov-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    nic-ich $p |- ( ph -/\ ( ch -/\ ch ) ) $=
      ( wnan nic-isw1 nic-imp nic-mp ) CCFZBFAJFZKJBEGABBJDHI $.
  $}

  ${
    nic-idbl.1 $e |- ( ph -/\ ( ps -/\ ps ) ) $.
    $( Double the terms.  Since doubling is the same as negation, this can be
       viewed as a contraposition inference.  (Contributed by Jeff Hoffman,
       17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-idbl $p |- ( ( ps -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ph -/\ ph ) ) ) $=
      ( wnan nic-imp nic-ich ) BBDABDAADABBBCEABBACEF $.
  $}

$( (not in Table of Contents)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Biconditional justification from Nicod's axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( For nic-* definitions, the biconditional connective is not used.  Instead,
     definitions are made based on this form. ~ nic-bi1 and ~ nic-bi2 are used
     to convert the definitions into usable theorems about one side of the
     implication.  (Contributed by Jeff Hoffman, 18-Nov-2007.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nic-bijust $p |- ( ( ta -/\ ta ) -/\ ( ( ta -/\ ta ) -/\ ( ta -/\ ta ) ) ) $=
    ( nic-swap ) AAB $.

  ${
    $( 'Biconditional' premise. $)
    nic-bi1.1 $e |- ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph )
         -/\ ( ps -/\ ps ) ) ) $.
    $( Inference to extract one side of an implication from a definition.
       (Contributed by Jeff Hoffman, 18-Nov-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    nic-bi1 $p |- ( ph -/\ ( ps -/\ ps ) ) $=
      ( wnan nic-id nic-iimp1 nic-isw2 nic-idel ) AABBAAABDBBDAADACAEFGH $.
  $}

  ${
    $( 'Biconditional' premise.  $)
    nic-bi2.1 $e |- ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph )
         -/\ ( ps -/\ ps ) ) ) $.
    $( Inference to extract the other side of an implication from a
       'biconditional' definition.  (Contributed by Jeff Hoffman,
       18-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-bi2 $p |- ( ps -/\ ( ph -/\ ph ) ) $=
      ( wnan nic-isw2 nic-id nic-iimp1 nic-idel ) BBAABDZAADZBBDZBKIJCEBFGH $.
  $}

$( (not in Table of Contents)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
             Prove the Lukasiewicz axioms from Nicod's axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $( Minor premise. $)
    nic-smin $e |- ph $.
    $( Major premise. $)
    nic-smaj $e |- ( ph -> ps ) $.
    $( Derive the standard modus ponens from ~ nic-mp .  (Contributed by Jeff
       Hoffman, 18-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-stdmp $p |- ps $=
      ( wi wnan nic-dfim nic-bi2 nic-mp ) ABBCABEZABBFFZKDKJABGHII $.
  $}

  $( Proof of ~ luk-1 from ~ nic-ax and ~ nic-mp (and definitions ~ nic-dfim
     and ~ nic-dfneg ).  Note that the standard axioms ~ ax-1 , ~ ax-2 , and
     ~ ax-3 are proved from the Lukasiewicz axioms by theorems ~ ax1 , ~ ax2 ,
     and ~ ax3 .  (Contributed by Jeff Hoffman, 18-Nov-2007.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nic-luk1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wta wi nic-dfim nic-bi2 nic-ax nic-isw2 nic-idel nic-bi1 nic-idbl nic-imp
    wnan nic-swap nic-ich nic-mp ) ABEZBCEZACEZEZUANNZRUAEZUCRABBNNZUAUDRABFGUD
    STTNZNZUAUDCCNZBNZAUGNZUINZNZUFUDDDDNNZUKUKUDULABBUGDHIJUKUEUHNUFUEUJUJUHUI
    TUITACFKLMSUHUHUESBUGNZUHUMSBCFGUGBOPMPPUFUASTFKPPUBUCRUAFKQ $.

  $( Proof of ~ luk-2 from ~ nic-ax and ~ nic-mp .  (Contributed by Jeff
     Hoffman, 18-Nov-2007.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  nic-luk2 $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wn wi wnan nic-dfim nic-bi2 nic-dfneg nic-iimp1 nic-isw2 nic-isw1 nic-bi1
    nic-id nic-mp ) ABZACZAADZDZOACZROPONPDZSPSONAEFNPPPNDNNDPPDPAGPLHIHJQROAEK
    M $.

  $( Proof of ~ luk-3 from ~ nic-ax and ~ nic-mp .  (Contributed by Jeff
     Hoffman, 18-Nov-2007.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  nic-luk3 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wnan nic-dfim nic-bi1 nic-dfneg nic-bi2 nic-id nic-iimp1 nic-iimp2 nic-mp
    wn wi ) AALZBMZOCCZAOMZQNBBCZOANRCONBDENAACZSASNAFGAHIJPQAODEK $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Derive Nicod's Axiom from Lukasiewicz's First Sheffer Stroke Axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( This alternative axiom for propositional calculus using the Sheffer Stroke
     was offered by Lukasiewicz in his Selected Works.  It improves on Nicod's
     axiom by reducing its number of variables by one.

     This axiom also uses ~ nic-mp for its constructions.

     Here, the axiom is proved as a substitution instance of ~ nic-ax .
     (Contributed by Anthony Hart, 31-Jul-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  lukshef-ax1 $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\ ( ( th -/\ ( th -/\ th ) )
          -/\ ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $=
    ( nic-ax ) ABCDDE $.

  $( Lemma for ~ renicax .  (Contributed by NM, 31-Jul-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  lukshefth1 $p |- ( ( ( ( ta -/\ ps ) -/\ ( ( ph -/\ ta ) -/\ ( ph
          -/\ ta ) ) ) -/\ ( th -/\ ( th -/\ th ) ) ) -/\ ( ph -/\ ( ps
          -/\ ch ) ) ) $=
    ( wnan lukshef-ax1 nic-mp ) ABCFFZEEEFFZEBFAEFZKFFZFZFZLDDDFFZFZIFZQACBEGPM
    MFFZNQQFFIIIFFJODEFEDFZSFFZFFRLLLFFEEEDGJTOLGHPMMIGHH $.

  $( Lemma for ~ renicax .  (Contributed by NM, 31-Jul-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  lukshefth2 $p |- ( ( ta -/\ th ) -/\ ( ( th -/\ ta ) -/\ ( th
          -/\ ta ) ) ) $=
    ( wps wch wph wnan lukshef-ax1 nic-mp lukshefth1 ) AAAFFZBAFABFZKFFBBBFFAJF
    ZCDEFFZAFZNFFZJBEFEBFZPFFZMJADFCAFZRFFZFFOJCEDAGMSJAGHQJFZEEEFFZFZOTFZUCEEE
    ABIOUAENFLEFZUDFFZFFUBUCUCFFTTTFFLNNEGOUEUATGHHHAAABGH $.

  $( A rederivation of ~ nic-ax from ~ lukshef-ax1 , proving that ~ lukshef-ax1
     with ~ nic-mp can be used as a complete axiomatization of propositional
     calculus.  (Contributed by Anthony Hart, 31-Jul-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  renicax $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\ ( ( ta -/\ ( ta -/\ ta ) )
          -/\ ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $=
    ( wnan lukshefth1 lukshefth2 nic-mp lukshef-ax1 ) EEEFFZDCFADFZLFFZFZACBFFZ
    FZONFZQOMKFZFZPPROFSSACBEDGORHINRRFFSPPFFOOOFFMKHNRROJIIONHI $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Derive the Lukasiewicz Axioms from the Tarski-Bernays-Wajsberg Axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Justification for ~ tbw-negdf .  (Contributed by Anthony Hart,
     15-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  tbw-bijust $p |- ( ( ph <-> ps ) <-> ( ( ( ph -> ps )
    -> ( ( ps -> ph ) -> F. ) ) -> F. ) ) $=
    ( wb wi wn wfal dfbi1 pm2.21 imim2i falim impbii notbii ax-1 pm2.43i 3bitri
    id ja ) ABCABDZBADZEZDZERSFDZDZEZUCFDZABGUAUCUAUCTUBRSFHIUBTRSFTTPTJQIKLUDU
    EUCFHUEUDUCFUEUDDZUDUEMUFJQNKO $.

  $( The definition of negation, in terms of ` -> ` and ` F. ` .  (Contributed
     by Anthony Hart, 15-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  tbw-negdf $p |- ( ( ( -. ph -> ( ph -> F. ) )
    -> ( ( ( ph -> F. ) -> -. ph ) -> F. ) ) -> F. ) $=
    ( wn wfal wi wb pm2.21 ax-1 falim ja pm2.43i impbii tbw-bijust mpbi ) ABZAC
    DZENODONDZCDDCDNOACFONACPNOGPHIJKNOLM $.

  $( The first of four axioms in the Tarski-Bernays-Wajsberg system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbw-ax1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( imim1 ) ABCD $.

  $( The second of four axioms in the Tarski-Bernays-Wajsberg system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbw-ax2 $p |- ( ph -> ( ps -> ph ) ) $=
    ( ax-1 ) ABC $.

  $( The third of four axioms in the Tarski-Bernays-Wajsberg system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbw-ax3 $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $=
    ( peirce ) ABC $.

  $( The fourth of four axioms in the Tarski-Bernays-Wajsberg system.

     This axiom was added to the Tarski-Bernays axiom system (see ~ tb-ax1 ,
     ~ tb-ax2 , and ~ tb-ax3 ) by Wajsberg for completeness.  (Contributed by
     Anthony Hart, 13-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  tbw-ax4 $p |- ( F. -> ph ) $=
    ( falim ) AB $.

  ${
    tbwsyl.1 $e |- ( ph -> ps ) $.
    tbwsyl.2 $e |- ( ps -> ch ) $.
    $( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
       (Contributed by Anthony Hart, 16-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    tbwsyl $p |- ( ph -> ch ) $=
      ( wi tbw-ax1 ax-mp ) BCFZACFZEABFIJFDABCGHH $.
  $}

  $( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbwlem1 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi tbw-ax2 tbw-ax1 tbwsyl tbw-ax3 mpsyl ) BBCDZCDZDAJDKACDZDBLDBJKDZKBJBD
    MBJEJBCFGMKCDKDKJKCFKCHGGAJCFBKLFI $.

  $( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbwlem2 $p |- ( ( ph -> ( ps -> F. ) ) -> ( ( ( ph -> ch ) -> th )
    -> ( ps -> th ) ) ) $=
    ( wfal wi tbw-ax4 tbw-ax1 tbwlem1 ax-mp mpsyl tbwsyl ) ABEFZFZBACFZFZODFBDF
    FBMCFZFZNQOFPMBCFZFZRECFZTCGMUASFFUATFBECHMUASIJJMBCIJAMCHBQOHKBODHL $.

  $( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbwlem3 $p |- ( ( ( ( ( ph -> F. ) -> ph ) -> ph ) -> ps ) -> ps ) $=
    ( wfal wi tbw-ax3 tbw-ax2 tbw-ax1 tbwsyl ax-mp ) ACDADADZBDZKBDZDZLJMACEJKJ
    DMJKFKJBGHIMLBDLDLKLBGLBEHI $.

  $( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbwlem4 $p |- ( ( ( ph -> F. ) -> ps ) -> ( ( ps -> F. ) -> ph ) ) $=
    ( wfal wi tbw-ax4 tbw-ax1 tbwlem1 ax-mp tbwlem2 tbwlem3 tbwsyl ) ACDZBDZLBC
    DZCDZDZNADZBODZMPDZNNDZRCCDZTCENUANDDUATDBCCFNUANGHHNBCGHMRPDDRSDLBOFMRPGHH
    PLADADQDQLNAAIAQJKK $.

  $( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbwlem5 $p |- ( ( ( ph -> ( ps -> F. ) ) -> F. ) -> ph ) $=
    ( wfal wi tbw-ax2 tbw-ax1 tbwsyl tbwlem1 ax-mp tbwlem4 ) ACDZABCDZDZDZMCDAD
    AKLDZDNABADOABEBACFGAKLHIAMJI $.

  $( ~ luk-1 derived from the Tarski-Bernays-Wajsberg axioms.  (Contributed by
     Anthony Hart, 16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re1luk1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( tbw-ax1 ) ABCD $.

  $( ~ luk-2 derived from the Tarski-Bernays-Wajsberg axioms.  (Contributed by
     Anthony Hart, 16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re1luk2 $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wn wi wfal tbw-negdf tbw-ax2 tbwlem4 ax-mp tbw-ax1 tbw-ax3 tbwsyl ) ABZAC
    ZADCZACZANLCZMOCLNCZPDCZCZDCZPAERSCTPCRQFPSGHHNLAIHADJK $.

  $( ~ luk-3 derived from the Tarski-Bernays-Wajsberg axioms.

     This theorem, along with ~ re1luk1 and ~ re1luk2 proves that ~ tbw-ax1 ,
     ~ tbw-ax2 , ~ tbw-ax3 , and ~ tbw-ax4 , with ~ ax-mp can be used as a
     complete axiom system for all of propositional calculus.  (Contributed by
     Anthony Hart, 16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re1luk3 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wn wfal wi tbw-negdf tbwlem5 ax-mp tbw-ax4 tbw-ax1 tbwlem1 mpsyl ) ACZADE
    ZEZANBEZMBEONMEZDEEDEOAFOQGHNABEZEZAPEDBEZSBINTREETSEADBJNTRKHHNABKHMNBJL
    $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Derive the Tarski-Bernays-Wajsberg axioms from Meredith's First CO Axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( A single axiom for propositional calculus offered by Meredith.

     This axiom is worthy of note, due to it having only 19 symbols, not
     counting parentheses.  The more well-known ~ meredith has 21 symbols, sans
     parentheses.

     See ~ merco2 for another axiom of equal length.  (Contributed by Anthony
     Hart, 13-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merco1 $p |- ( ( ( ( ( ph -> ps ) -> ( ch -> F. ) ) -> th ) -> ta )
         -> ( ( ta -> ph ) -> ( ch -> ph ) ) ) $=
    ( wi wfal wn ax-1 falim ja imim2i imim1i meredith syl ) ABFZCGFZFZDFZEFPDHZ
    CHZFZFZDFZEFEAFCAFFUDSERUCDQUBPCGUBUATIUBJKLMMABDCENO $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem1 $p |- ( ph -> ( F. -> ch ) ) $=
    ( wfal wi merco1 ax-mp ) AACADZDZDZACBDZDZHGDZHDZIGCDACDZDZGDHDZMGNDZNDZGDO
    DPCAANGEGNAGOEFGCAGHEFHCDZNDZGDLDZMIDQSDHDTDUACAASHEGNHHTEFHCAGLEFFHJDZKDZI
    KDZJCDNDZGDHDZUCRJDUEDUFCAANJEGNAJUEEFJCAGHEFKCDICDZDZJDUBDZUCUDDJUGDSDKDUH
    DUICBISKEJUGHKUHEFKCIJUBEFFF $.

  $( ~ tbw-ax4 rederived from ~ merco1 .  (Contributed by Anthony Hart,
     17-Sep-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  retbwax4 $p |- ( F. -> ph ) $=
    ( wfal wi merco1lem1 ax-mp ) ABACZCZFAADGADE $.

  $( ~ tbw-ax2 rederived from ~ merco1 .  (Contributed by Anthony Hart,
     17-Sep-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  retbwax2 $p |- ( ph -> ( ps -> ph ) ) $=
    ( wi wfal merco1lem1 merco1 ax-mp ) AAAACZCZCZABACZCZDACZHCZICZJHACADCZCACZ
    MCOQAEHAAAMFGIPCPCDCNCOJCAHAPDFIPADNFGGMKCZLCZJLCZKACPCACZMCSUAAEKAAAMFGLBD
    CZCJDCZCDCRCSTCAKBUCDFLUBJDRFGGG $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem2 $p |- ( ( ( ph -> ps ) -> ch ) -> ( ( ( ps -> ta ) -> ( ph ->
    F. ) ) -> ch ) ) $=
    ( wi wfal retbwax2 merco1 ax-mp ) CAEZBDEAFEEZFEZEZBEABEZEZNCEKCEELMEOLJGBD
    AFMHICAKBNHI $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem3 $p |- ( ( ( ph -> ps ) -> ( ch -> F. ) ) -> ( ch -> ph ) ) $=
    ( wi wfal merco1lem2 retbwax2 ax-mp ) AAADZAEDDZIDZDZABDCEDDZCADZDZIEDJEDDZ
    LAAEAFKLDPLDKAGJILEFHHNEDMEDDZLODZCAEBFORDQRDOLGMNREFHHH $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem4 $p |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ch ) ) $=
    ( wi wfal merco1lem3 merco1 ax-mp ) CADZBEDZDZBDABDZDZLCDBCDDJAEDZDIEDZDKDM
    JNIFBEAOKGHCABBLGH $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem5 $p |- ( ( ( ( ph -> F. ) -> ch ) -> ta ) -> ( ph -> ta ) ) $=
    ( wi wfal merco1lem4 merco1 ax-mp ) CADZAEDZDBDJBDZDKCDACDDIJBFCAABKGH $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem6 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ch -> ( ph -> ps ) ) ) $=
    ( wi wfal merco1lem5 merco1lem3 ax-mp merco1 ) ABDZEDCEDZDZEDZADZAJDCJDDJME
    DZDZNLODZPOEDMDQLEEFOELGHJKOFHABMGHJECEAIH $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem7 $p |- ( ph -> ( ( ( ps -> ch ) -> ps ) -> ps ) ) $=
    ( wi wfal merco1lem5 merco1 ax-mp merco1lem6 ) BCDZBDZKBDZDZALDBEDKEDZDCDJD
    MBNCFBEKCJGHKBAIH $.

  $( ~ tbw-ax3 rederived from ~ merco1 .  (Contributed by Anthony Hart,
     17-Sep-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  retbwax3 $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $=
    ( wi retbwax2 merco1lem7 ax-mp ) AAACCZABCACACAADGABEF $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem8 $p |- ( ph -> ( ( ps -> ( ps -> ch ) ) -> ( ps -> ch ) ) ) $=
    ( wi merco1lem6 ax-mp ) BBCDZDZHGDZDAIDBCHEHGAEF $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem9 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wfal wi merco1lem8 ax-mp ) CADZAABDZDHDZDZIGABEJABEF $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem10 $p |- ( ( ( ( ( ph -> ps ) -> ch ) -> ( ta -> ch ) ) -> ph ) ->
    ( th -> ph ) ) $=
    ( wi wfal merco1 merco1lem2 ax-mp ) ABFZDGFZFCAFEGFFAFZGFZFKCFECFFZFZOAFDAF
    FMKFOFPCAEAKHMKOLIJABDNOHJ $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem11 $p |- ( ( ph -> ps ) -> ( ( ( ch -> ( ph -> ta ) ) -> F. ) -> ps
    ) ) $=
    ( wi wfal merco1lem5 merco1lem3 ax-mp merco1lem4 merco1 merco1lem2 ) ADEZBA
    EZCMEZFEZFEZEZFEZFEZEZABEPBEEZOTEZUAQTEZUCRTEZUDTFESEUERFFGTFRHINQTJIOFTGIC
    MTJISAEUBEUAUBEBAPFAKSAUBDLII $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem12 $p |- ( ( ph -> ps ) -> ( ( ( ch -> ( ph -> ta ) ) -> ph ) -> ps
    ) ) $=
    ( wi wfal merco1lem3 merco1 ax-mp merco1lem9 merco1lem11 ) BAEZCADEZEZAEZFE
    ZEFEAEZABEOBEEOAEZQOREZRMPECFEZENESMPCGADOTNHIOAJIOALFKIBAOFAHI $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem13 $p |- ( ( ( ( ph -> ps ) -> ( ch -> ps ) ) -> ta ) -> ( ph ->
    ta ) ) $=
    ( wi wfal merco1 merco1lem4 ax-mp merco1lem12 ) DAEZAFEEAEABECBEEZEZLDEADEE
    ALEZMBAECFEEAEZAELENBACAAGOALHIALKFJIDAAALGI $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem14 $p |- ( ( ( ( ph -> ps ) -> ps ) -> ch ) -> ( ph -> ch ) ) $=
    ( wi wfal merco1lem13 merco1lem8 merco1 ax-mp merco1lem9 merco1lem12 ) CADZ
    AEDDADABDZBDZDZNCDACDDANDZOMNDNDZPDZPABMNFRRPDZDZSPADREDDADZQDTUAMBGPARAQHI
    RPJIIANLEKICAAANHI $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem15 $p |- ( ( ph -> ps ) -> ( ph -> ( ch -> ps ) ) ) $=
    ( wi merco1lem14 merco1lem13 ax-mp ) ABDZBDCBDZDAIDZDHJDABIEHBCJFG $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem16 $p |- ( ( ( ph -> ( ps -> ch ) ) -> ta ) -> ( ( ph -> ch ) -> ta
    ) ) $=
    ( wi wfal merco1lem15 merco1lem11 ax-mp merco1 ) DAEZACEZFEEFEABCEEZEZMDELD
    EELMENACBGLMKFHIDALFMJI $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem17 $p |- ( ( ( ( ( ph -> ps ) -> ph ) -> ch ) -> ta ) -> ( ( ph ->
    ch ) -> ta ) ) $=
    ( wfal merco1lem11 merco1lem7 ax-mp merco1lem9 merco1lem4 merco1lem16 mpsyl
    wi merco1 ) DAMZACMZEMZMCMZABMAMZCMZMTDMPDMMQPMZTMZRQCMTPTMZUBCAMZSEMMEMAMZ
    UCSAMZUEMZUESAUDEFUGUGUEMZMZUHUEAMUGEMMAMZUFMUIUJABGUEAUGAUFNHUGUEIHHCASEAN
    HTAMZUAEMMEMPMZUCUBMUAPMZULMZULUAPUKEFUNUNULMZMZUOULAMUNEMMAMZUMMUPUQPEGULA
    UNAUMNHUNULIHHTAUAEPNHHOQCJQACTKLDAPCTNH $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem18 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ps -> ph ) -> ( ps ->
    ch ) ) ) $=
    ( wfal merco1 merco1lem17 ax-mp merco1lem5 merco1lem3 merco1lem4 merco1lem2
    wi merco1lem9 ) BALZABCLZLZNOLZLZLZROBLZALRLZSTNDLZLTLALRLUAOBNTAETUBARFGBC
    ARFGSSRLZLZUCQRDLSDLZLZDLZDLZLZUDRUHLZUIUFUHLZUJUHDLUGLUKUFDDHUHDUFIGRUEUHH
    GPQUHJGUGNLUDLUIUDLRDSDNEUGNUDOKGGSRMGG $.

  $( ~ tbw-ax1 rederived from ~ merco1 .

     This theorem, along with ~ retbwax2 , ~ retbwax3 , and ~ retbwax4 , shows
     that ~ merco1 with ~ ax-mp can be used as a complete axiomatization of
     propositional calculus.  (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  retbwax1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wi merco1lem18 merco1lem16 ax-mp merco1lem15 merco1lem14 wfal merco1lem10
    merco1 merco1lem9 merco1lem13 ) BCDZABDZACDZDZDZPOQDZDZBQDRDSBACEBACRFGOSUA
    DZDZUBSRDUBDZUCRUBDZUDRUADUEPQOHRUASHGRSUAEGORUBIGUCUBDZJDZUADZUFUGTDZUHUFQ
    DZTDZUIOUBQITADZUGJDZDZQDUJDZUKUIDQADZUGDZUMDUNDZUOUMJDULJDDUGDUQDURUGJJUPU
    LKUMJULUGUQLGQAUFUMUNLGTAUGQUJLGGUGTPHGUHUBDUFDZUFDZUHUFDUSUTDUTUFJUAUSSKUS
    UFMGUHUBUCUFNGGGG $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Derive the Tarski-Bernays-Wajsberg axioms from Meredith's Second CO Axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( A single axiom for propositional calculus offered by Meredith.

     This axiom has 19 symbols, sans auxiliaries.  See notes in ~ merco1 .
     (Contributed by Anthony Hart, 7-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco2 $p |- ( ( ( ph -> ps ) -> ( ( F. -> ch ) -> th ) ) -> ( ( th
         -> ph ) -> ( ta -> ( et -> ph ) ) ) ) $=
    ( wi wfal falim pm2.04 mpi jarl idd jad looinv 3syl a1dd a1i com4l ) FABGZH
    CGZDGGZDAGZEAUBUCEAGGGFUBUCAEUBTDGZADGDGUCAGUBUAUDCITUADJKUDADDABDLUDDMNADO
    PQRS $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem1 $p |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ( th -> ch ) ) ) $=
    ( wi wfal merco2 ax-mp ) AAEZFAEZAEEIAIEEEZABEZCEZBDCEZEZEZAAAAAAGZKKPEZQCA
    EZJLEZEZPEZKREZCAALBDGPTEJUAEEZUBUCETOEJPEEZUDOJFEZEFBETEEUEBNAFJAGOUFBTJMG
    HTOAPJSGHPTAUAKKGHHHH $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem2 $p |- ( ( ( ph -> ps ) -> ph ) -> ( ch -> ( th -> ph ) ) ) $=
    ( wi wfal merco2 ax-mp ) AAEZFAEZAEEIAIEEEZABEZAEZCDAEEZEZAAAAAAGZKKOEZPIJL
    EZEZOEZKQEZAAALCDGOREJSEEZTUAERNEJOEEZUBNLEJREEZUCLJFEZEJNEEUDABAFCDGLUEANJ
    JGHNLARJMGHRNAOJIGHORASKKGHHHH $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem3 $p |- ( ( ps -> ch ) -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi wfal merco2 mercolem2 ax-mp ) AADZEADZADDIAIDDDZBCDZBACDZDZDZAAAAAAFZK
    KODZPCADZJBDZDZODZKQDZCAABBAFOSDJTDDZUAUBDSNDJODDZUCNBDJSDDUDBMJJGNBASJLFHS
    NAOJRFHOSATKKFHHHH $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem4 $p |- ( ( th -> ( et -> ph ) ) -> ( ( ( th -> ch )
  -> ph ) -> ( ta -> ( et -> ph ) ) ) ) $=
    ( wi wfal merco2 mercolem1 ax-mp mercolem3 ) AAFZGAFZAFFLALFFFZCEAFZFZCBFZA
    FZDOFFZFZAAAAAAHZNNTFZUAOAFZMCFFZTFZNUBFZOAACRDHTCFZMUDFFZUEUFFUGUDFZUHQMTF
    FZUIMQFZTFZUJLUKFSFULAAAQDEHLUKSPIJMQTMIJCBATUCMHJMUGUDKJTCAUDNNHJJJJ $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem5 $p |- ( th -> ( ( th -> ph ) -> ( ta -> ( ch -> ph ) ) ) ) $=
    ( wi wfal merco2 mercolem1 ax-mp mercolem2 ) AAEZFAEZAEEKAKEEEZCCAEDBAEEEZE
    ZAAAAAAGZMMOEZPLCEZOEZMQEZKRENESAAACDBGKRNCHIOCELREESTECNLLJOCARMMGIIII $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem6 $p |- ( ( ph -> ( ps -> ( ph -> ch ) ) )
  -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi wfal merco2 mercolem1 ax-mp mercolem5 mercolem4 ) AADZEADADDKAKDDDZABA
    CDZDZDZNDZAAAAAAFZLLPDZQLLRDZQORDZLSDZLTQMRDZLTDZAODZMDPDUBAOMBGUDMPLGHATDU
    BUCDNOALIRCALOJHHHLTUADZQPUADZLUEDZALDZPDSDUFALPLGUHPSLGHOUEDUFUGDRLOLIUANO
    LTJHHHHHHH $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem7 $p |- ( ( ph -> ps ) -> ( ( ( ph -> ch )
  -> ( th -> ps ) ) -> ( th -> ps ) ) ) $=
    ( wi wfal merco2 mercolem3 mercolem6 ax-mp mercolem5 mercolem4 ) AAEZFAEAEE
    MAMEEEZABEZACEZDBEZEZQEZEZAAAAAAGPSEZNTEZRUAEUARPQHRPQIJATEUAUBEBDARKSCANOL
    JJJ $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem8 $p |- ( ( ph -> ps ) -> ( ( ps -> ( ph -> ch ) )
  -> ( ta -> ( th -> ( ph -> ch ) ) ) ) ) $=
    ( wi wfal merco2 mercolem3 ax-mp mercolem7 ) AAFZGAFZAFFLALFFFZABFZBACFZFED
    PFFFZFZAAAAAAHZNNRFZSPMBFZFUAFZRFZNTFZUBQFUCPUAABEDHOUBQIJRMUBFZFUEFZUCUDFO
    UBFUFABCMKOUBQMKJRUEAUBNNHJJJJ $.

  $( ~ tbw-ax1 rederived from ~ merco2 .  (Contributed by Anthony Hart,
     16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re1tbw1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wi mercolem8 mercolem3 mercolem6 mpsyl ax-mp ) BCDZABDZJACDZDZDZDNKBLDZND
    DJONABCJKEABCFKOMGHJKLGI $.

  $( ~ tbw-ax2 rederived from ~ merco2 .  (Contributed by Anthony Hart,
     16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re1tbw2 $p |- ( ph -> ( ps -> ph ) ) $=
    ( wi mercolem1 ax-mp mercolem6 ) BABACZCZCZHAICZIAACZACHCJAAABDKAHBDEABGFEB
    AAFE $.

  $( ~ tbw-ax3 rederived from ~ merco2 .  (Contributed by Anthony Hart,
     16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re1tbw3 $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $=
    ( wi mercolem2 mercolem6 ax-mp ) AACZACAGCCZABCACZACZAAAADIHJCZCKABHIDIHAEF
    F $.

  $( ~ tbw-ax4 rederived from ~ merco2 .

     This theorem, along with ~ re1tbw1 , ~ re1tbw2 , and ~ re1tbw3 , shows
     that ~ merco2 , along with ~ ax-mp , can be used as a complete
     axiomatization of propositional calculus.  (Contributed by Anthony Hart,
     16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re1tbw4 $p |- ( F. -> ph ) $=
    ( wi wfal re1tbw3 re1tbw2 re1tbw1 ax-mp mercolem3 merco2 ) AABZCABZJABZABZJ
    AADALBMJBAJEALAFGGZJJKBZNKKBZJOBZKABZKBZKBZPKADKSBTPBKREKSKFGGRPBPQBCKAHKAA
    KJJIGGGG $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Derive the Lukasiewicz axioms from the Russell-Bernays Axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Justification for ~ rb-imdf .  (Contributed by Anthony Hart,
     17-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  rb-bijust $p |- ( ( ph <-> ps ) <-> -. ( -. ( -. ph \/ ps )
    \/ -. ( -. ps \/ ph ) ) ) $=
    ( wb wi wn wo dfbi1 imor notbii imbi12i pm4.62 3bitri ) ABCABDZBADZEZDZEAEB
    FZBEAFZEZDZEQESFZEABGPTMQOSABHNRBAHIJITUAQRKIL $.

  $( The definition of implication, in terms of ` \/ ` and ` -. ` .
     (Contributed by Anthony Hart, 17-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rb-imdf $p |- -. ( -. ( -. ( ph -> ps ) \/ ( -. ph \/ ps ) )
    \/ -. ( -. ( -. ph \/ ps ) \/ ( ph -> ps ) ) ) $=
    ( wi wn wo wb imor rb-bijust mpbi ) ABCZADBEZFJDKEDKDJEDEDABGJKHI $.

  ${
    anmp.min $e |- ph $.
    anmp.maj $e |- ( -. ph \/ ps ) $.
    $( Modus ponens for ` \/ ` ` -. ` axiom systems.  (Contributed by Anthony
       Hart, 12-Aug-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    anmp $p |- ps $=
      ( imorri ax-mp ) ABCABDEF $.
  $}

  $( The first of four axioms in the Russell-Bernays axiom system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rb-ax1 $p |- ( -. ( -. ps \/ ch ) \/ ( -. ( ph \/ ps ) \/ ( ph \/ ch ) ) ) $=
    ( wn wo wi orim2 imor 3imtr3i imori ) BDCEZABEZDACEZEZBCFLMFKNABCGBCHLMHIJ
    $.

  $( The second of four axioms in the Russell-Bernays axiom system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rb-ax2 $p |- ( -. ( ph \/ ps ) \/ ( ps \/ ph ) ) $=
    ( wo wn pm1.4 con3i con1i orri ) ABCZDZBACZKJIKABEFGH $.

  $( The third of four axioms in the Russell-Bernays axiom system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rb-ax3 $p |- ( -. ph \/ ( ps \/ ph ) ) $=
    ( wn wo pm2.46 con1i orri ) ACZBADZIHBAEFG $.

  $( The fourth of four axioms in the Russell-Bernays axiom system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rb-ax4 $p |- ( -. ( ph \/ ph ) \/ ph ) $=
    ( wo wn pm1.2 con3i con1i orri ) AABZCZAAIHAADEFG $.

  ${
    rbsyl.1 $e |- ( -. ps \/ ch ) $.
    rbsyl.2 $e |- ( ph \/ ps ) $.
    $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 18-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rbsyl $p |- ( ph \/ ch ) $=
      ( wo wn rb-ax1 anmp ) ABFZACFZEBGCFJGKFDABCHII $.
  $}

  ${
    rblem1.1 $e |- ( -. ph \/ ps ) $.
    rblem1.2 $e |- ( -. ch \/ th ) $.
    $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 18-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rblem1 $p |- ( -. ( ph \/ ch ) \/ ( ps \/ th ) ) $=
      ( wo wn rb-ax1 anmp rb-ax2 rbsyl ) ACGHZBCGZBDGZCHDGNHOGFBCDIJMCBGZNCBKMC
      AGZPAHBGQHPGECABIJACKLLL $.
  $}

  $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
     (Contributed by Anthony Hart, 18-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rblem2 $p |- ( -. ( ch \/ ph ) \/ ( ch \/ ( ph \/ ps ) ) ) $=
    ( wn wo rb-ax2 rb-ax3 rbsyl rb-ax1 anmp ) ADZABEZECAEDCLEEKBAELBAFABGHCALIJ
    $.

  $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
     (Contributed by Anthony Hart, 18-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rblem3 $p |- ( -. ( ch \/ ph ) \/ ( ( ch \/ ps ) \/ ph ) ) $=
    ( wo wn rb-ax2 rblem2 rbsyl ) CADEZACBDZDZJADAJFIACDKCBAGCAFHH $.

  ${
    rblem4.1 $e |- ( -. ph \/ th ) $.
    rblem4.2 $e |- ( -. ps \/ ta ) $.
    rblem4.3 $e |- ( -. ch \/ et ) $.
    $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 18-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rblem4 $p |- ( -. ( ( ph \/ ps ) \/ ch ) \/ ( ( et \/ ta ) \/ th ) ) $=
      ( wo wn rblem1 rb-ax2 rb-ax1 anmp rbsyl rb-ax4 rblem2 rb-ax3 ) ABJZCJKZCB
      JZAJZFEJZDJUBUDADCFBEIHLGLUABCJZAJZUCUFKZAUBJZUCAUBMUGAUEJZUHUEKUBJUIKUHJ
      BCMAUEUBNOUEAMPPUAUFUFJUFUFQTUFCUFTKUIUFAUEMBCARPCKZUEJUJUFJCBSUEAUJROLPP
      P $.
  $}

  $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
     (Contributed by Anthony Hart, 19-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rblem5 $p |- ( -. ( -. -. ph \/ ps ) \/ ( -. -. ps \/ ph ) ) $=
    ( wn wo rb-ax2 rb-ax4 rb-ax3 rbsyl anmp rblem1 ) ACZCZBDCABCZCZDNADANELABNK
    ADLCZADKAADAAFAAGHZKOAAOLDLODOLLDLLFLLGHOLEIPJINMDMNDNMMDMMFMMGHNMEIJH $.

  ${
    rblem6.1 $e |- -. ( -. ( -. ph \/ ps ) \/ -. ( -. ps \/ ph ) ) $.
    $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 19-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rblem6 $p |- ( -. ph \/ ps ) $=
      ( wn wo rb-ax4 rb-ax3 rbsyl rb-ax2 anmp rblem3 rblem5 ) ADBEZDZBDAEDZEZDZ
      MCNDZPEZQDMEPREZSNREZTRNEUARNNENNFNNGHRNIJRONKJPRIJMPLJJ $.
  $}

  ${
    rblem7.1 $e |- -. ( -. ( -. ph \/ ps ) \/ -. ( -. ps \/ ph ) ) $.
    $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 19-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rblem7 $p |- ( -. ps \/ ph ) $=
      ( wn wo rb-ax3 rblem5 anmp ) ADBEDZBDAEZDZEZDZJCKDLEMDJEKIFJLGHH $.
  $}

  ${
    re1axmp.min $e |- ph $.
    re1axmp.maj $e |- ( ph -> ps ) $.
    $( ~ ax-mp derived from Russell-Bernays'.  (Contributed by Anthony Hart,
       19-Aug-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    re1axmp $p |- ps $=
      ( wi wn wo rb-imdf rblem6 anmp ) ABCABEZAFBGZDKLABHIJJ $.
  $}

  $( ~ luk-1 derived from Russell-Bernays'.  (Contributed by Anthony Hart,
     19-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re2luk1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wi wn rb-imdf rblem7 rblem6 rb-ax2 rb-ax4 rb-ax3 rbsyl anmp rblem1 rb-ax1
    wo rblem4 ) ABDZEZBCDZACDZDZPZRUBDZSTEZUAPZUBUBUFTUAFGSAEZBPZUFUHEZBECPZEZU
    GCPZPZUFUKUEULUAUEUJPZUKEZUEPZTUJBCFHUNEUEUOPUPUEUOIUEUEUJUOUEEUEUEPUEUEJUE
    UEKLUOUKPUKUOPUOUKUKPUKUKJUKUKKLZUOUKIMNLMUAULACFGNUKUIULPZPZUIUMPZUGBCOUSE
    ZUMUIPZUTUMUIIVAURUKPVBUIULUKUIULUKUIEUIUIPUIUIJUIUIKLULEULULPULULJULULKLUQ
    QUKURILLMLRUHABFHLLUDUCRUBFGM $.

  $( ~ luk-2 derived from Russell-Bernays'.  (Contributed by Anthony Hart,
     19-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re2luk2 $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wn wi wo rb-ax4 rb-ax3 rbsyl rb-ax2 anmp rblem1 rb-imdf rblem6 rblem7 ) A
    BZACZBZADZOACZPNBZADZATBAADZAAEZSAAANADSBZADNUAAUBAAFGZNUCAAUCSDSUCDUCSSDSS
    ESSFGUCSHIUDJIUDJGOTNAKLGRQOAKMI $.

  $( ~ luk-3 derived from Russell-Bernays'.

     This theorem, along with ~ re1axmp , ~ re2luk1 , and ~ re2luk2 shows that
     ~ rb-ax1 , ~ rb-ax2 , ~ rb-ax3 , and ~ rb-ax4 , along with ~ anmp , can be
     used as a complete axiomatization of propositional calculus.  (Contributed
     by Anthony Hart, 19-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re2luk3 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wn wi wo rb-imdf rblem7 rb-ax4 rb-ax3 rbsyl rb-ax2 anmp rblem2 ) ACZNBDZE
    ZAODZNNCZBEZOOSNBFGNREZNSERNETRNNENNHNNIJRNKLRBNMLJQPAOFGL $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Stoic logic non-modal portion (Chrysippus of Soli)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The Greek Stoics developed a system of logic called Stoic logic.
  The Stoic Chrysippus, in particular, was often considered one of the greatest
  logicians of antiquity.
  Stoic logic is different from Aristotle's system, since it focuses
  on propositional logic,
  though later thinkers did combine the systems of the Stoics with Aristotle.
  Jan Lukasiewicz reports,
  ""For anybody familiar with mathematical logic it is self-evident
  that the Stoic dialectic is the ancient form of modern propositional logic""
  ( _On the history of the logic of proposition_ by Jan Lukasiewicz (1934),
  translated in: _Selected Works_ - Edited by Ludwik Borkowski -
  Amsterdam, North-Holland, 1970 pp. 197-217,
  referenced in ""History of Logic""
  ~ https://www.historyoflogic.com/logic-stoics.htm ).

  In this section we show that the propositional logic system we use
  (which is non-modal) is at least as strong as the non-modal portion
  of Stoic logic.  We show this by showing that our system
  assumes or proves all of key features of Stoic logic's non-modal portion
  (specifically the Stoic logic indemonstrables, themata, and principles).

  ""In terms of contemporary logic, Stoic syllogistic is best understood as
  a substructural backwards-working Gentzen-style natural-deduction system
  that consists of five kinds of axiomatic arguments (the indemonstrables)
  and four inference rules, called themata.  An argument is a syllogism
  precisely if it either is an indemonstrable or can be reduced to one by
  means of the themata (Diogenes Laertius (D. L. 7.78)).""
  (_Ancient Logic_, Stanford Encyclopedia of Philosophy
  ~ https://plato.stanford.edu/entries/logic-ancient/ ).
  There are also a few ""principles"" that support logical reasoning,
  discussed below.  For more information, see
  ""Stoic Logic"" by Susanne Bobzien, especially
  [Bobzien] p. 110-120, especially for a discussion about the themata
  (including how they were reconstructed and how they were used).
  There are differences in the systems we can only partly represent,
  for example, in Stoic logic
  ""truth and falsehood are temporal properties of assertibles...
  They can belong to an assertible at
  one time but not at another"" ([Bobzien] p. 87).
  Stoic logic also included various kinds of modalities, which we do not
  include here since our basic propositional logic does not include modalities.

  A key part of the Stoic logic system is a set of five ""indemonstrables""
  assigned to Chrysippus of Soli by Diogenes Laertius, though in
  general it is difficult to assign specific ideas to specific thinkers.
  The indemonstrables are described in, for example,
  [Lopez-Astorga] p. 11 , [Sanford] p. 39, and [Hitchcock] p. 5.
  These indemonstrables are
  modus ponendo ponens (modus ponens) ~ ax-mp ,
  modus tollendo tollens (modus tollens) ~ mto ,
  modus ponendo tollens I ~ mptnan ,
  modus ponendo tollens II ~ mptxor , and
  modus tollendo ponens (exclusive-or version) ~ mtpxor .
  The first is an axiom, the second is already proved; in this section
  we prove the other three.
  Note that modus tollendo ponens ~ mtpxor originally used exclusive-or,
  but over time the name modus tollendo ponens has increasingly referred
  to an inclusive-or variation, which is proved in ~ mtpor .

  After we prove the indemonstratables, we then prove all the Stoic logic
  themata (the inference rules of Stoic logic; ""thema"" is singular).
  This is straightforward for thema 1 ( ~ stoic1a and ~ stoic1b )
  and thema 3 ( ~ stoic3 ).
  However, while Stoic logic was once a leading logic system,
  most direct information about Stoic logic
  has since been lost, including the exact texts of thema 2 and thema 4.
  There are, however, enough references and specific
  examples to support reconstruction.  Themata 2 and 4
  have been reconstructed; see statements T2 and T4 in
  [Bobzien] p. 110-120 and our proofs of them in ~ stoic2a , ~ stoic2b ,
  ~ stoic4a , and ~ stoic4b .

  Stoic logic also had a set of principles involving assertibles.
  Statements in [Bobzien] p. 99 express the known principles.
  The following paragraphs discuss these principles and our proofs of them.

  ""A principle of double negation, expressed by saying that a
  double-negation (Not: not: p) is equivalent to the assertible
  that is doubly negated (p) (DL VII 69).""  In other words,
  ` ( ph <-> -. -. ph ) ` as proven in ~ notnot .

  ""The principle that all conditionals that are formed by using
  the same assertible twice (like 'If p, p') are true (Cic. Acad. II 98).""
  In other words, ` ( ph -> ph ) ` as proven in ~ id .

  ""The principle that all disjunctions formed by a contradiction
   (like 'Either p or not: p') are true (S. E. M VIII 282)""
  Remember that in Stoic logic, 'or' means 'exclusive or'.
  In other words, ` ( ph \/_ -. ph ) ` as proven in ~ xorexmid .

  [Bobzien] p. 99 also suggests that Stoic logic may have dealt with
  commutativity (see ~ xorcom and ~ ancom ) and the
  principle of contraposition ( ~ ax-3 ) (pointing to DL VII 194).

  In short, the non-modal propositional logic system we use is at
  least as strong as the non-modal portion of Stoic logic.

  For more about Aristotle's system, see ~ barbara and related theorems.
$)

  ${
    $( Minor premise for modus ponendo tollens 1. $)
    mptnan.min $e |- ph $.
    $( Major premise for modus ponendo tollens 1. $)
    mptnan.maj $e |- -. ( ph /\ ps ) $.
    $( Modus ponendo tollens 1, one of the ""indemonstrables"" in Stoic logic.
       See rule 1 on [Lopez-Astorga] p. 12 , rule 1 on [Sanford] p. 40, and
       rule A3 in [Hitchcock] p. 5.  Sanford describes this rule second (after
       ~ mptxor ) as a ""safer, and these days much more common"" version of
       modus ponendo tollens because it avoids confusion between inclusive-or
       and exclusive-or.  (Contributed by David A. Wheeler, 3-Jul-2016.) $)
    mptnan $p |- -. ps $=
      ( wn imnani ax-mp ) ABECABDFG $.
  $}

  ${
    $( Minor premise for modus ponendo tollens 2. $)
    mptxor.min $e |- ph $.
    $( Major premise for modus ponendo tollens 2. $)
    mptxor.maj $e |- ( ph \/_ ps ) $.
    $( Modus ponendo tollens 2, one of the ""indemonstrables"" in Stoic logic.
       Note that this uses exclusive-or ` \/_ ` .  See rule 2 on
       [Lopez-Astorga] p. 12 , rule 4 on [Sanford] p. 39 and rule A4 in
       [Hitchcock] p. 5 .  (Contributed by David A. Wheeler, 3-Jul-2016.)
       (Proof shortened by Wolf Lammen, 12-Nov-2017.)  (Proof shortened by BJ,
       19-Apr-2019.) $)
    mptxor $p |- -. ps $=
      ( wxo wa wn xornan ax-mp mptnan ) ABCABEABFGDABHIJ $.
  $}

  ${
    $( Minor premise for modus tollendo ponens (inclusive-or version). $)
    mtpor.min $e |- -. ph $.
    $( Major premise for modus tollendo ponens (inclusive-or version). $)
    mtpor.max $e |- ( ph \/ ps ) $.
    $( Modus tollendo ponens (inclusive-or version), aka disjunctive
       syllogism.  This is similar to ~ mtpxor , one of the five original
       ""indemonstrables"" in Stoic logic.  However, in Stoic logic this rule
       used exclusive-or, while the name modus tollendo ponens often refers to
       a variant of the rule that uses inclusive-or instead.  The rule says,
       ""if ` ph ` is not true, and ` ph ` or ` ps ` (or both) are true, then
       ` ps ` must be true.""  An alternative phrasing is, ""Once you eliminate
       the impossible, whatever remains, no matter how improbable, must be the
       truth."" -- Sherlock Holmes (Sir Arthur Conan Doyle, 1890:  The Sign of
       the Four, ch. 6).  (Contributed by David A. Wheeler, 3-Jul-2016.)
       (Proof shortened by Wolf Lammen, 11-Nov-2017.) $)
    mtpor $p |- ps $=
      ( wn ori ax-mp ) AEBCABDFG $.
  $}

  ${
    $( Minor premise for modus tollendo ponens (original exclusive-or version).
    $)
    mtpxor.min $e |- -. ph $.
    $( Major premise for modus tollendo ponens (original exclusive-or version).
    $)
    mtpxor.maj $e |- ( ph \/_ ps ) $.
    $( Modus tollendo ponens (original exclusive-or version), aka disjunctive
       syllogism, similar to ~ mtpor , one of the five ""indemonstrables"" in
       Stoic logic.  The rule says, ""if ` ph ` is not true, and either ` ph `
       or ` ps ` (exclusively) are true, then ` ps ` must be true.""  Today the
       name ""modus tollendo ponens"" often refers to a variant, the inclusive-or
       version as defined in ~ mtpor .  See rule 3 on [Lopez-Astorga] p. 12
       (note that the ""or"" is the same as ~ mptxor , that is, it is
       exclusive-or ~ df-xor ), rule 3 of [Sanford] p. 39 (where it is not as
       clearly stated which kind of ""or"" is used but it appears to be in the
       same sense as ~ mptxor ), and rule A5 in [Hitchcock] p. 5 (exclusive-or
       is expressly used).  (Contributed by David A. Wheeler, 4-Jul-2016.)
       (Proof shortened by Wolf Lammen, 11-Nov-2017.)  (Proof shortened by BJ,
       19-Apr-2019.) $)
    mtpxor $p |- ps $=
      ( wxo wo xoror ax-mp mtpor ) ABCABEABFDABGHI $.
  $}

  ${
    $( Premise for Stoic logic thema 1. $)
    stoic1.1 $e |- ( ( ph /\ ps ) -> th ) $.
    $( Stoic logic Thema 1 (part a).

       The first thema of the four Stoic logic themata, in its basic form, was:

       ""When from two (assertibles) a third follows, then from either of them
       together with the contradictory of the conclusion the contradictory of
       the other follows.""  (Apuleius Int. 209.9-14), see [Bobzien] p. 117 and
       ~ https://plato.stanford.edu/entries/logic-ancient/

       We will represent thema 1 as two very similar rules ~ stoic1a and
       ~ stoic1b to represent each side.  (Contributed by David A. Wheeler,
       16-Feb-2019.) $)
    stoic1a $p |- ( ( ph /\ -. th ) -> -. ps ) $=
      ( wn wa con3i ianor sylib anim2i orcom andi pm3.24 biorfi 3bitr4i simprd
      wo ) ACEZFZABEZSAAEZTQZFZATFZRUBARABFZEUBUECDGABHIJAUAFZUDQUDUFQUCUDUFUDK
      AUATLUFUDAMNOIP $.

    $( Stoic logic Thema 1 (part b).  The other part of thema 1 of Stoic logic;
       see ~ stoic1a .  (Contributed by David A. Wheeler, 16-Feb-2019.) $)
    stoic1b $p |- ( ( ps /\ -. th ) -> -. ph ) $=
      ( ancoms stoic1a ) BACABCDEF $.
  $}

  ${
    $( Premise 1 for Stoic logic thema 2 version a. $)
    stoic2a.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Premise 2 for Stoic logic thema 2 version a. $)
    stoic2a.2 $e |- ( ( ph /\ ch ) -> th ) $.
    $( Stoic logic Thema 2 version a.

       Statement T2 of [Bobzien] p. 117 shows a reconstructed version of Stoic
       logic thema 2 as follows:  ""When from two assertibles a third follows,
       and from the third and one (or both) of the two another follows, then
       this other follows from the first two.""

       Bobzien uses constructs such as ` ph ` , ` ps |- ch ` ; in Metamath we
       will represent that construct as ` ph /\ ps -> ch ` .

       This version a is without the phrase ""or both""; see ~ stoic2b for the
       version with the phrase ""or both"".  We already have this rule as
       ~ syldan , so here we show the equivalence and discourage its use.
       (New usage is discouraged.)  (Contributed by David A. Wheeler,
       17-Feb-2019.) $)
    stoic2a $p |- ( ( ph /\ ps ) -> th ) $=
      ( syldan ) ABCDEFG $.
  $}

  ${
    $( Premise 1 for Stoic logic thema 2 version b. $)
    stoic2b.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Premise 2 for Stoic logic thema 2 version b. $)
    stoic2b.2 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
    $( Stoic logic Thema 2 version b.  See ~ stoic2a .

       Version b is with the phrase ""or both"".  We already have this rule as
       ~ mpd3an3 , so here we prove the equivalence and discourage its use.
       (New usage is discouraged.)  (Contributed by David A. Wheeler,
       17-Feb-2019.) $)
    stoic2b $p |- ( ( ph /\ ps ) -> th ) $=
      ( mpd3an3 ) ABCDEFG $.
  $}

  ${
    $( Premise 1 for Stoic logic thema 3. $)
    stoic3.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Premise 2 for Stoic logic thema 3. $)
    stoic3.2 $e |- ( ( ch /\ th ) -> ta ) $.
    $( Stoic logic Thema 3.

       Statement T3 of [Bobzien] p. 116-117 discusses Stoic logic thema 3.

       ""When from two (assemblies) a third follows, and from the one that
       follows (i.e., the third) together with another, external external
       assumption, another follows, then other follows from the first two and
       the externally co-assumed one.  (Simp.  Cael. 237.2-4)"" (Contributed by
       David A. Wheeler, 17-Feb-2019.) $)
    stoic3 $p |- ( ( ph /\ ps /\ th ) -> ta ) $=
      ( wa sylan 3impa ) ABDEABHCDEFGIJ $.
  $}

  ${
    $( Premise 1 for Stoic logic thema 4a. $)
    stoic4a.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Premise 2 for Stoic logic thema 4a. $)
    stoic4a.2 $e |- ( ( ch /\ ph /\ th ) -> ta ) $.
    $( Stoic logic Thema 4 version a.

       Statement T4 of [Bobzien] p. 117 shows a reconstructed version of Stoic
       logic thema 4:  ""When from two assertibles a third follows, and from the
       third and one (or both) of the two and one (or more) external
       assertible(s) another follows, then this other follows from the first
       two and the external(s).""

       We use ` th ` to represent the ""external"" assertibles.  This is version
       a, which is without the phrase ""or both""; see ~ stoic4b for the version
       with the phrase ""or both"".  (Contributed by David A. Wheeler,
       17-Feb-2019.) $)
    stoic4a $p |- ( ( ph /\ ps /\ th ) -> ta ) $=
      ( w3a 3adant3 simp1 simp3 syl3anc ) ABDHCADEABCDFIABDJABDKGL $.
  $}

  ${
    $( Premise 1 for Stoic logic thema 4b. $)
    stoic4b.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Premise 2 for Stoic logic thema 4b. $)
    stoic4b.2 $e |- ( ( ( ch /\ ph /\ ps ) /\ th ) -> ta ) $.
    $( Stoic logic Thema 4 version b.

       This is version b, which is with the phrase ""or both"".  See ~ stoic4a
       for more information.  (Contributed by David A. Wheeler,
       17-Feb-2019.) $)
    stoic4b $p |- ( ( ph /\ ps /\ th ) -> ta ) $=
      ( w3a 3adant3 simp1 simp2 simp3 syl31anc ) ABDHCABDEABCDFIABDJABDKABDLGM
      $.
  $}

"
Class {
	#name : #MmRawFileDataPartThree,
	#superclass : #MmDatabase,
	#category : #'Metamath-Parsing'
}
