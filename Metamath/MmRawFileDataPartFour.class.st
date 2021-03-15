"
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
    Predicate calculus with equality:  Tarski's system S2 (1 rule, 6 schemes)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  Here we extend the language of wffs with predicate calculus, which allows us
  to talk about individual objects in a domain of discussion (which for us will
  be the universe of all sets, so we call them ""setvar variables"") and make
  true/false statements about predicates, which are relationships between
  objects, such as whether or not two objects are equal.  In addition, we
  introduce universal quantification (""for all"", e.g. ~ ax-4 ) in order to
  make statements about whether a wff holds for every object in the domain of
  discussion.  Later we introduce existential quantification (""there exists"",
  ~ df-ex ) which is defined in terms of universal quantification.

  Our axioms are really axiom _schemes_, and our wff and setvar variables are
  metavariables ranging over expressions in an underlying ""object language.""
  This is explained here:  ~ mmset.html#axiomnote .

  Our axiom system starts with the predicate calculus axiom schemes system S2
  of Tarski defined in his 1965 paper, ""A Simplified Formalization of Predicate
  Logic with Identity"" [Tarski].  System S2 is defined in the last paragraph on
  p. 77, and repeated on p. 81 of [KalishMontague].  We do not include scheme
  B5 (our ~ sp ) of system S2 since [KalishMontague] shows it to be logically
  redundant (Lemma 9, p. 87, which we prove as theorem ~ spw below).

  Theorem ~ spw can be used to prove any _instance_ of ~ sp having mutually
  distinct setvar variables and no wff metavariables.  However, it seems that
  ~ sp in its general form cannot be derived from only Tarski's schemes.  We do
  not include B5 i.e. ~ sp as part of what we call ""Tarski's system"" because we
  want it to be the smallest set of axioms that is logically complete with
  no redundancies.  We later prove ~ sp as theorem ~ axc5 using the auxiliary
  axioms that make our system metalogically complete.

  Our version of Tarski's system S2 consists of propositional calculus
  ( ~ ax-mp , ~ ax-1 , ~ ax-2 , ~ ax-3 ) plus ~ ax-gen , ~ ax-4 , ~ ax-5 ,
  ~ ax-6 , ~ ax-7 , ~ ax-8 , and ~ ax-9 . The last 3 are equality axioms that
  represent 3 sub-schemes of Tarski's scheme B8.  Due to its side-condition
  (""where ` ph ` is an atomic formula and ` ps ` is obtained by replacing an
  occurrence of the variable ` x ` by the variable ` y ` ""), we cannot
  represent his B8 directly without greatly complicating our scheme language,
  but the simpler schemes ~ ax-7 , ~ ax-8 , and ~ ax-9 are sufficient for set
  theory and much easier to work with.

  Tarski's system is exactly equivalent to the traditional axiom system in most
  logic textbooks but has the advantage of being easy to manipulate with a
  computer program, and its simpler metalogic (with no built-in notions of
  ""free variable"" and ""proper substitution"") is arguably easier for a
  non-logician human to follow step by step in a proof (where ""follow"" means
  being able to identify the substitutions that were made, without necessarily
  a higher-level understanding).  In particular, it is logically complete in
  that it can derive all possible object-language theorems of predicate
  calculus with equality, i.e. the same theorems as the traditional system can
  derive.

  However, for efficiency (and indeed a key feature that makes Metamath
  successful), our system is designed to derive reusable theorem schemes
  (rather than object-language theorems) from other schemes.  From this
  ""metalogical"" point of view, Tarski's S2 is not complete.  For example, we
  cannot derive scheme ~ sp , even though (using ~ spw ) we can derive all
  instances of it that don't involve wff metavariables or bundled set
  metavariables.  (Two set metavariables are ""bundled"" if they can be
  substituted with the same set metavariable i.e. do not have a $d distinct
  variable proviso.)  Later we will introduce auxiliary axiom schemes ~ ax-10 ,
  ~ ax-11 , ~ ax-12 , and ~ ax-13 that are metatheorems of Tarski's system
  (i.e. are logically redundant) but which give our system the property of
  ""metalogical completeness,"" allowing us to prove directly (instead of, say,
  by induction on formula length) all possible schemes that can be expressed in
  our language.

$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Universal quantifier (continued); define ""exists"" and ""not free""
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The universal quantifier was introduced above in ~ wal for use by ~ df-tru .
  See the comments in that section.  In this section, we continue with the
  first ""real"" use of it.
$)

  $( Declare some names for individual variables. $)
  $v x $.
  $v y $.
  $v z $.
  $v w $.
  $v v $.
  $v u $.
  $v t $.
  $( Let ` x ` be an individual variable. $)
  vx $f setvar x $.
  $( Let ` y ` be an individual variable. $)
  vy $f setvar y $.
  $( Let ` z ` be an individual variable. $)
  vz $f setvar z $.
  $( Let ` w ` be an individual variable. $)
  vw $f setvar w $.
  $( Let ` v ` be an individual variable. $)
  vv $f setvar v $.
  $( Let ` u ` be an individual variable. $)
  vu $f setvar u $.
  $( Let ` t ` be an individual variable. $)
  vt $f setvar t $.

  $( Register 'A.' as a primitive expression (lacking a definition). $)
  $( $j primitive 'wal'; $)

  $( Declare the existential quantifier symbol. $)
  $c E. $.   $( Backwards E (read:  ""there exists"") $)

  $( Extend wff definition to include the existential quantifier (""there
     exists""). $)
  wex $a wff E. x ph $.

  $( Define existential quantification. ` E. x ph ` means ""there exists at
     least one set ` x ` such that ` ph ` is true.""  Definition of [Margaris]
     p. 49.  (Contributed by NM, 10-Jan-1993.) $)
  df-ex $a |- ( E. x ph <-> -. A. x -. ph ) $.

  $( Theorem 19.7 of [Margaris] p. 89.  (Contributed by NM, 12-Mar-1993.) $)
  alnex $p |- ( A. x -. ph <-> -. E. x ph ) $=
    ( wex wn wal df-ex con2bii ) ABCADBEABFG $.

  $( A utility theorem.  An interesting case is when the same formula is
     substituted for both ` ph ` and ` ps ` , since then both implications
     express a type of non-freeness.  See also ~ alimex .  (Contributed by BJ,
     12-May-2019.) $)
  eximal $p |- ( ( E. x ph -> ps ) <-> ( -. ps -> A. x -. ph ) ) $=
    ( wex wi wn wal df-ex imbi1i con1b bitri ) ACDZBEAFCGZFZBEBFMELNBACHIMBJK
    $.

  $c F/ $.  $( The not-free symbol. $)

  $( Extend wff definition to include the not-free predicate. $)
  wnf $a wff F/ x ph $.

  $( Define the not-free predicate for wffs.  This is read "" ` x ` is not free
     in ` ph ` "".  Not-free means that the value of ` x ` cannot affect the
     value of ` ph ` , e.g., any occurrence of ` x ` in ` ph ` is effectively
     bound by a ""for all"" or something that expands to one (such as ""there
     exists"").  In particular, substitution for a variable not free in a wff
     does not affect its value ( ~ sbf ).  An example of where this is used is
     ~ stdpc5 .  See ~ nf2 for an alternative definition which does not involve
     nested quantifiers on the same variable.

     Not-free is a commonly used constraint, so it is useful to have a notation
     for it.  Surprisingly, there is no common formal notation for it, so here
     we devise one.  Our definition lets us work with the not-free notion
     within the logic itself rather than as a metalogical side condition.

     To be precise, our definition really means ""effectively not free,"" because
     it is slightly less restrictive than the usual textbook definition for
     not-free (which only considers syntactic freedom).  For example, ` x ` is
     effectively not free in the bare expression ` x = x ` (see ~ nfequid ),
     even though ` x ` would be considered free in the usual textbook
     definition, because the value of ` x ` in the expression ` x = x ` cannot
     affect the truth of the expression (and thus substitution will not change
     the result).

     This predicate only applies to wffs.  See ~ df-nfc for a not-free
     predicate for class variables.  (Contributed by Mario Carneiro,
     11-Aug-2016.) $)
  df-nf $a |- ( F/ x ph <-> A. x ( ph -> A. x ph ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Rule scheme ax-gen (Generalization)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    ax-g.1 $e |- ph $.
    $( Rule of Generalization.  The postulated inference rule of predicate
       calculus.  See e.g.  Rule 2 of [Hamilton] p. 74.  This rule says that if
       something is unconditionally true, then it is true for all values of a
       variable.  For example, if we have proved ` x = x ` , we can conclude
       ` A. x x = x ` or even ` A. y x = x ` .  Theorem ~ allt shows the
       special case ` A. x T. ` .  Theorem ~ spi shows we can go the other way
       also: in other words we can add or remove universal quantifiers from the
       beginning of any theorem as required.  (Contributed by NM,
       3-Jan-1993.) $)
    ax-gen $a |- A. x ph $.
  $}

  ${
    gen2.1 $e |- ph $.
    $( Generalization applied twice.  (Contributed by NM, 30-Apr-1998.) $)
    gen2 $p |- A. x A. y ph $=
      ( wal ax-gen ) ACEBACDFF $.
  $}

  ${
    mpg.1 $e |- ( A. x ph -> ps ) $.
    mpg.2 $e |- ph $.
    $( Modus ponens combined with generalization.  (Contributed by NM,
       24-May-1994.) $)
    mpg $p |- ps $=
      ( wal ax-gen ax-mp ) ACFBACEGDH $.
  $}

  ${
    mpgbi.1 $e |- ( A. x ph <-> ps ) $.
    mpgbi.2 $e |- ph $.
    $( Modus ponens on biconditional combined with generalization.
       (Contributed by NM, 24-May-1994.)  (Proof shortened by Stefan Allan,
       28-Oct-2008.) $)
    mpgbi $p |- ps $=
      ( wal ax-gen mpbi ) ACFBACEGDH $.
  $}

  ${
    mpgbir.1 $e |- ( ph <-> A. x ps ) $.
    mpgbir.2 $e |- ps $.
    $( Modus ponens on biconditional combined with generalization.
       (Contributed by NM, 24-May-1994.)  (Proof shortened by Stefan Allan,
       28-Oct-2008.) $)
    mpgbir $p |- ph $=
      ( wal ax-gen mpbir ) ABCFBCEGDH $.
  $}

  ${
    nfi.1 $e |- ( ph -> A. x ph ) $.
    $( Deduce that ` x ` is not free in ` ph ` from the definition.
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfi $p |- F/ x ph $=
      ( wnf wal wi df-nf mpgbir ) ABDAABEFBABGCH $.
  $}

  ${
    hbth.1 $e |- ph $.
    $( No variable is (effectively) free in a theorem.

       This and later ""hypothesis-building"" lemmas, with labels starting
       ""hb..."", allow us to construct proofs of formulas of the form
       ` |- ( ph -> A. x ph ) ` from smaller formulas of this form.  These are
       useful for constructing hypotheses that state "" ` x ` is (effectively)
       not free in ` ph ` .""  (Contributed by NM, 11-May-1993.) $)
    hbth $p |- ( ph -> A. x ph ) $=
      ( wal ax-gen a1i ) ABDAABCEF $.

    $( No variable is (effectively) free in a theorem.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
    nfth $p |- F/ x ph $=
      ( hbth nfi ) ABABCDE $.
  $}

  $( The true constant has no free variables.  (This can also be proven in one
     step with ~ nfv , but this proof does not use ~ ax-5 .)  (Contributed by
     Mario Carneiro, 6-Oct-2016.) $)
  nftru $p |- F/ x T. $=
    ( wtru tru nfth ) BACD $.

  ${
    nex.1 $e |- -. ph $.
    $( Generalization rule for negated wff.  (Contributed by NM,
       18-May-1994.) $)
    nex $p |- -. E. x ph $=
      ( wn wex alnex mpgbi ) ADABEDBABFCG $.
  $}

  ${
    nfnth.1 $e |- -. ph $.
    $( No variable is (effectively) free in a non-theorem.  (Contributed by
       Mario Carneiro, 6-Dec-2016.) $)
    nfnth $p |- F/ x ph $=
      ( wal pm2.21i nfi ) ABAABDCEF $.
  $}

  $( The false constant has no free variables (see ~ nftru ).  (Contributed by
     BJ, 6-May-2019.) $)
  nffal $p |- F/ x F. $=
    ( wfal fal nfnth ) BACD $.

  ${
    sptruw.1 $e |- ph $.
    $( Version of ~ sp when ` ph ` is true.  Uses only Tarski's FOL axiom
       schemes.  (Contributed by NM, 23-Apr-2017.) $)
    sptruw $p |- ( A. x ph -> ph ) $=
      ( wal a1i ) AABDCE $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
         Axiom scheme ax-4 (Quantified Implication)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Quantified Implication.  Axiom C4 of [Monk2] p. 105 and Theorem
     19.20 of [Margaris] p. 90.  It is restated as ~ alim for labelling
     consistency.  It should be used only by ~ alim .  (Contributed by NM,
     21-May-2008.)  (New usage is discouraged.) $)
  ax-4 $a |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $.

  $( Restatement of Axiom ~ ax-4 , for labelling consistency.  It should be the
     only theorem using ~ ax-4 .  (Contributed by NM, 10-Jan-1993.) $)
  alim $p |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $=
    ( ax-4 ) ABCD $.

  ${
    alimi.1 $e |- ( ph -> ps ) $.
    $( Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 5-Jan-1993.) $)
    alimi $p |- ( A. x ph -> A. x ps ) $=
      ( wi wal alim mpg ) ABEACFBCFECABCGDH $.

    $( Inference doubly quantifying both antecedent and consequent.
       (Contributed by NM, 3-Feb-2005.) $)
    2alimi $p |- ( A. x A. y ph -> A. x A. y ps ) $=
      ( wal alimi ) ADFBDFCABDEGG $.
  $}

  $( Closed form of ~ al2imi .  Version of ~ ax-4 for a nested implication.
     (Contributed by Alan Sare, 31-Dec-2011.) $)
  al2im $p |- ( A. x ( ph -> ( ps -> ch ) ) ->
                                     ( A. x ph -> ( A. x ps -> A. x ch ) ) ) $=
    ( wi wal alim syl6 ) ABCEZEDFADFIDFBDFCDFEAIDGBCDGH $.

  ${
    al2imi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference quantifying antecedent, nested antecedent, and consequent.
       (Contributed by NM, 10-Jan-1993.) $)
    al2imi $p |- ( A. x ph -> ( A. x ps -> A. x ch ) ) $=
      ( wi wal al2im mpg ) ABCFFADGBDGCDGFFDABCDHEI $.
  $}

  ${
    alanimi.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Variant of ~ al2imi with conjunctive antecedent.  (Contributed by Andrew
       Salmon, 8-Jun-2011.) $)
    alanimi $p |- ( ( A. x ph /\ A. x ps ) -> A. x ch ) $=
      ( wal ex al2imi imp ) ADFBDFCDFABCDABCEGHI $.
  $}

  ${
    alimdh.1 $e |- ( ph -> A. x ph ) $.
    alimdh.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.20 of [Margaris] p. 90, see ~ alim .
       (Contributed by NM, 4-Jan-2002.) $)
    alimdh $p |- ( ph -> ( A. x ps -> A. x ch ) ) $=
      ( wal wi al2imi syl ) AADGBDGCDGHEABCDFIJ $.
  $}

  $( Theorem 19.15 of [Margaris] p. 90.  (Contributed by NM, 24-Jan-1993.) $)
  albi $p |- ( A. x ( ph <-> ps ) -> ( A. x ph <-> A. x ps ) ) $=
    ( wb wal bi1 al2imi bi2 impbid ) ABDZCEACEBCEJABCABFGJBACABHGI $.

  ${
    albii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding universal quantifier to both sides of an equivalence.
       (Contributed by NM, 7-Aug-1994.) $)
    albii $p |- ( A. x ph <-> A. x ps ) $=
      ( wb wal albi mpg ) ABEACFBCFECABCGDH $.

    $( Theorem albii is the congruence law for universal quantification. $)
    $( $j congruence 'albii'; $)

    $( Inference adding two universal quantifiers to both sides of an
       equivalence.  (Contributed by NM, 9-Mar-1997.) $)
    2albii $p |- ( A. x A. y ph <-> A. x A. y ps ) $=
      ( wal albii ) ADFBDFCABDEGG $.
  $}

  ${
    alrimih.1 $e |- ( ph -> A. x ph ) $.
    alrimih.2 $e |- ( ph -> ps ) $.
    $( Inference form of Theorem 19.21 of [Margaris] p. 90.  See ~ 19.21 and
       ~ 19.21h .  (Contributed by NM, 9-Jan-1993.) $)
    alrimih $p |- ( ph -> A. x ps ) $=
      ( wal alimi syl ) AACFBCFDABCEGH $.
  $}

  ${
    hbxfrbi.1 $e |- ( ph <-> ps ) $.
    hbxfrbi.2 $e |- ( ps -> A. x ps ) $.
    $( A utility lemma to transfer a bound-variable hypothesis builder into a
       definition.  See ~ hbxfreq for equality version.  (Contributed by
       Jonathan Ben-Naim, 3-Jun-2011.) $)
    hbxfrbi $p |- ( ph -> A. x ph ) $=
      ( wal albii 3imtr4i ) BBCFAACFEDABCDGH $.
  $}

  ${
    nfbii.1 $e |- ( ph <-> ps ) $.
    $( Equality theorem for not-free.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nfbii $p |- ( F/ x ph <-> F/ x ps ) $=
      ( wal wi wnf albii imbi12i df-nf 3bitr4i ) AACEZFZCEBBCEZFZCEACGBCGMOCABL
      NDABCDHIHACJBCJK $.

    ${
      nfxfr.2 $e |- F/ x ps $.
      $( A utility lemma to transfer a bound-variable hypothesis builder into a
         definition.  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
      nfxfr $p |- F/ x ph $=
        ( wnf nfbii mpbir ) ACFBCFEABCDGH $.
    $}

    ${
      nfxfrd.2 $e |- ( ch -> F/ x ps ) $.
      $( A utility lemma to transfer a bound-variable hypothesis builder into a
         definition.  (Contributed by Mario Carneiro, 24-Sep-2016.) $)
      nfxfrd $p |- ( ch -> F/ x ph ) $=
        ( wnf nfbii sylibr ) CBDGADGFABDEHI $.
    $}
  $}

  $( Theorem 19.6 of [Margaris] p. 89.  (Contributed by NM, 12-Mar-1993.) $)
  alex $p |- ( A. x ph <-> -. E. x -. ph ) $=
    ( wal wn wex notnot albii alnex bitri ) ABCADZDZBCJBEDAKBAFGJBHI $.

  $( Theorem 19.14 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
  exnal $p |- ( E. x -. ph <-> -. A. x ph ) $=
    ( wal wn wex alex con2bii ) ABCADBEABFG $.

  $( Part of theorem *11.5 in [WhiteheadRussell] p. 164.  (Contributed by
     Andrew Salmon, 24-May-2011.) $)
  2nalexn $p |- ( -. A. x A. y ph <-> E. x E. y -. ph ) $=
    ( wn wex wal df-ex alex albii xchbinxr bicomi ) ADCEZBEZACFZBFZDMLDZBFOLBGN
    PBACHIJK $.

  $( Theorem *11.22 in [WhiteheadRussell] p. 160.  (Contributed by Andrew
     Salmon, 24-May-2011.) $)
  2exnaln $p |- ( E. x E. y ph <-> -. A. x A. y -. ph ) $=
    ( wex wn wal df-ex alnex albii xchbinxr ) ACDZBDKEZBFAECFZBFKBGMLBACHIJ $.

  $( Theorem *11.25 in [WhiteheadRussell] p. 160.  (Contributed by Andrew
     Salmon, 24-May-2011.) $)
  2nexaln $p |- ( -. E. x E. y ph <-> A. x A. y -. ph ) $=
    ( wn wal wex 2exnaln bicomi con1bii ) ADCEBEZACFBFZKJDABCGHI $.

  $( A utility theorem.  An interesting case is when the same formula is
     substituted for both ` ph ` and ` ps ` , since then both implications
     express a type of non-freeness.  See also ~ eximal .  (Contributed by BJ,
     12-May-2019.) $)
  alimex $p |- ( ( ph -> A. x ps ) <-> ( E. x -. ps -> -. ph ) ) $=
    ( wal wi wn wex alex imbi2i con2b bitri ) ABCDZEABFCGZFZEMAFELNABCHIAMJK $.

  ${
    aleximi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A variant of ~ al2imi : instead of applying ` A. x ` quantifiers to the
       final implication, replace them with ` E. x ` .  A shorter proof is
       possible using ~ nfa1 , ~ sps and ~ eximd , but it depends on more
       axioms.  (Contributed by Wolf Lammen, 18-Aug-2019.) $)
    aleximi $p |- ( A. x ph -> ( E. x ps -> E. x ch ) ) $=
      ( wal wex wn con3d al2imi alnex 3imtr3g con4d ) ADFZCDGZBDGZNCHZDFBHZDFOH
      PHAQRDABCEIJCDKBDKLM $.
  $}

  $( Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM, 10-Jan-1993.)
     (Proof shortened by Wolf Lammen, 4-Jul-2014.) $)
  exim $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ps ) ) $=
    ( wi id aleximi ) ABDZABCGEF $.

  $( Obsolete proof of ~ exim as of 4-Sep-2019.  (Contributed by NM,
     5-Aug-1993.)  (Proof shortened by Wolf Lammen, 4-Jul-2014.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  eximOLD $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ps ) ) $=
    ( wi wal wex wn con3 al2imi alnex 3imtr3g con4d ) ABDZCEZBCFZACFZNBGZCEAGZC
    EOGPGMQRCABHIBCJACJKL $.

  ${
    eximi.1 $e |- ( ph -> ps ) $.
    $( Inference adding existential quantifier to antecedent and consequent.
       (Contributed by NM, 10-Jan-1993.) $)
    eximi $p |- ( E. x ph -> E. x ps ) $=
      ( wi wex exim mpg ) ABEACFBCFECABCGDH $.

    $( Inference adding two existential quantifiers to antecedent and
       consequent.  (Contributed by NM, 3-Feb-2005.) $)
    2eximi $p |- ( E. x E. y ph -> E. x E. y ps ) $=
      ( wex eximi ) ADFBDFCABDEGG $.
  $}

  ${
    eximii.1 $e |- E. x ph $.
    eximii.2 $e |- ( ph -> ps ) $.
    $( Inference associated with ~ eximi .  (Contributed by BJ, 3-Feb-2018.) $)
    eximii $p |- E. x ps $=
      ( wex eximi ax-mp ) ACFBCFDABCEGH $.
  $}

  ${
    aleximiOLD.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Obsolete proof of ~ aleximi as of 4-Sep-2019.  (Contributed by Wolf
       Lammen, 18-Aug-2019.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    aleximiOLD $p |- ( A. x ph -> ( E. x ps -> E. x ch ) ) $=
      ( wal wi wex alimi exim syl ) ADFBCGZDFBDHCDHGALDEIBCDJK $.
  $}

  $( Add an antecedent in a universally quantified formula.  (Contributed by
     BJ, 6-Oct-2018.) $)
  ala1 $p |- ( A. x ph -> A. x ( ps -> ph ) ) $=
    ( wi ax-1 alimi ) ABADCABEF $.

  $( Add an antecedent in an existentially quantified formula.  (Contributed by
     BJ, 6-Oct-2018.) $)
  exa1 $p |- ( E. x ph -> E. x ( ps -> ph ) ) $=
    ( wi ax-1 eximi ) ABADCABEF $.

  $( Theorem 19.38 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.)
     Allow a shortening of ~ 19.21t and ~ 19.23t .  (Revised by Wolf Lammen,
     2-Jan-2018.) $)
  19.38 $p |- ( ( E. x ph -> A. x ps ) -> A. x ( ph -> ps ) ) $=
    ( wex wal wi wn alnex pm2.21 alimi sylbir ala1 ja ) ACDZBCEABFZCEZNGAGZCEPA
    CHQOCABIJKBACLM $.

  $( A transformation of quantifiers and logical connectives.  (Contributed by
     NM, 19-Aug-1993.) $)
  alinexa $p |- ( A. x ( ph -> -. ps ) <-> -. E. x ( ph /\ ps ) ) $=
    ( wn wi wal wa wex imnan albii alnex bitri ) ABDEZCFABGZDZCFNCHDMOCABIJNCKL
    $.

  $( A relationship between two quantifiers and negation.  (Contributed by NM,
     18-Aug-1993.) $)
  alexn $p |- ( A. x E. y -. ph <-> -. E. x A. y ph ) $=
    ( wn wex wal exnal albii alnex bitri ) ADCEZBFACFZDZBFLBEDKMBACGHLBIJ $.

  $( Theorem *11.51 in [WhiteheadRussell] p. 164.  (Contributed by Andrew
     Salmon, 24-May-2011.)  (Proof shortened by Wolf Lammen, 25-Sep-2014.) $)
  2exnexn $p |- ( E. x A. y ph <-> -. A. x E. y -. ph ) $=
    ( wn wex wal alexn con2bii ) ADCEBFACFBEABCGH $.

  $( Theorem 19.18 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
  exbi $p |- ( A. x ( ph <-> ps ) -> ( E. x ph <-> E. x ps ) ) $=
    ( wb wal wex bi1 aleximi bi2 impbid ) ABDZCEACFBCFKABCABGHKBACABIHJ $.

  ${
    exbii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding existential quantifier to both sides of an
       equivalence.  (Contributed by NM, 24-May-1994.) $)
    exbii $p |- ( E. x ph <-> E. x ps ) $=
      ( wb wex exbi mpg ) ABEACFBCFECABCGDH $.
  $}

  ${
    2exbii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding two existential quantifiers to both sides of an
       equivalence.  (Contributed by NM, 16-Mar-1995.) $)
    2exbii $p |- ( E. x E. y ph <-> E. x E. y ps ) $=
      ( wex exbii ) ADFBDFCABDEGG $.
  $}

  ${
    3exbii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding 3 existential quantifiers to both sides of an
       equivalence.  (Contributed by NM, 2-May-1995.) $)
    3exbii $p |- ( E. x E. y E. z ph <-> E. x E. y E. z ps ) $=
      ( wex exbii 2exbii ) AEGBEGCDABEFHI $.
  $}

  $( A transformation of quantifiers and logical connectives.  (Contributed by
     NM, 25-Mar-1996.)  (Proof shortened by Wolf Lammen, 4-Sep-2014.) $)
  exanali $p |- ( E. x ( ph /\ -. ps ) <-> -. A. x ( ph -> ps ) ) $=
    ( wn wa wex wi wal annim exbii exnal bitri ) ABDEZCFABGZDZCFNCHDMOCABIJNCKL
    $.

  $( Commutation of conjunction inside an existential quantifier.  (Contributed
     by NM, 18-Aug-1993.) $)
  exancom $p |- ( E. x ( ph /\ ps ) <-> E. x ( ps /\ ph ) ) $=
    ( wa ancom exbii ) ABDBADCABEF $.

  ${
    alrimdh.1 $e |- ( ph -> A. x ph ) $.
    alrimdh.2 $e |- ( ps -> A. x ps ) $.
    alrimdh.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.21 of [Margaris] p. 90, see ~ 19.21 and
       ~ 19.21h .  (Contributed by NM, 10-Feb-1997.)  (Proof shortened by
       Andrew Salmon, 13-May-2011.) $)
    alrimdh $p |- ( ph -> ( ps -> A. x ch ) ) $=
      ( wal alimdh syl5 ) BBDHACDHFABCDEGIJ $.
  $}

  ${
    eximdh.1 $e |- ( ph -> A. x ph ) $.
    eximdh.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by NM,
       20-May-1996.) $)
    eximdh $p |- ( ph -> ( E. x ps -> E. x ch ) ) $=
      ( wal wex wi aleximi syl ) AADGBDHCDHIEABCDFJK $.
  $}

  ${
    nexdh.1 $e |- ( ph -> A. x ph ) $.
    nexdh.2 $e |- ( ph -> -. ps ) $.
    $( Deduction for generalization rule for negated wff.  (Contributed by NM,
       2-Jan-2002.) $)
    nexdh $p |- ( ph -> -. E. x ps ) $=
      ( wn wal wex alrimih alnex sylib ) ABFZCGBCHFALCDEIBCJK $.
  $}

  ${
    albidh.1 $e |- ( ph -> A. x ph ) $.
    albidh.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for universal quantifier (deduction rule).
       (Contributed by NM, 26-May-1993.) $)
    albidh $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $=
      ( wb wal alrimih albi syl ) ABCGZDHBDHCDHGALDEFIBCDJK $.
  $}

  ${
    exbidh.1 $e |- ( ph -> A. x ph ) $.
    exbidh.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for existential quantifier (deduction rule).
       (Contributed by NM, 26-May-1993.) $)
    exbidh $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $=
      ( wb wal wex alrimih exbi syl ) ABCGZDHBDICDIGAMDEFJBCDKL $.
  $}

  $( Simplification of an existentially quantified conjunction.  (Contributed
     by Rodolfo Medina, 25-Sep-2010.)  (Proof shortened by Andrew Salmon,
     29-Jun-2011.) $)
  exsimpl $p |- ( E. x ( ph /\ ps ) -> E. x ph ) $=
    ( wa simpl eximi ) ABDACABEF $.

  $( Simplification of an existentially quantified conjunction.  (Contributed
     by Rodolfo Medina, 25-Sep-2010.)  (Proof shortened by Andrew Salmon,
     29-Jun-2011.) $)
  exsimpr $p |- ( E. x ( ph /\ ps ) -> E. x ps ) $=
    ( wa simpr eximi ) ABDBCABEF $.

  $( Theorem 19.40 of [Margaris] p. 90.  (Contributed by NM, 26-May-1993.) $)
  19.40 $p |- ( E. x ( ph /\ ps ) -> ( E. x ph /\ E. x ps ) ) $=
    ( wa wex exsimpl exsimpr jca ) ABDCEACEBCEABCFABCGH $.

  $( Theorem 19.26 of [Margaris] p. 90.  Also Theorem *10.22 of
     [WhiteheadRussell] p. 147.  (Contributed by NM, 12-Mar-1993.)  (Proof
     shortened by Wolf Lammen, 4-Jul-2014.) $)
  19.26 $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ A. x ps ) ) $=
    ( wa wal simpl alimi simpr jca id alanimi impbii ) ABDZCEZACEZBCEZDNOPMACAB
    FGMBCABHGIABMCMJKL $.

  $( Theorem ~ 19.26 with two quantifiers.  (Contributed by NM, 3-Feb-2005.) $)
  19.26-2 $p |- ( A. x A. y ( ph /\ ps ) <->
                ( A. x A. y ph /\ A. x A. y ps ) ) $=
    ( wa wal 19.26 albii bitri ) ABEDFZCFADFZBDFZEZCFKCFLCFEJMCABDGHKLCGI $.

  $( Theorem ~ 19.26 with triple conjunction.  (Contributed by NM,
     13-Sep-2011.) $)
  19.26-3an $p |- ( A. x ( ph /\ ps /\ ch )
                   <-> ( A. x ph /\ A. x ps /\ A. x ch ) ) $=
    ( wa wal w3a 19.26 anbi1i bitri df-3an albii 3bitr4i ) ABEZCEZDFZADFZBDFZEZ
    CDFZEZABCGZDFQRTGPNDFZTEUANCDHUCSTABDHIJUBODABCKLQRTKM $.

  $( Theorem 19.29 of [Margaris] p. 90.  See also ~ 19.29r .  (Contributed by
     NM, 21-Jun-1993.)  (Proof shortened by Andrew Salmon, 13-May-2011.) $)
  19.29 $p |- ( ( A. x ph /\ E. x ps ) -> E. x ( ph /\ ps ) ) $=
    ( wal wex wa pm3.2 aleximi imp ) ACDBCEABFZCEABJCABGHI $.

  $( Variation of ~ 19.29 .  (Contributed by NM, 18-Aug-1993.) $)
  19.29r $p |- ( ( E. x ph /\ A. x ps ) -> E. x ( ph /\ ps ) ) $=
    ( wex wal wa 19.29 ancoms exancom sylibr ) ACDZBCEZFBAFCDZABFCDLKMBACGHABCI
    J $.

  $( Variation of ~ 19.29r with double quantification.  (Contributed by NM,
     3-Feb-2005.) $)
  19.29r2 $p |- ( ( E. x E. y ph /\ A. x A. y ps ) ->
             E. x E. y ( ph /\ ps ) ) $=
    ( wex wal wa 19.29r eximi syl ) ADEZCEBDFZCFGKLGZCEABGDEZCEKLCHMNCABDHIJ $.

  $( Variation of ~ 19.29 with mixed quantification.  (Contributed by NM,
     11-Feb-2005.) $)
  19.29x $p |- ( ( E. x A. y ph /\ A. x E. y ps ) ->
             E. x E. y ( ph /\ ps ) ) $=
    ( wal wex wa 19.29r 19.29 eximi syl ) ADEZCFBDFZCEGLMGZCFABGDFZCFLMCHNOCABD
    IJK $.

  $( Theorem 19.35 of [Margaris] p. 90.  This theorem is useful for moving an
     implication (in the form of the right-hand side) into the scope of a
     single existential quantifier.  (Contributed by NM, 12-Mar-1993.)  (Proof
     shortened by Wolf Lammen, 27-Jun-2014.) $)
  19.35 $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> E. x ps ) ) $=
    ( wi wex wal pm2.27 aleximi com12 wn exnal pm2.21 eximi sylbir exa1 impbii
    ja ) ABDZCEZACFZBCEZDTSUAARBCABGHITUASTJAJZCESACKUBRCABLMNBACOQP $.

  $( Obsolete proof of ~ 19.35 as of 4-Sep-2019.  (Contributed by NM,
     5-Aug-1993.)  (Proof shortened by Wolf Lammen, 27-Jun-2014.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  19.35OLD $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> E. x ps ) ) $=
    ( wi wex wal wn wa 19.26 annim albii alnex anbi2i 3bitr3i con4bii ) ABDZCEZ
    ACFZBCEZDZPGZCFZRSGZHZQGTGABGZHZCFRUECFZHUBUDAUECIUFUACABJKUGUCRBCLMNPCLRSJ
    NO $.

  ${
    19.35i.1 $e |- E. x ( ph -> ps ) $.
    $( Inference associated with ~ 19.35 .  (Contributed by NM,
       21-Jun-1993.) $)
    19.35i $p |- ( A. x ph -> E. x ps ) $=
      ( wi wex wal 19.35 mpbi ) ABECFACGBCFEDABCHI $.
  $}

  ${
    19.35ri.1 $e |- ( A. x ph -> E. x ps ) $.
    $( Inference associated with ~ 19.35 .  (Contributed by NM,
       12-Mar-1993.) $)
    19.35ri $p |- E. x ( ph -> ps ) $=
      ( wi wex wal 19.35 mpbir ) ABECFACGBCFEDABCHI $.
  $}

  $( Theorem 19.25 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
  19.25 $p |- ( A. y E. x ( ph -> ps ) ->
              ( E. y A. x ph -> E. y E. x ps ) ) $=
    ( wi wex wal 19.35 biimpi aleximi ) ABECFZACGZBCFZDKLMEABCHIJ $.

  $( Theorem 19.30 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.)
     (Proof shortened by Andrew Salmon, 25-May-2011.) $)
  19.30 $p |- ( A. x ( ph \/ ps ) -> ( A. x ph \/ E. x ps ) ) $=
    ( wo wal wex wn exnal pm2.53 aleximi syl5bir orrd ) ABDZCEZACEZBCFZOGAGZCFN
    PACHMQBCABIJKL $.

  $( Theorem 19.43 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.)
     (Proof shortened by Wolf Lammen, 27-Jun-2014.) $)
  19.43 $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ E. x ps ) ) $=
    ( wo wex wn wi wal df-or exbii 19.35 alnex imbi1i 3bitri bitr4i ) ABDZCEZAC
    EZFZBCEZGZRTDQAFZBGZCEUBCHZTGUAPUCCABIJUBBCKUDSTACLMNRTIO $.

  $( Obsolete proof of ~ 19.43 as of 3-May-2099.  Leave this in for the example
     on the ~ mmrecent.html page and in ~ conventions .  (Contributed by NM,
     5-Aug-1993.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  19.43OLD $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ E. x ps ) ) $=
    ( wo wn wal wex wa ioran albii 19.26 alnex anbi12i 3bitri notbii df-ex oran
    3bitr4i ) ABDZEZCFZEACGZEZBCGZEZHZESCGUBUDDUAUFUAAEZBEZHZCFUGCFZUHCFZHUFTUI
    CABIJUGUHCKUJUCUKUEACLBCLMNOSCPUBUDQR $.

  $( Theorem 19.33 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
  19.33 $p |- ( ( A. x ph \/ A. x ps ) -> A. x ( ph \/ ps ) ) $=
    ( wal wo orc alimi olc jaoi ) ACDABEZCDBCDAJCABFGBJCBAHGI $.

  $( The antecedent provides a condition implying the converse of ~ 19.33 .
     (Contributed by NM, 27-Mar-2004.)  (Proof shortened by Andrew Salmon,
     25-May-2011.)  (Proof shortened by Wolf Lammen, 5-Jul-2014.) $)
  19.33b $p |- ( -. ( E. x ph /\ E. x ps ) ->
               ( A. x ( ph \/ ps ) <-> ( A. x ph \/ A. x ps ) ) ) $=
    ( wex wa wn wo wal ianor alnex pm2.53 al2imi syl5bir olc syl6com orcomd ord
    wi 19.30 orc jaoi sylbi 19.33 impbid1 ) ACDZBCDZEFZABGZCHZACHZBCHZGZUGUEFZU
    FFZGUIULRZUEUFIUMUOUNUIUMUKULUMAFZCHUIUKACJUHUPBCABKLMUKUJNOUIUNUJULUIUFUJU
    IUJUFABCSPQUJUKTOUAUBABCUCUD $.

  $( Theorem *11.42 in [WhiteheadRussell] p. 163.  Theorem 19.40 of [Margaris]
     p. 90 with two quantifiers.  (Contributed by Andrew Salmon,
     24-May-2011.) $)
  19.40-2 $p |- ( E. x E. y ( ph /\ ps ) ->
        ( E. x E. y ph /\ E. x E. y ps ) ) $=
    ( wa wex 19.40 eximi syl ) ABEDFZCFADFZBDFZEZCFKCFLCFEJMCABDGHKLCGI $.

  $( The antecedent provides a condition implying the converse of ~ 19.40 .
     This is to ~ 19.40 what ~ 19.33b is to ~ 19.33 .  (Contributed by BJ,
     6-May-2019.) $)
  19.40b $p |- ( ( A. x ph \/ A. x ps ) ->
                          ( ( E. x ph /\ E. x ps ) <-> E. x ( ph /\ ps ) ) ) $=
    ( wal wo wex wa wi 19.29 adantld 19.29r expcom adantrd jaoi 19.40 impbid1
    ex ) ACDZBCDZEACFZBCFZGZABGCFZRUBUCHSRUAUCTRUAUCABCIQJSTUCUATSUCABCKLMNABCO
    P $.

  $( Split a biconditional and distribute quantifier.  (Contributed by NM,
     18-Aug-1993.) $)
  albiim $p |- ( A. x ( ph <-> ps ) <->
             ( A. x ( ph -> ps ) /\ A. x ( ps -> ph ) ) ) $=
    ( wb wal wi wa dfbi2 albii 19.26 bitri ) ABDZCEABFZBAFZGZCEMCENCEGLOCABHIMN
    CJK $.

  $( Split a biconditional and distribute two quantifiers.  (Contributed by NM,
     3-Feb-2005.) $)
  2albiim $p |- ( A. x A. y ( ph <-> ps ) <->
             ( A. x A. y ( ph -> ps ) /\ A. x A. y ( ps -> ph ) ) ) $=
    ( wb wal wi wa albiim albii 19.26 bitri ) ABEDFZCFABGDFZBAGDFZHZCFNCFOCFHMP
    CABDIJNOCKL $.

  $( Add/remove a conjunct in the scope of an existential quantifier.
     (Contributed by Raph Levien, 3-Jul-2006.) $)
  exintrbi $p |- ( A. x ( ph -> ps ) -> ( E. x ph <-> E. x ( ph /\ ps ) ) ) $=
    ( wi wal wa wb wex pm4.71 albii exbi sylbi ) ABDZCEAABFZGZCEACHNCHGMOCABIJA
    NCKL $.

  $( Introduce a conjunct in the scope of an existential quantifier.
     (Contributed by NM, 11-Aug-1993.) $)
  exintr $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ( ph /\ ps ) ) ) $=
    ( wi wal wex wa exintrbi biimpd ) ABDCEACFABGCFABCHI $.

  $( Theorem *10.3 in [WhiteheadRussell] p. 150.  (Contributed by Andrew
     Salmon, 8-Jun-2011.) $)
  alsyl $p |- ( ( A. x ( ph -> ps ) /\ A. x ( ps -> ch ) ) ->
        A. x ( ph -> ch ) ) $=
    ( wi pm3.33 alanimi ) ABEBCEACEDABCFG $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Axiom scheme ax-5 (Distinctness) - first use of $d
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x ph $.
    $( Axiom of Distinctness.  This axiom quantifies a variable over a formula
       in which it does not occur.  Axiom C5 in [Megill] p. 444 (p. 11 of the
       preprint).  Also appears as Axiom B6 (p. 75) of system S2 of [Tarski]
       p. 77 and Axiom C5-1 of [Monk2] p. 113.

       (See comments in ~ ax5ALT about the logical redundancy of ~ ax-5 in the
       presence of our obsolete axioms.)

       This axiom essentially says that if ` x ` does not occur in ` ph ` ,
       i.e. ` ph ` does not depend on ` x ` in any way, then we can add the
       quantifier ` A. x ` to ` ph ` with no further assumptions.  By ~ sp , we
       can also remove the quantifier (unconditionally).  (Contributed by NM,
       10-Jan-1993.) $)
    ax-5 $a |- ( ph -> A. x ph ) $.
  $}

  ${
    $d x ps $.
    $( ~ ax-5 with antecedent.  Useful in proofs of deduction versions of
       bound-variable hypothesis builders.  (Contributed by NM, 1-Mar-2013.) $)
    ax5d $p |- ( ph -> ( ps -> A. x ps ) ) $=
      ( wal wi ax-5 a1i ) BBCDEABCFG $.
  $}

  ${
    $d x ph $.
    $( A rephrasing of ~ ax-5 using the existential quantifier.  (Contributed
       by Wolf Lammen, 4-Dec-2017.) $)
    ax5e $p |- ( E. x ph -> ph ) $=
      ( wex wi wn wal ax-5 eximal mpbir ) ABCADAEZJBFDJBGAABHI $.
  $}

  ${
    $d x ph $.
    $( If ` x ` is not present in ` ph ` , then ` x ` is not free in ` ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfv $p |- F/ x ph $=
      ( ax-5 nfi ) ABABCD $.
  $}

  ${
    $d x ps $.
    $( ~ nfv with antecedent.  Useful in proofs of deduction versions of
       bound-variable hypothesis builders such as ~ nfimd .  (Contributed by
       Mario Carneiro, 6-Oct-2016.) $)
    nfvd $p |- ( ph -> F/ x ps ) $=
      ( wnf nfv a1i ) BCDABCEF $.
  $}

  ${
    $d x ph $.
    alimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.20 of [Margaris] p. 90, see ~ alim .
       (Contributed by NM, 3-Apr-1994.) $)
    alimdv $p |- ( ph -> ( A. x ps -> A. x ch ) ) $=
      ( ax-5 alimdh ) ABCDADFEG $.

    $( Deduction form of Theorem 19.22 of [Margaris] p. 90, see ~ exim .
       (Contributed by NM, 27-Apr-1994.) $)
    eximdv $p |- ( ph -> ( E. x ps -> E. x ch ) ) $=
      ( ax-5 eximdh ) ABCDADFEG $.
  $}

  ${
    $d x ph $.  $d y ph $.
    2alimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.20 of [Margaris] p. 90 with two
       quantifiers, see ~ alim .  (Contributed by NM, 27-Apr-2004.) $)
    2alimdv $p |- ( ph -> ( A. x A. y ps -> A. x A. y ch ) ) $=
      ( wal alimdv ) ABEGCEGDABCEFHH $.

    $( Deduction form of Theorem 19.22 of [Margaris] p. 90 with two
       quantifiers, see ~ exim .  (Contributed by NM, 3-Aug-1995.) $)
    2eximdv $p |- ( ph -> ( E. x E. y ps -> E. x E. y ch ) ) $=
      ( wex eximdv ) ABEGCEGDABCEFHH $.
  $}

  ${
    $d x ph $.
    albidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for universal quantifier (deduction rule).
       (Contributed by NM, 26-May-1993.) $)
    albidv $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $=
      ( ax-5 albidh ) ABCDADFEG $.

    $( Formula-building rule for existential quantifier (deduction rule).
       (Contributed by NM, 26-May-1993.) $)
    exbidv $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $=
      ( ax-5 exbidh ) ABCDADFEG $.
  $}

  ${
    $d x ph $.  $d y ph $.
    2albidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for 2 universal quantifiers (deduction rule).
       (Contributed by NM, 4-Mar-1997.) $)
    2albidv $p |- ( ph -> ( A. x A. y ps <-> A. x A. y ch ) ) $=
      ( wal albidv ) ABEGCEGDABCEFHH $.

    $( Formula-building rule for 2 existential quantifiers (deduction rule).
       (Contributed by NM, 1-May-1995.) $)
    2exbidv $p |- ( ph -> ( E. x E. y ps <-> E. x E. y ch ) ) $=
      ( wex exbidv ) ABEGCEGDABCEFHH $.
  $}

  ${
    $d x ph $.  $d y ph $.  $d z ph $.
    3exbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for 3 existential quantifiers (deduction rule).
       (Contributed by NM, 1-May-1995.) $)
    3exbidv $p |- ( ph -> ( E. x E. y E. z ps <-> E. x E. y E. z ch ) ) $=
      ( wex exbidv 2exbidv ) ABFHCFHDEABCFGIJ $.
  $}

  ${
    $d x ph $.  $d y ph $.  $d z ph $.  $d w ph $.
    4exbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for 4 existential quantifiers (deduction rule).
       (Contributed by NM, 3-Aug-1995.) $)
    4exbidv $p |- ( ph ->
                     ( E. x E. y E. z E. w ps <-> E. x E. y E. z E. w ch ) ) $=
      ( wex 2exbidv ) ABGIFICGIFIDEABCFGHJJ $.
  $}

  ${
    $d x ph $.
    alrimiv.1 $e |- ( ph -> ps ) $.
    $( Inference form of Theorem 19.21 of [Margaris] p. 90.  See ~ 19.21 and
       ~ 19.21v .  (Contributed by NM, 21-Jun-1993.) $)
    alrimiv $p |- ( ph -> A. x ps ) $=
      ( ax-5 alrimih ) ABCACEDF $.
  $}

  ${
    $d x ph $.  $d y ph $.
    alrimivv.1 $e |- ( ph -> ps ) $.
    $( Inference form of Theorem 19.21 of [Margaris] p. 90.  See ~ 19.21 and
       ~ 19.21v .  (Contributed by NM, 31-Jul-1995.) $)
    alrimivv $p |- ( ph -> A. x A. y ps ) $=
      ( wal alrimiv ) ABDFCABDEGG $.
  $}

  ${
    $d x ph $.  $d x ps $.
    alrimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.21 of [Margaris] p. 90.  See ~ 19.21 and
       ~ 19.21v .  (Contributed by NM, 10-Feb-1997.) $)
    alrimdv $p |- ( ph -> ( ps -> A. x ch ) ) $=
      ( ax-5 alrimdh ) ABCDADFBDFEG $.
  $}

  ${
    $d x ps $.
    exlimiv.1 $e |- ( ph -> ps ) $.
    $( Inference form of Theorem 19.23 of [Margaris] p. 90, see ~ 19.23 .

       See ~ exlimi for a more general version requiring more axioms.

       This inference, along with its many variants such as ~ rexlimdv , is
       used to implement a metatheorem called ""Rule C"" that is given in many
       logic textbooks.  See, for example, Rule C in [Mendelson] p. 81, Rule C
       in [Margaris] p. 40, or Rule C in Hirst and Hirst's _A Primer for Logic
       and Proof_ p. 59 (PDF p. 65) at
       ~ http://www.appstate.edu/~~hirstjl/primer/hirst.pdf .  In informal
       proofs, the statement ""Let ` C ` be an element such that..."" almost
       always means an implicit application of Rule C.

       In essence, Rule C states that if we can prove that some element ` x `
       exists satisfying a wff, i.e. ` E. x ph ( x ) ` where ` ph ( x ) ` has
       ` x ` free, then we can use ` ph ( C ) ` as a hypothesis for the proof
       where ` C ` is a new (fictitious) constant not appearing previously in
       the proof, nor in any axioms used, nor in the theorem to be proved.  The
       purpose of Rule C is to get rid of the existential quantifier.

       We cannot do this in Metamath directly.  Instead, we use the original
       ` ph ` (containing ` x ` ) as an antecedent for the main part of the
       proof.  We eventually arrive at ` ( ph -> ps ) ` where ` ps ` is the
       theorem to be proved and does not contain ` x ` .  Then we apply
       ~ exlimiv to arrive at ` ( E. x ph -> ps ) ` .  Finally, we separately
       prove ` E. x ph ` and detach it with modus ponens ~ ax-mp to arrive at
       the final theorem ` ps ` .  (Contributed by NM, 21-Jun-1993.)  Remove
       dependencies on ~ ax-6 and ~ ax-8 .  (Revised by Wolf Lammen,
       4-Dec-2017.) $)
    exlimiv $p |- ( E. x ph -> ps ) $=
      ( wex eximi ax5e syl ) ACEBCEBABCDFBCGH $.
  $}

  ${
    $d x ps $.  $d y ps $.
    exlimivv.1 $e |- ( ph -> ps ) $.
    $( Inference form of Theorem 19.23 of [Margaris] p. 90, see ~ 19.23 .
       (Contributed by NM, 1-Aug-1995.) $)
    exlimivv $p |- ( E. x E. y ph -> ps ) $=
      ( wex exlimiv ) ADFBCABDEGG $.
  $}

  ${
    $d x ch $.  $d x ph $.
    exlimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.23 of [Margaris] p. 90, see ~ 19.23 .
       (Contributed by NM, 27-Apr-1994.)  Remove dependencies on ~ ax-6 ,
       ~ ax-7 .  (Revised by Wolf Lammen, 4-Dec-2017.) $)
    exlimdv $p |- ( ph -> ( E. x ps -> ch ) ) $=
      ( wex eximdv ax5e syl6 ) ABDFCDFCABCDEGCDHI $.
  $}

  ${
    $d x ch $.  $d x ph $.  $d y ch $.  $d y ph $.
    exlimdvv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.23 of [Margaris] p. 90, see ~ 19.23 .
       (Contributed by NM, 31-Jul-1995.) $)
    exlimdvv $p |- ( ph -> ( E. x E. y ps -> ch ) ) $=
      ( wex exlimdv ) ABEGCDABCEFHH $.
  $}

  ${
    $d x ch $.  $d x ph $.
    exlimddv.1 $e |- ( ph -> E. x ps ) $.
    exlimddv.2 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Existential elimination rule of natural deduction.  (Contributed by
       Mario Carneiro, 15-Jun-2016.) $)
    exlimddv $p |- ( ph -> ch ) $=
      ( wex ex exlimdv mpd ) ABDGCEABCDABCFHIJ $.
  $}

  ${
    $d x ph $.
    nfdv.1 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Apply the definition of not-free in a context.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
    nfdv $p |- ( ph -> F/ x ps ) $=
      ( wal wi wnf alrimiv df-nf sylibr ) ABBCEFZCEBCGAKCDHBCIJ $.
  $}

  ${
    $d x ph $.  $d y ph $.
    $( Quantification of two variables over a formula in which they do not
       occur.  (Contributed by Alan Sare, 12-Apr-2011.) $)
    2ax5 $p |- ( ph -> A. x A. y ph ) $=
      ( id alrimivv ) AABCADE $.
  $}

  ${
    $d x ph $.
    $( Version of ~ 19.21 with a dv condition.

       _Notational convention_:  We sometimes suffix with ""v"" the label of a
       theorem using a distinct variable (""dv"") condition instead of a
       non-freeness hypothesis such as ` F/ x ph ` .  Conversely, we sometimes
       suffix with ""f"" the label of a theorem introducing such a non-freeness
       hypothesis (""f"" stands for ""not free in"", see ~ df-nf ) instead of a dv
       condition.  For instance, ~ 19.21v versus ~ 19.21 and ~ vtoclf versus
       ~ vtocl .  Note that ""not free in"" is less restrictive than ""does not
       occur in.""  Note that the version with a dv condition is easily proved
       from the version with the corresponding non-freeness hypothesis, by
       using ~ nfv .  However, the dv version can often be proved from fewer
       axioms.  (Contributed by NM, 21-Jun-1993.)  Reduce dependencies on
       axioms.  (Revised by Wolf Lammen, 2-Jan-2020.) $)
    19.21v $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $=
      ( wi wal ax-5 alim syl5 wex ax5e imim1i 19.38 syl impbii ) ABDCEZABCEZDZA
      ACEOPACFABCGHQACIZPDORAPACJKABCLMN $.
  $}

  ${
    $d x ph $.
    $( Version of ~ 19.32 with a dv condition, requiring fewer axioms.
       (Contributed by BJ, 7-Mar-2020.) $)
    19.32v $p |- ( A. x ( ph \/ ps ) <-> ( ph \/ A. x ps ) ) $=
      ( wn wi wal wo 19.21v df-or albii 3bitr4i ) ADZBEZCFLBCFZEABGZCFANGLBCHOM
      CABIJANIK $.
  $}

  ${
    $d x ps $.
    $( Version of ~ 19.31 with a dv condition, requiring fewer axioms.
       (Contributed by BJ, 7-Mar-2020.) $)
    19.31v $p |- ( A. x ( ph \/ ps ) <-> ( A. x ph \/ ps ) ) $=
      ( wo wal 19.32v orcom albii 3bitr4i ) BADZCEBACEZDABDZCEKBDBACFLJCABGHKBG
      I $.
  $}

  ${
    $d x ph $.
    $( Version of ~ stdpc5 with a dv condition, requiring fewer axioms.
       (Contributed by BJ, 7-Mar-2020.) $)
    stdpc5v $p |- ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) ) $=
      ( wi wal 19.21v biimpi ) ABDCEABCEDABCFG $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Equality predicate (continued)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  The equality predicate was introduced above in ~ wceq for use by ~ df-tru .
  See the comments in that section.  In this section, we continue with the
  first ""real"" use of it.
$)

  $( Extend wff definition to include atomic formulas using the equality
     predicate.

     (Instead of introducing ~ weq as an axiomatic statement, as was done in an
     older version of this database, we introduce it by ""proving"" a special
     case of set theory's more general ~ wceq .  This lets us avoid overloading
     the ` = ` connective, thus preventing ambiguity that would complicate
     certain Metamath parsers.  However, logically ~ weq is considered to be a
     primitive syntax, even though here it is artificially ""derived"" from
     ~ wceq .  Note:  To see the proof steps of this syntax proof, type ""show
     proof weq /all"" in the Metamath program.)  (Contributed by NM,
     24-Jan-2006.) $)
  weq $p wff x = y $=
    ( cv wceq ) ACBCD $.

  $( Lemma used in proofs of substitution properties.  (Contributed by NM,
     10-May-1993.) $)
  equs3 $p |- ( E. x ( x = y /\ ph ) <-> -. A. x ( x = y -> -. ph ) ) $=
    ( weq wn wi wal wa wex alinexa con2bii ) BCDZAEFBGLAHBILABJK $.

  ${
    speimfw.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Specialization, with additional weakening (compared to ~ 19.2 ) to allow
       bundling of ` x ` and ` y ` .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 23-Apr-2017.)  (Proof shortened by Wolf Lammen,
       5-Dec-2017.) $)
    speimfw $p |- ( -. A. x -. x = y -> ( A. x ph -> E. x ps ) ) $=
      ( weq wn wal wex df-ex biimpri com12 aleximi syl5com ) CDFZGCHGZOCIZACHBC
      IQPOCJKAOBCOABELMN $.

    $( Obsolete proof of ~ speimfw as of 5-Dec-2019.  (Contributed by NM,
       23-Apr-2017.)  (Proof shortened by Wolf Lammen, 5-Aug-2017.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    speimfwOLD $p |- ( -. A. x -. x = y -> ( A. x ph -> E. x ps ) ) $=
      ( weq wex wi wn wal eximi df-ex 19.35 3imtr3i ) CDFZCGABHZCGOICJIACJBCGHO
      PCEKOCLABCMN $.
  $}

  ${
    spimfw.1 $e |- ( -. ps -> A. x -. ps ) $.
    spimfw.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Specialization, with additional weakening (compared to ~ sp ) to allow
       bundling of ` x ` and ` y ` .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 23-Apr-2017.)  (Proof shortened by Wolf Lammen,
       7-Aug-2017.) $)
    spimfw $p |- ( -. A. x -. x = y -> ( A. x ph -> ps ) ) $=
      ( weq wn wal wex speimfw df-ex con1i sylbi syl6 ) CDGHCIHACIBCJZBABCDFKPB
      HCIZHBBCLBQEMNO $.
  $}

  ${
    ax12i.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    ax12i.2 $e |- ( ps -> A. x ps ) $.
    $( Inference that has ~ ax-12 (without ` A. y ` ) as its conclusion.  Uses
       only Tarski's FOL axiom schemes.  The hypotheses may be eliminable
       without one or more of these axioms in special cases.  Proof similar to
       Lemma 16 of [Tarski] p. 70.  (Contributed by NM, 20-May-2008.) $)
    ax12i $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      ( weq wi wal biimprcd alrimih syl6bi ) CDGZABMAHZCIEBNCFMABEJKL $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Define proper substitution
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c [ $. $( Left bracket $)
  $c / $. $( Slash. $)
  $c ] $.  $( Right bracket $)

  $( Extend wff definition to include proper substitution (read ""the wff that
     results when ` y ` is properly substituted for ` x ` in wff ` ph ` "").
     (Contributed by NM, 24-Jan-2006.) $)
  wsb $a wff [ y / x ] ph $.

  $( Indicate that the variable ""y"" is free in wsb even though it could
     potentially bind occurrences in ""ph"". $)
  $( $j free_var 'wsb' with 'y'; $)

  $( Define proper substitution.  Remark 9.1 in [Megill] p. 447 (p. 15 of the
     preprint).  For our notation, we use ` [ y / x ] ph ` to mean ""the wff
     that results from the proper substitution of ` y ` for ` x ` in the wff
     ` ph ` .""  That is, ` y ` properly replaces ` x ` .  For example,
     ` [ x / y ] z e. y ` is the same as ` z e. x ` , as shown in ~ elsb4 .  We
     can also use ` [ y / x ] ph ` in place of the ""free for"" side condition
     used in traditional predicate calculus; see, for example, ~ stdpc4 .

     Our notation was introduced in Haskell B. Curry's _Foundations of
     Mathematical Logic_ (1977), p. 316 and is frequently used in textbooks of
     lambda calculus and combinatory logic.  This notation improves the common
     but ambiguous notation, "" ` ph ( y ) ` is the wff that results when ` y `
     is properly substituted for ` x ` in ` ph ( x ) ` .""  For example, if the
     original ` ph ( x ) ` is ` x = y ` , then ` ph ( y ) ` is ` y = y ` , from
     which we obtain that ` ph ( x ) ` is ` x = x ` .  So what exactly does
     ` ph ( x ) ` mean?  Curry's notation solves this problem.

     In most books, proper substitution has a somewhat complicated recursive
     definition with multiple cases based on the occurrences of free and bound
     variables in the wff.  Instead, we use a single formula that is exactly
     equivalent and gives us a direct definition.  We later prove that our
     definition has the properties we expect of proper substitution (see
     theorems ~ sbequ , ~ sbcom2 and ~ sbid2v ).

     Note that our definition is valid even when ` x ` and ` y ` are replaced
     with the same variable, as ~ sbid shows.  We achieve this by having ` x `
     free in the first conjunct and bound in the second.  We can also achieve
     this by using a dummy variable, as the alternate definition ~ dfsb7 shows
     (which some logicians may prefer because it doesn't mix free and bound
     variables).  Another version that mixes free and bound variables is
     ~ dfsb3 .  When ` x ` and ` y ` are distinct, we can express proper
     substitution with the simpler expressions of ~ sb5 and ~ sb6 .

     There are no restrictions on any of the variables, including what
     variables may occur in wff ` ph ` .  (Contributed by NM, 10-May-1993.) $)
  df-sb $a |- ( [ y / x ] ph <->
              ( ( x = y -> ph ) /\ E. x ( x = y /\ ph ) ) ) $.

  $( An equality theorem for substitution.  (Contributed by NM, 16-May-1993.)
     (Proof shortened by Wolf Lammen, 25-Feb-2018.) $)
  sbequ2 $p |- ( x = y -> ( [ y / x ] ph -> ph ) ) $=
    ( wsb weq wi wa wex df-sb simplbi com12 ) ABCDZBCEZALMAFMAGBHABCIJK $.

  $( One direction of a simplified definition of substitution.  The converse
     requires either a dv condition ( ~ sb5 ) or a non-freeness hypothesis
     ( ~ sb5f ).  (Contributed by NM, 13-May-1993.) $)
  sb1 $p |- ( [ y / x ] ph -> E. x ( x = y /\ ph ) ) $=
    ( wsb weq wi wa wex df-sb simprbi ) ABCDBCEZAFKAGBHABCIJ $.

  $( A specialization theorem.  (Contributed by NM, 29-Jun-1993.)  (Proof
     shortened by Wolf Lammen, 3-May-2018.) $)
  spsbe $p |- ( [ y / x ] ph -> E. x ph ) $=
    ( wsb weq wa wex sb1 exsimpr syl ) ABCDBCEZAFBGABGABCHKABIJ $.

  $( Elimination of equality from antecedent after substitution.  (Contributed
     by NM, 5-Aug-1993.)  Reduce dependencies on axioms.  (Revised by Wolf
     Lammen, 28-Jul-2018.) $)
  sbequ8 $p |- ( [ y / x ] ph <-> [ y / x ] ( x = y -> ph ) ) $=
    ( weq wi wa wex wsb pm5.4 bicomi abai exbii anbi12i df-sb 3bitr4i ) BCDZAEZ
    PAFZBGZFPQEZPQFZBGZFABCHQBCHQTSUBTQPAIJRUABPAKLMABCNQBCNO $.

  ${
    sbimi.1 $e |- ( ph -> ps ) $.
    $( Infer substitution into antecedent and consequent of an implication.
       (Contributed by NM, 25-Jun-1998.) $)
    sbimi $p |- ( [ y / x ] ph -> [ y / x ] ps ) $=
      ( weq wi wa wex wsb imim2i anim2i eximi anim12i df-sb 3imtr4i ) CDFZAGZQA
      HZCIZHQBGZQBHZCIZHACDJBCDJRUATUCABQEKSUBCABQELMNACDOBCDOP $.
  $}

  ${
    sbbii.1 $e |- ( ph <-> ps ) $.
    $( Infer substitution into both sides of a logical equivalence.
       (Contributed by NM, 14-May-1993.) $)
    sbbii $p |- ( [ y / x ] ph <-> [ y / x ] ps ) $=
      ( wsb biimpi sbimi biimpri impbii ) ACDFBCDFABCDABEGHBACDABEIHJ $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Axiom scheme ax-6 (Existence)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Existence.  One of the equality and substitution axioms of
     predicate calculus with equality.  This axiom tells us is that at least
     one thing exists.  In this form (not requiring that ` x ` and ` y ` be
     distinct) it was used in an axiom system of Tarski (see Axiom B7' in
     footnote 1 of [KalishMontague] p. 81.)  It is equivalent to axiom scheme
     C10' in [Megill] p. 448 (p. 16 of the preprint); the equivalence is
     established by ~ axc10 and ~ ax6fromc10 .  A more convenient form of this
     axiom is ~ ax6e , which has additional remarks.

     Raph Levien proved the independence of this axiom from the other logical
     axioms on 12-Apr-2005.  See item 16 at
     ~ http://us.metamath.org/award2003.html .

     ~ ax-6 can be proved from the weaker version ~ ax6v requiring that the
     variables be distinct; see theorem ~ ax6 .

     ~ ax-6 can also be proved from the Axiom of Separation (in the form that
     we use that axiom, where free variables are not universally quantified).
     See theorem ~ ax6vsep .

     Except by ~ ax6v , this axiom should not be referenced directly.  Instead,
     use theorem ~ ax6 .  (Contributed by NM, 10-Jan-1993.)
     (New usage is discouraged.) $)
  ax-6 $a |- -. A. x -. x = y $.

  ${
    $d x y $.
    $( Axiom B7 of [Tarski] p. 75, which requires that ` x ` and ` y ` be
       distinct.  This trivial proof is intended merely to weaken axiom ~ ax-6
       by adding a distinct variable restriction.  From here on, ~ ax-6 should
       not be referenced directly by any other proof, so that theorem ~ ax6
       will show that we can recover ~ ax-6 from this weaker version if it were
       an axiom (as it is in the case of Tarski).

       Note:  Introducing ` x , y ` as a distinct variable group ""out of the
       blue"" with no apparent justification has puzzled some people, but it is
       perfectly sound.  All we are doing is adding an additional redundant
       requirement, no different from adding a redundant logical hypothesis,
       that results in a weakening of the theorem.  This means that any
       _future_ theorem that references ~ ax6v must have a $d specified for the
       two variables that get substituted for ` x ` and ` y ` .  The $d does
       not propagate ""backwards"" i.e. it does not impose a requirement on
       ~ ax-6 .

       When possible, use of this theorem rather than ~ ax6 is preferred since
       its derivation is much shorter and requires fewer axioms.  (Contributed
       by NM, 7-Aug-2015.) $)
    ax6v $p |- -. A. x -. x = y $=
      ( ax-6 ) ABC $.
  $}

  ${
    $d x y $.
    $( At least one individual exists.  Weaker version of ~ ax6e .  When
       possible, use of this theorem rather than ~ ax6e is preferred since its
       derivation is much shorter and requires fewer axioms.  (Contributed by
       NM, 3-Aug-2017.) $)
    ax6ev $p |- E. x x = y $=
      ( weq wex wn wal ax6v df-ex mpbir ) ABCZADJEAFEABGJAHI $.
  $}

  ${
    $d x y $.
    exiftru.1 $e |- ph $.
    $( A companion rule to ax-gen, valid only if an individual exists.  Unlike
       ~ ax-6 , it does not require equality on its interface.  Some
       fundamental theorems of predicate logic can be proven from ~ ax-gen ,
       ~ ax-4 and this theorem alone, not requiring ~ ax-7 or excessive
       distinct variable conditions.  (Contributed by Wolf Lammen,
       12-Nov-2017.)  (Proof shortened by Wolf Lammen, 9-Dec-2017.) $)
    exiftru $p |- E. x ph $=
      ( vy weq ax6ev a1i eximii ) BDEZABBDFAICGH $.
  $}

  $( Theorem 19.2 of [Margaris] p. 89.  Note:  This proof is very different
     from Margaris' because we only have Tarski's FOL axiom schemes available
     at this point.  See the later ~ 19.2g for a more conventional proof of a
     more general result, which uses additional axioms.  (Contributed by NM,
     2-Aug-2017.)  Remove dependency on ~ ax-7 .  (Revised by Wolf Lammen,
     4-Dec-2017.) $)
  19.2 $p |- ( A. x ph -> E. x ph ) $=
    ( wi id exiftru 19.35i ) AABAACBADEF $.

  ${
    19.8w.1 $e |- ( ph -> A. x ph ) $.
    $( Weak version of ~ 19.8a .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 1-Aug-2017.)  (Proof shortened by Wolf Lammen,
       4-Dec-2017.) $)
    19.8w $p |- ( ph -> E. x ph ) $=
      ( wal wex 19.2 syl ) AABDABECABFG $.
  $}

  ${
    $d x ph $.
    $( Version of ~ 19.8a with a dv condition, requiring fewer axioms.
       (Contributed by BJ, 12-Mar-2020.) $)
    19.8v $p |- ( ph -> E. x ph ) $=
      ( ax-5 19.8w ) ABABCD $.

    $( Version of ~ 19.9 with a dv condition, requiring fewer axioms.  Any
       formula can be existentially quantified using a variable which it does
       not contain.  See also ~ 19.3v .  (Contributed by NM, 28-May-1995.)
       Remove dependency on ~ ax-7 .  (Revised by Wolf Lammen, 4-Dec-2017.) $)
    19.9v $p |- ( E. x ph <-> ph ) $=
      ( wex ax5e 19.8v impbii ) ABCAABDABEF $.

    $( Version of ~ 19.3 with a dv condition, requiring fewer axioms.  Any
       formula can be universally quantified using a variable which it does not
       contain.  See also ~ 19.9v .  (Contributed by Anthony Hart,
       13-Sep-2011.)  Remove dependency on ~ ax-7 .  (Revised by Wolf Lammen,
       4-Dec-2017.) $)
    19.3v $p |- ( A. x ph <-> ph ) $=
      ( wal wn wex alex 19.9v con2bii bitr4i ) ABCADZBEZDAABFKAJBGHI $.

    $( Version of ~ sp when ` x ` does not occur in ` ph ` .  This provides the
       other direction of ~ ax-5 .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 10-Apr-2017.)  (Proof shortened by Wolf Lammen,
       4-Dec-2017.) $)
    spvw $p |- ( A. x ph -> ph ) $=
      ( wal 19.3v biimpi ) ABCAABDE $.
  $}

  $( Theorem 19.39 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
  19.39 $p |- ( ( E. x ph -> E. x ps ) -> E. x ( ph -> ps ) ) $=
    ( wex wi wal 19.2 imim1i 19.35 sylibr ) ACDZBCDZEACFZLEABECDMKLACGHABCIJ $.

  $( Theorem 19.24 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
  19.24 $p |- ( ( A. x ph -> A. x ps ) -> E. x ( ph -> ps ) ) $=
    ( wal wi wex 19.2 imim2i 19.35 sylibr ) ACDZBCDZEKBCFZEABECFLMKBCGHABCIJ $.

  $( Theorem 19.34 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
  19.34 $p |- ( ( A. x ph \/ E. x ps ) -> E. x ( ph \/ ps ) ) $=
    ( wal wex wo 19.2 orim1i 19.43 sylibr ) ACDZBCEZFACEZLFABFCEKMLACGHABCIJ $.

  ${
    $d x ps $.
    $( Version of ~ 19.23 with a dv condition instead of a non-freeness
       hypothesis.  (Contributed by NM, 28-Jun-1998.)  Reduce dependencies on
       axioms.  (Revised by Wolf Lammen, 11-Jan-2020.) $)
    19.23v $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $=
      ( wi wal wex exim 19.9v syl6ib ax-5 imim2i 19.38 syl impbii ) ABDCEZACFZB
      DZOPBCFBABCGBCHIQPBCEZDOBRPBCJKABCLMN $.
  $}

  ${
    $d x ps $.  $d y ps $.
    $( Theorem ~ 19.23v extended to two variables.  (Contributed by NM,
       10-Aug-2004.) $)
    19.23vv $p |- ( A. x A. y ( ph -> ps ) <-> ( E. x E. y ph -> ps ) ) $=
      ( wi wal wex 19.23v albii bitri ) ABEDFZCFADGZBEZCFLCGBEKMCABDHILBCHJ $.
  $}

  ${
    $d x ps $.
    $( Version of ~ 19.36 with a dv condition instead of a non-freeness
       hypothesis.  (Contributed by NM, 18-Aug-1993.)  Reduce dependencies on
       axioms.  (Revised by Wolf Lammen, 17-Jan-2020.) $)
    19.36v $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> ps ) ) $=
      ( wi wex wal 19.35 19.9v imbi2i bitri ) ABDCEACFZBCEZDKBDABCGLBKBCHIJ $.
  $}

  ${
    $d x ps $.
    19.36aiv.1 $e |- E. x ( ph -> ps ) $.
    $( Inference form of ~ 19.36v .  (Contributed by NM, 5-Aug-1993.)  Reduce
       dependencies on axioms.  (Revised by Wolf Lammen, 17-Jan-2020.) $)
    19.36aiv $p |- ( A. x ph -> ps ) $=
      ( wi wex wal 19.36v mpbi ) ABECFACGBEDABCHI $.
  $}

  ${
    $d ph y $.  $d ps x $.  $d x y $.
    $( Version of ~ pm11.53 with a dv condition, requiring fewer axioms.
       (Contributed by BJ, 7-Mar-2020.) $)
    pm11.53v $p |- ( A. x A. y ( ph -> ps ) <-> ( E. x ph -> A. y ps ) ) $=
      ( wi wal wex 19.21v albii 19.23v bitri ) ABEDFZCFABDFZEZCFACGMELNCABDHIAM
      CJK $.
  $}

  ${
    $d x ps $.  $d y ph $.  $d x y $.
    $( Version of ~ 19.12vv with a dv condition, requiring fewer axioms.  See
       also ~ 19.12 .  (Contributed by BJ, 18-Mar-2020.) $)
    19.12vvv $p |- ( E. x A. y ( ph -> ps ) <-> A. y E. x ( ph -> ps ) ) $=
      ( wi wal wex 19.21v exbii 19.36v albii bitr2i 3bitri ) ABEZDFZCGABDFZEZCG
      ACFZPEZNCGZDFZOQCABDHIAPCJUARBEZDFSTUBDABCJKRBDHLM $.
  $}

  ${
    $d x ps $.
    $( Version of ~ 19.27 with a dv condition requiring fewer axioms.
       (Contributed by NM, 3-Jun-2004.) $)
    19.27v $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ ps ) ) $=
      ( wa wal 19.26 19.3v anbi2i bitri ) ABDCEACEZBCEZDJBDABCFKBJBCGHI $.
  $}

  ${
    $d x ph $.
    $( Version of ~ 19.28 with a dv condition requiring fewer axioms.
       (Contributed by NM, 25-Mar-2004.) $)
    19.28v $p |- ( A. x ( ph /\ ps ) <-> ( ph /\ A. x ps ) ) $=
      ( wa wal 19.26 19.3v anbi1i bitri ) ABDCEACEZBCEZDAKDABCFJAKACGHI $.
  $}

  ${
    $d x ph $.
    $( Version of ~ 19.37 with a dv condition requiring fewer axioms.
       (Contributed by NM, 21-Jun-1993.) $)
    19.37v $p |- ( E. x ( ph -> ps ) <-> ( ph -> E. x ps ) ) $=
      ( wi wex wal 19.35 19.3v imbi1i bitri ) ABDCEACFZBCEZDALDABCGKALACHIJ $.
  $}

  ${
    $d x ph $.
    19.37aiv.1 $e |- E. x ( ph -> ps ) $.
    $( Inference associated with ~ 19.37v .  (Contributed by NM,
       5-Aug-1993.) $)
    19.37aiv $p |- ( ph -> E. x ps ) $=
      ( wi wex 19.37v mpbi ) ABECFABCFEDABCGH $.
  $}

  ${
    $d x ps $.
    $( Version of ~ 19.41 with a dv condition requiring fewer axioms.
       (Contributed by NM, 21-Jun-1993.) $)
    19.41v $p |- ( E. x ( ph /\ ps ) <-> ( E. x ph /\ ps ) ) $=
      ( wa wex 19.40 19.9v anbi2i sylib pm3.21 eximdv impcom impbii ) ABDZCEZAC
      EZBDZOPBCEZDQABCFRBPBCGHIBPOBANCBAJKLM $.
  $}

  ${
    $d x ps $.  $d y ps $.
    $( Version of ~ 19.41 with two quantifiers and a dv condition requiring
       fewer axioms.  (Contributed by NM, 30-Apr-1995.) $)
    19.41vv $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x E. y ph /\ ps ) ) $=
      ( wa wex 19.41v exbii bitri ) ABEDFZCFADFZBEZCFKCFBEJLCABDGHKBCGI $.
  $}

  ${
    $d x ps $.  $d y ps $.  $d z ps $.
    $( Version of ~ 19.41 with three quantifiers and a dv condition requiring
       fewer axioms.  (Contributed by NM, 30-Apr-1995.) $)
    19.41vvv $p |- ( E. x E. y E. z ( ph /\ ps ) <->
                     ( E. x E. y E. z ph /\ ps ) ) $=
      ( wa wex 19.41vv exbii 19.41v bitri ) ABFEGDGZCGAEGDGZBFZCGMCGBFLNCABDEHI
      MBCJK $.
  $}

  ${
    $d w ps $.  $d x ps $.  $d y ps $.  $d z ps $.
    $( Version of ~ 19.41 with four quantifiers and a dv condition requiring
       fewer axioms.  (Contributed by FL, 14-Jul-2007.) $)
    19.41vvvv $p |- ( E. w E. x E. y E. z ( ph /\ ps ) <->
                     ( E. w E. x E. y E. z ph /\ ps ) ) $=
      ( wa wex 19.41vvv exbii 19.41v bitri ) ABGEHDHCHZFHAEHDHCHZBGZFHNFHBGMOFA
      BCDEIJNBFKL $.
  $}

  ${
    $d x ph $.
    $( Version of ~ 19.42 with a dv condition requiring fewer axioms.
       (Contributed by NM, 21-Jun-1993.) $)
    19.42v $p |- ( E. x ( ph /\ ps ) <-> ( ph /\ E. x ps ) ) $=
      ( wa wex 19.41v exancom ancom 3bitr4i ) BADCEBCEZADABDCEAJDBACFABCGAJHI
      $.
  $}

  ${
    $d y ph $.
    $( Distribution of existential quantifiers.  (Contributed by NM,
       9-Mar-1995.) $)
    exdistr $p |- ( E. x E. y ( ph /\ ps ) <-> E. x ( ph /\ E. y ps ) ) $=
      ( wa wex 19.42v exbii ) ABEDFABDFECABDGH $.
  $}

  ${
    $d x ph $.  $d y ph $.
    $( Version of ~ 19.42 with two quantifiers and a dv condition requiring
       fewer axioms.  (Contributed by NM, 16-Mar-1995.) $)
    19.42vv $p |- ( E. x E. y ( ph /\ ps ) <-> ( ph /\ E. x E. y ps ) ) $=
      ( wa wex exdistr 19.42v bitri ) ABEDFCFABDFZECFAJCFEABCDGAJCHI $.
  $}

  ${
    $d x ph $.  $d y ph $.  $d z ph $.
    $( Version of ~ 19.42 with three quantifiers and a dv condition requiring
       fewer axioms.  (Contributed by NM, 21-Sep-2011.) $)
    19.42vvv $p |- ( E. x E. y E. z ( ph /\ ps )
                       <-> ( ph /\ E. x E. y E. z ps ) ) $=
      ( wa wex 19.42vv exbii 19.42v bitri ) ABFEGDGZCGABEGDGZFZCGAMCGFLNCABDEHI
      AMCJK $.
  $}

  ${
    $d y ph $.  $d z ph $.
    $( Distribution of existential quantifiers.  (Contributed by NM,
       17-Mar-1995.) $)
    exdistr2 $p |- ( E. x E. y E. z ( ph /\ ps ) <->
                   E. x ( ph /\ E. y E. z ps ) ) $=
      ( wa wex 19.42vv exbii ) ABFEGDGABEGDGFCABDEHI $.
  $}

  ${
    $d y ph $.  $d z ph $.  $d z ps $.
    $( Distribution of existential quantifiers in a triple conjunction.
       (Contributed by NM, 9-Mar-1995.)  (Proof shortened by Andrew Salmon,
       25-May-2011.) $)
    3exdistr $p |- ( E. x E. y E. z ( ph /\ ps /\ ch ) <->
                E. x ( ph /\ E. y ( ps /\ E. z ch ) ) ) $=
      ( w3a wex wa 3anass 2exbii 19.42vv exdistr anbi2i 3bitri exbii ) ABCGZFHE
      HZABCFHIEHZIZDRABCIZIZFHEHAUAFHEHZITQUBEFABCJKAUAEFLUCSABCEFMNOP $.
  $}

  ${
    $d y ph $.  $d z ph $.  $d w ph $.  $d z ps $.  $d w ps $.  $d w ch $.
    $( Distribution of existential quantifiers in a quadruple conjunction.
       (Contributed by NM, 9-Mar-1995.)  (Proof shortened by Wolf Lammen,
       20-Jan-2018.) $)
    4exdistr $p |- ( E. x E. y E. z E. w ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
                E. x ( ph /\ E. y ( ps /\ E. z ( ch /\ E. w th ) ) ) ) $=
      ( wa wex w3a 19.42v anbi2i df-3an 3bitr4i 3exbii 3exdistr bitri ) ABIZCDI
      ZIHJZGJFJEJABCDHJIZKZGJFJEJABUBGJIFJIEJUAUCEFGSTHJZISUBIUAUCUDUBSCDHLMSTH
      LABUBNOPABUBEFGQR $.
  $}

  ${
    $d x y $.
    spimeh.1 $e |- ( ph -> A. x ph ) $.
    spimeh.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Existential introduction, using implicit substitution.  Compare Lemma 14
       of [Tarski] p. 70.  (Contributed by NM, 7-Aug-1994.)  (Proof shortened
       by Wolf Lammen, 10-Dec-2017.) $)
    spimeh $p |- ( ph -> E. x ps ) $=
      ( wal wex weq wi ax6ev eximii 19.35i syl ) AACGBCHEABCCDIABJCCDKFLMN $.
  $}

  ${
    $d x y $.
    spimw.1 $e |- ( -. ps -> A. x -. ps ) $.
    spimw.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Specialization.  Lemma 8 of [KalishMontague] p. 87.  Uses only Tarski's
       FOL axiom schemes.  (Contributed by NM, 19-Apr-2017.)  (Proof shortened
       by Wolf Lammen, 7-Aug-2017.) $)
    spimw $p |- ( A. x ph -> ps ) $=
      ( weq wn wal wi ax6v spimfw ax-mp ) CDGHCIHACIBJCDKABCDEFLM $.
  $}

  ${
    $d x y $.  $d x ps $.
    spimvw.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Specialization.  Lemma 8 of [KalishMontague] p. 87.  Uses only Tarski's
       FOL axiom schemes.  (Contributed by NM, 9-Apr-2017.) $)
    spimvw $p |- ( A. x ph -> ps ) $=
      ( wn ax-5 spimw ) ABCDBFCGEH $.
  $}

  ${
    $d x y $.  $d y ph $.
    spnfw.1 $e |- ( -. ph -> A. x -. ph ) $.
    $( Weak version of ~ sp .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 1-Aug-2017.)  (Proof shortened by Wolf Lammen,
       13-Aug-2017.) $)
    spnfw $p |- ( A. x ph -> ph ) $=
      ( vy weq idd spimw ) AABDCBDEAFG $.
  $}

  ${
    spfalw.1 $e |- -. ph $.
    $( Version of ~ sp when ` ph ` is false.  Uses only Tarski's FOL axiom
       schemes.  (Contributed by NM, 23-Apr-2017.)  (Proof shortened by Wolf
       Lammen, 25-Dec-2017.) $)
    spfalw $p |- ( A. x ph -> ph ) $=
      ( wn hbth spnfw ) ABADBCEF $.
  $}

  ${
    $d x y $.
    $( Version of ~ equs4 with a dv condition, which requires fewer axioms.
       (Contributed by BJ, 31-May-2019.) $)
    equs4v $p |- ( A. x ( x = y -> ph ) -> E. x ( x = y /\ ph ) ) $=
      ( weq wi wal wex wa ax6ev exintr mpi ) BCDZAEBFLBGLAHBGBCILABJK $.
  $}

  ${
    $d x y $.
    cbvaliw.1 $e |- ( A. x ph -> A. y A. x ph ) $.
    cbvaliw.2 $e |- ( -. ps -> A. x -. ps ) $.
    cbvaliw.3 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.  Part of
       Lemma 7 of [KalishMontague] p. 86.  (Contributed by NM, 19-Apr-2017.) $)
    cbvaliw $p |- ( A. x ph -> A. y ps ) $=
      ( wal spimw alrimih ) ACHBDEABCDFGIJ $.
  $}

  ${
    $d x y $.  $d x ps $.  $d y ph $.
    cbvalivw.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.  Part of
       Lemma 7 of [KalishMontague] p. 86.  (Contributed by NM, 9-Apr-2017.) $)
    cbvalivw $p |- ( A. x ph -> A. y ps ) $=
      ( wal spimvw alrimiv ) ACFBDABCDEGH $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Axiom scheme ax-7 (Equality)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Equality.  One of the equality and substitution axioms of
     predicate calculus with equality.  This is similar to, but not quite, a
     transitive law for equality (proved later as ~ equtr ).  This axiom scheme
     is a sub-scheme of Axiom Scheme B8 of system S2 of [Tarski], p. 75, whose
     general form cannot be represented with our notation.  Also appears as
     Axiom C7 of [Monk2] p. 105 and Axiom Scheme C8' in [Megill] p. 448 (p. 16
     of the preprint).

     The equality symbol was invented in 1527 by Robert Recorde.  He chose a
     pair of parallel lines of the same length because ""noe .2. thynges, can be
     moare equalle.""

     Note that this axiom is still valid even when any two or all three of
     ` x ` , ` y ` , and ` z ` are replaced with the same variable since they
     do not have any distinct variable (Metamath's $d) restrictions.  Because
     of this, we say that these three variables are ""bundled"" (a term coined by
     Raph Levien).  (Contributed by NM, 10-Jan-1993.) $)
  ax-7 $a |- ( x = y -> ( x = z -> y = z ) ) $.

  ${
    $d x y $.
    $( Identity law for equality.  Lemma 2 of [KalishMontague] p. 85.  See also
       Lemma 6 of [Tarski] p. 68.  (Contributed by NM, 1-Apr-2005.)  (Revised
       by NM, 9-Apr-2017.)  (Proof shortened by Wolf Lammen, 5-Feb-2018.) $)
    equid $p |- x = x $=
      ( vy weq wex ax6ev ax-7 pm2.43i eximii ax5e ax-mp ) AACZBDKBACZKBBAELKBAA
      FGHKBIJ $.
  $}

  $( Bound-variable hypothesis builder for ` x = x ` .  This theorem tells us
     that any variable, including ` x ` , is effectively not free in
     ` x = x ` , even though ` x ` is technically free according to the
     traditional definition of free variable.  (Contributed by NM,
     13-Jan-2011.)  (Revised by NM, 21-Aug-2017.) $)
  nfequid $p |- F/ y x = x $=
    ( weq equid nfth ) AACBADE $.

  ${
    $d x w $.
    $( Commutative law for equality.  Lemma 3 of [KalishMontague] p. 85.  See
       also Lemma 7 of [Tarski] p. 69.  (Contributed by NM, 10-Jan-1993.)
       (Revised by NM, 9-Apr-2017.) $)
    equcomi $p |- ( x = y -> y = x ) $=
      ( weq equid ax-7 mpi ) ABCAACBACADABAEF $.
  $}

  $( Commutative law for equality.  (Contributed by NM, 20-Aug-1993.) $)
  equcom $p |- ( x = y <-> y = x ) $=
    ( weq equcomi impbii ) ABCBACABDBADE $.

  ${
    equcoms.1 $e |- ( x = y -> ph ) $.
    $( An inference commuting equality in antecedent.  Used to eliminate the
       need for a syllogism.  (Contributed by NM, 10-Jan-1993.) $)
    equcoms $p |- ( y = x -> ph ) $=
      ( weq equcomi syl ) CBEBCEACBFDG $.
  $}

  $( A transitive law for equality.  (Contributed by NM, 23-Aug-1993.) $)
  equtr $p |- ( x = y -> ( y = z -> x = z ) ) $=
    ( weq wi ax-7 equcoms ) BCDACDEBABACFG $.

  $( A transitive law for equality.  Lemma L17 in [Megill] p. 446 (p. 14 of the
     preprint).  (Contributed by NM, 23-Aug-1993.) $)
  equtrr $p |- ( x = y -> ( z = x -> z = y ) ) $=
    ( weq equtr com12 ) CADABDCBDCABEF $.

  $( An equivalence law for equality.  (Contributed by NM, 1-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 10-Dec-2017.) $)
  equequ1 $p |- ( x = y -> ( x = z <-> y = z ) ) $=
    ( weq ax-7 equtr impbid ) ABDACDBCDABCEABCFG $.

  $( An equivalence law for equality.  (Contributed by NM, 21-Jun-1993.)
     (Proof shortened by Wolf Lammen, 4-Aug-2017.) $)
  equequ2 $p |- ( x = y -> ( z = x <-> z = y ) ) $=
    ( weq equequ1 equcom 3bitr3g ) ABDACDBCDCADCBDABCEACFBCFG $.

  $( One of the two equality axioms of standard predicate calculus, called
     reflexivity of equality.  (The other one is ~ stdpc7 .)  Axiom 6 of
     [Mendelson] p. 95.  Mendelson doesn't say why he prepended the redundant
     quantifier, but it was probably to be compatible with free logic (which is
     valid in the empty domain).  (Contributed by NM, 16-Feb-2005.) $)
  stdpc6 $p |- A. x x = x $=
    ( weq equid ax-gen ) AABAACD $.

  $( One of the two equality axioms of standard predicate calculus, called
     substitutivity of equality.  (The other one is ~ stdpc6 .)  Translated to
     traditional notation, it can be
     read:  "" ` x = y -> ( ph ( x , x ) -> ph ( x , y ) ) ` , provided that
     ` y ` is free for ` x ` in ` ph ( x , x ) ` .""  Axiom 7 of [Mendelson]
     p. 95.  (Contributed by NM, 15-Feb-2005.) $)
  stdpc7 $p |- ( x = y -> ( [ x / y ] ph -> ph ) ) $=
    ( wsb wi sbequ2 equcoms ) ACBDAECBACBFG $.

  $( A transitive law for equality.  (Contributed by NM, 12-Aug-1993.)  (Proof
     shortened by Andrew Salmon, 25-May-2011.) $)
  equtr2 $p |- ( ( x = z /\ y = z ) -> x = y ) $=
    ( weq wi equtrr equcoms impcom ) BCDACDZABDZIJECBCBAFGH $.

  ${
    $d x z $.  $d y z $.
    $( A specialized version of ~ equvini with a distinct variable
       restriction.  (Contributed by Wolf Lammen, 8-Sep-2018.) $)
    equviniv $p |- ( x = y -> E. z ( x = z /\ y = z ) ) $=
      ( weq wex wa ax6ev equcomi equtr ancrd syl5 eximdv mpi ) ABDZCBDZCEACDZBC
      DZFZCECBGNORCOQNRCBHNQPABCIJKLM $.
  $}

  ${
    $d x z $.  $d y z $.
    $( A variable introduction law for equality.  Lemma 15 of [Monk2] p. 109.
       (Contributed by NM, 9-Jan-1993.)  Remove dependencies on ~ ax-10 ,
       ~ ax-13 .  (Revised by Wolf Lammen, 10-Jun-2019.) $)
    equvin $p |- ( x = y <-> E. z ( x = z /\ z = y ) ) $=
      ( weq wa wex equviniv equcom anbi2i exbii sylib equtr imp exlimiv impbii
      ) ABDZACDZCBDZEZCFZPQBCDZEZCFTABCGUBSCUARQBCHIJKSPCQRPACBLMNO $.
  $}

  $( Two equivalent ways of expressing ~ ax-13 .  See the comment for
     ~ ax-13 .  (Contributed by NM, 2-May-2017.)  (Proof shortened by Wolf
     Lammen, 26-Feb-2018.) $)
  ax13b $p |- ( ( -. x = y -> ( y = z -> A. x y = z ) )
     <-> ( -. x = y -> ( -. x = z -> ( y = z -> A. x y = z ) ) ) ) $=
    ( weq wn wal ax-1 equtrr equcoms con3rr3 imim1d pm2.43 syl6 impbid2 pm5.74i
    wi ) ABDZEZBCDZSAFZPZACDZEZUAPZRUAUDUAUCGRUDSUAPUARSUCUASUBQUBQPCBCBAHIJKST
    LMNO $.

  ${
    $d x y $.
    spfw.1 $e |- ( -. ps -> A. x -. ps ) $.
    spfw.2 $e |- ( A. x ph -> A. y A. x ph ) $.
    spfw.3 $e |- ( -. ph -> A. y -. ph ) $.
    spfw.4 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Weak version of ~ sp .  Uses only Tarski's FOL axiom schemes.  Lemma 9
       of [KalishMontague] p. 87.  This may be the best we can do with minimal
       distinct variable conditions.  (Contributed by NM, 19-Apr-2017.) $)
    spfw $p |- ( A. x ph -> ph ) $=
      ( wal wi alim weq biimprd equcoms spimw syl56 biimpd mpg ) ACIZBJZSAJDSSD
      ITDIBDIAFSBDKBADCGBAJCDCDLZABHMNOPABCDEUAABHQOR $.
  $}

  ${
    $d x y $.  $d x ps $.  $d y ph $.
    spw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Weak version of the specialization scheme ~ sp .  Lemma 9 of
       [KalishMontague] p. 87.  While it appears that ~ sp in its general form
       does not follow from Tarski's FOL axiom schemes, from this theorem we
       can prove any _instance_ of ~ sp having mutually distinct setvar
       variables and no wff metavariables (see ~ ax12wdemo for an example of
       the procedure to eliminate the hypothesis).  Other approximations of
       ~ sp are ~ spfw (minimal distinct variable requirements), ~ spnfw (when
       ` x ` is not free in ` -. ph ` ), ~ spvw (when ` x ` does not appear in
       ` ph ` ), ~ sptruw (when ` ph ` is true), and ~ spfalw (when ` ph ` is
       false).  (Contributed by NM, 9-Apr-2017.)  (Proof shortened by Wolf
       Lammen, 27-Feb-2018.) $)
    spw $p |- ( A. x ph -> ph ) $=
      ( wn ax-5 wal spfw ) ABCDBFCGACHDGAFDGEI $.
  $}

  ${
    $d x y $.
    cbvalw.1 $e |- ( A. x ph -> A. y A. x ph ) $.
    cbvalw.2 $e |- ( -. ps -> A. x -. ps ) $.
    cbvalw.3 $e |- ( A. y ps -> A. x A. y ps ) $.
    cbvalw.4 $e |- ( -. ph -> A. y -. ph ) $.
    cbvalw.5 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 9-Apr-2017.) $)
    cbvalw $p |- ( A. x ph <-> A. y ps ) $=
      ( wal weq biimpd cbvaliw wi biimprd equcoms impbii ) ACJBDJABCDEFCDKZABIL
      MBADCGHBANCDRABIOPMQ $.
  $}

  ${
    $d x y $.  $d x ps $.  $d y ph $.
    cbvalvw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 9-Apr-2017.)  (Proof shortened by Wolf Lammen,
       28-Feb-2018.) $)
    cbvalvw $p |- ( A. x ph <-> A. y ps ) $=
      ( wal ax-5 wn cbvalw ) ABCDACFDGBHCGBDFCGAHDGEI $.

    $( Change bound variable.  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 19-Apr-2017.) $)
    cbvexvw $p |- ( E. x ph <-> E. y ps ) $=
      ( wn wal wex weq notbid cbvalvw notbii df-ex 3bitr4i ) AFZCGZFBFZDGZFACHB
      DHPROQCDCDIABEJKLACMBDMN $.
  $}

  ${
    $d y z $.  $d x y $.  $d z ph $.  $d y ps $.
    alcomiw.1 $e |- ( y = z -> ( ph <-> ps ) ) $.
    $( Weak version of ~ alcom .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 10-Apr-2017.) $)
    alcomiw $p |- ( A. x A. y ph -> A. y A. x ph ) $=
      ( wal weq biimpd cbvalivw alimi ax-5 wi biimprd equcoms spimvw 3syl ) ADG
      ZCGBEGZCGZTDGACGZDGRSCABDEDEHZABFIJKTDLTUADSACBAEDBAMDEUBABFNOPKKQ $.
  $}

  ${
    $d x y $.
    hbn1fw.1 $e |- ( A. x ph -> A. y A. x ph ) $.
    hbn1fw.2 $e |- ( -. ps -> A. x -. ps ) $.
    hbn1fw.3 $e |- ( A. y ps -> A. x A. y ps ) $.
    hbn1fw.4 $e |- ( -. ph -> A. y -. ph ) $.
    hbn1fw.5 $e |- ( -. A. y ps -> A. x -. A. y ps ) $.
    hbn1fw.6 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Weak version of ~ ax-10 from which we can prove any ~ ax-10 instance not
       involving wff variables or bundling.  Uses only Tarski's FOL axiom
       schemes.  (Contributed by NM, 19-Apr-2017.)  (Proof shortened by Wolf
       Lammen, 28-Feb-2018.) $)
    hbn1fw $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
      ( wal wn cbvalw notbii hbxfrbi ) ACKZLBDKZLCPQABCDEFGHJMNIO $.
  $}

  ${
    $d y ph $.  $d x ps $.  $d x y $.
    hbn1w.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Weak version of ~ hbn1 .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 9-Apr-2017.) $)
    hbn1w $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
      ( wal ax-5 wn hbn1fw ) ABCDACFDGBHCGBDFZCGAHDGJHCGEI $.

    $( Weak version of ~ hba1 .  See comments for ~ ax10w .  Uses only Tarski's
       FOL axiom schemes.  (Contributed by NM, 9-Apr-2017.) $)
    hba1w $p |- ( A. x ph -> A. x A. x ph ) $=
      ( wal wn weq wb cbvalvw a1i notbid spw con2i hbn1w con1i alimi 3syl ) ACF
      ZSGZCFZGZUBCFSCFUASTBDFZGZCDCDHZSUCSUCIUEABCDEJKLZMNTUDCDUFOUBSCSUAABCDEO
      PQR $.

    $( Weak version of ~ hbe1 .  See comments for ~ ax10w .  Uses only Tarski's
       FOL axiom schemes.  (Contributed by NM, 19-Apr-2017.) $)
    hbe1w $p |- ( E. x ph -> A. x E. x ph ) $=
      ( wex wn wal df-ex weq notbid hbn1w hbxfrbi ) ACFAGZCHGCACINBGCDCDJABEKLM
      $.
  $}

  ${
    $d x z $.  $d x y $.  $d z ph $.  $d x ps $.
    hbalw.1 $e |- ( x = z -> ( ph <-> ps ) ) $.
    hbalw.2 $e |- ( ph -> A. x ph ) $.
    $( Weak version of ~ hbal .  Uses only Tarski's FOL axiom schemes.  Unlike
       ~ hbal , this theorem requires that ` x ` and ` y ` be distinct i.e. are
       not bundled.  (Contributed by NM, 19-Apr-2017.) $)
    hbalw $p |- ( A. y ph -> A. x A. y ph ) $=
      ( wal alimi alcomiw syl ) ADHZACHZDHLCHAMDGIABDCEFJK $.
  $}

  ${
    $d x v w $.  $d y v w $.
    $( Change bound variable in an equality with a dv condition.  (Contributed
       by NM, 22-Jul-2015.)  (Revised by BJ, 18-Jun-2019.) $)
    cbvaev $p |- ( A. x x = w -> A. y y = w ) $=
      ( vv weq wal ax-7 cbvalivw syl ) ACEZAFDCEZDFBCEZBFJKADADCGHKLDBDBCGHI $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                  Membership predicate
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare the membership predicate symbol. $)
  $c e. $. $( Stylized epsilon $)

  ${
    $v A $.
    $v B $.
    wcel.cA $f class A $.
    wcel.cB $f class B $.
    $( Extend wff definition to include the membership connective between
       classes.

       For a general discussion of the theory of classes, see
       ~ http://us.metamath.org/mpeuni/mmset.html#class .

       (The purpose of introducing ` wff A e. B ` here is to allow us to
       express i.e.  ""prove"" the ~ wel of predicate calculus in terms of the
       ~ wcel of set theory, so that we don't ""overload"" the ` e. ` connective
       with two syntax definitions.  This is done to prevent ambiguity that
       would complicate some Metamath parsers.  The class variables ` A ` and
       ` B ` are introduced temporarily for the purpose of this definition but
       otherwise not used in predicate calculus.  See ~ df-clab for more
       information on the set theory usage of ~ wcel .) $)
    wcel $a wff A e. B $.
  $}

  $( Extend wff definition to include atomic formulas with the epsilon
     (membership) predicate.  This is read "" ` x ` is an element of
     ` y ` ,"" "" ` x ` is a member of ` y ` ,"" "" ` x ` belongs to ` y ` ,""
     or "" ` y ` contains ` x ` .""  Note:  The phrase "" ` y ` includes
     ` x ` "" means "" ` x ` is a subset of ` y ` ;"" to use it also for
     ` x e. y ` , as some authors occasionally do, is poor form and causes
     confusion, according to George Boolos (1992 lecture at MIT).

     This syntactical construction introduces a binary non-logical predicate
     symbol ` e. ` (epsilon) into our predicate calculus.  We will eventually
     use it for the membership predicate of set theory, but that is irrelevant
     at this point: the predicate calculus axioms for ` e. ` apply to any
     arbitrary binary predicate symbol.  ""Non-logical"" means that the predicate
     is presumed to have additional properties beyond the realm of predicate
     calculus, although these additional properties are not specified by
     predicate calculus itself but rather by the axioms of a theory (in our
     case set theory) added to predicate calculus.  ""Binary"" means that the
     predicate has two arguments.

     (Instead of introducing ~ wel as an axiomatic statement, as was done in an
     older version of this database, we introduce it by ""proving"" a special
     case of set theory's more general ~ wcel .  This lets us avoid overloading
     the ` e. ` connective, thus preventing ambiguity that would complicate
     certain Metamath parsers.  However, logically ~ wel is considered to be a
     primitive syntax, even though here it is artificially ""derived"" from
     ~ wcel .  Note:  To see the proof steps of this syntax proof, type ""show
     proof wel /all"" in the Metamath program.)  (Contributed by NM,
     24-Jan-2006.) $)
  wel $p wff x e. y $=
    ( cv wcel ) ACBCD $.

  $( Register class-to-set promotion and class equality and membership as
     primitive expressions. Although these are actually definitions, the above
     ambiguity prevention necessitates our taking class equality as the
     primitive, instead of set equality. $)
  $( $j primitive 'weq' 'wel'; $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Axiom scheme ax-8 (Left Equality for Binary Predicate)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Left Equality for Binary Predicate.  One of the equality and
     substitution axioms for a non-logical predicate in our predicate calculus
     with equality.  It substitutes equal variables into the left-hand side of
     an arbitrary binary predicate ` e. ` , which we will use for the set
     membership relation when set theory is introduced.  This axiom scheme is a
     sub-scheme of Axiom Scheme B8 of system S2 of [Tarski], p. 75, whose
     general form cannot be represented with our notation.  Also appears as
     Axiom scheme C12' in [Megill] p. 448 (p. 16 of the preprint).
     ""Non-logical"" means that the predicate is not a primitive of predicate
     calculus proper but instead is an extension to it.  ""Binary"" means that
     the predicate has two arguments.  In a system of predicate calculus with
     equality, like ours, equality is not usually considered to be a
     non-logical predicate.  In systems of predicate calculus without equality,
     it typically would be.  (Contributed by NM, 30-Jun-1993.) $)
  ax-8 $a |- ( x = y -> ( x e. z -> y e. z ) ) $.

  $( An identity law for the non-logical predicate.  (Contributed by NM,
     30-Jun-1993.) $)
  elequ1 $p |- ( x = y -> ( x e. z <-> y e. z ) ) $=
    ( weq wel ax-8 wi equcoms impbid ) ABDACEZBCEZABCFKJGBABACFHI $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Axiom scheme ax-9 (Right Equality for Binary Predicate)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Right Equality for Binary Predicate.  One of the equality and
     substitution axioms for a non-logical predicate in our predicate calculus
     with equality.  It substitutes equal variables into the right-hand side of
     an arbitrary binary predicate ` e. ` , which we will use for the set
     membership relation when set theory is introduced.  This axiom scheme is a
     sub-scheme of Axiom Scheme B8 of system S2 of [Tarski], p. 75, whose
     general form cannot be represented with our notation.  Also appears as
     Axiom scheme C13' in [Megill] p. 448 (p. 16 of the preprint).
     (Contributed by NM, 21-Jun-1993.) $)
  ax-9 $a |- ( x = y -> ( z e. x -> z e. y ) ) $.

  $( An identity law for the non-logical predicate.  (Contributed by NM,
     21-Jun-1993.) $)
  elequ2 $p |- ( x = y -> ( z e. x <-> z e. y ) ) $=
    ( weq wel ax-9 wi equcoms impbid ) ABDCAEZCBEZABCFKJGBABACFHI $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Logical redundancy of ax-10 , ax-11 , ax-12 , ax-13
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The original axiom schemes of Tarski's predicate calculus are ~ ax-4 ,
  ~ ax-5 , ~ ax6v , ~ ax-7 , ~ ax-8 , and ~ ax-9 , together with rule
  ~ ax-gen .  See ~ http://us.metamath.org/mpeuni/mmset.html#compare .  They
  are given as axiom schemes B4 through B8 in [KalishMontague] p. 81.  These
  are shown to be logically complete by Theorem 1 of [KalishMontague] p. 85.

  The axiom system of set.mm includes the auxiliary axiom schemes ~ ax-10 ,
  ~ ax-11 , ~ ax-12 , and ~ ax-13 , which are not part of Tarski's axiom
  schemes.  Each object language instance of them is provable from Tarski's
  axioms, so they are logically redundant.  However, they are conjectured not
  to be provable directly _as schemes_ from Tarski's axiom schemes using only
  Metamath's direct substitution rule.  They are used to make our system
  ""metalogically complete"" i.e. able to prove directly all possible schemes
  with wff and set metavariables, bundled or not, whose object-language
  instances are valid.  ( ~ ax-12 has been proved to be required; see
  ~ http://us.metamath.org/award2003.html#9a .  Metalogical independence of the
  other three are open problems.)

  (There are additional predicate calculus axiom schemes included in set.mm
  such as ~ ax-c5 , but they can all be proved as theorems from the above.)

  Terminology:  Two set (individual) metavariables are ""bundled"" in an axiom or
  theorem scheme when there is no distinct variable constraint ($d) imposed on
  them.  (The term ""bundled"" is due to Raph Levien.)  For example, the ` x `
  and ` y ` in ~ ax-6 are bundled, but they are not in ~ ax6v . We also say
  that a scheme is bundled when it has at least one pair of bundled set
  metavariables.  If distinct variable conditions are added to all set
  metavariable pairs in a bundled scheme, we call that the ""principal"" instance
  of the bundled scheme.  For example, ~ ax6v is the principal instance of
  ~ ax-6 . Whenever a common variable is substituted for two or more bundled
  variables in an axiom or theorem scheme, we call the substitution instance
  ""degenerate"".  For example, the instance ` -. A. x -. x = x ` of ~ ax-6 is
  degenerate.  An advantage of bundling is ease of use since there are fewer
  distinct variable restrictions ($d) to be concerned with.  There is also a
  small economy in being able to state principal and degenerate instances
  simultaneously.  A disadvantage is that bundling may present difficulties in
  translations to other proof languages, which typically lack the concept (in
  part because their variables often represent the variables of the object
  language rather than metavariables ranging over them).

  Because Tarski's axiom schemes are logically complete, they can be used to
  prove any object-language instance of ~ ax-10 , ~ ax-11 , ~ ax-12 , and
  ~ ax-13 . ""Translating"" this to Metamath, it means that Tarski's axioms can
  prove any substitution instance of ~ ax-10 , ~ ax-11 , ~ ax-12 , or ~ ax-13
  in which (1) there are no wff metavariables and (2) all set metavariables are
  mutually distinct i.e. are not bundled.  In effect this is mimicking the
  object language by pretending that each set metavariable is an
  object-language variable.  (There may also be specific instances with wff
  metavariables and/or bundling that are directly provable from Tarski's axiom
  schemes, but it isn't guaranteed.  Whether all of them are possible is part
  of the still open metalogical independence problem for our additional axiom
  schemes.)

  It can be useful to see how this can be done, both to show that our
  additional schemes are valid metatheorems of Tarski's system and to be able
  to translate object language instances of our proofs into proofs that would
  work with a system using only Tarski's original schemes.  In addition, it may
  (or may not) provide insight into the conjectured metalogical independence of
  our additional schemes.

  The theorem schemes ~ ax10w , ~ ax11w , ~ ax12w , and ~ ax13w are derived
  using only Tarski's axiom schemes, showing that Tarski's schemes can be used
  to derive all substitution instances of ~ ax-10 , ~ ax-11 , ~ ax-12 , and
  ~ ax-13 meeting conditions (1) and (2).  (The ""w"" suffix stands for ""weak
  version"".)  Each hypothesis of ~ ax10w , ~ ax11w , and ~ ax12w is of the form
  ` ( x = y -> ( ph <-> ps ) ) ` where ` ps ` is an auxiliary or ""dummy"" wff
  metavariable in which ` x ` doesn't occur.  We can show by induction on
  formula length that the hypotheses can be eliminated in all cases meeting
  conditions (1) and (2).  The example ~ ax12wdemo illustrates the techniques
  (equality theorems and bound variable renaming) used to achieve this.

  We also show the degenerate instances for axioms with bundled variables in
  ~ ax11dgen , ~ ax12dgen , ~ ax13dgen1 , ~ ax13dgen2 , ~ ax13dgen3 , and
  ~ ax13dgen4 . (Their proofs are trivial, but we include them to be thorough.)
  Combining the principal and degenerate cases _outside_ of Metamath, we show
  that the bundled schemes ~ ax-10 , ~ ax-11 , ~ ax-12 , and ~ ax-13 are
  schemes of Tarski's system, meaning that all object language instances they
  generate are theorems of Tarski's system.

  It is interesting that Tarski used the bundled scheme ~ ax-6 in an older
  system, so it seems the main purpose of his later ~ ax6v was just to show
  that the weaker unbundled form is sufficient rather than an aesthetic
  objection to bundled free and bound variables.  Since we adopt the
  bundled ~ ax-6 as our official axiom, we  show that the degenerate
  instance holds in ~ ax6dgen .

  The case of ~ sp is curious:  originally an axiom of Tarski's system, it was
  proved logically redundant by Lemma 9 of [KalishMontague] p. 86.  However,
  the proof is by induction on formula length, and the scheme form
  ` A. x ph -> ph ` apparently cannot be proved directly from Tarski's other
  axiom schemes.  The best we can do seems to be ~ spw , again requiring
  substitution instances of ` ph ` that meet conditions (1) and (2) above.
  Note that our direct proof ~ sp requires ~ ax-12 , which is not part of
  Tarski's system.

$)

  ${
    $( Tarski's system uses the weaker ~ ax6v instead of the bundled ~ ax-6 ,
       so here we show that the degenerate case of ~ ax-6 can be derived.
       (Contributed by NM, 23-Apr-2017.) $)
    ax6dgen $p |- -. A. x -. x = x $=
      ( weq wn wal equid notnoti spfalw mt2 ) AABZCZADIAEZJAIKFGH $.
  $}

  ${
    $d y ph $.  $d x ps $.  $d x y $.
    ax10w.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Weak version of ~ ax-10 from which we can prove any ~ ax-10 instance not
       involving wff variables or bundling.  Uses only Tarski's FOL axiom
       schemes.  (Contributed by NM, 9-Apr-2017.) $)
    ax10w $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
      ( hbn1w ) ABCDEF $.
  $}

  ${
    $d y z $.  $d x y $.  $d z ph $.  $d y ps $.
    ax11w.1 $e |- ( y = z -> ( ph <-> ps ) ) $.
    $( Weak version of ~ ax-11 from which we can prove any ~ ax-11 instance not
       involving wff variables or bundling.  Uses only Tarski's FOL axiom
       schemes.  Unlike ~ ax-11 , this theorem requires that ` x ` and ` y ` be
       distinct i.e. are not bundled.  (Contributed by NM, 10-Apr-2017.) $)
    ax11w $p |- ( A. x A. y ph -> A. y A. x ph ) $=
      ( alcomiw ) ABCDEFG $.
  $}

  $( Degenerate instance of ~ ax-11 where bundled variables ` x ` and ` y `
     have a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
  ax11dgen $p |- ( A. x A. x ph -> A. x A. x ph ) $=
    ( wal id ) ABCBCD $.

  ${
    $d x ps $.
    ax12wlemw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Lemma for weak version of ~ ax-12 .  Uses only Tarski's FOL axiom
       schemes.  In some cases, this lemma may lead to shorter proofs than
       ~ ax12w .  (Contributed by NM, 10-Apr-2017.) $)
    ax12wlem $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      ( ax-5 ax12i ) ABCDEBCFG $.
  $}

  ${
    $d y z $.  $d x ps $.  $d z ph $.  $d y ch $.
    ax12w.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    ax12w.2 $e |- ( y = z -> ( ph <-> ch ) ) $.
    $( Weak version of ~ ax-12 from which we can prove any ~ ax-12 instance not
       involving wff variables or bundling.  Uses only Tarski's FOL axiom
       schemes.  An instance of the first hypothesis will normally require that
       ` x ` and ` y ` be distinct (unless ` x ` does not occur in ` ph ` ).
       For an example of how the hypotheses can be eliminated when we
       substitute an expression without wff variables for ` ph ` , see
       ~ ax12wdemo .  (Contributed by NM, 10-Apr-2017.) $)
    ax12w $p |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $=
      ( wal weq wi spw ax12wlem syl5 ) AEIADEJZOAKDIACEFHLABDEGMN $.
  $}

  $( Degenerate instance of ~ ax-12 where bundled variables ` x ` and ` y `
     have a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
  ax12dgen $p |- ( x = x -> ( A. x ph -> A. x ( x = x -> ph ) ) ) $=
    ( wal weq wi ala1 a1i ) ABCBBDZAEBCEHAHBFG $.

  ${
    $d x y z w v $.
    $( Example of an application of ~ ax12w that results in an instance of
       ~ ax-12 for a contrived formula with mixed free and bound variables,
       ` ( x e. y /\ A. x z e. x /\ A. y A. z y e. x ) ` , in place of
       ` ph ` .  The proof illustrates bound variable renaming with ~ cbvalvw
       to obtain fresh variables to avoid distinct variable clashes.  Uses only
       Tarski's FOL axiom schemes.  (Contributed by NM, 14-Apr-2017.) $)
    ax12wdemo $p |- ( x = y
              -> ( A. y ( x e. y /\ A. x z e. x /\ A. y A. z y e. x )
     -> A. x ( x = y -> ( x e. y /\ A. x z e. x /\ A. y A. z y e. x ) ) ) ) $=
      ( vw vv wel wal w3a weq elequ1 elequ2 cbvalvw a1i albidv syl5bb 3anbi123d
      wb 3anbi13d ax12w ) ABFZCAFZAGZBAFZCGZBGZHBBFZCDFZDGZEBFZCGZEGZHAEFZUBEAF
      ZCGZEGZHABEABIZTUFUBUHUEUKABBJUBUHQUPUAUGADADCKLMUEUOUPUKUDUNBEBEIZUCUMCB
      EAJNLZUPUNUJEUPUMUICABEKNNOPUQTULUEUOUBBEAKUEUOQUQURMRS $.
  $}

  ${
    $d x y $.  $d x z $.
    $( Weak version (principal instance) of ~ ax-13 .  (Because ` y ` and ` z `
       don't need to be distinct, this actually bundles the principal instance
       and the degenerate instance
       ` ( -. x = y -> ( y = y -> A. x y = y ) ) ` .)  Uses only Tarski's FOL
       axiom schemes.  The proof is trivial but is included to complete the set
       ~ ax10w , ~ ax11w , and ~ ax12w .  (Contributed by NM, 10-Apr-2017.) $)
    ax13w $p |- ( -. x = y -> ( y = z -> A. x y = z ) ) $=
      ( weq wn ax5d ) ABDEBCDAF $.
  $}

  $( Degenerate instance of ~ ax-13 where bundled variables ` x ` and ` y `
     have a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
  ax13dgen1 $p |- ( -. x = x -> ( x = z -> A. x x = z ) ) $=
    ( weq wal wi equid pm2.24i ) AACABCZHADEAFG $.

  $( Degenerate instance of ~ ax-13 where bundled variables ` x ` and ` z `
     have a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
  ax13dgen2 $p |- ( -. x = y -> ( y = x -> A. x y = x ) ) $=
    ( weq wn wal equcomi pm2.21 syl5 ) BACZABCZJDIAEZBAFJKGH $.

  $( Degenerate instance of ~ ax-13 where bundled variables ` y ` and ` z `
     have a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
  ax13dgen3 $p |- ( -. x = y -> ( y = y -> A. x y = y ) ) $=
    ( weq wn wal equid ax-gen a1ii ) ABCDBBCZIAEIABFGH $.

  $( Degenerate instance of ~ ax-13 where bundled variables ` x ` , ` y ` , and
     ` z ` have a common substitution.  Uses only Tarski's FOL axiom schemes .
     (Contributed by NM, 13-Apr-2017.) $)
  ax13dgen4 $p |- ( -. x = x -> ( x = x -> A. x x = x ) ) $=
    ( ax13dgen1 ) AAB $.


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
   Predicate calculus with equality:  Auxiliary axiom schemes (4 schemes)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  In this section we introduce four additional schemes ~ ax-10 , ~ ax-11 ,
  ~ ax-12 , and ~ ax-13 that are not part of Tarski's system but can be proved
  (outside of Metamath) as theorem schemes of Tarski's system.  These are
  needed to give our system the property of ""metalogical completeness,"" which
  means that we can prove (with Metamath) all possible theorem schemes
  expressible in our language of wff metavariables ranging over object-language
  wffs and set metavariables ranging over object-language individual variables.

  To show that these schemes are valid metatheorems of Tarski's system S2,
  above we proved from Tarski's system theorems ~ ax10w , ~ ax11w , ~ ax12w ,
  and ~ ax13w , which show that any object-language instance of these schemes
  (emulated by having no wff metavariables and requiring all set
  metavariables to be mutually distinct) can be proved using only the schemes
  in Tarski's system S2.

  An open problem is to show that these four additional schemes are mutually
  _metalogically_ independent and metalogically independent from Tarski's.  So
  far, independence of ~ ax-12 from all others has been shown, and
  independence of Tarski's ~ ax-6 from all others has been shown; see
  items 9a and 11 on ~ http://us.metamath.org/award2003.html .

$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Axiom scheme ax-10 (Quantified Negation)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Quantified Negation.  Axiom C5-2 of [Monk2] p. 113.  This axiom
     scheme is logically redundant (see ~ ax10w ) but is used as an auxiliary
     axiom to achieve metalogical completeness.  It means that ` x ` is not
     free in ` -. A. x ph ` .  (Contributed by NM, 21-May-2008.)  Use its alias
     ~ hbn1 instead.  (New usage is discouraged.) $)
  ax-10 $a |- ( -. A. x ph -> A. x -. A. x ph ) $.

  $( Alias for ~ ax-10 to be used instead of it.  (Contributed by NM,
     24-Jan-1993.)  (Proof shortened by Wolf Lammen, 18-Aug-2014.) $)
  hbn1 $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
    ( ax-10 ) ABC $.

  $( ` x ` is not free in ` E. x ph ` .  (Contributed by NM, 24-Jan-1993.) $)
  hbe1 $p |- ( E. x ph -> A. x E. x ph ) $=
    ( wex wn wal df-ex hbn1 hbxfrbi ) ABCADZBEDBABFIBGH $.

  $( ` x ` is not free in ` E. x ph ` .  (Contributed by Mario Carneiro,
     11-Aug-2016.) $)
  nfe1 $p |- F/ x E. x ph $=
    ( wex hbe1 nfi ) ABCBABDE $.

  $( The analog in our predicate calculus of axiom 5 of modal logic S5.
     (Contributed by NM, 5-Oct-2005.) $)
  modal-5 $p |- ( -. A. x -. ph -> A. x -. A. x -. ph ) $=
    ( wn hbn1 ) ACBD $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
            Axiom scheme ax-11 (Quantifier Commutation)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Quantifier Commutation.  This axiom says universal quantifiers
     can be swapped.  Axiom scheme C6' in [Megill] p. 448 (p. 16 of the
     preprint).  Also appears as Lemma 12 of [Monk2] p. 109 and Axiom C5-3 of
     [Monk2] p. 113.  This axiom scheme is logically redundant (see ~ ax11w )
     but is used as an auxiliary axiom to achieve metalogical completeness.
     (Contributed by NM, 12-Mar-1993.) $)
  ax-11 $a |- ( A. x A. y ph -> A. y A. x ph ) $.

  ${
    alcoms.1 $e |- ( A. x A. y ph -> ps ) $.
    $( Swap quantifiers in an antecedent.  (Contributed by NM, 11-May-1993.) $)
    alcoms $p |- ( A. y A. x ph -> ps ) $=
      ( wal ax-11 syl ) ACFDFADFCFBADCGEH $.
  $}

  ${
    hbal.1 $e |- ( ph -> A. x ph ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` A. y ph ` .
       (Contributed by NM, 12-Mar-1993.) $)
    hbal $p |- ( A. y ph -> A. x A. y ph ) $=
      ( wal alimi ax-11 syl ) ACEZABEZCEIBEAJCDFACBGH $.
  $}

  $( Theorem 19.5 of [Margaris] p. 89.  (Contributed by NM, 30-Jun-1993.) $)
  alcom $p |- ( A. x A. y ph <-> A. y A. x ph ) $=
    ( wal ax-11 impbii ) ACDBDABDCDABCEACBEF $.

  $( Theorem *11.21 in [WhiteheadRussell] p. 160.  (Contributed by Andrew
     Salmon, 24-May-2011.) $)
  alrot3 $p |- ( A. x A. y A. z ph <-> A. y A. z A. x ph ) $=
    ( wal alcom albii bitri ) ADEZCEBEIBEZCEABEDEZCEIBCFJKCABDFGH $.

  $( Rotate 4 universal quantifiers twice.  (Contributed by NM, 2-Feb-2005.)
     (Proof shortened by Fan Zheng, 6-Jun-2016.) $)
  alrot4 $p |- ( A. x A. y A. z A. w ph <-> A. z A. w A. x A. y ph ) $=
    ( wal alrot3 albii bitri ) AEFDFCFZBFACFZEFDFZBFKBFEFDFJLBACDEGHKBDEGI $.

  ${
    hbald.1 $e |- ( ph -> A. y ph ) $.
    hbald.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbal .
       (Contributed by NM, 2-Jan-2002.) $)
    hbald $p |- ( ph -> ( A. y ps -> A. x A. y ps ) ) $=
      ( wal alimdh ax-11 syl6 ) ABDGZBCGZDGKCGABLDEFHBDCIJ $.
  $}

  $( Theorem 19.11 of [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.)
     Remove dependencies on ~ ax-12 , ~ ax-10 , ~ ax-6 , ~ ax-7 and ~ ax-5 .
     (Revised by Wolf Lammen, 8-Jan-2018.) $)
  excom $p |- ( E. x E. y ph <-> E. y E. x ph ) $=
    ( wn wal wex alcom notbii exnal 3bitr4i df-ex exbii ) ADZCEZDZBFZMBEZDZCFZA
    CFZBFABFZCFNBEZDQCEZDPSUBUCMBCGHNBIQCIJTOBACKLUARCABKLJ $.

  $( One direction of Theorem 19.11 of [Margaris] p. 89.  (Contributed by NM,
     5-Aug-1993.)  (Revised by Mario Carneiro, 24-Sep-2016.)  Remove
     dependencies on ~ ax-12 , ~ ax-10 , ~ ax-6 , ~ ax-7 and ~ ax-5 .  (Revised
     by Wolf Lammen, 8-Jan-2018.) $)
  excomim $p |- ( E. x E. y ph -> E. y E. x ph ) $=
    ( wex excom biimpi ) ACDBDABDCDABCEF $.

  $( Swap 1st and 3rd existential quantifiers.  (Contributed by NM,
     9-Mar-1995.) $)
  excom13 $p |- ( E. x E. y E. z ph <-> E. z E. y E. x ph ) $=
    ( wex excom exbii 3bitri ) ADEZCEBEIBEZCEABEZDEZCEKCEDEIBCFJLCABDFGKCDFH $.

  $( Rotate existential quantifiers.  (Contributed by NM, 17-Mar-1995.) $)
  exrot3 $p |- ( E. x E. y E. z ph <-> E. y E. z E. x ph ) $=
    ( wex excom13 excom bitri ) ADECEBEABEZCEDEIDECEABCDFIDCGH $.

  $( Rotate existential quantifiers twice.  (Contributed by NM, 9-Mar-1995.) $)
  exrot4 $p |- ( E. x E. y E. z E. w ph <-> E. z E. w E. x E. y ph ) $=
    ( wex excom13 exbii bitri ) AEFDFCFZBFACFZDFEFZBFKBFEFDFJLBACDEGHKBEDGI $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           Axiom scheme ax-12 (Substitution)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Substitution.  One of the 5 equality axioms of predicate
     calculus.  The final consequent ` A. x ( x = y -> ph ) ` is a way of
     expressing "" ` y ` substituted for ` x ` in wff ` ph ` "" (cf. ~ sb6 ).  It
     is based on Lemma 16 of [Tarski] p. 70 and Axiom C8 of [Monk2] p. 105,
     from which it can be proved by cases.

     The original version of this axiom was ~ ax-c15 and was replaced with this
     shorter ~ ax-12 in Jan. 2007.  The old axiom is proved from this one as
     theorem ~ axc15 .  Conversely, this axiom is proved from ~ ax-c15 as
     theorem ~ ax12 .

     Juha Arpiainen proved the metalogical independence of this axiom (in the
     form of the older axiom ~ ax-c15 ) from the others on 19-Jan-2006.  See
     item 9a at ~ http://us.metamath.org/award2003.html .

     See ~ ax12v and ~ ax12v2 for other equivalents of this axiom that (unlike
     this axiom) have distinct variable restrictions.

     This axiom scheme is logically redundant (see ~ ax12w ) but is used as an
     auxiliary axiom to achieve metalogical completeness.  (Contributed by NM,
     22-Jan-2007.) $)
  ax-12 $a |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $.

  ${
    $d x y z $.  $d ph z $.
    $( This is a version of ~ ax-12 when the variables are distinct.  Axiom
       (C8) of [Monk2] p. 105.  See theorem ~ ax12v2 for the rederivation of
       ~ ax-c15 from this theorem.  (Contributed by NM, 5-Aug-1993.)  Removed
       dependencies on ~ ax-10 and ~ ax-13 .  (Revised by Jim Kingdon,
       15-Dec-2017.)  (Proof shortened by Wolf Lammen, 8-Dec-2019.) $)
    ax12v $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      ( vz weq wex wi ax6ev equequ2 biimprd ax-5 ax-12 syl5 imim1d alimdv syl9r
      wal syld exlimiv ax-mp ) DCEZDFBCEZAUBAGZBQZGZGZDCHUAUFDUAUBBDEZUEUAUGUBD
      CBIJZUGAUGAGZBQZUAUDAADQUGUJADKABDLMUAUIUCBUAUBUGAUHNOPRST $.
  $}

  ${
    $d x y z $.  $d ph z $.
    $( Obsolete proof of ~ ax12v as of 8-Dec-2019.  (Contributed by Jim
       Kingdon, 15-Dec-2017.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax12vOLD $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      ( vz cv wceq wex wi ax6ev ax-5 ax-12 equequ2 imbi1d albidv imbi2d imbi12d
      wal syl5 mpbii exlimiv ax-mp ) DEZCEZFZDGBEZUCFZAUFAHZBQZHZHZDCIUDUJDUDUE
      UBFZAUKAHZBQZHZHUJAADQUKUMADJABDKRUDUKUFUNUIDCBLZUDUMUHAUDULUGBUDUKUFAUOM
      NOPSTUA $.
  $}

  ${
    $d x w $.  $d w ph $.
    $( If a wff is true, it is true for at least one instance.  Special case of
       Theorem 19.8 of [Margaris] p. 89.  See ~ 19.8v for a version requiring
       fewer axioms.  (Contributed by NM, 9-Jan-1993.)  Allow a shortening of
       ~ sp .  (Revised by Wolf Lammen, 13-Jan-2018.)  (Proof shortened by Wolf
       Lammen, 8-Dec-2019.) $)
    19.8a $p |- ( ph -> E. x ph ) $=
      ( vw weq wex wi ax6ev wal ax12v exim syl6mpi equcoms exlimiv ax-mp ) CBDZ
      CEAABEZFZCBGOQCQBCBCDZARAFBHRBEPABCIBCGRABJKLMN $.
  $}

  ${
    $d x w $.  $d w ph $.
    $( Obsolete proof of ~ 19.8a as of 8-Dec-2019.  (Contributed by NM,
       9-Jan-1993.)  (Revised by Wolf Lammen, 13-Jan-2018.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    19.8aOLD $p |- ( ph -> E. x ph ) $=
      ( vw weq wex wi ax6ev wal ax-5 ax-12 exim mpi syl56 equcoms exlimiv ax-mp
      ) CBDZCEAABEZFZCBGQSCSBCAACHBCDZTAFBHZRACIABCJUATBERBCGTABKLMNOP $.
  $}

  ${
    $( Specialization.  A universally quantified wff implies the wff without a
       quantifier Axiom scheme B5 of [Tarski] p. 67 (under his system S2,
       defined in the last paragraph on p. 77).  Also appears as Axiom scheme
       C5' in [Megill] p. 448 (p. 16 of the preprint).

       For the axiom of specialization presented in many logic textbooks, see
       theorem ~ stdpc4 .

       This theorem shows that our obsolete axiom ~ ax-c5 can be derived from
       the others.  The proof uses ideas from the proof of Lemma 21 of [Monk2]
       p. 114.

       It appears that this scheme cannot be derived directly from Tarski's
       axioms without auxiliary axiom scheme ~ ax-12 .  It is thought the best
       we can do using only Tarski's axioms is ~ spw .  (Contributed by NM,
       21-May-2008.)  (Proof shortened by Scott Fenton, 24-Jan-2011.)  (Proof
       shortened by Wolf Lammen, 13-Jan-2018.) $)
    sp $p |- ( A. x ph -> ph ) $=
      ( wal wn wex alex 19.8a con1i sylbi ) ABCADZBEZDAABFAKJBGHI $.
  $}

  $( Show that the original axiom ~ ax-c4 can be derived from ~ ax-4 and
     others.  See ~ ax4 for the rederivation of ~ ax-4 from ~ ax-c4 .

     Part of the proof is based on the proof of Lemma 22 of [Monk2] p. 114.
     (Contributed by NM, 21-May-2008.)  (Proof modification is discouraged.) $)
  axc4 $p |- ( A. x ( A. x ph -> ps ) -> ( A. x ph -> A. x ps ) ) $=
    ( wal wi wn sp con2i hbn1 con1i alimi 3syl alim syl5 ) ACDZOCDZOBECDBCDOOFZ
    CDZFZSCDPROQCGHQCISOCORACIJKLOBCMN $.

  $( Show that the original axiom ~ ax-c7 can be derived from ~ ax-10 and
     others.  See ~ ax10 for the rederivation of ~ ax-10 from ~ ax-c7 .

     Normally, ~ axc7 should be used rather than ~ ax-c7 , except by theorems
     specifically studying the latter's properties.  (Contributed by NM,
     21-May-2008.) $)
  axc7 $p |- ( -. A. x -. A. x ph -> ph ) $=
    ( wal wn sp hbn1 nsyl4 ) ABCZAHDBCABEABFG $.

  $( Abbreviated version of ~ axc7 .  (Contributed by NM, 5-Aug-1993.) $)
  axc7e $p |- ( E. x A. x ph -> ph ) $=
    ( wal wex wn df-ex axc7 sylbi ) ABCZBDIEBCEAIBFABGH $.

  $( The analog in our predicate calculus of the Brouwer axiom (B) of modal
     logic S5.  (Contributed by NM, 5-Oct-2005.) $)
  modal-b $p |- ( ph -> A. x -. A. x -. ph ) $=
    ( wn wal axc7 con4i ) ACZBDCBDAGBEF $.

  ${
    spi.1 $e |- A. x ph $.
    $( Inference rule reversing generalization.  (Contributed by NM,
       5-Aug-1993.) $)
    spi $p |- ph $=
      ( wal sp ax-mp ) ABDACABEF $.
  $}

  ${
    sps.1 $e |- ( ph -> ps ) $.
    $( Generalization of antecedent.  (Contributed by NM, 5-Jan-1993.) $)
    sps $p |- ( A. x ph -> ps ) $=
      ( wal sp syl ) ACEABACFDG $.
  $}

  $( A double specialization (see ~ sp ).  Another double specialization,
     closer to PM*11.1, is ~ 2stdpc4 .  (Contributed by BJ, 15-Sep-2018.) $)
  2sp $p |- ( A. x A. y ph -> ph ) $=
    ( wal sp sps ) ACDABACEF $.

  ${
    spsd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction generalizing antecedent.  (Contributed by NM, 17-Aug-1994.) $)
    spsd $p |- ( ph -> ( A. x ps -> ch ) ) $=
      ( wal sp syl5 ) BDFBACBDGEH $.
  $}

  $( Theorem 19.2 of [Margaris] p. 89, generalized to use two setvar
     variables.  Use ~ 19.2 when sufficient.  (Contributed by Mel L. O'Cat,
     31-Mar-2008.) $)
  19.2g $p |- ( A. x ph -> E. y ph ) $=
    ( wex 19.8a sps ) AACDBACEF $.

  ${
    19.21bi.1 $e |- ( ph -> A. x ps ) $.
    $( Inference form of ~ 19.21 and also deduction form of ~ sp .
       (Contributed by NM, 26-May-1993.) $)
    19.21bi $p |- ( ph -> ps ) $=
      ( wal sp syl ) ABCEBDBCFG $.
  $}

  ${
    19.21bbi.1 $e |- ( ph -> A. x A. y ps ) $.
    $( Inference removing double quantifier.  Version of ~ 19.21bi with two
       quanditiers.  (Contributed by NM, 20-Apr-1994.) $)
    19.21bbi $p |- ( ph -> ps ) $=
      ( wal 19.21bi ) ABDABDFCEGG $.
  $}

  ${
    19.23bi.1 $e |- ( E. x ph -> ps ) $.
    $( Inference form of Theorem 19.23 of [Margaris] p. 90, see ~ 19.23 .
       (Contributed by NM, 12-Mar-1993.) $)
    19.23bi $p |- ( ph -> ps ) $=
      ( wex 19.8a syl ) AACEBACFDG $.
  $}

  ${
    nexr.1 $e |- -. E. x ph $.
    $( Inference form of ~ 19.8a .  (Contributed by Jeff Hankins,
       26-Jul-2009.) $)
    nexr $p |- -. ph $=
      ( wex 19.8a mto ) AABDCABEF $.
  $}

  $( Consequence of the definition of not-free.  (Contributed by Mario
     Carneiro, 26-Sep-2016.) $)
  nfr $p |- ( F/ x ph -> ( ph -> A. x ph ) ) $=
    ( wnf wal wi df-nf sp sylbi ) ABCAABDEZBDIABFIBGH $.

  ${
    nfri.1 $e |- F/ x ph $.
    $( Consequence of the definition of not-free.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
    nfri $p |- ( ph -> A. x ph ) $=
      ( wnf wal wi nfr ax-mp ) ABDAABEFCABGH $.
  $}

  ${
    nfrd.1 $e |- ( ph -> F/ x ps ) $.
    $( Consequence of the definition of not-free in a context.  (Contributed by
       Mario Carneiro, 11-Aug-2016.) $)
    nfrd $p |- ( ph -> ( ps -> A. x ps ) ) $=
      ( wnf wal wi nfr syl ) ABCEBBCFGDBCHI $.
  $}

  ${
    alimd.1 $e |- F/ x ph $.
    alimd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.20 of [Margaris] p. 90, see ~ alim .
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    alimd $p |- ( ph -> ( A. x ps -> A. x ch ) ) $=
      ( nfri alimdh ) ABCDADEGFH $.
  $}

  ${
    alrimi.1 $e |- F/ x ph $.
    alrimi.2 $e |- ( ph -> ps ) $.
    $( Inference form of Theorem 19.21 of [Margaris] p. 90, see ~ 19.21 .
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    alrimi $p |- ( ph -> A. x ps ) $=
      ( nfri alrimih ) ABCACDFEG $.
  $}

  ${
    nfd.1 $e |- F/ x ph $.
    nfd.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduce that ` x ` is not free in ` ps ` in a context.  (Contributed by
       Mario Carneiro, 24-Sep-2016.) $)
    nfd $p |- ( ph -> F/ x ps ) $=
      ( wal wi wnf alrimi df-nf sylibr ) ABBCFGZCFBCHALCDEIBCJK $.
  $}

  ${
    nfdh.1 $e |- ( ph -> A. x ph ) $.
    nfdh.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduce that ` x ` is not free in ` ps ` in a context.  (Contributed by
       Mario Carneiro, 24-Sep-2016.) $)
    nfdh $p |- ( ph -> F/ x ps ) $=
      ( nfi nfd ) ABCACDFEG $.
  $}

  ${
    alrimdd.1 $e |- F/ x ph $.
    alrimdd.2 $e |- ( ph -> F/ x ps ) $.
    alrimdd.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.21 of [Margaris] p. 90, see ~ 19.21 .
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    alrimdd $p |- ( ph -> ( ps -> A. x ch ) ) $=
      ( wal nfrd alimd syld ) ABBDHCDHABDFIABCDEGJK $.
  $}

  ${
    alrimd.1 $e |- F/ x ph $.
    alrimd.2 $e |- F/ x ps $.
    alrimd.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.21 of [Margaris] p. 90, see ~ 19.21 .
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    alrimd $p |- ( ph -> ( ps -> A. x ch ) ) $=
      ( wnf a1i alrimdd ) ABCDEBDHAFIGJ $.
  $}

  ${
    eximd.1 $e |- F/ x ph $.
    eximd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.22 of [Margaris] p. 90, see ~ exim .
       (Contributed by NM, 29-Jun-1993.)  (Revised by Mario Carneiro,
       24-Sep-2016.) $)
    eximd $p |- ( ph -> ( E. x ps -> E. x ch ) ) $=
      ( nfri eximdh ) ABCDADEGFH $.
  $}

  ${
    nexd.1 $e |- F/ x ph $.
    nexd.2 $e |- ( ph -> -. ps ) $.
    $( Deduction for generalization rule for negated wff.  (Contributed by
       Mario Carneiro, 24-Sep-2016.) $)
    nexd $p |- ( ph -> -. E. x ps ) $=
      ( nfri nexdh ) ABCACDFEG $.
  $}

  ${
    $d x ph $.
    nexdv.1 $e |- ( ph -> -. ps ) $.
    $( Deduction for generalization rule for negated wff.  (Contributed by NM,
       5-Aug-1993.) $)
    nexdv $p |- ( ph -> -. E. x ps ) $=
      ( nfv nexd ) ABCACEDF $.
  $}

  ${
    albid.1 $e |- F/ x ph $.
    albid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for universal quantifier (deduction rule).
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    albid $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $=
      ( nfri albidh ) ABCDADEGFH $.
  $}

  ${
    exbid.1 $e |- F/ x ph $.
    exbid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for existential quantifier (deduction rule).
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    exbid $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $=
      ( nfri exbidh ) ABCDADEGFH $.
  $}

  ${
    nfbidf.1 $e |- F/ x ph $.
    nfbidf.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An equality theorem for effectively not free.  (Contributed by Mario
       Carneiro, 4-Oct-2016.) $)
    nfbidf $p |- ( ph -> ( F/ x ps <-> F/ x ch ) ) $=
      ( wal wi wnf albid imbi12d df-nf 3bitr4g ) ABBDGZHZDGCCDGZHZDGBDICDIAOQDE
      ABCNPFABCDEFJKJBDLCDLM $.
  $}

  ${
    19.3.1 $e |- F/ x ph $.
    $( A wff may be quantified with a variable not free in it.  Theorem 19.3 of
       [Margaris] p. 89.  See ~ 19.3v for a version requiring fewer axioms.
       (Contributed by NM, 12-Mar-1993.)  (Revised by Mario Carneiro,
       24-Sep-2016.) $)
    19.3 $p |- ( A. x ph <-> ph ) $=
      ( wal sp nfri impbii ) ABDAABEABCFG $.
  $}

  $( A closed version of ~ 19.9 .  (Contributed by NM, 13-May-1993.)  (Proof
     shortened by Wolf Lammen, 3-Mar-2018.) $)
  19.9ht $p |- ( A. x ( ph -> A. x ph ) -> ( E. x ph -> ph ) ) $=
    ( wal wi wex exim axc7e syl6 ) AABCZDBCABEIBEAAIBFABGH $.

  $( A closed version of ~ 19.9 .  (Contributed by NM, 13-May-1993.)  (Revised
     by Mario Carneiro, 24-Sep-2016.)  (Proof shortened by Wolf Lammen,
     30-Dec-2017.) $)
  19.9t $p |- ( F/ x ph -> ( E. x ph <-> ph ) ) $=
    ( wnf wex wal wi df-nf 19.9ht sylbi 19.8a impbid1 ) ABCZABDZALAABEFBEMAFABG
    ABHIABJK $.

  ${
    19.9h.1 $e |- ( ph -> A. x ph ) $.
    $( A wff may be existentially quantified with a variable not free in it.
       Theorem 19.9 of [Margaris] p. 89.  (Contributed by FL, 24-Mar-2007.)
       (Proof shortened by Wolf Lammen, 5-Jan-2018.) $)
    19.9h $p |- ( E. x ph <-> ph ) $=
      ( wnf wex wb nfi 19.9t ax-mp ) ABDABEAFABCGABHI $.
  $}

  ${
    19.9d.1 $e |- ( ps -> F/ x ph ) $.
    $( A deduction version of one direction of ~ 19.9 .  (Contributed by NM,
       14-May-1993.)  (Revised by Mario Carneiro, 24-Sep-2016.) $)
    19.9d $p |- ( ps -> ( E. x ph -> ph ) ) $=
      ( wex wnf wb 19.9t syl biimpd ) BACEZABACFKAGDACHIJ $.
  $}

  ${
    19.9.1 $e |- F/ x ph $.
    $( A wff may be existentially quantified with a variable not free in it.
       Theorem 19.9 of [Margaris] p. 89.  See ~ 19.9v for a version requiring
       fewer axioms.  (Contributed by FL, 24-Mar-2007.)  (Revised by Mario
       Carneiro, 24-Sep-2016.)  (Proof shortened by Wolf Lammen,
       30-Dec-2017.) $)
    19.9 $p |- ( E. x ph <-> ph ) $=
      ( nfri 19.9h ) ABABCDE $.
  $}

  $( Closed theorem version of bound-variable hypothesis builder ~ hbn .
     (Contributed by NM, 10-May-1993.)  (Proof shortened by Wolf Lammen,
     3-Mar-2018.) $)
  hbnt $p |- ( A. x ( ph -> A. x ph ) -> ( -. ph -> A. x -. ph ) ) $=
    ( wal wi wn wex df-ex 19.9ht syl5bir con1d ) AABCDBCZAEBCZALEABFKAABGABHIJ
    $.

  ${
    hbn.1 $e |- ( ph -> A. x ph ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` -. ph ` .
       (Contributed by NM, 10-Jan-1993.)  (Proof shortened by Wolf Lammen,
       17-Dec-2017.) $)
    hbn $p |- ( -. ph -> A. x -. ph ) $=
      ( wal wi wn hbnt mpg ) AABDEAFZIBDEBABGCH $.
  $}

  $( ` x ` is not free in ` A. x ph ` .  Example in Appendix in [Megill] p. 450
     (p. 19 of the preprint).  Also Lemma 22 of [Monk2] p. 114.  (Contributed
     by NM, 24-Jan-1993.)  (Proof shortened by Wolf Lammen, 15-Dec-2017.) $)
  hba1 $p |- ( A. x ph -> A. x A. x ph ) $=
    ( wal wn wex alex hbe1 hbn hbxfrbi ) ABCADZBEZDBABFKBJBGHI $.

  $( ` x ` is not free in ` A. x ph ` .  (Contributed by Mario Carneiro,
     11-Aug-2016.) $)
  nfa1 $p |- F/ x A. x ph $=
    ( wal hba1 nfi ) ABCBABDE $.

  ${
    axc4i.1 $e |- ( A. x ph -> ps ) $.
    $( Inference version of ~ axc4 .  (Contributed by NM, 3-Jan-1993.) $)
    axc4i $p |- ( A. x ph -> A. x ps ) $=
      ( wal nfa1 alrimi ) ACEBCACFDG $.
  $}

  $( ` x ` is not free in ` F/ x ph ` .  (Contributed by Mario Carneiro,
     11-Aug-2016.) $)
  nfnf1 $p |- F/ x F/ x ph $=
    ( wnf wal wi df-nf nfa1 nfxfr ) ABCAABDEZBDBABFIBGH $.

  $( If ` x ` is not free in ` ph ` , then it is not free in ` -. ph ` .
     (Contributed by Mario Carneiro, 24-Sep-2016.)  (Proof shortened by Wolf
     Lammen, 28-Dec-2017.)  (Revised by BJ, 24-Jul-2019.) $)
  nfnt $p |- ( F/ x ph -> F/ x -. ph ) $=
    ( wnf wn nfnf1 wal wi df-nf hbnt sylbi nfd ) ABCZADZBABELAABFGBFMMBFGABHABI
    JK $.

  ${
    nfn.1 $e |- F/ x ph $.
    $( Inference associated with ~ nfnt .  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nfn $p |- F/ x -. ph $=
      ( wnf wn nfnt ax-mp ) ABDAEBDCABFG $.
  $}

  ${
    nfnd.1 $e |- ( ph -> F/ x ps ) $.
    $( Deduction associated with ~ nfnt .  (Contributed by Mario Carneiro,
       24-Sep-2016.) $)
    nfnd $p |- ( ph -> F/ x -. ps ) $=
      ( wnf wn nfnt syl ) ABCEBFCEDBCGH $.
  $}

  $( A convenience theorem particularly designed to remove dependencies on
     ~ ax-11 in conjunction with disjunctors.  (Contributed by Wolf Lammen,
     2-Sep-2018.) $)
  nfna1 $p |- F/ x -. A. x ph $=
    ( wal nfa1 nfn ) ABCBABDE $.

  $( Closed form of Theorem 19.21 of [Margaris] p. 90, see ~ 19.21 .
     (Contributed by NM, 27-May-1997.)  (Revised by Mario Carneiro,
     24-Sep-2016.)  (Proof shortened by Wolf Lammen, 3-Jan-2018.) $)
  19.21t $p |- ( F/ x ph -> ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) ) $=
    ( wnf wi wal nfr alim syl9 wex 19.9t imbi1d 19.38 syl6bir impbid ) ACDZABEC
    FZABCFZEZPAACFQRACGABCHIPSACJZREQPTARACKLABCMNO $.

  ${
    19.21.1 $e |- F/ x ph $.
    $( Theorem 19.21 of [Margaris] p. 90.  The hypothesis can be thought of
       as "" ` x ` is not free in ` ph ` .""  See ~ 19.21v for a version
       requiring fewer axioms.  See also ~ 19.21h .  (Contributed by NM,
       14-May-1993.)  (Revised by Mario Carneiro, 24-Sep-2016.) $)
    19.21 $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $=
      ( wnf wi wal wb 19.21t ax-mp ) ACEABFCGABCGFHDABCIJ $.
  $}

  ${
    19.21-2.1 $e |- F/ x ph $.
    19.21-2.2 $e |- F/ y ph $.
    $( Version of ~ 19.21 with two quantifiers.  (Contributed by NM,
       4-Feb-2005.) $)
    19.21-2 $p |- ( A. x A. y ( ph -> ps ) <-> ( ph -> A. x A. y ps ) ) $=
      ( wi wal 19.21 albii bitri ) ABGDHZCHABDHZGZCHAMCHGLNCABDFIJAMCEIK $.
  $}

  ${
    19.21h.1 $e |- ( ph -> A. x ph ) $.
    $( Theorem 19.21 of [Margaris] p. 90.  The hypothesis can be thought of
       as "" ` x ` is not free in ` ph ` .""  See also ~ 19.21 and ~ 19.21v .
       (Contributed by NM, 1-Aug-2017.)  (Proof shortened by Wolf Lammen,
       1-Jan-2018.) $)
    19.21h $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $=
      ( nfi 19.21 ) ABCACDEF $.
  $}

  ${
    stdpc5.1 $e |- F/ x ph $.
    $( An axiom scheme of standard predicate calculus that emulates Axiom 5 of
       [Mendelson] p. 69.  The hypothesis ` F/ x ph ` can be thought of as
       emulating "" ` x ` is not free in ` ph ` .""  With this definition, the
       meaning of ""not free"" is less restrictive than the usual textbook
       definition; for example ` x ` would not (for us) be free in ` x = x ` by
       ~ nfequid .  This theorem scheme can be proved as a metatheorem of
       Mendelson's axiom system, even though it is slightly stronger than his
       Axiom 5.  See ~ stdpc5v for a version requiring fewer axioms.
       (Contributed by NM, 22-Sep-1993.)  (Revised by Mario Carneiro,
       12-Oct-2016.)  (Proof shortened by Wolf Lammen, 1-Jan-2018.) $)
    stdpc5 $p |- ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) ) $=
      ( wi wal 19.21 biimpi ) ABECFABCFEABCDGH $.
  $}

  $( Closed form of Theorem 19.23 of [Margaris] p. 90.  See ~ 19.23 .
     (Contributed by NM, 7-Nov-2005.)  (Proof shortened by Wolf Lammen,
     2-Jan-2018.) $)
  19.23t $p |- ( F/ x ps -> ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) ) $=
    ( wnf wi wal wex exim 19.9t biimpd syl9r nfr imim2d 19.38 syl6 impbid ) BCD
    ZABECFZACGZBEZRSBCGZQBABCHQUABBCIJKQTSBCFZERQBUBSBCLMABCNOP $.

  ${
    19.23.1 $e |- F/ x ps $.
    $( Theorem 19.23 of [Margaris] p. 90.  See ~ 19.23v for a version requiring
       fewer axioms.  (Contributed by NM, 24-Jan-1993.)  (Revised by Mario
       Carneiro, 24-Sep-2016.) $)
    19.23 $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $=
      ( wnf wi wal wex wb 19.23t ax-mp ) BCEABFCGACHBFIDABCJK $.
  $}

  ${
    19.23h.1 $e |- ( ps -> A. x ps ) $.
    $( Theorem 19.23 of [Margaris] p. 90.  See ~ 19.23 .  (Contributed by NM,
       24-Jan-1993.)  (Revised by Mario Carneiro, 24-Sep-2016.)  (Proof
       shortened by Wolf Lammen, 1-Jan-2018.) $)
    19.23h $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $=
      ( nfi 19.23 ) ABCBCDEF $.
  $}

  ${
    exlimi.1 $e |- F/ x ps $.
    exlimi.2 $e |- ( ph -> ps ) $.
    $( Inference associated with ~ 19.23 .  See ~ exlimiv for a version with a
       dv condition requiring fewer axioms.  (Contributed by NM, 10-Jan-1993.)
       (Revised by Mario Carneiro, 24-Sep-2016.) $)
    exlimi $p |- ( E. x ph -> ps ) $=
      ( wi wex 19.23 mpgbi ) ABFACGBFCABCDHEI $.
  $}

  ${
    exlimih.1 $e |- ( ps -> A. x ps ) $.
    exlimih.2 $e |- ( ph -> ps ) $.
    $( Inference associated with ~ 19.23 .  See ~ exlimiv for a version with a
       dv condition requiring fewer axioms.  (Contributed by NM, 10-Jan-1993.)
       (Proof shortened by Andrew Salmon, 13-May-2011.)  (Proof shortened by
       Wolf Lammen, 1-Jan-2018.) $)
    exlimih $p |- ( E. x ph -> ps ) $=
      ( nfi exlimi ) ABCBCDFEG $.
  $}

  ${
    exlimd.1 $e |- F/ x ph $.
    exlimd.2 $e |- F/ x ch $.
    exlimd.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.9 of [Margaris] p. 89.  (Contributed by NM,
       23-Jan-1993.)  (Revised by Mario Carneiro, 24-Sep-2016.)  (Proof
       shortened by Wolf Lammen, 12-Jan-2018.) $)
    exlimd $p |- ( ph -> ( E. x ps -> ch ) ) $=
      ( wex eximd 19.9 syl6ib ) ABDHCDHCABCDEGICDFJK $.
  $}

  ${
    exlimdh.1 $e |- ( ph -> A. x ph ) $.
    exlimdh.2 $e |- ( ch -> A. x ch ) $.
    exlimdh.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction form of Theorem 19.9 of [Margaris] p. 89.  (Contributed by NM,
       28-Jan-1997.) $)
    exlimdh $p |- ( ph -> ( E. x ps -> ch ) ) $=
      ( nfi exlimd ) ABCDADEHCDFHGI $.
  $}

  ${
    nfdi.1 $e |- ( ph -> F/ x ph ) $.
    $( Since the converse holds by ~ a1i , this inference shows that we can
       represent a not-free hypothesis with either ` F/ x ph ` (inference form)
       or ` ( ph -> F/ x ph ) ` (deduction form).  (Contributed by NM,
       17-Aug-2018.)  (Proof shortened by Wolf Lammen, 10-Jul-2019.) $)
    nfdi $p |- F/ x ph $=
      ( wal nfrd pm2.43i nfi ) ABAABDAABCEFG $.
  $}

  ${
    nfimd.1 $e |- ( ph -> F/ x ps ) $.
    nfimd.2 $e |- ( ph -> F/ x ch ) $.
    $( If in a context ` x ` is not free in ` ps ` and ` ch ` , it is not free
       in ` ( ps -> ch ) ` .  (Contributed by Mario Carneiro, 24-Sep-2016.)
       (Proof shortened by Wolf Lammen, 30-Dec-2017.) $)
    nfimd $p |- ( ph -> F/ x ( ps -> ch ) ) $=
      ( wnf wal nfnf1 nfr imim2d 19.21t biimprd syl9r alrimd df-nf syl6ibr sylc
      wi ) ABDGZCDGZBCSZDGZEFTUAUBUBDHZSZDHUCTUAUEDBDICDIUAUBBCDHZSZTUDUACUFBCD
      JKTUDUGBCDLMNOUBDPQR $.
  $}

  ${
    hbim1.1 $e |- ( ph -> A. x ph ) $.
    hbim1.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( A closed form of ~ hbim .  (Contributed by NM, 2-Jun-1993.) $)
    hbim1 $p |- ( ( ph -> ps ) -> A. x ( ph -> ps ) ) $=
      ( wi wal a2i 19.21h sylibr ) ABFZABCGZFKCGABLEHABCDIJ $.
  $}

  ${
    nfim1.1 $e |- F/ x ph $.
    nfim1.2 $e |- ( ph -> F/ x ps ) $.
    $( A closed form of ~ nfim .  (Contributed by NM, 2-Jun-1993.)  (Revised by
       Mario Carneiro, 24-Sep-2016.)  (Proof shortened by Wolf Lammen,
       2-Jan-2018.) $)
    nfim1 $p |- F/ x ( ph -> ps ) $=
      ( wi nfri nfrd hbim1 nfi ) ABFCABCACDGABCEHIJ $.
  $}

  ${
    nfim.1 $e |- F/ x ph $.
    nfim.2 $e |- F/ x ps $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph -> ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.)
       (Proof shortened by Wolf Lammen, 2-Jan-2018.) $)
    nfim $p |- F/ x ( ph -> ps ) $=
      ( wnf a1i nfim1 ) ABCDBCFAEGH $.
  $}

  ${
    hbimd.1 $e |- ( ph -> A. x ph ) $.
    hbimd.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    hbimd.3 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbim .
       (Contributed by NM, 14-May-1993.)  (Proof shortened by Wolf Lammen,
       3-Jan-2018.) $)
    hbimd $p |- ( ph -> ( ( ps -> ch ) -> A. x ( ps -> ch ) ) ) $=
      ( wi nfdh nfimd nfrd ) ABCHDABCDABDEFIACDEGIJK $.
  $}

  ${
    hbim.1 $e |- ( ph -> A. x ph ) $.
    hbim.2 $e |- ( ps -> A. x ps ) $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph -> ps ) ` .  (Contributed by NM, 24-Jan-1993.)  (Proof shortened
       by Mel L. O'Cat, 3-Mar-2008.)  (Proof shortened by Wolf Lammen,
       1-Jan-2018.) $)
    hbim $p |- ( ( ph -> ps ) -> A. x ( ph -> ps ) ) $=
      ( wal wi a1i hbim1 ) ABCDBBCFGAEHI $.
  $}

  ${
    19.27.1 $e |- F/ x ps $.
    $( Theorem 19.27 of [Margaris] p. 90.  See ~ 19.27v for a version requiring
       fewer axioms.  (Contributed by NM, 21-Jun-1993.) $)
    19.27 $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ ps ) ) $=
      ( wa wal 19.26 19.3 anbi2i bitri ) ABECFACFZBCFZEKBEABCGLBKBCDHIJ $.
  $}

  ${
    19.28.1 $e |- F/ x ph $.
    $( Theorem 19.28 of [Margaris] p. 90.  See ~ 19.28v for a version requiring
       fewer axioms.  (Contributed by NM, 1-Aug-1993.) $)
    19.28 $p |- ( A. x ( ph /\ ps ) <-> ( ph /\ A. x ps ) ) $=
      ( wa wal 19.26 19.3 anbi1i bitri ) ABECFACFZBCFZEALEABCGKALACDHIJ $.
  $}

  ${
    nfand.1 $e |- ( ph -> F/ x ps ) $.
    nfand.2 $e |- ( ph -> F/ x ch ) $.
    $( If in a context ` x ` is not free in ` ps ` and ` ch ` , it is not free
       in ` ( ps /\ ch ) ` .  (Contributed by Mario Carneiro, 7-Oct-2016.) $)
    nfand $p |- ( ph -> F/ x ( ps /\ ch ) ) $=
      ( wa wn wi df-an nfnd nfimd nfxfrd ) BCGBCHZIZHADBCJAODABNDEACDFKLKM $.

    nfand.3 $e |- ( ph -> F/ x th ) $.
    $( Deduction form of bound-variable hypothesis builder ~ nf3an .
       (Contributed by NM, 17-Feb-2013.)  (Revised by Mario Carneiro,
       16-Oct-2016.) $)
    nf3and $p |- ( ph -> F/ x ( ps /\ ch /\ th ) ) $=
      ( w3a wa df-3an nfand nfxfrd ) BCDIBCJZDJAEBCDKANDEABCEFGLHLM $.
  $}

  ${
    nfan1.1 $e |- F/ x ph $.
    nfan1.2 $e |- ( ph -> F/ x ps ) $.
    $( A closed form of ~ nfan .  (Contributed by Mario Carneiro,
       3-Oct-2016.) $)
    nfan1 $p |- F/ x ( ph /\ ps ) $=
      ( wa wal nfrd imdistani 19.28 sylibr nfi ) ABFZCMABCGZFMCGABNABCEHIABCDJK
      L $.
  $}

  ${
    nfan.1 $e |- F/ x ph $.
    nfan.2 $e |- F/ x ps $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph /\ ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.)
       (Proof shortened by Wolf Lammen, 13-Jan-2018.) $)
    nfan $p |- F/ x ( ph /\ ps ) $=
      ( wnf a1i nfan1 ) ABCDBCFAEGH $.

    $( If ` x ` is not free in ` ph ` and ` ps ` , then it is not free in
       ` ( ph -/\ ps ) ` .  (Contributed by Scott Fenton, 2-Jan-2018.) $)
    nfnan $p |- F/ x ( ph -/\ ps ) $=
      ( wnan wa wn df-nan nfan nfn nfxfr ) ABFABGZHCABIMCABCDEJKL $.

    nfan.3 $e |- F/ x ch $.
    $( If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , it is not free in
       ` ( ph /\ ps /\ ch ) ` .  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nf3an $p |- F/ x ( ph /\ ps /\ ch ) $=
      ( w3a wa df-3an nfan nfxfr ) ABCHABIZCIDABCJMCDABDEFKGKL $.
  $}

  ${
    hb.1 $e |- ( ph -> A. x ph ) $.
    hb.2 $e |- ( ps -> A. x ps ) $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph /\ ps ) ` .  (Contributed by NM, 14-May-1993.)  (Proof shortened
       by Wolf Lammen, 2-Jan-2018.) $)
    hban $p |- ( ( ph /\ ps ) -> A. x ( ph /\ ps ) ) $=
      ( wa nfi nfan nfri ) ABFCABCACDGBCEGHI $.
    hb.3 $e |- ( ch -> A. x ch ) $.
    $( If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , it is not free in
       ` ( ph /\ ps /\ ch ) ` .  (Contributed by NM, 14-Sep-2003.)  (Proof
       shortened by Wolf Lammen, 2-Jan-2018.) $)
    hb3an $p |- ( ( ph /\ ps /\ ch ) -> A. x ( ph /\ ps /\ ch ) ) $=
      ( w3a nfi nf3an nfri ) ABCHDABCDADEIBDFICDGIJK $.
  $}

  ${
    nfbid.1 $e |- ( ph -> F/ x ps ) $.
    nfbid.2 $e |- ( ph -> F/ x ch ) $.
    $( If in a context ` x ` is not free in ` ps ` and ` ch ` , it is not free
       in ` ( ps <-> ch ) ` .  (Contributed by Mario Carneiro, 24-Sep-2016.)
       (Proof shortened by Wolf Lammen, 29-Dec-2017.) $)
    nfbid $p |- ( ph -> F/ x ( ps <-> ch ) ) $=
      ( wb wi wa dfbi2 nfimd nfand nfxfrd ) BCGBCHZCBHZIADBCJANODABCDEFKACBDFEK
      LM $.
  $}

  ${
    nf.1 $e |- F/ x ph $.
    nf.2 $e |- F/ x ps $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph <-> ps ) ` .  (Contributed by NM, 26-May-1993.)  (Revised by
       Mario Carneiro, 11-Aug-2016.)  (Proof shortened by Wolf Lammen,
       2-Jan-2018.) $)
    nfbi $p |- F/ x ( ph <-> ps ) $=
      ( wb wnf wtru a1i nfbid trud ) ABFCGHABCACGHDIBCGHEIJK $.

    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph \/ ps ) ` .  (Contributed by NM, 5-Aug-1993.)  (Revised by Mario
       Carneiro, 11-Aug-2016.) $)
    nfor $p |- F/ x ( ph \/ ps ) $=
      ( wo wn wi df-or nfn nfim nfxfr ) ABFAGZBHCABIMBCACDJEKL $.

    nf.3 $e |- F/ x ch $.
    $( If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , it is not free in
       ` ( ph \/ ps \/ ch ) ` .  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nf3or $p |- F/ x ( ph \/ ps \/ ch ) $=
      ( w3o wo df-3or nfor nfxfr ) ABCHABIZCIDABCJMCDABDEFKGKL $.
  $}

  $( Same as ~ axc11 but with reversed antecedent.  (Contributed by NM,
     25-Jul-2015.) $)
  axc112 $p |- ( A. y y = x -> ( A. x ph -> A. y ph ) ) $=
    ( weq wal wi ax-12 sps pm2.27 al2imi syld ) CBDZCEABEZLAFZCEZACELMOFCACBGHL
    NACLAIJK $.

  ${
    $d x z $.  $d y z $.
    axc11nlem.1 $e |- ( -. A. y y = x -> ( x = z -> A. y x = z ) ) $.
    $( Lemma for ~ axc11n .  Change bound variable in an equality.
       (Contributed by NM, 8-Jul-2016.)  (Proof shortened by Wolf Lammen,
       17-Feb-2018.)  Restructure to ease either bundling, or reducing
       dependencies on axioms.  (Revised by Wolf Lammen, 30-Nov-2019.) $)
    axc11nlem $p |- ( A. x x = z -> A. y y = x ) $=
      ( weq wal cbvaev equequ2 biimprd al2imi syl5com spsd com12 con1d pm2.61d
      wn ) ACEZAFZQBFZBAEZBFZRBCEZBFSUAABCGQUBTBQTUBACBHIJKRUASUAPZRSUCQSADLMNO
      $.
  $}

  ${
    $d v w z $.  $d v x y $.
    $( Lemma for ~ aev and ~ axc16g .  Change free and bound variables.
       (Contributed by NM, 22-Jul-2015.)  (Proof shortened by Wolf Lammen,
       17-Feb-2018.)  Remove dependency on ~ ax-13 , along an idea of BJ.
       (Revised by Wolf Lammen, 30-Nov-2019.) $)
    aevlem1 $p |- ( A. z z = w -> A. y y = x ) $=
      ( vv weq wal cbvaev wn ax5d axc11nlem 4syl ) CDFCGEDFZEGCEFCGZAEFZAGBAFBG
      ZCEDHECDNIMCJKCAEHABEPIOBJKL $.
  $}

  ${
    $d w x y $.  $d w z $.  $d w ph $.
    $( Generalization of ~ axc16 .  Use the latter when sufficient.
       (Contributed by NM, 15-May-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.)  (Proof shortened by Wolf Lammen, 18-Feb-2018.)  Remove
       dependency on ~ ax-13 , along an idea of BJ. (Revised by Wolf Lammen,
       30-Nov-2019.) $)
    axc16g $p |- ( A. x x = y -> ( ph -> A. z ph ) ) $=
      ( vw weq wal aevlem1 ax-5 axc112 syl2im ) BCFBGDEFDGAAEGADGEDBCHAEIAEDJK
      $.
  $}

  ${
    $d x y z $.  $d z ph $.
    $( Proof of older axiom ~ ax-c16 .  (Contributed by NM, 8-Nov-2006.)
       (Revised by NM, 22-Sep-2017.) $)
    axc16 $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      ( axc16g ) ABCBD $.
  $}

  ${
    $d x y $.
    $( A generalization of axiom ~ ax-c16 .  (Contributed by NM,
       15-May-1993.) $)
    ax16gb $p |- ( A. x x = y -> ( ph <-> A. z ph ) ) $=
      ( weq wal axc16g sp impbid1 ) BCEBFAADFABCDGADHI $.
  $}

  ${
    $d u v $.  $d u x y $.  $d u w $.
    $( A ""distinctor elimination"" lemma with no restrictions on variables in
       the consequent.  (Contributed by NM, 8-Nov-2006.)  Remove dependency on
       ~ ax-11 .  (Revised by Wolf Lammen, 7-Sep-2018.)  Remove dependency on
       ~ ax-13 , inspired by an idea of BJ. (Revised by Wolf Lammen,
       30-Nov-2019.) $)
    aev $p |- ( A. x x = y -> A. z w = v ) $=
      ( vu weq wal wex aevlem1 ax6ev ax-7 aleximi mpi ax5e 3syl axc16g mpd ) AB
      GAHZDEGZTCHSFDGZFHZTFIZTDFABJUBFEGZFIUCFEKUAUDTFFDELMNTFOPTABCQR $.
  $}

  ${
    $d x y $.  $d z w $.
    $( If ~ dtru is false, then there is only one element in the universe, so
       everything satisfies ` F/ ` .  (Contributed by Mario Carneiro,
       7-Oct-2016.)  Remove dependency on ~ ax-11 .  (Revised by Wolf Lammen,
       9-Sep-2018.)  (Proof shortened by BJ, 14-Jun-2019.) $)
    ax16nf $p |- ( A. x x = y -> F/ z ph ) $=
      ( vw weq wal wnf aev nfa1 axc16 nfd syl ) BCFBGDEFZDGZADHBCDDEIOADNDJADEK
      LM $.
  $}

  ${
    $d x y $.
    equsalhw.1 $e |- ( ps -> A. x ps ) $.
    equsalhw.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Weaker version of ~ equsalh (requiring distinct variables) without using
       ~ ax-13 .  (Contributed by NM, 29-Nov-2015.)  (Proof shortened by Wolf
       Lammen, 28-Dec-2017.) $)
    equsalhw $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      ( weq wi wal wex 19.23h pm5.74i albii ax6ev a1bi 3bitr4i ) CDGZBHZCIQCJZB
      HQAHZCIBQBCEKTRCQABFLMSBCDNOP $.
  $}

  ${
    hbex.1 $e |- ( ph -> A. x ph ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` E. y ph ` .
       (Contributed by NM, 12-Mar-1993.) $)
    hbex $p |- ( E. y ph -> A. x E. y ph ) $=
      ( wex wn wal df-ex hbn hbal hbxfrbi ) ACEAFZCGZFBACHMBLBCABDIJIK $.
  $}

  ${
    nfal.1 $e |- F/ x ph $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` A. y ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfal $p |- F/ x A. y ph $=
      ( wal nfri hbal nfi ) ACEBABCABDFGH $.

    $( If ` x ` is not free in ` ph ` , it is not free in ` E. y ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.)  (Proof shortened by Wolf
       Lammen, 30-Dec-2017.) $)
    nfex $p |- F/ x E. y ph $=
      ( wex nfri hbex nfi ) ACEBABCABDFGH $.

    $( If ` x ` is not free in ` ph ` , it is not free in ` F/ y ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.)  (Proof shortened by Wolf
       Lammen, 30-Dec-2017.) $)
    nfnf $p |- F/ x F/ y ph $=
      ( wnf wal wi df-nf nfal nfim nfxfr ) ACEAACFZGZCFBACHMBCALBDABCDIJIK $.
  $}

  $( Theorem 19.12 of [Margaris] p. 89.  Assuming the converse is a mistake
     sometimes made by beginners!  But sometimes the converse does hold, as in
     ~ 19.12vv and ~ r19.12sn .  (Contributed by NM, 12-Mar-1993.)  (Proof
     shortened by Wolf Lammen, 3-Jan-2018.) $)
  19.12 $p |- ( E. x A. y ph -> A. y E. x ph ) $=
    ( wal wex nfa1 nfex sp eximi alrimi ) ACDZBEABECKCBACFGKABACHIJ $.

  ${
    nfald.1 $e |- F/ y ph $.
    nfald.2 $e |- ( ph -> F/ x ps ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` A. y ph ` .
       (Contributed by Mario Carneiro, 24-Sep-2016.)  (Proof shortened by Wolf
       Lammen, 6-Jan-2018.) $)
    nfald $p |- ( ph -> F/ x A. y ps ) $=
      ( wnf wal alrimi nfnf1 nfal hba1 sp nfrd hbald nfd syl ) ABCGZDHZBDHZCGAR
      DEFISTCRCDBCJKSBCDRDLSBCRDMNOPQ $.

    $( If ` x ` is not free in ` ph ` , it is not free in ` E. y ph ` .
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    nfexd $p |- ( ph -> F/ x E. y ps ) $=
      ( wex wn wal df-ex nfnd nfald nfxfrd ) BDGBHZDIZHACBDJAOCANCDEABCFKLKM $.
  $}

  $( Lemma 24 of [Monk2] p. 114.  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)
  nfa2 $p |- F/ x A. y A. x ph $=
    ( wal nfa1 nfal ) ABDBCABEF $.

  $( Lemma 23 of [Monk2] p. 114.  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)
  nfia1 $p |- F/ x ( A. x ph -> A. x ps ) $=
    ( wal nfa1 nfim ) ACDBCDCACEBCEF $.

  ${
    $d x z $.  $d y z $.
    dvelimhw.1 $e |- ( ph -> A. x ph ) $.
    dvelimhw.2 $e |- ( ps -> A. z ps ) $.
    dvelimhw.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $(  dvelimhw.4 $e |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $. $)
    dvelimhw.4 $e |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $.
    $( Proof of ~ dvelimh without using ~ ax-13 but with additional distinct
       variable conditions.  (Contributed by Andrew Salmon, 21-Jul-2011.)
       (Revised by NM, 1-Aug-2017.)  (Proof shortened by Wolf Lammen,
       23-Dec-2018.) $)
    dvelimhw $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( weq wal wn wi wnf nfv equcom nfna1 nfd nfxfrd nfi a1i nfimd nfald nfbii
      equsalhw sylib nfrd ) CDJZCKLZBCUIEDJZAMZEKZCNBCNUIUKCEUIEOUIUJACUJDEJZUI
      CEDPUIUMCUHCQIRSACNUIACFTUAUBUCULBCABEDGHUEUDUFUG $.
  $}

  ${
    $d x y $.
    cbv3hv.1 $e |- ( ph -> A. y ph ) $.
    cbv3hv.2 $e |- ( ps -> A. x ps ) $.
    cbv3hv.3 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Lemma for ~ axc11n .  Similar to ~ cbv3h .  Requires distinct variables
       but avoids ~ ax-13 .  (Contributed by NM, 25-Jul-2015.)  (Proof
       shortened by Wolf Lammen, 29-Dec-2017.) $)
    cbv3hv $p |- ( A. x ph -> A. y ps ) $=
      ( wal alimi wex weq wi ax6ev eximii 19.35i 19.9h sylib alcoms syl ) ACHZA
      DHZCHBDHZAUACEIAUBDCTBDTBCJBABCCDKABLCCDMGNOBCFPQIRS $.
  $}

  ${
    19.16.1 $e |- F/ x ph $.
    $( Theorem 19.16 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
    19.16 $p |- ( A. x ( ph <-> ps ) -> ( ph <-> A. x ps ) ) $=
      ( wal wb 19.3 albi syl5bbr ) AACEABFCEBCEACDGABCHI $.
  $}

  ${
    19.17.1 $e |- F/ x ps $.
    $( Theorem 19.17 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
    19.17 $p |- ( A. x ( ph <-> ps ) -> ( A. x ph <-> ps ) ) $=
      ( wb wal albi 19.3 syl6bb ) ABECFACFBCFBABCGBCDHI $.
  $}

  ${
    19.19.1 $e |- F/ x ph $.
    $( Theorem 19.19 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
    19.19 $p |- ( A. x ( ph <-> ps ) -> ( ph <-> E. x ps ) ) $=
      ( wex wb wal 19.9 exbi syl5bbr ) AACEABFCGBCEACDHABCIJ $.
  $}

  $( An alternative definition of ~ df-nf , which does not involve nested
     quantifiers on the same variable.  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)
  nf2 $p |- ( F/ x ph <-> ( E. x ph -> A. x ph ) ) $=
    ( wnf wal wi wex df-nf nfa1 19.23 bitri ) ABCAABDZEBDABFKEABGAKBABHIJ $.

  $( An alternative definition of ~ df-nf .  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)
  nf3 $p |- ( F/ x ph <-> A. x ( E. x ph -> ph ) ) $=
    ( wnf wex wal wi nf2 nfe1 19.21 bitr4i ) ABCABDZABEFKAFBEABGKABABHIJ $.

  $( Variable ` x ` is effectively not free in ` ph ` iff ` ph ` is always true
     or always false.  (Contributed by Mario Carneiro, 24-Sep-2016.) $)
  nf4 $p |- ( F/ x ph <-> ( A. x ph \/ A. x -. ph ) ) $=
    ( wnf wex wal wi wn wo nf2 imor orcom alnex orbi2i bitr4i 3bitri ) ABCABDZA
    BEZFPGZQHZQAGBEZHZABIPQJSQRHUARQKTRQABLMNO $.

  ${
    nfdiOLD.1 $e |- ( ph -> F/ x ph ) $.
    $( Obsolete proof of ~ nfdi as of 10-Jul-2019.  (Contributed by NM,
       17-Aug-2018.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nfdiOLD $p |- F/ x ph $=
      ( wex wal 19.8a wnf wi nf2 sylib mpd nfi ) ABAABDZABEZABFAABGMNHCABIJKL
      $.
  $}

  ${
    19.36.1 $e |- F/ x ps $.
    $( Theorem 19.36 of [Margaris] p. 90.  See ~ 19.36v for a version requiring
       fewer axioms.  (Contributed by NM, 24-Jun-1993.) $)
    19.36 $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> ps ) ) $=
      ( wi wex wal 19.35 19.9 imbi2i bitri ) ABECFACGZBCFZELBEABCHMBLBCDIJK $.

    19.36i.2 $e |- E. x ( ph -> ps ) $.
    $( Inference associated with ~ 19.36 .  See ~ 19.36aiv for a version
       requiring fewer axioms.  (Contributed by NM, 24-Jun-1993.) $)
    19.36i $p |- ( A. x ph -> ps ) $=
      ( wi wex wal 19.36 mpbi ) ABFCGACHBFEABCDIJ $.
  $}

  ${
    19.37.1 $e |- F/ x ph $.
    $( Theorem 19.37 of [Margaris] p. 90.  See ~ 19.37v for a version requiring
       fewer axioms.  (Contributed by NM, 21-Jun-1993.) $)
    19.37 $p |- ( E. x ( ph -> ps ) <-> ( ph -> E. x ps ) ) $=
      ( wi wex wal 19.35 19.3 imbi1i bitri ) ABECFACGZBCFZEAMEABCHLAMACDIJK $.
  $}

  ${
    19.32.1 $e |- F/ x ph $.
    $( Theorem 19.32 of [Margaris] p. 90.  See ~ 19.32v for a version requiring
       fewer axioms.  (Contributed by NM, 14-May-1993.)  (Revised by Mario
       Carneiro, 24-Sep-2016.) $)
    19.32 $p |- ( A. x ( ph \/ ps ) <-> ( ph \/ A. x ps ) ) $=
      ( wn wi wal wo nfn 19.21 df-or albii 3bitr4i ) AEZBFZCGNBCGZFABHZCGAPHNBC
      ACDIJQOCABKLAPKM $.
  $}

  ${
    19.31.1 $e |- F/ x ps $.
    $( Theorem 19.31 of [Margaris] p. 90.  See ~ 19.31v for a version requiring
       fewer axioms.  (Contributed by NM, 14-May-1993.) $)
    19.31 $p |- ( A. x ( ph \/ ps ) <-> ( A. x ph \/ ps ) ) $=
      ( wo wal 19.32 orcom albii 3bitr4i ) BAEZCFBACFZEABEZCFLBEBACDGMKCABHILBH
      J $.
  $}

  ${
    19.44.1 $e |- F/ x ps $.
    $( Theorem 19.44 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
    19.44 $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ ps ) ) $=
      ( wo wex 19.43 19.9 orbi2i bitri ) ABECFACFZBCFZEKBEABCGLBKBCDHIJ $.
  $}

  ${
    19.45.1 $e |- F/ x ph $.
    $( Theorem 19.45 of [Margaris] p. 90.  (Contributed by NM, 12-Mar-1993.) $)
    19.45 $p |- ( E. x ( ph \/ ps ) <-> ( ph \/ E. x ps ) ) $=
      ( wo wex 19.43 19.9 orbi1i bitri ) ABECFACFZBCFZEALEABCGKALACDHIJ $.
  $}

  ${
    19.41.1 $e |- F/ x ps $.
    $( Theorem 19.41 of [Margaris] p. 90.  See ~ 19.41v for a version requiring
       fewer axioms.  (Contributed by NM, 14-May-1993.)  (Proof shortened by
       Andrew Salmon, 25-May-2011.)  (Proof shortened by Wolf Lammen,
       12-Jan-2018.) $)
    19.41 $p |- ( E. x ( ph /\ ps ) <-> ( E. x ph /\ ps ) ) $=
      ( wa wex 19.40 19.9 anbi2i sylib pm3.21 eximd impcom impbii ) ABEZCFZACFZ
      BEZPQBCFZERABCGSBQBCDHIJBQPBAOCDBAKLMN $.
  $}

  ${
    19.42.1 $e |- F/ x ph $.
    $( Theorem 19.42 of [Margaris] p. 90.  See ~ 19.42v for a version requiring
       fewer axioms.  (Contributed by NM, 18-Aug-1993.) $)
    19.42 $p |- ( E. x ( ph /\ ps ) <-> ( ph /\ E. x ps ) ) $=
      ( wa wex 19.41 exancom ancom 3bitr4i ) BAECFBCFZAEABECFAKEBACDGABCHAKIJ
      $.
  $}

  ${
    exan.1 $e |- ( E. x ph /\ ps ) $.
    $( Place a conjunct in the scope of an existential quantifier.
       (Contributed by NM, 18-Aug-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.)  (Proof shortened by Wolf Lammen, 13-Jan-2018.) $)
    exan $p |- E. x ( ph /\ ps ) $=
      ( wa wex simpri nfth 19.41 mpbir ) ABECFACFZBEDABCBCKBDGHIJ $.
  $}

  ${
    hbnd.1 $e |- ( ph -> A. x ph ) $.
    hbnd.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbn .
       (Contributed by NM, 3-Jan-2002.) $)
    hbnd $p |- ( ph -> ( -. ps -> A. x -. ps ) ) $=
      ( wal wi wn alrimih hbnt syl ) ABBCFGZCFBHZMCFGALCDEIBCJK $.
  $}

  ${
    aaan.1 $e |- F/ y ph $.
    aaan.2 $e |- F/ x ps $.
    $( Rearrange universal quantifiers.  (Contributed by NM, 12-Aug-1993.) $)
    aaan $p |- ( A. x A. y ( ph /\ ps ) <-> ( A. x ph /\ A. y ps ) ) $=
      ( wa wal 19.28 albii nfal 19.27 bitri ) ABGDHZCHABDHZGZCHACHOGNPCABDEIJAO
      CBCDFKLM $.
  $}

  ${
    eeor.1 $e |- F/ y ph $.
    eeor.2 $e |- F/ x ps $.
    $( Rearrange existential quantifiers.  (Contributed by NM, 8-Aug-1994.) $)
    eeor $p |- ( E. x E. y ( ph \/ ps ) <-> ( E. x ph \/ E. y ps ) ) $=
      ( wo wex 19.45 exbii nfex 19.44 bitri ) ABGDHZCHABDHZGZCHACHOGNPCABDEIJAO
      CBCDFKLM $.
  $}

  $( Quantified ""excluded middle.""  Exercise 9.2a of Boolos, p. 111,
     _Computability and Logic_.  (Contributed by NM, 10-Dec-2000.) $)
  qexmid $p |- E. x ( ph -> A. x ph ) $=
    ( wal 19.8a 19.35ri ) AABCZBFBDE $.

  $( A property related to substitution that unlike ~ equs5 doesn't require a
     distinctor antecedent.  (Contributed by NM, 2-Feb-2007.) $)
  equs5a $p |- ( E. x ( x = y /\ A. y ph ) -> A. x ( x = y -> ph ) ) $=
    ( weq wal wa wi nfa1 ax-12 imp exlimi ) BCDZACEZFLAGZBEZBNBHLMOABCIJK $.

  $( A property related to substitution that unlike ~ equs5 doesn't require a
     distinctor antecedent.  (Contributed by NM, 2-Feb-2007.)  (Proof shortened
     by Wolf Lammen, 15-Jan-2018.) $)
  equs5e $p |- ( E. x ( x = y /\ ph ) -> A. x ( x = y -> E. y ph ) ) $=
    ( weq wa wex wi wal nfa1 hbe1 19.23bi ax-12 syl5 imp exlimi ) BCDZAEPACFZGZ
    BHZBRBIPASAQCHZPSATCACJKQBCLMNO $.

  ${
    exlimdd.1 $e |- F/ x ph $.
    exlimdd.2 $e |- F/ x ch $.
    exlimdd.3 $e |- ( ph -> E. x ps ) $.
    exlimdd.4 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Existential elimination rule of natural deduction.  (Contributed by
       Mario Carneiro, 9-Feb-2017.) $)
    exlimdd $p |- ( ph -> ch ) $=
      ( wex ex exlimd mpd ) ABDICGABCDEFABCHJKL $.
  $}

  ${
    $d x ph $.
    $( Obsolete proof of ~ 19.21v as of 2-Jan-2020.  (Contributed by NM,
       21-Jun-1993.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    19.21vOLD $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $=
      ( nfv 19.21 ) ABCACDE $.
  $}

  ${
    $d x ps $.
    $( Obsolete proof of ~ 19.23v as of 11-Jan-2020.  (Contributed by NM,
       28-Jun-1998.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    19.23vOLD $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $=
      ( nfv 19.23 ) ABCBCDE $.
  $}

  ${
    $d ph y $.  $d ps x $.
    $( Theorem *11.53 in [WhiteheadRussell] p. 164.  See ~ pm11.53v for a
       version requiring fewer axioms.  (Contributed by Andrew Salmon,
       24-May-2011.) $)
    pm11.53 $p |- ( A. x A. y ( ph -> ps ) <-> ( E. x ph -> A. y ps ) ) $=
      ( wi wal wex 19.21v albii nfv nfal 19.23 bitri ) ABEDFZCFABDFZEZCFACGOENP
      CABDHIAOCBCDBCJKLM $.
  $}

  ${
    $d x ps $.
    $( Obsolete proof of ~ 19.36v as of 17-Jan-2020.  (Contributed by NM,
       18-Aug-1993.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    19.36vOLD $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> ps ) ) $=
      ( nfv 19.36 ) ABCBCDE $.
  $}

  ${
    $d x ps $.
    19.36aivOLD.1 $e |- E. x ( ph -> ps ) $.
    $( Obsolete proof of ~ 19.36aiv as of 17-Jan-2020.  (Contributed by NM,
       5-Aug-1993.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    19.36aivOLD $p |- ( A. x ph -> ps ) $=
      ( nfv 19.36i ) ABCBCEDF $.
  $}

  ${
    $d x ps $.  $d y ph $.
    $( Special case of ~ 19.12 where its converse holds.  See ~ 19.12vvv for a
       version with a dv condition requiring fewer axioms.  (Contributed by NM,
       18-Jul-2001.)  (Revised by Andrew Salmon, 11-Jul-2011.) $)
    19.12vv $p |- ( E. x A. y ( ph -> ps ) <-> A. y E. x ( ph -> ps ) ) $=
      ( wi wal wex 19.21v exbii nfv nfal 19.36 19.36v albii 19.21 bitr2i 3bitri
      ) ABEZDFZCGABDFZEZCGACFZTEZRCGZDFZSUACABDHIATCBCDBCJKLUEUBBEZDFUCUDUFDABC
      MNUBBDADCADJKOPQ $.
  $}

  ${
    eean.1 $e |- F/ y ph $.
    eean.2 $e |- F/ x ps $.
    $( Rearrange existential quantifiers.  (Contributed by NM, 27-Oct-2010.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
    eean $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x ph /\ E. y ps ) ) $=
      ( wa wex 19.42 exbii nfex 19.41 bitri ) ABGDHZCHABDHZGZCHACHOGNPCABDEIJAO
      CBCDFKLM $.
  $}

  ${
    $d y ph $.  $d x ps $.
    $( Rearrange existential quantifiers.  (Contributed by NM, 26-Jul-1995.) $)
    eeanv $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x ph /\ E. y ps ) ) $=
      ( nfv eean ) ABCDADEBCEF $.
  $}

  ${
    $d y ph $.  $d z ph $.  $d x ps $.  $d z ps $.  $d x ch $.  $d y ch $.
    $( Rearrange existential quantifiers.  (Contributed by NM, 26-Jul-1995.)
       (Proof shortened by Andrew Salmon, 25-May-2011.)  Reduce distinct
       variable restrictions.  (Revised by Wolf Lammen, 20-Jan-2018.) $)
    eeeanv $p |- ( E. x E. y E. z ( ph /\ ps /\ ch ) <->
                 ( E. x ph /\ E. y ps /\ E. z ch ) ) $=
      ( wa wex w3a eeanv anbi1i df-3an exbii 19.42v bitri 2exbii nfv nfex 19.41
      3bitri 3bitr4i ) ABGZEHZDHZCFHZGZADHZBEHZGZUEGABCIZFHZEHDHZUGUHUEIUDUIUEA
      BDEJKULUBUEGZEHZDHUCUEGZDHUFUKUMDEUKUBCGZFHUMUJUPFABCLMUBCFNOPUNUODUBUEEC
      EFCEQRSMUCUEDCDFCDQRSTUGUHUELUA $.
  $}

  ${
    $d z ph $.  $d w ph $.  $d x ps $.  $d y ps $.  $d y z $.  $d w x $.
    $( Rearrange existential quantifiers.  (Contributed by NM, 31-Jul-1995.) $)
    ee4anv $p |- ( E. x E. y E. z E. w ( ph /\ ps ) <->
                  ( E. x E. y ph /\ E. z E. w ps ) ) $=
      ( wa wex excom exbii eeanv 2exbii 3bitri ) ABGFHZEHDHZCHNDHZEHZCHADHZBFHZ
      GZEHCHRCHSEHGOQCNDEIJPTCEABDFKLRSCEKM $.
  $}

  $( An equality theorem for substitution.  (Contributed by NM,
     16-May-1993.) $)
  sbequ1 $p |- ( x = y -> ( ph -> [ y / x ] ph ) ) $=
    ( weq wsb wa wi wex pm3.4 19.8a df-sb sylanbrc ex ) BCDZAABCEZNAFZNAGPBHONA
    IPBJABCKLM $.

  $( An equality theorem for substitution.  (Contributed by NM,
     14-May-1993.) $)
  sbequ12 $p |- ( x = y -> ( ph <-> [ y / x ] ph ) ) $=
    ( weq wsb sbequ1 sbequ2 impbid ) BCDAABCEABCFABCGH $.

  $( An equality theorem for substitution.  (Contributed by NM, 6-Oct-2004.)
     (Proof shortened by Andrew Salmon, 21-Jun-2011.) $)
  sbequ12r $p |- ( x = y -> ( [ x / y ] ph <-> ph ) ) $=
    ( wsb wb weq sbequ12 bicomd equcoms ) ACBDZAECBCBFAJACBGHI $.

  $( An equality theorem for substitution.  (Contributed by NM, 2-Jun-1993.)
     (Proof shortened by Wolf Lammen, 23-Jun-2019.) $)
  sbequ12a $p |- ( x = y -> ( [ y / x ] ph <-> [ x / y ] ph ) ) $=
    ( weq wsb sbequ12r sbequ12 bitr2d ) BCDACBEAABCEABCFABCGH $.

  $( Obsolete proof of ~ sbequ12a as of 23-Jun-2019.  (Contributed by NM,
     5-Aug-1993.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  sbequ12aOLD $p |- ( x = y -> ( [ y / x ] ph <-> [ x / y ] ph ) ) $=
    ( weq wsb sbequ12 wb equcoms bitr3d ) BCDAABCEACBEZABCFAJGCBACBFHI $.

  $( An identity theorem for substitution.  Remark 9.1 in [Megill] p. 447 (p.
     15 of the preprint).  (Contributed by NM, 26-May-1993.)  (Proof shortened
     by Wolf Lammen, 30-Sep-2018.) $)
  sbid $p |- ( [ x / x ] ph <-> ph ) $=
    ( weq wsb wb equid sbequ12r ax-mp ) BBCABBDAEBFABBGH $.

  $( A version of ~ sb4 that doesn't require a distinctor antecedent.
     (Contributed by NM, 2-Feb-2007.) $)
  sb4a $p |- ( [ y / x ] A. y ph -> A. x ( x = y -> ph ) ) $=
    ( wal wsb weq wa wex wi sb1 equs5a syl ) ACDZBCEBCFZMGBHNAIBDMBCJABCKL $.

  $( One direction of a simplified definition of substitution that unlike ~ sb4
     doesn't require a distinctor antecedent.  (Contributed by NM,
     2-Feb-2007.) $)
  sb4e $p |- ( [ y / x ] ph -> A. x ( x = y -> E. y ph ) ) $=
    ( wsb weq wa wex wi wal sb1 equs5e syl ) ABCDBCEZAFBGMACGHBIABCJABCKL $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Axiom scheme ax-13 (Quantified Equality)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Quantified Equality.  One of the equality and substitution axioms
     of predicate calculus with equality.

     An equivalent way to express this axiom that may be easier to understand
     is ` ( -. x = y -> ( -. x = z -> ( y = z -> A. x y = z ) ) ) ` (see
     ~ ax13b ).  Recall that in the intended interpretation, our variables are
     metavariables ranging over the variables of predicate calculus (the object
     language).  In order for the first antecedent ` -. x = y ` to hold, ` x `
     and ` y ` must have different values and thus cannot be the same
     object-language variable (so they are effectively ""distinct variables""
     even though no $d is present).  Similarly, ` x ` and ` z ` cannot be the
     same object-language variable.  Therefore, ` x ` will not occur in the wff
     ` y = z ` when the first two antecedents hold, so analogous to ~ ax-5 ,
     the conclusion ` ( y = z -> A. x y = z ) ` follows.  Note that ~ ax-5
     cannot prove this directly because it requires $d statements.

     The original version of this axiom was ~ ax-c9 and was replaced with this
     shorter ~ ax-13 in December 2015.  The old axiom is proved from this one
     as theorem ~ axc9 .  Conversely, this axiom is proved from ~ ax-c9 as
     theorem ~ ax13 .

     The primary purpose of this axiom is to provide a way to introduce the
     quantifier ` A. x ` on ` y = z ` even when ` x ` and ` y ` are substituted
     with the same variable.  In this case, the first antecedent becomes
     ` -. x = x ` and the axiom still holds.

     Although this version is shorter, the original version ~ axc9 may be more
     practical to work with because of the ""distinctor"" form of its
     antecedents.  A typical application of ~ axc9 is in ~ dvelimh which
     converts a distinct variable pair to the distinctor antecedent
     ` -. A. x x = y ` .  In particular, it is conjectured that it is not
     possible to prove ~ ax6 from ~ ax6v without this axiom.

     This axiom can be weakened if desired by adding distinct variable
     restrictions on pairs ` x , z ` and ` y , z ` .  To show that, we add
     these restrictions to theorem ~ ax13v and use only ~ ax13v for further
     derivations.  Thus, ~ ax13v should be the only theorem referencing this
     axiom.  Other theorems can reference either ~ ax13v (preferred) or
     ~ ax13 .

     This axiom scheme is logically redundant (see ~ ax13w ) but is used as an
     auxiliary axiom to achieve metalogical completeness (i.e. so that all
     possible cases of bundling can be proved; see text linked at
     ~ mmtheorems.html#wal ).  It is not known whether this axiom can be
     derived from the others.  (Contributed by NM, 21-Dec-2015.)
     (New usage is discouraged.) $)
  ax-13 $a |- ( -. x = y -> ( y = z -> A. x y = z ) ) $.

  ${
    $d x z $.  $d y z $.
    $( A weaker version of ~ ax-13 with distinct variable restrictions on pairs
       ` x , z ` and ` y , z ` .  In order to show that this weakening is
       adequate, this should be the only theorem referencing ~ ax-13 directly.
       (Contributed by NM, 30-Jun-2016.) $)
    ax13v $p |- ( -. x = y -> ( y = z -> A. x y = z ) ) $=
      ( ax-13 ) ABCD $.
  $}

  ${
    $d x z w $.  $d y w $.
    $( A version of ~ ax13v with one distinct variable restriction dropped.
       For convenience, ` y ` is kept on the right side of equations.  The
       proof of ~ ax13 bases on ideas from NM, 24-Dec-2015.  (Contributed by
       Wolf Lammen, 8-Sep-2018.)  (New usage is discouraged.) $)
    axc9lem1 $p |- ( -. x = y -> ( z = y -> A. x z = y ) ) $=
      ( vw weq wa wex wn wal equviniv equequ2 biimprcd alimdv syl9 impd exlimdv
      ax13v syl5 ) CBEZCDEZBDEZFZDGABEHZSAIZCBDJUCUBUDDUCTUAUDUCUAUAAITUDABDQTU
      ASAUASTBDCKLMNOPR $.
  $}

  ${
    $d y w $.  $d x w $.
    $( At least one individual exists.  This is not a theorem of free logic,
       which is sound in empty domains.  For such a logic, we would add this
       theorem as an axiom of set theory (Axiom 0 of [Kunen] p. 10).  In the
       system consisting of ~ ax-4 through ~ ax-9 , all axioms other than
       ~ ax-6 are believed to be theorems of free logic, although the system
       without ~ ax-6 is not complete in free logic.

       It is preferred to use ~ ax6ev when it is sufficient.  (Contributed by
       NM, 14-May-1993.)  Shortened after ~ axc9lem1 became available.
       (Revised by Wolf Lammen, 8-Sep-2018.) $)
    ax6e $p |- E. x x = y $=
      ( vw weq wex 19.8a wn wi ax6ev wal axc9lem1 eximii 19.35i syl6com exlimiv
      equtr ax-mp pm2.61i ) ABDZSAEZSAFCBDZCESGZTHZCBIUAUCCUBUAUAAJTABCKUASAACD
      UASHAACIACBPLMNOQR $.
  $}

  $( Theorem showing that ~ ax-6 follows from the weaker version ~ ax6v .
     (Even though this theorem depends on ~ ax-6 , all references of ~ ax-6 are
     made via ~ ax6v .  An earlier version stated ~ ax6v as a separate axiom,
     but having two axioms caused some confusion.)

     This theorem should be referenced in place of ~ ax-6 so that all proofs
     can be traced back to ~ ax6v .  (Contributed by NM, 12-Nov-2013.)
     (Revised by NM, 25-Jul-2015.)  (Proof shortened by Wolf Lammen,
     4-Feb-2018.) $)
  ax6 $p |- -. A. x -. x = y $=
    ( weq wex wn wal ax6e df-ex mpbi ) ABCZADJEAFEABGJAHI $.

  $( Show that the original axiom ~ ax-c10 can be derived from ~ ax6 and
     others.  See ~ ax6fromc10 for the rederivation of ~ ax6 from ~ ax-c10 .

     Normally, ~ axc10 should be used rather than ~ ax-c10 , except by theorems
     specifically studying the latter's properties.  (Contributed by NM,
     5-Aug-1993.)  (Proof modification is discouraged.) $)
  axc10 $p |- ( A. x ( x = y -> A. x ph ) -> ph ) $=
    ( weq wal wi wn ax6 con3 al2imi mtoi axc7 syl ) BCDZABEZFZBEZOGZBEZGAQSNGZB
    EBCHPRTBNOIJKABLM $.

  $( Closed theorem form of ~ spim .  (Contributed by NM, 15-Jan-2008.)
     (Revised by Mario Carneiro, 17-Oct-2016.)  (Proof shortened by Wolf
     Lammen, 24-Feb-2018.) $)
  spimt $p |- ( ( F/ x ps /\ A. x ( x = y -> ( ph -> ps ) ) ) ->
                                                         ( A. x ph -> ps ) ) $=
    ( weq wi wal wex wnf ax6e exim mpi 19.35 sylib 19.9t biimpd sylan9r ) CDEZA
    BFZFCGZACGZBCHZBCIZBTSCHZUAUBFTRCHUDCDJRSCKLABCMNUCUBBBCOPQ $.

  ${
    spim.1 $e |- F/ x ps $.
    spim.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Specialization, using implicit substitution.  Compare Lemma 14 of
       [Tarski] p. 70.  The ~ spim series of theorems requires that only one
       direction of the substitution hypothesis hold.  (Contributed by NM,
       10-Jan-1993.)  (Revised by Mario Carneiro, 3-Oct-2016.)  (Proof
       shortened by Wolf Lammen, 18-Feb-2018.) $)
    spim $p |- ( A. x ph -> ps ) $=
      ( weq wi ax6e eximii 19.36i ) ABCECDGABHCCDIFJK $.
  $}

  ${
    spimed.1 $e |- ( ch -> F/ x ph ) $.
    spimed.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Deduction version of ~ spime .  (Contributed by NM, 14-May-1993.)
       (Revised by Mario Carneiro, 3-Oct-2016.)  (Proof shortened by Wolf
       Lammen, 19-Feb-2018.) $)
    spimed $p |- ( ch -> ( ph -> E. x ps ) ) $=
      ( wal wex nfrd weq wi ax6e eximii 19.35i syl6 ) CAADHBDICADFJABDDEKABLDDE
      MGNOP $.
  $}

  ${
    spime.1 $e |- F/ x ph $.
    spime.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Existential introduction, using implicit substitution.  Compare Lemma 14
       of [Tarski] p. 70.  (Contributed by NM, 7-Aug-1994.)  (Revised by Mario
       Carneiro, 3-Oct-2016.)  (Proof shortened by Wolf Lammen, 6-Mar-2018.) $)
    spime $p |- ( ph -> E. x ps ) $=
      ( wex wi wtru wnf a1i spimed trud ) ABCGHABICDACJIEKFLM $.
  $}

  ${
    $d x ps $.
    spimv.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( A version of ~ spim with a distinct variable requirement instead of a
       bound variable hypothesis.  (Contributed by NM, 31-Jul-1993.) $)
    spimv $p |- ( A. x ph -> ps ) $=
      ( nfv spim ) ABCDBCFEG $.
  $}

  ${
    $d x ph $.
    spimev.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Distinct-variable version of ~ spime .  (Contributed by NM,
       10-Jan-1993.) $)
    spimev $p |- ( ph -> E. x ps ) $=
      ( nfv spime ) ABCDACFEG $.
  $}

  ${
    $d x ps $.
    spv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Specialization, using implicit substitution.  (Contributed by NM,
       30-Aug-1993.) $)
    spv $p |- ( A. x ph -> ps ) $=
      ( weq biimpd spimv ) ABCDCDFABEGH $.
  $}

  ${
    spei.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    spei.2 $e |- ps $.
    $( Inference from existential specialization, using implicit substitution.
       Remove a distinct variable constraint.  (Contributed by NM,
       19-Aug-1993.)  (Proof shortened by Wolf Lammen, 12-May-2018.) $)
    spei $p |- E. x ph $=
      ( weq ax6e mpbiri eximii ) CDGZACCDHKABFEIJ $.
  $}

  ${
    chvar.1 $e |- F/ x ps $.
    chvar.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    chvar.3 $e |- ph $.
    $( Implicit substitution of ` y ` for ` x ` into a theorem.  (Contributed
       by Raph Levien, 9-Jul-2003.)  (Revised by Mario Carneiro,
       3-Oct-2016.) $)
    chvar $p |- ps $=
      ( weq biimpd spim mpg ) ABCABCDECDHABFIJGK $.
  $}

  ${
    $d x ps $.
    chvarv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    chvarv.2 $e |- ph $.
    $( Implicit substitution of ` y ` for ` x ` into a theorem.  (Contributed
       by NM, 20-Apr-1994.)  (Proof shortened by Wolf Lammen, 22-Apr-2018.) $)
    chvarv $p |- ps $=
      ( nfv chvar ) ABCDBCGEFH $.
  $}

  ${
    cbv3.1 $e |- F/ y ph $.
    cbv3.2 $e |- F/ x ps $.
    cbv3.3 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution, that
       does not use ~ ax-c9 .  (Contributed by NM, 5-Aug-1993.)  (Proof
       shortened by Wolf Lammen, 12-May-2018.) $)
    cbv3 $p |- ( A. x ph -> A. y ps ) $=
      ( wal nfal spim alrimi ) ACHBDADCEIABCDFGJK $.
  $}

  ${
    cbv3h.1 $e |- ( ph -> A. y ph ) $.
    cbv3h.2 $e |- ( ps -> A. x ps ) $.
    cbv3h.3 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 8-Jun-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.)  (Proof shortened by Wolf Lammen, 12-May-2018.) $)
    cbv3h $p |- ( A. x ph -> A. y ps ) $=
      ( nfi cbv3 ) ABCDADEHBCFHGI $.
  $}

  ${
    cbv1.1 $e |- F/ x ph $.
    cbv1.2 $e |- F/ y ph $.
    cbv1.3 $e |- ( ph -> F/ y ps ) $.
    cbv1.4 $e |- ( ph -> F/ x ch ) $.
    cbv1.5 $e |- ( ph -> ( x = y -> ( ps -> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       3-Oct-2016.)  Format hypotheses to common style.  (Revised by Wolf
       Lammen, 13-May-2018.) $)
    cbv1 $p |- ( ph -> ( A. x ps -> A. y ch ) ) $=
      ( wal wi nfim1 weq com12 a2d cbv3 19.21 3imtr3i pm2.86i ) ABDKZCEKZABLZDK
      ACLZEKAUALAUBLUCUDDEABEGHMACDFIMDENZABCAUEBCLJOPQABDFRACEGRST $.
  $}

  ${
    cbv1h.1 $e |- ( ph -> ( ps -> A. y ps ) ) $.
    cbv1h.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    cbv1h.3 $e |- ( ph -> ( x = y -> ( ps -> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 11-May-1993.)  (Proof shortened by Wolf Lammen,
       13-May-2018.) $)
    cbv1h $p |- ( A. x A. y ph -> ( A. x ps -> A. y ch ) ) $=
      ( wal nfa1 nfa2 wi 2sp syl nfd weq cbv1 ) AEIZDIZBCDERDJZAEDKZSBEUASABBEI
      LADEMZFNOSCDTSACCDILUBGNOSADEPBCLLUBHNQ $.
  $}

  ${
    cbv2h.1 $e |- ( ph -> ( ps -> A. y ps ) ) $.
    cbv2h.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    cbv2h.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 11-May-1993.) $)
    cbv2h $p |- ( A. x A. y ph -> ( A. x ps <-> A. y ch ) ) $=
      ( wal weq wb wi bi1 syl6 cbv1h equcomi bi2 syl56 alcoms impbid ) AEIDIBDI
      ZCEIZABCDEFGADEJZBCKZBCLHBCMNOAUBUALEDACBEDGFEDJUCAUDCBLEDPHBCQROST $.
  $}

  ${
    cbv2.1 $e |- F/ x ph $.
    cbv2.2 $e |- F/ y ph $.
    cbv2.3 $e |- ( ph -> F/ y ps ) $.
    cbv2.4 $e |- ( ph -> F/ x ch ) $.
    cbv2.5 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       3-Oct-2016.)  Format hypotheses to common style.  (Revised by Wolf
       Lammen, 13-May-2018.) $)
    cbv2 $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      ( wal wb nfri alrimi nfrd cbv2h syl ) AAEKZDKBDKCEKLARDFAEGMNABCDEABEHOAC
      DIOJPQ $.
  $}

  ${
    cbval.1 $e |- F/ y ph $.
    cbval.2 $e |- F/ x ps $.
    cbval.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 13-May-1993.)  (Revised by Mario Carneiro,
       3-Oct-2016.) $)
    cbval $p |- ( A. x ph <-> A. y ps ) $=
      ( wal weq biimpd cbv3 wi biimprd equcoms impbii ) ACHBDHABCDEFCDIZABGJKBA
      DCFEBALCDPABGMNKO $.

    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 21-Jun-1993.) $)
    cbvex $p |- ( E. x ph <-> E. y ps ) $=
      ( wn wal wex nfn weq notbid cbval notbii df-ex 3bitr4i ) AHZCIZHBHZDIZHAC
      JBDJSUARTCDADEKBCFKCDLABGMNOACPBDPQ $.
  $}

  ${
    $d y ph $.  $d x ps $.
    cbvalv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.) $)
    cbvalv $p |- ( A. x ph <-> A. y ps ) $=
      ( nfv cbval ) ABCDADFBCFEG $.

    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 21-Jun-1993.) $)
    cbvexv $p |- ( E. x ph <-> E. y ps ) $=
      ( nfv cbvex ) ABCDADFBCFEG $.
  $}

  ${
    $d x ph $.  $d x ch $.
    cbvald.1 $e |- F/ y ph $.
    cbvald.2 $e |- ( ph -> F/ y ps ) $.
    cbvald.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Deduction used to change bound variables, using implicit substitution,
       particularly useful in conjunction with ~ dvelim .  (Contributed by NM,
       2-Jan-2002.)  (Revised by Mario Carneiro, 6-Oct-2016.)  (Revised by Wolf
       Lammen, 13-May-2018.) $)
    cbvald $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      ( nfv nfvd cbv2 ) ABCDEADIFGACDJHK $.

    $( Deduction used to change bound variables, using implicit substitution,
       particularly useful in conjunction with ~ dvelim .  (Contributed by NM,
       2-Jan-2002.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)
    cbvexd $p |- ( ph -> ( E. x ps <-> E. y ch ) ) $=
      ( wn wal wex nfnd weq wb notbi syl6ib cbvald notbid df-ex 3bitr4g ) ABIZD
      JZICIZEJZIBDKCEKAUBUDAUAUCDEFABEGLADEMBCNUAUCNHBCOPQRBDSCEST $.
  $}

  ${
    $d y x $.  $d y z $.  $d w x $.  $d w z $.
    cbval2.1 $e |- F/ z ph $.
    cbval2.2 $e |- F/ w ph $.
    cbval2.3 $e |- F/ x ps $.
    cbval2.4 $e |- F/ y ps $.
    cbval2.5 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 22-Dec-2003.)  (Revised by Mario Carneiro,
       6-Oct-2016.)  (Proof shortened by Wolf Lammen, 22-Apr-2018.) $)
    cbval2 $p |- ( A. x A. y ph <-> A. z A. w ps ) $=
      ( wal nfal weq wi nfv nfim wb cbval 19.21v pm5.74d 3bitr3i pm5.74ri
      expcom ) ADLZBFLZCEAEDGMBCFIMCENZUEUFUGAOZDLUGBOZFLUGUEOUGUFOUHUIDFUGAFUG
      FPHQUGBDUGDPJQDFNZUGABUGUJABRKUDUASUGADTUGBFTUBUCS $.

    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 14-Sep-2003.)  (Revised by Mario Carneiro,
       6-Oct-2016.)  (Proof shortened by Wolf Lammen, 16-Jun-2019.) $)
    cbvex2 $p |- ( E. x E. y ph <-> E. z E. w ps ) $=
      ( wn wal wex nfn weq wa notbid cbval2 2exnaln notbii 3bitr4i ) ALZDMCMZLB
      LZFMEMZLADNCNBFNENUDUFUCUECDEFAEGOAFHOBCIOBDJOCEPDFPQABKRSUAACDTBEFTUB $.

    $( Obsolete proof of ~ cbvex2 as of 16-Jun-2019.  (Contributed by NM,
       14-Sep-2003.)  (Revised by Mario Carneiro, 6-Oct-2016.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    cbvex2OLD $p |- ( E. x E. y ph <-> E. z E. w ps ) $=
      ( wex nfex weq wb wa nfv nfan cbvex 19.42v wi expcom pm5.32d pm5.32 mpbir
      3bitr3i ) ADLZBFLZCEAEDGMBCFIMCENZUGUHOUAUIUGPZUIUHPZOUIAPZDLUIBPZFLUJUKU
      LUMDFUIAFUIFQHRUIBDUIDQJRDFNZUIABUIUNABOKUBUCSUIADTUIBFTUFUIUGUHUDUES $.
  $}

  ${
    $d z w ph $.  $d x y ps $.  $d x w $.  $d z y $.
    cbval2v.1 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 4-Feb-2005.) $)
    cbval2v $p |- ( A. x A. y ph <-> A. z A. w ps ) $=
      ( nfv cbval2 ) ABCDEFAEHAFHBCHBDHGI $.

    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 26-Jul-1995.) $)
    cbvex2v $p |- ( E. x E. y ph <-> E. z E. w ps ) $=
      ( nfv cbvex2 ) ABCDEFAEHAFHBCHBDHGI $.
  $}

  ${
    $d ps y $.  $d ch x $.  $d ph x $.  $d ph y $.
    cbvaldva.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Rule used to change the bound variable in a universal quantifier with
       implicit substitution.  Deduction form.  (Contributed by David Moews,
       1-May-2017.) $)
    cbvaldva $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      ( nfv nfvd weq wb ex cbvald ) ABCDEAEGABEHADEIBCJFKL $.

    $( Rule used to change the bound variable in an existential quantifier with
       implicit substitution.  Deduction form.  (Contributed by David Moews,
       1-May-2017.) $)
    cbvexdva $p |- ( ph -> ( E. x ps <-> E. y ch ) ) $=
      ( nfv nfvd weq wb ex cbvexd ) ABCDEAEGABEHADEIBCJFKL $.
  $}

  ${
    $v f $.
    $v g $.
    $( Define temporary individual variables. $)
    cbvex4v.vf $f setvar f $.
    cbvex4v.vg $f setvar g $.
    $d w z ch $.  $d u v ph $.  $d x y ps $.  $d f g ps $.  $d f w $.
    $d g z $.  $d u v w x y z $.
    cbvex4v.1 $e |- ( ( x = v /\ y = u ) -> ( ph <-> ps ) ) $.
    cbvex4v.2 $e |- ( ( z = f /\ w = g ) -> ( ps <-> ch ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 26-Jul-1995.) $)
    cbvex4v $p |- ( E. x E. y E. z E. w ph <-> E. v E. u E. f E. g ch ) $=
      ( wex weq wa 2exbidv cbvex2v 2exbii bitri ) AGNFNZENDNBGNFNZINHNCKNJNZINH
      NUAUBDEHIDHOEIOPABFGLQRUBUCHIBCFGJKMRST $.
  $}

  $( Lemma used in proofs of substitution properties.  The converse requires
     either a dv condition ( ~ sb56 ) or a non-freeness hypothesis
     ( ~ equs45f ).  See ~ equs4v for a version requiring fewer axioms.
     (Contributed by NM, 10-May-1993.)  (Proof shortened by Mario Carneiro,
     20-May-2014.)  (Proof shortened by Wolf Lammen, 5-Feb-2018.) $)
  equs4 $p |- ( A. x ( x = y -> ph ) -> E. x ( x = y /\ ph ) ) $=
    ( weq wi wal wex wa ax6e exintr mpi ) BCDZAEBFLBGLAHBGBCILABJK $.

  ${
    equsal.1 $e |- F/ x ps $.
    equsal.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( A useful equivalence related to substitution.  (Contributed by NM,
       2-Jun-1993.)  (Proof shortened by Andrew Salmon, 12-Aug-2011.)  (Revised
       by Mario Carneiro, 3-Oct-2016.)  (Proof shortened by Wolf Lammen,
       5-Feb-2018.) $)
    equsal $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      ( weq wi wal wex 19.23 pm5.74i albii ax6e a1bi 3bitr4i ) CDGZBHZCIQCJZBHQ
      AHZCIBQBCEKTRCQABFLMSBCDNOP $.
  $}

  ${
    equsalh.1 $e |- ( ps -> A. x ps ) $.
    equsalh.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( A useful equivalence related to substitution.  (Contributed by NM,
       2-Jun-1993.) $)
    equsalh $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      ( nfi equsal ) ABCDBCEGFH $.
  $}

  ${
    equsex.1 $e |- F/ x ps $.
    equsex.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( A useful equivalence related to substitution.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 3-Oct-2016.)  (Proof shortened
       by Wolf Lammen, 6-Feb-2018.) $)
    equsex $p |- ( E. x ( x = y /\ ph ) <-> ps ) $=
      ( weq wa wex biimpa exlimi wi wal equsal equs4 sylbir impbii ) CDGZAHZCIZ
      BSBCERABFJKBRALCMTABCDEFNACDOPQ $.
  $}

  ${
    equsexh.1 $e |- ( ps -> A. x ps ) $.
    equsexh.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( A useful equivalence related to substitution.  (Contributed by NM,
       5-Aug-1993.) $)
    equsexh $p |- ( E. x ( x = y /\ ph ) <-> ps ) $=
      ( nfi equsex ) ABCDBCEGFH $.
  $}

  ${
    $d w x z $.  $d w y $.
    $( Lemma for ~ nfeqf2 .  This lemma is equivalent to ~ ax13v with one
       distinct variable constraint removed.  (Contributed by Wolf Lammen,
       8-Sep-2018.)  (New usage is discouraged.) $)
    axc9lem2 $p |- ( -. x = y -> ( E. x z = y -> z = y ) ) $=
      ( vw weq wn wex wi wal axc9lem1 equequ2 biimprcd eximi sylib syl9 alrimdv
      19.36v nfv equsal syl6ib ) ABEFZCBEZAGZDBEZCDEZHZDIUBUAUCUFDUAUDUDAIZUCUE
      ABDJUCUFAGUGUEHUBUFAUDUEUBDBCKZLMUDUEAQNOPUEUBDBUBDRUHST $.
  $}

  ${
    $d x z $.
    $( An equation between setvar is free of any other setvar.  (Contributed by
       Wolf Lammen, 9-Jun-2019.) $)
    nfeqf2 $p |- ( -. A. x x = y -> F/ x z = y ) $=
      ( weq wal wn wex wnf exnal nfnf1 axc9lem2 axc9lem1 syld nf2 sylibr exlimi
      wi sylbir ) ABDZAEFSFZAGCBDZAHZSAITUBAUAAJTUAAGZUAAEZQUBTUCUAUDABCKABCLMU
      AANOPR $.
  $}

  ${
    $d x z $.
    $( Quantifier introduction when one pair of variables is distinct.
       (Contributed by NM, 2-Jan-2002.)  (Revised by NM, 20-Jul-2015.)  Remove
       dependency on ~ ax-11 .  (Revised by Wolf Lammen, 8-Sep-2018.) $)
    dveeq2 $p |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $=
      ( weq wal wn nfeqf2 nfrd ) ABDAEFCBDAABCGH $.
  $}

  ${
    $d x z $.
    $( An equation between setvar is free of any other setvar.  (Contributed by
       Wolf Lammen, 10-Jun-2019.) $)
    nfeqf1 $p |- ( -. A. x x = y -> F/ x y = z ) $=
      ( weq wal wn wnf nfeqf2 equcom nfbii sylib ) ABDAEFCBDZAGBCDZAGABCHLMACBI
      JK $.
  $}

  ${
    $d x z $.
    $( Quantifier introduction when one pair of variables is distinct.
       (Contributed by NM, 2-Jan-2002.)  Remove dependency on ~ ax-11 .
       (Revised by Wolf Lammen, 8-Sep-2018.) $)
    dveeq1 $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $=
      ( weq wal wn nfeqf1 nfrd ) ABDAEFBCDAABCGH $.
  $}

  ${
    $d x w $.  $d y w $.  $d z w $.
    $( A variable is effectively not free in an equality if it is not either of
       the involved variables. ` F/ ` version of ~ ax-c9 .  (Contributed by
       Mario Carneiro, 6-Oct-2016.)  Remove dependency on ~ ax-11 .  (Revised
       by Wolf Lammen, 6-Sep-2018.) $)
    nfeqf $p |- ( ( -. A. z z = x /\ -. A. z z = y ) -> F/ z x = y ) $=
      ( vw weq wal wn wa nfna1 nfan wex equviniv dveeq1 imp equtr2 alanimi an4s
      syl2an ex exlimdv syl5 nfd ) CAEZCFGZCBEZCFGZHZABEZCUDUFCUCCIUECIJUHADEZB
      DEZHZDKUGUHCFZABDLUGUKULDUGUKULUDUIUFUJULUDUIHUICFZUJCFZULUFUJHUDUIUMCADM
      NUFUJUNCBDMNUIUJUHCABDOPRQSTUAUB $.
  $}

  $( Derive set.mm's original ~ ax-c9 from the shorter ~ ax-13 .  (Contributed
     by NM, 29-Nov-2015.)  (Revised by NM, 24-Dec-2015.)  (Proof shortened by
     Wolf Lammen, 29-Apr-2018.) $)
  axc9 $p |- ( -. A. z z = x -> ( -. A. z z = y
              -> ( x = y -> A. z x = y ) ) ) $=
    ( weq wal wn wi wa nfeqf nfrd ex ) CADCEFZCBDCEFZABDZNCEGLMHNCABCIJK $.

  $( Derive ~ ax-13 from ~ ax13v via ~ axc9 .  This shows that the weakening in
     ~ ax13v is still sufficient for a complete system.  (Contributed by NM,
     21-Dec-2015.)  (Proof shortened by Wolf Lammen, 31-Jan-2018.) $)
  ax13 $p |- ( -. x = y -> ( y = z -> A. x y = z ) ) $=
    ( weq wn wal wi sp con3i axc9 syl2im ax13b mpbir ) ABDZEZBCDZPAFGZGOACDZEZQ
    GGONAFZESRAFZEQTNNAHIUARRAHIBCAJKABCLM $.

  ${
    $d w x $.  $d w y $.
    $( Obsolete proof ~ axc11nlem as of 30-Nov-2019.  (Contributed by NM,
       8-Jul-2016.)  (Proof shortened by Wolf Lammen, 17-Feb-2018.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    axc11nlemOLD $p |- ( A. x x = w -> A. y y = x ) $=
      ( weq wal cbvaev equequ2 biimprd al2imi syl5com dveeq1 spsd com12 pm2.61d
      wn con1d ) ACDZAEZQBEZBADZBEZRBCDZBESUAABCFQUBTBQTUBACBGHIJRUASUAOZRSUCQS
      ABACKLMPN $.
  $}

  ${
    $d x z $.  $d y z $.
    $( Derive set.mm's original ~ ax-c11n from others.  Commutation law for
       identical variable specifiers.  The antecedent and consequent are true
       when ` x ` and ` y ` are substituted with the same variable.  Lemma L12
       in [Megill] p. 445 (p. 12 of the preprint).  Use ~ aecom instead when
       this does not lengthen the proof.  (Contributed by NM, 10-May-1993.)
       (Revised by NM, 7-Nov-2015.)  (Proof shortened by Wolf Lammen,
       6-Mar-2018.)  Adapt to a modification of ~ axc11nlem .  (Revised by Wolf
       Lammen, 30-Nov-2019.) $)
    axc11n $p |- ( A. x x = y -> A. y y = x ) $=
      ( vz weq wal wex wn wi ax6ev equcomi dveeq1 syl5com axc112 axc11nlem syl6
      syl9 exlimiv ax-mp pm2.18d ) ABDAEZBADBEZCADZCFTUAGZUAHHZCAIUBUDCUBUCACDZ
      BEZTUAUBUEUCUFCAJBACKZLTUFUEAEUAUEBAMABCUGNOPQRS $.
  $}

  ${
    $d x z $.  $d y z $.
    $( Obsolete proof of ~ axc11n as of 30-Nov-2019.  (Contributed by NM,
       10-May-1993.)  (Revised by NM, 7-Nov-2015.)  (Proof shortened by Wolf
       Lammen, 6-Mar-2018.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    axc11nOLD $p |- ( A. x x = y -> A. y y = x ) $=
      ( vz weq wal wex wn ax6ev equcomi dveeq1 syl5com axc112 axc11nlemOLD syl6
      wi syl9 exlimiv ax-mp pm2.18d ) ABDAEZBADBEZCADZCFTUAGZUAOOZCAHUBUDCUBUCA
      CDZBEZTUAUBUEUCUFCAIBACJKTUFUEAEUAUEBALABCMNPQRS $.
  $}

  $( Commutation law for identical variable specifiers.  Both sides of the
     biconditional are true when ` x ` and ` y ` are substituted with the same
     variable.  (Contributed by NM, 10-May-1993.)  Changed to a biconditional.
     (Revised by BJ, 26-Sep-2019.) $)
  aecom $p |- ( A. x x = y <-> A. y y = x ) $=
    ( weq wal axc11n impbii ) ABCADBACBDABEBAEF $.

  ${
    aecoms.1 $e |- ( A. x x = y -> ph ) $.
    $( A commutation rule for identical variable specifiers.  (Contributed by
       NM, 10-May-1993.) $)
    aecoms $p |- ( A. y y = x -> ph ) $=
      ( weq wal aecom sylbi ) CBECFBCEBFACBGDH $.
  $}

  ${
    naecoms.1 $e |- ( -. A. x x = y -> ph ) $.
    $( A commutation rule for distinct variable specifiers.  (Contributed by
       NM, 2-Jan-2002.) $)
    naecoms $p |- ( -. A. y y = x -> ph ) $=
      ( weq wal aecom sylnbir ) CBECFBCEBFABCGDH $.
  $}

  $( Show that ~ ax-c11 can be derived from ~ ax-c11n in the form of
     ~ axc11n .  Normally, ~ axc11 should be used rather than ~ ax-c11 , except
     by theorems specifically studying the latter's properties.  (Contributed
     by NM, 16-May-2008.)  (Proof shortened by Wolf Lammen, 21-Apr-2018.) $)
  axc11 $p |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $=
    ( wal wi axc112 aecoms ) ABDACDECBABCFG $.

  $( All variables are effectively bound in an identical variable specifier.
     (Contributed by NM, 13-May-1993.)  (Proof shortened by Wolf Lammen,
     21-Apr-2018.) $)
  hbae $p |- ( A. x x = y -> A. z A. x x = y ) $=
    ( weq wal wi wn sp axc9 syl7 axc112 axc11 pm2.43i syl5 pm2.61ii axc4i ax-11
    syl ) ABDZAEZSCEZAETCESUAACADCEZCBDCEZTUAFTSUBGUCGUASAHABCIJSACKTSBEZUCUATU
    DSABLMSBCKNOPSACQR $.

  $( All variables are effectively bound in an identical variable specifier.
     (Contributed by Mario Carneiro, 11-Aug-2016.) $)
  nfae $p |- F/ z A. x x = y $=
    ( weq wal hbae nfi ) ABDAECABCFG $.

  $( All variables are effectively bound in a distinct variable specifier.
     Lemma L19 in [Megill] p. 446 (p. 14 of the preprint).  (Contributed by NM,
     13-May-1993.) $)
  hbnae $p |- ( -. A. x x = y -> A. z -. A. x x = y ) $=
    ( weq wal hbae hbn ) ABDAECABCFG $.

  $( All variables are effectively bound in a distinct variable specifier.
     (Contributed by Mario Carneiro, 11-Aug-2016.) $)
  nfnae $p |- F/ z -. A. x x = y $=
    ( weq wal nfae nfn ) ABDAECABCFG $.

  ${
    hbnaes.1 $e |- ( A. z -. A. x x = y -> ph ) $.
    $( Rule that applies ~ hbnae to antecedent.  (Contributed by NM,
       15-May-1993.) $)
    hbnaes $p |- ( -. A. x x = y -> ph ) $=
      ( weq wal wn hbnae syl ) BCFBGHZKDGABCDIEJ $.
  $}

  ${
    $d v w z $.  $d v x $.  $d v y $.
    $( Obsolete proof of ~ aevlem1 as of 30-Nov-2019.  (Contributed by NM,
       22-Jul-2015.)  (Proof shortened by Wolf Lammen, 17-Feb-2018.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    aevlem1OLD $p |- ( A. z z = w -> A. y y = x ) $=
      ( vv weq wal cbvaev axc11nlemOLD 4syl ) CDFCGEDFEGCEFCGAEFAGBAFBGCEDHECDI
      CAEHABEIJ $.
  $}

  ${
    $d x y $.  $d w ph $.
    $( Obsolete proof of ~ axc16g as of 30-Nov-2019.  (Contributed by NM,
       15-May-1993.)  (Proof shortened by Wolf Lammen, 18-Feb-2018.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    axc16gOLD $p |- ( A. x x = y -> ( ph -> A. z ph ) ) $=
      ( vw weq wal aevlem1OLD ax-5 axc11 syl2im ) BCFBGEDFEGAAEGADGDEBCHAEIAEDJ
      K $.
  $}

  ${
    $d u v $.  $d u x y $.  $d u w $.
    $( Obsolete proof of ~ aev as of 30-Nov-2019.  (Contributed by NM,
       8-Nov-2006.)  (Revised by Wolf Lammen, 7-Sep-2018.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    aevOLD $p |- ( A. x x = y -> A. z w = v ) $=
      ( vu weq wal aevlem1 ax-7 spimv syl axc16g mpd ) ABGAHZDEGZPCHOFEGZFHPEFA
      BIQPFDFDEJKLPABCMN $.

    $( Alternate proof of ~ aev .  Uses ~ ax-11 and ~ ax-13 contrary to
       ~ aev .  (Contributed by NM, 8-Nov-2006.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    aevALT $p |- ( A. x x = y -> A. z w = v ) $=
      ( vu weq wal hbae aevlem1 ax-7 spimv syl alrimih ) ABGAHZDEGZCABCIOFEGZFH
      PEFABJQPFDFDEKLMN $.
  $}

  ${
    $d x y z $.  $d z ph $.
    axc16i.1 $e |- ( x = z -> ( ph <-> ps ) ) $.
    axc16i.2 $e |- ( ps -> A. x ps ) $.
    $( Inference with ~ axc16 as its conclusion.  (Contributed by NM,
       20-May-2008.)  (Proof modification is discouraged.) $)
    axc16i $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      ( weq wal wi nfv ax-7 cbv3 spimv equcomi syl syl5com alimdv mpcom alimi
      biimpcd nfi biimprd syl6com 3syl ) CDHZCIEDHZEIZCEHZEIZAACIZJUFUGCEUFEKUG
      CKCEDLMUHECHZEIZUJUFUHUMUGUFECECDLNUFUGULEUFDCHZUGULCDOUGDEHUNULJEDODECLP
      QRSULUIEECOZTPAUJBEIUKAUIBEUIABFUARBAECBCGUBAEKULUIBAJUOUIABFUCPMUDUE $.
  $}

  ${
    $d x y $.
    $( Alternate proof of ~ ax16nf , shorter but requiring ~ ax-11 .
       (Contributed by Mario Carneiro, 7-Oct-2016.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    ax16nfALT $p |- ( A. x x = y -> F/ z ph ) $=
      ( weq wal nfae axc16g nfd ) BCEBFADBCDGABCDHI $.
  $}

  ${
    dral1.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).
       (Contributed by NM, 27-Feb-2005.)  Allow a shortening of ~ dral1 .
       (Revised by Wolf Lammen, 4-Mar-2018.) $)
    dral2 $p |- ( A. x x = y -> ( A. z ph <-> A. z ps ) ) $=
      ( weq wal nfae albid ) CDGCHABECDEIFJ $.

    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).
       (Contributed by NM, 24-Nov-1994.)  Remove dependency on ~ ax-11 .
       (Revised by Wolf Lammen, 6-Sep-2018.) $)
    dral1 $p |- ( A. x x = y -> ( A. x ph <-> A. y ps ) ) $=
      ( weq wal nfa1 albid axc11 axc112 impbid bitrd ) CDFZCGZACGBCGZBDGZOABCNC
      HEIOPQBCDJBDCKLM $.

    $( Alternate proof of ~ dral1 , shorter but requiring ~ ax-11 .
       (Contributed by NM, 24-Nov-1994.)  (Proof shortened by Wolf Lammen,
       22-Apr-2018.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    dral1ALT $p |- ( A. x x = y -> ( A. x ph <-> A. y ps ) ) $=
      ( weq wal dral2 axc11 axc112 impbid bitrd ) CDFCGZACGBCGZBDGZABCDCEHMNOBC
      DIBDCJKL $.

    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).
       (Contributed by NM, 27-Feb-2005.) $)
    drex1 $p |- ( A. x x = y -> ( E. x ph <-> E. y ps ) ) $=
      ( weq wal wn wex notbid dral1 df-ex 3bitr4g ) CDFCGZAHZCGZHBHZDGZHACIBDIN
      PROQCDNABEJKJACLBDLM $.

    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).
       (Contributed by NM, 27-Feb-2005.) $)
    drex2 $p |- ( A. x x = y -> ( E. z ph <-> E. z ps ) ) $=
      ( weq wal hbae exbidh ) CDGCHABECDEIFJ $.

    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       (Contributed by Mario Carneiro, 4-Oct-2016.) $)
    drnf1 $p |- ( A. x x = y -> ( F/ x ph <-> F/ y ps ) ) $=
      ( weq wal wi wnf dral1 imbi12d df-nf 3bitr4g ) CDFCGZAACGZHZCGBBDGZHZDGAC
      IBDIPRCDNABOQEABCDEJKJACLBDLM $.

    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       (Contributed by Mario Carneiro, 4-Oct-2016.)  (Proof shortened by Wolf
       Lammen, 5-May-2018.) $)
    drnf2 $p |- ( A. x x = y -> ( F/ z ph <-> F/ z ps ) ) $=
      ( weq wal nfae nfbidf ) CDGCHABECDEIFJ $.
  $}

  ${
    nfald2.1 $e |- F/ y ph $.
    nfald2.2 $e |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $.
    $( Variation on ~ nfald which adds the hypothesis that ` x ` and ` y ` are
       distinct in the inner subproof.  (Contributed by Mario Carneiro,
       8-Oct-2016.) $)
    nfald2 $p |- ( ph -> F/ x A. y ps ) $=
      ( weq wal wnf wn wa nfnae nfan nfald ex nfa1 biidd drnf1 mpbiri pm2.61d2
      ) ACDGCHZBDHZCIZAUAJZUCAUDKBCDAUDDECDDLMFNOUAUCUBDIBDPUBUBCDUAUBQRST $.

    $( Variation on ~ nfexd which adds the hypothesis that ` x ` and ` y ` are
       distinct in the inner subproof.  (Contributed by Mario Carneiro,
       8-Oct-2016.) $)
    nfexd2 $p |- ( ph -> F/ x E. y ps ) $=
      ( wex wn wal df-ex weq wa nfnd nfald2 nfxfrd ) BDGBHZDIZHACBDJAQCAPCDEACD
      KCIHLBCFMNMO $.
  $}

  ${
    exdistrf.1 $e |- ( -. A. x x = y -> F/ y ph ) $.
    $( Distribution of existential quantifiers, with a bound-variable
       hypothesis saying that ` y ` is not free in ` ph ` , but ` x ` can be
       free in ` ph ` (and there is no distinct variable condition on ` x ` and
       ` y ` ).  (Contributed by Mario Carneiro, 20-Mar-2013.)  (Proof
       shortened by Wolf Lammen, 14-May-2018.) $)
    exdistrf $p |- ( E. x E. y ( ph /\ ps ) -> E. x ( ph /\ E. y ps ) ) $=
      ( wa wex weq wal wi 19.8a anim2i eximi biidd drex1 syl5ibr wn 19.40 19.9d
      nfe1 anim1d syl56 pm2.61i exlimi ) ABFZDGZABDGZFZCGZCUHCTCDHCIZUFUIJUFUIU
      JUHDGUEUHDBUGABDKLMUHUHCDUJUHNOPUFADGZUGFUJQZUHUIABDRULUKAUGAULDESUAUHCKU
      BUCUD $.
  $}

  ${
    dvelimf.1 $e |- F/ x ph $.
    dvelimf.2 $e |- F/ z ps $.
    dvelimf.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Version of ~ dvelimv without any variable restrictions.  (Contributed by
       NM, 1-Oct-2002.)  (Revised by Mario Carneiro, 6-Oct-2016.)  (Proof
       shortened by Wolf Lammen, 11-May-2018.) $)
    dvelimf $p |- ( -. A. x x = y -> F/ x ps ) $=
      ( weq wi wal wn equsal bicomi nfnae wa wnf nfeqf ancoms a1i nfald2 nfxfrd
      nfimd ) BEDIZAJZEKZCDICKLZCUFBABEDGHMNUGUECECDEOUGCEICKLZPZUDACUHUGUDCQED
      CRSACQUIFTUCUAUB $.
  $}

  ${
    dvelimdf.1 $e |- F/ x ph $.
    dvelimdf.2 $e |- F/ z ph $.
    dvelimdf.3 $e |- ( ph -> F/ x ps ) $.
    dvelimdf.4 $e |- ( ph -> F/ z ch ) $.
    dvelimdf.5 $e |- ( ph -> ( z = y -> ( ps <-> ch ) ) ) $.
    $( Deduction form of ~ dvelimf .  (Contributed by NM, 7-Apr-2004.)
       (Revised by Mario Carneiro, 6-Oct-2016.)  (Proof shortened by Wolf
       Lammen, 11-May-2018.) $)
    dvelimdf $p |- ( ph -> ( -. A. x x = y -> F/ x ch ) ) $=
      ( weq wal wn wi wnf nfim1 wb com12 pm5.74d dvelimf pm5.5 nfbidf syl5ib )
      DELDMNACOZDPACDPABOUEDEFABDGIQACFHJQFELZABCAUFBCRKSTUAAUECDGACUBUCUD $.
  $}

  ${
    dvelimh.1 $e |- ( ph -> A. x ph ) $.
    dvelimh.2 $e |- ( ps -> A. z ps ) $.
    dvelimh.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Version of ~ dvelim without any variable restrictions.  (Contributed by
       NM, 1-Oct-2002.)  (Proof shortened by Wolf Lammen, 11-May-2018.) $)
    dvelimh $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( weq wal wn nfi dvelimf nfrd ) CDICJKBCABCDEACFLBEGLHMN $.
  $}

  ${
    $d z ps $.
    dvelim.1 $e |- ( ph -> A. x ph ) $.
    dvelim.2 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( This theorem can be used to eliminate a distinct variable restriction on
       ` x ` and ` z ` and replace it with the ""distinctor"" ` -. A. x x = y `
       as an antecedent. ` ph ` normally has ` z ` free and can be read
       ` ph ( z ) ` , and ` ps ` substitutes ` y ` for ` z ` and can be read
       ` ph ( y ) ` .  We do not require that ` x ` and ` y ` be distinct: if
       they are not, the distinctor will become false (in multiple-element
       domains of discourse) and ""protect"" the consequent.

       To obtain a closed-theorem form of this inference, prefix the hypotheses
       with ` A. x A. z ` , conjoin them, and apply ~ dvelimdf .

       Other variants of this theorem are ~ dvelimh (with no distinct variable
       restrictions) and ~ dvelimhw (that avoids ~ ax-13 ).  (Contributed by
       NM, 23-Nov-1994.) $)
    dvelim $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( ax-5 dvelimh ) ABCDEFBEHGI $.
  $}

  ${
    $d x ph $.  $d z ps $.
    dvelimv.1 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Similar to ~ dvelim with first hypothesis replaced by distinct variable
       condition.  (Contributed by NM, 25-Jul-2015.)  (Proof shortened by Wolf
       Lammen, 30-Apr-2018.) $)
    dvelimv $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( ax-5 dvelim ) ABCDEACGFH $.
  $}

  ${
    $d z ps $.
    dvelimnf.1 $e |- F/ x ph $.
    dvelimnf.2 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Version of ~ dvelim using ""not free"" notation.  (Contributed by Mario
       Carneiro, 9-Oct-2016.) $)
    dvelimnf $p |- ( -. A. x x = y -> F/ x ps ) $=
      ( nfv dvelimf ) ABCDEFBEHGI $.
  $}

  ${
    $d w x z $.  $d w y $.
    $( Alternate proof of ~ dveeq2 , shorter but requiring ~ ax-11 .
       (Contributed by NM, 2-Jan-2002.)  (Revised by NM, 20-Jul-2015.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    dveeq2ALT $p |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $=
      ( vw weq equequ2 dvelimv ) CDECBEABDDBCFG $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    ax12v2.1 $e |- ( x = z -> ( ph -> A. x ( x = z -> ph ) ) ) $.
    $( Recovery of ~ ax-c15 from ~ ax12v .  This proof uses ~ ax-c11n and
       ~ ax-12 .  TODO: figure out if this is useful, or if it should be
       simplified or eliminated.  (Contributed by NM, 2-Feb-2007.)  (Proof
       shortened by Wolf Lammen, 21-Apr-2018.) $)
    ax12v2 $p |- ( -. A. x x = y ->
                 ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( weq wal wn wex wi ax6ev dveeq2 wb equequ2 sps nfa1 imbi1d albid imbi12d
      imbi2d mpbii syl6 exlimdv mpi ) BCFZBGHZDCFZDIUEAUEAJZBGZJZJZDCKUFUGUKDUF
      UGUGBGZUKBCDLULBDFZAUMAJZBGZJZJUKEULUMUEUPUJUGUMUEMBDCBNOZULUOUIAULUNUHBU
      GBPULUMUEAUQQRTSUAUBUCUD $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    ax12a2.1 $e |- ( x = z -> ( A. z ph -> A. x ( x = z -> ph ) ) ) $.
    $( Derive ~ ax-c15 from a hypothesis in the form of ~ ax-12 . ~ ax-c11n and
       ~ ax-12 are used by the proof, but not ~ ax-c11 or ~ ax-c15 .  TODO:
       figure out if this is useful, or if it should be simplified or
       eliminated.  (Contributed by NM, 2-Feb-2007.) $)
    ax12a2 $p |- ( -. A. x x = y ->
                 ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( ax12v ax12v2 ) ABCDABDFG $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    $( Derivation of set.mm's original ~ ax-c15 from ~ ax-c11n and the shorter
       ~ ax-12 that has replaced it.

       Theorem ~ ax12 shows the reverse derivation of ~ ax-12 from ~ ax-c15 .

       Normally, ~ axc15 should be used rather than ~ ax-c15 , except by
       theorems specifically studying the latter's properties.  (Contributed by
       NM, 3-Feb-2007.) $)
    axc15 $p |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( vz ax-12 ax12a2 ) ABCDABDEF $.
  $}

  $( A bidirectional version of ~ axc15 .  (Contributed by NM, 30-Jun-2006.) $)
  ax12b $p |- ( ( -. A. x x = y /\ x = y ) ->
              ( ph <-> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wn wa wi axc15 imp sp com12 adantl impbid ) BCDZBEFZOGAOAHZBEZPOA
    RHABCIJORAHPROAQBKLMN $.

  $( A variable introduction law for equality.  Lemma 15 of [Monk2] p. 109,
     however we do not require ` z ` to be distinct from ` x ` and ` y ` .  See
     ~ equvin for a shorter proof requiring fewer axioms when ` z ` is required
     to be distinct from ` x ` and ` y ` .  (Contributed by NM, 10-Jan-1993.)
     (Proof shortened by Andrew Salmon, 25-May-2011.)  (Proof shortened by Wolf
     Lammen, 15-Sep-2018.) $)
  equvini $p |- ( x = y -> E. z ( x = z /\ z = y ) ) $=
    ( weq wa wex wi equtr equequ2 biimprd anc2ri syli 19.8a syl6 wn ax13 eximii
    wal ax6e 19.35i pm2.61i ) CADZABDZACDZCBDZEZCFZGUBUCUFUGUCUBUEUFCABHUEUCUDU
    EUDUCCBAIJKZLUFCMNUBOUCUCCRUGCABPUCUFCUEUCUFGCCBSUHQTNUA $.

  $( A variable elimination law for equality with no distinct variable
     requirements.  (Compare ~ equvini .)  (Contributed by NM, 1-Mar-2013.)
     (Proof shortened by Mario Carneiro, 17-Oct-2016.)  (Proof shortened by
     Wolf Lammen, 15-Jun-2019.) $)
  equveli $p |- ( A. z ( z = x <-> z = y ) -> x = y ) $=
    ( weq wb wal wex albi wi ax6e bi2 ax-7 syli com12 eximii 19.35i spsd sps wn
    a1dd wa nfeqf 19.9d ex bija sylc ) CADZCBDZEZCFUGCFZUHCFZEABDZCGZULUGUHCHUI
    ULCUHUIULICCBJUIUHULUHUIUGULUGUHKCABLZMNOPUJUKUMULIZUJUKULUMUGUKULICUGUHULC
    UNQRTUJSZUKSZUOULUPUQUACABCUBUCUDUEUF $.

  $( Obsolete proof of ~ equveli as of 15-Jun-2019.  (Contributed by NM,
     1-Mar-2013.)  (Proof shortened by Mario Carneiro, 17-Oct-2016.)  (Proof
     shortened by Wolf Lammen, 11-Sep-2018.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  equveliOLD $p |- ( A. z ( z = x <-> z = y ) -> x = y ) $=
    ( weq wb wal wi wex ax6e bi2 ax-7 syli com12 eximii 19.35i wnf nfeqf al2imi
    wn ex nf2 syl6ib syl7 bi1 syld pm2.61ii 19.21bi ) CADZCBDZEZCFZABDZCUHCFZUI
    CFZUKULCFZGUKULCHZUMSZUNSZUOUJULCUIUJULGCCBIUJUIULUIUJUHULUHUIJCABKZLMZNOUQ
    URULCPZUPUOGUQURVAABCQTULCUAUBUCUHUJULCUHUJUIULUJUHUIUHUIUDMUSUERUIUJULCUTR
    UFUG $.

  ${
    $d x z $.  $d y z $.
    $( Obsolete proof of ~ equvin as of 10-Jun-2019.  (Contributed by NM,
       5-Aug-1993.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    equvinOLD $p |- ( x = y <-> E. z ( x = z /\ z = y ) ) $=
      ( weq wa wex equvini equtr imp exlimiv impbii ) ABDZACDZCBDZEZCFABCGOLCMN
      LACBHIJK $.
  $}

  ${
    equs45f.1 $e |- F/ y ph $.
    $( Two ways of expressing substitution when ` y ` is not free in ` ph ` .
       The implication ""to the left"" is ~ equs4 and does not require the
       non-freeness hypothesis.  Theorem ~ sb56 replaces the non-freeness
       hypothesis with a dv condition.  (Contributed by NM, 25-Apr-2008.)
       (Revised by Mario Carneiro, 4-Oct-2016.) $)
    equs45f $p |- ( E. x ( x = y /\ ph ) <-> A. x ( x = y -> ph ) ) $=
      ( weq wa wex wi wal nfri anim2i eximi equs5a syl equs4 impbii ) BCEZAFZBG
      ZQAHBIZSQACIZFZBGTRUBBAUAQACDJKLABCMNABCOP $.
  $}

  $( Lemma used in proofs of substitution properties.  (Contributed by NM,
     14-May-1993.)  (Revised by BJ, 1-Oct-2018.) $)
  equs5 $p |- ( -. A. x x = y ->
             ( E. x ( x = y /\ ph ) <-> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wn wa wex wi nfna1 nfa1 axc15 impd exlimd equs4 impbid1 ) BCDZBEF
    ZQAGZBHQAIZBEZRSUABQBJTBKRQAUAABCLMNABCOP $.

  $( One direction of a simplified definition of substitution.  The converse
     requires either a dv condition ( ~ sb6 ) or a non-freeness hypothesis
     ( ~ sb6f ).  (Contributed by NM, 13-May-1993.) $)
  sb2 $p |- ( A. x ( x = y -> ph ) -> [ y / x ] ph ) $=
    ( weq wi wal wa wex wsb sp equs4 df-sb sylanbrc ) BCDZAEZBFONAGBHABCIOBJABC
    KABCLM $.

  $( The specialization axiom of standard predicate calculus.  It states that
     if a statement ` ph ` holds for all ` x ` , then it also holds for the
     specific case of ` y ` (properly) substituted for ` x ` .  Translated to
     traditional notation, it can be read:  "" ` A. x ph ( x ) -> ph ( y ) ` ,
     provided that ` y ` is free for ` x ` in ` ph ( x ) ` .""  Axiom 4 of
     [Mendelson] p. 69.  See also ~ spsbc and ~ rspsbc .  (Contributed by NM,
     14-May-1993.) $)
  stdpc4 $p |- ( A. x ph -> [ y / x ] ph ) $=
    ( wal weq wi wsb ala1 sb2 syl ) ABDBCEZAFBDABCGAKBHABCIJ $.

  $( A double specialization using explicit substitution.  This is Theorem
     PM*11.1 in [WhiteheadRussell] p. 159.  See ~ stdpc4 for the analogous
     single specialization.  See ~ 2sp for another double specialization.
     (Contributed by Andrew Salmon, 24-May-2011.)  (Revised by BJ,
     21-Oct-2018.) $)
  2stdpc4 $p |- ( A. x A. y ph -> [ z / x ] [ w / y ] ph ) $=
    ( wal wsb stdpc4 alimi syl ) ACFZBFACEGZBFLBDGKLBACEHILBDHJ $.

  $( One direction of a simplified definition of substitution when variables
     are distinct.  (Contributed by NM, 5-Aug-1993.) $)
  sb3 $p |- ( -. A. x x = y -> ( E. x ( x = y /\ ph ) -> [ y / x ] ph ) ) $=
    ( weq wal wn wa wex wi wsb equs5 sb2 syl6bi ) BCDZBEFNAGBHNAIBEABCJABCKABCL
    M $.

  $( One direction of a simplified definition of substitution when variables
     are distinct.  (Contributed by NM, 14-May-1993.) $)
  sb4 $p |- ( -. A. x x = y -> ( [ y / x ] ph -> A. x ( x = y -> ph ) ) ) $=
    ( wsb weq wa wex wal wn wi sb1 equs5 syl5ib ) ABCDBCEZAFBGNBHINAJBHABCKABCL
    M $.

  $( Simplified definition of substitution when variables are distinct.
     (Contributed by NM, 27-May-1997.) $)
  sb4b $p |- ( -. A. x x = y -> ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wn wsb wi sb4 sb2 impbid1 ) BCDZBEFABCGLAHBEABCIABCJK $.

  $( Bound-variable hypothesis builder for substitution.  (Contributed by NM,
     14-May-1993.) $)
  hbsb2 $p |- ( -. A. x x = y -> ( [ y / x ] ph -> A. x [ y / x ] ph ) ) $=
    ( weq wal wn wsb wi sb4 sb2 axc4i syl6 ) BCDZBEFABCGZMAHZBENBEABCIONBABCJKL
    $.

  $( Bound-variable hypothesis builder for substitution.  (Contributed by Mario
     Carneiro, 4-Oct-2016.) $)
  nfsb2 $p |- ( -. A. x x = y -> F/ x [ y / x ] ph ) $=
    ( weq wal wn wsb nfna1 hbsb2 nfd ) BCDZBEFABCGBKBHABCIJ $.

  $( Special case of a bound-variable hypothesis builder for substitution.
     (Contributed by NM, 2-Feb-2007.) $)
  hbsb2a $p |- ( [ y / x ] A. y ph -> A. x [ y / x ] ph ) $=
    ( wal wsb weq wi sb4a sb2 axc4i syl ) ACDBCEBCFAGZBDABCEZBDABCHLMBABCIJK $.

  $( Special case of a bound-variable hypothesis builder for substitution.
     (Contributed by NM, 2-Feb-2007.) $)
  hbsb2e $p |- ( [ y / x ] ph -> A. x [ y / x ] E. y ph ) $=
    ( wsb weq wex wi wal sb4e sb2 axc4i syl ) ABCDBCEACFZGZBHMBCDZBHABCINOBMBCJ
    KL $.

  ${
    hbsb3.1 $e |- ( ph -> A. y ph ) $.
    $( If ` y ` is not free in ` ph ` , ` x ` is not free in
       ` [ y / x ] ph ` .  (Contributed by NM, 14-May-1993.) $)
    hbsb3 $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $=
      ( wsb wal sbimi hbsb2a syl ) ABCEZACFZBCEJBFAKBCDGABCHI $.
  $}

  ${
    nfs1.1 $e |- F/ y ph $.
    $( If ` y ` is not free in ` ph ` , ` x ` is not free in
       ` [ y / x ] ph ` .  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfs1 $p |- F/ x [ y / x ] ph $=
      ( wsb nfri hbsb3 nfi ) ABCEBABCACDFGH $.
  $}

  ${
    $d x y z $.  $d z ph $.
    $( Alternate proof of ~ axc16 , shorter but requiring ~ ax-11 and using
       ~ df-sb .  (Contributed by NM, 17-May-2008.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    axc16ALT $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      ( vz wsb sbequ12 ax-5 hbsb3 axc16i ) AABDEBCDABDFABDADGHI $.
  $}

  ${
    $d x y $.
    $( Alternate proof of ~ axc16g that uses ~ df-sb .  (Contributed by NM,
       15-May-1993.)  (Proof shortened by Andrew Salmon, 25-May-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    axc16gALT $p |- ( A. x x = y -> ( ph -> A. z ph ) ) $=
      ( weq wal aev axc16ALT biidd dral1 biimprd sylsyld ) BCEBFDBEDFZAABFZADFZ
      BCDDBGABCHMONAADBMAIJKL $.
  $}

  $( Substitution applied to an atomic wff.  (Contributed by NM,
     10-May-1993.) $)
  equsb1 $p |- [ y / x ] x = y $=
    ( weq wi wsb sb2 id mpg ) ABCZIDIABEAIABFIGH $.

  $( Substitution applied to an atomic wff.  (Contributed by NM,
     10-May-1993.) $)
  equsb2 $p |- [ y / x ] y = x $=
    ( weq wi wsb sb2 equcomi mpg ) ABCBACZDIABEAIABFABGH $.

  ${
    $d x z $.  $d y z $.
    $( When the class variables in definition ~ df-clel are replaced with
       setvar variables, this theorem of predicate calculus is the result.
       This theorem provides part of the justification for the consistency of
       that definition, which ""overloads"" the setvar variables in ~ wel with
       the class variables in ~ wcel .  Note:  This proof is referenced on the
       Metamath Proof Explorer Home Page and shouldn't be changed.
       (Contributed by NM, 28-Jan-2004.)
       (Proof modification is discouraged.) $)
    cleljust $p |- ( x e. y <-> E. z ( z = x /\ z e. y ) ) $=
      ( weq wel wa wex ax-5 elequ1 equsexh bicomi ) CADCBEZFCGABEZLMCAMCHCABIJK
      $.
  $}

  ${
    $d x z $.  $d y z $.
    $( Alternate proof of ~ cleljust .  (Contributed by NM, 28-Jan-2004.)
       (Revised by Mario Carneiro, 21-Dec-2016.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    cleljustALT $p |- ( x e. y <-> E. z ( z = x /\ z e. y ) ) $=
      ( weq wel wa wex nfv elequ1 equsex bicomi ) CADCBEZFCGABEZLMCAMCHCABIJK
      $.
  $}

  ${
    $d w z x $.  $d w y $.
    $( Quantifier introduction when one pair of variables is distinct.
       (Contributed by NM, 2-Jan-2002.) $)
    dveel1 $p |- ( -. A. x x = y -> ( y e. z -> A. x y e. z ) ) $=
      ( vw wel elequ1 dvelimv ) DCEBCEABDDBCFG $.

    $( Quantifier introduction when one pair of variables is distinct.
       (Contributed by NM, 2-Jan-2002.) $)
    dveel2 $p |- ( -. A. x x = y -> ( z e. y -> A. x z e. y ) ) $=
      ( vw wel elequ2 dvelimv ) CDECBEABDDBCFG $.
  $}

  ${
    $d w y $.  $d w z $.  $d w x $.  $( ` w ` is dummy. $)
    $( Axiom ~ ax-c14 is redundant if we assume ~ ax-5 .  Remark 9.6 in
       [Megill] p. 448 (p. 16 of the preprint), regarding axiom scheme C14'.

       Note that ` w ` is a dummy variable introduced in the proof.  Its
       purpose is to satisfy the distinct variable requirements of ~ dveel2 and
       ~ ax-5 .  By the end of the proof it has vanished, and the final theorem
       has no distinct variable requirements.  (Contributed by NM,
       29-Jun-1995.)  (Proof modification is discouraged.) $)
    axc14 $p |- ( -. A. z z = x -> ( -. A. z z = y ->
              ( x e. y -> A. z x e. y ) ) ) $=
      ( vw weq wal wn wel hbn1 dveel2 hbim1 elequ1 imbi2d dvelim nfa1 nfn 19.21
      wi syl6ib pm2.86d ) CAECFGZCBEZCFZGZABHZUECFZUAUDUERZUGCFUDUFRUDDBHZRUGCA
      DUDUHCUBCICBDJKDAEUHUEUDDABLMNUDUECUCCUBCOPQST $.
  $}

  $( An alternate definition of proper substitution that, like ~ df-sb , mixes
     free and bound variables to avoid distinct variable requirements.
     (Contributed by NM, 17-Feb-2005.) $)
  dfsb2 $p |- ( [ y / x ] ph <->
              ( ( x = y /\ ph ) \/ A. x ( x = y -> ph ) ) ) $=
    ( wsb weq wa wi wal wo sp sbequ2 sps orc syl6an sb4 olc syl6 pm2.61i sbequ1
    wn imp sb2 jaoi impbii ) ABCDZBCEZAFZUFAGBHZIZUFBHZUEUIGUJUFUEAUIUFBJUFUEAG
    BABCKLUGUHMNUJTUEUHUIABCOUHUGPQRUGUEUHUFAUEABCSUAABCUBUCUD $.

  $( An alternate definition of proper substitution ~ df-sb that uses only
     primitive connectives (no defined terms) on the right-hand side.
     (Contributed by NM, 6-Mar-2007.) $)
  dfsb3 $p |- ( [ y / x ] ph <->
              ( ( x = y -> -. ph ) -> A. x ( x = y -> ph ) ) ) $=
    ( weq wa wi wal wo wn wsb df-or dfsb2 imnan imbi1i 3bitr4i ) BCDZAEZPAFBGZH
    QIZRFABCJPAIFZRFQRKABCLTSRPAMNO $.

  $( An equality theorem for substitution.  (Contributed by NM, 14-May-1993.)
     (Proof shortened by Wolf Lammen, 15-Sep-2018.) $)
  sbequi $p |- ( x = y -> ( [ x / z ] ph -> [ y / z ] ph ) ) $=
    ( weq wsb wi equtr sbequ2 sbequ1 syl9 syld wn wal ax13 sp con3i sb4 equequ2
    syl biimprd imim1d al2imi sb2 syl6 pm2.61i ) DBEZBCEZADBFZADCFZGZGUGUHDCEZU
    KDBCHUGUIAULUJADBIADCJKLUGMZUHUHDNZUKDBCOUMUIUGAGZDNZUNUJUMUGDNZMUIUPGUQUGU
    GDPQADBRTUNUPULAGZDNUJUHUOURDUHULUGAUHUGULBCDSUAUBUCADCUDUEKLUF $.

  $( An equality theorem for substitution.  Used in proof of Theorem 9.7 in
     [Megill] p. 449 (p. 16 of the preprint).  (Contributed by NM,
     14-May-1993.) $)
  sbequ $p |- ( x = y -> ( [ x / z ] ph <-> [ y / z ] ph ) ) $=
    ( weq wsb sbequi wi equcoms impbid ) BCEADBFZADCFZABCDGLKHCBACBDGIJ $.

  $( Formula-building lemma for use with the Distinctor Reduction Theorem.
     Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  (Contributed
     by NM, 2-Jun-1993.) $)
  drsb1 $p |- ( A. x x = y -> ( [ z / x ] ph <-> [ z / y ] ph ) ) $=
    ( weq wal wi wa wex wsb wb equequ1 sps imbi1d anbi1d drex1 anbi12d 3bitr4g
    df-sb ) BCEZBFZBDEZAGZUBAHZBIZHCDEZAGZUFAHZCIZHABDJACDJUAUCUGUEUIUAUBUFATUB
    UFKBBCDLMZNUDUHBCUAUBUFAUJOPQABDSACDSR $.

  $( Formula-building lemma for use with the Distinctor Reduction Theorem.
     Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  (Contributed
     by NM, 27-Feb-2005.) $)
  drsb2 $p |- ( A. x x = y -> ( [ x / z ] ph <-> [ y / z ] ph ) ) $=
    ( weq wsb wb sbequ sps ) BCEADBFADCFGBABCDHI $.

  $( Substitution has no effect on a non-free variable.  (Contributed by NM,
     30-May-2009.)  (Revised by Mario Carneiro, 12-Oct-2016.)  (Proof shortened
     by Wolf Lammen, 3-May-2018.) $)
  sbft $p |- ( F/ x ph -> ( [ y / x ] ph <-> ph ) ) $=
    ( wnf wsb wex spsbe 19.9t syl5ib wal nfr stdpc4 syl6 impbid ) ABDZABCEZAPAB
    FOAABCGABHIOAABJPABKABCLMN $.

  ${
    sbf.1 $e |- F/ x ph $.
    $( Substitution for a variable not free in a wff does not affect it.
       (Contributed by NM, 14-May-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
    sbf $p |- ( [ y / x ] ph <-> ph ) $=
      ( wnf wsb wb sbft ax-mp ) ABEABCFAGDABCHI $.
  $}

  ${
    sbh.1 $e |- ( ph -> A. x ph ) $.
    $( Substitution for a variable not free in a wff does not affect it.
       (Contributed by NM, 14-May-1993.) $)
    sbh $p |- ( [ y / x ] ph <-> ph ) $=
      ( nfi sbf ) ABCABDEF $.
  $}

  $( Substitution has no effect on a bound variable.  (Contributed by NM,
     1-Jul-2005.) $)
  sbf2 $p |- ( [ y / x ] A. x ph <-> A. x ph ) $=
    ( wal nfa1 sbf ) ABDBCABEF $.

  ${
    nfs1f.1 $e |- F/ x ph $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfs1f $p |- F/ x [ y / x ] ph $=
      ( wsb sbf nfxfr ) ABCEABABCDFDG $.
  $}

  ${
    sb6x.1 $e |- F/ x ph $.
    $( Equivalence involving substitution for a variable not free.
       (Contributed by NM, 2-Jun-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
    sb6x $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $=
      ( wsb weq wi wal sbf biidd equsal bitr4i ) ABCEABCFZAGBHABCDIAABCDMAJKL
      $.
  $}

  ${
    sb6f.1 $e |- F/ y ph $.
    $( Equivalence for substitution when ` y ` is not free in ` ph ` .  The
       implication ""to the left"" is ~ sb2 and does not require the non-freeness
       hypothesis.  Theorem ~ sb6 replaces the non-freeness hypothesis with a
       dv condition.  (Contributed by NM, 2-Jun-1993.)  (Revised by Mario
       Carneiro, 4-Oct-2016.) $)
    sb6f $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $=
      ( wsb weq wi wal nfri sbimi sb4a syl sb2 impbii ) ABCEZBCFAGBHZOACHZBCEPA
      QBCACDIJABCKLABCMN $.

    $( Equivalence for substitution when ` y ` is not free in ` ph ` .  The
       implication ""to the right"" is ~ sb1 and does not require the
       non-freeness hypothesis.  Theorem ~ sb5 replaces the non-freeness
       hypothesis with a dv condition.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 4-Oct-2016.) $)
    sb5f $p |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) ) $=
      ( wsb weq wi wal wa wex sb6f equs45f bitr4i ) ABCEBCFZAGBHNAIBJABCDKABCDL
      M $.
  $}

  $( Substitution does not change an identical variable specifier.
     (Contributed by NM, 15-May-1993.) $)
  sbequ5 $p |- ( [ w / z ] A. x x = y <-> A. x x = y ) $=
    ( weq wal nfae sbf ) ABEAFCDABCGH $.

  $( Substitution does not change a distinctor.  (Contributed by NM,
     5-Aug-1993.) $)
  sbequ6 $p |- ( [ w / z ] -. A. x x = y <-> -. A. x x = y ) $=
    ( weq wal wn nfnae sbf ) ABEAFGCDABCHI $.

  $( A variable not free remains so after substitution with a distinct variable
     (closed form of ~ nfsb4 ).  (Contributed by NM, 7-Apr-2004.)  (Revised by
     Mario Carneiro, 4-Oct-2016.)  (Proof shortened by Wolf Lammen,
     11-May-2018.) $)
  nfsb4t $p |- ( A. x F/ z ph ->
                 ( -. A. z z = y -> F/ z [ y / x ] ph ) ) $=
    ( wnf wal weq wn wsb wi wa sbequ12 sps drnf2 biimpd spsd impcom nfnae nfan
    wb a1d nfnf1 nfal nfa1 sp adantr nfsb2 adantl a1i dvelimdf pm2.61dan ) ADEZ
    BFZBCGZBFZDCGDFHZABCIZDEZJUMUOKURUPUOUMURUOULURBUOULURAUQBCDUNAUQTZBABCLZMN
    OPQUAUMUOHZKZAUQDCBUMVADULDBADUBUCBCDRSUMVABULBUDBCBRSUMULVAULBUEUFVAUQBEUM
    ABCUGUHUNUSJVBUTUIUJUK $.

  ${
    nfsb4.1 $e |- F/ z ph $.
    $( A variable not free remains so after substitution with a distinct
       variable.  (Contributed by NM, 14-May-1993.)  (Revised by Mario
       Carneiro, 4-Oct-2016.) $)
    nfsb4 $p |- ( -. A. z z = y -> F/ z [ y / x ] ph ) $=
      ( wnf weq wal wn wsb wi nfsb4t mpg ) ADFDCGDHIABCJDFKBABCDLEM $.
  $}

  $( Negation inside and outside of substitution are equivalent.  (Contributed
     by NM, 14-May-1993.)  (Proof shortened by Wolf Lammen, 30-Apr-2018.) $)
  sbn $p |- ( [ y / x ] -. ph <-> -. [ y / x ] ph ) $=
    ( wn wsb weq wi wal wa wex df-sb exanali anbi2i annim 3bitri dfsb3 xchbinxr
    ) ADZBCEZBCFZRGZTAGBHZGZABCESUATRIBJZIUAUBDZIUCDRBCKUDUEUATABLMUAUBNOABCPQ
    $.

  $( Removal of implication from substitution.  (Contributed by NM,
     14-May-1993.) $)
  sbi1 $p |- ( [ y / x ] ( ph -> ps ) -> ( [ y / x ] ph -> [ y / x ] ps ) ) $=
    ( weq wal wi wsb sbequ2 syl5d sbequ1 syl6d sps sb4 ax-2 al2imi syl6 pm2.61i
    wn sb2 ) CDEZCFZABGZCDHZACDHZBCDHZGGZUAUGCUAUDUEBUFUAUEAUDBACDIUCCDIJBCDKLM
    UBSZUEUAAGZCFZUDUFACDNUHUDUAUCGZCFZUJUFGUCCDNULUJUABGZCFUFUKUIUMCUAABOPBCDT
    QQJR $.

  $( Introduction of implication into substitution.  (Contributed by NM,
     14-May-1993.) $)
  sbi2 $p |- ( ( [ y / x ] ph -> [ y / x ] ps ) -> [ y / x ] ( ph -> ps ) ) $=
    ( wsb wi wn sbn pm2.21 sbimi sylbir ax-1 ja ) ACDEZBCDEABFZCDEZNGAGZCDEPACD
    HQOCDABIJKBOCDBALJM $.

  $( Specialization of implication.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Andrew Salmon, 25-May-2011.) $)
  spsbim $p |- ( A. x ( ph -> ps ) -> ( [ y / x ] ph -> [ y / x ] ps ) ) $=
    ( wi wal wsb stdpc4 sbi1 syl ) ABEZCFKCDGACDGBCDGEKCDHABCDIJ $.

  $( Implication inside and outside of substitution are equivalent.
     (Contributed by NM, 14-May-1993.) $)
  sbim $p |- ( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> [ y / x ] ps ) ) $=
    ( wi wsb sbi1 sbi2 impbii ) ABECDFACDFBCDFEABCDGABCDHI $.

  ${
    sbrim.1 $e |- F/ x ph $.
    $( Substitution with a variable not free in antecedent affects only the
       consequent.  (Contributed by NM, 2-Jun-1993.)  (Revised by Mario
       Carneiro, 4-Oct-2016.) $)
    sbrim $p |- ( [ y / x ] ( ph -> ps ) <-> ( ph -> [ y / x ] ps ) ) $=
      ( wi wsb sbim sbf imbi1i bitri ) ABFCDGACDGZBCDGZFAMFABCDHLAMACDEIJK $.
  $}

  ${
    sblim.1 $e |- F/ x ps $.
    $( Substitution with a variable not free in consequent affects only the
       antecedent.  (Contributed by NM, 14-Nov-2013.)  (Revised by Mario
       Carneiro, 4-Oct-2016.) $)
    sblim $p |- ( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> ps ) ) $=
      ( wi wsb sbim sbf imbi2i bitri ) ABFCDGACDGZBCDGZFLBFABCDHMBLBCDEIJK $.
  $}

  $( Logical OR inside and outside of substitution are equivalent.
     (Contributed by NM, 29-Sep-2002.) $)
  sbor $p |- ( [ y / x ] ( ph \/ ps ) <-> ( [ y / x ] ph \/ [ y / x ] ps ) ) $=
    ( wn wi wsb wo sbim sbn imbi1i bitri df-or sbbii 3bitr4i ) AEZBFZCDGZACDGZE
    ZBCDGZFZABHZCDGSUAHRPCDGZUAFUBPBCDIUDTUAACDJKLUCQCDABMNSUAMO $.

  $( Conjunction inside and outside of a substitution are equivalent.
     (Contributed by NM, 14-May-1993.) $)
  sban $p |- ( [ y / x ] ( ph /\ ps ) <-> ( [ y / x ] ph /\ [ y / x ] ps ) ) $=
    ( wn wi wsb wa sbn sbim imbi2i bitri xchbinx df-an sbbii 3bitr4i ) ABEZFZEZ
    CDGZACDGZBCDGZEZFZEABHZCDGUAUBHTRCDGZUDRCDIUFUAQCDGZFUDAQCDJUGUCUABCDIKLMUE
    SCDABNOUAUBNP $.

  $( Conjunction inside and outside of a substitution are equivalent.
     (Contributed by NM, 14-Dec-2006.) $)
  sb3an $p |- ( [ y / x ] ( ph /\ ps /\ ch ) <->
              ( [ y / x ] ph /\ [ y / x ] ps /\ [ y / x ] ch ) ) $=
    ( w3a wsb wa df-3an sbbii sban anbi1i bitr4i 3bitri ) ABCFZDEGABHZCHZDEGPDE
    GZCDEGZHZADEGZBDEGZSFZOQDEABCIJPCDEKTUAUBHZSHUCRUDSABDEKLUAUBSIMN $.

  $( Equivalence inside and outside of a substitution are equivalent.
     (Contributed by NM, 14-May-1993.) $)
  sbbi $p |- ( [ y / x ] ( ph <-> ps )
     <-> ( [ y / x ] ph <-> [ y / x ] ps ) ) $=
    ( wb wsb wi wa dfbi2 sbbii sbim anbi12i sban 3bitr4i bitri ) ABEZCDFABGZBAG
    ZHZCDFZACDFZBCDFZEZPSCDABIJQCDFZRCDFZHUAUBGZUBUAGZHTUCUDUFUEUGABCDKBACDKLQR
    CDMUAUBINO $.

  $( Specialization of biconditional.  (Contributed by NM, 2-Jun-1993.) $)
  spsbbi $p |- ( A. x ( ph <-> ps ) -> ( [ y / x ] ph <-> [ y / x ] ps ) ) $=
    ( wb wal wsb stdpc4 sbbi sylib ) ABEZCFKCDGACDGBCDGEKCDHABCDIJ $.

  ${
    sbbid.1 $e |- F/ x ph $.
    sbbid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction substituting both sides of a biconditional.  (Contributed by
       NM, 30-Jun-1993.) $)
    sbbid $p |- ( ph -> ( [ y / x ] ps <-> [ y / x ] ch ) ) $=
      ( wb wal wsb alrimi spsbbi syl ) ABCHZDIBDEJCDEJHANDFGKBCDELM $.
  $}

  ${
    sblbis.1 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Introduce left biconditional inside of a substitution.  (Contributed by
       NM, 19-Aug-1993.) $)
    sblbis $p |- ( [ y / x ] ( ch <-> ph ) <-> ( [ y / x ] ch <-> ps ) ) $=
      ( wb wsb sbbi bibi2i bitri ) CAGDEHCDEHZADEHZGLBGCADEIMBLFJK $.
  $}

  ${
    sbrbis.1 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Introduce right biconditional inside of a substitution.  (Contributed by
       NM, 18-Aug-1993.) $)
    sbrbis $p |- ( [ y / x ] ( ph <-> ch ) <-> ( ps <-> [ y / x ] ch ) ) $=
      ( wb wsb sbbi bibi1i bitri ) ACGDEHADEHZCDEHZGBMGACDEILBMFJK $.
  $}

  ${
    sbrbif.1 $e |- F/ x ch $.
    sbrbif.2 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Introduce right biconditional inside of a substitution.  (Contributed by
       NM, 18-Aug-1993.)  (Revised by Mario Carneiro, 4-Oct-2016.) $)
    sbrbif $p |- ( [ y / x ] ( ph <-> ch ) <-> ( ps <-> ch ) ) $=
      ( wb wsb sbrbis sbf bibi2i bitri ) ACHDEIBCDEIZHBCHABCDEGJNCBCDEFKLM $.
  $}

  $( Alternate proof of ~ sbequ8 , shorter but requiring more axioms.
     (Contributed by NM, 5-Aug-1993.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  sbequ8ALT $p |- ( [ y / x ] ph <-> [ y / x ] ( x = y -> ph ) ) $=
    ( wsb weq wi equsb1 a1bi sbim bitr4i ) ABCDZBCEZBCDZKFLAFBCDMKBCGHLABCIJ $.

  ${
    sbie.1 $e |- F/ x ps $.
    sbie.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Conversion of implicit substitution to explicit substitution.
       (Contributed by NM, 30-Jun-1994.)  (Revised by Mario Carneiro,
       4-Oct-2016.)  (Proof shortened by Wolf Lammen, 13-Jul-2019.) $)
    sbie $p |- ( [ y / x ] ph <-> ps ) $=
      ( wb wsb weq equsb1 sbimi ax-mp sbf sblbis mpbi ) ABGZCDHZACDHBGCDIZCDHQC
      DJRPCDFKLBBACDBCDEMNO $.
    $( Obsolete proof of ~ sbie as of 13-Jul-2019.  (Contributed by NM,
       30-Jun-1994.)  (Revised by Mario Carneiro, 4-Oct-2016.)  (Revised by
       Wolf Lammen, 16-Sep-2018.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    sbieOLD $p |- ( [ y / x ] ph <-> ps ) $=
      ( wsb wb weq equsb1 sbimi ax-mp sbbi mpbi sbf bitri ) ACDGZBCDGZBABHZCDGZ
      QRHCDIZCDGTCDJUASCDFKLABCDMNBCDEOP $.
  $}

  ${
    sbied.1 $e |- F/ x ph $.
    sbied.2 $e |- ( ph -> F/ x ch ) $.
    sbied.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Conversion of implicit substitution to explicit substitution (deduction
       version of ~ sbie ).  (Contributed by NM, 30-Jun-1994.)  (Revised by
       Mario Carneiro, 4-Oct-2016.)  (Proof shortened by Wolf Lammen,
       24-Jun-2018.) $)
    sbied $p |- ( ph -> ( [ y / x ] ps <-> ch ) ) $=
      ( wsb wi sbrim nfim1 weq wb com12 pm5.74d sbie bitr3i pm5.74ri ) ABDEIZCA
      TJABJZDEIACJZABDEFKUAUBDEACDFGLDEMZABCAUCBCNHOPQRS $.
  $}

  ${
    $d x ph $.  $d x ch $.
    sbiedv.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Conversion of implicit substitution to explicit substitution (deduction
       version of ~ sbie ).  (Contributed by NM, 7-Jan-2017.) $)
    sbiedv $p |- ( ph -> ( [ y / x ] ps <-> ch ) ) $=
      ( nfv nfvd weq wb ex sbied ) ABCDEADGACDHADEIBCJFKL $.
  $}

  $( Substituting ` y ` for ` x ` and then ` z ` for ` y ` is equivalent to
     substituting ` z ` for both ` x ` and ` y ` .  (Contributed by Giovanni
     Mascellani, 8-Apr-2018.)  Remove dependency on ~ ax-11 .  (Revised by Wolf
     Lammen, 16-Sep-2018.)  (Proof shortened by Wolf Lammen, 16-Sep-2018.) $)
  sbcom3 $p |- ( [ z / y ] [ y / x ] ph <-> [ z / y ] [ z / x ] ph ) $=
    ( weq wal wsb wb nfa1 drsb2 sbbid wn sb4b sbequ pm5.74i albii syl6bb bitr4d
    wi pm2.61i ) CDEZCFZABCGZCDGZABDGZCDGZHUBUCUECDUACIACDBJKUBLZUDUAUESZCFZUFU
    GUDUAUCSZCFUIUCCDMUJUHCUAUCUEACDBNOPQUECDMRT $.

  $( A composition law for substitution.  (Contributed by NM, 14-May-1993.)
     (Proof shortened by Wolf Lammen, 21-Sep-2018.) $)
  sbco $p |- ( [ y / x ] [ x / y ] ph <-> [ y / x ] ph ) $=
    ( wsb sbcom3 sbid sbbii bitri ) ACBDBCDACCDZBCDABCDACBCEIABCACFGH $.

  ${
    sbid2.1 $e |- F/ x ph $.
    $( An identity law for substitution.  (Contributed by NM, 14-May-1993.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
    sbid2 $p |- ( [ y / x ] [ x / y ] ph <-> ph ) $=
      ( wsb sbco sbf bitri ) ACBEBCEABCEAABCFABCDGH $.
  $}

  $( An idempotent law for substitution.  (Contributed by NM, 30-Jun-1994.)
     (Proof shortened by Andrew Salmon, 25-May-2011.)  (Proof shortened by Wolf
     Lammen, 13-Jul-2019.) $)
  sbidm $p |- ( [ y / x ] [ y / x ] ph <-> [ y / x ] ph ) $=
    ( wsb sbcom3 sbid sbbii bitr3i ) ABCDZBCDABBDZBCDIABBCEJABCABFGH $.

  $( Obsolete proof of ~ sbidm as of 13-Jul-2019.  (Contributed by NM,
     30-Jun-1994.)  (Proof shortened by Andrew Salmon, 25-May-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  sbidmOLD $p |- ( [ y / x ] [ y / x ] ph <-> [ y / x ] ph ) $=
    ( wsb wb weq equsb2 sbequ12r sbimi ax-mp sbbi mpbi ) ABCDZAEZBCDZMBCDMECBFZ
    BCDOBCGPNBCACBHIJMABCKL $.

  ${
    sbco2.1 $e |- F/ z ph $.
    $( A composition law for substitution.  (Contributed by NM, 30-Jun-1994.)
       (Revised by Mario Carneiro, 6-Oct-2016.)  (Proof shortened by Wolf
       Lammen, 17-Sep-2018.) $)
    sbco2 $p |- ( [ y / z ] [ z / x ] ph <-> [ y / x ] ph ) $=
      ( weq wal wsb wb sbequ12 sbequ bitr3d sps wn nfnae nfsb4 wi sbied pm2.61i
      a1i ) DCFZDGZABDHZDCHZABCHZIZUAUFDUAUCUDUEUCDCJADCBKZLMUBNZUCUEDCDCDOABCD
      EPUAUCUEIQUHUGTRS $.
  $}

  ${
    sbco2d.1 $e |- F/ x ph $.
    sbco2d.2 $e |- F/ z ph $.
    sbco2d.3 $e |- ( ph -> F/ z ps ) $.
    $( A composition law for substitution.  (Contributed by NM, 2-Jun-1993.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
    sbco2d $p |- ( ph -> ( [ y / z ] [ z / x ] ps <-> [ y / x ] ps ) ) $=
      ( wsb wi nfim1 sbco2 sbrim sbbii bitri 3bitr3i pm5.74ri ) ABCEIZEDIZBCDIZ
      ABJZCEIZEDIZUACDIASJZATJUACDEABEGHKLUCARJZEDIUDUBUEEDABCEFMNAREDGMOABCDFM
      PQ $.
  $}

  $( A composition law for substitution.  (Contributed by NM, 2-Jun-1993.)
     (Proof shortened by Wolf Lammen, 18-Sep-2018.) $)
  sbco3 $p |- ( [ z / y ] [ y / x ] ph <-> [ z / x ] [ x / y ] ph ) $=
    ( weq wal wsb wb drsb1 nfae sbequ12a sbbid bitr3d wn sbco sbbii nfnae nfsb2
    sps sbco2d syl5rbbr pm2.61i ) BCEZBFZABCGZCDGZACBGZBDGZHUDUEBDGUFUHUEBCDIUD
    UEUGBDBCBJUCUEUGHBABCKSLMUHUECBGZBDGUDNZUFUIUGBDACBOPUJUECDBBCCQBCBQABCRTUA
    UB $.

  $( A commutativity law for substitution.  (Contributed by NM, 27-May-1997.)
     (Proof shortened by Wolf Lammen, 20-Sep-2018.) $)
  sbcom $p |- ( [ y / z ] [ y / x ] ph <-> [ y / x ] [ y / z ] ph ) $=
    ( wsb sbco3 sbcom3 3bitr3i ) ABDEDCEADBEBCEABCEDCEADCEBCEABDCFABDCGADBCGH
    $.

  ${
    sbt.1 $e |- ph $.
    $( A substitution into a theorem yields a theorem.  (See ~ chvar and
       ~ chvarv for versions using implicit substitution.)  (Contributed by NM,
       21-Jan-2004.)  (Proof shortened by Andrew Salmon, 25-May-2011.)  (Proof
       shortened by Wolf Lammen, 20-Jul-2018.) $)
    sbt $p |- [ y / x ] ph $=
      ( wsb stdpc4 mpg ) AABCEBABCFDG $.
  $}

  ${
    sbtrt.nf $e |- F/ y ph $.
    $( Partially closed form of ~ sbtr .  (Contributed by BJ, 4-Jun-2019.) $)
    sbtrt $p |- ( A. y [ y / x ] ph -> ph ) $=
      ( wsb wal stdpc4 sbid2 sylib ) ABCEZCFJCBEAJCBGACBDHI $.
  $}

  ${
    sbtr.nf $e |- F/ y ph $.
    sbtr.1 $e |- [ y / x ] ph $.
    $( A partial converse to ~ sbt .  If the substitution of a variable for a
       non-free one in a wff gives a theorem, then the original wff is a
       theorem.  (Contributed by BJ, 15-Sep-2018.) $)
    sbtr $p |- ph $=
      ( wsb sbtrt mpg ) ABCFACABCDGEH $.
  $}

  ${
    sb5rf.1 $e |- F/ y ph $.
    $( Reversed substitution.  (Contributed by NM, 3-Feb-2005.)  (Revised by
       Mario Carneiro, 6-Oct-2016.)  (Proof shortened by Wolf Lammen,
       20-Sep-2018.) $)
    sb5rf $p |- ( ph <-> E. y ( y = x /\ [ y / x ] ph ) ) $=
      ( weq wsb wa wex sbequ12r equsex bicomi ) CBEABCFZGCHALACBDACBIJK $.

    $( Reversed substitution.  (Contributed by NM, 1-Aug-1993.)  (Revised by
       Mario Carneiro, 6-Oct-2016.)  (Proof shortened by Wolf Lammen,
       21-Sep-2018.) $)
    sb6rf $p |- ( ph <-> A. y ( y = x -> [ y / x ] ph ) ) $=
      ( weq wsb wi wal sbequ12r equsal bicomi ) CBEABCFZGCHALACBDACBIJK $.

    $( Substitution of variable in universal quantifier.  (Contributed by NM,
       16-May-1993.)  (Revised by Mario Carneiro, 6-Oct-2016.)  (Proof
       shortened by Jim Kingdon, 15-Jan-2018.) $)
    sb8 $p |- ( A. x ph <-> A. y [ y / x ] ph ) $=
      ( wsb nfs1 sbequ12 cbval ) AABCEBCDABCDFABCGH $.

    $( Substitution of variable in existential quantifier.  (Contributed by NM,
       12-Aug-1993.)  (Revised by Mario Carneiro, 6-Oct-2016.)  (Proof
       shortened by Jim Kingdon, 15-Jan-2018.) $)
    sb8e $p |- ( E. x ph <-> E. y [ y / x ] ph ) $=
      ( wsb nfs1 sbequ12 cbvex ) AABCEBCDABCDFABCGH $.
  $}

  $( Commutation of quantification and substitution variables.  (Contributed by
     NM, 5-Aug-1993.)  Allow a shortening of ~ sb9i .  (Revised by Wolf Lammen,
     15-Jun-2019.) $)
  sb9 $p |- ( A. x [ x / y ] ph <-> A. y [ y / x ] ph ) $=
    ( weq wal wsb wb sbequ12a equcoms sps dral1 wn nfnae wnf nfsb2 naecoms cbv2
    wi a1i pm2.61i ) BCDZBEZACBFZBEABCFZCEGUCUDBCUAUCUDGZBUECBACBHIZJKUBLZUCUDB
    CBCBMBCCMUCCNCBACBOPABCOUAUERUGUFSQT $.

  $( Commutation of quantification and substitution variables.  (Contributed by
     NM, 5-Aug-1993.)  (Proof shortened by Wolf Lammen, 15-Jun-2019.) $)
  sb9i $p |- ( A. x [ x / y ] ph -> A. y [ y / x ] ph ) $=
    ( wsb wal sb9 biimpi ) ACBDBEABCDCEABCFG $.

  ${
    $d x y $.
    $( Alternative proof of ~ ax12v , shorter, but depending on more axioms.
       (Contributed by NM, 5-Aug-1993.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    ax12vALT $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      ( weq wal wi ax-1 axc16 syl5 a1d axc15 pm2.61i ) BCDZBEZMAMAFZBEZFZFNQMAO
      NPAMGOBCHIJABCKL $.
  $}

  ${
    $d x y $.
    $( Two equivalent ways of expressing the proper substitution of ` y ` for
       ` x ` in ` ph ` , when ` x ` and ` y ` are distinct.  Theorem 6.2 of
       [Quine] p. 40.  The proof does not involve ~ df-sb .  The implication
       ""to the left"" is ~ equs4 and does not require any dv condition.  Theorem
       ~ equs45f replaces the dv condition with a non-freeness hypothesis.
       (Contributed by NM, 14-Apr-2008.) $)
    sb56 $p |- ( E. x ( x = y /\ ph ) <-> A. x ( x = y -> ph ) ) $=
      ( weq wi wal nfa1 ax12v sp com12 impbid equsex ) ABCDZAEZBFZBCNBGMAOABCHO
      MANBIJKL $.
  $}

  ${
    $d x y $.
    $( Equivalence for substitution.  Compare Theorem 6.2 of [Quine] p. 40.
       Also proved as Lemmas 16 and 17 of [Tarski] p. 70.  The implication ""to
       the left"" is ~ sb2 and does not require any dv condition.  Theorem
       ~ sb6f replaces the dv condition with a non-freeness hypothesis.
       (Contributed by NM, 18-Aug-1993.)  (Proof shortened by Wolf Lammen,
       21-Sep-2018.) $)
    sb6 $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $=
      ( wsb weq wi wal wa wex sb1 sb56 sylib sb2 impbii ) ABCDZBCEZAFBGZOPAHBIQ
      ABCJABCKLABCMN $.
  $}

  ${
    $d x y $.
    $( Equivalence for substitution.  Similar to Theorem 6.1 of [Quine] p. 40.
       The implication ""to the right"" is ~ sb1 and does not require any dv
       condition.  Theorem ~ sb5f replaces the dv condition with a non-freeness
       hypothesis.  (Contributed by NM, 18-Aug-1993.) $)
    sb5 $p |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) ) $=
      ( wsb weq wi wal wa wex sb6 sb56 bitr4i ) ABCDBCEZAFBGMAHBIABCJABCKL $.
  $}

  ${
    $d y z $.  $d x y $.
    $( Lemma for ~ equsb3 .  (Contributed by Raph Levien and FL, 4-Dec-2005.)
       (Proof shortened by Andrew Salmon, 14-Jun-2011.) $)
    equsb3lem $p |- ( [ x / y ] y = z <-> x = z ) $=
      ( weq nfv equequ1 sbie ) BCDACDZBAHBEBACFG $.
  $}

  ${
    $d y w z $.  $d x w $.
    $( Substitution applied to an atomic wff.  (Contributed by Raph Levien and
       FL, 4-Dec-2005.)  Remove dependency on ~ ax-11 .  (Revised by Wolf
       Lammen, 21-Sep-2018.) $)
    equsb3 $p |- ( [ x / y ] y = z <-> x = z ) $=
      ( vw weq wsb equsb3lem sbbii sbcom3 nfv sbf bitri 3bitr3i ) BCEZBDFZDAFZD
      CEZDAFNBAFZACEOQDADBCGHPRDAFRNBDAIRDARDJKLADCGM $.
  $}

  ${
    $d w y z $.  $d w x $.
    $( Alternate proof of ~ eqsb3 , shorter but requiring ~ ax-11 .
       (Contributed by Raph Levien and FL, 4-Dec-2005.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    equsb3ALT $p |- ( [ x / y ] y = z <-> x = z ) $=
      ( vw weq wsb equsb3lem sbbii nfv sbco2 3bitr3i ) BCEZBDFZDAFDCEZDAFLBAFAC
      EMNDADBCGHLBADLDIJADCGK $.
  $}

  ${
    $d w y z $.  $d w x $.
    $( Substitution applied to an atomic membership wff.  (Contributed by NM,
       7-Nov-2006.)  (Proof shortened by Andrew Salmon, 14-Jun-2011.) $)
    elsb3 $p |- ( [ x / y ] y e. z <-> x e. z ) $=
      ( vw wel wsb nfv sbco2 elequ1 sbie sbbii 3bitr3i ) DCEZDBFZBAFMDAFBCEZBAF
      ACEZMDABMBGHNOBAMODBODGDBCIJKMPDAPDGDACIJL $.
  $}

  ${
    $d w y z $.  $d w x $.
    $( Substitution applied to an atomic membership wff.  (Contributed by
       Rodolfo Medina, 3-Apr-2010.)  (Proof shortened by Andrew Salmon,
       14-Jun-2011.) $)
    elsb4 $p |- ( [ x / y ] z e. y <-> z e. x ) $=
      ( vw wel wsb nfv sbco2 elequ2 sbie sbbii 3bitr3i ) CDEZDBFZBAFMDAFCBEZBAF
      CAEZMDABMBGHNOBAMODBODGDBCIJKMPDAPDGDACIJL $.
  $}

  ${
    $d x y $.
    $( ` x ` is not free in ` [ y / x ] ph ` when ` x ` and ` y ` are
       distinct.  (Contributed by NM, 26-May-1993.) $)
    hbs1 $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $=
      ( weq wal wsb wi axc16 hbsb2 pm2.61i ) BCDBEABCFZKBEGKBCHABCIJ $.

    $( ` x ` is not free in ` [ y / x ] ph ` when ` x ` and ` y ` are
       distinct.  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfs1v $p |- F/ x [ y / x ] ph $=
      ( wsb hbs1 nfi ) ABCDBABCEF $.
  $}

  ${
    $d y ph $.
    $( Two ways of expressing "" ` x ` is (effectively) not free in ` ph ` .""
       (Contributed by NM, 29-May-2009.) $)
    sbhb $p |- ( ( ph -> A. x ph ) <-> A. y ( ph -> [ y / x ] ph ) ) $=
      ( wal wi wsb nfv sb8 imbi2i 19.21v bitr4i ) AABDZEAABCFZCDZEAMECDLNAABCAC
      GHIAMCJK $.
  $}

  ${
    $d x y z $.  $d y z ph $.
    $( Two ways of expressing "" ` x ` is (effectively) not free in ` ph ` .""
       (Contributed by G&eacute;rard Lang, 14-Nov-2013.)  (Revised by Mario
       Carneiro, 6-Oct-2016.)  (Proof shortened by Wolf Lammen,
       22-Sep-2018.) $)
    sbnf2 $p |- ( F/ x ph
       <-> A. y A. z ( [ y / x ] ph <-> [ z / x ] ph ) ) $=
      ( wnf wa wsb wi wal wb wex nfv sb8e sb8 imbi12i nf2 pm11.53v bitr4i alcom
      3bitr4i 3bitri anbi12i pm4.24 2albiim ) ABEZUEFABCGZABDGZHDICIZUGUFHZDICI
      ZFUEUFUGJDICIUEUHUEUJABKZABIZHZUFCKZUGDIZHUEUHUKUNULUOABCACLZMABDADLZNOAB
      PZUFUGCDQTUEUMUICIDIZUJURUMUGDKZUFCIZHUSUKUTULVAABDUQMABCUPNOUGUFDCQRUIDC
      SUAUBUEUCUFUGCDUDT $.
  $}

  ${
    $d y z $.
    nfsb.1 $e |- F/ z ph $.
    $( If ` z ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` when
       ` y ` and ` z ` are distinct.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nfsb $p |- F/ z [ y / x ] ph $=
      ( weq wal wsb wnf ax16nf nfsb4 pm2.61i ) DCFDGABCHZDIMDCDJABCDEKL $.
  $}

  ${
    $d y z $.
    hbsb.1 $e |- ( ph -> A. z ph ) $.
    $( If ` z ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` when
       ` y ` and ` z ` are distinct.  (Contributed by NM, 12-Aug-1993.) $)
    hbsb $p |- ( [ y / x ] ph -> A. z [ y / x ] ph ) $=
      ( wsb nfi nfsb nfri ) ABCFDABCDADEGHI $.
  $}

  ${
    $d y z $.
    nfsbd.1 $e |- F/ x ph $.
    nfsbd.2 $e |- ( ph -> F/ z ps ) $.
    $( Deduction version of ~ nfsb .  (Contributed by NM, 15-Feb-2013.) $)
    nfsbd $p |- ( ph -> F/ z [ y / x ] ps ) $=
      ( weq wal wsb wnf wn wi alrimi nfsb4t syl ax16nf pm2.61d2 ) AEDHEIZBCDJZE
      KZABEKZCISLUAMAUBCFGNBCDEOPTEDEQR $.
  $}

  ${
    $d x y z $.  $d w y $.
    $( Equivalence for double substitution.  (Contributed by NM,
       3-Feb-2005.) $)
    2sb5 $p |- ( [ z / x ] [ w / y ] ph <->
               E. x E. y ( ( x = z /\ y = w ) /\ ph ) ) $=
      ( wsb weq wa wex sb5 19.42v anass exbii anbi2i 3bitr4ri bitri ) ACEFZBDFB
      DGZQHZBIRCEGZHAHZCIZBIQBDJSUBBRTAHZHZCIRUCCIZHUBSRUCCKUAUDCRTALMQUERACEJN
      OMP $.

    $( Equivalence for double substitution.  (Contributed by NM,
       3-Feb-2005.) $)
    2sb6 $p |- ( [ z / x ] [ w / y ] ph <->
               A. x A. y ( ( x = z /\ y = w ) -> ph ) ) $=
      ( wsb weq wi wal wa sb6 19.21v impexp albii imbi2i 3bitr4ri bitri ) ACEFZ
      BDFBDGZRHZBISCEGZJAHZCIZBIRBDKTUCBSUAAHZHZCISUDCIZHUCTSUDCLUBUECSUAAMNRUF
      SACEKOPNQ $.
  $}
${
    $d x z $.  $d u v x w $.  $d u v y z $.  $d u v ph $.
    $( Commutativity law for substitution.  Used in proof of Theorem 9.7 of
       [Megill] p. 449 (p. 16 of the preprint).  (Contributed by NM,
       27-May-1997.)  (Proof shortened by Wolf Lammen, 24-Sep-2018.) $)
    sbcom2 $p |- ( [ w / z ] [ y / x ] ph <-> [ y / x ] [ w / z ] ph ) $=
      ( vu vv weq wex wsb wb ax6ev wi wa wal 2sb6 alcom nfv sbequ sbbid ancomst
      2albii 3bitri bitr4i syl5bbr sylan9bb sylan9bbr bitr3d ex exlimdv exlimiv
      mp2 ) FCHZFIGEHZGIZABCJZDEJZADEJZBCJZKZFCLGELUMUOUTMFUMUNUTGUMUNUTUMUNNAD
      GJZBFJZUQUSUMVBUPDGJZUNUQVBABFJZDGJZUMVCVEBFHZDGHZNAMZDOBOZVBVEVGVFNAMZBO
      DOVJDOBOVIADBGFPVJDBQVJVHBDVGVFAUAUBUCABDFGPUDUMVDUPDGUMDRAFCBSTUEUPGEDSU
      FUNVBURBFJUMUSUNVAURBFUNBRAGEDSTURFCBSUGUHUIUJUKUL $.
  $}
${
    $d ph x y z $.  $d w x z $.
    $( Commutativity law for substitution.  This theorem was incorrectly used
       as our previous version of ~ pm11.07 but may still be useful.
       (Contributed by Andrew Salmon, 17-Jun-2011.)  (Proof shortened by Jim
       Kingdon, 22-Jan-2018.) $)
    sbcom4 $p |- ( [ w / x ] [ y / z ] ph <-> [ y / x ] [ w / z ] ph ) $=
      ( wsb nfv sbf sbbii bitri 3bitr4i ) ABEFAADCFZBEFADEFZBCFZABEABGZHLABEADC
      ADGZHINABCFAMABCADEPHIABCOHJK $.
  $}

  ${
    pm11.07.1 $e |- ph $.
    $( Axiom *11.07 in [WhiteheadRussell] p. 159.  The original reads: *11.07
       ""Whatever possible argument ` x ` may be, ` ph ( x , y ) ` is true
       whatever possible argument ` y ` may be"" implies the corresponding
       statement with ` x ` and ` y ` interchanged except
       in "" ` ph ( x , y ) ` "".  Under our formalism this appears to correspond
       to ~ idi and not to ~ sbcom4 as earlier thought.  See
       ~ https://groups.google.com/d/msg/metamath/iS0fOvSemC8/M1zTH8wxCAAJ .
       (Contributed by BJ, 16-Sep-2018.)  (New usage is discouraged.) $)
    pm11.07 $p |- ph $=
      ( a1i ) B $.
  $} 
  ${
    $d x y $.
    $( Equivalence for substitution.  (Contributed by NM, 2-Jun-1993.)  (Proof
       shortened by Wolf Lammen, 23-Sep-2018.) $)
    sb6a $p |- ( [ y / x ] ph <-> A. x ( x = y -> [ x / y ] ph ) ) $=
      ( wsb weq wi wal sbco sb6 bitr3i ) ABCDACBDZBCDBCEKFBGABCHKBCIJ $.
  $}

  $( We can always find values matching ` x ` and ` y ` , as long as they are
     represented by distinct variables.  This theorem merges two ~ ax6e
     instances ` E. z z = x ` and ` E. w w = y ` into a common expression.
     Alan Sare contributed a variant of this theorem with distinct variable
     conditions before, see ~ax6e2nd .  (Contributed by Wolf Lammen,
     27-Sep-2018.) $)
  2ax6elem $p |- ( -. A. w w = z -> E. z E. w ( z = x /\ w = y ) ) $=
    ( weq wal wn wex ax6e nfnae nfan nfeqf pm3.21 spimed eximd mpi nfae equvini
    wa ex equtrr anim1d aleximi syl5 pm2.61d2 ) DCEDFGZDAEZDFZCAEZDBEZSZDHZCHZU
    FUHGZUMUFUNSZUICHUMCAIUOUIULCUFUNCDCCJDACJKUIUKUODBCADLUJUIMNOPTUHCBEZCHUMC
    BIUHUPULCDACQUPCDEZUJSZDHUHULCBDRUGURUKDUGUQUIUJDACUAUBUCUDOPUE $.

  ${
    $d w z $.
    $( We can always find values matching ` x ` and ` y ` , as long as they are
       represented by distinct variables.  Version of ~ 2ax6elem with a
       distinct variable constraint.  (Contributed by Wolf Lammen,
       28-Sep-2018.) $)
    2ax6e $p |- E. z E. w ( z = x /\ w = y ) $=
      ( weq wal wa wex aev 19.21bi jca 19.8a 3syl 2ax6elem pm2.61i ) DCEDFZCAEZ
      DBEZGZDHZCHZPSTUAPQRPQCDCCCAIJPRDDCDDBIJKSDLTCLMABCDNO $.
  $}

  ${
    $d w z $.
    2sb5rf.1 $e |- F/ z ph $.
    2sb5rf.2 $e |- F/ w ph $.
    $( Reversed double substitution.  (Contributed by NM, 3-Feb-2005.)
       (Revised by Mario Carneiro, 6-Oct-2016.)  Remove distinct variable
       constraints.  (Revised by Wolf Lammen, 28-Sep-2018.) $)
    2sb5rf $p |- ( ph <->
                E. z E. w ( ( z = x /\ w = y ) /\ [ z / x ] [ w / y ] ph ) ) $=
      ( weq wa wex wsb 19.41 exbii bitri sbequ12r sylan9bb pm5.32i 2exbii 2ax6e
      biantrur 3bitr4ri ) DBHZECHZIZAIZEJZDJZUDEJZDJZAIZUDACEKZBDKZIZEJDJAUGUHA
      IZDJUJUFUNDUDAEGLMUHADFLNUMUEDEUDULAUBULUKUCAUKDBOAECOPQRUIABCDESTUA $.

    $( Reversed double substitution.  (Contributed by NM, 3-Feb-2005.)
       (Revised by Mario Carneiro, 6-Oct-2016.)  Remove variable constraints.
       (Revised by Wolf Lammen, 28-Sep-2018.) $)
    2sb6rf $p |- ( ph <->
                A. z A. w ( ( z = x /\ w = y ) -> [ z / x ] [ w / y ] ph ) ) $=
      ( weq wa wsb wal wex sbequ12r sylan9bb pm5.74i 2albii 19.23 albii bitri
      wi wb 2ax6e pm5.5 ax-mp 3bitrri ) DBHZECHZIZACEJZBDJZTZEKDKUHATZEKZDKZUHE
      LZDLZATZAUKULDEUHUJAUFUJUIUGAUIDBMAECMNOPUNUOATZDKUQUMURDUHAEGQRUOADFQSUP
      UQAUABCDEUBUPAUCUDUE $.
  $}

  ${
    $d y z $.
    sb7f.1 $e |- F/ z ph $.
    $( This version of ~ dfsb7 does not require that ` ph ` and ` z ` be
       distinct.  This permits it to be used as a definition for substitution
       in a formalization that omits the logically redundant axiom ~ ax-5 i.e.
       that doesn't have the concept of a variable not occurring in a wff.
       ( ~ df-sb is also suitable, but its mixing of free and bound variables
       is distasteful to some logicians.)  (Contributed by NM, 26-Jul-2006.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
    sb7f $p |- ( [ y / x ] ph <->
               E. z ( z = y /\ E. x ( x = z /\ ph ) ) ) $=
      ( wsb cv wceq wa wex sb5f sbbii sbco2 sb5 3bitr3i ) ABDFZDCFBGDGZHAIBJZDC
      FABCFQCGHRIDJPRDCABDEKLABCDEMRDCNO $.
  $}

  ${
    $d y z $.
    sb7h.1 $e |- ( ph -> A. z ph ) $.
    $( This version of ~ dfsb7 does not require that ` ph ` and ` z ` be
       distinct.  This permits it to be used as a definition for substitution
       in a formalization that omits the logically redundant axiom ~ ax-5 i.e.
       that doesn't have the concept of a variable not occurring in a wff.
       ( ~ df-sb is also suitable, but its mixing of free and bound variables
       is distasteful to some logicians.)  (Contributed by NM, 26-Jul-2006.)
       (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    sb7h $p |- ( [ y / x ] ph <->
               E. z ( z = y /\ E. x ( x = z /\ ph ) ) ) $=
      ( nfi sb7f ) ABCDADEFG $.
  $}

  ${
    $d y z $.  $d z ph $.
    $( An alternate definition of proper substitution ~ df-sb .  By introducing
       a dummy variable ` z ` in the definiens, we are able to eliminate any
       distinct variable restrictions among the variables ` x ` , ` y ` , and
       ` ph ` of the definiendum.  No distinct variable conflicts arise because
       ` z ` effectively insulates ` x ` from ` y ` .  To achieve this, we use
       a chain of two substitutions in the form of ~ sb5 , first ` z ` for
       ` x ` then ` y ` for ` z ` .  Compare Definition 2.1'' of [Quine] p. 17,
       which is obtained from this theorem by applying ~ df-clab .  Theorem
       ~ sb7h provides a version where ` ph ` and ` z ` don't have to be
       distinct.  (Contributed by NM, 28-Jan-2004.) $)
    dfsb7 $p |- ( [ y / x ] ph <-> E. z ( z = y /\ E. x ( x = z /\ ph ) ) ) $=
      ( nfv sb7f ) ABCDADEF $.
  $}

  ${
    $d x y $.
    sb10f.1 $e |- F/ x ph $.
    $( Hao Wang's identity axiom P6 in Irving Copi, _Symbolic Logic_ (5th ed.,
       1979), p. 328.  In traditional predicate calculus, this is a sole axiom
       for identity from which the usual ones can be derived.  (Contributed by
       NM, 9-May-2005.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)
    sb10f $p |- ( [ y / z ] ph <-> E. x ( x = y /\ [ x / z ] ph ) ) $=
      ( weq wsb wa wex nfsb sbequ equsex bicomi ) BCFADBGZHBIADCGZNOBCADCBEJABC
      DKLM $.
  $}

  ${
    $d x ph $.
    $( An identity law for substitution.  Used in proof of Theorem 9.7 of
       [Megill] p. 449 (p. 16 of the preprint).  (Contributed by NM,
       5-Aug-1993.) $)
    sbid2v $p |- ( [ y / x ] [ x / y ] ph <-> ph ) $=
      ( nfv sbid2 ) ABCABDE $.
  $}

  ${
    $d x y $.  $d x ph $.
    $( Elimination of substitution.  (Contributed by NM, 5-Aug-1993.) $)
    sbelx $p |- ( ph <-> E. x ( x = y /\ [ x / y ] ph ) ) $=
      ( wsb weq wa wex sbid2v sb5 bitr3i ) AACBDZBCDBCEKFBGABCHKBCIJ $.
  $}

  ${
    $d x y ph $.
    $( Elimination of double substitution.  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by Wolf Lammen, 29-Sep-2018.) $)
    sbel2x $p |- ( ph <-> E. x E. y ( ( x = z /\ y = w ) /\
                     [ y / w ] [ x / z ] ph ) ) $=
      ( weq wa wsb wex nfv 2sb5rf ancom anbi1i 2exbii excom 3bitri ) ACEFZBDFZG
      ZADBHECHZGZBICIRQGZTGZBICIUCCIBIAEDCBACJABJKUAUCCBSUBTQRLMNUCCBOP $.
  $}

  ${
    $d x y $.
    $( A theorem used in elimination of disjoint variable restriction on ` x `
       and ` y ` by replacing it with a distinctor ` -. A. x x = z ` .
       (Contributed by NM, 15-May-1993.)  (Proof shortened by Wolf Lammen,
       3-Oct-2018.) $)
    sbal1 $p |- ( -. A. x x = z ->
             ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) ) $=
      ( weq wal wn wsb wb wa wi sb4b nfnae wnf nfeqf2 19.21t bicomd sbequ12 sps
      albid syl sylan9bbr alcom syl6bb adantl bitr4d ex dral2 bitr3d pm2.61d2 )
      BDEBFGZCDEZCFZABFZCDHZACDHZBFZIZUKUMGZURUKUSJUOULAKZBFZCFZUQUSUOULUNKZCFU
      KVBUNCDLUKVCVACBDCMUKULBNZVCVAIBDCOVDVAVCULABPQUATUBUSUQVBIUKUSUQUTCFZBFV
      BUSUPVEBCDBMACDLTUTBCUCUDUEUFUGUMUNUOUQULUNUOICUNCDRSAUPCDBULAUPICACDRSUH
      UIUJ $.
  $}

  ${
    $d z x $.
    $( Move quantifier in and out of substitution.  (Contributed by NM,
       2-Jan-2002.)  Remove a distinct variable constraint.  (Revised by Wolf
       Lammen, 3-Oct-2018.) $)
    sbal2 $p |- ( -. A. x x = y ->
             ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) ) $=
      ( weq wal wn wsb wb wa wi sb4b adantl nfnae albid alcom wnf drsb2 syl5bbr
      sbid nfeqf1 19.21t syl syl5bb sylan9bbr bitr4d ex dral2 bitr3d pm2.61d2 )
      BCEBFGZCDEZCFZABFZCDHZACDHZBFZIZUKUMGZURUKUSJUOULUNKZCFZUQUSUOVAIUKUNCDLM
      USUQULAKZCFZBFZUKVAUSUPVCBCDBNACDLOVDVBBFZCFUKVAVBBCPUKVEUTCBCCNUKULBQVEU
      TIBCDUAULABUBUCOUDUEUFUGUMUNUOUQUNUNCCHUMUOUNCTUNCDCRSAUPCDBAACCHUMUPACTA
      CDCRSUHUIUJ $.
  $}

  ${
    $d x y $.  $d x z $.
    $( Move universal quantifier in and out of substitution.  (Contributed by
       NM, 16-May-1993.)  (Proof shortened by Wolf Lammen, 29-Sep-2018.) $)
    sbal $p |- ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) $=
      ( weq wal wsb wb nfae ax16gb sbbid bitr3d sbal1 pm2.61i ) BDEBFZABFZCDGZA
      CDGZBFZHORQSOAPCDBDCIABDBJKRBDBJLABCDMN $.
  $}

  ${
    $d x y $.  $d x z $.
    $( Move existential quantifier in and out of substitution.  (Contributed by
       NM, 27-Sep-2003.) $)
    sbex $p |- ( [ z / y ] E. x ph <-> E. x [ z / y ] ph ) $=
      ( wn wal wsb wex sbn sbal albii bitri xchbinx df-ex sbbii 3bitr4i ) AEZBF
      ZEZCDGZACDGZEZBFZEABHZCDGUABHTRCDGZUCRCDIUEQCDGZBFUCQBCDJUFUBBACDIKLMUDSC
      DABNOUABNP $.
  $}

  ${
    $d x z $.  $d y z $.
    sbalv.1 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Quantify with new variable inside substitution.  (Contributed by NM,
       18-Aug-1993.) $)
    sbalv $p |- ( [ y / x ] A. z ph <-> A. z ps ) $=
      ( wal wsb sbal albii bitri ) AEGCDHACDHZEGBEGAECDILBEFJK $.
  $}

  ${
    $d v w ph $.  $d v w x $.  $d v w y $.
    $( Lemma for ~ sbco4 .  It replaces the temporary variable ` v ` with
       another temporary variable ` w ` .  (Contributed by Jim Kingdon,
       26-Sep-2018.) $)
    sbco4lem $p |- ( [ x / v ] [ y / x ] [ v / y ] ph <->
        [ x / w ] [ y / x ] [ w / y ] ph ) $=
      ( wsb sbcom2 sbbii nfv sbco2 bitri sbid2v 3bitr3i ) ACDFZDEFZBCFZEDFZDBFZ
      OEDFZBCFZDBFACEFZBCFZEBFZNBCFZDBFQTDBOBCEDGHRUBEDFZDBFUCQUEDBPUBEDOUABCAC
      EDADIJHHHUBEBDUBDIJKTUDDBSNBCNEDLHHM $.
  $}

  ${
    $d t u v ph $.  $d t u v x $.  $d t u v y $.  $d w ph $.  $d w x $.
    $d w y $.  $d t w $.
    $( Two ways of exchanging two variables.  Both sides of the biconditional
       exchange ` x ` and ` y ` , either via two temporary variables ` u ` and
       ` v ` , or a single temporary ` w ` .  (Contributed by Jim Kingdon,
       25-Sep-2018.) $)
    sbco4 $p |- ( [ y / u ] [ x / v ] [ u / x ] [ v / y ] ph <->
        [ x / w ] [ y / x ] [ w / y ] ph ) $=
      ( vt wsb sbcom2 nfv sbco2 sbbii bitr3i sbco4lem 3bitri ) ACEHZBFHZEBHFCHZ
      PBCHZEBHZACGHBCHGBHACDHBCHDBHRQFCHZEBHTQFCEBIUASEBPBCFPFJKLMABCGENABCDGNO
      $.
  $}

  ${
    $d z w ph $.
    $( An equivalent expression for double existence.  (Contributed by Wolf
       Lammen, 2-Nov-2019.) $)
    2sb8e $p |- ( E. x E. y ph <->
                  E. z E. w [ z / x ] [ w / y ] ph ) $=
      ( wex wsb nfv sb8e exbii excom bitri nfsb 3bitri ) ACFZBFZACEGZBFZEFZQBDG
      ZDFZEFTEFDFPQEFZBFSOUBBACEAEHIJQBEKLRUAEQBDACEDADHMIJTEDKN $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( An equivalent expression for existence.  (Contributed by NM,
       2-Feb-2005.) $)
    exsb $p |- ( E. x ph <-> E. y A. x ( x = y -> ph ) ) $=
      ( weq wi wal nfv nfa1 ax12v sp com12 impbid cbvex ) ABCDZAEZBFZBCACGOBHNA
      PABCIPNAOBJKLM $.
  $}

  ${
    $d x y z $.  $d y w $.  $d z w ph $.
    $( An equivalent expression for double existence.  (Contributed by NM,
       2-Feb-2005.)  (Proof shortened by Wolf Lammen, 30-Sep-2018.) $)
    2exsb $p |- ( E. x E. y ph <->
                  E. z E. w A. x A. y ( ( x = z /\ y = w ) -> ph ) ) $=
      ( wex wsb weq wa wi wal 2sb8e 2sb6 2exbii bitri ) ACFBFACEGBDGZEFDFBDHCEH
      IAJCKBKZEFDFABCDELPQDEABCDEMNO $.
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Predicate calculus with equality:  Older axiomatization (1 rule, 14 schemes)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  The ""metalogical completeness theorem"", Theorem 9.7 of [Megill] p. 448, uses
  a different but (logically and metalogically) equivalent set of axiom schemes
  for its proof.  In order to show that our axiomatization is also
  metalogically complete, we derive the axiom schemes of that paper in this
  section (or mention where they are derived, if they have already been derived
  as theorems above).  Additionally, we re-derive our axiomatization from the
  one in the paper, showing that the two systems are equivalent.

  The 14 predicate calculus axioms used by the paper are ~ ax-c4 , ~ ax-c5 ,
  ~ ax-11 , ~ ax-c7 , ~ ax-7 , ~ ax-c9 , ~ ax-c10 , ~ ax-c11 , ~ ax-8 ,
  ~ ax-9 , ~ ax-c14 , ~ ax-c15 , ~ ax-c16 , and ~ ax-5 .  Like ours, it
  includes the rule of generalization ( ~ ax-gen ).

  The ones we need to prove from our axioms are ~ ax-c4 , ~ ax-c5 ,
  ~ ax-c7 , ~ ax-c9 , ~ ax-c10 , ~ ax-c11 , ~ ax-c14 , ~ ax-c15 ,
  and ~ ax-c16 . The theorems showing the derivations of those axioms,
  which have all been proved earlier, are ~ axc4 , ~ axc5 (also called
  ~ sp ), ~ axc7 , ~ axc9 , ~ axc10 , ~ axc11 , ~ axc14 , ~ axc15 ,
  ~ axc16 , and ~ axc11n . In addition, ~ ax-c11n was an intermediate axiom we
  adopted at one time, and we show its proof in this section as
  ~ axc11nfromc11 .

  This section also includes a few miscellaneous legacy theorems such as
  ~ hbequid use the older axioms.

  Note:  The axioms and theorems in this section should not be used outside of
  this section.  Inside this section, we may use the external axioms ~ ax-gen ,
  ~ ax-5 , ~ ax-7 , ~ ax-6 , ~ ax-8 , and ~ ax-9 since they are common to
  both our current and the older axiomatizations.  (These are the ones that
  were never revised.)

  The following newer axioms may NOT be used in this section until we
  have proved them from the older axioms:  ~ ax-4 , ~ ax-10 , ~ ax-6 ,
  ~ ax-12 , and ~ ax-13 .  However, once we have rederived an axiom
  (e.g. theorem ~ ax4 for axiom ~ ax-4 ), we may make use of theorems
  outside of this section that make use of the rederived axiom (e.g. we
  may use theorem ~ alimi , which uses ~ ax-4 , after proving ~ ax4 ).

$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
 Obsolete schemes ax-c4,c5,c7,c10,c11,c11n,c15,c9,c14,c16
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  These older axiom schemes are obsolete and should not be used outside of this
  section.  They are proved above as theorems axc4 , ~ sp , ~ axc7 , ~ axc10 ,
  ~ axc11 , ~ axc11n , ~ axc15 , ~ axc9 , ~ axc14 , and ~ axc16 .

$)

  $( Axiom of Specialization.  A quantified wff implies the wff without a
     quantifier (i.e. an instance, or special case, of the generalized wff).
     In other words if something is true for all ` x ` , it is true for any
     specific ` x ` (that would typically occur as a free variable in the wff
     substituted for ` ph ` ).  (A free variable is one that does not occur in
     the scope of a quantifier: ` x ` and ` y ` are both free in ` x = y ` ,
     but only ` x ` is free in ` A. y x = y ` .)  Axiom scheme C5' in [Megill]
     p. 448 (p. 16 of the preprint).  Also appears as Axiom B5 of [Tarski]
     p. 67 (under his system S2, defined in the last paragraph on p. 77).

     Note that the converse of this axiom does not hold in general, but a
     weaker inference form of the converse holds and is expressed as rule
     ~ ax-gen .  Conditional forms of the converse are given by ~ ax-13 ,
     ~ ax-c14 , ~ ax-c16 , and ~ ax-5 .

     Unlike the more general textbook Axiom of Specialization, we cannot choose
     a variable different from ` x ` for the special case.  For use, that
     requires the assistance of equality axioms, and we deal with it later
     after we introduce the definition of proper substitution - see ~ stdpc4 .

     An interesting alternate axiomatization uses ~ axc5c711 and ~ ax-c4 in
     place of ~ ax-c5 , ~ ax-4 , ~ ax-10 , and ~ ax-11 .

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ sp .  (Contributed by NM, 3-Jan-1993.)
     (New usage is discouraged.) $)
  ax-c5 $a |- ( A. x ph -> ph ) $.

  $( Axiom of Quantified Implication.  This axiom moves a quantifier from
     outside to inside an implication, quantifying ` ps ` .  Notice that ` x `
     must not be a free variable in the antecedent of the quantified
     implication, and we express this by binding ` ph ` to ""protect"" the axiom
     from a ` ph ` containing a free ` x ` .  Axiom scheme C4' in [Megill]
     p. 448 (p. 16 of the preprint).  It is a special case of Lemma 5 of
     [Monk2] p. 108 and Axiom 5 of [Mendelson] p. 69.

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ axc4 .  (Contributed by NM, 3-Jan-1993.)
     (New usage is discouraged.) $)
  ax-c4 $a |- ( A. x ( A. x ph -> ps ) -> ( A. x ph -> A. x ps ) ) $.

  $( Axiom of Quantified Negation.  This axiom is used to manipulate negated
     quantifiers.  Equivalent to axiom scheme C7' in [Megill] p. 448 (p. 16 of
     the preprint).  An alternate axiomatization could use ~ axc5c711 in place
     of ~ ax-c5 , ~ ax-c7 , and ~ ax-11 .

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ axc7 .  (Contributed by NM, 10-Jan-1993.)
     (New usage is discouraged.) $)
  ax-c7 $a |- ( -. A. x -. A. x ph -> ph ) $.

  $( A variant of ~ ax6 .  Axiom scheme C10' in [Megill] p. 448 (p. 16 of the
     preprint).

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ axc10 .  (Contributed by NM, 10-Jan-1993.)
     (New usage is discouraged.) $)
  ax-c10 $a |- ( A. x ( x = y -> A. x ph ) -> ph ) $.

  $( Axiom ~ ax-c11 was the original version of ~ ax-c11n (""n"" for ""new""),
     before it was discovered (in May 2008) that the shorter ~ ax-c11n could
     replace it.  It appears as Axiom scheme C11' in [Megill] p. 448 (p. 16 of
     the preprint).

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ axc11 .  (Contributed by NM, 10-May-1993.)
     (New usage is discouraged.) $)
  ax-c11 $a |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $.

  $( Axiom of Quantifier Substitution.  One of the equality and substitution
     axioms of predicate calculus with equality.  Appears as Lemma L12 in
     [Megill] p. 445 (p. 12 of the preprint).

     The original version of this axiom was ~ ax-c11 and was replaced with this
     shorter ~ ax-c11n (""n"" for ""new"") in May 2008.  The old axiom is proved
     from this one as theorem ~ axc11 .  Conversely, this axiom is proved from
     ~ ax-c11 as theorem ~ axc11nfromc11 .

     This axiom was proved redundant in July 2015.  See theorem ~ axc11n .

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ axc11n .  (Contributed by NM, 16-May-2008.)
     (New usage is discouraged.) $)
  ax-c11n $a |- ( A. x x = y -> A. y y = x ) $.

  $( Axiom ~ ax-c15 was the original version of ~ ax-12 , before it was
     discovered (in Jan. 2007) that the shorter ~ ax-12 could replace it.  It
     appears as Axiom scheme C15' in [Megill] p. 448 (p. 16 of the preprint).
     It is based on Lemma 16 of [Tarski] p. 70 and Axiom C8 of [Monk2] p. 105,
     from which it can be proved by cases.  To understand this theorem more
     easily, think of "" ` -. A. x x = y -> ` ..."" as informally meaning ""if
     ` x ` and ` y ` are distinct variables then...""  The antecedent becomes
     false if the same variable is substituted for ` x ` and ` y ` , ensuring
     the theorem is sound whenever this is the case.  In some later theorems,
     we call an antecedent of the form ` -. A. x x = y ` a ""distinctor.""

     Interestingly, if the wff expression substituted for ` ph ` contains no
     wff variables, the resulting statement _can_ be proved without invoking
     this axiom.  This means that even though this axiom is _metalogically_
     independent from the others, it is not _logically_ independent.
     Specifically, we can prove any wff-variable-free instance of axiom
     ~ ax-c15 (from which the ~ ax-12 instance follows by theorem ~ ax12 .)
     The proof is by induction on formula length, using ~ ax12eq and ~ ax12el
     for the basis steps and ~ ax12indn , ~ ax12indi , and ~ ax12inda for the
     induction steps.  (This paragraph is true provided we use ~ ax-c11 in
     place of ~ ax-c11n .)

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ axc15 , which should be used instead.  (Contributed by NM,
     14-May-1993.)  (New usage is discouraged.) $)
  ax-c15 $a |- ( -. A. x x = y ->
             ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.

  $( Axiom of Quantifier Introduction.  One of the equality and substitution
     axioms of predicate calculus with equality.  Informally, it says that
     whenever ` z ` is distinct from ` x ` and ` y ` , and ` x = y ` is true,
     then ` x = y ` quantified with ` z ` is also true.  In other words, ` z `
     is irrelevant to the truth of ` x = y ` .  Axiom scheme C9' in [Megill]
     p. 448 (p. 16 of the preprint).  It apparently does not otherwise appear
     in the literature but is easily proved from textbook predicate calculus by
     cases.

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ axc9 .  (Contributed by NM, 10-Jan-1993.)
     (New usage is discouraged.) $)
  ax-c9 $a |- ( -. A. z z = x -> ( -. A. z z = y ->
              ( x = y -> A. z x = y ) ) ) $.

  $( Axiom of Quantifier Introduction.  One of the equality and substitution
     axioms for a non-logical predicate in our predicate calculus with
     equality.  Axiom scheme C14' in [Megill] p. 448 (p. 16 of the preprint).
     It is redundant if we include ~ ax-5 ; see theorem ~ axc14 .  Alternately,
     ~ ax-5 becomes unnecessary in principle with this axiom, but we lose the
     more powerful metalogic afforded by ~ ax-5 .  We retain ~ ax-c14 here to
     provide completeness for systems with the simpler metalogic that results
     from omitting ~ ax-5 , which might be easier to study for some theoretical
     purposes.

     This axiom is obsolete and should no longer be used.  It is proved above
     as theorem ~ axc14 .  (Contributed by NM, 24-Jun-1993.)
     (New usage is discouraged.) $)
  ax-c14 $a |- ( -. A. z z = x -> ( -. A. z z = y ->
              ( x e. y -> A. z x e. y ) ) ) $.

  ${
    $d x y $.
    $( Axiom of Distinct Variables.  The only axiom of predicate calculus
       requiring that variables be distinct (if we consider ~ ax-5 to be a
       metatheorem and not an axiom).  Axiom scheme C16' in [Megill] p. 448 (p.
       16 of the preprint).  It apparently does not otherwise appear in the
       literature but is easily proved from textbook predicate calculus by
       cases.  It is a somewhat bizarre axiom since the antecedent is always
       false in set theory (see ~ dtru ), but nonetheless it is technically
       necessary as you can see from its uses.

       This axiom is redundant if we include ~ ax-5 ; see theorem ~ axc16 .
       Alternately, ~ ax-5 becomes logically redundant in the presence of this
       axiom, but without ~ ax-5 we lose the more powerful metalogic that
       results from being able to express the concept of a setvar variable not
       occurring in a wff (as opposed to just two setvar variables being
       distinct).  We retain ~ ax-c16 here to provide logical completeness for
       systems with the simpler metalogic that results from omitting ~ ax-5 ,
       which might be easier to study for some theoretical purposes.

       This axiom is obsolete and should no longer be used.  It is proved above
       as theorem ~ axc16 .  (Contributed by NM, 10-Jan-1993.)
       (New usage is discouraged.) $)
    ax-c16 $a |- ( A. x x = y -> ( ph -> A. x ph ) ) $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Rederive new axioms from old:  ax4 , ax10 , ax6fromc10 , ax12 , ax13fromc9
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Theorems ~ ax12 and ~ ax13fromc9 require some intermediate theorems that are
  included in this section.

$)

  $( This theorem repeats ~ sp under the name ~ axc5 , so that the metamath
     program's ""verify markup"" command will check that it matches axiom scheme
     ~ ax-c5 .  It is preferred that references to this theorem use the name
     ~ sp .  (Contributed by NM, 18-Aug-2017.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  axc5 $p |- ( A. x ph -> ph ) $=
    ( sp ) ABC $.

  $( Rederivation of axiom ~ ax-4 from ~ ax-c4 and other older axioms.  See
     ~ axc4 for the derivation of ~ ax-c4 from ~ ax-4 .  (Contributed by NM,
     23-May-2008.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax4 $p |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $=
    ( wi wal ax-c4 ax-c5 syl5 mpg syl ) ABDZCEZACEZBDZCEZMBCEDLNDLODCKNCFMALBAC
    GKCGHIABCFJ $.

  $( Rederivation of axiom ~ ax-10 from ~ ax-c7 and other older axioms.  See
     ~ axc7 for the derivation of ~ ax-c7 from ~ ax-10 .  (Contributed by NM,
     23-May-2008.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax10 $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
    ( wal wn wi ax-c4 ax-c5 id mpg nsyl ax-c7 nsyl4 ) ABCZBCZDZBCZMDZBCZMPQEPRE
    BOQBFPNMOBGMMEMNEBAMBFMHIJIMBKL $.

  $( Rederivation of axiom ~ ax-6 from ~ ax-c10 and other older axioms.  See
     ~ axc10 for the derivation of ~ ax-c10 from ~ ax-6 .  Lemma L18 in
     [Megill] p. 446 (p. 14 of the preprint).  (Contributed by NM,
     14-May-1993.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax6fromc10 $p |- -. A. x -. x = y $=
    ( weq wn wal wi ax-c10 ax-c7 con4i mpg ) ABCZKDZAEDZAEZFMAMABGNKLAHIJ $.

  $( ` x ` is not free in ` A. x ph ` .  Example in Appendix in [Megill] p. 450
     (p. 19 of the preprint).  Also Lemma 22 of [Monk2] p. 114.  (Contributed
     by NM, 24-Jan-1993.)  (New usage is discouraged.) $)
  hba1-o $p |- ( A. x ph -> A. x A. x ph ) $=
    ( wal wn ax-c5 con2i ax10 con1i alimi 3syl ) ABCZKDZBCZDZNBCKBCMKLBEFLBGNKB
    KMABGHIJ $.

  ${
    axc4i-o.1 $e |- ( A. x ph -> ps ) $.
    $( Inference version of ~ ax-c4 .  (Contributed by NM, 3-Jan-1993.)
       (New usage is discouraged.) $)
    axc4i-o $p |- ( A. x ph -> A. x ps ) $=
      ( wal hba1-o alrimih ) ACEBCACFDG $.
  $}

  $( Commutation law for identical variable specifiers.  The antecedent and
     consequent are true when ` x ` and ` y ` are substituted with the same
     variable.  Lemma L12 in [Megill] p. 445 (p. 12 of the preprint).  Version
     of ~ aecom using ~ ax-c11 .  Unlike ~ axc11nfromc11 , this version does
     not require ~ ax-5 .  (Contributed by NM, 10-May-1993.)
     (New usage is discouraged.) $)
  aecom-o $p |- ( A. x x = y -> A. y y = x ) $=
    ( weq wal ax-c11 pm2.43i equcomi alimi syl ) ABCZADZJBDZBACZBDKLJABEFJMBABG
    HI $.

  ${
    alequcoms-o.1 $e |- ( A. x x = y -> ph ) $.
    $( A commutation rule for identical variable specifiers.  Version of
       ~ aecoms using ax-c11 .  (Contributed by NM, 10-May-1993.)
       (New usage is discouraged.) $)
    aecoms-o $p |- ( A. y y = x -> ph ) $=
      ( weq wal aecom-o syl ) CBECFBCEBFACBGDH $.
  $}

  $( All variables are effectively bound in an identical variable specifier.
     Version of ~ hbae using ~ ax-c11 .  (Contributed by NM, 13-May-1993.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  hbae-o $p |- ( A. x x = y -> A. z A. x x = y ) $=
    ( weq wal wi ax-c5 ax-c9 syl7 ax-c11 aecoms-o pm2.43i syl5 pm2.61ii axc4i-o
    wn ax-11 syl ) ABDZAEZSCEZAETCESUAACADCEZCBDCEZTUAFZTSUBPUCPUASAGABCHIUDACS
    ACJKUDBCTSBEZBCDBEUATUESABJLSBCJMKNOSACQR $.

  ${
    dral1-o.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  Version of
       ~ dral1 using ~ ax-c11 .  (Contributed by NM, 24-Nov-1994.)
       (New usage is discouraged.) $)
    dral1-o $p |- ( A. x x = y -> ( A. x ph <-> A. y ps ) ) $=
      ( weq wal hbae-o biimpd alimdh ax-c11 syld biimprd wi aecoms-o impbid ) C
      DFCGZACGZBDGZQRBCGSQABCCDCHQABEIJBCDKLQSADGZRQBADCDDHQABEMJTRNDCADCKOLP
      $.
  $}

  $( Rederivation of axiom ~ ax-12 from ~ ax-c15 , ~ ax-c11 , and other older
     axioms.  See theorem ~ axc15 for the derivation of ~ ax-c15 from ~ ax-12 .

     An open problem is whether we can prove this using ~ ax-c11n instead of
     ~ ax-c11 .

     This proof uses newer axioms ~ ax-4 and ~ ax-6 , but since these are
     proved from the older axioms above, this is acceptable and lets us avoid
     having to reprove several earlier theorems to use ~ ax-c4 and ~ ax-c10 .
     (Contributed by NM, 22-Jan-2007.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax12 $p |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $=
    ( weq wal wi biidd dral1-o ax-1 alimi syl6bir a1d ax-c5 ax-c15 syl7 pm2.61i
    wn ) BCDZBEZRACEZRAFZBEZFZFSUCRSTABEUBAABCSAGHAUABARIJKLTASQRUBACMABCNOP $.

  $( Derive ~ ax-13 from ~ ax-c9 and other older axioms.

     This proof uses newer axioms ~ ax-4 and ~ ax-6 , but since these are
     proved from the older axioms above, this is acceptable and lets us avoid
     having to reprove several earlier theorems to use ~ ax-c4 and ~ ax-c10 .
     (Contributed by NM, 21-Dec-2015.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax13fromc9 $p |- ( -. x = y -> ( y = z -> A. x y = z ) ) $=
    ( weq wn wal wi wa ax-c5 con3i adantr equtrr equcoms con3rr3 imp nsyl ax-c9
    sylc ex pm2.43d ) ABDZEZBCDZUCAFZUBUCUCUDGZUBUCHZUAAFZEZACDZAFZEUEUBUHUCUGU
    AUAAIJKUFUIUJUBUCUIEUCUIUAUIUAGCBCBALMNOUIAIPBCAQRST $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
               Legacy theorems using obsolete axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  These theorems were mostly intended to study properties of the older axiom
  schemes and are not useful outside of this section.  They should not be
  used outside of this section.  They may be deleted when they are deemed to no
  longer be of interest.

$)

  ${
    $d x ph $.
    $( Axiom to quantify a variable over a formula in which it does not occur.
       Axiom C5 in [Megill] p. 444 (p. 11 of the preprint).  Also appears as
       Axiom B6 (p. 75) of system S2 of [Tarski] p. 77 and Axiom C5-1 of
       [Monk2] p. 113.

       (This theorem simply repeats ~ ax-5 so that we can include the following
       note, which applies only to the obsolete axiomatization.)

       This axiom is _logically_ redundant in the (logically complete)
       predicate calculus axiom system consisting of ~ ax-gen , ~ ax-c4 ,
       ~ ax-c5 , ~ ax-11 , ~ ax-c7 , ~ ax-7 , ~ ax-c9 , ~ ax-c10 , ~ ax-c11 ,
       ~ ax-8 , ~ ax-9 , ~ ax-c14 , ~ ax-c15 , and ~ ax-c16 : in that system,
       we can derive any instance of ~ ax-5 not containing wff variables by
       induction on formula length, using ~ ax5eq and ~ ax5el for the basis
       together ~ hbn , ~ hbal , and ~ hbim .  However, if we omit this axiom,
       our development would be quite inconvenient since we could work only
       with specific instances of wffs containing no wff variables - this axiom
       introduces the concept of a setvar variable not occurring in a wff (as
       opposed to just two setvar variables being distinct).  (Contributed by
       NM, 19-Aug-2017.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    ax5ALT $p |- ( ph -> A. x ph ) $=
      ( ax-5 ) ABC $.
  $}

  $( Proof of ~ equid from our older axioms.  This is often an axiom of
     equality in textbook systems, but we don't need it as an axiom since it
     can be proved from our other axioms (although the proof, as you can see
     below, is not as obvious as you might think).  This proof uses only axioms
     without distinct variable conditions and requires no dummy variables.  A
     simpler proof, similar to Tarski's, is possible if we make use of ~ ax-5 ;
     see the proof of ~ equid .  See ~ equid1ALT for an alternate proof.
     (Contributed by NM, 10-Jan-1993.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  equid1 $p |- x = x $=
    ( weq wal wn wi ax-c4 ax-c5 ax-c9 sylc mpg ax-c10 syl ax-c7 pm2.61i ) AABZA
    CZDZACZOROPEZACZORSERTEAQSAFRQQSQAGZUAAAAHIJOAAKLOAMN $.

  ${
    sps-o.1 $e |- ( ph -> ps ) $.
    $( Generalization of antecedent.  (Contributed by NM, 5-Jan-1993.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    sps-o $p |- ( A. x ph -> ps ) $=
      ( wal ax-c5 syl ) ACEABACFDG $.
  $}

  $( Bound-variable hypothesis builder for ` x = x ` .  This theorem tells us
     that any variable, including ` x ` , is effectively not free in
     ` x = x ` , even though ` x ` is technically free according to the
     traditional definition of free variable.  (The proof does not use
     ~ ax-c10 .)  (Contributed by NM, 13-Jan-2011.)  (Proof shortened by Wolf
     Lammen, 23-Mar-2014.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  hbequid $p |- ( x = x -> A. y x = x ) $=
    ( weq wal wi ax-c9 ax-7 pm2.43i alimi a1d pm2.61ii ) BACZBDZMAACZNBDZEAABFM
    ONLNBLNBAAGHIJZPK $.

  $( Bound-variable hypothesis builder for ` x = x ` .  This theorem tells us
     that any variable, including ` x ` , is effectively not free in
     ` x = x ` , even though ` x ` is technically free according to the
     traditional definition of free variable.  (The proof uses only ~ ax-4 ,
     ~ ax-7 , ~ ax-c9 , and ~ ax-gen .  This shows that this can be proved
     without ~ ax6 , even though the theorem ~ equid cannot be.  A shorter
     proof using ~ ax6 is obtainable from ~ equid and ~ hbth .)  Remark added
     2-Dec-2015 NM:  This proof does implicitly use ~ ax6v , which is used for
     the derivation of ~ axc9 , unless we consider ~ ax-c9 the starting axiom
     rather than ~ ax-13 .  (Contributed by NM, 13-Jan-2011.)  (Revised by
     Mario Carneiro, 12-Oct-2016.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  nfequid-o $p |- F/ y x = x $=
    ( weq hbequid nfi ) AACBABDE $.

  $( Proof of a single axiom that can replace ~ ax-c5 and ~ ax-c7 .  See
     ~ axc5c7toc5 and ~ axc5c7toc7 for the re-derivation of those axioms.
     (Contributed by Scott Fenton, 12-Sep-2005.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  axc5c7 $p |- ( ( A. x -. A. x ph -> A. x ph ) -> ph ) $=
    ( wal wn ax-c7 ax-c5 ja ) ABCZDBCHAABEABFG $.

  $( Re-derivation of ~ ax-c5 from ~ axc5c7 .  Only propositional calculus is
     used for the re-derivation.  (Contributed by Scott Fenton, 12-Sep-2005.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  axc5c7toc5 $p |- ( A. x ph -> ph ) $=
    ( wal wn wi ax-1 axc5c7 syl ) ABCZIDBCZIEAIJFABGH $.

  $( Re-derivation of ~ ax-c7 from ~ axc5c7 .  Only propositional calculus is
     used for the re-derivation.  (Contributed by Scott Fenton, 12-Sep-2005.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  axc5c7toc7 $p |- ( -. A. x -. A. x ph -> ph ) $=
    ( wal wn wi pm2.21 axc5c7 syl ) ABCZDBCZDJIEAJIFABGH $.

  $( Proof of a single axiom that can replace both ~ ax-c7 and ~ ax-11 .  See
     ~ axc711toc7 and ~ axc711to11 for the re-derivation of those axioms.
     (Contributed by NM, 18-Nov-2006.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  axc711 $p |- ( -. A. x -. A. y A. x ph -> A. y ph ) $=
    ( wal wn ax-11 con3i alimi ax-c7 syl ) ABDCDZEZBDZEACDZBDZEZBDZENQMPLBKOACB
    FGHGNBIJ $.

  $( ` x ` is not free in ` A. x ph ` .  (Contributed by Mario Carneiro,
     11-Aug-2016.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  nfa1-o $p |- F/ x A. x ph $=
    ( wal hba1-o nfi ) ABCBABDE $.

  $( Re-derivation of ~ ax-c7 from ~ axc711 .  Note that ~ ax-c7 and ~ ax-11
     are not used by the re-derivation.  (Contributed by NM, 18-Nov-2006.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  axc711toc7 $p |- ( -. A. x -. A. x ph -> ph ) $=
    ( wal wn hba1-o con3i alimi axc711 ax-c5 3syl ) ABCZDZBCZDKBCZDZBCZDKAPMOLB
    KNABEFGFABBHABIJ $.

  $( Re-derivation of ~ ax-11 from ~ axc711 .  Note that ~ ax-c7 and ~ ax-11
     are not used by the re-derivation.  (Contributed by NM, 18-Nov-2006.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  axc711to11 $p |- ( A. x A. y ph -> A. y A. x ph ) $=
    ( wal wn axc711toc7 con4i axc711 alimi syl ) ACDBDZKEZCDEZCDZABDZCDNKLCFGMO
    CACBHIJ $.

  $( Proof of a single axiom that can replace ~ ax-c5 , ~ ax-c7 , and ~ ax-11
     in a subsystem that includes these axioms plus ~ ax-c4 and ~ ax-gen (and
     propositional calculus).  See ~ axc5c711toc5 , ~ axc5c711toc7 , and
     ~ axc5c711to11 for the re-derivation of those axioms.  This theorem
     extends the idea in Scott Fenton's ~ axc5c7 .  (Contributed by NM,
     18-Nov-2006.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  axc5c711 $p |- ( ( A. x A. y -. A. x A. y ph -> A. x ph ) -> ph ) $=
    ( wal wn ax-c5 ax10 ax-c7 con1i alimi ax-11 3syl nsyl4 ja ) ACDZBDEZCDBDZAB
    DAOAQACFOEZRCDPBDZCDQACGRSCSOOBHIJPCBKLMABFN $.

  $( Re-derivation of ~ ax-c5 from ~ axc5c711 .  Only propositional calculus is
     used by the re-derivation.  (Contributed by NM, 19-Nov-2006.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  axc5c711toc5 $p |- ( A. x ph -> ph ) $=
    ( wal wn wi ax-1 axc5c711 syl ) ABCZIBCDBCBCZIEAIJFABBGH $.

  $( Re-derivation of ~ ax-c7 from ~ axc5c711 .  Note that ~ ax-c7 and ~ ax-11
     are not used by the re-derivation.  The use of ~ alimi (which uses
     ~ ax-c5 ) is allowed since we have already proved ~ axc5c711toc5 .
     (Contributed by NM, 19-Nov-2006.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  axc5c711toc7 $p |- ( -. A. x -. A. x ph -> ph ) $=
    ( wal wn wi hba1-o con3i alimi sps-o pm2.21 axc5c711 3syl ) ABCZDZBCZDMBCZD
    ZBCZBCZDSMEASOROBQNBMPABFGHIGSMJABBKL $.

  $( Re-derivation of ~ ax-11 from ~ axc5c711 .  Note that ~ ax-c7 and ~ ax-11
     are not used by the re-derivation.  The use of ~ alimi (which uses
     ~ ax-c5 ) is allowed since we have already proved ~ axc5c711toc5 .
     (Contributed by NM, 19-Nov-2006.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  axc5c711to11 $p |- ( A. x A. y ph -> A. y A. x ph ) $=
    ( wal wn axc5c711toc7 con4i wi pm2.21 axc5c711 syl alimi nsyl4 ) ACDBDZNEZC
    DZEZCDZABDZCDRNOCFGQSCPBDZEZBDSPUAABUATSHATSIABCJKLPBFMLK $.

  $( ~ equid with existential quantifier without using ~ ax-c5 or ~ ax-5 .
     (Contributed by NM, 13-Jan-2011.)  (Proof shortened by Wolf Lammen,
     27-Feb-2014.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  equidqe $p |- -. A. y -. x = x $=
    ( weq wn wal ax6fromc10 ax-7 pm2.43i con3i alimi mto ) AACZDZBEBACZDZBEBAFM
    OBNLNLBAAGHIJK $.

  $( A special case of ~ ax-c5 without using ~ ax-c5 or ~ ax-5 .  (Contributed
     by NM, 13-Jan-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  axc5sp1 $p |- ( A. y -. x = x -> -. x = x ) $=
    ( weq wn wal equidqe pm2.21i ) AACDZBEHABFG $.

  $( ~ equid with universal quantifier without using ~ ax-c5 or ~ ax-5 .
     (Contributed by NM, 13-Jan-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  equidq $p |- A. y x = x $=
    ( weq wal wn equidqe ax10 hbequid con3i alrimih mt3 ) AACZBDZLEZBDABFMENBLB
    GLMABHIJK $.

  $( Alternate proof of ~ equid and ~ equid1 from older axioms ~ ax-c7 ,
     ~ ax-c10 and ~ ax-c9 .  (Contributed by NM, 10-Jan-1993.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  equid1ALT $p |- x = x $=
    ( weq wal wn wi ax-c9 pm2.43i alimi ax-c10 syl ax-c7 pm2.61i ) AABZACZDZACZ
    MPMNEZACMOQAOQAAAFGHMAAIJMAKL $.

  $( Rederivation of ~ ax-c11n from original version ~ ax-c11 .  See theorem
     ~ axc11 for the derivation of ~ ax-c11 from ~ ax-c11n .

     This theorem should not be referenced in any proof.  Instead, use
     ~ ax-c11n above so that uses of ~ ax-c11n can be more easily identified,
     or use ~ aecom-o when this form is needed for studies involving ~ ax-c11
     and omitting ~ ax-5 .  (Contributed by NM, 16-May-2008.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  axc11nfromc11 $p |- ( A. x x = y -> A. y y = x ) $=
    ( weq wal ax-c11 pm2.43i equcomi alimi syl ) ABCZADZJBDZBACZBDKLJABEFJMBABG
    HI $.

  ${
    nalequcoms-o.1 $e |- ( -. A. x x = y -> ph ) $.
    $( A commutation rule for distinct variable specifiers.  Version of
       ~ naecoms using ~ ax-c11 .  (Contributed by NM, 2-Jan-2002.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    naecoms-o $p |- ( -. A. y y = x -> ph ) $=
      ( weq wal aecom-o nsyl4 con1i ) ACBECFZBCEBFJABCGDHI $.
  $}

  $( All variables are effectively bound in a distinct variable specifier.
     Lemma L19 in [Megill] p. 446 (p. 14 of the preprint).  Version of ~ hbnae
     using ~ ax-c11 .  (Contributed by NM, 13-May-1993.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  hbnae-o $p |- ( -. A. x x = y -> A. z -. A. x x = y ) $=
    ( weq wal hbae-o hbn ) ABDAECABCFG $.

  ${
    dvelimf-o.1 $e |- ( ph -> A. x ph ) $.
    dvelimf-o.2 $e |- ( ps -> A. z ps ) $.
    dvelimf-o.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Proof of ~ dvelimh that uses ~ ax-c11 but not ~ ax-c15 , ~ ax-c11n , or
       ~ ax-12 .  Version of ~ dvelimh using ~ ax-c11 instead of ~ axc11 .
       (Contributed by NM, 12-Nov-2002.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    dvelimf-o $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      ( weq wal wn wi hba1-o ax-c11 aecoms-o syl5 a1d wa hbnae-o hban ax-c9 imp
      a1i hbimd hbald ex pm2.61i equsalh albii 3imtr3g ) CDICJKZEDIZALZEJZUNCJZ
      BBCJCEICJZUKUNUOLZLUPUQUKUNUNEJZUPUOUMEMURUOLECUNECNOPQUPKZUKUQUSUKRZUMCE
      USUKECEESCDESTUTULACUSUKCCECSCDCSTUSUKULULCJLEDCUAUBAACJLUTFUCUDUEUFUGABE
      DGHUHZUNBCVAUIUJ $.
  $}

  ${
    dral2-o.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  Version of
       ~ dral2 using ~ ax-c11 .  (Contributed by NM, 27-Feb-2005.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    dral2-o $p |- ( A. x x = y -> ( A. z ph <-> A. z ps ) ) $=
      ( weq wal hbae-o albidh ) CDGCHABECDEIFJ $.
  $}

  ${
    $d t u v $.  $d t u x y $.  $d u w $.
    $( A ""distinctor elimination"" lemma with no restrictions on variables in
       the consequent, proved without using ~ ax-c16 .  Version of ~ aev using
       ~ ax-c11 .  (Contributed by NM, 8-Nov-2006.)  (Proof shortened by Andrew
       Salmon, 21-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    aev-o $p |- ( A. x x = y -> A. z w = v ) $=
      ( vt vu weq wal hbae-o ax-7 alrimih equcomi syl6 aecoms-o axc4i-o aecom-o
      spimv 3syl ) ABHZAIZDEHZCABCJUAFBHZFIZGEHZGIZUBUAUCFABFJTUCAFAFBKRLUDFGHZ
      FIZEGHZEIUFUCUGFUGBFBFHZUGBGBGHUJGFHUGBGFKGFMNROPUHUIEFGEJUGUIFEFEGKRLEGQ
      SUEUBGDGDEKRSL $.
  $}

  ${
    $d x z $.  $d y z $.
    $( Theorem to add distinct quantifier to atomic formula.  (This theorem
       demonstrates the induction basis for ~ ax-5 considered as a
       metatheorem.  Do not use it for later proofs - use ~ ax-5 instead, to
       avoid reference to the redundant axiom ~ ax-c16 .)  (Contributed by NM,
       10-Jan-1993.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax5eq $p |- ( x = y -> A. z x = y ) $=
      ( weq wal wi ax-c9 ax-c16 pm2.61ii ) CADCECBDCEABDZJCEFABCGJCAHJCBHI $.
  $}

  ${
    $d w z x $.  $d w y $.
    $( Quantifier introduction when one pair of variables is distinct.  Version
       of ~ dveeq2 using ~ ax-c15 .  (Contributed by NM, 2-Jan-2002.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    dveeq2-o $p |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $=
      ( vw weq ax-5 equequ2 dvelimf-o ) CDEZCBEZABDIAFJDFDBCGH $.
  $}

  ${
    $d x y $.
    $( A generalization of axiom ~ ax-c16 .  Version of ~ axc16g using
       ~ ax-c11 .  (Contributed by NM, 15-May-1993.)  (Proof shortened by
       Andrew Salmon, 25-May-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax16g-o $p |- ( A. x x = y -> ( ph -> A. z ph ) ) $=
      ( weq wal aev-o ax-c16 biidd dral1-o biimprd sylsyld ) BCEBFDBEDFZAABFZAD
      FZBCDDBGABCHMONAADBMAIJKL $.
  $}

  ${
    $d w z x $.  $d w y $.
    $( Quantifier introduction when one pair of variables is distinct.  Version
       of ~ dveeq1 using ax-c11 .  (Contributed by NM, 2-Jan-2002.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    dveeq1-o $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $=
      ( vw weq ax-5 equequ1 dvelimf-o ) DCEZBCEZABDIAFJDFDBCGH $.

    $( Version of ~ dveeq1 using ~ ax-c16 instead of ~ ax-5 .  (Contributed by
       NM, 29-Apr-2008.)  TODO:  Recover proof from older set.mm to remove use
       of ~ ax-5 .  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    dveeq1-o16 $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $=
      ( vw weq ax5eq equequ1 dvelimh ) DCEBCEABDDCAFBCDFDBCGH $.
  $}

  ${
    $d x z $.  $d y z $.
    $( Theorem to add distinct quantifier to atomic formula.  This theorem
       demonstrates the induction basis for ~ ax-5 considered as a
       metatheorem.)  (Contributed by NM, 22-Jun-1993.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax5el $p |- ( x e. y -> A. z x e. y ) $=
      ( weq wal wel wi ax-c14 ax-c16 pm2.61ii ) CADCECBDCEABFZKCEGABCHKCAIKCBIJ
      $.
  $}

  ${
    $d x z w $.
    $( This theorem shows that, given ~ ax-c16 , we can derive a version of
       ~ ax-c11n .  However, it is weaker than ~ ax-c11n because it has a
       distinct variable requirement.  (Contributed by Andrew Salmon,
       27-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    axc11n-16 $p |- ( A. x x = z -> A. z z = x ) $=
      ( weq wal ax-c16 alrimiv axc4i-o equequ1 cbvalv a1i imbi12d albidv biimpi
      vw wi wb wex nfa1-o 19.23 alcoms albii ax6ev pm2.27 ax-mp alimi spv sps-o
      equequ2 syl sylbi 3syl ) ABCZADZANCZUNADZOZNDZADZBNCZUSBDZOZNDZBDZBACZBDU
      LUQAUMUPNUNABEFGURVCUQVBABULUPVANULUNUSUOUTABNHZUOUTPULUNUSABVEIJKLIMVBVD
      BVAVDNBVABDZNDUSBQZUTOZNDZVDVFVHNUSUTBUSBRSUAVIUTNDVDVHUTNVGVHUTOBNUBVGUT
      UCUDUEUSVDBNUSNDVDBUSVDNANABUHUFUGTUIUJTGUK $.
  $}

  ${
    $d w z x $.  $d w y $.
    $( Alternate proof of ~ dveel2 using ~ ax-c16 instead of ~ ax-5 .
       (Contributed by NM, 10-May-2008.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    dveel2ALT $p |- ( -. A. x x = y -> ( z e. y -> A. x z e. y ) ) $=
      ( vw wel ax5el elequ2 dvelimh ) CDECBEABDCDAFCBDFDBCGH $.
  $}

  ${
    ax12f.1 $e |- ( ph -> A. x ph ) $.
    $( Basis step for constructing a substitution instance of ~ ax-c15 without
       using ~ ax-c15 .  We can start with any formula ` ph ` in which ` x ` is
       not free.  (Contributed by NM, 21-Jan-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax12f $p |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( weq wal wn wi ax-1 alrimih a1ii ) BCEZBFGLALAHZBFHAMBDALIJK $.
  $}

  ${
    $d x u v $.  $d y u v $.  $d z u v $.  $d w u v $.
    $( Basis step for constructing a substitution instance of ~ ax-c15 without
       using ~ ax-c15 .  Atomic formula for equality predicate.  (Contributed
       by NM, 22-Jan-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax12eq $p |- ( -. A. x x = y ->
               ( x = y -> ( z = w -> A. x ( x = y -> z = w ) ) ) ) $=
      ( vu vv weq wal wn wi wa 19.26 a1i wb equequ1 equequ2 sps-o imbi12d exp32
      imbi2d equid ax-gen sylan9bb nfa1-o albid adantr mpbii sylbir axc9 impcom
      ad2antll adantrr equtrr alimi syl6 sylbid adantll ad2antrr mpbid biimprcd
      dral2-o imp adantlr ad2antlr ax-1 alrimiv adantl dveeq2-o im2anan9 sylibr
      wex ax6ev syl exlimdv mpi a1d 4cases ) ACGZAHZADGZAHZABGZAHIZWBCDGZWBWDJZ
      AHZJZJZJZVSWAKVRVTKZAHZWIVRVTALWKWCWBWGWKWCWBKZKAAGZWBWMJZAHZJZWGWOWMWNAW
      MWBAUAMUBMWKWPWGNWLWKWMWDWOWFWJWMWDNAVRWMCAGZVTWDACAOADCPZUCQZWKWNWEAWJAU
      DWKWMWDWBWSTUERUFUGSUHVSWAIZKZWCWBWGXAWLKVTWBVTJZAHZJZWGWTWLXDVSWTWLKZVTB
      DGZXCWBVTXFNWTWCABDOUKXEXFXFAHZXCWTWCXFXGJZWBWCWTXHBDAUIUJULXFXBABDAUMUNU
      OUPUQVSXDWGNWTWLVSVTWDXCWFVRVTWDNAACDOQZXBWEACAVSVTWDWBXITVARURUSSVSIZWAK
      ZWCWBWGXKWLKWQWBWQJZAHZJZWGXJWLXNWAXJWLKZWQCBGZXMWBWQXPNXJWCABCPZUKXOXPXP
      AHZXMXJWCXPXRJZWBXJWCXSCBAUIVBULXPXLAWBWQXPXQUTUNUOUPVCWAXNWGNXJWLWAWQWDX
      MWFVTWQWDNAWRQZXLWEADAWAWQWDWBXTTVARVDUSSXJWTKZWHWCYAWGWBYAEDGZEVKWGEDVLY
      AYBWGEYAFCGZFVKYBWGJZFCVLYAYCYDFYAYCYBWGYAYCYBKZKZFEGZWBYGJZAHZJWGYGYHAYG
      WBVEVFYFYGWDYIWFYEYGWDNZYAYCYGCEGYBWDFCEOEDCPUCZVGYFYEAHZYIWFNYFYCAHZYBAH
      ZKZYLYAYEYOXJYCYMWTYBYNACFVHADEVHVIVBYCYBALVJYLYHWEAYEAUDYLYGWDWBYEYJAYKQ
      TUEVMRUGSVNVOVNVOVPVPVQ $.
  $}

  ${
    $d x u v $.  $d y u v $.  $d z u v $.  $d w u v $.
    $( Basis step for constructing a substitution instance of ~ ax-c15 without
       using ~ ax-c15 .  Atomic formula for membership predicate.  (Contributed
       by NM, 22-Jan-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax12el $p |- ( -. A. x x = y ->
               ( x = y -> ( z e. w -> A. x ( x = y -> z e. w ) ) ) ) $=
      ( vv vu weq wal wn wel wi wa wb elequ1 elequ2 adantl sps-o imbi2d imbi12d
      exp32 19.26 bitrd ax-5 dvelimf-o biimprcd alimi syl6 adantr sylbid nfa1-o
      sylan9bb albid sylbir ad2antll ax-c14 impcom adantrr adantll ad2antrr imp
      mpbid dral2-o adantlr ad2antlr wex ax6ev alrimiv dveeq2-o im2anan9 sylibr
      ax-1 syl mpbii exlimdv mpi a1d 4cases ) ACGZAHZADGZAHZABGZAHIZWBCDJZWBWDK
      ZAHZKZKZKZVSWALVRVTLZAHZWIVRVTAUAWKWCWBWGWKWCWBLZLAAJZWBWMKZAHZKZWGWLWPWK
      WLWMBBJZWOWBWMWQMWCWBWMBAJWQABANABBOUBZPWCWQWOKWBWCWQWQAHWOEEJZWQABEWSAUC
      WQEUCEBGWSBEJWQEBENEBBOUBUDWQWNAWBWMWQWRUEUFUGUHUIPWKWPWGMWLWKWMWDWOWFWJW
      MWDMAVRWMCAJZVTWDACANADCOZUKQZWKWNWEAWJAUJWKWMWDWBXBRULSUHVATUMVSWAIZLZWC
      WBWGXDWLLADJZWBXEKZAHZKZWGXCWLXHVSXCWLLZXEBDJZXGWBXEXJMXCWCABDNZUNXIXJXJA
      HZXGXCWCXJXLKZWBWCXCXMBDAUOUPUQXJXFAWBXEXJXKUEUFUGUIURVSXHWGMXCWLVSXEWDXG
      WFVRXEWDMAACDNQZXFWEACAVSXEWDWBXNRVBSUSVATVSIZWALZWCWBWGXPWLLWTWBWTKZAHZK
      ZWGXOWLXSWAXOWLLZWTCBJZXRWBWTYAMXOWCABCOZUNXTYAYAAHZXRXOWCYAYCKZWBXOWCYDC
      BAUOUTUQYAXQAWBWTYAYBUEUFUGUIVCWAXSWGMXOWLWAWTWDXRWFVTWTWDMAXAQZXQWEADAWA
      WTWDWBYERVBSVDVATXOXCLZWHWCYFWGWBYFFDGZFVEWGFDVFYFYGWGFYFECGZEVEYGWGKZECV
      FYFYHYIEYFYHYGWGYFYHYGLZLZEFJZWBYLKZAHZKWGYLYMAYLWBVKVGYKYLWDYNWFYJYLWDMZ
      YFYHYLCFJYGWDECFNFDCOUKZPYKYJAHZYNWFMYKYHAHZYGAHZLZYQYFYJYTXOYHYRXCYGYSAC
      EVHADFVHVIUTYHYGAUAVJYQYMWEAYJAUJYQYLWDWBYJYOAYPQRULVLSVMTVNVOVNVOVPVPVQ
      $.
  $}

  ${
    ax12indn.1 $e |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.
    $( Induction step for constructing a substitution instance of ~ ax-c15
       without using ~ ax-c15 .  Negation case.  (Contributed by NM,
       21-Jan-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax12indn $p |- ( -. A. x x = y ->
               ( x = y -> ( -. ph -> A. x ( x = y -> -. ph ) ) ) ) $=
      ( weq wal wn wi wa 19.8a exanali hbn1 con3 syl6 com23 alrimdh syl5bi syl5
      wex expd ) BCEZBFGZUAAGZUAUCHZBFZUAUCIZUFBSZUBUEUFBJUGUAAHZBFZGZUBUEUAABK
      UBUJUDBUABLUHBLUBUAUJUCUBUAAUIHUJUCHDAUIMNOPQRT $.

    ${
      ax12indi.2 $e |- ( -. A. x x = y ->
                 ( x = y -> ( ps -> A. x ( x = y -> ps ) ) ) ) $.
      $( Induction step for constructing a substitution instance of ~ ax-c15
         without using ~ ax-c15 .  Implication case.  (Contributed by NM,
         21-Jan-2007.)  (Proof modification is discouraged.)
         (New usage is discouraged.) $)
      ax12indi $p |- ( -. A. x x = y ->
           ( x = y -> ( ( ph -> ps ) -> A. x ( x = y -> ( ph -> ps ) ) ) ) ) $=
        ( weq wal wn wi wa ax12indn imp pm2.21 imim2i alimi syl6 ax-1 jad ex )
        CDGZCHIZUAABJZUAUCJZCHZJUBUAKZABUEUFAIZUAUGJZCHZUEUBUAUGUIJACDELMUHUDCU
        GUCUAABNOPQUFBUABJZCHZUEUBUABUKJFMUJUDCBUCUABAROPQST $.
    $}
  $}

  ${
    ax12indalem.1 $e |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.
    $( Lemma for ~ ax12inda2 and ~ ax12inda .  (Contributed by NM,
       24-Jan-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax12indalem $p |- ( -. A. y y = z -> ( -. A. x x = y ->
               ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) ) $=
      ( weq wal wn wi ax-1 axc4i-o a1i biidd a1d aecom-o con3i imp hbnae-o hban
      wa dral1-o imbi2d dral2-o 3imtr4d adantr simplr axc9 syl2an adantlr ax-c5
      aecoms-o hba1-o sylan2 alimdh syl2anc ax-11 wnf wb nfdh 19.21t syl albidh
      syl5ib ad2antrr syld exp31 pm2.61ian ) BDFBGZCDFCGZHZBCFZBGHZVKADGZVKVMIZ
      BGZIZIZIZVHVRVJVHVQVLVHVPVKVPDBDBFDGZABGZVKVTIZBGZVMVOVTWBIVSAWABVTVKJKLA
      ADBVSAMUAZVNWADBBVSVMVTVKWCUBUCUDUKNNUEVHHZVJTZVLVKVPWEVLTVKTZVMVKAIZBGZD
      GZVOWFVLVKDGZVMWIIWEVLVKUFWEVKWJVLWEVKWJWDVSHZDCFDGZHZVKWJIZVJVSVHDBOPWLV
      IDCOPWKWMWNBCDUGQUHZQUIVLWJTAWHDVLWJDBCDRVKDULSWJVLVKAWHIZVKDUJVLVKWPEQUM
      UNUOWEWIVOIVLVKWIWGDGZBGWEVOWGDBUPWEWQVNBWDVJBBDBRCDBRSWEVKDUQWQVNURWEVKD
      WDVJDBDDRCDDRSWOUSVKADUTVAVBVCVDVEVFVG $.
  $}

  ${
    $d z y $.
    ax12inda2.1 $e |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.
    $( Alternate proof of ~ ax12inda2 , slightly more direct and not requiring
       ~ ax-c16 .  (Contributed by NM, 4-May-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax12inda2ALT $p |- ( -. A. x x = y ->
               ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) $=
      ( weq wal wn wi ax-1 axc4i-o a1i biidd dral1-o imbi2d dral2-o a1d hbnae-o
      wa imp 3imtr4d aecoms-o simplr naecoms-o adantlr hba1-o hban ax-c5 sylan2
      dveeq1-o alimdh syl2anc ax-11 wnf wb nfdh 19.21t syl albidh ad2antrr syld
      syl5ib exp31 pm2.61i ) BDFBGZBCFZBGHZVFADGZVFVHIZBGZIZIZIVEVLVGVEVKVFVKDB
      DBFDGZABGZVFVNIZBGZVHVJVNVPIVMAVOBVNVFJKLAADBVMAMNZVIVODBBVMVHVNVFVQOPUAU
      BQQVEHZVGVFVKVRVGSVFSZVHVFAIZBGZDGZVJVSVGVFDGZVHWBIVRVGVFUCVRVFWCVGVRVFWC
      VFWCIDBDBCUJUDZTUEVGWCSAWADVGWCDBCDRVFDUFUGWCVGVFAWAIZVFDUHVGVFWEETUIUKUL
      VRWBVJIVGVFWBVTDGZBGVRVJVTDBUMVRWFVIBBDBRVRVFDUNWFVIUOVRVFDBDDRWDUPVFADUQ
      URUSVBUTVAVCVD $.

    $( Induction step for constructing a substitution instance of ~ ax-c15
       without using ~ ax-c15 .  Quantification case.  When ` z ` and ` y ` are
       distinct, this theorem avoids the dummy variables needed by the more
       general ~ ax12inda .  (Contributed by NM, 24-Jan-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax12inda2 $p |- ( -. A. x x = y ->
               ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) $=
      ( weq wal wn wi ax-1 ax16g-o syl5 a1d ax12indalem pm2.61i ) CDFCGZBCFZBGH
      ZQADGZQSIZBGZIZIZIPUCRPUBQSTPUASQJTCDBKLMMABCDENO $.
  $}

  ${
    $d w ph $.  $d w x $.  $d w y $.  $d w z $.
    ax12inda.1 $e |- ( -. A. x x = w ->
               ( x = w -> ( ph -> A. x ( x = w -> ph ) ) ) ) $.
    $( Induction step for constructing a substitution instance of ~ ax-c15
       without using ~ ax-c15 .  Quantification case.  (When ` z ` and ` y `
       are distinct, ~ ax12inda2 may be used instead to avoid the dummy
       variable ` w ` in the proof.)  (Contributed by NM, 24-Jan-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax12inda $p |- ( -. A. x x = y ->
               ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) $=
      ( weq wal wn wi wex ax6ev wa ax12inda2 wb dveeq2-o imp albidh syl imbi12d
      hba1-o equequ2 sps-o notbid adantl imbi1d imbi2d mpbii ex exlimdv pm2.43i
      mpi ) BCGZBHZIZUMADHZUMUPJZBHZJZJZUOECGZEKUOUTJZECLUOVAVBEUOVAVBUOVAMZBEG
      ZBHZIZVDUPVDUPJZBHZJZJZJVBABEDFNVCVFUOVJUTVCVABHZVFUOOUOVAVKBCEPQZVKVEUNV
      KVDUMBVABUAZVAVDUMOZBECBUBZUCZRUDSVCVDUMVIUSVAVNUOVOUEVCVHURUPVCVKVHUROVL
      VKVGUQBVMVKVDUMUPVPUFRSUGTTUHUIUJULUK $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    ax12v2-o.1 $e |- ( x = z -> ( ph -> A. x ( x = z -> ph ) ) ) $.
    $( Recovery of ~ ax-c15 from ~ ax12v without using ~ ax-c15 .  The
       hypothesis is even weaker than ~ ax12v , with ` z ` both distinct from
       ` x ` _and_ not occurring in ` ph ` .  Thus, the hypothesis provides an
       alternate axiom that can be used in place of ~ ax-c15 .  (Contributed by
       NM, 2-Feb-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax12v2-o $p |- ( -. A. x x = y ->
                 ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( weq wal wn wex wi ax6ev wa wb equequ2 adantl dveeq2-o imp nfa1-o imbi1d
      sps-o albid syl imbi2d imbi12d mpbii ex exlimdv mpi ) BCFZBGHZDCFZDIUIAUI
      AJZBGZJZJZDCKUJUKUODUJUKUOUJUKLZBDFZAUQAJZBGZJZJUOEUPUQUIUTUNUKUQUIMUJDCB
      NZOUPUSUMAUPUKBGZUSUMMUJUKVBBCDPQVBURULBUKBRUKURULMBUKUQUIAVASTUAUBUCUDUE
      UFUGUH $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    ax12a2-o.1 $e |- ( x = z -> ( A. z ph -> A. x ( x = z -> ph ) ) ) $.
    $( Derive ~ ax-c15 from a hypothesis in the form of ~ ax-12 , without using
       ~ ax-12 or ~ ax-c15 .  The hypothesis is even weaker than ~ ax-12 , with
       ` z ` both distinct from ` x ` and not occurring in ` ph ` .  Thus, the
       hypothesis provides an alternate axiom that can be used in place of
       ~ ax-12 , if we also hvae ~ ax-c11 which this proof uses .  As theorem
       ~ ax12 shows, the distinct variable conditions are optional.  An open
       problem is whether we can derive this with ~ ax-c11n instead of
       ~ ax-c11 .  (Contributed by NM, 2-Feb-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax12a2-o $p |- ( -. A. x x = y ->
                 ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      ( wal weq wi ax-5 syl5 ax12v2-o ) ABCDAADFBDGZLAHBFADIEJK $.
  $}

  $( Show that ~ ax-c11 can be derived from ~ ax-c11n .  An open problem is
     whether this theorem can be derived from ~ ax-c11n and the others when
     ~ ax-12 is replaced with ~ ax-c15 .  See theorem ~ axc11nfromc11 for the
     rederivation of ~ ax-c11n from ~ axc11 .

     Normally, ~ axc11 should be used rather than ~ ax-c11 or ~ axc11-o ,
     except by theorems specifically studying the latter's properties.
     (Contributed by NM, 16-May-2008.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  axc11-o $p |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $=
    ( weq wal wi ax-c11n ax12 equcoms sps-o pm2.27 al2imi sylsyld ) BCDZBECBDZC
    EABEZOAFZCEZACEBCGNPRFZBSCBACBHIJOQACOAKLM $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
               Existential uniqueness
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $( Declare new symbols needed for uniqueness notation. $)
  $c E! $.  $( Backwards E exclamation point. $)
  $c E* $.  $( Backwards E superscript *. $)

  $( Extend wff definition to include existential uniqueness (""there exists a
     unique ` x ` such that ` ph ` ""). $)
  weu $a wff E! x ph $.

  $( Extend wff definition to include uniqueness (""there exists at most one
     ` x ` such that ` ph ` ""). $)
  wmo $a wff E* x ph $.

  ${
    $d w x y $.  $d x z $.  $d y ph $.  $d w z ph $.
    $( A soundness justification theorem for ~ df-eu , showing that the
       definition is equivalent to itself with its dummy variable renamed.
       Note that ` y ` and ` z ` needn't be distinct variables.  See
       ~ eujustALT for a proof that provides an example of how it can be
       achieved through the use of ~ dvelim .  (Contributed by NM,
       11-Mar-2010.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
    eujust $p |- ( E. y A. x ( ph <-> x = y )
        <-> E. z A. x ( ph <-> x = z ) ) $=
      ( vw weq wb wal wex equequ2 bibi2d albidv cbvexv bitri ) ABCFZGZBHZCIABEF
      ZGZBHZEIABDFZGZBHZDIQTCECEFZPSBUDORACEBJKLMTUCEDEDFZSUBBUERUAAEDBJKLMN $.

    $( Alternate proof of ~ eujust illustrating the use of ~ dvelim .
       (Contributed by NM, 11-Mar-2010.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    eujustALT $p |- ( E. y A. x ( ph <-> x = y )
        <-> E. z A. x ( ph <-> x = z ) ) $=
      ( vw weq wal wb wex equequ2 bibi2d albidv sps wn hbnae ax-5 notbid dvelim
      wi df-ex drex1 alrimih naecoms a1i cbv2h syl 3bitr4g pm2.61i ) CDFZCGZABC
      FZHZBGZCIZABDFZHZBGZDIZHUMUQCDUIUMUQHCUIULUPBUIUKUOACDBJKLZMUAUJNZUMNZCGZ
      NUQNZDGZNUNURUTVBVDUTUTDGZCGVBVDHUTVECCDCOCDDOUBUTVAVCCDVAVADGSDCABEFZHZB
      GZNZVADCEVIDPECFZVHUMVJVGULBVJVFUKAECBJKLQRUCVIVCCDEVICPEDFZVHUQVKVGUPBVK
      VFUOAEDBJKLQRUIVAVCHSUTUIUMUQUSQUDUEUFQUMCTUQDTUGUH $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( Define existential uniqueness, i.e.  ""there exists exactly one ` x `
       such that ` ph ` .""  Definition 10.1 of [BellMachover] p. 97; also
       Definition *14.02 of [WhiteheadRussell] p. 175.  Other possible
       definitions are given by ~ eu1 , ~ eu2 , ~ eu3v , and ~ eu5 (which in
       some cases we show with a hypothesis ` ph -> A. y ph ` in place of a
       distinct variable condition on ` y ` and ` ph ` ).  Double uniqueness is
       tricky: ` E! x E! y ph ` does not mean ""exactly one ` x ` and one
       ` y ` "" (see ~ 2eu4 ).  (Contributed by NM, 12-Aug-1993.) $)
    df-eu $a |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) $.
  $}

  $( Define ""there exists at most one ` x ` such that ` ph ` .""  Here we define
     it in terms of existential uniqueness.  Notation of [BellMachover] p. 460,
     whose definition we show as ~ mo3 .  For other possible definitions see
     ~ mo2 and ~ mo4 .  (Contributed by NM, 8-Mar-1995.) $)
  df-mo $a |- ( E* x ph <-> ( E. x ph -> E! x ph ) ) $.

  ${
    $d x y z $.
    $( Equality has existential uniqueness.  Special case of ~ eueq1 proved
       using only predicate calculus.  The proof needs ` y = z ` be free of
       ` x ` .  This is ensured by having ` x ` and ` y ` be distinct.
       Alternatevly, a distinctor ` A. x x = y ` could have been used instead.
       (Contributed by Stefan Allan, 4-Dec-2008.)  (Proof shortened by Wolf
       Lammen, 8-Sep-2019.) $)
    euequ1 $p |- E! x x = y $=
      ( vz weq weu wb wal wex ax6ev equequ2 equcoms alrimiv eximii df-eu mpbir
      ) ABDZAEPACDFZAGZCHCBDZRCCBISQAQBCBCAJKLMPACNO $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( Alternate definition of ""at most one.""  Unlike ~ mo2 , which is slightly
       more general, it does not depend on ~ ax-11 and ~ ax-13 , whence it is
       preferable within predicate logic.  Elsewhere, most theorems depend on
       these axioms anyway, so this advantage is no longer important.
       (Contributed by Wolf Lammen, 27-May-2019.)  (Proof shortened by Wolf
       Lammen, 10-Nov-2019.) $)
    mo2v $p |- ( E* x ph <-> E. y A. x ( ph -> x = y ) ) $=
      ( wmo wex weu wi wb df-mo df-eu imbi2i wn alnex pm2.21 alimi sylbir eximi
      weq wal com12 19.23bi bi1 ja nfia1 wa id ax12v embantd spsd ancld syl6ibr
      albiim exlimi eximdv impbii 3bitri ) ABDABEZABFZGUQABCRZHZBSZCEZGZAUSGZBS
      ZCEZABIURVBUQABCJKVCVFUQVBVFUQLZVFCVGVECVGALZBSVEABMVHVDBAUSNOPQUAVAVECUT
      VDBAUSUBOQUCUQVFVBUQVEVACAVEVAGBVDUTBUDAVEVEUSAGBSZUEVAAVEVIAVDVIBAAUSVIA
      UFUSAVIABCUGTUHUIUJAUSBULUKUMUNTUOUP $.

    $( Obsolete proof of ~ mo2v as of 10-Nov-2019.  (Contributed by Wolf
       Lammen, 27-May-2019.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    mo2vOLD $p |- ( E* x ph <-> E. y A. x ( ph -> x = y ) ) $=
      ( wmo wex weu wi wb df-mo df-eu imbi2i wn alnex pm2.21 alimi sylbir 19.8a
      weq wal syl bi1 eximi ja nfia1 wa ax-5 ax-12 syl5com embantd ancld albiim
      id spsd syl6ibr exlimi eximdv com12 impbii 3bitri ) ABDABEZABFZGUTABCRZHZ
      BSZCEZGZAVBGZBSZCEZABIVAVEUTABCJKVFVIUTVEVIUTLZVHVIVJALZBSVHABMVKVGBAVBNO
      PVHCQTVDVHCVCVGBAVBUAOUBUCUTVIVEUTVHVDCAVHVDGBVGVCBUDAVHVHVBAGBSZUEVDAVHV
      LAVGVLBAAVBVLAULAACSVBVLACUFABCUGUHUIUMUJAVBBUKUNUOUPUQURUS $.

    $( Obsolete proof of ~ mo2v as of 24-Aug-2019.  (Contributed by Wolf
       Lammen, 27-May-2019.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    mo2vOLDOLD $p |- ( E* x ph <-> E. y A. x ( ph -> x = y ) ) $=
      ( wmo wex weu wi wb df-mo df-eu imbi2i wn alnex pm2.21 alimi sylbir 19.8a
      weq wal syl bi1 eximi ja wa nfia1 ax-5 ax-12 syl5com embantd exlimi ancld
      id spsd albiim syl6ibr eximdv com12 impbii 3bitri ) ABDABEZABFZGUTABCRZHZ
      BSZCEZGZAVBGZBSZCEZABIVAVEUTABCJKVFVIUTVEVIUTLZVHVIVJALZBSVHABMVKVGBAVBNO
      PVHCQTVDVHCVCVGBAVBUAOUBUCUTVIVEUTVHVDCUTVHVHVBAGZBSZUDVDUTVHVMAVHVMGBVGV
      LBUEAVGVMBAAVBVMAULAACSVBVMACUFABCUGUHUIUMUJUKAVBBUNUOUPUQURUS $.
  $}

  ${
    $d x y z $.  $d ph z $.
    euf.1 $e |- F/ y ph $.
    $( A version of the existential uniqueness definition with a hypothesis
       instead of a distinct variable condition.  (Contributed by NM,
       12-Aug-1993.)  (Proof shortened by Wolf Lammen, 30-Oct-2018.) $)
    euf $p |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) $=
      ( vz weu weq wb wal wex df-eu nfbi nfal equequ2 bibi2d albidv cbvex bitri
      nfv ) ABFABEGZHZBIZEJABCGZHZBIZCJABEKUBUEECUACBATCDTCSLMUEESECGZUAUDBUFTU
      CAECBNOPQR $.
  $}

  ${
    $d x y z $.  $d ph z $.
    mo2.1 $e |- F/ y ph $.
    $( Alternate definition of ""at most one.""  (Contributed by NM,
       8-Mar-1995.)  Restrict dummy variable z.  (Revised by Wolf Lammen,
       28-May-2019.) $)
    mo2 $p |- ( E* x ph <-> E. y A. x ( ph -> x = y ) ) $=
      ( vz wmo weq wal wex mo2v nfv nfim nfal equequ2 imbi2d albidv cbvex bitri
      wi ) ABFABEGZSZBHZEIABCGZSZBHZCIABEJUBUEECUACBATCDTCKLMUEEKECGZUAUDBUFTUC
      AECBNOPQR $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( Bound-variable hypothesis builder for uniqueness.  (Contributed by NM,
       9-Jul-1994.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
    nfeu1 $p |- F/ x E! x ph $=
      ( vy weu weq wb wal wex df-eu nfa1 nfex nfxfr ) ABDABCEFZBGZCHBABCINBCMBJ
      KL $.
  $}

  $( Bound-variable hypothesis builder for ""at most one.""  (Contributed by NM,
     8-Mar-1995.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
  nfmo1 $p |- F/ x E* x ph $=
    ( wmo wex weu wi df-mo nfe1 nfeu1 nfim nfxfr ) ABCABDZABEZFBABGLMBABHABIJK
    $.

  ${
    $d x z $.  $d y z $.  $d z ph $.  $d z ps $.
    nfeud2.1 $e |- F/ y ph $.
    nfeud2.2 $e |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $.
    $( Bound-variable hypothesis builder for uniqueness.  (Contributed by Mario
       Carneiro, 14-Nov-2016.)  (Proof shortened by Wolf Lammen,
       4-Oct-2018.) $)
    nfeud2 $p |- ( ph -> F/ x E! y ps ) $=
      ( vz weu weq wb wal wex df-eu nfv wn wa wnf nfeqf1 adantl nfbid nfald2
      nfexd nfxfrd ) BDHBDGIZJZDKZGLACBDGMAUFCGAGNAUECDEACDICKOZPBUDCFUGUDCQACD
      GRSTUAUBUC $.
  $}

  ${
    nfmod2.1 $e |- F/ y ph $.
    nfmod2.2 $e |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $.
    $( Bound-variable hypothesis builder for ""at most one.""  (Contributed by
       Mario Carneiro, 14-Nov-2016.) $)
    nfmod2 $p |- ( ph -> F/ x E* y ps ) $=
      ( wmo wex weu wi df-mo nfexd2 nfeud2 nfimd nfxfrd ) BDGBDHZBDIZJACBDKAPQC
      ABCDEFLABCDEFMNO $.
  $}

  ${
    nfeud.1 $e |- F/ y ph $.
    nfeud.2 $e |- ( ph -> F/ x ps ) $.
    $( Deduction version of ~ nfeu .  (Contributed by NM, 15-Feb-2013.)
       (Revised by Mario Carneiro, 7-Oct-2016.) $)
    nfeud $p |- ( ph -> F/ x E! y ps ) $=
      ( wnf weq wal wn adantr nfeud2 ) ABCDEABCGCDHCIJFKL $.

    $( Bound-variable hypothesis builder for ""at most one.""  (Contributed by
       Mario Carneiro, 14-Nov-2016.) $)
    nfmod $p |- ( ph -> F/ x E* y ps ) $=
      ( wnf weq wal wn adantr nfmod2 ) ABCDEABCGCDHCIJFKL $.
  $}

  ${
    $d y z $.  $d x z $.  $d z ph $.
    nfeu.1 $e |- F/ x ph $.
    $( Bound-variable hypothesis builder for uniqueness.  Note that ` x ` and
       ` y ` needn't be distinct.  (Contributed by NM, 8-Mar-1995.)  (Revised
       by Mario Carneiro, 7-Oct-2016.) $)
    nfeu $p |- F/ x E! y ph $=
      ( weu wnf wtru nftru a1i nfeud trud ) ACEBFGABCCHABFGDIJK $.

    $( Bound-variable hypothesis builder for ""at most one.""  (Contributed by
       NM, 9-Mar-1995.) $)
    nfmo $p |- F/ x E* y ph $=
      ( wmo wnf wtru nftru a1i nfmod trud ) ACEBFGABCCHABFGDIJK $.
  $}

  ${
    $d x y $.  $d y ph $.  $d y ps $.  $d y ch $.
    eubid.1 $e |- F/ x ph $.
    eubid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for uniqueness quantifier (deduction rule).
       (Contributed by NM, 9-Jul-1994.) $)
    eubid $p |- ( ph -> ( E! x ps <-> E! x ch ) ) $=
      ( vy weq wb wal wex weu bibi1d albid exbidv df-eu 3bitr4g ) ABDGHZIZDJZGK
      CRIZDJZGKBDLCDLATUBGASUADEABCRFMNOBDGPCDGPQ $.
  $}

  ${
    mobid.1 $e |- F/ x ph $.
    mobid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for ""at most one"" quantifier (deduction rule).
       (Contributed by NM, 8-Mar-1995.) $)
    mobid $p |- ( ph -> ( E* x ps <-> E* x ch ) ) $=
      ( wex weu wi wmo exbid eubid imbi12d df-mo 3bitr4g ) ABDGZBDHZICDGZCDHZIB
      DJCDJAPRQSABCDEFKABCDEFLMBDNCDNO $.
  $}

  ${
    $d x ph $.
    eubidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for uniqueness quantifier (deduction rule).
       (Contributed by NM, 9-Jul-1994.) $)
    eubidv $p |- ( ph -> ( E! x ps <-> E! x ch ) ) $=
      ( nfv eubid ) ABCDADFEG $.
  $}

  ${
    $d x ph $.
    mobidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for ""at most one"" quantifier (deduction rule).
       (Contributed by Mario Carneiro, 7-Oct-2016.) $)
    mobidv $p |- ( ph -> ( E* x ps <-> E* x ch ) ) $=
      ( nfv mobid ) ABCDADFEG $.
  $}

  ${
    eubii.1 $e |- ( ph <-> ps ) $.
    $( Introduce uniqueness quantifier to both sides of an equivalence.
       (Contributed by NM, 9-Jul-1994.)  (Revised by Mario Carneiro,
       6-Oct-2016.) $)
    eubii $p |- ( E! x ph <-> E! x ps ) $=
      ( weu wb wtru a1i eubidv trud ) ACEBCEFGABCABFGDHIJ $.
  $}

  ${
    mobii.1 $e |- ( ps <-> ch ) $.
    $( Formula-building rule for ""at most one"" quantifier (inference rule).
       (Contributed by NM, 9-Mar-1995.)  (Revised by Mario Carneiro,
       17-Oct-2016.) $)
    mobii $p |- ( E* x ps <-> E* x ch ) $=
      ( wmo wb wtru a1i mobidv trud ) ACEBCEFGABCABFGDHIJ $.
  $}

  ${
    $d x y $.  $d ph y $.
    $( Existential uniqueness implies existence.  For a shorter proof using
       more axioms, see ~ euexALT .  (Contributed by NM, 15-Sep-1993.)  (Proof
       shortened by Andrew Salmon, 9-Jul-2011.)  (Proof shortened by Wolf
       Lammen, 4-Dec-2018.) $)
    euex $p |- ( E! x ph -> E. x ph ) $=
      ( vy weu weq wb wal wex df-eu ax6ev bi2 com12 eximii 19.35i exlimiv sylbi
      wi ) ABDABCEZFZBGZCHABHZABCITUACSABRSAQBBCJSRAARKLMNOP $.
  $}

  $( Something exists or at most one exists.  (Contributed by NM,
     8-Mar-1995.) $)
  exmo $p |- ( E. x ph \/ E* x ph ) $=
    ( wex wmo wn weu wi pm2.21 df-mo sylibr orri ) ABCZABDZLELABFZGMLNHABIJK $.

  $( Uniqueness in terms of ""at most one.""  Revised to reduce dependencies on
     axioms.  (Contributed by NM, 23-Mar-1995.)  (Proof shortened by Wolf
     Lammen, 25-May-2019.) $)
  eu5 $p |- ( E! x ph <-> ( E. x ph /\ E* x ph ) ) $=
    ( wex weu wa wi wmo abai euex pm4.71ri df-mo anbi2i 3bitr4i ) ABCZABDZENNOF
    ZEONABGZENOHONABIJQPNABKLM $.

  $( Existence implies ""at most one"" is equivalent to uniqueness.  (Contributed
     by NM, 5-Apr-2004.) $)
  exmoeu2 $p |- ( E. x ph -> ( E* x ph <-> E! x ph ) ) $=
    ( weu wex wmo eu5 baibr ) ABCABDABEABFG $.

  ${
    $d x y $.  $d ph y $.
    $( An alternate way to express existential uniqueness.  (Contributed by NM,
       8-Jul-1994.)  Add a distinct variable condition on ` ph ` .  (Revised by
       Wolf Lammen, 29-May-2019.) $)
    eu3v $p |- ( E! x ph <-> ( E. x ph /\ E. y A. x ( ph -> x = y ) ) ) $=
      ( weu wex wmo wa weq wi wal eu5 mo2v anbi2i bitri ) ABDABEZABFZGOABCHIBJC
      EZGABKPQOABCLMN $.
  $}

  $( Existential uniqueness implies ""at most one.""  (Contributed by NM,
     23-Mar-1995.) $)
  eumo $p |- ( E! x ph -> E* x ph ) $=
    ( weu wex wmo eu5 simprbi ) ABCABDABEABFG $.

  ${
    eumoi.1 $e |- E! x ph $.
    $( ""At most one"" inferred from existential uniqueness.  (Contributed by NM,
       5-Apr-1995.) $)
    eumoi $p |- E* x ph $=
      ( weu wmo eumo ax-mp ) ABDABECABFG $.
  $}

  $( Absorption of existence condition by ""at most one.""  (Contributed by NM,
     4-Nov-2002.) $)
  moabs $p |- ( E* x ph <-> ( E. x ph -> E* x ph ) ) $=
    ( wex weu wi wmo pm5.4 df-mo imbi2i 3bitr4ri ) ABCZKABDZEZEMKABFZENKLGNMKAB
    HZIOJ $.

  $( Existence in terms of ""at most one"" and uniqueness.  (Contributed by NM,
     5-Apr-2004.)  (Proof shortened by Wolf Lammen, 5-Dec-2018.) $)
  exmoeu $p |- ( E. x ph <-> ( E* x ph -> E! x ph ) ) $=
    ( wex wmo weu wi df-mo biimpi com12 exmo ori con1i euex ja impbii ) ABCZABD
    ZABEZFQPRQPRFABGHIQRPPQPQABJKLABMNO $.

  ${
    $d x y $.
    eumo0OLD.1 $e |- F/ y ph $.
    $( Obsolete as of 6-Jun-2018.  Existential uniqueness implies ""at most
       one.""  (Contributed by NM, 8-Jul-1994.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    eumo0OLD $p |- ( E! x ph -> E. y A. x ( ph -> x = y ) ) $=
      ( weu weq wb wal wex wi euf bi1 alimi eximi sylbi ) ABEABCFZGZBHZCIAPJZBH
      ZCIABCDKRTCQSBAPLMNO $.
  $}

  ${
    $d w y z $.  $d ph z w $.  $d w x z $.
    sb8eu.1 $e |- F/ y ph $.
    $( Variable substitution in uniqueness quantifier.  (Contributed by NM,
       7-Aug-1994.)  (Revised by Mario Carneiro, 7-Oct-2016.)  (Proof shortened
       by Wolf Lammen, 24-Aug-2019.) $)
    sb8eu $p |- ( E! x ph <-> E! y [ y / x ] ph ) $=
      ( vz vw weq wal wex wsb weu nfv sb8 equsb3 sblbis albii nfsb nfbi df-eu
      wb sbequ equequ1 bibi12d cbval 3bitri exbii 3bitr4i ) ABEGZTZBHZEIABCJZCE
      GZTZCHZEIABKUKCKUJUNEUJUIBFJZFHABFJZFEGZTZFHUNUIBFUIFLMUOURFUHUQABFFBENOP
      URUMFCUPUQCABFCDQUQCLRUMFLFCGUPUKUQULAFCBUAFCEUBUCUDUEUFABESUKCESUG $.

    $( Obsolete proof of ~ sb8eu as of 24-Aug-2019.  (Contributed by NM,
       7-Aug-1994.)  (Revised by Mario Carneiro, 7-Oct-2016.)  (Proof shortened
       by Wolf Lammen, 8-Oct-2018.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    sb8euOLD $p |- ( E! x ph <-> E! y [ y / x ] ph ) $=
      ( vz vw weq wal wex wsb weu nfv sb8 equsb3 sblbis nfsb nfbi nfxfr df-eu
      wb sbequ cbval albii 3bitri exbii 3bitr4i ) ABEGZTZBHZEIABCJZCEGZTZCHZEIA
      BKUJCKUIUMEUIUHBFJZFHUHBCJZCHUMUHBFUHFLMUNUOFCUNABFJZFEGZTCUGUQABFFBENOUP
      UQCABFCDPUQCLQRUOFLUHFCBUAUBUOULCUGUKABCCBENOUCUDUEABESUJCESUF $.

    $( Variable substitution for ""at most one.""  (Contributed by Alexander van
       der Vekens, 17-Jun-2017.) $)
    sb8mo $p |- ( E* x ph <-> E* y [ y / x ] ph ) $=
      ( wex weu wi wsb wmo sb8e sb8eu imbi12i df-mo 3bitr4i ) ABEZABFZGABCHZCEZ
      QCFZGABIQCIORPSABCDJABCDKLABMQCMN $.
  $}

  ${
    cbveu.1 $e |- F/ y ph $.
    cbveu.2 $e |- F/ x ps $.
    cbveu.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 25-Nov-1994.)  (Revised by Mario Carneiro,
       7-Oct-2016.) $)
    cbveu $p |- ( E! x ph <-> E! y ps ) $=
      ( weu wsb sb8eu sbie eubii bitri ) ACHACDIZDHBDHACDEJNBDABCDFGKLM $.
  $}

  ${
    cbvmo.1 $e |- F/ y ph $.
    cbvmo.2 $e |- F/ x ps $.
    cbvmo.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 9-Mar-1995.)  (Revised by Andrew Salmon,
       8-Jun-2011.) $)
    cbvmo $p |- ( E* x ph <-> E* y ps ) $=
      ( wex weu wi wmo cbvex cbveu imbi12i df-mo 3bitr4i ) ACHZACIZJBDHZBDIZJAC
      KBDKQSRTABCDEFGLABCDEFGMNACOBDOP $.
  $}

  ${
    $d x y z $.  $d ph z $.
    mo3.1 $e |- F/ y ph $.
    $( Alternate definition of ""at most one.""  Definition of [BellMachover]
       p. 460, except that definition has the side condition that ` y ` not
       occur in ` ph ` in place of our hypothesis.  (Contributed by NM,
       8-Mar-1995.)  (Proof shortened by Wolf Lammen, 18-Aug-2019.) $)
    mo3 $p |- ( E* x ph <->
               A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $=
      ( vz wmo wsb wa weq wi wal nfmo1 nfmo mo2v sp spsbim equsb3 syl6ib alrimi
      wex anim12d equtr2 syl6 exlimiv sylbi nfs1v pm3.21 imim1d alimd com12 mo2
      aleximi sb8e 3imtr4g moabs sylibr alcoms impbii ) ABFZAABCGZHZBCIZJZCKZBK
      USVDBABLUSVCCACBDMUSABEIZJZBKZETVCABENVGVCEVGVAVECEIZHVBVGAVEUTVHVFBOVGUT
      VEBCGVHAVEBCPCBEQRUABCEUBUCUDUESSVCUSCBVCBKZCKZABTZUSJUSVJUTCTAVBJZBKZCTV
      KUSVIUTVMCUTVIVMUTVCVLBABCUFUTAVAVBUTAUGUHUIUJULABCDUMABCDUKUNABUOUPUQUR
      $.

    $( Obsolete proof of ~ mo3 as of 20-Jul-2019.  (Contributed by NM,
       8-Mar-1995.)  (Revised by Wolf Lammen, 3-Dec-2018.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    mo3OLD $p |- ( E* x ph <->
               A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $=
      ( vz wmo wsb wa weq wi wal wex mo2v nfim nfs1v sbequ2 ax-7 imim12d sylibr
      nfv cbv3 ancli aaan prth equtr2 syl6 2alimi syl exlimiv sylbi pm3.3 com3r
      nfa1 alimd com12 sps eximd sb8e mo2 3imtr4g moabs alcoms impbii ) ABFZAAB
      CGZHZBCIZJZCKBKZVDABEIZJZBKZELVIABEMVLVIEVLVKVECEIZJZHZCKBKZVIVLVLVNCKZHV
      PVLVQVKVNBCAVJCDVJCTNZVEVMBABCOZVMBTNZVGVEAVJVMABCPBCEQRUAUBVKVNBCVRVTUCS
      VOVHBCVOVFVJVMHVGAVJVEVMUDBCEUEUFUGUHUIUJVHVDCBVHBKZCKZABLZVDJVDWBVECLAVG
      JZBKZCLWCVDWBVEWECWACUMWAVEWEJCVEWAWEVEVHWDBVSVHAVEVGAVEVGUKULUNUOUPUQABC
      DURABCDUSUTABVASVBVC $.
  $}

  ${
    $d x y $.
    mo.1 $e |- F/ y ph $.
    $( Equivalent definitions of ""there exists at most one.""  (Contributed by
       NM, 7-Aug-1994.)  (Revised by Mario Carneiro, 7-Oct-2016.)  (Proof
       shortened by Wolf Lammen, 2-Dec-2018.) $)
    mo $p |- ( E. y A. x ( ph -> x = y ) <->
               A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $=
      ( weq wi wal wex wmo wsb wa mo2 mo3 bitr3i ) ABCEZFBGCHABIAABCJKOFCGBGABC
      DLABCDMN $.
  $}

  ${
    $d x y $.
    eu2.1 $e |- F/ y ph $.
    $( An alternate way of defining existential uniqueness.  Definition 6.10 of
       [TakeutiZaring] p. 26.  (Contributed by NM, 8-Jul-1994.)  (Proof
       shortened by Wolf Lammen, 2-Dec-2018.) $)
    eu2 $p |- ( E! x ph <->
    ( E. x ph /\ A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) ) $=
      ( weu wex wmo wa wsb weq wi wal eu5 mo3 anbi2i bitri ) ABEABFZABGZHQAABCI
      HBCJKCLBLZHABMRSQABCDNOP $.
  $}

  ${
    $d x y $.
    eu1.1 $e |- F/ y ph $.
    $( An alternate way to express uniqueness used by some authors.  Exercise
       2(b) of [Margaris] p. 110.  (Contributed by NM, 20-Aug-1993.)  (Revised
       by Mario Carneiro, 7-Oct-2016.)  (Proof shortened by Wolf Lammen,
       29-Oct-2018.) $)
    eu1 $p |- ( E! x ph <->
                E. x ( ph /\ A. y ( [ y / x ] ph -> x = y ) ) ) $=
      ( wsb weu weq wb wal wi wa nfs1v sb8eu sb6rf equcom imbi2i albii anbi12ci
      wex euf albiim bitr4i exbii 3bitr4i ) ABCEZCFUECBGZHCIZBSABFAUEBCGZJZCIZK
      ZBSUECBABCLTABCDMUKUGBUKUEUFJZCIZUFUEJCIZKUGAUNUJUMABCDNUIULCUHUFUEBCOPQR
      UEUFCUAUBUCUD $.
  $}

  ${
    $d x y $.  $d ph y $.
    $( Alternate proof of ~ euex .  Shorter but uses more axioms.  (Contributed
       by NM, 15-Sep-1993.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    euexALT $p |- ( E! x ph -> E. x ph ) $=
      ( vy weu wsb weq wi wal wa wex nfv eu1 exsimpl sylbi ) ABDAABCEBCFGCHZIBJ
      ABJABCACKLAOBMN $.
  $}

  ${
    $d x y $.
    eu3OLD.1 $e |- F/ y ph $.
    $( Obsolete theorem as of 29-May-2018.  Superseded by ~ eu3v that better
       fits common usage pattern.  (Contributed by NM, 8-Jul-1994.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    eu3OLD $p |- ( E! x ph <-> ( E. x ph /\ E. y A. x ( ph -> x = y ) ) ) $=
      ( weu wex wsb wa weq wi wal eu2 mo anbi2i bitr4i ) ABEABFZAABCGHBCIZJCKBK
      ZHPAQJBKCFZHABCDLSRPABCDMNO $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( Obsolete proof of ~ eu5 as of 25-May-2019 (Contributed by NM,
       23-Mar-1995.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    eu5OLD $p |- ( E! x ph <-> ( E. x ph /\ E* x ph ) ) $=
      ( vy weu wex weq wi wal wa wmo nfv eu3OLD mo2 anbi2i bitr4i ) ABDABEZABCF
      GBHCEZIPABJZIABCACKZLRQPABCSMNO $.
  $}

  ${
    euor.1 $e |- F/ x ph $.
    $( Introduce a disjunct into a uniqueness quantifier.  (Contributed by NM,
       21-Oct-2005.) $)
    euor $p |- ( ( -. ph /\ E! x ps ) -> E! x ( ph \/ ps ) ) $=
      ( wn weu wo nfn biorf eubid biimpa ) AEZBCFABGZCFLBMCACDHABIJK $.
  $}

  ${
    $d x ph $.
    $( Introduce a disjunct into a uniqueness quantifier.  (Contributed by NM,
       23-Mar-1995.) $)
    euorv $p |- ( ( -. ph /\ E! x ps ) -> E! x ( ph \/ ps ) ) $=
      ( nfv euor ) ABCACDE $.
  $}

  $( Introduce or eliminate a disjunct in a uniqueness quantifier.
     (Contributed by NM, 21-Oct-2005.)  (Proof shortened by Andrew Salmon,
     9-Jul-2011.)  (Proof shortened by Wolf Lammen, 27-Dec-2018.) $)
  euor2 $p |- ( -. E. x ph -> ( E! x ( ph \/ ps ) <-> E! x ps ) ) $=
    ( wex wn wo nfe1 nfn wb 19.8a con3i biorf bicomd syl eubid ) ACDZEZABFZBCPC
    ACGHQAEZRBIAPACJKSBRABLMNO $.

  ${
    $d x y $.
    mo2OLD.1 $e |- F/ y ph $.
    $( Obsolete proof of ~ mo2 as of 28-May-2019.  (Contributed by NM,
       8-Mar-1995.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    mo2OLD $p |- ( E* x ph <-> E. y A. x ( ph -> x = y ) ) $=
      ( wmo wex weu wi weq df-mo wn alnex pm2.21 alimi 19.8a sylbir eumo0OLD ja
      wal syl eu3OLD simplbi2com impbii bitri ) ABEABFZABGZHZABCIZHZBSZCFZABJUG
      UKUEUFUKUEKAKZBSZUKABLUMUJUKULUIBAUHMNUJCOTPABCDQRUFUEUKABCDUAUBUCUD $.
  $}

  ${
    $d w x z $.  $d w y z $.  $d w ph $.
    $( Substitution into ""at most one"".  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
    sbmo $p |- ( [ y / x ] E* z ph <-> E* z [ y / x ] ph ) $=
      ( vw weq wi wal wex wsb wmo sbex nfv sblim sbalv exbii bitri mo2v 3bitr4i
      sbbii ) ADEFZGZDHZEIZBCJZABCJZUAGZDHZEIZADKZBCJUFDKUEUCBCJZEIUIUCEBCLUKUH
      EUBUGBCDAUABCUABMNOPQUJUDBCADERTUFDERS $.
  $}

  ${
    $d x y $.  $d y ph $.
    mo4f.1 $e |- F/ x ps $.
    mo4f.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( ""At most one"" expressed using implicit substitution.  (Contributed by
       NM, 10-Apr-2004.) $)
    mo4f $p |- ( E* x ph <-> A. x A. y ( ( ph /\ ps ) -> x = y ) ) $=
      ( wmo wsb wa weq wi wal nfv mo3 sbie anbi2i imbi1i 2albii bitri ) ACGAACD
      HZIZCDJZKZDLCLABIZUBKZDLCLACDADMNUCUECDUAUDUBTBAABCDEFOPQRS $.
  $}

  ${
    $d x y $.  $d y ph $.  $d x ps $.
    mo4.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( ""At most one"" expressed using implicit substitution.  (Contributed by
       NM, 26-Jul-1995.) $)
    mo4 $p |- ( E* x ph <-> A. x A. y ( ( ph /\ ps ) -> x = y ) ) $=
      ( nfv mo4f ) ABCDBCFEG $.
  $}

  ${
    $d x y $.  $d y ph $.  $d x ps $.
    eu4.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Uniqueness using implicit substitution.  (Contributed by NM,
       26-Jul-1995.) $)
    eu4 $p |- ( E! x ph <-> ( E. x ph /\
             A. x A. y ( ( ph /\ ps ) -> x = y ) ) ) $=
      ( weu wex wmo wa weq wi wal eu5 mo4 anbi2i bitri ) ACFACGZACHZIQABICDJKDL
      CLZIACMRSQABCDENOP $.
  $}

  ${
    $d x y $.  $d y ph $.  $d y ps $.
    $( ""At most one"" is preserved through implication (notice wff reversal).
       (Contributed by NM, 22-Apr-1995.) $)
    moim $p |- ( A. x ( ph -> ps ) -> ( E* x ps -> E* x ph ) ) $=
      ( vy wi wal weq wex wmo imim1 al2imi eximdv mo2v 3imtr4g ) ABEZCFZBCDGZEZ
      CFZDHAQEZCFZDHBCIACIPSUADORTCABQJKLBCDMACDMN $.
  $}

  ${
    immoi.1 $e |- ( ph -> ps ) $.
    $( ""At most one"" is preserved through implication (notice wff reversal).
       (Contributed by NM, 15-Feb-2006.) $)
    moimi $p |- ( E* x ps -> E* x ph ) $=
      ( wi wmo moim mpg ) ABEBCFACFECABCGDH $.
  $}

  $( Obsolete theorem as of 22-Dec-2018.  Use ~ moimi applied to ~ ax-1 , as
     demonstrated in the proof.  (Contributed by NM, 28-Jul-1995.)  (Proof
     shortened by Wolf Lammen, 22-Dec-2018.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  morimOLD $p |- ( E* x ( ph -> ps ) -> ( ph -> E* x ps ) ) $=
    ( wi wmo ax-1 moimi a1d ) ABDZCEBCEABICBAFGH $.

  ${
    $d x y $.  $d x y ph $.  $d y ps $.
    $( Obsolete proof of ~ morimOLD as of 22-Dec-2018.  (Contributed by NM,
       28-Jul-1995.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    morimvOLD $p |- ( E* x ( ph -> ps ) -> ( ph -> E* x ps ) ) $=
      ( vy wmo weq wal wex ax-1 a1i imim1d alimdv eximdv nfv mo2 3imtr4g com12
      wi ) AABRZCEZBCEZASCDFZRZCGZDHBUBRZCGZDHTUAAUDUFDAUCUECABSUBBSRABAIJKLMSC
      DSDNOBCDBDNOPQ $.
  $}

  $( Uniqueness implies ""at most one"" through implication.  (Contributed by NM,
     22-Apr-1995.) $)
  euimmo $p |- ( A. x ( ph -> ps ) -> ( E! x ps -> E* x ph ) ) $=
    ( weu wmo wi wal eumo moim syl5 ) BCDBCEABFCGACEBCHABCIJ $.

  $( Add existential uniqueness quantifiers to an implication.  Note the
     reversed implication in the antecedent.  (Contributed by NM,
     19-Oct-2005.)  (Proof shortened by Andrew Salmon, 14-Jun-2011.) $)
  euim $p |- ( ( E. x ph /\ A. x ( ph -> ps ) ) -> ( E! x ps -> E! x ph ) ) $=
    ( wex wi wal wa weu wmo ax-1 euimmo anim12ii eu5 syl6ibr ) ACDZABECFZGBCHZO
    ACIZGACHOQOPROQJABCKLACMN $.

  $( ""At most one"" is still the case when a conjunct is added.  (Contributed by
     NM, 22-Apr-1995.) $)
  moan $p |- ( E* x ph -> E* x ( ps /\ ph ) ) $=
    ( wa simpr moimi ) BADACBAEF $.

  ${
    moani.1 $e |- E* x ph $.
    $( ""At most one"" is still true when a conjunct is added.  (Contributed by
       NM, 9-Mar-1995.) $)
    moani $p |- E* x ( ps /\ ph ) $=
      ( wmo wa moan ax-mp ) ACEBAFCEDABCGH $.
  $}

  $( ""At most one"" is still the case when a disjunct is removed.  (Contributed
     by NM, 5-Apr-2004.) $)
  moor $p |- ( E* x ( ph \/ ps ) -> E* x ph ) $=
    ( wo orc moimi ) AABDCABEF $.

  $( ""At most one"" imports disjunction to conjunction.  (Contributed by NM,
     5-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
  mooran1 $p |- ( ( E* x ph \/ E* x ps ) -> E* x ( ph /\ ps ) ) $=
    ( wmo wa simpl moimi moan jaoi ) ACDABEZCDBCDJACABFGBACHI $.

  $( ""At most one"" exports disjunction to conjunction.  (Contributed by NM,
     5-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
  mooran2 $p |- ( E* x ( ph \/ ps ) -> ( E* x ph /\ E* x ps ) ) $=
    ( wo wmo moor olc moimi jca ) ABDZCEACEBCEABCFBJCBAGHI $.

  ${
    moanim.1 $e |- F/ x ph $.
    $( Introduction of a conjunct into ""at most one"" quantifier.  (Contributed
       by NM, 3-Dec-2001.)  (Proof shortened by Wolf Lammen, 24-Dec-2018.) $)
    moanim $p |- ( E* x ( ph /\ ps ) <-> ( ph -> E* x ps ) ) $=
      ( wa wmo wi ibar mobid biimprcd wex simpl exlimi exmo nsyl4 con1i moan ja
      ori impbii ) ABEZCFZABCFZGAUCUBABUACDABHIJAUCUBUBAUACKZAUBUAACDABLMUDUBUA
      CNSOPBACQRT $.

    $( Introduction of a conjunct into uniqueness quantifier.  (Contributed by
       NM, 19-Feb-2005.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.)
       (Proof shortened by Wolf Lammen, 24-Dec-2018.) $)
    euan $p |- ( E! x ( ph /\ ps ) <-> ( ph /\ E! x ps ) ) $=
      ( wa weu wex euex simpl exlimi syl ibar eubid biimprcd jcai biimpa impbii
      ) ABEZCFZABCFZESATSRCGARCHRACDABIJKATSABRCDABLMZNOATSUAPQ $.
  $}

  ${
    $d x y ph $.  $d y ps $.
    $( Introduction of a conjunct into ""at most one"" quantifier.  (Contributed
       by NM, 23-Mar-1995.) $)
    moanimv $p |- ( E* x ( ph /\ ps ) <-> ( ph -> E* x ps ) ) $=
      ( nfv moanim ) ABCACDE $.
  $}

  $( Nested ""at most one"" quantifiers.  (Contributed by NM, 25-Jan-2006.) $)
  moanmo $p |- E* x ( ph /\ E* x ph ) $=
    ( wmo wa wi id nfmo1 moanim mpbir ancom mobii ) AABCZDZBCLADZBCZOLLELFLABAB
    GHIMNBALJKI $.

  $( Nested ""at most one"" and uniqueness quantifiers.  (Contributed by NM,
     25-Jan-2006.)  (Proof shortened by Wolf Lammen, 27-Dec-2018.) $)
  moaneu $p |- E* x ( ph /\ E! x ph ) $=
    ( wmo wa weu moanmo eumo anim2i moimi ax-mp ) AABCZDZBCAABEZDZBCABFNLBMKAAB
    GHIJ $.

  ${
    $d x ph $.
    $( Introduction of a conjunct into uniqueness quantifier.  (Contributed by
       NM, 23-Mar-1995.) $)
    euanv $p |- ( E! x ( ph /\ ps ) <-> ( ph /\ E! x ps ) ) $=
      ( nfv euan ) ABCACDE $.
  $}

  ${
    $d x y $.  $d y ph $.  $d y ps $.
    $( ""At most one"" picks a variable value, eliminating an existential
       quantifier.  (Contributed by NM, 27-Jan-1997.)  (Proof shortened by Wolf
       Lammen, 17-Sep-2019.) $)
    mopick $p |- ( ( E* x ph /\ E. x ( ph /\ ps ) ) -> ( ph -> ps ) ) $=
      ( vy wmo wa wex wi weq wal mo2v sp pm3.45 aleximi sb56 sylbi syl6 exlimiv
      syl5d imp ) ACEZABFZCGZABHZUAACDIZHZCJZDGUCUDHZACDKUGUHDUGAUEUCBUFCLUGUCU
      EBFZCGZUEBHZUFUBUICAUEBMNUJUKCJUKBCDOUKCLPQSRPT $.

    $( Obsolete proof of ~ mopick as of 15-Sep-2019.  (Contributed by NM,
       27-Jan-1997.)  (Proof shortened by Wolf Lammen, 29-Dec-2018.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    mopickOLD $p |- ( ( E* x ph /\ E. x ( ph /\ ps ) ) -> ( ph -> ps ) ) $=
      ( vy wa wex wmo wsb nfv sb8e sban weq wal mo3 2sp sylbi expd sbequ2 syl8
      wi com4t imp exlimiv impcom ) ABEZCFZACGZABTZUFUECDHZDFUGUHTZUECDUEDIJUIU
      JDUIACDHZBCDHZEUJABCDKUKULUJUGAUKULBUGAUKCDLZULBTUGAUKUMUGAUKEUMTZDMCMUNA
      CDADINUNCDOPQBCDRSUAUBPUCPUD $.
  $}

  $( Existential uniqueness ""picks"" a variable value for which another wff is
     true.  If there is only one thing ` x ` such that ` ph ` is true, and
     there is also an ` x ` (actually the same one) such that ` ph ` and ` ps `
     are both true, then ` ph ` implies ` ps ` regardless of ` x ` .  This
     theorem can be useful for eliminating existential quantifiers in a
     hypothesis.  Compare Theorem *14.26 in [WhiteheadRussell] p. 192.
     (Contributed by NM, 10-Jul-1994.) $)
  eupick $p |- ( ( E! x ph /\ E. x ( ph /\ ps ) ) -> ( ph -> ps ) ) $=
    ( weu wmo wa wex wi eumo mopick sylan ) ACDACEABFCGABHACIABCJK $.

  $( Version of ~ eupick with closed formulas.  (Contributed by NM,
     6-Sep-2008.) $)
  eupicka $p |- ( ( E! x ph /\ E. x ( ph /\ ps ) ) -> A. x ( ph -> ps ) ) $=
    ( weu wa wex wi nfeu1 nfe1 nfan eupick alrimi ) ACDZABEZCFZEABGCMOCACHNCIJA
    BCKL $.

  $( Existential uniqueness ""pick"" showing wff equivalence.  (Contributed by
     NM, 25-Nov-1994.)  (Proof shortened by Wolf Lammen, 27-Dec-2018.) $)
  eupickb $p |- ( ( E! x ph /\ E! x ps /\ E. x ( ph /\ ps ) ) ->
               ( ph <-> ps ) ) $=
    ( weu wa wex w3a wi eupick 3adant2 exancom sylan2b 3adant1 impbid ) ACDZBCD
    ZABECFZGABOQABHPABCIJPQBAHZOQPBAECFRABCKBACILMN $.

  $( Theorem *14.26 in [WhiteheadRussell] p. 192.  (Contributed by Andrew
     Salmon, 11-Jul-2011.)  (Proof shortened by Wolf Lammen, 27-Dec-2018.) $)
  eupickbi $p |- ( E! x ph -> ( E. x ( ph /\ ps ) <-> A. x ( ph -> ps ) ) ) $=
    ( weu wa wex wi wal eupicka ex euex exintr syl5com impbid ) ACDZABECFZABGCH
    ZOPQABCIJOACFQPACKABCLMN $.

  $( ""At most one"" can show the existence of a common value.  In this case we
     can infer existence of conjunction from a conjunction of existence, and it
     is one way to achieve the converse of ~ 19.40 .  (Contributed by NM,
     5-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
  mopick2 $p |- ( ( E* x ph /\ E. x ( ph /\ ps ) /\ E. x ( ph /\ ch ) ) ->
                E. x ( ph /\ ps /\ ch ) ) $=
    ( wmo wa wex w3a nfmo1 nfe1 mopick ancld anim1d df-3an syl6ibr eximd 3impia
    nfan ) ADEZABFZDGZACFZDGABCHZDGSUAFZUBUCDSUADADITDJRUDUBTCFUCUDATCUDABABDKL
    MABCNOPQ $.

  ${
    moexex.1 $e |- F/ y ph $.
    $( ""At most one"" double quantification.  (Contributed by NM, 3-Dec-2001.)
       (Proof shortened by Wolf Lammen, 28-Dec-2018.) $)
    moexex $p |- ( ( E* x ph /\ A. x E* y ps ) -> E* y E. x ( ph /\ ps ) ) $=
      ( wmo wal wa wex wi nfmo1 nfa1 nfe1 nfmo nfim mopick ex com23 alrimd moim
      spsd syl6 exlimd wn nfex exsimpl exlimi exmo ori nsyl4 con1i a1d pm2.61d1
      imp ) ACFZBDFZCGZABHZCIZDFZUOACIZUQUTJZUOAVBCACKUQUTCUPCLUSCDURCMNOUOAUSB
      JZDGZVBUOAVCDADCENEUOUSABUOUSABJABCPQRSVDUPUTCUSBDTUAUBUCVAUDUTUQUTVAUSDI
      ZVAUTUSVADADCEUEABCUFUGVEUTUSDUHUIUJUKULUMUN $.
  $}

  ${
    $d y ph $.
    $( ""At most one"" double quantification.  (Contributed by NM,
       26-Jan-1997.) $)
    moexexv $p |- ( ( E* x ph /\ A. x E* y ps ) -> E* y E. x ( ph /\ ps ) ) $=
      ( nfv moexex ) ABCDADEF $.
  $}

  $( Double quantification with ""at most one.""  (Contributed by NM,
     3-Dec-2001.) $)
  2moex $p |- ( E* x E. y ph -> A. y E* x ph ) $=
    ( wex wmo nfe1 nfmo 19.8a moimi alrimi ) ACDZBEABECKCBACFGAKBACHIJ $.

  $( Double quantification with existential uniqueness.  (Contributed by NM,
     3-Dec-2001.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
  2euex $p |- ( E! x E. y ph -> E. y E! x ph ) $=
    ( wex weu wmo wa eu5 excom nfe1 19.8a moimi df-mo sylib eximd syl5bi impcom
    nfmo wi sylbi ) ACDZBEUABDZUABFZGABEZCDZUABHUCUBUEUBABDZCDUCUEABCIUCUFUDCUA
    CBACJRUCABFUFUDSAUABACKLABMNOPQT $.

  $( Double quantification with existential uniqueness and ""at most one.""
     (Contributed by NM, 3-Dec-2001.) $)
  2eumo $p |- ( E! x E* y ph -> E* x E! y ph ) $=
    ( weu wmo wi euimmo eumo mpg ) ACDZACEZFKBDJBEFBJKBGACHI $.

  $( Double existential uniqueness.  (Contributed by NM, 3-Dec-2001.) $)
  2eu2ex $p |- ( E! x E! y ph -> E. x E. y ph ) $=
    ( weu wex euex eximi syl ) ACDZBDIBEACEZBEIBFIJBACFGH $.

  $( A condition allowing swap of ""at most one"" and existential quantifiers.
     (Contributed by NM, 10-Apr-2004.) $)
  2moswap $p |- ( A. x E* y ph -> ( E* x E. y ph -> E* y E. x ph ) ) $=
    ( wmo wal wex wa nfe1 moexex expcom 19.8a pm4.71ri exbii mobii syl6ibr ) AC
    DBEZACFZBDZQAGZBFZCDZABFZCDRPUAQABCACHIJUBTCASBAQACKLMNO $.

  $( A condition allowing swap of uniqueness and existential quantifiers.
     (Contributed by NM, 10-Apr-2004.) $)
  2euswap $p |- ( A. x E* y ph -> ( E! x E. y ph -> E! y E. x ph ) ) $=
    ( wmo wal wex wa weu wi excomim a1i 2moswap anim12d eu5 3imtr4g ) ACDBEZACF
    ZBFZQBDZGABFZCFZTCDZGQBHTCHPRUASUBRUAIPABCJKABCLMQBNTCNO $.

  $( Double existential uniqueness implies double uniqueness quantification.
     (Contributed by NM, 3-Dec-2001.)  (Proof shortened by Mario Carneiro,
     22-Dec-2016.) $)
  2exeu $p |- ( ( E! x E. y ph /\ E! y E. x ph ) -> E! x E! y ph ) $=
    ( wex weu wa wmo eumo euex moimi syl 2euex anim12ci eu5 sylibr ) ACDZBEZABD
    CEZFACEZBDZSBGZFSBEQUARTQPBGUAPBHSPBACIJKACBLMSBNO $.

  ${
    $d x y z w $.  $d z w ph $.
    $( This theorem extends the idea of ""at most one"" to expressions in two set
       variables (""at most one pair ` x ` and ` y ` "".  Note: this is not
       expressed by ` E* x E* y ph ` ). ~ 2eu4 relates this extension to double
       existential uniqueness, if at least one pair exists.  (Contributed by
       Wolf Lammen, 26-Oct-2019.) $)
    2mo2 $p |- ( ( E* x E. y ph /\ E* y E. x ph ) <->
               E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) ) $=
      ( wex weq wi wal wmo eeanv jcab 2albii 19.26-2 19.23v albii alcom anbi12i
      wa mo2v bitri 3bitri 2exbii 3bitr4ri ) ACFZBDGZHZBIZABFZCEGZHZCIZSZEFDFUH
      DFZULEFZSAUFUJSHZCIBIZEFDFUEBJZUICJZSUHULDEKUQUMDEUQAUFHZAUJHZSZCIBIUTCIZ
      BIZVACIBIZSUMUPVBBCAUFUJLMUTVABCNVDUHVEULVCUGBAUFCOPVEVABIZCIULVABCQVFUKC
      AUJBOPUARUBUCURUNUSUOUEBDTUICETRUD $.
  $}

  ${
    $d x y z w $.  $d z w ph $.
    $( Two equivalent expressions for double ""at most one.""  (Contributed by
       NM, 2-Feb-2005.)  (Revised by Mario Carneiro, 17-Oct-2016.)  (Proof
       shortened by Wolf Lammen, 2-Nov-2019.) $)
    2mo $p |- ( E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) <->
              A. x A. y A. z A. w ( ( ph /\ [ z / x ] [ w / y ] ph ) ->
                   ( x = z /\ y = w ) ) ) $=
      ( weq wa wi wal wex wsb wmo nfmo1 nfe1 nfmo nfan 19.8a spsbe sbimi nfv wn
      2mo2 biimpi 19.21bbi syl2ani sbcom2 sylbi anim12ii alrimi alrimivv sylbir
      nfs1v nfsb pm3.21 imim1d alimd com12 aleximi 2nexaln 2sb8e xchnxbi pm2.21
      mo3 2alimi 2eximi 19.23bi pm2.61d1 impbii alrot4 bitri ) ABDFZCEFZGZHZCIZ
      BIZEJZDJZAACEKZBDKZGZVMHZCIZBIZEIZDIZWBEIDICIBIVRWFVRACJZBLZABJZCLZGZWFAB
      CDEUBWKWDDEWKWCBWHWJBWGBMWIBCABNOPWKWBCWHWJCWGCBACNOWICMPWHWAVKWJVLAWHWGW
      GBDKZVKVTACQVSWGBDACERSWHWGWLGVKHZBDWHWMDIBIWGBDWGDTVCUCUDUEAWJWIWICEKZVL
      VTABQVTABDKZCEKWNACEBDUFWOWICEABDRSUGWJWIWNGVLHZCEWJWPEICIWICEWIETVCUCUDU
      EUHUIUIUJUKWFVTEJZDJZVRWEWQVQDWDVTVPEVTWDVPVTWCVOBVSBDULVTWBVNCVSBDCACEUL
      UMVTAWAVMVTAUNUOUPUPUQURURWRUAAUAZCIBIZVRWGBJWTWRABCUSABCDEUTVAWTVREWTEJV
      RDWTVPDEWSVNBCAVMVBVDVEVFVFUGVGVHWBDEBCVIVJ $.
  $}

  ${
    $d x y z w $.  $d z w ph $.
    $( Obsolete proof of ~ 2mo as of 2-Nov-2019.  (Contributed by NM,
       2-Feb-2005.)  (Revised by Mario Carneiro, 17-Oct-2016.)  (Proof
       shortened by Wolf Lammen, 25-Oct-2019.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    2moOLD $p |- ( E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) <->
              A. x A. y A. z A. w ( ( ph /\ [ z / x ] [ w / y ] ph ) ->
                   ( x = z /\ y = w ) ) ) $=
      ( weq wa wal wex wsb wmo nfmo1 nfe1 nfmo nfan 19.8a spsbe sbimi anim12i
      wi 2mo2 nfv mo3 biimpi 19.21bbi syl5com sbcom2 sylbi anim12d com12 alrimi
      alrimivv sylbir nfs1v nfsb pm3.21 imim1d alimd aleximi 2nexaln 2exsb 2sb6
      2exbii bitr4i xchnxbi pm2.21 2alimi 2eximi 19.23bi pm2.61d1 impbii alrot4
      wn bitri ) ABDFZCEFZGZTZCHZBHZEIZDIZAACEJZBDJZGZVQTZCHZBHZEHZDHZWFEHDHCHB
      HWBWJWBACIZBKZABIZCKZGZWJABCDEUAWOWHDEWOWGBWLWNBWKBLWMBCABMNOWOWFCWLWNCWK
      CBACMNWMCLOWEWOVQWEWLVOWNVPWEWKWKBDJZGZWLVOAWKWDWPACPWCWKBDACEQRSWLWQVOTZ
      BDWLWRDHBHWKBDWKDUBUCUDUEUFWEWMWMCEJZGZWNVPAWMWDWSABPWDABDJZCEJWSACEBDUGX
      AWMCEABDQRUHSWNWTVPTZCEWNXBEHCHWMCEWMEUBUCUDUEUFUIUJUKUKULUMWJWDEIZDIZWBW
      IXCWADWHWDVTEWDWHVTWDWGVSBWCBDUNWDWFVRCWCBDCACEUNUOWDAWEVQWDAUPUQURURUJUS
      USXDVMAVMZCHBHZWBWKBIZXFXDABCUTXGVQATCHBHZEIDIXDABCDEVAWDXHDEABCDEVBVCVDV
      EXFWBEXFEIWBDXFVTDEXEVRBCAVQVFVGVHVIVIUHVJVKWFDEBCVLVN $.
  $}

  ${
    $d z w ph $.  $d x y ps $.  $d x y z w $.
    2mos.1 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Double ""exists at most one"", using implicit substitution.  (Contributed
       by NM, 10-Feb-2005.) $)
    2mos $p |- ( E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) <->
             A. x A. y A. z A. w ( ( ph /\ ps ) -> ( x = z /\ y = w ) ) ) $=
      ( weq wa wi wal wex wsb 2mo nfv sbiedv sbie anbi2i imbi1i 2albii bitri )
      ACEHZDFHIZJDKCKFLELAADFMZCEMZIZUCJZFKEKZDKCKABIZUCJZFKEKZDKCKACDEFNUHUKCD
      UGUJEFUFUIUCUEBAUDBCEBCOUBABDFGPQRSTTUA $.
  $}

  $( Double existential uniqueness.  This theorem shows a condition under which
     a ""naive"" definition matches the correct one.  (Contributed by NM,
     3-Dec-2001.)  (Proof shortened by Wolf Lammen, 11-Nov-2019.) $)
  2eu1 $p |- ( A. x E* y ph ->
        ( E! x E! y ph <-> ( E! x E. y ph /\ E! y E. x ph ) ) ) $=
    ( wmo wal weu wex wa wi 2eu2ex df-mo albii euim syl5bi pm2.43b 2euswap syld
    ex syl jcad 2exeu impbid1 ) ACDZBEZACFZBFZACGZBFZABGCFZHUDUFUHUIUDUFUHUFUGB
    GZUDUFUHIZIABCJUDUGUEIZBEZUJUKUCULBACKLUJUMUKUGUEBMRNSOZUDUFUHUIUNABCPQTABC
    UAUB $.

  $( Obsolete proof of ~ 2eu1 as of 11-Nov-2019.  (Contributed by NM,
     3-Dec-2001.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  2eu1OLD $p |- ( A. x E* y ph ->
        ( E! x E! y ph <-> ( E! x E. y ph /\ E! y E. x ph ) ) ) $=
    ( wmo wal weu wex wa wi eu5 exbii mobii anbi12i bitri simprbi anim2i ancoms
    sp sylib com12 moimi nfa1 moanim ancrd 2moswap imdistani syl6 syl excom jca
    2eu2ex jctild an4 syl6ibr 2exeu impbid1 ) ACDZBEZACFZBFZACGZBFZABGZCFZHZUTU
    RVEUTURVABGZVCCGZHZVABDZVCCDZHZHZVEUTURVKVHUTVAUQHZBDZURVKIUTVMBGZVNUTUSBGZ
    USBDZHVOVNHUSBJVPVOVQVNUSVMBACJZKUSVMBVRLMNOVNURVIURHVKVNURVIVNURVAHZBDURVI
    IVSVMBVAURVMURUQVAUQBRPQUAURVABUQBUBUCSUDVIURVJURVIVJABCUETUFUGUHUTVFVGABCU
    KZUTVFVGVTABCUISUJULVEVFVIHZVGVJHZHVLVBWAVDWBVABJVCCJMVFVIVGVJUMNUNTABCUOUP
    $.

  $( Double existential uniqueness.  (Contributed by NM, 3-Dec-2001.) $)
  2eu2 $p |- ( E! y E. x ph -> ( E! x E! y ph <-> E! x E. y ph ) ) $=
    ( wex weu wmo wal wi eumo 2moex 2eu1 simpl syl6bi 3syl 2exeu expcom impbid
    wa ) ABDZCEZACEBEZACDBEZTSCFACFBGZUAUBHSCIACBJUCUAUBTRUBABCKUBTLMNUBTUAABCO
    PQ $.

  $( Double existential uniqueness.  (Contributed by NM, 3-Dec-2001.) $)
  2eu3 $p |- ( A. x A. y ( E* x ph \/ E* y ph ) ->
 ( ( E! x E! y ph /\ E! y E! x ph ) <-> ( E! x E. y ph /\ E! y E. x ph ) ) ) $=
    ( wmo wo wal weu wa wex wb nfmo1 19.31 albii nfal 19.32 bitri wi 2eu1 2exeu
    biimpd ancom syl6ib adantld adantrd jaoi ancoms jca impbid1 sylbi ) ABDZACD
    ZECFZBFZUJCFZUKBFZEZACGBGZABGCGZHZACIBGZABICGZHZJUMUNUKEZBFUPULVCBUJUKCACKL
    MUNUKBUJBCABKNOPUPUSVBUNUSVBQUOUNURVBUQUNURVAUTHZVBUNURVDACBRTVAUTUAUBUCUOU
    QVBURUOUQVBABCRTUDUEVBUQURABCSVAUTURACBSUFUGUHUI $.

  ${
    $d x y z w $.  $d z w ph $.
    $( This theorem provides us with a definition of double existential
       uniqueness (""exactly one ` x ` and exactly one ` y ` "").  Naively one
       might think (incorrectly) that it could be defined by
       ` E! x E! y ph ` .  See ~ 2eu1 for a condition under which the naive
       definition holds and ~ 2exeu for a one-way implication.  See ~ 2eu5 and
       ~ 2eu8 for alternate definitions.  (Contributed by NM, 3-Dec-2001.)
       (Proof shortened by Wolf Lammen, 14-Sep-2019.) $)
    2eu4 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <->
      ( E. x E. y ph /\ E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) ) ) $=
      ( wex weu wa wmo weq wi wal excom anbi1i bitri anbi12i anandi 2mo2 anbi2i
      eu5 3bitr2i ) ACFZBGZABFZCGZHUBBFZUBBIZHZUFUDCIZHZHUFUGUIHZHUFABDJCEJHKCL
      BLEFDFZHUCUHUEUJUBBTUEUDCFZUIHUJUDCTUMUFUIACBMNOPUFUGUIQUKULUFABCDERSUA
      $.

    $( Obsolete proof of ~ 2eu4 as of 14-Sep-2019.  (Contributed by NM,
       3-Dec-2001.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    2eu4OLD $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <->
      ( E. x E. y ph /\ E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) ) ) $=
      ( wex weu wa weq wi wal eu3v anbi12i anbi2i bitri 19.26 nfa1 albii bitr4i
      19.3 an4 excom anidm jcab bitr2i alcom 19.23v 2albii nfe1 nfv nfim 3bitri
      aaan 2exbii eeanv ) ACFZBGZABFZCGZHUPBFZUPBDIZJZBKZDFZHZURCFZURCEIZJZCKZE
      FZHZHUTVFHZVDVJHZHUTAVAVGHJZCKZBKZEFDFZHUQVEUSVKUPBDLURCELMUTVDVFVJUAVLUT
      VMVQVLUTUTHUTVFUTUTACBUBNUTUCOVQVCVIHZEFDFVMVPVRDEVPAVAJZCKZAVGJZBKZHZCKZ
      BKZVBVHHZCKBKVRVPVTWACKZBKZHZBKZWEWJVTBKZWHBKZHZVPVTWHBPWMWKWHHZVPWLWHWKW
      HBWGBQTNVPVTWGHZBKWNVOWOBVOVSWAHZCKWOVNWPCAVAVGUDRVSWACPORVTWGBPOSUEWDWIB
      WDVTCKZWBCKZHWIVTWBCPWQVTWRWHVTCVSCQTWACBUFMORSWCWFBCVTVBWBVHAVACUGAVGBUG
      MUHVBVHBCUPVACACUIVACUJUKURVGBABUIVGBUJUKUMULUNVCVIDEUOUEMUL $.

    $( An alternate definition of double existential uniqueness (see ~ 2eu4 ).
       A mistake sometimes made in the literature is to use ` E! x E! y ` to
       mean ""exactly one ` x ` and exactly one ` y ` .""  (For example, see
       Proposition 7.53 of [TakeutiZaring] p. 53.)  It turns out that this is
       actually a weaker assertion, as can be seen by expanding out the formal
       definitions.  This theorem shows that the erroneous definition can be
       repaired by conjoining ` A. x E* y ph ` as an additional condition.  The
       correct definition apparently has never been published.  ( ` E* ` means
       ""exists at most one."") (Contributed by NM, 26-Oct-2003.) $)
    2eu5 $p |- ( ( E! x E! y ph /\ A. x E* y ph ) <->
      ( E. x E. y ph /\ E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) ) ) $=
      ( weu wmo wal wa wex weq 2eu1 pm5.32ri eumo adantl 2moex syl pm4.71i 2eu4
      wi 3bitr2i ) ACFBFZACGBHZIACJZBFZABJZCFZIZUCIUHUDBJABDKCEKITCHBHEJDJIUCUB
      UHABCLMUHUCUHUFCGZUCUGUIUEUFCNOACBPQRABCDESUA $.
  $}

  ${
    $d x y z w $.  $d z w ph $.
    $( Two equivalent expressions for double existential uniqueness.
       (Contributed by NM, 2-Feb-2005.)  (Revised by Mario Carneiro,
       17-Oct-2016.)  (Proof shortened by Wolf Lammen, 2-Oct-2019.) $)
    2eu6 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <->
               E. z E. w A. x A. y ( ph <-> ( x = z /\ y = w ) ) ) $=
      ( wex weu wa weq wi wal wb 2eu4 imim2i sps exlimd syli wsb 2alimi 2eximi
      nfia1 nfa1 nfv simpl ax12v com12 spsd nfs1v sbequ1 imim2d al2imi sb6 2sb6
      simpr bitr3i syl6ib sylcom ancld 2albiim syl6ibr exlimi 2eximdv imp 2exsb
      bi2 sylibr bi1 jca impbii bitri ) ACFZBGABFCGHVKBFZABDIZCEIZHZJZCKZBKZEFD
      FZHZAVOLZCKZBKZEFDFZABCDEMVTWDVLVSWDVLVRWCDEVKVRWCJBVQWBBUAVKVRVRVOAJZCKB
      KZHWCVKVRWFVKVRVMVKJZBKZWFVKVQWHBVQVKWHVKVQVMWHVQAVMCVPCUBZVMCUCVPAVMJCVO
      VMAVMVNUDNOPVKBDUEQUFUGVRWHVMACERZJZBKZWFVQWGWKBVQVKWJVMVQAWJCWIACEUHVPAW
      JJCAVPVNWJVOVNAVMVNUNNACEUIQOPUJUKWLWJBDRWFWJBDULABCDEUMUOUPUQURAVOBCUSUT
      VAVBVCWDVLVSWDWFEFDFVLWCWFDEWAWEBCAVOVESTABCDEVDVFWCVRDEWAVPBCAVOVGSTVHVI
      VJ $.
  $}

  ${
    $d x y z w v u $.  $d z w v u ph $.
    $( Obsolete proof of ~ 2eu6 as of 21-Sep-2019.  (Contributed by NM,
       2-Feb-2005.)  (Revised by Mario Carneiro, 17-Oct-2016.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    2eu6OLD $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <->
               E. z E. w A. x A. y ( ph <-> ( x = z /\ y = w ) ) ) $=
      ( vu vv wex wa weq wal wsb nfv nfsb sbequ12 equequ2 bi2anan9 nfim bitri
      wi weu 2eu4 nfs1v sylan9bbr cbvex2 imbi2d 2albidv cbvex2v equequ1 imbi12d
      cbval2 2exbii 2mo 19.29r2 syl2anb 2albiim ancom sbco2 sbbii sbcom2 bitr3i
      nfan syl6bb anbi2d equcom anbi12i imbi2i impexp 2albii anbi2i abai bitr4i
      wb 19.21-2 2sb6 anbi1i sylibr bi2 2alimi 2eximi 2exsb bi1 jca impbii ) AC
      HZBUAABHCUAIWEBHZABDJZCEJZIZTZCKBKZEHDHZIZAWIVMZCKBKZEHDHZABCDEUBWMWPWMAC
      ELZBDLZWRWREFLZDGLZIZDGJZEFJZIZTZFKGKZIZEHDHZWPWFWREHDHXFEKDKZXHWLAWRBCDE
      ADMAEMZWQBDUCZWQBDCACEUCNZWHAWQWGWRACEOWQBDOUDZUEWLABGJZCFJZIZTZCKBKZFHGH
      ZXIWKXRDEGFXDWJXQBCXDWIXPAXBWGXNXCWHXODGBPEFCPQUFUGUHXSWRXDTZEKDKZFHGHXIX
      RYAGFXQXTBCDEXQDMXQEMWRXDBXKXDBMZRWRXDCXLXDCMZRWIAWRXPXDXMWGXNXBWHXOXCBDG
      UICEFUIQUJUKULWRDEGFUMSSWRXFDEUNUOWPWIATZCKBKZWKIZEHDHXHWOYFDEWOWKYEIYFAW
      IBCUPWKYEUQSULXGYFDEXGWRWKIZYFXGWRWRWKTZIYGXFYHWRXFWRWJTZCKBKZYHXFWRAIZDB
      JZECJZIZTZCKBKYJYOXEBCGFYOGMYOFMXAXDBWRWTBXKWSDGBWREFBXKNNVBYBRXAXDCWRWTC
      XLWSDGCWREFCXLNNVBYCRXPYKXAYNXDXPAWTWRXPAACFLZBGLZWTXOAYPXNYQACFOYPBGOUDY
      QWQEFLZBGLZWTYRYPBGACFEXJURUSYSYRBDLZDGLWTYRBGDYRDMURYTWSDGWQEFBDUTUSVAVA
      VCVDXNYLXBXOYMXCBGDPCFEPQUJUKYOYIBCYOYKWITYIYNWIYKYLWGYMWHDBVEECVEVFVGWRA
      WIVHSVIVAWRWJBCXKXLVNSVJWRWKVKVLWRYEWKABCDEVOVPSULVLVQWPWFWLWPYEEHDHWFWOY
      EDEWNYDBCAWIVRVSVTABCDEWAVQWOWKDEWNWJBCAWIWBVSVTWCWDS $.
  $}

  $( Two equivalent expressions for double existential uniqueness.
     (Contributed by NM, 19-Feb-2005.) $)
  2eu7 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <->
             E! x E! y ( E. x ph /\ E. y ph ) ) $=
    ( wex weu wa nfe1 nfeu euan ancom eubii 3bitri 3bitr4ri ) ABDZCEZACDZFZBEOP
    BEZFNPFZCEZBEROFOPBNBCABGHITQBTPNFZCEPOFQSUACNPJKPNCACGIPOJLKROJM $.

  $( Two equivalent expressions for double existential uniqueness.  Curiously,
     we can put ` E! ` on either of the internal conjuncts but not both.  We
     can also commute ` E! x E! y ` using ~ 2eu7 .  (Contributed by NM,
     20-Feb-2005.) $)
  2eu8 $p |- ( E! x E! y ( E. x ph /\ E. y ph ) <->
                E! x E! y ( E! x ph /\ E. y ph ) ) $=
    ( wex wa 2eu2 pm5.32i nfeu1 nfeu euan ancom eubii nfe1 3bitri 3bitr4ri 2eu7
    weu 3bitr3ri ) ACDZBQZABQZCQZEZTABDZCQZEUASEZCQZBQZUDSECQBQTUBUEACBFGUBSEZB
    QUBTEUHUCUBSBUABCABHIJUGUIBUGSUAEZCQSUBEUIUFUJCUASKLSUACACMJSUBKNLTUBKOABCP
    R $.

  ${
    $d x y z $.
    $( Obsolete proof of ~ euequ1 as of 8-Sep-2019.  (Contributed by Stefan
       Allan, 4-Dec-2008.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    euequ1OLD $p |- E! x x = y $=
      ( vz weq weu wex wa wi wal ax6ev equtr2 gen2 equequ1 eu4 mpbir2an ) ABDZA
      EPAFPCBDZGACDHZCIAIABJRACACBKLPQACACBMNO $.
  $}

  ${
    $d x y $.
    $( Two ways to express ""only one thing exists.""  The left-hand side
       requires only one variable to express this.  Both sides are false in set
       theory; see theorem ~ dtru .  (Contributed by NM, 5-Apr-2004.) $)
    exists1 $p |- ( E! x x = x <-> A. x x = y ) $=
      ( weq weu wb wal wex df-eu equid tbt bicom bitri albii exbii nfae 3bitr2i
      19.9 ) AACZADRABCZEZAFZBGSAFZBGUBRABHUBUABSTASSRETRSAIJSRKLMNUBBABBOQP $.

    $( A condition implying that at least two things exist.  (Contributed by
       NM, 10-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
    exists2 $p |- ( ( E. x ph /\ E. x -. ph ) -> -. E! x x = x ) $=
      ( vy wex wn weq weu nfeu1 nfa1 wi exists1 axc16 sylbi exlimd com12 syl6ib
      wal alex con2d imp ) ABDZAEBDZBBFZBGZEUAUDUBUAUDABQZUBEUDUAUEUDAUEBUCBHAB
      IUDBCFBQAUEJBCKABCLMNOABRPST $.
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
             Other axiomatizations related to classical predicate calculus
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Predicate calculus with all distinct variables
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y z $.
    $( Distinct variable version of ~ ax-11 .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)
    ax-7d $a |- ( A. x A. y ph -> A. y A. x ph ) $.

    $( Distinct variable version of ~ ax-7 .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)
    ax-8d $a |- ( x = y -> ( x = z -> y = z ) ) $.

    $( Distinct variable version of ~ ax-6 , equal variables case.
       (Contributed by Mario Carneiro, 14-Aug-2015.) $)
    ax-9d1 $a |- -. A. x -. x = x $.

    $( Distinct variable version of ~ ax-6 , distinct variables case.
       (Contributed by Mario Carneiro, 14-Aug-2015.) $)
    ax-9d2 $a |- -. A. x -. x = y $.

    $( Distinct variable version of ~ axc11n .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)
    ax-10d $a |- ( A. x x = y -> A. y y = x ) $.

    $( Distinct variable version of ~ ax-12 .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)
    ax-11d $a |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
               Aristotelian logic: Assertic syllogisms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Model the Aristotelian assertic syllogisms using modern notation.
  This section shows that the Aristotelian assertic syllogisms can be proven
  with our axioms of logic, and also provides generally useful theorems.

  In antiquity Aristotelian logic and Stoic logic
  (see ~ mptnan ) were the leading logical systems.
  Aristotelian logic became the leading system in medieval Europe;
  this section models this system (including later refinements to it).
  Aristotle defined syllogisms very generally
  (""a discourse in which certain (specific) things having been supposed,
  something different from the things supposed results of necessity
  because these things are so"")
  Aristotle, _Prior Analytics_ 24b18-20.
  However, in _Prior Analytics_ he limits himself to
  categorical syllogisms that consist of three categorical propositions
  with specific structures.  The syllogisms are the valid subset of
  the possible combinations of these structures.
  The medieval schools used vowels to identify the types of terms
  (a=all, e=none, i=some, and o=some are not), and named the different
  syllogisms with Latin words that had the vowels in the intended order.

  ""There is a surprising amount of scholarly debate
  about how best to formalize Aristotle's syllogisms..."" according to
  _Aristotle's Modal Proofs: Prior Analytics A8-22 in Predicate Logic_,
  Adriane Rini, Springer, 2011, ISBN 978-94-007-0049-9, page 28.
  For example, Lukasiewicz believes it is important to note that
  ""Aristotle does not introduce singular terms or premisses into his system"".
  Lukasiewicz also believes that Aristotelian syllogisms are
  predicates (having a true/false value), not inference rules:
  ""The characteristic sign of an inference is the word 'therefore'...
  no syllogism is formulated by Aristotle primarily as an inference,
  but they are all implications.""
  Jan Lukasiewicz, _Aristotle's Syllogistic from the Standpoint of
  Modern Formal Logic_, Second edition, Oxford, 1957, page 1-2.
  Lukasiewicz devised a specialized prefix notation for representing
  Aristotelian syllogisms instead of using standard predicate logic notation.

  We instead translate each Aristotelian syllogism into an inference rule,
  and each rule is defined using standard predicate logic notation and
  predicates.  The predicates are represented by wff variables
  that may depend on the quantified variable ` x ` .
  Our translation is essentially identical to the one
  use in Rini page 18, Table 2 ""Non-Modal Syllogisms in
  Lower Predicate Calculus (LPC)"", which uses
  standard predicate logic with predicates.  Rini states,
  ""the crucial point is that we capture the meaning Aristotle intends,
  and the method by which we represent that meaning is less important.""
  There are two differences: we make the existence criteria explicit, and
  we use ` ph ` , ` ps ` , and ` ch ` in the order they appear
  (a common Metamath convention).
  Patzig also uses standard predicate logic notation and predicates
  (though he interprets them as conditional propositions, not as
  inference rules); see
  Gunther Patzig, _Aristotle's Theory of the Syllogism_ second edition, 1963,
  English translation by Jonathan Barnes, 1968, page 38.
  Terms such as ""all"" and ""some"" are translated into predicate logic
  using the approach devised by Frege and Russell.
  ""Frege (and Russell) devised an ingenious procedure for regimenting
  binary quantifiers like ""every"" and ""some"" in terms of unary quantifiers
  like ""everything"" and ""something"": they formalized sentences of the form
  ""Some A is B"" and ""Every A is B"" as
  exists x (Ax and Bx) and all x (Ax implies Bx), respectively.""
  ""Quantifiers and Quantification"", _Stanford Encyclopedia of Philosophy_,
  ~ http://plato.stanford.edu/entries/quantification/ .
  See _Principia Mathematica_ page 22 and *10 for more information
  (especially *10.3 and *10.26).

  Expressions of the form ""no ` ph ` is ` ps ` "" are consistently translated as
  ` A. x ( ph -> -. ps ) ` .  These can also be expressed as
  ` -. E. x ( ph /\ ps ) ` , per ~ alinexa .
  We translate ""all ` ph ` is ` ps ` "" to ` A. x ( ph -> ps ) ` ,
  ""some ` ph ` is ` ps ` "" to ` E. x ( ph /\ ps ) ` , and
  ""some ` ph ` is not ` ps ` "" to ` E. x ( ph /\ -. ps ) ` .
  It is traditional to use the singular verb ""is"", not the plural
  verb ""are"", in the generic expressions.
  By convention the major premise is listed first.

  In traditional Aristotelian syllogisms the predicates
  have a restricted form (""x is a ...""); those predicates
  could be modeled in modern notation by more specific constructs such as
  ` x = A ` , ` x e. A ` , or ` x C_ A ` .
  Here we use wff variables instead of specialized restricted forms.
  This generalization makes the syllogisms more useful
  in more circumstances.  In addition, these expressions make
  it clearer that the syllogisms of Aristotelian logic are the
  forerunners of predicate calculus.  If we used restricted forms
  like ` x e. A ` instead, we would not only unnecessarily limit
  their use, but we would also need to use set and class axioms,
  making their relationship to predicate calculus less clear.
  Using such specific constructs would also be anti-historical; Aristotle
  and others who directly followed his work focused on relating wholes
  to their parts, an approach now called part-whole theory.
  The work of Cantor and Peano (over 2,000 years later) led to a sharper
  distinction between inclusion ( ` C_ ` ) and membership ( ` e. ` );
  this distinction was not directly made in Aristotle's work.

  There are some widespread misconceptions about the existential
  assumptions made by Aristotle (aka ""existential import"").
  Aristotle was not trying to develop something exactly corresponding
  to modern logic.  Aristotle devised ""a companion-logic for science.
  He relegates fictions like fairy godmothers and mermaids and unicorns to
  the realms of poetry and literature. In his mind, they exist outside the
  ambit of science. This is why he leaves no room for such non-existent
  entities in his logic.  This is a thoughtful choice, not an inadvertent
  omission. Technically, Aristotelian science is a search for definitions,
  where a definition is ""a phrase signifying a thing's essence.""
  (Topics, I.5.102a37, Pickard-Cambridge.)...
  Because non-existent entities cannot be anything, they do not, in
  Aristotle's mind, possess an essence...  This is why he leaves
  no place for fictional entities like goat-stags (or unicorns).""
  Source: Louis F. Groarke, ""Aristotle: Logic"",
  section 7. (Existential Assumptions),
  _Internet Encyclopedia of Philosophy_ (A Peer-Reviewed Academic Resource),
  ~ http://www.iep.utm.edu/aris-log/ .
  Thus, some syllogisms have ""extra"" existence
  hypotheses that do not directly appear in Aristotle's original materials
  (since they were always assumed); they are added where they are needed.
  This affects ~ barbari , ~ celaront , ~ cesaro , ~ camestros , ~ felapton ,
  ~ darapti , ~ calemos , ~ fesapo , and ~ bamalip .

  These are only the _assertic_ syllogisms.
  Aristotle also defined modal syllogisms that deal with modal
  qualifiers such as ""necessarily"" and ""possibly"".
  Historically Aristotelian modal syllogisms were not as widely used.
  For more about modal syllogisms in a modern context, see Rini as well as
  _Aristotle's Modal Syllogistic_ by Marko Malink, Harvard
  University Press, November 2013.  We do not treat them further here.

  Aristotelian logic is essentially the forerunner of predicate calculus
  (as well as set theory since it discusses membership in groups),
  while Stoic logic is essentially the forerunner of propositional calculus.
$)

  $( Figure 1.  Aristotelian syllogisms are grouped by ""figures"",
     which doesn't matter for our purposes but is a reasonable way
     to order them. $)

  ${
    $( Major premise for the Aristotelian syllogism ""Barbara"", e.g.,
       ""All men are mortal"". By convention, the major premise is first. $)
    barbara.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Barbara, e.g., ""Socrates is a man"". $)
    barbara.min $e |- A. x ( ch -> ph ) $.
    $( ""Barbara"", one of the fundamental syllogisms of Aristotelian logic.  All
       ` ph ` is ` ps ` , and all ` ch ` is ` ph ` , therefore all ` ch ` is
       ` ps ` .  (In Aristotelian notation, AAA-1:  MaP and SaM therefore SaP.)
       For example, given ""All men are mortal"" and ""Socrates is a man"", we can
       prove ""Socrates is mortal"".  If H is the set of men, M is the set of
       mortal beings, and S is Socrates, these word phrases can be represented
       as ` A. x ( x e. H -> x e. M ) ` (all men are mortal) and
       ` A. x ( x = S -> x e. H ) ` (Socrates is a man) therefore
       ` A. x ( x = S -> x e. M ) ` (Socrates is mortal).  Russell and
       Whitehead note that the ""syllogism in Barbara is derived..."" from
       ~ syl .  (quote after Theorem *2.06 of [WhiteheadRussell] p. 101).  Most
       of the proof is in ~ alsyl .  There are a legion of sources for Barbara,
       including ~ http://www.friesian.com/aristotl.htm ,
       ~ http://plato.stanford.edu/entries/aristotle-logic/ , and
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 24-Aug-2016.) $)
    barbara $p |- A. x ( ch -> ps ) $=
      ( wi wal alsyl mp2an ) CAGDHABGDHCBGDHFECABDIJ $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism ""Celarent"", e.g.,
       ""No reptiles have fur"". $)
    celarent.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Celarent, e.g., ""All snakes are reptiles"". $)
    celarent.min $e |- A. x ( ch -> ph ) $.
    $( ""Celarent"", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and all ` ch ` is ` ph ` , therefore no ` ch ` is ` ps ` .  (In
       Aristotelian notation, EAE-1:  MeP and SaM therefore SeP.) For example,
       given the ""No reptiles have fur"" and ""All snakes are reptiles"",
       therefore ""No snakes have fur"".  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 24-Aug-2016.)  (Revised by David A. Wheeler, 2-Sep-2016.) $)
    celarent $p |- A. x ( ch -> -. ps ) $=
      ( wn barbara ) ABGCDEFH $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism ""Darii"", e.g.,
       ""All rabbits have fur"". $)
    darii.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Darii, e.g., ""Some pets are rabbits."" $)
    darii.min $e |- E. x ( ch /\ ph ) $.
    $( ""Darii"", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and some ` ch ` is ` ph ` , therefore some ` ch ` is ` ps ` .
       (In Aristotelian notation, AII-1:  MaP and SiM therefore SiP.) For
       example, given ""All rabbits have fur"" and ""Some pets are rabbits"",
       therefore ""Some pets have fur"".  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 24-Aug-2016.) $)
    darii $p |- E. x ( ch /\ ps ) $=
      ( wa wi spi anim2i eximii ) CAGCBGDFABCABHDEIJK $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism ""Ferio"" (""Ferioque""),
       e.g., ""No homework is fun"". $)
    ferio.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Ferio, e.g., ""Some reading is homework."" $)
    ferio.min $e |- E. x ( ch /\ ph ) $.
    $( ""Ferio"" (""Ferioque""), one of the syllogisms of Aristotelian logic.  No
       ` ph ` is ` ps ` , and some ` ch ` is ` ph ` , therefore some ` ch ` is
       not ` ps ` .  (In Aristotelian notation, EIO-1:  MeP and SiM therefore
       SoP.) For example, given ""No homework is fun"" and ""Some reading is
       homework"", therefore ""Some reading is not fun"".  This is essentially a
       logical axiom in Aristotelian logic.  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 24-Aug-2016.)  (Revised by David A. Wheeler, 2-Sep-2016.) $)
    ferio $p |- E. x ( ch /\ -. ps ) $=
      ( wn darii ) ABGCDEFH $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism ""Barbari"", e.g.,
       e.g., ""All men are mortal"". $)
    barbari.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Barbari, e.g., ""All Greeks are men."" $)
    barbari.min $e |- A. x ( ch -> ph ) $.
    $( Existence premise for Barbari, e.g., ""Greeks exist."" $)
    barbari.e $e |- E. x ch $.
    $( ""Barbari"", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , all ` ch ` is ` ph ` , and some ` ch ` exist, therefore some
       ` ch ` is ` ps ` .  (In Aristotelian notation, AAI-1:  MaP and SaM
       therefore SiP.) For example, given ""All men are mortal"", ""All Greeks are
       men"", and ""Greeks exist"", therefore ""Some Greeks are mortal"".  Note the
       existence hypothesis (to prove the ""some"" in the conclusion).  Example
       from ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David
       A. Wheeler, 27-Aug-2016.)  (Revised by David A. Wheeler,
       30-Aug-2016.) $)
    barbari $p |- E. x ( ch /\ ps ) $=
      ( wa wi barbara spi ancli eximii ) CCBHDGCBCBIDABCDEFJKLM $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism ""Celaront"", e.g.,
       e.g., ""No reptiles have fur"". $)
    celaront.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Celaront, e.g., ""All Snakes are reptiles."" $)
    celaront.min $e |- A. x ( ch -> ph ) $.
    $( Existence premise for Celaront, e.g., ""Snakes exist."" $)
    celaront.e $e |- E. x ch $.
    $( ""Celaront"", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ch ` is ` ph ` , and some ` ch ` exist, therefore some
       ` ch ` is not ` ps ` .  (In Aristotelian notation, EAO-1:  MeP and SaM
       therefore SoP.) For example, given ""No reptiles have fur"", ""All snakes
       are reptiles."", and ""Snakes exist."", prove ""Some snakes have no fur"".
       Note the existence hypothesis.  Example from
       ~ https://en.wikipedia.org/wiki/Syllogism .  (Contributed by David A.
       Wheeler, 27-Aug-2016.)  (Revised by David A. Wheeler, 2-Sep-2016.) $)
    celaront $p |- E. x ( ch /\ -. ps ) $=
      ( wn barbari ) ABHCDEFGI $.
  $}

  $( Figure 2 $)

  ${
    $( Major premise for the Aristotelian syllogism ""Cesare"" $)
    cesare.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Cesare $)
    cesare.min $e |- A. x ( ch -> ps ) $.
    $( ""Cesare"", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and all ` ch ` is ` ps ` , therefore no ` ch ` is ` ph ` .  (In
       Aristotelian notation, EAE-2:  PeM and SaM therefore SeP.) Related to
       ~ celarent .  (Contributed by David A. Wheeler, 27-Aug-2016.)  (Revised
       by David A. Wheeler, 13-Nov-2016.) $)
    cesare $p |- A. x ( ch -> -. ph ) $=
      ( wn wi spi nsyl3 ax-gen ) CAGHDABCABGHDEICBHDFIJK $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism ""Camestres"" $)
    camestres.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Camestres $)
    camestres.min $e |- A. x ( ch -> -. ps ) $.
    $( ""Camestres"", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and no ` ch ` is ` ps ` , therefore no ` ch ` is ` ph ` .  (In
       Aristotelian notation, AEE-2:  PaM and SeM therefore SeP.) (Contributed
       by David A. Wheeler, 28-Aug-2016.)  (Revised by David A. Wheeler,
       2-Sep-2016.) $)
    camestres $p |- A. x ( ch -> -. ph ) $=
      ( wn wi spi nsyl ax-gen ) CAGHDCBACBGHDFIABHDEIJK $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism ""Festino"" $)
    festino.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Festino $)
    festino.min $e |- E. x ( ch /\ ps ) $.
    $( ""Festino"", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and some ` ch ` is ` ps ` , therefore some ` ch ` is not
       ` ph ` .  (In Aristotelian notation, EIO-2:  PeM and SiM therefore SoP.)
       (Contributed by David A. Wheeler, 25-Nov-2016.) $)
    festino $p |- E. x ( ch /\ -. ph ) $=
      ( wa wn wi spi con2i anim2i eximii ) CBGCAHZGDFBNCABABHIDEJKLM $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism ""Baroco"" $)
    baroco.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for Baroco $)
    baroco.min $e |- E. x ( ch /\ -. ps ) $.
    $( ""Baroco"", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and some ` ch ` is not ` ps ` , therefore some ` ch ` is not
       ` ph ` .  (In Aristotelian notation, AOO-2:  PaM and SoM therefore SoP.)
       For example, ""All informative things are useful"", ""Some websites are not
       useful"", therefore ""Some websites are not informative.""  (Contributed by
       David A. Wheeler, 28-Aug-2016.) $)
    baroco $p |- E. x ( ch /\ -. ph ) $=
      ( wn wa wi spi con3i anim2i eximii ) CBGZHCAGZHDFNOCABABIDEJKLM $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism ""Cesaro"" $)
    cesaro.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for Cesaro $)
    cesaro.min $e |- A. x ( ch -> ps ) $.
    $( Existence premise for Cesaro $)
    cesaro.e $e |- E. x ch $.
    $( ""Cesaro"", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ch ` is ` ps ` , and ` ch ` exist, therefore some ` ch `
       is not ` ph ` .  (In Aristotelian notation, EAO-2:  PeM and SaM
       therefore SoP.) (Contributed by David A. Wheeler, 28-Aug-2016.)
       (Revised by David A. Wheeler, 2-Sep-2016.) $)
    cesaro $p |- E. x ( ch /\ -. ph ) $=
      ( wn wa wi spi nsyl3 ancli eximii ) CCAHZIDGCOABCABHJDEKCBJDFKLMN $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism ""Camestros"" $)
    camestros.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for  $)
    camestros.min $e |- A. x ( ch -> -. ps ) $.
    $( Existence premise for Camestros $)
    camestros.e $e |- E. x ch $.
    $( ""Camestros"", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , no ` ch ` is ` ps ` , and ` ch ` exist, therefore some ` ch `
       is not ` ph ` .  (In Aristotelian notation, AEO-2:  PaM and SeM
       therefore SoP.) For example, ""All horses have hooves"", ""No humans have
       hooves"", and humans exist, therefore ""Some humans are not horses"".
       (Contributed by David A. Wheeler, 28-Aug-2016.)  (Revised by David A.
       Wheeler, 2-Sep-2016.) $)
    camestros $p |- E. x ( ch /\ -. ph ) $=
      ( wn wa wi spi nsyl ancli eximii ) CCAHZIDGCOCBACBHJDFKABJDEKLMN $.
  $}

  $( Figure 3 $)

  ${
    $( Major premise for the Aristotelian syllogism ""Datisi"" $)
    datisi.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for  $)
    datisi.min $e |- E. x ( ph /\ ch ) $.
    $( ""Datisi"", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and some ` ph ` is ` ch ` , therefore some ` ch ` is ` ps ` .
       (In Aristotelian notation, AII-3:  MaP and MiS therefore SiP.)
       (Contributed by David A. Wheeler, 28-Aug-2016.) $)
    datisi $p |- E. x ( ch /\ ps ) $=
      ( wa simpr wi spi adantr jca eximii ) ACGZCBGDFNCBACHABCABIDEJKLM $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism ""Disamis"" $)
    disamis.maj $e |- E. x ( ph /\ ps ) $.
    $( Minor premise for  $)
    disamis.min $e |- A. x ( ph -> ch ) $.
    $( ""Disamis"", one of the syllogisms of Aristotelian logic.  Some ` ph ` is
       ` ps ` , and all ` ph ` is ` ch ` , therefore some ` ch ` is ` ps ` .
       (In Aristotelian notation, IAI-3:  MiP and MaS therefore SiP.)
       (Contributed by David A. Wheeler, 28-Aug-2016.) $)
    disamis $p |- E. x ( ch /\ ps ) $=
      ( wa wi spi anim1i eximii ) ABGCBGDEACBACHDFIJK $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism ""Ferison"" $)
    ferison.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for  $)
    ferison.min $e |- E. x ( ph /\ ch ) $.
    $( ""Ferison"", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , and some ` ph ` is ` ch ` , therefore some ` ch ` is not
       ` ps ` .  (In Aristotelian notation, EIO-3:  MeP and MiS therefore SoP.)
       (Contributed by David A. Wheeler, 28-Aug-2016.)  (Revised by David A.
       Wheeler, 2-Sep-2016.) $)
    ferison $p |- E. x ( ch /\ -. ps ) $=
      ( wn datisi ) ABGCDEFH $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism ""Bocardo"" $)
    bocardo.maj $e |- E. x ( ph /\ -. ps ) $.
    $( Minor premise for  $)
    bocardo.min $e |- A. x ( ph -> ch ) $.
    $( ""Bocardo"", one of the syllogisms of Aristotelian logic.  Some ` ph ` is
       not ` ps ` , and all ` ph ` is ` ch ` , therefore some ` ch ` is not
       ` ps ` .  (In Aristotelian notation, OAO-3:  MoP and MaS therefore SoP.)
       For example, ""Some cats have no tails"", ""All cats are mammals"",
       therefore ""Some mammals have no tails"".  A reorder of ~ disamis ; prefer
       using that instead.  (Contributed by David A. Wheeler, 28-Aug-2016.)
       (New usage is discouraged.) $)
    bocardo $p |- E. x ( ch /\ -. ps ) $=
      ( wn disamis ) ABGCDEFH $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism ""Felapton"" $)
    felapton.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for  $)
    felapton.min $e |- A. x ( ph -> ch ) $.
    $( Existence premise for Felapton $)
    felapton.e $e |- E. x ph $.
    $( ""Felapton"", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ph ` is ` ch ` , and some ` ph ` exist, therefore some
       ` ch ` is not ` ps ` .  (In Aristotelian notation, EAO-3:  MeP and MaS
       therefore SoP.) For example, ""No flowers are animals"" and ""All flowers
       are plants"", therefore ""Some plants are not animals"".  (Contributed by
       David A. Wheeler, 28-Aug-2016.)  (Revised by David A. Wheeler,
       2-Sep-2016.) $)
    felapton $p |- E. x ( ch /\ -. ps ) $=
      ( wn wa wi spi jca eximii ) ACBHZIDGACNACJDFKANJDEKLM $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism ""Darapti"" $)
    darapti.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for  $)
    darapti.min $e |- A. x ( ph -> ch ) $.
    $( Existence premise for Darapti $)
    darapti.e $e |- E. x ph $.
    $( ""Darapti"", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , all ` ph ` is ` ch ` , and some ` ph ` exist, therefore some
       ` ch ` is ` ps ` .  (In Aristotelian notation, AAI-3:  MaP and MaS
       therefore SiP.) For example, ""All squares are rectangles"" and ""All
       squares are rhombuses"", therefore ""Some rhombuses are rectangles"".
       (Contributed by David A. Wheeler, 28-Aug-2016.) $)
    darapti $p |- E. x ( ch /\ ps ) $=
      ( wa wi spi jca eximii ) ACBHDGACBACIDFJABIDEJKL $.
  $}

  $( Figure 4 $)

  ${
    $( Major premise for the Aristotelian syllogism ""Calemes"" $)
    calemes.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for  $)
    calemes.min $e |- A. x ( ps -> -. ch ) $.
    $( ""Calemes"", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , and no ` ps ` is ` ch ` , therefore no ` ch ` is ` ph ` .  (In
       Aristotelian notation, AEE-4:  PaM and MeS therefore SeP.) (Contributed
       by David A. Wheeler, 28-Aug-2016.)  (Revised by David A. Wheeler,
       2-Sep-2016.) $)
    calemes $p |- A. x ( ch -> -. ph ) $=
      ( wn wi spi con2i nsyl ax-gen ) CAGHDCBABCBCGHDFIJABHDEIKL $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism ""Dimatis"" $)
    dimatis.maj $e |- E. x ( ph /\ ps ) $.
    $( Minor premise for  $)
    dimatis.min $e |- A. x ( ps -> ch ) $.
    $( ""Dimatis"", one of the syllogisms of Aristotelian logic.  Some ` ph ` is
       ` ps ` , and all ` ps ` is ` ch ` , therefore some ` ch ` is ` ph ` .
       (In Aristotelian notation, IAI-4:  PiM and MaS therefore SiP.) For
       example, ""Some pets are rabbits."", ""All rabbits have fur"", therefore
       ""Some fur bearing animals are pets"".  Like ~ darii with positions
       interchanged.  (Contributed by David A. Wheeler, 28-Aug-2016.) $)
    dimatis $p |- E. x ( ch /\ ph ) $=
      ( wa wi spi adantl simpl jca eximii ) ABGZCAGDENCABCABCHDFIJABKLM $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism ""Fresison"" $)
    fresison.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for  $)
    fresison.min $e |- E. x ( ps /\ ch ) $.
    $( ""Fresison"", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` (PeM), and some ` ps ` is ` ch ` (MiS), therefore some ` ch ` is
       not ` ph ` (SoP).  (In Aristotelian notation, EIO-4:  PeM and MiS
       therefore SoP.) (Contributed by David A. Wheeler, 28-Aug-2016.)
       (Revised by David A. Wheeler, 2-Sep-2016.) $)
    fresison $p |- E. x ( ch /\ -. ph ) $=
      ( wa wn simpr wi spi con2i adantr jca eximii ) BCGZCAHZGDFPCQBCIBQCABABHJ
      DEKLMNO $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism ""Calemos"" $)
    calemos.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for  $)
    calemos.min $e |- A. x ( ps -> -. ch ) $.
    $( Existence premise for Calemos $)
    calemos.e $e |- E. x ch $.
    $( ""Calemos"", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` (PaM), no ` ps ` is ` ch ` (MeS), and ` ch ` exist, therefore
       some ` ch ` is not ` ph ` (SoP).  (In Aristotelian notation, AEO-4:  PaM
       and MeS therefore SoP.) (Contributed by David A. Wheeler, 28-Aug-2016.)
       (Revised by David A. Wheeler, 2-Sep-2016.) $)
    calemos $p |- E. x ( ch /\ -. ph ) $=
      ( wn wa wi spi con2i nsyl ancli eximii ) CCAHZIDGCPCBABCBCHJDFKLABJDEKMNO
      $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism ""Fesapo"" $)
    fesapo.maj $e |- A. x ( ph -> -. ps ) $.
    $( Minor premise for  $)
    fesapo.min $e |- A. x ( ps -> ch ) $.
    $( Existence premise for Fesapo $)
    fesapo.e $e |- E. x ps $.
    $( ""Fesapo"", one of the syllogisms of Aristotelian logic.  No ` ph ` is
       ` ps ` , all ` ps ` is ` ch ` , and ` ps ` exist, therefore some ` ch `
       is not ` ph ` .  (In Aristotelian notation, EAO-4:  PeM and MaS
       therefore SoP.) (Contributed by David A. Wheeler, 28-Aug-2016.)
       (Revised by David A. Wheeler, 2-Sep-2016.) $)
    fesapo $p |- E. x ( ch /\ -. ph ) $=
      ( wn wa wi spi con2i jca eximii ) BCAHZIDGBCOBCJDFKABABHJDEKLMN $.
  $}

  ${
    $( Major premise for the Aristotelian syllogism ""Bamalip"" $)
    bamalip.maj $e |- A. x ( ph -> ps ) $.
    $( Minor premise for  $)
    bamalip.min $e |- A. x ( ps -> ch ) $.
    $( Existence premise for Bamalip $)
    bamalip.e $e |- E. x ph $.
    $( ""Bamalip"", one of the syllogisms of Aristotelian logic.  All ` ph ` is
       ` ps ` , all ` ps ` is ` ch ` , and ` ph ` exist, therefore some ` ch `
       is ` ph ` .  (In Aristotelian notation, AAI-4:  PaM and MaS therefore
       SiP.) Like ~ barbari .  (Contributed by David A. Wheeler,
       28-Aug-2016.) $)
    bamalip $p |- E. x ( ch /\ ph ) $=
      ( wa wi spi syl ancri eximii ) ACAHDGACABCABIDEJBCIDFJKLM $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
               Intuitionistic logic
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

Intuitionistic (constructive) logic is similar to classical logic
with the notable omission of ~ ax-3 and theorems such as ~ exmid or
~ peirce .  We mostly treat intuitionistic logic in a separate file, iset.mm,
which is known as the Intuitionistic Logic Explorer on the web site.  However,
iset.mm has a number of additional axioms (mainly to replace definitions like
~ df-or and ~ df-ex which are not valid in intuitionistic logic) and we want
to prove those axioms here to demonstrate that adding those axioms in iset.mm
does not make iset.mm any less consistent than set.mm.

The following axioms are unchanged between set.mm and iset.mm: ~ ax-1 ,
~ ax-2 , ~ ax-mp , ~ ax-4 , ~ ax-11 , ~ ax-gen , ~ ax-7 , ~ ax-12 ,
~ ax-8 , ~ ax-9 , and ~ ax-5 .

In this list of axioms, the ones that repeat earlier theorems are marked
""(New usage is discouraged.)"" so that the earlier theorems will be used
consistently in other proofs.

$)

  $( Left 'and' elimination (intuitionistic logic axiom ax-ia1).  (Contributed
     by Jim Kingdon, 21-May-2018.)  (New usage is discouraged.) $)
  axia1 $p |- ( ( ph /\ ps ) -> ph ) $=
    ( simpl ) ABC $.

  $( Right 'and' elimination (intuitionistic logic axiom ax-ia2).  (Contributed
     by Jim Kingdon, 21-May-2018.)  (New usage is discouraged.) $)
  axia2 $p |- ( ( ph /\ ps ) -> ps ) $=
    ( simpr ) ABC $.

  $( 'And' introduction (intuitionistic logic axiom ax-ia3).  (Contributed by
     Jim Kingdon, 21-May-2018.)  (New usage is discouraged.) $)
  axia3 $p |- ( ph -> ( ps -> ( ph /\ ps ) ) ) $=
    ( pm3.2 ) ABC $.

  $( 'Not' introduction (intuitionistic logic axiom ax-in1).  (Contributed by
     Jim Kingdon, 21-May-2018.)  (New usage is discouraged.) $)
  axin1 $p |- ( ( ph -> -. ph ) -> -. ph ) $=
    ( pm2.01 ) AB $.

  $( 'Not' elimination (intuitionistic logic axiom ax-in2).  (Contributed by
     Jim Kingdon, 21-May-2018.)  (New usage is discouraged.) $)
  axin2 $p |- ( -. ph -> ( ph -> ps ) ) $=
    ( pm2.21 ) ABC $.

  $( Definition of 'or' (intuitionistic logic axiom ax-io).  (Contributed by
     Jim Kingdon, 21-May-2018.)  (New usage is discouraged.) $)
  axio $p |- ( ( ( ph \/ ch ) -> ps ) <->
      ( ( ph -> ps ) /\ ( ch -> ps ) ) ) $=
    ( jaob ) ABCD $.

  $( Specialization (intuitionistic logic axiom ax-4).  This is just ~ sp by
     another name.  (Contributed by Jim Kingdon, 31-Dec-2017.)
     (New usage is discouraged.) $)
  axi4 $p |- ( A. x ph -> ph ) $=
    ( sp ) ABC $.

  $( Converse of ax-c4 (intuitionistic logic axiom ax-i5r).  (Contributed by
     Jim Kingdon, 31-Dec-2017.) $)
  axi5r $p |- ( ( A. x ph -> A. x ps ) -> A. x ( A. x ph -> ps ) ) $=
    ( wal wi hba1 hbim sp imim2i alrimih ) ACDZBCDZEKBECKLCACFBCFGLBKBCHIJ $.

  $( ` x ` is not free in ` A. x ph ` (intuitionistic logic axiom ax-ial).
     (Contributed by Jim Kingdon, 31-Dec-2017.)  (New usage is discouraged.) $)
  axial $p |- ( A. x ph -> A. x A. x ph ) $=
    ( hba1 ) ABC $.

  $( ` x ` is not free in ` E. x ph ` (intuitionistic logic axiom ax-ie1).
     (Contributed by Jim Kingdon, 31-Dec-2017.)  (New usage is discouraged.) $)
  axie1 $p |- ( E. x ph -> A. x E. x ph ) $=
    ( hbe1 ) ABC $.

  $( A key property of existential quantification (intuitionistic logic axiom
     ax-ie2).  (Contributed by Jim Kingdon, 31-Dec-2017.) $)
  axie2 $p |- ( A. x ( ps -> A. x ps ) ->
              ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) ) $=
    ( wal wi wnf wex wb df-nf 19.23t sylbir ) BBCDECDBCFABECDACGBEHBCIABCJK $.

  $( Axiom of existence (intuitionistic logic axiom ax-i9).  In classical
     logic, this is equivalent to ~ ax-6 but in intuitionistic logic it needs
     to be stated using the existential quantifier.  (Contributed by Jim
     Kingdon, 31-Dec-2017.)  (New usage is discouraged.) $)
  axi9 $p |- E. x x = y $=
    ( ax6e ) ABC $.

  $( Axiom of Quantifier Substitution (intuitionistic logic axiom ax-10).  This
     is just ~ axc11n by another name.  (Contributed by Jim Kingdon,
     31-Dec-2017.)  (New usage is discouraged.) $)
  axi10 $p |- ( A. x x = y -> A. y y = x ) $=
    ( axc11n ) ABC $.

  $( Axiom of Quantifier Introduction (intuitionistic logic axiom ax-i12).  In
     classical logic, this is mostly a restatement of ~ axc9 (with one
     additional quantifier).  But in intuitionistic logic, changing the
     negations and implications to disjunctions makes it stronger.
     (Contributed by Jim Kingdon, 31-Dec-2017.) $)
  axi12 $p |- ( A. z z = x \/ ( A. z z = y \/
                A. z ( x = y -> A. z x = y ) ) ) $=
    ( weq wal wo wi nfae nfor 19.32 wn axc9 orrd orri orass mpbir mpgbi mpbi )
    CADCEZCBDCEZFZABDZUBCEGZCEZFZSTUDFFUAUCFZUECUAUCCSTCCACHCBCHIJUFSTUCFZFSUGS
    KTUCABCLMNSTUCOPQSTUDOR $.

  $( Axiom of Bundling (intuitionistic logic axiom ax-bnd).  In classical
     logic, this and ~ axi12 are fairly straightforward consequences of
     ~ axc9 .  But in intuitionistic logic, it is not easy to add the extra
     ` A. x ` to ~ axi12 and so we treat the two as separate axioms.
     (Contributed by Jim Kingdon, 22-Mar-2018.) $)
  axbnd $p |- ( A. z z = x \/ ( A. z z = y \/
                 A. x A. z ( x = y -> A. z x = y ) ) ) $=
    ( weq wal wi wo wn wa nfnae nfan axc9 imp alrimi ex orrd orri ) CADCEZCBDCE
    ZABDZTCEFZCEZAEZGRHZSUCUDSHZUCUDUEIZUBAUDUEACAAJCBAJKUFUACUDUECCACJCBCJKUDU
    EUAABCLMNNOPQ $.

$( End $[ set-pred.mm $] $)

"
Class {
	#name : #MmRawFileDataPartFour,
	#superclass : #MmDatabase,
	#category : #'Metamath-Parsing'
}
