/-!
# Fox 2007: Free Choice and the Theory of Scalar Implicatures
@cite{fox-2007}

Danny Fox, "Free Choice and the Theory of Scalar Implicatures."
In Sauerland & Stateva (eds.), *Presupposition and Implicature in
Compositional Semantics*, pp. 71--120. Palgrave Macmillan.

## Core Ideas

1. SIs are derived by a **covert exhaustivity operator** `exh` in the
   grammar (not pragmatically via NG-MQ)
2. `exh` uses **innocent exclusion** (I-E): exclude only alternatives
   whose exclusion doesn't force including others
3. **Recursive** application of `exh` derives **free choice** (FC) for
   disjunction under existential modals: ◇(p∨q) ⟹ ◇p ∧ ◇q
4. The system resolves Chierchia's puzzle about embedded disjunction

## Computable Algorithm

This file provides a **computable** (Bool/List) implementation of Fox's
innocent exclusion algorithm, complementing the Set-theoretic version
in `Exhaustification/Operators.lean` (@cite{spector-2016}). The definitions are:

- `nonWeakerIndices`: NW(p, A) — alternatives not entailed by prejacent
- `exclusionConsistent`: consistency of {p} ∪ {¬q : q ∈ excl}
- `maxConsistentExclusions`: maximal consistent exclusion sets
- `ieIndices`: I-E(p, A) — innocently excludable alternatives
- `exhB`: the exhaustivity operator (Bool version)

## Key Results

- `disj_exh_eq_exor`: Exh(Alt)(p∨q) = p ⊻ q (exclusive or)
- `chierchia_puzzle_ie`: `exh` resolves Chierchia's puzzle (§4)
- `free_choice`: Exh²(◇(p∨q)) = ◇p ∧ ◇q ∧ ¬◇(p∧q) (§7.2)

## Connection to the Symmetry Problem

Innocent exclusion was designed to handle **symmetric alternatives**
(see `Symmetry.lean`): when S₁, S₂ partition S's denotation, excluding
both is inconsistent, so they land in different MCEs and neither is in
I-E. This correctly predicts that `exh` is vacuous when the alternative
set contains both symmetric partners (`ContextualRestriction.symmetry_problem`).
The problem of *which alternatives enter the set* is addressed by
@cite{katzir-2007}'s structural complexity (`Structural.lean`).

## Duality with Santorio 2018

Fox's innocent exclusion is the **dual** of @cite{santorio-2018}'s
stability algorithm (footnote 40, p. 540). This duality is verified
computationally in `Semantics/Conditionals/AlternativeSensitive.lean`,
which imports this file and proves the correspondence.
-/

namespace Exhaustification.InnocentExclusion


-- ============================================================
-- SECTION 1: Computable Innocent Exclusion Algorithm
-- ============================================================

/-- All sublists (power set) of a list. -/
def sublists {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => let p := sublists xs; p ++ p.map (x :: ·)

/-- Non-weaker alternatives (by index): alternatives not entailed by p.
    NW(p, A) = {q ∈ A : p ⊭ q}, i.e., there exists a world where p
    is true but q is false. -/
def nonWeakerIndices {W : Type} (domain : List W)
    (p : W → Bool) (alts : List (W → Bool)) : List Nat :=
  (List.range alts.length).filter fun i =>
    match alts[i]? with
    | some q => domain.any fun w => p w && !q w
    | none => false

/-- Consistency of an exclusion: {p} ∪ {¬q : q ∈ excl} is satisfiable.
    There exists a world where p holds and all excluded alternatives
    are false. -/
def exclusionConsistent {W : Type} (domain : List W)
    (p : W → Bool) (alts : List (W → Bool)) (excl : List Nat) : Bool :=
  domain.any fun w =>
    p w && (excl.filterMap fun i => alts[i]?).all fun q => !q w

/-- Maximal consistent exclusions: maximal subsets A' ⊆ NW(p, A) such
    that {p} ∪ {¬q : q ∈ A'} is consistent.

    These are Fox's MC-sets projected to the excludable alternatives.
    The intersection of all maximal exclusions gives I-E. -/
def maxConsistentExclusions {W : Type} (domain : List W)
    (p : W → Bool) (alts : List (W → Bool)) : List (List Nat) :=
  let nw := nonWeakerIndices domain p alts
  let allSubsets := sublists nw
  let consistent := allSubsets.filter (exclusionConsistent domain p alts)
  consistent.filter fun s =>
    !consistent.any fun t =>
      t.length > s.length && s.all fun i => t.contains i

/-- Innocently excludable alternatives (by index): those appearing in
    **every** maximal consistent exclusion.

    I-E(p, A) = ⋂ {A' : A' is a maximal consistent exclusion}

    An alternative is innocently excludable iff excluding it doesn't
    force including some other alternative — i.e., it can be excluded
    no matter which maximal exclusion we choose. -/
def ieIndices {W : Type} (domain : List W)
    (p : W → Bool) (alts : List (W → Bool)) : List Nat :=
  let mces := maxConsistentExclusions domain p alts
  match mces with
  | [] => []
  | first :: rest =>
    first.filter fun i => rest.all fun mce => mce.contains i

/-- The exhaustivity operator (computable Bool version).

    ⟦Exh⟧(A)(p)(w) ⟺ p(w) ∧ ∀q ∈ I-E(p, A). ¬q(w)

    Asserts the prejacent and negates every innocently excludable
    alternative. -/
def exhB {W : Type} (domain : List W)
    (alts : List (W → Bool)) (p : W → Bool) : W → Bool :=
  fun w => p w && (ieIndices domain p alts).all fun i =>
    match alts[i]? with
    | some q => !q w
    | none => true


-- ============================================================
-- Shared World Type for Propositional Examples
-- ============================================================

/-- Four propositional worlds for examples with two atomic propositions. -/
inductive PQWorld where
  | pOnly | qOnly | both | neither
  deriving Repr, DecidableEq, BEq

def pqDomain : List PQWorld := [.pOnly, .qOnly, .both, .neither]

def pProp : PQWorld → Bool | .pOnly | .both => true | _ => false
def qProp : PQWorld → Bool | .qOnly | .both => true | _ => false
def pOrQ : PQWorld → Bool | .neither => false | _ => true
def pAndQ : PQWorld → Bool | .both => true | _ => false

/-- Sauerland alternatives for p∨q: {p∨q, p, q, p∧q}. -/
def disjAlts : List (PQWorld → Bool) := [pOrQ, pProp, qProp, pAndQ]


-- ============================================================
-- SECTION 2: Simple Disjunction — p∨q (§6.2, pp. 98–99)
-- ============================================================

/-!
## Simple Disjunction: p∨q → ExOR

With Sauerland alternatives Alt(p∨q) = {p∨q, p, q, p∧q}:
- NW(p∨q) = {p, q, p∧q} (none entailed by p∨q)
- Maximal consistent exclusions: {q, p∧q} and {p, p∧q}
  (can't exclude both p and q: (p∨q) ∧ ¬p ∧ ¬q is contradictory)
- I-E = {p∧q} (the only alternative in both exclusions)
- Exh(Alt)(p∨q) = (p∨q) ∧ ¬(p∧q) = exclusive or
-/

section SimpleDisjunction

/-- The non-weaker alternatives are p, q, and p∧q (indices 1, 2, 3). -/
theorem disj_nonWeaker :
    nonWeakerIndices pqDomain pOrQ disjAlts = [1, 2, 3] := by native_decide

/-- Two maximal consistent exclusions: {q, p∧q} and {p, p∧q}.
    Excluding both p and q simultaneously is inconsistent with p∨q. -/
theorem disj_maxExclusions :
    maxConsistentExclusions pqDomain pOrQ disjAlts = [[2, 3], [1, 3]] := by
  native_decide

/-- p∧q (index 3) is the only innocently excludable alternative. -/
theorem disj_ie :
    ieIndices pqDomain pOrQ disjAlts = [3] := by native_decide

/-- **Exh(Alt)(p∨q) = exclusive or**: the prejacent conjoined with
    ¬(p∧q). This is the standard scalar implicature for disjunction. -/
theorem disj_exh_eq_exor :
    ∀ w : PQWorld, exhB pqDomain disjAlts pOrQ w =
      (pOrQ w && !pAndQ w) := by
  intro w; cases w <;> native_decide

end SimpleDisjunction


-- ============================================================
-- SECTION 3: Chierchia's Puzzle (§4, pp. 89–90)
-- ============================================================

/-!
## Chierchia's Puzzle: Embedded Disjunction

@cite{chierchia-2004} observed that when a scalar item is embedded
in a disjunction, the standard neo-Gricean system (NG-MQ) derives
the wrong implicature.

Example: "John did the reading or some of the homework."
- r ∨ sh, with stronger alternative r ∨ ah (all homework)
- The correct SI: ¬ah (John didn't do ALL the homework)
- NG-MQ's SI: ¬(r ∨ ah) = ¬r ∧ ¬ah (too strong — negates r too!)

Fox's solution: `exh` correctly derives ¬ah without ¬r, because
`ah` is the only innocently excludable alternative among the
relevant ones.
-/

section ChierchiaPuzzle

/-- "John did the reading or some/all of the homework."
    Worlds: r=reading, sh=some homework (⊂all), ah=all homework. -/
private inductive ChW where
  | rOnly        -- reading done, no homework
  | rAndSh       -- reading + some homework
  | rAndAh       -- reading + all homework
  | shOnly       -- some homework only
  | ahOnly       -- all homework only
  | neither      -- nothing done
  deriving Repr, DecidableEq, BEq

private def chDomain : List ChW :=
  [.rOnly, .rAndSh, .rAndAh, .shOnly, .ahOnly, .neither]

private def reading : ChW → Bool
  | .rOnly | .rAndSh | .rAndAh => true | _ => false
private def someHW : ChW → Bool
  | .rAndSh | .rAndAh | .shOnly | .ahOnly => true | _ => false
private def allHW : ChW → Bool
  | .rAndAh | .ahOnly => true | _ => false
private def rOrSh : ChW → Bool  -- r ∨ sh (the utterance)
  | .neither => false | _ => true
private def rOrAh : ChW → Bool  -- r ∨ ah (the stronger alternative)
  | .rOnly | .rAndSh | .rAndAh | .ahOnly => true | _ => false

/-- Alternatives for "r ∨ sh": {r∨sh, r, sh, r∧sh, r∨ah, r∧ah, ah}

    Generated by Sauerland's Horn-Set {or, and} × {some, all}
    applied to both the connective and the scalar item. -/
private def chAlts : List (ChW → Bool) :=
  [ rOrSh                                          -- 0: r ∨ sh
  , reading                                        -- 1: r
  , someHW                                         -- 2: sh
  , fun w => reading w && someHW w                 -- 3: r ∧ sh
  , rOrAh                                          -- 4: r ∨ ah
  , fun w => reading w && allHW w                  -- 5: r ∧ ah
  , allHW                                          -- 6: ah
  ]

/-- **Chierchia's puzzle**: NG-MQ would derive SI = ¬(r∨ah) = ¬r ∧ ¬ah,
    which negates the first disjunct. Fox's `exh` correctly identifies
    that only `ah` (index 6) and `r∧ah` (index 5) are innocently
    excludable — NOT `r` or `r∨ah`. -/
theorem chierchia_puzzle_ie :
    let ie := ieIndices chDomain rOrSh chAlts
    -- ah and r∧ah are innocently excludable
    ie.contains 6 = true ∧ ie.contains 5 = true ∧
    -- r and r∨ah are NOT innocently excludable
    ie.contains 1 = false ∧ ie.contains 4 = false := by
  native_decide

/-- `exh` correctly preserves the first disjunct's truth value:
    the exhaustified meaning is consistent with r being true. -/
theorem chierchia_exh_preserves_reading :
    exhB chDomain chAlts rOrSh .rOnly = true := by native_decide

/-- `exh` correctly negates the stronger alternative: the exhaustified
    meaning entails ¬ah (not all homework). -/
theorem chierchia_exh_negates_all :
    ∀ w : ChW, exhB chDomain chAlts rOrSh w = true →
      allHW w = false := by
  intro w h; cases w <;> simp_all [allHW] <;> exact absurd h (by native_decide)

end ChierchiaPuzzle


-- ============================================================
-- SECTION 4: Free Choice — ◇(p∨q) (§7.2, pp. 104–105)
-- ============================================================

/-!
## Free Choice via Double Exhaustification

The key result: recursive exhaustification derives the conjunctive
interpretation of disjunction under existential modals.

**Layer 1**: Exh(C)(◇(p∨q)) = ◇(p∨q) ∧ ¬◇(p∧q)
- Excludes ◇(p∧q) but NOT ◇p or ◇q (excluding one forces the other)
- Consistent with FC but doesn't assert it

**Layer 2**: Exh(C')[Exh(C)(◇(p∨q))] = ◇p ∧ ◇q ∧ ¬◇(p∧q)
- Alternatives are {Exh(C)(φ) : φ ∈ C}
- Exh(C)(◇p) = ◇p ∧ ¬◇q, Exh(C)(◇q) = ◇q ∧ ¬◇p
- Both are innocently excludable at the second layer
- Their exclusion forces ◇p ∧ ◇q — free choice!
-/

section FreeChoice

/-- Modal worlds: each represents which propositional situations are
    accessible. Named by which ◇-propositions they make true. -/
inductive ModalW where
  | seesP        -- accessible: {p∧¬q}
  | seesQ        -- accessible: {¬p∧q}
  | seesPQ       -- accessible: {p∧¬q, ¬p∧q}
  | seesBoth     -- accessible: {p∧q}
  | seesNothing  -- accessible: ∅
  deriving Repr, DecidableEq, BEq

def mDomain : List ModalW :=
  [.seesP, .seesQ, .seesPQ, .seesBoth, .seesNothing]

def diamP : ModalW → Bool
  | .seesP | .seesPQ | .seesBoth => true | _ => false
def diamQ : ModalW → Bool
  | .seesQ | .seesPQ | .seesBoth => true | _ => false
def diamPorQ : ModalW → Bool
  | .seesNothing => false | _ => true
def diamPandQ : ModalW → Bool
  | .seesBoth => true | _ => false

/-- Sauerland alternatives under ◇: {◇(p∨q), ◇p, ◇q, ◇(p∧q)}. -/
def modalAlts : List (ModalW → Bool) :=
  [diamPorQ, diamP, diamQ, diamPandQ]

-- ── Layer 1 ─────────────────────────────────────────────────

/-- ◇(p∧q) is the only innocently excludable alternative at layer 1.
    ◇p and ◇q cannot be innocently excluded: excluding ◇p while keeping
    ◇(p∨q) forces ◇q, and vice versa. -/
theorem modal_ie_layer1 :
    ieIndices mDomain diamPorQ modalAlts = [3] := by native_decide

/-- **Layer 1**: Exh(C)(◇(p∨q)) = ◇(p∨q) ∧ ¬◇(p∧q).
    Consistent with FC (◇p ∧ ◇q) but doesn't yet assert it. -/
theorem modal_exh1 :
    ∀ w : ModalW, exhB mDomain modalAlts diamPorQ w =
      (diamPorQ w && !diamPandQ w) := by
  intro w; cases w <;> native_decide

-- ── Exhaustified alternatives for Layer 2 ───────────────────

def exhDiamP : ModalW → Bool := exhB mDomain modalAlts diamP
def exhDiamQ : ModalW → Bool := exhB mDomain modalAlts diamQ
def exhDiamPandQ : ModalW → Bool := exhB mDomain modalAlts diamPandQ

/-- Exh(C)(◇p) = ◇p ∧ ¬◇q: exhaustifying ◇p excludes ◇q. -/
theorem exhDiamP_eq :
    ∀ w : ModalW, exhDiamP w = (diamP w && !diamQ w) := by
  intro w; cases w <;> native_decide

/-- Exh(C)(◇q) = ◇q ∧ ¬◇p: symmetric to ◇p. -/
theorem exhDiamQ_eq :
    ∀ w : ModalW, exhDiamQ w = (diamQ w && !diamP w) := by
  intro w; cases w <;> native_decide

/-- Exh(C)(◇(p∧q)) = ◇(p∧q): no non-weaker alternatives
    (◇(p∧q) entails all of ◇p, ◇q, ◇(p∨q)). -/
theorem exhDiamPandQ_eq :
    ∀ w : ModalW, exhDiamPandQ w = diamPandQ w := by
  intro w; cases w <;> native_decide

-- ── Layer 2 ─────────────────────────────────────────────────

/-- Layer 2 alternatives: {Exh(C)(φ) : φ ∈ C}. -/
def layer2Alts : List (ModalW → Bool) :=
  [exhB mDomain modalAlts diamPorQ, exhDiamP, exhDiamQ, exhDiamPandQ]

/-- Layer 1 result as prejacent for layer 2. -/
def layer1Result : ModalW → Bool :=
  exhB mDomain modalAlts diamPorQ

/-- **Free Choice**: double exhaustification yields ◇p ∧ ◇q ∧ ¬◇(p∧q).

    Exh(C')[Exh(C)(◇(p∨q))] asserts:
    - ◇p ∧ ◇q (free choice permission)
    - ¬◇(p∧q) (anti-conjunctive inference)

    The FC inference ◇p ∧ ◇q arises because the second layer excludes
    Exh(C)(◇p) = ◇p∧¬◇q and Exh(C)(◇q) = ◇q∧¬◇p, whose negation
    (given the prejacent) forces both ◇p and ◇q to hold. -/
theorem free_choice :
    ∀ w : ModalW, exhB mDomain layer2Alts layer1Result w =
      (diamP w && diamQ w && !diamPandQ w) := by
  intro w; cases w <;> native_decide

/-- FC entails both disjuncts hold: the speaker has permission for
    each disjunct individually. -/
theorem fc_entails_both_disjuncts (w : ModalW)
    (h : exhB mDomain layer2Alts layer1Result w = true) :
    diamP w = true ∧ diamQ w = true := by
  cases w
  · exact absurd h (by native_decide)
  · exact absurd h (by native_decide)
  · exact ⟨rfl, rfl⟩
  · exact absurd h (by native_decide)
  · exact absurd h (by native_decide)

end FreeChoice


-- ============================================================
-- SECTION 5: Relevance-Sensitive Exhaustification
-- ============================================================

/-!
## Relevance-Sensitive EXH

@cite{magri-2009} §3.2.3 (eq. 42) introduces a relevance-parameterized
variant of EXH. A contextually supplied relevance relation R determines
which alternatives are "active":

    EXH_R(A)(p)(w) = p(w) ∧ ∀q ∈ I-E(p,A). (¬q(w) ∨ ¬R(q))

Alternatives that are not relevant are simply ignored — neither asserted
nor negated. This explains why non-mismatching implicatures are optional
(the alternative may be irrelevant in context), while mismatching
implicatures are mandatory (the alternative is necessarily relevant by
postulate (43b): relevance is closed under contextual equivalence, so a
mismatching alternative — contextually equivalent to the prejacent — is
always relevant).
-/

section RelevanceSensitive

/-- Relevance-sensitive exhaustivity operator.

    @cite{magri-2009} eq. (42): EXH_R asserts the prejacent and negates
    only those innocently excludable alternatives that are relevant.
    Irrelevant alternatives are skipped (the `!relevant i` disjunct
    trivializes the conjunct).

    When `relevant i = true` for all i, this reduces to `exhB`. -/
def exhR {W : Type} (domain : List W)
    (alts : List (W → Bool)) (p : W → Bool)
    (relevant : Nat → Bool) : W → Bool :=
  fun w => p w && (ieIndices domain p alts).all fun i =>
    match alts[i]? with
    | some q => !relevant i || !q w
    | none => true

/-- When all alternatives are relevant, `exhR` reduces to `exhB`.

    Universal relevance is the default: `exhB` is the special case of
    `exhR` where every alternative matters. -/
theorem exhR_all_relevant_eq_exhB {W : Type} (domain : List W)
    (alts : List (W → Bool)) (p : W → Bool) :
    exhR domain alts p (fun _ => true) = exhB domain alts p := rfl

end RelevanceSensitive


end Exhaustification.InnocentExclusion
