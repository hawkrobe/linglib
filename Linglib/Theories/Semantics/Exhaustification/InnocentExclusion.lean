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
  deriving Repr, DecidableEq

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
  deriving Repr, DecidableEq

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
  deriving Repr, DecidableEq

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


-- ============================================================
-- SECTION 6: Contradiction-Tolerating Exhaustification
-- ============================================================

/-!
## Chierchia 2013 Exhaustivity Operator

@cite{chierchia-2013} defines an exhaustivity operator that negates
**all** alternatives not entailed by the prejacent, regardless of whether
the result is consistent (contradiction-tolerating). This contrasts with
Fox's `exhB`, which uses innocent exclusion to guarantee consistency.

The contradiction-tolerating operator is important for the theory of
EFCIs (@cite{alonso-ovalle-moghiseh-2025}): when applied to all
alternatives of an unembedded EFCI, it derives a contradiction, motivating
either modal insertion (for *irgendein*-type EFCIs) or partial
exhaustification (for Farsi *yek-i* DPs).
-/

section ChierchiaExh

/-- Contradiction-tolerating exhaustivity operator (@cite{chierchia-2013}).

    Negates every alternative not entailed by the prejacent, even if
    the result is inconsistent. When restricted to alternatives where
    IE = NW (all non-entailed alts are innocently excludable), this
    coincides with `exhB`. -/
def exhAll {W : Type} (domain : List W)
    (alts : List (W → Bool)) (p : W → Bool) : W → Bool :=
  fun w => p w && alts.all fun q =>
    -- entailed? if yes, keep; if no, negate
    if domain.any (fun v => p v && !q v) then !q w else true

-- ── Helper: sublists membership ───────────────────────────────

private theorem sublists_sub' {α : Type} (l sub : List α)
    (h : sub ∈ sublists l) : ∀ x, x ∈ sub → x ∈ l := by
  induction l generalizing sub with
  | nil =>
    simp [sublists] at h; subst h
    intro x hx; exact absurd hx List.not_mem_nil
  | cons a as ih =>
    simp only [sublists, List.mem_append] at h
    rcases h with h | h
    · intro x hx; exact List.mem_cons_of_mem a (ih sub h x hx)
    · rw [List.mem_map] at h
      obtain ⟨t, ht, rfl⟩ := h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem a (ih t ht x hx)

-- ── Helper: ieIndices ⊆ nonWeakerIndices ─────────────────────

private theorem ieIndices_sub_nw {W : Type} (domain : List W)
    (p : W → Bool) (alts : List (W → Bool)) :
    ∀ i ∈ ieIndices domain p alts, i ∈ nonWeakerIndices domain p alts := by
  intro i hi
  simp only [ieIndices] at hi
  generalize hm : maxConsistentExclusions domain p alts = mces at hi
  match mces, hi with
  | first :: _, hi =>
    rw [List.mem_filter] at hi
    have hfirst : first ∈ maxConsistentExclusions domain p alts :=
      hm ▸ List.mem_cons_self
    simp only [maxConsistentExclusions, List.mem_filter] at hfirst
    -- hfirst.1.1 : first ∈ sublists (nonWeakerIndices ...)
    exact sublists_sub' _ _ hfirst.1.1 i hi.1

-- ── Helper: h implies every alt is non-weaker ────────────────

private theorem all_nonweaker {W : Type} (domain : List W)
    (p : W → Bool) (alts : List (W → Bool))
    (h : ieIndices domain p alts = List.range alts.length)
    (i : Nat) (hi : i < alts.length)
    (q : W → Bool) (hq : alts[i]? = some q) :
    (domain.any fun w => p w && !q w) = true := by
  have hmem : i ∈ ieIndices domain p alts := h ▸ List.mem_range.mpr hi
  have hnw := ieIndices_sub_nw domain p alts i hmem
  simp only [nonWeakerIndices, List.mem_filter, List.mem_range] at hnw
  rw [hq] at hnw; exact hnw.2

-- ── Helper: per-element agreement ────────────────────────────

private theorem all_agree {W : Type} (domain : List W)
    (p : W → Bool) (alts : List (W → Bool)) (w : W)
    (hnw : ∀ i, i < alts.length → ∀ q, alts[i]? = some q →
      (domain.any fun v => p v && !q v) = true) :
    alts.all (fun q => if domain.any (fun v => p v && !q v) then !q w else true) =
    (List.range alts.length).all (fun i =>
      match alts[i]? with | some q => !q w | none => true) := by
  induction alts with
  | nil => rfl
  | cons a as ih =>
    simp only [List.all_cons, List.length_cons, List.range_succ_eq_map,
               List.getElem?_cons_zero]
    have ha : (domain.any fun v => p v && !a v) = true :=
      hnw 0 (Nat.zero_lt_succ _) a rfl
    rw [ha]; simp only [ite_true]
    congr 1
    rw [List.all_map]
    have hshift : (fun i => match (a :: as)[i]? with | some q => !q w | none => true) ∘ Nat.succ =
                  (fun i => match as[i]? with | some q => !q w | none => true) := by
      funext j; simp [Function.comp, List.getElem?_cons_succ]
    rw [hshift]
    exact ih (fun i hi q hq => hnw (i + 1) (Nat.succ_lt_succ hi) q
      (by simp [List.getElem?_cons_succ, hq]))

-- ── Main theorem ─────────────────────────────────────────────

/-- When all alternatives are innocently excludable, `exhAll` = `exhB`.

    **Proof**: The hypothesis IE = [0, ..., n-1] implies every alternative
    is non-weaker (since IE ⊆ NW by construction). Therefore `exhAll`'s
    if-then-else always takes the `then` branch, and both operators reduce
    to p(w) ∧ ∀q ∈ alts. ¬q(w). -/
theorem exhAll_eq_exhB_when_all_ie {W : Type} (domain : List W)
    (alts : List (W → Bool)) (p : W → Bool)
    (h : ieIndices domain p alts = List.range alts.length) :
    ∀ w, exhAll domain alts p w = exhB domain alts p w := by
  intro w
  simp only [exhAll, exhB, h]
  congr 1
  exact all_agree domain p alts w
    (fun i hi q hq => all_nonweaker domain p alts h i hi q hq)

end ChierchiaExh


-- ============================================================
-- SECTION 7: Maximize Strength
-- ============================================================

/-!
## Maximize Strength (@cite{chierchia-2013})

A constraint on exhaustification: do not exhaustify a sub-constituent
S inside a matrix S' if doing so globally weakens S'. This blocks
scalar exhaustification of EFCIs in downward-entailing contexts.
-/

section MaximizeStrength

/-- Maximize Strength check: returns `true` if exhaustification does NOT
    globally weaken (i.e., the exhaustified matrix is not strictly weaker
    than the unexhaustified matrix).

    Weakening = every world satisfying the original also satisfies
    the exhaustified version, but not vice versa (the exhaustified
    version is true in strictly more worlds → carries less information). -/
def maximizeStrength {W : Type} (domain : List W)
    (withExh withoutExh : W → Bool) : Bool :=
  let origEntailsExhaust := domain.all fun w => !withoutExh w || withExh w
  let exhaustEntailsOrig := domain.all fun w => !withExh w || withoutExh w
  -- Blocked when exhaustification strictly weakens (orig ⊂ exh in truth-worlds)
  !(origEntailsExhaust && !exhaustEntailsOrig)

end MaximizeStrength


-- ============================================================
-- SECTION 8: IE = NW under NW-Consistency (Bridge Theorem)
-- ============================================================

/-!
## IE = NW: When Exhaustification and Maximize Agree

The two dominant approaches to scalar inference — grammatical exhaustification
(@cite{fox-2007}) and the neo-Gricean Maximize principle (@cite{katzir-2007}
def 21) — make the same predictions when the alternative set satisfies
**NW-consistency**: all non-weaker alternatives can be jointly negated
consistently with the prejacent.

Under NW-consistency, IE = NW: every non-weaker alternative is innocently
excludable, so `exhB` negates exactly the alternatives that the Maximize
principle predicts. This condition holds for all linear Horn scales (where
alternatives are totally ordered by entailment) and fails precisely when
there are symmetric alternatives.

The general theorem `ie_eq_nw_of_nw_consistent` states this at the
proposition level. The concrete Horn scale examples (§9) verify it
computationally.

The connection to tree-level structural alternatives (`violatesMaximize`
from `Structural.lean`) follows because `horn_alternatives_are_structural`
shows that Horn scale substitutions ARE structural alternatives.
-/

section IEeqNW

/-- The disjunction alternative set FAILS NW-consistency: excluding all
    non-weaker alternatives {p, q, p∧q} simultaneously with p∨q is
    unsatisfiable, because (p∨q) ∧ ¬p ∧ ¬q is a contradiction.

    This is the symmetric case: p and q are each other's symmetric
    alternatives. Contrast with `scale3_some_nw_consistent` below,
    where the linear scale has no symmetric pairs. -/
theorem disj_nw_inconsistent :
    exclusionConsistent pqDomain pOrQ disjAlts
      (nonWeakerIndices pqDomain pOrQ disjAlts) = false := by
  native_decide

-- ── Helper definitions for the IE = NW proof ──────────────────

/-- Consistent subsets of NW: sublists of NW that pass the consistency check. -/
private def consistentSubsets {W : Type} (domain : List W)
    (p : W → Bool) (alts : List (W → Bool)) : List (List Nat) :=
  (sublists (nonWeakerIndices domain p alts)).filter
    (exclusionConsistent domain p alts)

/-- Whether some consistent subset strictly contains s. -/
private def dominates (cs : List (List Nat)) (s : List Nat) : Bool :=
  cs.any fun t => t.length > s.length && s.all fun i => t.contains i

private theorem maxConsistentExclusions_eq {W : Type} (domain : List W)
    (p : W → Bool) (alts : List (W → Bool)) :
    maxConsistentExclusions domain p alts =
    (consistentSubsets domain p alts).filter
      fun s => !dominates (consistentSubsets domain p alts) s := rfl

private theorem mem_mce_iff {W : Type} (domain : List W)
    (p : W → Bool) (alts : List (W → Bool)) (s : List Nat) :
    s ∈ maxConsistentExclusions domain p alts ↔
    s ∈ consistentSubsets domain p alts ∧
    dominates (consistentSubsets domain p alts) s = false := by
  simp only [maxConsistentExclusions_eq, dominates, List.mem_filter,
             Bool.not_eq_true']

-- ── Sublists lemmas ───────────────────────────────────────────

private theorem mem_sublists_self {α : Type} (l : List α) :
    l ∈ sublists l := by
  induction l with
  | nil => simp [sublists]
  | cons x xs ih =>
    simp only [sublists, List.mem_append]
    right; rw [List.mem_map]; exact ⟨xs, ih, rfl⟩

private theorem sublists_sub {α : Type} (l sub : List α)
    (h : sub ∈ sublists l) : ∀ x, x ∈ sub → x ∈ l := by
  induction l generalizing sub with
  | nil =>
    simp [sublists] at h; subst h
    intro x hx; exact absurd hx List.not_mem_nil
  | cons a as ih =>
    simp only [sublists, List.mem_append] at h
    rcases h with h | h
    · intro x hx; exact List.mem_cons_of_mem a (ih sub h x hx)
    · rw [List.mem_map] at h
      obtain ⟨t, ht, rfl⟩ := h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem a (ih t ht x hx)

private theorem sublists_length_le {α : Type} (l sub : List α)
    (h : sub ∈ sublists l) : sub.length ≤ l.length := by
  induction l generalizing sub with
  | nil => simp [sublists] at h; subst h; simp
  | cons a as ih =>
    simp only [sublists, List.mem_append] at h
    rcases h with h | h
    · exact Nat.le_succ_of_le (ih sub h)
    · rw [List.mem_map] at h
      obtain ⟨t, ht, rfl⟩ := h
      simp only [List.length_cons]
      exact Nat.add_le_add_right (ih t ht) 1

private theorem sublists_max_length_unique {α : Type} [DecidableEq α]
    (l : List α) (hnd : l.Nodup) (sub : List α)
    (h : sub ∈ sublists l) (hlen : sub.length = l.length) : sub = l := by
  induction l generalizing sub with
  | nil => simp [sublists] at h; exact h
  | cons a as ih =>
    simp only [sublists, List.mem_append] at h
    rcases h with h | h
    · exact absurd (sublists_length_le as sub h) (by simp at hlen; omega)
    · rw [List.mem_map] at h
      obtain ⟨t, ht, rfl⟩ := h
      simp [List.length_cons] at hlen
      congr 1; exact ih (List.nodup_cons.mp hnd).2 t ht hlen

private theorem sublists_proper_shorter {α : Type} [DecidableEq α]
    (l : List α) (hnd : l.Nodup) (sub : List α)
    (h : sub ∈ sublists l) (hne : sub ≠ l) : sub.length < l.length := by
  rcases Nat.lt_or_eq_of_le (sublists_length_le l sub h) with hlt | heq
  · exact hlt
  · exact absurd (sublists_max_length_unique l hnd sub h heq) hne

private theorem sublists_all_mem_contains (l sub : List Nat)
    (h : sub ∈ sublists l) :
    sub.all (fun i => l.contains i) = true := by
  rw [List.all_eq_true]
  intro x hx
  simp only [List.contains_eq_any_beq, List.any_eq_true]
  exact ⟨x, sublists_sub l sub h x hx, beq_self_eq_true x⟩

private theorem nw_nodup {W : Type} (domain : List W) (p : W → Bool)
    (alts : List (W → Bool)) :
    (nonWeakerIndices domain p alts).Nodup :=
  List.nodup_range.sublist List.filter_sublist

-- ── Key lemmas ────────────────────────────────────────────────

/-- NW is not dominated: no sublist of NW is strictly longer than NW. -/
private theorem not_dominates_nw {W : Type} (domain : List W)
    (p : W → Bool) (alts : List (W → Bool)) :
    dominates (consistentSubsets domain p alts)
      (nonWeakerIndices domain p alts) = false := by
  simp only [dominates]
  cases hc : (consistentSubsets domain p alts).any fun t =>
    t.length > (nonWeakerIndices domain p alts).length &&
    (nonWeakerIndices domain p alts).all fun i => t.contains i
  · rfl
  · exfalso
    rw [List.any_eq_true] at hc
    obtain ⟨t, ht, hdom⟩ := hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hdom
    simp only [consistentSubsets, List.mem_filter] at ht
    exact absurd hdom.1 (Nat.not_lt.mpr (sublists_length_le _ t ht.1))

/-- NW is in the MCEs when it is consistent. -/
private theorem nw_mem_mce {W : Type} (domain : List W)
    (p : W → Bool) (alts : List (W → Bool))
    (h : exclusionConsistent domain p alts
      (nonWeakerIndices domain p alts) = true) :
    nonWeakerIndices domain p alts ∈ maxConsistentExclusions domain p alts := by
  rw [mem_mce_iff]
  constructor
  · simp only [consistentSubsets, List.mem_filter]
    exact ⟨mem_sublists_self _, h⟩
  · exact not_dominates_nw domain p alts

/-- Any proper subset of NW is dominated by NW when NW is consistent. -/
private theorem dominates_proper_subset {W : Type} (domain : List W)
    (p : W → Bool) (alts : List (W → Bool))
    (h : exclusionConsistent domain p alts
      (nonWeakerIndices domain p alts) = true)
    (s : List Nat)
    (hs_sub : s ∈ sublists (nonWeakerIndices domain p alts))
    (hne : s ≠ nonWeakerIndices domain p alts) :
    dominates (consistentSubsets domain p alts) s = true := by
  simp only [dominates, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨nonWeakerIndices domain p alts, ?_, ?_, ?_⟩
  · simp only [consistentSubsets, List.mem_filter]
    exact ⟨mem_sublists_self _, h⟩
  · exact sublists_proper_shorter _ (nw_nodup domain p alts) s hs_sub hne
  · exact sublists_all_mem_contains _ s hs_sub

/-- Every MCE equals NW when NW is consistent. -/
private theorem mce_eq_nw {W : Type} (domain : List W)
    (p : W → Bool) (alts : List (W → Bool))
    (h : exclusionConsistent domain p alts
      (nonWeakerIndices domain p alts) = true)
    (s : List Nat)
    (hs : s ∈ maxConsistentExclusions domain p alts) :
    s = nonWeakerIndices domain p alts := by
  rw [mem_mce_iff] at hs
  obtain ⟨hs_cons, hs_nodom⟩ := hs
  simp only [consistentSubsets, List.mem_filter] at hs_cons
  rcases Decidable.em (s = nonWeakerIndices domain p alts) with rfl | hne
  · rfl
  · exfalso
    have := dominates_proper_subset domain p alts h s hs_cons.1 hne
    simp [this] at hs_nodom

private theorem self_contains (l : List Nat) (i : Nat) (hi : i ∈ l) :
    l.contains i = true := by
  simp only [List.contains_eq_any_beq, List.any_eq_true]
  exact ⟨i, hi, beq_self_eq_true i⟩

private theorem filter_all_true_of {α : Type} (l : List α) (f : α → Bool)
    (hf : ∀ x ∈ l, f x = true) : l.filter f = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filter_cons, hf x List.mem_cons_self]
    simp only [ite_true, List.cons.injEq, true_and]
    exact ih (fun y hy => hf y (List.mem_cons_of_mem x hy))

-- ── Main theorem ──────────────────────────────────────────────

/-- When all non-weaker alternatives are jointly consistently excludable,
    IE = NW: every non-weaker alternative is innocently excludable.

    **Proof**: NW is consistent (hypothesis), so NW ∈ MCEs (`nw_mem_mce`).
    Every MCE equals NW (`mce_eq_nw`): any proper subset of NW is dominated
    by NW itself (which is consistent and strictly longer). Therefore the
    intersection of all MCEs is NW.

    **Counterexample when the condition fails**: p = A∨B, ALT = {A∨B, A, B, A∧B}.
    NW = {A, B, A∧B}. Excluding A and B jointly is inconsistent with A∨B.
    MCEs = {{B, A∧B}, {A, A∧B}}. IE = {A∧B} ⊊ NW. See `disj_ie` and
    `disj_nw_inconsistent` above.

    **Connection to Maximize**: When IE = NW, `exhB` negates all non-weaker
    alternatives. For linear scales, non-weaker = strictly stronger, so this
    matches the Maximize principle's prediction exactly. The two mechanisms
    agree whenever the alternative set is well-behaved (no symmetry). When
    symmetry is present, IE is more conservative (avoids inconsistency),
    while Maximize needs additional constraints (like Katzir's structural
    restriction) to avoid over-generation. -/
theorem ie_eq_nw_of_nw_consistent {W : Type} (domain : List W)
    (p : W → Bool) (alts : List (W → Bool))
    (h : exclusionConsistent domain p alts
      (nonWeakerIndices domain p alts) = true) :
    ieIndices domain p alts = nonWeakerIndices domain p alts := by
  unfold ieIndices
  have all_eq : ∀ s ∈ maxConsistentExclusions domain p alts,
      s = nonWeakerIndices domain p alts :=
    fun s hs => mce_eq_nw domain p alts h s hs
  have nw_mem := nw_mem_mce domain p alts h
  generalize maxConsistentExclusions domain p alts = mces at *
  rcases mces with _ | ⟨first, rest⟩
  · exact absurd nw_mem List.not_mem_nil
  · have hfirst := all_eq first List.mem_cons_self
    have hrest : ∀ s ∈ rest, s = nonWeakerIndices domain p alts :=
      fun s hs => all_eq s (List.mem_cons_of_mem _ hs)
    rw [hfirst]
    apply filter_all_true_of
    intro i hi
    rw [List.all_eq_true]
    intro mce hmce
    rw [hrest mce hmce]
    exact self_contains _ i hi

end IEeqNW


-- ============================================================
-- SECTION 9: Three-Point Horn Scale ⟨some, most, all⟩
-- ============================================================

/-!
## Worked Example: Three-Point Horn Scale

The scale ⟨some, most, all⟩ demonstrates the Maximize–exhaustification
agreement on a non-trivial linear scale. For each scale position:

- **Prejacent = "some"**: NW = {most, all}, NW-consistent ✓,
  IE = NW, exh(some) = some ∧ ¬most ∧ ¬all
- **Prejacent = "most"**: NW = {all}, NW-consistent ✓,
  IE = NW, exh(most) = most ∧ ¬all
- **Prejacent = "all"**: NW = ∅, IE = ∅, exh(all) = all

In each case, exhB negates exactly the strictly stronger alternatives,
matching the Maximize prediction.
-/

section HornScale

/-- Four-world model for a three-point quantity scale. -/
inductive ScaleW3 where
  | none_ | someFew | most_ | all_
  deriving Repr, DecidableEq

def scale3Domain : List ScaleW3 := [.none_, .someFew, .most_, .all_]

def scaleSome : ScaleW3 → Bool | .someFew | .most_ | .all_ => true | _ => false
def scaleMost : ScaleW3 → Bool | .most_ | .all_ => true | _ => false
def scaleAll  : ScaleW3 → Bool | .all_ => true | _ => false

/-- Alternatives for the Horn scale ⟨some, most, all⟩. -/
def scale3Alts : List (ScaleW3 → Bool) := [scaleSome, scaleMost, scaleAll]

-- ── Entailment chain (linearity) ───────────────────────────

/-- The scale is linear: all ⊆ most ⊆ some (entailment ordering). -/
theorem scale3_all_entails_most :
    ∀ w : ScaleW3, scaleAll w = true → scaleMost w = true := by
  intro w h; cases w <;> simp_all [scaleAll, scaleMost]

theorem scale3_most_entails_some :
    ∀ w : ScaleW3, scaleMost w = true → scaleSome w = true := by
  intro w h; cases w <;> simp_all [scaleMost, scaleSome]

-- ── Prejacent = "some" ─────────────────────────────────────

/-- Non-weaker alternatives for "some": most (1) and all (2). -/
theorem scale3_some_nw :
    nonWeakerIndices scale3Domain scaleSome scale3Alts = [1, 2] := by
  native_decide

/-- NW-consistency holds: (some ∧ ¬most ∧ ¬all) is satisfiable at .someFew. -/
theorem scale3_some_nw_consistent :
    exclusionConsistent scale3Domain scaleSome scale3Alts
      (nonWeakerIndices scale3Domain scaleSome scale3Alts) = true := by
  native_decide

/-- **IE = NW for "some"**: all non-weaker alternatives are innocently
    excludable. No symmetric alternatives exist on a linear scale. -/
theorem scale3_some_ie_eq_nw :
    ieIndices scale3Domain scaleSome scale3Alts =
    nonWeakerIndices scale3Domain scaleSome scale3Alts := by
  native_decide

/-- **exh(some) = some ∧ ¬most ∧ ¬all**: exhaustification negates both
    strictly stronger alternatives, matching the Maximize prediction.
    True only at world .someFew — the "some but not most" reading. -/
theorem scale3_exh_some :
    ∀ w : ScaleW3, exhB scale3Domain scale3Alts scaleSome w =
      (scaleSome w && !scaleMost w && !scaleAll w) := by
  intro w; cases w <;> native_decide

-- ── Prejacent = "most" ─────────────────────────────────────

/-- Non-weaker alternatives for "most": only all (2). -/
theorem scale3_most_nw :
    nonWeakerIndices scale3Domain scaleMost scale3Alts = [2] := by
  native_decide

/-- NW-consistency for "most": (most ∧ ¬all) is satisfiable at .most_. -/
theorem scale3_most_nw_consistent :
    exclusionConsistent scale3Domain scaleMost scale3Alts
      (nonWeakerIndices scale3Domain scaleMost scale3Alts) = true := by
  native_decide

/-- **IE = NW for "most"**: all is the only non-weaker alternative
    and is innocently excludable. -/
theorem scale3_most_ie_eq_nw :
    ieIndices scale3Domain scaleMost scale3Alts =
    nonWeakerIndices scale3Domain scaleMost scale3Alts := by
  native_decide

/-- **exh(most) = most ∧ ¬all**: exhaustification negates the single
    strictly stronger alternative, matching the Maximize prediction.
    True at .most_ — the "most but not all" reading. -/
theorem scale3_exh_most :
    ∀ w : ScaleW3, exhB scale3Domain scale3Alts scaleMost w =
      (scaleMost w && !scaleAll w) := by
  intro w; cases w <;> native_decide

-- ── Prejacent = "all" ──────────────────────────────────────

/-- No non-weaker alternatives for "all": it entails everything on the scale. -/
theorem scale3_all_nw_empty :
    nonWeakerIndices scale3Domain scaleAll scale3Alts = [] := by
  native_decide

/-- **exh(all) = all**: the strongest element has no alternatives to negate. -/
theorem scale3_exh_all :
    ∀ w : ScaleW3, exhB scale3Domain scale3Alts scaleAll w = scaleAll w := by
  intro w; cases w <;> native_decide

end HornScale


end Exhaustification.InnocentExclusion
