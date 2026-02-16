/-
# Germanic V2: An Existence Proof of HMC Violation via Head-to-Head Movement

This file analyzes Germanic V2 as HEAD-TO-HEAD movement, showing that the verb
moves directly to C, skipping T. This provides an existence proof that
head-to-head movement CAN violate the HMC.

## Contrast with Bulgarian LHM

| | Bulgarian LHM | Germanic V2 |
|---|---------------|-------------|
| Type | Head-to-specifier | Head-to-head |
| Mover at landing | +maximal (phrase) | +minimal (head) |
| HMC violation | NECESSARY (by maximality) | CONTINGENT (by skipping T) |
| Proof type | Universal theorem | Existence proof |

## The Empirical Pattern

German root clauses show V2 order (Vikner 1995:32, (11d)):

    Diesen Film haben die Kinder gesehen.
    this   film have  the children seen
    'The children have seen this film.'

The finite verb "haben" occupies C, preceding the subject.

## The Analysis

From Harizanov (Section 5.1.2, p.35-36):
- In embedded non-V2 clauses, V does NOT raise to T (stays below adverbs/negation)
- In V2 clauses, V raises DIRECTLY to C
- Therefore V skips T, violating the HMC

## References

- Harizanov, B. "Syntactic Head Movement"
  - V2 data: Section 5.1.1, pp.31-35, example (35)
  - HMC violation: Section 5.1.2, pp.35-36
  - Complex LIs: Section 5.2, pp.37-41
- Vikner (1995:32, (11d)): Original German data
- den Besten (1977/1983)
-/

import Linglib.Theories.Syntax.Minimalism.Formal.Constraints.HMC

namespace Minimalism.Phenomena.HeadMovement.GermanicV2

/-! ## Part 1: The Lexicon

We define the lexical items for the German sentence from Harizanov (2019).

    Diesen Film haben die Kinder gesehen.
    this   film have  the children seen
-/

/-- The COMPLEX finite verb "haben" (have): both V and C features

    Following Harizanov (Section 5.2), V2 verbs are categorially complex:
    - V-component projects in base position
    - C-component projects in derived position -/
def verbHaben : LIToken :=
  ⟨(LexicalItem.simple .V [.D]).combine (LexicalItem.simple .C [.T]), 307⟩

/-- Tense head: category T, selects V -/
def tenseHead : LIToken := ⟨.simple .T [.V], 306⟩

/-- Complementizer "dass" (that): category C, selects T -/
def compDass : LIToken := ⟨.simple .C [.T], 308⟩

/-- Determiner "die/diesen": category D, selects N -/
def detGer : LIToken := ⟨.simple .D [.N], 304⟩

/-- "Kinder" (children): category N -/
def nounKinder : LIToken := ⟨.simple .N [], 302⟩

/-- "Film" (film): category N -/
def nounFilm : LIToken := ⟨.simple .N [], 303⟩

/-! ## Part 2: Structure

```
        CP
       /  \
    haben  TP
          /  \
    die Kinder  T'
               /  \
              T    VP
                  /  \
              haben  diesen Film
```
-/

def theFiniteVerb : SyntacticObject := .leaf verbHaben
def theT : SyntacticObject := .leaf tenseHead

/-- DP "diesen Film" (this film) = {D, N} -/
def dpDiesenFilm : SyntacticObject := .node (.leaf detGer) (.leaf nounFilm)

/-- DP "die Kinder" (the children) = {D, N} -/
def dpDieKinder : SyntacticObject := .node (.leaf detGer) (.leaf nounKinder)

/-- VP = {V, DP_object} -/
def vpV2 : SyntacticObject := .node theFiniteVerb dpDiesenFilm

/-- T' = {T, VP} -/
def tBarV2 : SyntacticObject := .node theT vpV2

/-- TP = {DP_subject, T'} -/
def tpV2 : SyntacticObject := .node dpDieKinder tBarV2

/-- CP after V2 = {V, TP} — verb reprojects its C-features -/
def cpV2 : SyntacticObject := .node theFiniteVerb tpV2

/-! ## Part 3: Movement Structure -/

theorem verb_in_tp : contains tpV2 theFiniteVerb := by
  apply contains.trans _ _ tBarV2; exact Or.inr rfl
  apply contains.trans _ _ vpV2; exact Or.inr rfl
  apply contains.imm; exact Or.inl rfl

def germanicV2Movement : Movement where
  mover := theFiniteVerb
  target := tpV2
  result := cpV2
  mover_in_target := verb_in_tp
  is_merge := rfl

/-! ## Part 4: Head-to-Head Properties

The verb stays MINIMAL (a head) at C. It reprojects its C-features.
This is the defining property of head-to-head movement.
-/

theorem verb_minimal_in_result : isMinimalIn theFiniteVerb cpV2 := by
  unfold isMinimalIn isTermOf
  constructor
  · right; exact contains.imm _ _ (Or.inl rfl)
  · simp only [theFiniteVerb]

theorem verb_was_head_in_target : isHeadIn theFiniteVerb tpV2 := by
  unfold isHeadIn isMinimalIn isTermOf
  constructor
  · constructor
    · right; exact verb_in_tp
    · simp only [theFiniteVerb]
  · -- Not maximal: projects in VP
    unfold isMaximalIn
    intro ⟨_, hNoProj⟩
    apply hNoProj
    use vpV2
    constructor
    · unfold isTermOf; right
      apply contains.trans _ _ tBarV2; exact Or.inr rfl
      exact contains.imm _ _ (Or.inr rfl)
    · unfold projectsIn immediatelyContains sameLabel
      constructor
      · exact Or.inl rfl
      · constructor <;> native_decide

/-! ## Part 5: The Key Claim — T Intervenes

This is the existence proof: we show T is between V and C,
so V2 violates the HMC.
-/

/-- T is a head in the result structure -/
theorem t_is_head_in_result : isHeadIn theT cpV2 := by
  unfold isHeadIn isMinimalIn isTermOf
  constructor
  · constructor
    · right
      apply contains.trans _ _ tpV2; exact Or.inr rfl
      apply contains.trans _ _ tBarV2; exact Or.inr rfl
      exact contains.imm _ _ (Or.inl rfl)
    · simp only [theT]
  · -- Not maximal: projects in T'
    unfold isMaximalIn
    intro ⟨_, hNoProj⟩
    apply hNoProj
    use tBarV2
    constructor
    · unfold isTermOf; right
      apply contains.trans _ _ tpV2; exact Or.inr rfl
      exact contains.imm _ _ (Or.inr rfl)
    · unfold projectsIn immediatelyContains sameLabel
      constructor
      · exact Or.inl rfl
      · constructor <;> native_decide

/-- T ≠ V (they have different LI tokens) -/
theorem t_neq_v : theT ≠ theFiniteVerb := by native_decide

/-- T ≠ TP (T is a leaf, TP is a node) -/
theorem t_neq_tp : theT ≠ tpV2 := by native_decide

/-! ## Part 6: Main Results -/

/-- **MAIN THEOREM**: T intervenes between V and C in V2

    This establishes the structural condition for HMC violation.
    V moves to C, but T is between V's base position and C.

    From Harizanov (p.35-36): "verb raises directly to its final
    landing site, moving across any and all intervening functional heads" -/
theorem t_intervenes_in_v2 :
    isHeadIn theT cpV2 ∧
    theT ≠ theFiniteVerb ∧
    theT ≠ tpV2 ∧
    contains tpV2 theT ∧
    contains tBarV2 theFiniteVerb :=
  ⟨t_is_head_in_result, t_neq_v, t_neq_tp,
   contains.trans _ _ tBarV2 (Or.inr rfl) (contains.imm _ _ (Or.inl rfl)),
   contains.trans _ _ vpV2 (Or.inr rfl) (contains.imm _ _ (Or.inl rfl))⟩

/-- V2 is head-to-head movement (mover stays minimal)

    Unlike head-to-specifier where the mover becomes maximal,
    in head-to-head the mover reprojects and stays a head. -/
theorem v2_mover_stays_minimal :
    isMinimalIn germanicV2Movement.mover germanicV2Movement.result :=
  verb_minimal_in_result

/-! ## Appendix: Summary of Harizanov's Typology

**Head-to-specifier** (e.g., Bulgarian LHM):
- Mover becomes +maximal in derived position
- Target projects (mover is a specifier)
- NECESSARILY violates HMC (by maximality argument)
- Can be unbounded (like phrasal A-bar movement)

**Head-to-head** (e.g., Germanic V2):
- Mover stays +minimal in derived position
- Mover reprojects (has complex LI)
- CAN violate HMC (when skipping heads, as V2 does)
- Phase-bounded (cannot apply successive-cyclically)

**Amalgamation** (e.g., French V-to-T):
- Post-syntactic (PF) operation
- MUST respect HMC
- Results in morphological fusion
-/

end Minimalism.Phenomena.HeadMovement.GermanicV2
