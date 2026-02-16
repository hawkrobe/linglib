/-
# Bulgarian Long Head Movement: A Formal Analysis

This file proves that Bulgarian Long Head Movement (LHM) violates the
Head Movement Constraint (HMC), formalizing the argument in Harizanov (2019).

## The Empirical Pattern

Bulgarian participle fronting (Lambova 2004c:274, (15)):

    Pročeli   bjaha      studentite     statijata.
    read      be.3p.pst  the.students   the.article
    'The students had read the article.'

The participle "pročeli" appears BEFORE the auxiliary "bjaha", suggesting it has
moved to a position above T (the auxiliary's head).

## The Theoretical Claim

Harizanov argues this is HEAD-TO-SPECIFIER movement:
- The verb moves from its base position (in VP) to Spec-TP
- At Spec-TP, the verb becomes a MAXIMAL PROJECTION (a phrase)
- This contrasts with head-to-head movement where the verb stays minimal

## What We Prove

1. The verb is maximal at its derived position (Spec-TP)
2. Bulgarian LHM instantiates head-to-specifier movement
3. All head-to-specifier movement violates the HMC
4. Therefore: Bulgarian LHM violates the HMC

## References

- Harizanov, B. "Syntactic Head Movement: Elements in Generative Syntax"
  - Bulgarian data: Section 4.1.1, pp.19-21, examples (29), (48), (52)
  - Maximality claim: Section 4.2, p.29
  - HMC violation: Section 3.1, p.12; Section 4.2, p.29
- Lambova (2004c:274, (15)): Original Bulgarian data
- Collins, C. & E. Stabler (2016). "A Formalization of Minimalist Syntax"
  - Position-indexed maximality: Section 3.4
-/

import Linglib.Theories.Syntax.Minimalism.Formal.Constraints.HMC
import Linglib.Phenomena.WordOrder.VerbPosition

namespace Minimalism.Phenomena.HeadMovement.BulgarianLHM

open Phenomena.WordOrderAlternations.VerbPosition

/-! ## Part 1: The Lexicon

We define the lexical items for the Bulgarian sentence from Harizanov (2019).
Each item has a category (V, N, D, T) and selectional requirements.

    Pročeli   bjaha      studentite     statijata.
    read      be.3p.pst  the.students   the.article
-/

/-- The participle "pročeli" (read): category V, selects a D (object) -/
def verbProceli : LIToken := ⟨.simple .V [.D], 201⟩

/-- The auxiliary "bjaha" (be.3p.pst): category T, selects V -/
def auxBjaha : LIToken := ⟨.simple .T [.V], 206⟩

/-- Determiner: category D, selects N -/
def detBg : LIToken := ⟨.simple .D [.N], 204⟩

/-- "studentite" (the students): category N -/
def nounStudentite : LIToken := ⟨.simple .N [], 202⟩

/-- "statijata" (the article): category N -/
def nounStatijata : LIToken := ⟨.simple .N [], 203⟩

/-! ## Part 2: Syntactic Structure BEFORE Movement

We build the clause structure with the verb in its base position.
This corresponds to Harizanov's structure (52) on p.21, before V raises.

```
         T'
        /  \
       T    VP
    bjaha  /  \
         DP    V'
   studentite /  \
             V    DP
         pročeli  statijata
```
-/

/-- The participle as a syntactic object -/
def theVerb : SyntacticObject := .leaf verbProceli

/-- DP "statijata" (the article) = {D, N} -/
def dpStatijata : SyntacticObject := .node (.leaf detBg) (.leaf nounStatijata)

/-- DP "studentite" (the students) = {D, N} -/
def dpStudentite : SyntacticObject := .node (.leaf detBg) (.leaf nounStudentite)

/-- VP = {V, DP_object} — the verb's base position -/
def vpBefore : SyntacticObject := .node theVerb dpStatijata

/-- V' = {DP_subject, VP} (subject in Spec-VP for simplicity) -/
def vBarBefore : SyntacticObject := .node dpStudentite vpBefore

/-- T' = {T, V'} — the target for movement -/
def tBarBefore : SyntacticObject := .node (.leaf auxBjaha) vBarBefore

/-! ## Part 3: Syntactic Structure AFTER Movement

The participle moves to Spec-TP, yielding verb-initial order:

```
        TP
       /  \
  pročeli  T'
          /  \
         T    VP
       bjaha /  \
           DP    V'
      studentite /  \
               (V)   DP
                   statijata
```

The participle now appears at the LEFT edge (specifier position).
Under copy theory, a copy remains in VP.

This derives: "Pročeli bjaha studentite statijata"
             (read   had   the.students the.article)
-/

/-- TP after movement = {participle, T'} -/
def tpAfterLHM : SyntacticObject := .node theVerb tBarBefore

/-! ## Part 4: The Movement Operation

We package the movement as a `Movement` structure, which records:
- What moved (the participle)
- Where it moved from (contained in T')
- The result (TP with participle in Spec)
-/

/-- The participle is contained within T' (it's deeply embedded in VP) -/
theorem verb_in_target : contains tBarBefore theVerb := by
  -- Trace the path: T' contains V' contains VP contains V
  apply contains.trans _ _ vBarBefore; exact Or.inr rfl
  apply contains.trans _ _ vpBefore; exact Or.inr rfl
  apply contains.imm; exact Or.inl rfl

/-- Bulgarian LHM as a Movement structure -/
def bulgarianLHM : Movement where
  mover := theVerb           -- what moves (pročeli)
  target := tBarBefore       -- where it moves from (Internal Merge)
  result := tpAfterLHM       -- the resulting structure
  mover_in_target := verb_in_target
  is_merge := rfl            -- result = merge(mover, target)

/-! ## Part 5: The Key Property — Maximality at Derived Position

The crucial claim: the participle is MAXIMAL at Spec-TP.

Being "maximal" means: NOT PROJECTING (not passing its label upward).
At Spec-TP, the participle doesn't project because T' projects instead.

We formalize this using POSITION-SPECIFIC maximality (Collins & Stabler 2016):
- A position is a path from the root (here: "go left" = Spec)
- We check projection only at THAT position
- This handles copy theory correctly (verb projects in VP but not at Spec-TP)
-/

/-- The derived position: Spec = left daughter of root -/
def verbDerivedPosition : TreePos := derivedSpecPosition

/-- VERIFIED: The participle is located at Spec-TP -/
theorem verb_at_derived_position :
    atPosition tpAfterLHM verbDerivedPosition = some theVerb := by
  simp [verbDerivedPosition, derivedSpecPosition, atPosition, tpAfterLHM]

/-- VERIFIED: The participle does NOT project at Spec-TP

    Why? The parent (TP) has label T, but the participle has label V.
    Since T ≠ V, the participle doesn't project. -/
theorem verb_does_not_project_at_derived :
    ¬projectsAtPosition theVerb tpAfterLHM verbDerivedPosition := by
  unfold projectsAtPosition
  intro ⟨_, hProj⟩
  have hParent : parentSO tpAfterLHM verbDerivedPosition = some tpAfterLHM :=
    by simp [parentSO, parentPos, verbDerivedPosition, derivedSpecPosition, atPosition]
  simp only [hParent] at hProj
  -- hProj claims: label(verb) = label(TP). But V ≠ T.
  unfold sameLabel at hProj
  obtain ⟨hEq, _⟩ := hProj
  have h1 : label theVerb = some verbProceli.item := rfl
  have h2 : label tpAfterLHM = some auxBjaha.item := by native_decide
  rw [h1, h2] at hEq
  simp only [Option.some.injEq] at hEq
  have : verbProceli.item.features ≠ auxBjaha.item.features := by native_decide
  exact this (congrArg LexicalItem.features hEq)

/-- VERIFIED: The participle is maximal at its derived position -/
theorem verb_maximal_at_derived :
    isMaximalAtPosition theVerb tpAfterLHM verbDerivedPosition :=
  ⟨verb_at_derived_position, verb_does_not_project_at_derived⟩

/-! ## Part 6: Verifying Head-to-Specifier Movement

We now verify all the conditions for head-to-specifier movement:

1. **Mover was a head**: V projected in VP (it was -maximal there)
2. **Mover is now maximal**: V doesn't project at Spec-TP
3. **Target projects**: T' determines the label of TP
-/

/-- VERIFIED: The participle was a HEAD in the source structure

    In VP, the participle PROJECTS (V selects D, so V's label becomes VP's label).
    Projecting means -maximal, i.e., being a head. -/
theorem verb_was_head_in_target : isHeadIn theVerb tBarBefore := by
  unfold isHeadIn isMinimalIn
  constructor
  · -- V is minimal (it's a leaf) and is a term of T'
    constructor
    · unfold isTermOf; exact Or.inr verb_in_target
    · simp only [theVerb]
  · -- V is NOT maximal in T' (because V projects in VP)
    unfold isMaximalIn
    intro ⟨_, hNoProj⟩
    apply hNoProj
    use vpBefore
    constructor
    · unfold isTermOf; right
      apply contains.trans _ _ vBarBefore; exact Or.inr rfl
      apply contains.imm; exact Or.inr rfl
    · -- V projects in VP: V is daughter of VP and label(V) = label(VP)
      unfold projectsIn immediatelyContains sameLabel
      constructor
      · exact Or.inl rfl
      · constructor <;> native_decide

/-- VERIFIED: T' projects in the result (T' is the "head" of TP) -/
theorem tbar_projects_in_result : projectsIn tBarBefore tpAfterLHM := by
  unfold projectsIn immediatelyContains sameLabel
  constructor
  · exact Or.inr rfl
  · constructor <;> native_decide

/-! ## Part 7: Main Results

We can now state and prove the main theorems.
-/

/-- Bulgarian LHM is head-to-specifier movement (all conditions verified) -/
def bulgarianLHM_h2s_positional : HeadToSpecMovementPositional where
  toMovement := bulgarianLHM
  mover_was_head := verb_was_head_in_target
  mover_maximal_at_derived := verb_maximal_at_derived
  target_projects := tbar_projects_in_result

/-- **MAIN THEOREM 1**: The participle is maximal at Spec-TP

    This formalizes Harizanov's claim (Section 4.2, p.29):
    "The head X is therefore a maximal projection in its derived position—
    though it is of course also minimal, as it is a lexical item"

    The Bulgarian example structure is given as (52) on p.21. -/
theorem bulgarian_lhm_is_head_to_spec :
    isMaximalAtPosition bulgarianLHM.mover bulgarianLHM.result derivedSpecPosition :=
  verb_maximal_at_derived

/-- **MAIN THEOREM 2**: Bulgarian LHM violates the Head Movement Constraint

    This formalizes the claim (Section 3.1, p.12; Section 4.2, p.29):
    "head-to-specifier movement violates the Head Movement Constraint"

    The participle moves from VP to Spec-TP, becoming maximal at its derived position.
    By the universal theorem that head-to-specifier movement violates HMC,
    Bulgarian LHM violates HMC. ∎ -/
theorem bulgarian_lhm_violates_hmc_positional :
    violatesHMC_positional bulgarianLHM tpAfterLHM derivedSpecPosition :=
  head_to_spec_violates_hmc_positional bulgarianLHM_h2s_positional

-- Grounding: Connection to Theory-Neutral Phenomena Data

/-- The Minimalist analysis models the fronted order from the phenomena data. -/
theorem models_fronted_order :
    bulgarianExample.fronted = "Pročeli bjaha studentite statijata" := rfl

/-- The Minimalist analysis correctly captures that both orders are grammatical.
    The unfronted order would be derived without the LHM operation. -/
theorem captures_alternation :
    bulgarianExample.bothGrammatical = true := rfl

/-- The derivation produces the participle-initial order (V precedes Aux). -/
theorem derivation_yields_fronted_order :
    -- The mover (participle) is in specifier position (left daughter of root)
    tpAfterLHM.isNode ∧
    (match tpAfterLHM with
     | .node left _ => left = theVerb
     | .leaf _ => False) := by
  constructor
  · rfl
  · rfl

end Minimalism.Phenomena.HeadMovement.BulgarianLHM
