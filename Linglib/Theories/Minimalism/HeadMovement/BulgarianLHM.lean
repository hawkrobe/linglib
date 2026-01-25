/-
# Bulgarian Long Head Movement: A Formal Analysis

This file proves that Bulgarian Long Head Movement (LHM) violates the
Head Movement Constraint (HMC), formalizing the argument in Harizanov (2019).

## The Empirical Pattern

Bulgarian yes/no questions show verb-initial order:

    Prodade  li  Ivan  kolata?
    sold     Q   Ivan  car.the
    "Did Ivan sell the car?"

The verb "prodade" appears BEFORE the Q-particle "li", suggesting it has
moved to a position above C (the Q-particle's head).

## The Theoretical Claim

Harizanov argues this is HEAD-TO-SPECIFIER movement:
- The verb moves from its base position (in VP) to Spec-CP
- At Spec-CP, the verb becomes a MAXIMAL PROJECTION (a phrase)
- This contrasts with head-to-head movement where the verb stays minimal

## What We Prove

1. The verb is maximal at its derived position (Spec-CP)
2. Bulgarian LHM instantiates head-to-specifier movement
3. All head-to-specifier movement violates the HMC
4. Therefore: Bulgarian LHM violates the HMC

## How to Read This File

- `def` introduces a definition (a named object)
- `theorem` states a claim that Lean has verified
- `by ...` is a proof; the details can be skipped
- `/-- ... -/` are documentation comments explaining what follows

## References

- Harizanov, B. "Syntactic Head Movement: Elements in Generative Syntax"
  - Bulgarian data: Section 4.1.1, pp.19-21, examples (47)-(52)
  - Maximality claim: Section 4.2, p.29
  - HMC violation: Section 3.1, p.12; Section 4.2, p.29
- Collins, C. & E. Stabler (2016). "A Formalization of Minimalist Syntax"
  - Position-indexed maximality: Section 3.4
-/

import Linglib.Theories.Minimalism.Constraints.HMC

namespace Minimalism.BulgarianLHM

/-! ## Part 1: The Lexicon

We define the lexical items for the Bulgarian sentence.
Each item has a category (V, N, D, C, T) and selectional requirements.
-/

/-- The verb "prodade" (sold): category V, selects a D (object) -/
def verbProdade : LIToken := ⟨.simple .V [.D], 201⟩

/-- The Q-particle "li": category C, selects T -/
def compLi : LIToken := ⟨.simple .C [.T], 205⟩

/-- Tense head: category T, selects V -/
def tenseBg : LIToken := ⟨.simple .T [.V], 206⟩

/-- Determiner: category D, selects N -/
def detBg : LIToken := ⟨.simple .D [.N], 204⟩

/-- "Ivan": category N -/
def nounIvan : LIToken := ⟨.simple .N [], 202⟩

/-- "kolata" (the car): category N -/
def nounKolata : LIToken := ⟨.simple .N [], 203⟩

/-! ## Part 2: Syntactic Structure BEFORE Movement

We build the clause structure with the verb in its base position.

```
        C'
       /  \
      li   TP
          /  \
       Ivan   T'
             /  \
            T    VP
                /  \
           prodade  kolata
```
-/

/-- The verb as a syntactic object -/
def theVerb : SyntacticObject := .leaf verbProdade

/-- DP "kolata" = {D, N} -/
def dpKolata : SyntacticObject := .node (.leaf detBg) (.leaf nounKolata)

/-- DP "Ivan" = {D, N} -/
def dpIvan : SyntacticObject := .node (.leaf detBg) (.leaf nounIvan)

/-- VP = {V, DP_object} — the verb's base position -/
def vpBefore : SyntacticObject := .node theVerb dpKolata

/-- T' = {T, VP} -/
def tBarBefore : SyntacticObject := .node (.leaf tenseBg) vpBefore

/-- TP = {DP_subject, T'} -/
def tpBefore : SyntacticObject := .node dpIvan tBarBefore

/-- C' = {C, TP} — the target for movement -/
def cBarBefore : SyntacticObject := .node (.leaf compLi) tpBefore

/-! ## Part 3: Syntactic Structure AFTER Movement

The verb moves to Spec-CP, yielding verb-initial order:

```
        CP
       /  \
   prodade  C'
           /  \
          li   TP
              /  \
           Ivan   T'
                 /  \
                T    VP
                    /  \
                  (V)   kolata
```

The verb now appears at the LEFT edge (specifier position).
Under copy theory, a copy remains in VP.
-/

/-- CP after movement = {verb, C'} -/
def cpAfterLHM : SyntacticObject := .node theVerb cBarBefore

/-! ## Part 4: The Movement Operation

We package the movement as a `Movement` structure, which records:
- What moved (the verb)
- Where it moved from (contained in C')
- The result (CP with verb in Spec)
-/

/-- The verb is contained within C' (it's deeply embedded in VP) -/
theorem verb_in_target : contains cBarBefore theVerb := by
  -- Trace the path: C' contains TP contains T' contains VP contains V
  apply contains.trans _ _ tpBefore; exact Or.inr rfl
  apply contains.trans _ _ tBarBefore; exact Or.inr rfl
  apply contains.trans _ _ vpBefore; exact Or.inr rfl
  apply contains.imm; exact Or.inl rfl

/-- Bulgarian LHM as a Movement structure -/
def bulgarianLHM : Movement where
  mover := theVerb           -- what moves
  target := cBarBefore       -- where it moves from (Internal Merge)
  result := cpAfterLHM       -- the resulting structure
  mover_in_target := verb_in_target
  is_merge := rfl            -- result = merge(mover, target)

/-! ## Part 5: The Key Property — Maximality at Derived Position

The crucial claim: the verb is MAXIMAL at Spec-CP.

Being "maximal" means: NOT PROJECTING (not passing its label upward).
At Spec-CP, the verb doesn't project because C' projects instead.

We formalize this using POSITION-SPECIFIC maximality (Collins & Stabler 2016):
- A position is a path from the root (here: "go left" = Spec)
- We check projection only at THAT position
- This handles copy theory correctly (verb projects in VP but not at Spec-CP)
-/

/-- The derived position: Spec = left daughter of root -/
def verbDerivedPosition : TreePos := derivedSpecPosition

/-- VERIFIED: The verb is located at Spec-CP -/
theorem verb_at_derived_position :
    atPosition cpAfterLHM verbDerivedPosition = some theVerb := by
  simp [verbDerivedPosition, derivedSpecPosition, atPosition, cpAfterLHM]

/-- VERIFIED: The verb does NOT project at Spec-CP

    Why? The parent (CP) has label C, but the verb has label V.
    Since C ≠ V, the verb doesn't project. -/
theorem verb_does_not_project_at_derived :
    ¬projectsAtPosition theVerb cpAfterLHM verbDerivedPosition := by
  unfold projectsAtPosition
  intro ⟨_, hProj⟩
  have hParent : parentSO cpAfterLHM verbDerivedPosition = some cpAfterLHM :=
    by simp [parentSO, parentPos, verbDerivedPosition, derivedSpecPosition, atPosition]
  simp only [hParent] at hProj
  -- hProj claims: label(verb) = label(CP). But V ≠ C.
  unfold sameLabel at hProj
  obtain ⟨hEq, _⟩ := hProj
  have h1 : label theVerb = some verbProdade.item := rfl
  have h2 : label cpAfterLHM = some compLi.item := by native_decide
  rw [h1, h2] at hEq
  simp only [Option.some.injEq] at hEq
  have : verbProdade.item.features ≠ compLi.item.features := by native_decide
  exact this (congrArg LexicalItem.features hEq)

/-- VERIFIED: The verb is maximal at its derived position -/
theorem verb_maximal_at_derived :
    isMaximalAtPosition theVerb cpAfterLHM verbDerivedPosition :=
  ⟨verb_at_derived_position, verb_does_not_project_at_derived⟩

/-! ## Part 6: Verifying Head-to-Specifier Movement

We now verify all the conditions for head-to-specifier movement:

1. **Mover was a head**: V projected in VP (it was -maximal there)
2. **Mover is now maximal**: V doesn't project at Spec-CP
3. **Target projects**: C' determines the label of CP
-/

/-- VERIFIED: The verb was a HEAD in the source structure

    In VP, the verb PROJECTS (V selects D, so V's label becomes VP's label).
    Projecting means -maximal, i.e., being a head. -/
theorem verb_was_head_in_target : isHeadIn theVerb cBarBefore := by
  unfold isHeadIn isMinimalIn
  constructor
  · -- V is minimal (it's a leaf) and is a term of C'
    constructor
    · unfold isTermOf; exact Or.inr verb_in_target
    · simp only [theVerb]
  · -- V is NOT maximal in C' (because V projects in VP)
    unfold isMaximalIn
    intro ⟨_, hNoProj⟩
    apply hNoProj
    use vpBefore
    constructor
    · unfold isTermOf; right
      apply contains.trans _ _ tpBefore; exact Or.inr rfl
      apply contains.trans _ _ tBarBefore; exact Or.inr rfl
      apply contains.imm; exact Or.inr rfl
    · -- V projects in VP: V is daughter of VP and label(V) = label(VP)
      unfold projectsIn immediatelyContains sameLabel
      constructor
      · exact Or.inl rfl
      · constructor <;> native_decide

/-- VERIFIED: C' projects in the result (C' is the "head" of CP) -/
theorem cbar_projects_in_result : projectsIn cBarBefore cpAfterLHM := by
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
  target_projects := cbar_projects_in_result

/-- **MAIN THEOREM 1**: The verb is maximal at Spec-CP

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

    The verb moves from VP to Spec-CP, becoming maximal at its derived position.
    By the universal theorem that head-to-specifier movement violates HMC,
    Bulgarian LHM violates HMC. ∎ -/
theorem bulgarian_lhm_violates_hmc_positional :
    violatesHMC_positional bulgarianLHM cpAfterLHM derivedSpecPosition :=
  head_to_spec_violates_hmc_positional bulgarianLHM_h2s_positional

end Minimalism.BulgarianLHM
