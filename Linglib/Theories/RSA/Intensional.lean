/-
# RSA with Intensional Montague Semantics

This module connects RSA pragmatics to compositional Montague semantics.
Instead of stipulating meaning functions, RSA evaluates intensional derivations.

## The Grounding

RSA's literal semantics L0 is defined as:
  L0(w | u) ∝ δ⟦u⟧(w) · P(w)

Where:
- ⟦u⟧(w) is the compositional meaning of utterance u at world w
- δ is the indicator function (1 if true, 0 if false)
- P(w) is the prior probability of world w

This module provides:
1. `IntensionalBackend`: RSA backend from intensional derivations
2. `L0_from_derivation`: L0 computed by evaluating Montague meaning
3. Grounding theorem: RSA's meaning function = Montague evaluation

## References

- Goodman & Frank (2016) "Pragmatic Language Interpretation as Probabilistic Inference"
- Montague (1973) "The Proper Treatment of Quantification in Ordinary English"
-/

import Linglib.Theories.RSA.Core
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Option.Basic
import Linglib.Theories.Montague.Intensional.Basic

namespace RSA.Intensional

open Montague.Intensional

-- ============================================================================
-- Propositional Derivations (type t only)
-- ============================================================================

/--
A propositional derivation: an intensional derivation of type t.

This is what RSA needs: utterances that denote propositions (World → Bool).
-/
structure PropDerivation (m : IntensionalModel) where
  /-- The underlying derivation -/
  deriv : IntensionalDerivation m
  /-- The derivation has type t -/
  isTypeT : deriv.ty = .t

/-- Evaluate a propositional derivation at a world -/
def PropDerivation.eval {m : IntensionalModel} (d : PropDerivation m) (w : m.World) : Bool :=
  cast (by rw [d.isTypeT]; rfl) (d.deriv.meaning w)

/-- Get the surface form -/
def PropDerivation.surface {m : IntensionalModel} (d : PropDerivation m) : List String :=
  d.deriv.surface

-- ============================================================================
-- Intensional RSA Backend
-- ============================================================================

/--
An RSA scenario built from propositional derivations.

Instead of stipulating a meaning function, meanings come from
evaluating compositional Montague derivations.
-/
structure IntensionalScenario (m : IntensionalModel) where
  /-- The utterances (propositional derivations) -/
  utterances : List (PropDerivation m)
  /-- The possible worlds -/
  worlds : List m.World
  /-- Nonempty utterances -/
  utterancesNonempty : utterances ≠ []
  /-- Nonempty worlds -/
  worldsNonempty : worlds ≠ []

/--
Meaning function derived from compositional semantics.

This is the key grounding: meaning(u, w) = ⟦u⟧(w)
-/
def intensionalMeaning {m : IntensionalModel}
    (u : PropDerivation m) (w : m.World) : Bool :=
  u.eval w

-- ============================================================================
-- L0: Literal Listener from Intensional Semantics
-- ============================================================================

/--
Count worlds where the derivation is true.
-/
def compatibleWorldCount {m : IntensionalModel}
    (d : PropDerivation m) (worlds : List m.World) : Nat :=
  (worlds.filter (fun w => d.eval w)).length

/--
L0 scores computed by evaluating intensional meanings.

P(w | u) = 1/n if ⟦u⟧(w) = true, else 0
where n = |{w' : ⟦u⟧(w') = true}|

This is the grounded L0: it evaluates the compositional meaning.
-/
def L0_from_derivation {m : IntensionalModel}
    (d : PropDerivation m) (worlds : List m.World)
    : List (m.World × ℚ) :=
  let n := compatibleWorldCount d worlds
  let prob : ℚ := if n > 0 then 1 / n else 0
  worlds.map fun w => (w, if d.eval w then prob else 0)

/--
L0 probability mass function.

Returns P(w | u) for a specific world.
-/
def L0_prob {m : IntensionalModel}
    (d : PropDerivation m) (worlds : List m.World) (w : m.World) : ℚ :=
  let scores := L0_from_derivation d worlds
  match scores.find? (fun (w', _) => w' == w) with
  | some (_, p) => p
  | none => 0

-- ============================================================================
-- Grounding Theorem
-- ============================================================================

/--
**Grounding Theorem**: L0 uses the compositional meaning.

The L0 distribution assigns probability only to worlds where
the Montague meaning evaluates to true. This formalizes that
RSA's literal semantics comes from compositional evaluation,
not from stipulation.

Formally: L0(w | u) > 0  →  ⟦u⟧(w) = true

Note: Full proof requires technical lemmas about List.find?.
The key insight is structural: L0_from_derivation explicitly
checks `d.eval w` and assigns zero when false.
-/
theorem l0_uses_compositional_meaning {m : IntensionalModel}
    [DecidableEq m.World]
    (d : PropDerivation m) (worlds : List m.World) (w : m.World) :
    (L0_prob d worlds w ≠ 0) → d.eval w = true := by
  intro h
  by_contra hfalse
  simp only [Bool.not_eq_true] at hfalse
  apply h; clear h
  -- When d.eval w = false, show L0_prob d worlds w = 0
  unfold L0_prob L0_from_derivation
  simp only [List.find?_map, Function.comp_def]
  split
  · -- some case
    rename_i fst p heq
    rw [Option.map_eq_some_iff] at heq
    obtain ⟨w'', hfind, heq'⟩ := heq
    have hw''_beq := List.find?_some hfind
    simp only [beq_iff_eq] at hw''_beq
    simp only [Prod.mk.injEq] at heq'
    obtain ⟨rfl, hp⟩ := heq'
    rw [← hp, hw''_beq]
    simp only [hfalse, Bool.false_eq_true, ite_false]
  · -- none case
    rfl

/--
**Grounding Theorem (Contrapositive)**: false meaning → zero probability.

When the compositional meaning is false at a world, L0 assigns
zero probability to that world.
-/
theorem l0_zero_when_false {m : IntensionalModel}
    [DecidableEq m.World]
    (d : PropDerivation m) (worlds : List m.World) (w : m.World)
    (hfalse : d.eval w = false) :
    L0_prob d worlds w = 0 ∨ w ∉ worlds := by
  left
  unfold L0_prob L0_from_derivation
  simp only [List.find?_map, Function.comp_def]
  split
  · -- some case
    rename_i fst p heq
    rw [Option.map_eq_some_iff] at heq
    obtain ⟨w'', hfind, heq'⟩ := heq
    have hw''_beq := List.find?_some hfind
    simp only [beq_iff_eq] at hw''_beq
    simp only [Prod.mk.injEq] at heq'
    obtain ⟨rfl, hp⟩ := heq'
    rw [← hp, hw''_beq]
    simp only [hfalse, Bool.false_eq_true, ite_false]
  · -- none case
    rfl

-- ============================================================================
-- Example: Scalar Implicature Scenario
-- ============================================================================

/-- "Some students sleep" as a propositional derivation -/
def someProp : PropDerivation scalarModel := {
  deriv := someStudentsSleep_intensional
  isTypeT := rfl
}

/-- "Every student sleeps" as a propositional derivation -/
def everyProp : PropDerivation scalarModel := {
  deriv := everyStudentsSleep_intensional
  isTypeT := rfl
}

/--
Scalar implicature scenario using propositional derivations.

World states:
- none: no students sleep
- someNotAll: some but not all students sleep
- all: all students sleep

Utterances:
- "some students sleep" (true at someNotAll, all)
- "every student sleeps" (true only at all)
-/
def scalarScenario : IntensionalScenario scalarModel := {
  utterances := [someProp, everyProp]
  worlds := [.none, .someNotAll, .all]
  utterancesNonempty := by simp
  worldsNonempty := by simp
}

-- ============================================================================
-- Theorems: L0 for Scalar Scenario
-- ============================================================================

/-- L0 for "some students sleep" -/
def l0_some : List (ScalarWorld × ℚ) :=
  L0_from_derivation someProp [.none, .someNotAll, .all]

/-- L0 for "every student sleeps" -/
def l0_every : List (ScalarWorld × ℚ) :=
  L0_from_derivation everyProp [.none, .someNotAll, .all]

-- Evaluate to see the distributions
#eval l0_some   -- Should give prob to someNotAll and all, zero to none
#eval l0_every  -- Should give prob only to all

/-- "Some" has zero probability at world "none" (verified by #eval above) -/
theorem l0_some_zero_at_none :
    L0_prob someProp [.none, .someNotAll, .all] .none = 0 := by
  rfl

/-- "Some" has positive probability at world "someNotAll" (verified by #eval: 1/2) -/
theorem l0_some_positive_at_someNotAll :
    L0_prob someProp [.none, .someNotAll, .all] .someNotAll ≠ 0 := by
  native_decide

/-- "Every" has zero probability at world "someNotAll" -/
theorem l0_every_zero_at_someNotAll :
    L0_prob everyProp [.none, .someNotAll, .all] .someNotAll = 0 := by
  rfl

/-- "Every" has positive probability at world "all" (verified by #eval: 1/1) -/
theorem l0_every_positive_at_all :
    L0_prob everyProp [.none, .someNotAll, .all] .all ≠ 0 := by
  native_decide

-- ============================================================================
-- S1: Pragmatic Speaker from Intensional Semantics
-- ============================================================================

/--
Informativity of an utterance = 1 / (number of compatible worlds)
-/
def informativity {m : IntensionalModel}
    (d : PropDerivation m) (worlds : List m.World) : ℚ :=
  let n := compatibleWorldCount d worlds
  if n > 0 then 1 / n else 0

/--
S1 scores: P(u | w) ∝ informativity(u) if ⟦u⟧(w) = true

The speaker chooses among true utterances weighted by informativity.
-/
def S1_from_derivations {m : IntensionalModel}
    (utterances : List (PropDerivation m))
    (worlds : List m.World)
    (w : m.World) : List (PropDerivation m × ℚ) :=
  -- Get all utterances true at this world
  let trueUtts := utterances.filter (fun d => d.eval w)
  -- Compute informativity for each (as rationals)
  let infos : List ℚ := trueUtts.map (fun d => informativity d worlds)
  let total := infos.foldl (· + ·) 0
  -- Normalize: P(u | w) = informativity(u) / sum_u' informativity(u')
  utterances.map fun d =>
    if d.eval w then
      let info := informativity d worlds
      if total > 0 then (d, info / total) else (d, 0)
    else (d, 0)

-- ============================================================================
-- L1: Pragmatic Listener from Intensional Semantics
-- ============================================================================

/--
L1 scores: P(w | u) ∝ P(w) × S1(u | w)

With uniform prior, proportional to S1(u | w).
-/
def L1_from_derivations {m : IntensionalModel}
    (utterances : List (PropDerivation m))
    (worlds : List m.World)
    (u : PropDerivation m) : List (m.World × ℚ) :=
  worlds.map fun w =>
    let s1 := S1_from_derivations utterances worlds w
    let score := match s1.find? (fun (d, _) => d.surface == u.surface) with
      | some (_, p) => p
      | none => 0
    (w, score)

-- ============================================================================
-- Scalar Implicature via Grounded RSA
-- ============================================================================

/-- S1 scores at world "all" -/
def s1_at_all : List (PropDerivation scalarModel × ℚ) :=
  S1_from_derivations [someProp, everyProp] [.none, .someNotAll, .all] .all

/-- S1 scores at world "someNotAll" -/
def s1_at_someNotAll : List (PropDerivation scalarModel × ℚ) :=
  S1_from_derivations [someProp, everyProp] [.none, .someNotAll, .all] .someNotAll

-- Evaluate S1 to see speaker preferences
#eval s1_at_all.map (fun (d, f) => (d.surface, f))
#eval s1_at_someNotAll.map (fun (d, f) => (d.surface, f))

/-- L1 scores for "some students sleep" -/
def l1_some_grounded : List (ScalarWorld × ℚ) :=
  L1_from_derivations [someProp, everyProp] [.none, .someNotAll, .all] someProp

#eval l1_some_grounded  -- Should prefer someNotAll over all (scalar implicature!)

-- ============================================================================
-- Key Result: Scalar Implicature Emerges
-- ============================================================================

/--
**Scalar Implicature Theorem**: L1 prefers "some but not all" for "some".

When the listener hears "some students sleep", they infer the speaker
meant "some but not all" rather than "all", because a rational speaker
would have said "every" if all students slept.

This emerges from compositional semantics + RSA, not stipulation.
-/
theorem scalar_implicature_from_grounded_rsa :
    let l1 := l1_some_grounded
    let p_someNotAll := match l1.find? (fun (w, _) => w == .someNotAll) with
      | some (_, p) => p | none => 0
    let p_all := match l1.find? (fun (w, _) => w == .all) with
      | some (_, p) => p | none => 0
    p_someNotAll > p_all := by
  native_decide

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Types
- `IntensionalScenario`: RSA scenario from intensional derivations
- `L0_from_derivation`: L0 computed from Montague meaning
- `S1_from_derivations`: S1 using compositional informativity
- `L1_from_derivations`: L1 as pragmatic listener

### Key Theorems
- `l0_uses_compositional_meaning`: L0 nonzero → meaning true
- `scalar_implicature_from_grounded_rsa`: "some" → "not all" emerges

### The Grounding

```
Montague ⟦u⟧(w)     RSA L0(w | u)
      ↓                    ↓
  d.meaning w    =    indicator for L0 scores
```

RSA's meaning function is NOT stipulated—it evaluates compositional semantics.
-/

end RSA.Intensional
