import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Necessity

/-!
# Prevention Semantics
@cite{sloman-barbey-hotaling-2009}

`preventSem` formalizes the SEM semantics of "prevent": B := ¬A
(Figure 4, eq. 4a). The preventer blocks an effect that would otherwise occur.

## Definition

Prevention is **structural**: "X prevents Y in background `bg`" means
the dynamics contains an inhibitory law L such that

  (i) L's effect is Y with effectValue = true
  (ii) `(X, false)` is a precondition of L (X must be absent for L to fire)
  (iii) every other precondition of L is met by `bg`

Under this definition, X being present blocks L from firing (Y stays
undetermined), while X being absent allows L to fire (Y becomes true).

This is a **direct-prevention** semantics: chains like `B := ¬A, C := B`
where A indirectly prevents C are NOT captured here. That kind of
indirect prevention requires a richer semantics over chains.

## Why structural, not fixpoint-based?

Earlier versions defined `preventSem` via two `normalDevelopment` calls
under contrasting interventions. That has a hidden correctness issue:
`normalDevelopment` is fuel-bounded and only well-defined for *positive*
(monotone) dynamics — for non-positive cases like prevention, the
function can silently return iteration-100 state on dynamics with no
fixpoint. The structural definition avoids that bog by reading prevention
off the law list directly: decidable, terminating, and semantically
crisp on the inhibitory laws that prevention actually requires.
-/

namespace Semantics.Causation.Prevention

open Core.Causal
open Semantics.Causation.Sufficiency
open Semantics.Causation.Necessity

/-- **Structural prevention semantics** (@cite{sloman-barbey-hotaling-2009} Figure 4).

    "X prevented Y in background `bg`" iff `dyn` contains an inhibitory
    law for `effect` whose firing is blocked by `preventer` being true. -/
def preventSem (dyn : CausalDynamics) (bg : Situation)
    (preventer effect : Variable) : Prop :=
  ∃ law ∈ dyn.laws,
    law.effect = effect ∧
    law.effectValue = true ∧
    (preventer, false) ∈ law.preconditions ∧
    ∀ p ∈ law.preconditions, p.1 ≠ preventer → bg.hasValue p.1 p.2 = true

instance (dyn : CausalDynamics) (bg : Situation) (preventer effect : Variable) :
    Decidable (preventSem dyn bg preventer effect) :=
  List.decidableBEx _ _

/-- **Prevention is impossible in positive-only dynamics.**

    Positive dynamics have no precondition with value `false`, so no law
    can have `(preventer, false)` in its preconditions — hence no
    structural prevention. -/
theorem preventSem_impossible_positive
    (dyn : CausalDynamics) (bg : Situation)
    (x e : Variable) (hPos : isPositiveDynamics dyn = true) :
    ¬ (preventSem dyn bg x e) := by
  intro ⟨law, hLawMem, _hEffect, _hEffVal, hPrecMem, _hOther⟩
  -- positivity says every law's preconditions have .2 = true
  unfold isPositiveDynamics at hPos
  have hLawPos := List.all_eq_true.mp hPos law hLawMem
  rw [Bool.and_eq_true] at hLawPos
  obtain ⟨hPosPrec, _⟩ := hLawPos
  -- (x, false) ∈ preconditions, but each precondition has .2 = true
  have hAllTrue : (x, false).2 = true := List.all_eq_true.mp hPosPrec (x, false) hPrecMem
  -- (x, false).2 = false definitionally; so false = true, contradiction
  exact Bool.false_ne_true hAllTrue

/-- Witness: `preventSem` holds with the canonical prevention dynamics. -/
theorem preventSem_possible_inhibitory :
    ∃ (dyn : CausalDynamics) (bg : Situation) (x e : Variable),
      isPositiveDynamics dyn = false ∧
      preventSem dyn bg x e := by
  refine ⟨CausalDynamics.prevention (mkVar "x") (mkVar "e"),
          Situation.empty, mkVar "x", mkVar "e", ?_, ?_⟩
  · decide
  · refine ⟨CausalLaw.inhibitory (mkVar "x") (mkVar "e"),
            ?_, rfl, rfl, ?_, ?_⟩
    · simp [CausalDynamics.prevention]
    · simp [CausalLaw.inhibitory]
    · -- ∀ p ∈ [(x, false)], p.1 ≠ x → ...; but only p = (x, false), and (x, false).1 = x
      intro p hp hne
      simp [CausalLaw.inhibitory] at hp
      -- hp : p = (mkVar "x", false), so p.1 = mkVar "x", contradicting hne
      subst hp
      exact absurd rfl hne

/-- `preventSem` holds for the canonical prevention model. -/
theorem preventSem_prevention_model :
    let x := mkVar "x"; let e := mkVar "e"
    preventSem (CausalDynamics.prevention x e) Situation.empty x e := by
  refine ⟨CausalLaw.inhibitory (mkVar "x") (mkVar "e"),
          ?_, rfl, rfl, ?_, ?_⟩
  · simp [CausalDynamics.prevention]
  · simp [CausalLaw.inhibitory]
  · intro p hp hne
    simp [CausalLaw.inhibitory] at hp
    subst hp
    exact absurd rfl hne

/-- The prevention model is not positive (it has an inhibitory law). -/
theorem prevention_not_positive :
    let x := mkVar "x"; let e := mkVar "e"
    isPositiveDynamics (CausalDynamics.prevention x e) = false := by
  decide

/-- Prevention with accessory: B := ¬A ∧ X.

    @cite{sloman-barbey-hotaling-2009} eq. 4b: the effect requires both
    the preventer's absence AND an accessory cause. -/
theorem preventSem_with_accessory :
    let x := mkVar "x"; let acc := mkVar "acc"; let e := mkVar "e"
    preventSem (CausalDynamics.preventionWithAccessory x acc e)
      (Situation.empty.extend acc true) x e := by
  refine ⟨{ preconditions := [(mkVar "x", false), (mkVar "acc", true)],
            effect := mkVar "e", effectValue := true },
          ?_, rfl, rfl, ?_, ?_⟩
  · simp [CausalDynamics.preventionWithAccessory]
  · simp
  · intro p hp hne
    simp at hp
    rcases hp with hpx | hpacc
    · -- p = (x, false); contradicts p.1 ≠ x
      subst hpx
      exact absurd rfl hne
    · -- p = (acc, true); bg has acc=true
      subst hpacc
      simp [Situation.hasValue, Situation.extend]

end Semantics.Causation.Prevention
