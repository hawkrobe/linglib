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
where A indirectly prevents C are NOT captured here.

After the @cite{schulz-2011}/@cite{fitting-1985} unification, negative
preconditions like `(X, false)` are first-class in `normalDevelopment`
itself (no positivity restriction). The structural definition below
remains useful as a discriminator for "this is a prevention law" — it
reads directly off the law structure rather than running the dynamics.
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
    ∀ p ∈ law.preconditions, p.1 ≠ preventer → bg.hasValue p.1 p.2

instance (dyn : CausalDynamics) (bg : Situation) (preventer effect : Variable) :
    Decidable (preventSem dyn bg preventer effect) :=
  List.decidableBEx _ _

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
    · subst hpx; exact absurd rfl hne
    · subst hpacc
      show (Situation.empty.extend (mkVar "acc") true).hasValue (mkVar "acc") true
      unfold Situation.hasValue Situation.extend; simp

end Semantics.Causation.Prevention
