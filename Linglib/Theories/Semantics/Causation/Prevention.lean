import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Necessity
import Linglib.Core.Causal.V2.SEM.Counterfactual

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

/-! ### V2 namespace for new code

Legacy `preventSem` above is a structural predicate over CausalDynamics
laws (checks for an inhibitory law explicitly). V2 takes a behavioral
view: setting preventer=false produces effect=true; preventer=true
blocks effect=true. The two definitions are equivalent for direct
prevention models but the V2 form delegates to V2's `developDet` semantics
rather than introspecting law structure. -/

namespace V2

open Core.Causal.V2 (SEM CausalGraph Valuation DecidableValuation)

/-- V2 prevention semantics: preventer-as-`xPrev` blocks effect-from-
    being-`xE`, AND there exists some alternative preventer value that
    would have allowed `effect = xE` to develop. Polymorphic over value
    types; arity-uniform with `makeSem`/`causeSem` so `Causative.V2.toSemantics`
    can dispatch uniformly. Bool models recover the standard
    `false vs true` flip via the `∃ xPrev_alt ≠ xPrev` clause
    (with `xPrev = true`, the only alternative is `false`). -/
noncomputable def preventSem {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (bg : Valuation α)
    (preventer : V) (xPrev : α preventer)
    (effect : V) (xE : α effect) : Prop :=
  ¬ (M.developDet (bg.extend preventer xPrev)).hasValue effect xE ∧
  ∃ xPrev_alt : α preventer, xPrev_alt ≠ xPrev ∧
    (M.developDet (bg.extend preventer xPrev_alt)).hasValue effect xE

noncomputable instance {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (bg : Valuation α) (preventer : V) (xP : α preventer)
    (effect : V) (xE : α effect) :
    Decidable (preventSem M bg preventer xP effect xE) := Classical.dec _

end V2

end Semantics.Causation.Prevention
