module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Linglib.Semantics.Causation.CausalModel.Development

/-!
# Causal sufficiency and causal necessity

This file defines the two relations of causal dependence that Nadathur and Lauer draw on for the
meanings of periphrastic causatives, over the strict development of an observation
(`CausalModel.CausallyEntails`). A fact is causally sufficient for another relative to a
background when the background does not settle the effect but, with the cause added, does
(`CausalModel.CausallySufficient`, Nadathur and Lauer's Definition 23). A fact is causally
necessary for another when the background settles neither, some settlement of the exogenous
variables together with the cause settles the effect, and every settlement of the exogenous
variables that settles the effect also settles the cause (`CausalModel.CausallyNecessary`,
Nadathur's Definition 10b).

## Main definitions

* `CausalModel.CausallySufficient`: Nadathur and Lauer's causal sufficiency
* `CausalModel.IsExogenousSettlement`: an extension of an observation at exogenous variables
* `CausalModel.CausallyNecessary`: Nadathur's causal necessity

## Main results

* `CausalModel.CausallyEntails.of_isExogenousSettlement`: settling exogenous variables settles
  no less
* `CausalModel.isExogenousSettlement_update`, `CausalModel.IsExogenousSettlement.trans`

## Implementation notes

Necessity quantifies over settlements of the exogenous variables, the variables with no parents that
the background leaves open, not over every consistent extension of the background: on the literal
quantification, settling an inner variable can reach the effect around the cause and falsify the
verdicts of Nadathur's worked examples, which consider only background settlements. In a finite
model each relation is decided through the computed strict development
(`CausalModel.causallyEntails_iff_develop`), the quantified settlements ranging over the finitely
many partial assignments.

## References

* [nadathur-lauer-2020]
* [nadathur-2023-implicatives]
-/

@[expose] public section

namespace CausalModel

variable {U V : Type*} {α : V → Type*} (M : CausalModel U V α) [M.IsAcyclic] [DecidableEq V]

/-- `M.CausallySufficient s c x e y` says that `c = x` is causally sufficient for `e = y` relative
to the background `s`: the background does not settle the effect, and the background together with
the cause does. -/
def CausallySufficient (s : ∀ v, Flat (α v)) (c : V) (x : α c) (e : V) (y : α e) : Prop :=
  ¬ M.CausallyEntails s e y ∧ M.CausallyEntails (Function.update s c ↑x) e y

/-- `s'` settles the observation `s` further at exogenous variables only, those with no parents
that the strict development of `s` leaves open. -/
def IsExogenousSettlement (s s' : ∀ v, Flat (α v)) : Prop :=
  s ≤ s' ∧ ∀ v, s v = ⊥ → s' v ≠ ⊥ → (∀ w, ¬ M.graph.Adj w v) ∧ ∀ x, ¬ M.CausallyEntails s v x

/-- `M.CausallyNecessary s c x e y` says that `c = x` is causally necessary for `e = y` relative to
the background `s`. The background settles neither fact; some exogenous settlement of the
background with the cause added, leaving the effect open, settles the effect; and every exogenous
settlement of the background leaving the effect open that settles the effect settles the cause. -/
def CausallyNecessary (s : ∀ v, Flat (α v)) (c : V) (x : α c) (e : V) (y : α e) : Prop :=
  (¬ M.CausallyEntails s c x ∧ ¬ M.CausallyEntails s e y) ∧
  (∃ s', M.IsExogenousSettlement (Function.update s c ↑x) s' ∧ s' e = ⊥ ∧
    M.CausallyEntails s' e y) ∧
  ∀ s', M.IsExogenousSettlement s s' → s' e = ⊥ → M.CausallyEntails s' e y →
    M.CausallyEntails s' c x

variable {M}

omit [DecidableEq V] in
/-- Settling exogenous variables settles no less. What the strict development of an observation
settles, that of any exogenous settlement of it settles too. -/
theorem CausallyEntails.of_isExogenousSettlement {s s' : ∀ v, Flat (α v)}
    (hs : M.IsExogenousSettlement s s') {v : V} {x : α v} (h : M.CausallyEntails s v x) :
    M.CausallyEntails s' v x := by
  induction v using ‹M.IsAcyclic›.induction with
  | _ v ih =>
    rcases causallyEntails_iff.1 h with hv | ⟨hv, hpar, heq⟩
    · exact causallyEntails_iff.2 (.inl (Flat.coe_le_iff.1 (hv ▸ hs.1 v)))
    · have hv' : s' v = ⊥ := by
        by_contra hne
        exact (hs.2 v hv hne).2 x h
      refine causallyEntails_iff.2 (.inr ⟨hv', fun w hw ↦ ?_, fun u y hy ↦ ?_⟩)
      · obtain ⟨z, hz⟩ := hpar w hw
        exact ⟨z, ih w hw hz⟩
      · exact heq u y fun w hw z hz ↦ hy w hw z (ih w hw hz)

/-- Settling an open exogenous variable is an exogenous settlement. -/
theorem isExogenousSettlement_update {s : ∀ v, Flat (α v)} {p : V}
    (hroot : ∀ w, ¬ M.graph.Adj w p) (hopen : ∀ x, ¬ M.CausallyEntails s p x) (x : α p) :
    M.IsExogenousSettlement s (Function.update s p ↑x) := by
  have hsp : s p = ⊥ := by
    by_contra h
    obtain ⟨y, hy⟩ := Flat.ne_bot_iff_exists.1 h
    exact hopen y (causallyEntails_iff.2 (.inl hy))
  refine ⟨fun v ↦ ?_, fun v hv hne ↦ ?_⟩
  · by_cases hvp : v = p
    · subst hvp; rw [hsp]; exact bot_le
    · rw [Function.update_of_ne hvp]
  · by_cases hvp : v = p
    · subst hvp; exact ⟨hroot, hopen⟩
    · rw [Function.update_of_ne hvp] at hne; exact absurd hv hne

omit [DecidableEq V] in
/-- Every observation is an exogenous settlement of itself. -/
theorem IsExogenousSettlement.refl (s : ∀ v, Flat (α v)) : M.IsExogenousSettlement s s :=
  ⟨le_rfl, fun _ hv hne ↦ absurd hv hne⟩

omit [DecidableEq V] in
/-- An exogenous settlement leaves open every variable with a parent that the observation leaves
open. -/
theorem IsExogenousSettlement.eq_bot {s s' : ∀ v, Flat (α v)} (h : M.IsExogenousSettlement s s')
    {v : V} (hv : s v = ⊥) (hpar : ∃ w, M.graph.Adj w v) : s' v = ⊥ := by
  by_contra hne
  obtain ⟨w, hw⟩ := hpar
  exact (h.2 v hv hne).1 w hw

omit [DecidableEq V] in
/-- Exogenous settlements compose. -/
theorem IsExogenousSettlement.trans {s s' s'' : ∀ v, Flat (α v)}
    (h₁ : M.IsExogenousSettlement s s') (h₂ : M.IsExogenousSettlement s' s'') :
    M.IsExogenousSettlement s s'' := by
  refine ⟨h₁.1.trans h₂.1, fun v hv hne ↦ ?_⟩
  by_cases hv' : s' v = ⊥
  · exact ⟨(h₂.2 v hv' hne).1, fun x hx ↦ (h₂.2 v hv' hne).2 x (hx.of_isExogenousSettlement h₁)⟩
  · exact h₁.2 v hv hv'

section Decidable

variable [Fintype U] [Inhabited U] [∀ v, Inhabited (α v)] [∀ v, DecidableEq (α v)] [Fintype V]
  [DecidableRel M.graph.Adj]

instance (s : ∀ v, Flat (α v)) (c : V) (x : α c) (e : V) (y : α e) :
    Decidable (M.CausallySufficient s c x e y) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable [∀ v, Fintype (α v)]

instance (s s' : ∀ v, Flat (α v)) : Decidable (M.IsExogenousSettlement s s') :=
  haveI : ∀ v, Decidable (s v = ⊥ → s' v ≠ ⊥ →
      (∀ w, ¬ M.graph.Adj w v) ∧ ∀ x, ¬ M.CausallyEntails s v x) := fun _ ↦ inferInstance
  inferInstanceAs (Decidable (_ ∧ _))

/-- Partial assignments over finitely many variables of finite types are finitely many. Not an
instance: a `Fintype` instance on `Flat` would change how `decide` evaluates flat-valued
functions, so necessity installs this one locally. -/
@[reducible] def fintypePartialAssignment : Fintype (∀ v, Flat (α v)) :=
  inferInstanceAs (Fintype (∀ v, Option (α v)))

instance (s : ∀ v, Flat (α v)) (c : V) (x : α c) (e : V) (y : α e) :
    Decidable (M.CausallyNecessary s c x e y) :=
  letI := fintypePartialAssignment (α := α)
  haveI : DecidablePred fun s' ↦ M.IsExogenousSettlement (Function.update s c ↑x) s' ∧
      s' e = ⊥ ∧ M.CausallyEntails s' e y := fun _ ↦ inferInstance
  haveI : DecidablePred fun s' ↦ M.IsExogenousSettlement s s' → s' e = ⊥ →
      M.CausallyEntails s' e y → M.CausallyEntails s' c x := fun _ ↦ inferInstance
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end Decidable

end CausalModel
