/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Computability.Language
import Mathlib.Logic.Function.Basic

/-!
# Membership invariance for languages

Extensions to mathlib's `Language` API. `Language.InvariantUnder f L` says membership
in `L` **factors through `f`** — any two words with equal `f`-image are L-equivalent,
i.e. `L` is saturated under `Setoid.ker f`. It is `Function.FactorsThrough (· ∈ L) f`,
so it inherits mathlib's `FactorsThrough` API (notably `Function.factorsThrough_iff`,
whose witness `∃ e, (· ∈ L) = e ∘ f` is the "permitted-image" predicate).

Many subregular language classes are exactly this for a fixed projection `f`: the
definite family factors membership through an edge substring, the strictly-piecewise
family through a subsequence test. Stating the notion once gives those classes a
uniform foundation and the shared closure lemmas (`InvariantUnder.compl`) for free.
-/

namespace Language

variable {α : Type*} {β : Type*}

/-- `L` is **invariant under `f`**: membership factors through `f` (the saturation
of `L` under `Setoid.ker f`). -/
def InvariantUnder (f : List α → β) (L : Language α) : Prop :=
  Function.FactorsThrough (· ∈ L) f

/-- Invariance in `Iff`-form: equal `f`-image gives L-equivalence (the `Prop`-equality
that `FactorsThrough` carries, transported across `propext`). -/
lemma invariantUnder_iff {f : List α → β} {L : Language α} :
    L.InvariantUnder f ↔ ∀ ⦃a b⦄, f a = f b → (a ∈ L ↔ b ∈ L) :=
  ⟨fun h _ _ hab => iff_of_eq (h hab), fun h _ _ hab => propext (h hab)⟩

/-- Introduction form: build invariance from the pointwise `Iff`. -/
lemma InvariantUnder.mk {f : List α → β} {L : Language α}
    (h : ∀ ⦃a b⦄, f a = f b → (a ∈ L ↔ b ∈ L)) : L.InvariantUnder f :=
  invariantUnder_iff.mpr h

/-- Elimination form: equal `f`-image gives L-equivalence. -/
lemma InvariantUnder.iff {f : List α → β} {L : Language α} (h : L.InvariantUnder f)
    {a b : List α} (hab : f a = f b) : a ∈ L ↔ b ∈ L :=
  invariantUnder_iff.mp h hab

/-- Invariance is closed under complement: `L` and `Lᶜ` saturate the same kernel. -/
lemma InvariantUnder.compl {f : List α → β} {L : Language α}
    (h : L.InvariantUnder f) : Lᶜ.InvariantUnder f :=
  invariantUnder_iff.mpr fun _ _ hab => not_congr (h.iff hab)

end Language
