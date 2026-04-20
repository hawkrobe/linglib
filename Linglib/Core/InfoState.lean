import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.SetNotation

/-!
# Information States — `Set W` propositional algebra
@cite{ciardelli-groenendijk-roelofsen-2018}

`InfoState W := Set W`. Sets-of-worlds are the natural mathlib type for
the inquisitive-semantic notion of an information state. All the
standard operations are reused from mathlib (`∅`, `Set.univ`, `∩`, `∪`,
`⊆`, `Set.Nonempty`, `⊊`); the only file-local additions are short
aliases (`absurdState`, `trivialState`, `supports`, `propEntails`) so
that the rest of the dynamic-semantics surface still reads naturally.

`Set W` is definitionally `W → Prop`, so `w ∈ σ` and `σ w` are
interchangeable. Decidability of these predicates is *not* an axiom of
this layer — consumers that compute over the world list (Roberts QUD,
inquisitive Hamblin alternatives, dialogue scoreboards) ask for
`[DecidablePred σ]` at the call site as needed.
-/

namespace Discourse

/-- An information state: the set of worlds compatible with current
    information. The empty state represents inconsistent information. -/
abbrev InfoState (W : Type*) := Set W

/-- The absurd/inconsistent info state: no worlds compatible. -/
abbrev absurdState {W : Type*} : InfoState W := (∅ : Set W)

/-- The trivial info state: total ignorance — every world is compatible. -/
abbrev trivialState {W : Type*} : InfoState W := Set.univ

/-- σ supports proposition `p` iff every world in σ makes `p` true.
    The fundamental relation in inquisitive semantics: σ ⊨ p. The empty
    state supports every proposition (ex falso quodlibet). -/
abbrev supports {W : Type*} (σ : InfoState W) (p : W → Prop) : Prop :=
  ∀ w ∈ σ, p w

/-- Propositional entailment between two `Set W` propositions. -/
abbrev propEntails {W : Type*} (p q : Set W) : Prop := p ⊆ q

/-- Reflexivity of propositional entailment. -/
theorem propEntails_refl {W : Type*} (p : Set W) : propEntails p p :=
  fun _ h => h

/-- Transitivity of propositional entailment. -/
theorem propEntails_trans {W : Type*} {p q r : Set W}
    (hpq : propEntails p q) (hqr : propEntails q r) : propEntails p r :=
  fun w hp => hqr (hpq hp)

/-- The trivial state supports any pointwise-true proposition. -/
theorem supports_trivialState {W : Type*} (p : W → Prop)
    (h : ∀ w, p w) : supports (trivialState : InfoState W) p :=
  fun w _ => h w

/-- The absurd state supports every proposition. -/
theorem supports_absurdState {W : Type*} (p : W → Prop) :
    supports (absurdState : InfoState W) p := by
  intro w hw; exact (Set.notMem_empty w hw).elim

end Discourse
