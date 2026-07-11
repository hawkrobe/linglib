import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Filter

/-!
# Asymmetric entailment over a finite world set

A polymorphic primitive: `ψ` asymmetrically entails `φ` over a finite
set of worlds when every ψ-world is a φ-world and at least one φ-world
is not a ψ-world. Equivalently, `worlds.filter ψ ⊂ worlds.filter φ`.

This is the shared core of "primary-implicature triggering" (Sauerland
2004 over `EpistemicState.possible`) and the asymmetric-entailment
fragment of various exhaustification operators. The intent is that any
study or theory file needing asymmetric entailment over a finite domain
of world predicates uses this rather than reinventing it.

## Why a polymorphic version

`Semantics/Entailment/Basic.lean` defines `entails` over a
concrete `World` enum (w0–w3) for testbed purposes. That file is not the
right home for a polymorphic primitive. This file is.

## What this does NOT subsume

- **`Franke2011.strongestAt`** (`Studies/Franke2011/ScalarGames.lean`) —
  expresses "m is the strongest true message at s" as a unary predicate
  on messages, not the binary asymmetric-entailment relation; its proofs
  are built around the unary form.

- **`Magri2014.innerExcludable`** (`Studies/Magri2014.lean`) —
  combines (a) a hand-wired `entails : Role → Role → Bool` on a
  three-element role enum with (b) a Horn-mateness filter. The `entails`
  is not derivable as `asymStrongerOn` over a world set because Magri's
  `Scenario` type isn't `Fintype` (arbitrary `total : Nat`). Lifting
  Magri to use this primitive would require either a Fintype-restricted
  Scenario or a separate non-Fintype variant.

Both are noted as future consolidation targets but require deeper
architectural work than a literal find-and-replace.
-/

namespace Entailment

variable {W : Type*}

/-- `ψ` asymmetrically entails `φ` over `worlds`: every ψ-world in
`worlds` is a φ-world, and at least one φ-world in `worlds` is not a
ψ-world.

Defined in explicit forall-exists form (matching mathlib's `MonotoneOn`
idiom). Equivalent to `worlds.filter ψ ⊂ worlds.filter φ` — see
`asymStrongerOn_iff_filter_ssubset`. -/
def asymStrongerOn (worlds : Finset W) (ψ φ : W → Prop)
    [DecidablePred ψ] [DecidablePred φ] : Prop :=
  (∀ w ∈ worlds, ψ w → φ w) ∧ (∃ w ∈ worlds, φ w ∧ ¬ ψ w)

instance (worlds : Finset W) (ψ φ : W → Prop)
    [DecidablePred ψ] [DecidablePred φ] :
    Decidable (asymStrongerOn worlds ψ φ) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Bridge to the mathlib filter form: `asymStrongerOn` is exactly
strict subset of the filtered subsets. -/
theorem asymStrongerOn_iff_filter_ssubset (worlds : Finset W) (ψ φ : W → Prop)
    [DecidablePred ψ] [DecidablePred φ] :
    asymStrongerOn worlds ψ φ ↔ worlds.filter ψ ⊂ worlds.filter φ := by
  constructor
  · rintro ⟨hfwd, w, hw, hφ, hnotψ⟩
    refine ⟨fun x hx => ?_, fun hsub => ?_⟩
    · simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hfwd x hx.1 hx.2⟩
    · exact hnotψ ((Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hw, hφ⟩))).2)
  · intro hss
    have hsub : worlds.filter ψ ⊆ worlds.filter φ := hss.1
    have hne : ∃ w ∈ worlds.filter φ, w ∉ worlds.filter ψ := by
      by_contra hall
      push Not at hall
      exact hss.2 (fun w hw => by
        by_contra hnotmem
        exact hnotmem (hall w hw))
    refine ⟨fun w hw hψ => ?_, ?_⟩
    · exact (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hw, hψ⟩))).2
    · obtain ⟨w, hw, hnotψ⟩ := hne
      simp only [Finset.mem_filter] at hw hnotψ
      exact ⟨w, hw.1, hw.2, fun hψw => hnotψ ⟨hw.1, hψw⟩⟩

/-- Asymmetric entailment is irreflexive. -/
theorem not_asymStrongerOn_self (worlds : Finset W) (φ : W → Prop)
    [DecidablePred φ] :
    ¬ asymStrongerOn worlds φ φ := by
  rintro ⟨_, _, _, hφ, hnotφ⟩
  exact hnotφ hφ

end Entailment
