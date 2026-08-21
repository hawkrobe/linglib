import Linglib.Semantics.Attitudes.Preference

/-!
# Effective-preference desire semantics

`a wants φ` holds at `w` iff some maximal preference of `a`'s preferential background
`P a w` stands in a designated relation to `φ` — [condoravdi-lauer-2016]'s analysis,
where the background plays the role of a Kratzerian conversational background
([condoravdi-lauer-2011], [condoravdi-lauer-2012], [lauer-2013], [lauer-condoravdi-2014]).
The relation fixes the reading: identity is the canonical exact-match reading (`Want`);
reverse inclusion gives a preference satisfied *if* `φ` holds (`WantSufficient`, their
success-oriented reading), which is downward entailing in `φ`; inclusion gives a
preference satisfied *only if* `φ` holds (`WantNecessary`, their Quine–Hintikka reading),
which is upward entailing. Blocking of simultaneous `want φ` and `want ¬φ` over a
consistent background is `PreferenceStructure.maxElts_pair_belief_compatible`.
-/

namespace Desire.Preferential

variable {Agent W : Type*} (P : Agent → W → PreferenceStructure W) (a : Agent) (φ : Set W)
  (w : W)

/-- Exact-match want: `φ` itself is a maximal preference, `φ ∈ max[P(a, w)]`. -/
def Want : Prop := φ ∈ (P a w).maxElts

/-- Some maximal preference is entailed by `φ`: a preference satisfied if `φ` holds. -/
def WantSufficient : Prop := ∃ p ∈ (P a w).maxElts, φ ⊆ p

/-- Some maximal preference entails `φ`: a preference satisfied only if `φ` holds. -/
def WantNecessary : Prop := ∃ p ∈ (P a w).maxElts, p ⊆ φ

variable {P a φ w}

theorem Want.wantSufficient (h : Want P a φ w) : WantSufficient P a φ w := ⟨φ, h, subset_rfl⟩

theorem Want.wantNecessary (h : Want P a φ w) : WantNecessary P a φ w := ⟨φ, h, subset_rfl⟩

theorem WantSufficient.anti {ψ : Set W} (hφψ : φ ⊆ ψ) (h : WantSufficient P a ψ w) :
    WantSufficient P a φ w :=
  let ⟨p, hp, hψp⟩ := h; ⟨p, hp, hφψ.trans hψp⟩

theorem WantNecessary.mono {ψ : Set W} (hφψ : φ ⊆ ψ) (h : WantNecessary P a φ w) :
    WantNecessary P a ψ w :=
  let ⟨p, hp, hpφ⟩ := h; ⟨p, hp, hpφ.trans hφψ⟩

end Desire.Preferential
