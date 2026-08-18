import Linglib.Core.Order.PreferenceStructure
import Linglib.Core.Order.PreferenceStructure.EffectivePreference
import Linglib.Core.Order.PreferenceStructure.MaxInducedOrdering

/-!
# The effective-preference theory of *want*

Condoravdi & Lauer's analysis of *want*, developed across
[condoravdi-lauer-2011], [condoravdi-lauer-2012], [lauer-2013],
[lauer-condoravdi-2014], and [condoravdi-lauer-2016]: the verb is
parameterized by a *preferential background*
`P : Agent → W → PreferenceStructure W` — analogous to Kratzer's modal
base/ordering source — whose distinguished value is the agent's
effective preference function `EP : ∀ a w, EffectivePreference W (B a w)`
(`Core.Order.EffectivePreference`).

A want-report holds when some maximal preference in the background
stands in a designated relation to the complement, and the relation is
the locus of variation: [condoravdi-lauer-2016] eq. 71 considers
equality (`wantExactMatch`, the canonical reading, their eq. 69),
reverse inclusion (`wantSuccessOriented` — a preference satisfied *if*
the complement is true), and inclusion (`wantQuineHintikka` —
satisfied *only if* it is true). `wantPreference` is the shared
schema, and the choice of relation fixes the reading's inferential
profile: success-oriented want is downward-entailing in the
complement, Quine-Hintikka want upward-entailing, exact-match want
neither (counterexample-construction deferred).
`wantEffectivePreference` is exact-match against the agent's effective
preferences, and `maxOrderingSource` extracts the `Set`-valued
ordering source `max[EP(Ad, w)]` (their eq. 88) consumed by the inner
modal of the double-modal anankastic analysis.

Declarations live in the `Desire` namespace, alongside the rival
want-semantics of `Desire.lean`. The anankastic-conditional analysis
is prosecuted in `Studies/CondoravdiLauer2016.lean`, the imperative
analysis (contra [roberts-2023]'s modal-in-LF account) in
`Studies/CondoravdiLauer2012.lean`, and discourse-particle uses
([deo-2025-bara]) in `Studies/Deo2025.lean`.
-/

namespace Desire

open Core.Order

variable {Agent W : Type*} (P : Agent → W → PreferenceStructure W)

/-! ### The want schema and its three readings -/

/-- `wantPreference P R a φ w` iff some maximal preference in the
    preferential background `P` — Condoravdi & Lauer's analog of a
    Kratzerian conversational background — stands in `R` to `φ`. The
    readings of *want* instantiate `R`; the choice determines the
    operator's inferential profile. -/
def wantPreference (R : Set W → Set W → Prop) (a : Agent) (φ : Set W)
    (w : W) : Prop :=
  ∃ p ∈ (P a w).maxElts, R φ p

/-- Exact-match want: some maximal preference is `φ` itself — the
    canonical reading. -/
def wantExactMatch : Agent → Set W → W → Prop :=
  wantPreference P (· = ·)

/-- Success-oriented want: some maximal preference is entailed by `φ`
    — a preference satisfied if `φ` is true. -/
def wantSuccessOriented : Agent → Set W → W → Prop :=
  wantPreference P (· ⊆ ·)

/-- Quine-Hintikka want: some maximal preference entails `φ` — a
    preference satisfied only if `φ` is true. -/
def wantQuineHintikka : Agent → Set W → W → Prop :=
  wantPreference P (· ⊇ ·)

variable {P}

/-- `wantExactMatch P a φ w` iff `φ ∈ max[P(a, w)]`. -/
theorem wantExactMatch_iff {a : Agent} {φ : Set W} {w : W} :
    wantExactMatch P a φ w ↔ φ ∈ (P a w).maxElts :=
  ⟨fun ⟨_, hp, h⟩ => by rwa [h], fun h => ⟨φ, h, rfl⟩⟩

/-- A pointwise implication between relations transfers between
    readings. -/
theorem wantPreference_mono {R R' : Set W → Set W → Prop}
    (h : ∀ φ p, R φ p → R' φ p) {a : Agent} {φ : Set W} {w : W} :
    wantPreference P R a φ w → wantPreference P R' a φ w :=
  fun ⟨p, hp, hR⟩ => ⟨p, hp, h φ p hR⟩

/-- Exact match implies the success-oriented reading. -/
theorem wantSuccessOriented_of_exactMatch {a : Agent} {φ : Set W} {w : W} :
    wantExactMatch P a φ w → wantSuccessOriented P a φ w :=
  wantPreference_mono fun _ _ h => h.subset

/-- Exact match implies the Quine-Hintikka reading. -/
theorem wantQuineHintikka_of_exactMatch {a : Agent} {φ : Set W} {w : W} :
    wantExactMatch P a φ w → wantQuineHintikka P a φ w :=
  wantPreference_mono fun _ _ h => h.superset

/-- Success-oriented want is downward-entailing in the complement. -/
theorem wantSuccessOriented_downward_entailing
    {a : Agent} {φ ψ : Set W} {w : W} (hφψ : φ ⊆ ψ) :
    wantSuccessOriented P a ψ w → wantSuccessOriented P a φ w :=
  fun ⟨p, hp, hψp⟩ => ⟨p, hp, hφψ.trans hψp⟩

/-- Quine-Hintikka want is upward-entailing in the complement. -/
theorem wantQuineHintikka_upward_entailing
    {a : Agent} {φ ψ : Set W} {w : W} (hφψ : φ ⊆ ψ) :
    wantQuineHintikka P a φ w → wantQuineHintikka P a ψ w :=
  fun ⟨p, hp, hpφ⟩ => ⟨p, hp, hpφ.trans hφψ⟩

/-! ### Effective preferences -/

variable {B : Agent → W → Set W} (EP : ∀ a w, EffectivePreference W (B a w))

/-- Exact-match want against the agent's effective preferences —
    Condoravdi & Lauer's designated background `EP`. -/
def wantEffectivePreference : Agent → Set W → W → Prop :=
  wantExactMatch fun a w => (EP a w).toPreferenceStructure

/-- Two effective-preference wants are jointly belief-consistent:
    wanting propositions the agent believes incompatible is
    impossible. -/
theorem wantEffectivePreference_jointly_belief_consistent
    {a : Agent} {φ ψ : Set W} {w : W}
    (hφ : wantEffectivePreference EP a φ w)
    (hψ : wantEffectivePreference EP a ψ w) :
    (φ ∩ ψ) ∩ B a w ≠ ∅ :=
  (EP a w).toPreferenceStructure.maxElts_pair_belief_compatible
    (EP a w).isConsistent
    (wantExactMatch_iff.mp hφ) (wantExactMatch_iff.mp hψ)

/-- `maxOrderingSource EP Ad w` is the set of maximal preferences in
    `EP(Ad, w)` — the ordering source consumed by the inner modal of
    the double-modal anankastic analysis. -/
def maxOrderingSource (Ad : Agent) : W → Set (Set W) :=
  fun w => (EP Ad w).toPreferenceStructure.maxElts

end Desire
