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
the locus of variation among the three readings of
[condoravdi-lauer-2016] eq. 71: equality (`WantExactMatch`, the
canonical reading, their eq. 69), reverse inclusion
(`WantSuccessOriented` — a preference satisfied *if* the complement is
true), and inclusion (`WantQuineHintikka` — satisfied *only if* it is
true). The choice fixes the reading's inferential profile:
success-oriented want is downward-entailing in the complement,
Quine-Hintikka want upward-entailing, exact-match want neither
(counterexample-construction deferred). `WantEffectivePreference` is
exact-match against the agent's effective preferences, and
`maxOrderingSource` extracts the `Set`-valued ordering source
`max[EP(Ad, w)]` (their eq. 88) consumed by the inner modal of the
double-modal anankastic analysis.

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

/-! ### The three readings of want -/

/-- Exact-match want: some maximal preference in the preferential
    background `P` — Condoravdi & Lauer's analog of a Kratzerian
    conversational background — is `φ` itself: `φ ∈ max[P(a, w)]`. The
    canonical reading. -/
def WantExactMatch (a : Agent) (φ : Set W) (w : W) : Prop :=
  φ ∈ (P a w).maxElts

/-- Success-oriented want: some maximal preference is entailed by `φ`
    — a preference satisfied if `φ` is true. -/
def WantSuccessOriented (a : Agent) (φ : Set W) (w : W) : Prop :=
  ∃ p ∈ (P a w).maxElts, φ ⊆ p

/-- Quine-Hintikka want: some maximal preference entails `φ` — a
    preference satisfied only if `φ` is true. -/
def WantQuineHintikka (a : Agent) (φ : Set W) (w : W) : Prop :=
  ∃ p ∈ (P a w).maxElts, p ⊆ φ

variable {P}

/-- Exact match implies the success-oriented reading. -/
theorem wantSuccessOriented_of_exactMatch {a : Agent} {φ : Set W} {w : W}
    (h : WantExactMatch P a φ w) : WantSuccessOriented P a φ w :=
  ⟨φ, h, subset_rfl⟩

/-- Exact match implies the Quine-Hintikka reading. -/
theorem wantQuineHintikka_of_exactMatch {a : Agent} {φ : Set W} {w : W}
    (h : WantExactMatch P a φ w) : WantQuineHintikka P a φ w :=
  ⟨φ, h, subset_rfl⟩

/-- Success-oriented want is downward-entailing in the complement. -/
theorem wantSuccessOriented_downward_entailing
    {a : Agent} {φ ψ : Set W} {w : W} (hφψ : φ ⊆ ψ) :
    WantSuccessOriented P a ψ w → WantSuccessOriented P a φ w :=
  fun ⟨p, hp, hψp⟩ => ⟨p, hp, hφψ.trans hψp⟩

/-- Quine-Hintikka want is upward-entailing in the complement. -/
theorem wantQuineHintikka_upward_entailing
    {a : Agent} {φ ψ : Set W} {w : W} (hφψ : φ ⊆ ψ) :
    WantQuineHintikka P a φ w → WantQuineHintikka P a ψ w :=
  fun ⟨p, hp, hpφ⟩ => ⟨p, hp, hpφ.trans hφψ⟩

/-! ### Effective preferences -/

variable {B : Agent → W → Set W} (EP : ∀ a w, EffectivePreference W (B a w))

/-- Exact-match want against the agent's effective preferences —
    Condoravdi & Lauer's designated background `EP`. -/
def WantEffectivePreference : Agent → Set W → W → Prop :=
  WantExactMatch fun a w => (EP a w).toPreferenceStructure

/-- Two effective-preference wants are jointly belief-consistent:
    wanting propositions the agent believes incompatible is
    impossible. -/
theorem wantEffectivePreference_jointly_belief_consistent
    {a : Agent} {φ ψ : Set W} {w : W}
    (hφ : WantEffectivePreference EP a φ w)
    (hψ : WantEffectivePreference EP a ψ w) :
    (φ ∩ ψ) ∩ B a w ≠ ∅ :=
  (EP a w).toPreferenceStructure.maxElts_pair_belief_compatible
    (EP a w).isConsistent hφ hψ

/-- `maxOrderingSource EP Ad w` is the set of maximal preferences in
    `EP(Ad, w)` — the ordering source consumed by the inner modal of
    the double-modal anankastic analysis. -/
def maxOrderingSource (Ad : Agent) : W → Set (Set W) :=
  fun w => (EP Ad w).toPreferenceStructure.maxElts

end Desire
