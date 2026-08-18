import Mathlib.Order.Defs.Unbundled
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Rat.Defs
import Linglib.Features.Attitudes
import Linglib.Semantics.Attitudes.Distributivity

/-!
# Preference in attitude semantics

The two mathematizations of preference that attitude semantics runs
on, gathered: qualitative preference *orderings* on propositions and
quantitative preference *degrees* measured against thresholds.

A **preference structure** ([condoravdi-lauer-2012] (65)) is a pair
`⟨P, ≺⟩` where `P ⊆ ℘(W)` is a set of propositions and `≺` is a strict
partial order — the mathematical spine of Condoravdi & Lauer's
effective-preference framework ([condoravdi-lauer-2011], [lauer-2013],
[condoravdi-lauer-2016]), consumed by the *want* semantics in
`Desire.lean` and the dynamic necessity operator of
`Semantics/Dynamic/UpdateSemantics/Necessity.lean`. `maxElts` (their
eq. 70) collects the maximal elements. Relative to an information
state `B`, `consistent` (eq. 66) demands that any subfamily of
preferences jointly incompatible with `B` contain a strictly ranked
pair, and `realistic` (eq. 67) — derivable from consistency
(`consistent_implies_realistic`, their fn. 30) — demands every
preference be belief-compatible. `maxElts_pair_belief_compatible` is
the conflicting-desires blocker: two maximal preferences of a
consistent structure meet inside `B`. `maxInducedLe` is the
world-side preorder induced by maximal preferences, the Kratzer-style
([kratzer-1981]) derivation of a world ordering from an ordering
source.

A **preferential predicate** ([villalta-2008]) measures preference as
a degree: ⟦x V p⟧(C) = μ(x, p) > θ(C), for a preference degree
function μ and a contextual threshold θ over a comparison class C.
[qing-uegaki-2025] classify non-veridical preferentials by clausal
distributivity (`Distributivity.IsDistributive`) and evaluative
valence: the degree-comparison predicates built here are distributive
by construction (`mkDegreeComparison_isDistributive`), while *worry*
and Mandarin *qidai* carry an extra global condition on the question
that breaks distributivity (`worry_not_distributive`).
`ThresholdSignificance` is the presupposition [uegaki-sudo-2019]
posit for degree constructions — triggered by positive preferentials,
not by negative ones ([qing-uegaki-2025] §3.2) — from which the
anti-rogativity of the distributive positive class is derived in
`Studies/UegakiSudo2019.lean`; the classification's cross-linguistic
support lives in `Studies/QingEtAl2025.lean`, and the emotive
doxastic refinement of *hope* and *fear* ([anand-hacquard-2013]) in
`Studies/AnandHacquard2013.lean`.
-/

variable {W : Type*}

/-- A preference structure: a set of propositions `prefs` and a strict
    ranking `prec`, with `prec p q` read "q is strictly preferred to p".
    The ranking is a relation on all of `Set W`; only its restriction to
    `prefs` is ever observed. -/
structure PreferenceStructure (W : Type*) where
  /-- The propositions the agent has preferences over. -/
  prefs : Set (Set W)
  /-- The strict ranking. `prec p q` reads "q is strictly preferred
      to p". -/
  prec : Set W → Set W → Prop
  /-- The strict-partial-order axioms, packaged as a mathlib typeclass. -/
  isStrictOrder : IsStrictOrder (Set W) prec

namespace PreferenceStructure

variable (P : PreferenceStructure W)

instance : IsStrictOrder (Set W) P.prec := P.isStrictOrder

/-- The maximal elements of the preference structure: the preferences
    with nothing in `prefs` strictly above them. -/
def maxElts : Set (Set W) :=
  {p ∈ P.prefs | ∀ q ∈ P.prefs, ¬ P.prec p q}

@[simp] theorem mem_maxElts {φ : Set W} :
    φ ∈ P.maxElts ↔ φ ∈ P.prefs ∧ ∀ q ∈ P.prefs, ¬ P.prec φ q :=
  Iff.rfl

theorem maxElts_subset_prefs : P.maxElts ⊆ P.prefs := fun _ h => h.1

/-- Consistency w.r.t. an information state `B`: any subfamily of
    preferences whose joint realization is incompatible with `B`
    contains a strictly ranked pair. -/
def consistent (B : Set W) : Prop :=
  ∀ X : Set (Set W), X ⊆ P.prefs → B ∩ ⋂ p ∈ X, p = ∅ →
    ∃ p ∈ X, ∃ q ∈ X, P.prec p q

/-- Realism w.r.t. an information state: every preference is
    belief-compatible. -/
def realistic (B : Set W) : Prop :=
  ∀ p ∈ P.prefs, p ∩ B ≠ ∅

/-- Realism follows from consistency via the singleton-`X` case combined
    with irreflexivity. -/
theorem consistent_implies_realistic {B : Set W} (hC : P.consistent B) :
    P.realistic B := by
  intro p hp hpB
  obtain ⟨q, hq, r, hr, hqr⟩ := hC {p} (Set.singleton_subset_iff.mpr hp) (by
    rw [Set.biInter_singleton, Set.inter_comm]; exact hpB)
  rw [Set.mem_singleton_iff] at hq hr
  rw [hq, hr] at hqr
  exact irrefl_of P.prec p hqr

/-- Pair belief-consistency of maximal preferences: given `consistent B`,
    two maximal preferences cannot have an empty intersection w.r.t. `B`.
    The four cases of the consistency conclusion are blocked by
    irreflexivity (diagonal pairs) and maximality (off-diagonal pairs). -/
theorem maxElts_pair_belief_compatible {B : Set W} (hC : P.consistent B)
    {φ ψ : Set W} (hφ : φ ∈ P.maxElts) (hψ : ψ ∈ P.maxElts) :
    (φ ∩ ψ) ∩ B ≠ ∅ := by
  intro hEmpty
  obtain ⟨hφP, hφmax⟩ := hφ
  obtain ⟨hψP, hψmax⟩ := hψ
  have hX_sub : ({φ, ψ} : Set (Set W)) ⊆ P.prefs :=
    Set.insert_subset hφP (Set.singleton_subset_iff.mpr hψP)
  have hX_int : B ∩ ⋂ p ∈ ({φ, ψ} : Set (Set W)), p = ∅ := by
    rw [Set.biInter_pair, Set.inter_comm]; exact hEmpty
  obtain ⟨p, hpX, q, hqX, hpq⟩ := hC _ hX_sub hX_int
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpX hqX
  rcases hpX with hp | hp <;> rcases hqX with hq | hq <;> rw [hp, hq] at hpq
  · exact irrefl_of P.prec φ hpq
  · exact hφmax ψ hψP hpq
  · exact hψmax φ hφP hpq
  · exact irrefl_of P.prec ψ hpq

/-! ### The world preorder induced by maximal preferences -/

/-- The world-level preorder induced by maximal preferences:
    `maxInducedLe w v` iff `w` verifies every maximal preference that
    `v` verifies. -/
def maxInducedLe : W → W → Prop :=
  fun w v => ∀ p ∈ P.maxElts, v ∈ p → w ∈ p

theorem maxInducedLe_refl (w : W) :
    P.maxInducedLe w w := fun _ _ hw => hw

theorem maxInducedLe_trans {w v u : W}
    (hwv : P.maxInducedLe w v) (hvu : P.maxInducedLe v u) :
    P.maxInducedLe w u :=
  fun p hp hu => hwv p hp (hvu p hp hu)

end PreferenceStructure

/-! ### Degree-comparison preferential predicates -/

namespace Preferential

open Features (AttitudeValence)

variable {W E : Type*}

/-- A preferential attitude predicate: an evaluative valence, a
    preference degree function, a contextual threshold, and
    propositional and question semantics relative to a comparison
    class of propositions. -/
structure PreferentialPredicate (W E : Type*) where
  /-- Evaluative valence (positive for *hope*, negative for *fear*). -/
  valence : AttitudeValence
  /-- Preference degree function: `μ x p` is how strongly `x` prefers
      (or, for negative valence, dreads) `p`. -/
  μ : E → Finset W → ℚ
  /-- Contextual threshold over a comparison class. -/
  θ : List (Finset W) → ℚ
  /-- ⟦x V p⟧(C), the propositional semantics. -/
  propSemantics : E → Finset W → List (Finset W) → Prop
  /-- ⟦x V Q⟧(C), the question semantics. -/
  questionSemantics : E → List (Finset W) → List (Finset W) → Prop

/-- A preferential predicate is clausally distributive when its
    question semantics is the existential over its propositional
    semantics — the world-free instance of
    `Distributivity.IsDistributive` (preferential semantics are
    world-independent because the predicates are non-veridical). -/
def PreferentialPredicate.IsDistributive (V : PreferentialPredicate W E) : Prop :=
  ∀ (x : E) (Q C : List (Finset W)),
    V.questionSemantics x Q C ↔ ∃ p ∈ Q, V.propSemantics x p C

/-! ### Degree-comparison predicates -/

/-- Degree-comparison predicate ([villalta-2008]): ⟦x V p⟧(C) =
    μ(x, p) > θ(C), with the question semantics the pointwise
    existential. -/
def mkDegreeComparison (valence : AttitudeValence)
    (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ) :
    PreferentialPredicate W E where
  valence := valence
  μ := μ
  θ := θ
  propSemantics x p C := μ x p > θ C
  questionSemantics x Q C := ∃ p ∈ Q, μ x p > θ C

/-- Degree-comparison predicates are clausally distributive by
    construction: the question semantics is the existential over the
    propositional semantics. -/
theorem mkDegreeComparison_isDistributive (valence : AttitudeValence)
    (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ) :
    (mkDegreeComparison valence μ θ).IsDistributive :=
  fun _ _ _ => Iff.rfl

/-- *hope*: degree comparison, positive valence. What distinguishes
    *hope* from *want* is an additional doxastic component
    ([anand-hacquard-2013]), formalized in
    `Studies/AnandHacquard2013.lean`. -/
def hope (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ) :
    PreferentialPredicate W E :=
  mkDegreeComparison .positive μ θ

/-- *fear*: degree comparison, negative valence. -/
def fear (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ) :
    PreferentialPredicate W E :=
  mkDegreeComparison .negative μ θ

/-- *expect*: degree comparison, positive valence. -/
def expect (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ) :
    PreferentialPredicate W E :=
  mkDegreeComparison .positive μ θ

/-- *wish*: degree comparison, positive valence. -/
def wish (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ) :
    PreferentialPredicate W E :=
  mkDegreeComparison .positive μ θ

/-- *dread*: degree comparison, negative valence. -/
def dread (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ) :
    PreferentialPredicate W E :=
  mkDegreeComparison .negative μ θ

/-! ### Non-distributive preferentials -/

/-- *worry*: propositionally a degree comparison, but the question
    semantics adds a global uncertainty condition on the question —
    not reducible to the existential over answers
    ([qing-uegaki-2025] §3.1.2). -/
def worry (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ)
    (Uncertain : E → List (Finset W) → Prop) :
    PreferentialPredicate W E where
  valence := .negative
  μ := μ
  θ := θ
  propSemantics x p C := μ x p > θ C
  questionSemantics x Q C := Uncertain x Q ∧ ∃ p ∈ Q, μ x p > θ C

/-- Mandarin *qidai* "look forward to": positive valence, with an
    anticipation-of-resolution condition on the question — a positive
    non-distributive preferential ([qing-uegaki-2025] §3.1.1). -/
def qidai (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ)
    (AnticipatesResolution : E → List (Finset W) → Prop) :
    PreferentialPredicate W E where
  valence := .positive
  μ := μ
  θ := θ
  propSemantics x p C := μ x p > θ C
  questionSemantics x Q C := AnticipatesResolution x Q ∧ ∃ p ∈ Q, μ x p > θ C

/-- *worry* is not clausally distributive: when the agent is not
    uncertain about `Q` but some answer clears the threshold, the
    existential over the propositional semantics holds while the
    question semantics fails. -/
theorem worry_not_distributive (μ : E → Finset W → ℚ)
    (θ : List (Finset W) → ℚ) (Uncertain : E → List (Finset W) → Prop)
    (x : E) (Q C : List (Finset W)) (hu : ¬ Uncertain x Q)
    (h : ∃ p ∈ Q, μ x p > θ C) :
    ¬ (worry μ θ Uncertain).IsDistributive :=
  fun hdist => hu (((hdist x Q C).mpr h).1)

/-! ### Threshold significance -/

/-- The Threshold Significance Presupposition ([uegaki-sudo-2019]):
    some member of the comparison class clears the threshold. Degree
    constructions presuppose it generally; positive preferentials
    trigger it while negative ones do not ([qing-uegaki-2025] §3.2),
    which is how *fear*-type predicates escape the anti-rogativity
    triviality derived in `Studies/UegakiSudo2019.lean`. -/
def ThresholdSignificance (μ : E → Finset W → ℚ)
    (θ : List (Finset W) → ℚ) (x : E) (C : List (Finset W)) : Prop :=
  ∃ p ∈ C, μ x p > θ C

end Preferential
