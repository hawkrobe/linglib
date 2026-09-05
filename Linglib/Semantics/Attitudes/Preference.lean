import Mathlib.Order.Defs.Unbundled
import Mathlib.Order.Preorder.Chain
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Rat.Defs
import Linglib.Features.Attitudes
import Linglib.Semantics.Attitudes.Distributivity
import Linglib.Core.Order.Normality

/-!
# Preference in attitude semantics

The two mathematizations of preference that attitude semantics runs
on, gathered: qualitative preference *orderings* on propositions and
quantitative preference *degrees* measured against thresholds.

A **preference structure** ([condoravdi-lauer-2012] (28),
[condoravdi-lauer-2016] (65)) is a pair `⟨P, ≺⟩` where `P ⊆ ℘(W)` is a
set of propositions and `≺` is a strict partial order — the
mathematical spine of Condoravdi & Lauer's effective-preference
framework ([condoravdi-lauer-2011], [lauer-2013],
[condoravdi-lauer-2016]), consumed by the *want* semantics in
`Desire.lean` and the dynamic necessity operator of
`Semantics/Dynamic/UpdateSemantics/Necessity.lean`. `maxElts`
([condoravdi-lauer-2016] (70)) collects the maximal elements. Relative
to an information state `B`, `Consistent` (their (66)) demands that
any subfamily of preferences jointly incompatible with `B` contain a
strictly ranked pair, and `Realistic` (their (67)) — derivable from
consistency (`Consistent.realistic`, their fn. 30) — demands every
preference be belief-compatible. A preference incompatible with a
maximal one is ranked strictly below it
(`Consistent.prec_of_mem_maxElts`), so the maximal preferences of a
consistent structure are jointly belief-compatible
(`Consistent.inter_sInter_maxElts_nonempty` and, for a pair, the
conflicting-desires blocker
`Consistent.inter_inter_nonempty_of_mem_maxElts`), and a chain of
realistic preferences is consistent
(`consistent_of_realistic_of_isChain`). `maxPreorder` is the
world-side preorder induced by maximal preferences, the Kratzer-style
([kratzer-1981]) derivation of a world ordering from an ordering
source, and `best` its optimal worlds in a domain, exactly the worlds
realizing every maximal preference when there are any
(`best_eq_of_nonempty`); `discrete` is the unranked structure on a set of
preferences and `single` its one-preference case.

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
def Consistent (B : Set W) : Prop :=
  ∀ X ⊆ P.prefs, B ∩ ⋂₀ X = ∅ → ∃ p ∈ X, ∃ q ∈ X, P.prec p q

/-- Realism w.r.t. an information state: every preference is
    belief-compatible. -/
def Realistic (B : Set W) : Prop :=
  ∀ p ∈ P.prefs, p ∩ B ≠ ∅

section Consistent

variable {P} {B : Set W}

/-- Realism follows from consistency via the singleton-`X` case combined
    with irreflexivity. -/
theorem Consistent.realistic (hC : P.Consistent B) : P.Realistic B := by
  intro p hp hpB
  obtain ⟨_, rfl, _, rfl, hqr⟩ := hC {p} (Set.singleton_subset_iff.2 hp)
    (by rw [Set.sInter_singleton, Set.inter_comm]; exact hpB)
  exact irrefl_of P.prec _ hqr

/-- A consistent structure has a nonempty information state: the empty subfamily. -/
theorem Consistent.nonempty (hC : P.Consistent B) : B.Nonempty :=
  Set.nonempty_iff_ne_empty.2 λ h =>
    let ⟨_, hp, _⟩ := hC ∅ (Set.empty_subset _) (by rw [Set.sInter_empty, Set.inter_univ]; exact h)
    hp

/-- A preference incompatible with a maximal one is ranked strictly below it. -/
theorem Consistent.prec_of_mem_maxElts (hC : P.Consistent B) {p q : Set W} (hp : p ∈ P.maxElts)
    (hq : q ∈ P.prefs) (h : B ∩ (p ∩ q) = ∅) : P.prec q p := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hC {p, q}
    (Set.insert_subset hp.1 (Set.singleton_subset_iff.2 hq)) (by rwa [Set.sInter_pair])
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  exacts [absurd hxy (irrefl_of P.prec _), absurd hxy (hp.2 _ hq), hxy,
    absurd hxy (irrefl_of P.prec _)]

/-- The maximal preferences of a consistent structure are jointly belief-compatible. -/
theorem Consistent.inter_sInter_maxElts_nonempty (hC : P.Consistent B) :
    (B ∩ ⋂₀ P.maxElts).Nonempty :=
  Set.nonempty_iff_ne_empty.2 λ h =>
    let ⟨_, hp, _, hq, hpq⟩ := hC _ P.maxElts_subset_prefs h
    hp.2 _ hq.1 hpq

/-- Two maximal preferences of a consistent structure are jointly belief-compatible: the
    conflicting-desires blocker. -/
theorem Consistent.inter_inter_nonempty_of_mem_maxElts (hC : P.Consistent B) {φ ψ : Set W}
    (hφ : φ ∈ P.maxElts) (hψ : ψ ∈ P.maxElts) : (B ∩ (φ ∩ ψ)).Nonempty :=
  hC.inter_sInter_maxElts_nonempty.mono <| Set.inter_subset_inter_right _ <|
    Set.subset_inter (Set.sInter_subset_of_mem hφ) (Set.sInter_subset_of_mem hψ)

/-- A chain of realistic preferences is consistent. -/
theorem consistent_of_realistic_of_isChain (hR : P.Realistic B) (hc : IsChain P.prec P.prefs)
    (hB : B.Nonempty) : P.Consistent B := by
  intro X hX hXB
  by_contra h
  have hs : X.Subsingleton := λ p hp q hq =>
    by_contra λ hne => (hc (hX hp) (hX hq) hne).elim (λ hpq => h ⟨p, hp, q, hq, hpq⟩)
      (λ hqp => h ⟨q, hq, p, hp, hqp⟩)
  rcases hs.eq_empty_or_singleton with rfl | ⟨p, rfl⟩
  · rw [Set.sInter_empty, Set.inter_univ] at hXB
    exact hB.ne_empty hXB
  · rw [Set.sInter_singleton, Set.inter_comm] at hXB
    exact hR p (hX (Set.mem_singleton p)) hXB

end Consistent

/-! ### The world preorder induced by maximal preferences -/

/-- The world preorder induced by the maximal preferences, [kratzer-1981]'s ordering-source
    construction with `maxElts` as the source: `w ≤ v` iff `w` verifies every maximal
    preference that `v` verifies. -/
@[reducible] def maxPreorder : Preorder W := Preorder.ofCriteria (· ∈ ·) P.maxElts

theorem maxPreorder_le_iff {w v : W} :
    P.maxPreorder.le w v ↔ ∀ p ∈ P.maxElts, v ∈ p → w ∈ p :=
  Iff.rfl

/-- The worlds of `F` that best realize the maximal preferences. -/
def best (F : Set W) : Set W := Core.Order.Normality.optimal P.maxPreorder F

/-- When some world of `F` realizes every maximal preference, the best worlds of `F` are
    exactly those. -/
theorem best_eq_of_nonempty {F : Set W} (h : (F ∩ ⋂₀ P.maxElts).Nonempty) :
    P.best F = F ∩ ⋂₀ P.maxElts :=
  Core.Order.Normality.optimal_ofCriteria_eq h

/-! ### Unranked preferences -/

/-- The structure with the preferences `S` and no ranking: every preference is maximal. -/
def discrete (S : Set (Set W)) : PreferenceStructure W where
  prefs := S
  prec _ _ := False
  isStrictOrder := { irrefl := λ _ h => h, trans := λ _ _ _ h _ => h }

@[simp] theorem maxElts_discrete (S : Set (Set W)) : (discrete S).maxElts = S :=
  Set.ext λ _ => ⟨And.left, λ h => ⟨h, λ _ _ h => h⟩⟩

/-- The structure with the single preference `p`. -/
abbrev single (p : Set W) : PreferenceStructure W := discrete {p}

@[simp] theorem maxElts_single (p : Set W) : (single p).maxElts = {p} := maxElts_discrete _

theorem consistent_single {p B : Set W} (h : (p ∩ B).Nonempty) : (single p).Consistent B :=
  consistent_of_realistic_of_isChain
    (λ _ hq => by rw [Set.mem_singleton_iff.1 hq]; exact h.ne_empty)
    (Set.pairwise_singleton _ _) (h.mono Set.inter_subset_right)

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
