module

public import Mathlib.Order.Defs.Unbundled
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Rat.Defs
public import Linglib.Semantics.Attitudes.Basic
public import Linglib.Semantics.Attitudes.Distributivity
public import Linglib.Core.Order.Minimals

/-!
# Preference in attitude semantics

This file defines the two mathematizations of preference that attitude semantics runs on,
qualitative preference orderings on propositions and quantitative preference degrees measured
against thresholds.

A preference structure, in the sense of Condoravdi and Lauer, is a pair of a set of
propositions and a strict partial order on them. It is the mathematical spine of their
effective-preference framework, and is consumed by the *want* semantics in `Desire.lean` and by
the dynamic necessity operator of `Semantics/Dynamic/UpdateSemantics/Necessity.lean`. `maxElts`
collects the maximal elements. Relative to an information state `B`, a structure is `Consistent`
when any subfamily of preferences jointly incompatible with `B` contains a strictly ranked pair,
and `Realistic` when every preference is compatible with `B`, which follows from consistency
(`Consistent.realistic`). A preference incompatible with a maximal one is ranked strictly below
it (`Consistent.prec_of_mem_maxElts`), so the maximal preferences of a consistent structure are
jointly compatible with the information (`Consistent.inter_sInter_maxElts_nonempty`, and for a
pair `Consistent.inter_inter_nonempty_of_mem_maxElts`), and a chain of realistic preferences is
consistent (`consistent_of_realistic_of_isChain`). `maxPreorder` is the preorder on worlds that
the maximal preferences induce, by Kratzer's derivation of a world ordering from an ordering
source, and `best` gives its minimal worlds in a domain, which are exactly the worlds realizing
every maximal preference when there are any (`best_eq_of_nonempty`). `discrete` is the unranked
structure on a set of preferences and `single` its one-preference case.

A preferential predicate, in the sense of Villalta, measures preference as a degree, with
⟦x V p⟧(C) = μ(x, p) > θ(C) for a preference degree function μ and a contextual threshold θ over
a comparison class C. The degree-comparison predicates built here are clausally distributive by
construction (`mkDegreeComparison_isDistributive`), and a predicate that holds of a question but
of none of its answers is not (`PreferentialPredicate.not_isDistributive_of_forall_not`). This
is the diagnostic that Elliott and colleagues apply to *care*, and that Qing and colleagues
apply to *worry* and Mandarin *qidai* in `Studies/QingEtAl2025.lean`. `ThresholdSignificance` is
the presupposition that Uegaki and Sudo posit for degree constructions, from which the
anti-rogativity of *hope* is derived in `Studies/UegakiSudo2019.lean`. The emotive doxastic
refinement of *hope* and *fear* due to Anand and Hacquard is in
`Studies/AnandHacquard2013.lean`.

## References

* [C. Condoravdi and S. Lauer, *Performative Verbs and Performative Acts*
  (2011)][condoravdi-lauer-2011]
* [C. Condoravdi and S. Lauer, *Imperatives: Meaning and Illocutionary Force*
  (2012)][condoravdi-lauer-2012]
* [C. Condoravdi and S. Lauer, *Anankastic Conditionals are Just Conditionals*
  (2016)][condoravdi-lauer-2016]
* [S. Lauer, *Towards a Dynamic Pragmatics* (2013)][lauer-2013]
* [A. Kratzer, *The Notional Category of Modality* (1981)][kratzer-1981]
* [E. Villalta, *Mood and Gradability: An Investigation of the Subjunctive Mood in Spanish*
  (2008)][villalta-2008]
* [W. Uegaki and Y. Sudo, *The hope-wh puzzle* (2019)][uegaki-sudo-2019]
* [C. Qing, D. Özyıldız, F. Roelofsen, M. Romero and W. Uegaki, *When can non-veridical
  preferential attitude predicates take questions?* (2025)][qing-uegaki-2025]
* [P. Anand and V. Hacquard, *Epistemics and attitudes* (2013)][anand-hacquard-2013]
* [P. D. Elliott, N. Klinedinst, Y. Sudo and W. Uegaki, *Predicates of Relevance and Theories of
  Question Embedding* (2017)][elliott-etal-2017]
-/

@[expose] public section

variable {W : Type*}

/-- A preference structure is a set of propositions `prefs` with a strict ranking `prec`, where
`prec p q` reads "`q` is strictly preferred to `p`". The ranking is a relation on all of `Set W`,
and only its restriction to `prefs` is ever observed. -/
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

/-- The maximal elements of the preference structure are the preferences with nothing in `prefs`
strictly above them. -/
def maxElts : Set (Set W) :=
  {p ∈ P.prefs | ∀ q ∈ P.prefs, ¬ P.prec p q}

@[simp] theorem mem_maxElts {φ : Set W} :
    φ ∈ P.maxElts ↔ φ ∈ P.prefs ∧ ∀ q ∈ P.prefs, ¬ P.prec φ q :=
  Iff.rfl

theorem maxElts_subset_prefs : P.maxElts ⊆ P.prefs := fun _ h ↦ h.1

/-- A preference structure is consistent with respect to an information state `B` when any subfamily
of preferences whose joint realization is incompatible with `B` contains a strictly ranked pair. -/
def Consistent (B : Set W) : Prop :=
  ∀ X ⊆ P.prefs, B ∩ ⋂₀ X = ∅ → ∃ p ∈ X, ∃ q ∈ X, P.prec p q

/-- A preference structure is realistic with respect to an information state when every preference
is compatible with it. -/
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

/-- A consistent structure has a nonempty information state, as the empty subfamily shows. -/
theorem Consistent.nonempty (hC : P.Consistent B) : B.Nonempty :=
  Set.nonempty_iff_ne_empty.2 fun h ↦
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
  Set.nonempty_iff_ne_empty.2 fun h ↦
    let ⟨_, hp, _, hq, hpq⟩ := hC _ P.maxElts_subset_prefs h
    hp.2 _ hq.1 hpq

/-- Two maximal preferences of a consistent structure are jointly belief-compatible, which blocks
conflicting desires. -/
theorem Consistent.inter_inter_nonempty_of_mem_maxElts (hC : P.Consistent B) {φ ψ : Set W}
    (hφ : φ ∈ P.maxElts) (hψ : ψ ∈ P.maxElts) : (B ∩ (φ ∩ ψ)).Nonempty :=
  hC.inter_sInter_maxElts_nonempty.mono <| Set.inter_subset_inter_right _ <|
    Set.subset_inter (Set.sInter_subset_of_mem hφ) (Set.sInter_subset_of_mem hψ)

/-- A chain of realistic preferences is consistent. -/
theorem consistent_of_realistic_of_isChain (hR : P.Realistic B) (hc : IsChain P.prec P.prefs)
    (hB : B.Nonempty) : P.Consistent B := by
  intro X hX hXB
  by_contra h
  have hs : X.Subsingleton := fun p hp q hq ↦
    by_contra fun hne ↦ (hc (hX hp) (hX hq) hne).elim (fun hpq ↦ h ⟨p, hp, q, hq, hpq⟩)
      (fun hqp ↦ h ⟨q, hq, p, hp, hqp⟩)
  rcases hs.eq_empty_or_singleton with rfl | ⟨p, rfl⟩
  · rw [Set.sInter_empty, Set.inter_univ] at hXB
    exact hB.ne_empty hXB
  · rw [Set.sInter_singleton, Set.inter_comm] at hXB
    exact hR p (hX (Set.mem_singleton p)) hXB

end Consistent

/-! ### The world preorder induced by maximal preferences -/

/-- The world preorder induced by the maximal preferences ranks `w` below `v` when `w` verifies
every maximal preference that `v` verifies. It is the ordering-source construction with `maxElts` as
the source. -/
@[reducible] def maxPreorder : Preorder W := Preorder.ofCriteria (· ∈ ·) P.maxElts

theorem maxPreorder_le_iff {w v : W} :
    P.maxPreorder.le w v ↔ ∀ p ∈ P.maxElts, v ∈ p → w ∈ p :=
  Iff.rfl

/-- The worlds of `F` that best realize the maximal preferences. -/
def best (F : Set W) : Set W := P.maxPreorder.minimals F

/-- When some world of `F` realizes every maximal preference, the best worlds of `F` are
    exactly those. -/
theorem best_eq_of_nonempty {F : Set W} (h : (F ∩ ⋂₀ P.maxElts).Nonempty) :
    P.best F = F ∩ ⋂₀ P.maxElts :=
  Preorder.minimals_ofCriteria_eq h

/-! ### Unranked preferences -/

/-- The discrete structure has the preferences `S` and no ranking, so every preference is maximal.
-/
def discrete (S : Set (Set W)) : PreferenceStructure W where
  prefs := S
  prec _ _ := False
  isStrictOrder := { irrefl := fun _ h ↦ h, trans := fun _ _ _ h _ ↦ h }

@[simp] theorem maxElts_discrete (S : Set (Set W)) : (discrete S).maxElts = S :=
  Set.ext fun _ ↦ ⟨And.left, fun h ↦ ⟨h, fun _ _ h ↦ h⟩⟩

/-- Unranked preferences are consistent when jointly belief-compatible. -/
theorem consistent_discrete {S : Set (Set W)} {B : Set W} (h : (B ∩ ⋂₀ S).Nonempty) :
    (discrete S).Consistent B := fun _ hX hXB ↦
  absurd hXB (h.mono (Set.inter_subset_inter_right _ (Set.sInter_subset_sInter hX))).ne_empty

/-- The structure with the single preference `p`. -/
abbrev single (p : Set W) : PreferenceStructure W := discrete {p}

@[simp] theorem maxElts_single (p : Set W) : (single p).maxElts = {p} := maxElts_discrete _

theorem consistent_single {p B : Set W} (h : (p ∩ B).Nonempty) : (single p).Consistent B :=
  consistent_discrete (by rwa [Set.sInter_singleton, Set.inter_comm])

end PreferenceStructure

/-! ### Degree-comparison preferential predicates -/

namespace Preferential

variable {W E : Type*}

/-- A preferential attitude predicate consists of an evaluative valence, a preference degree
function, a contextual threshold, and propositional and question semantics relative to a comparison
class of propositions. -/
structure PreferentialPredicate (W E : Type*) where
  /-- Evaluative valence (positive for *hope*, negative for *fear*). -/
  valence : Valence
  /-- The preference degree `μ x p` is how strongly `x` prefers, or for negative valence dreads,
  `p`. -/
  μ : E → Finset W → ℚ
  /-- Contextual threshold over a comparison class. -/
  θ : List (Finset W) → ℚ
  /-- ⟦x V p⟧(C), the propositional semantics. -/
  propSemantics : E → Finset W → List (Finset W) → Prop
  /-- ⟦x V Q⟧(C), the question semantics. -/
  questionSemantics : E → List (Finset W) → List (Finset W) → Prop

/-- A preferential predicate is clausally distributive when its question semantics is the
existential over its propositional semantics. This is the world-free instance of
`Distributivity.IsDistributive`, since preferential semantics are world-independent for
non-veridical predicates. -/
def PreferentialPredicate.IsDistributive (V : PreferentialPredicate W E) : Prop :=
  ∀ (x : E) (Q C : List (Finset W)),
    V.questionSemantics x Q C ↔ ∃ p ∈ Q, V.propSemantics x p C

/-- A predicate that holds of a question but of none of its answers is not clausally distributive.
-/
theorem PreferentialPredicate.not_isDistributive_of_forall_not {V : PreferentialPredicate W E}
    {x : E} {Q C : List (Finset W)} (hQ : V.questionSemantics x Q C)
    (h : ∀ p ∈ Q, ¬ V.propSemantics x p C) : ¬ V.IsDistributive :=
  fun hV ↦ let ⟨p, hp, hxp⟩ := (hV x Q C).1 hQ; h p hp hxp

/-! ### Degree-comparison predicates -/

/-- A degree-comparison predicate has ⟦x V p⟧(C) = μ(x, p) > θ(C), with the pointwise existential as
its question semantics. -/
def mkDegreeComparison (valence : Valence)
    (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ) :
    PreferentialPredicate W E where
  valence := valence
  μ := μ
  θ := θ
  propSemantics x p C := μ x p > θ C
  questionSemantics x Q C := ∃ p ∈ Q, μ x p > θ C

/-- Degree-comparison predicates are clausally distributive by construction, since the question
semantics is the existential over the propositional semantics. -/
theorem mkDegreeComparison_isDistributive (valence : Valence)
    (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ) :
    (mkDegreeComparison valence μ θ).IsDistributive :=
  fun _ _ _ ↦ Iff.rfl

/-- The predicate *hope* is a degree comparison of positive valence. Its difference from *want* is
an additional doxastic component, formalized in `Studies/AnandHacquard2013.lean`. -/
def hope (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ) :
    PreferentialPredicate W E :=
  mkDegreeComparison .positive μ θ

/-- The predicate *fear* is a degree comparison of negative valence. -/
def fear (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ) :
    PreferentialPredicate W E :=
  mkDegreeComparison .negative μ θ

/-- The predicate *expect* is a degree comparison of positive valence. -/
def expect (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ) :
    PreferentialPredicate W E :=
  mkDegreeComparison .positive μ θ

/-- The predicate *wish* is a degree comparison of positive valence. -/
def wish (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ) :
    PreferentialPredicate W E :=
  mkDegreeComparison .positive μ θ

/-- The predicate *dread* is a degree comparison of negative valence. -/
def dread (μ : E → Finset W → ℚ) (θ : List (Finset W) → ℚ) :
    PreferentialPredicate W E :=
  mkDegreeComparison .negative μ θ

/-! ### Threshold significance -/

/-- The Threshold Significance Presupposition says that some member of the comparison class clears
the threshold. Degree constructions presuppose it generally. Positive preferentials trigger it while
negative ones do not, which is how predicates of the *fear* type escape the anti-rogativity
triviality derived in `Studies/UegakiSudo2019.lean`. -/
def ThresholdSignificance (μ : E → Finset W → ℚ)
    (θ : List (Finset W) → ℚ) (x : E) (C : List (Finset W)) : Prop :=
  ∃ p ∈ C, μ x p > θ C

end Preferential
