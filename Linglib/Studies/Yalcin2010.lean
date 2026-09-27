module

public import Linglib.Logic.ComparativeProbability.Patterns
public import Linglib.Logic.ComparativeProbability.WorldOrdering
public import Linglib.Core.Order.Probability.Content
public import Linglib.Semantics.Modality.Kratzer.Operators
public import Linglib.Data.Examples.Yalcin2010
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.FinCases

/-!
# Yalcin (2010): Probability operators

[yalcin-2010] asks what formal structure the semantics of *probably*, *likely* and the
comparative *at least as likely as* requires, and answers by running three candidate
semantics against a list of inference patterns: the intuitively valid V1–V12, the invalid I1
and I2, and the questionable Conjunctivitis E1 (`Logic/ComparativeProbability/Patterns`).
The relative likelihood account of [kratzer-1991] lifts the preorder an ordering source
induces on worlds to propositions by [lewis-1973]'s clause, every world of the less likely
proposition being matched by an at least as high world of the more likely one; the
possibility space account of [hamblin-1959] measures a proposition by its most possible
world; the probability space account measures it by a finitely additive probability. The
paper's verdict: Kratzer's account validates V1–V10 but fails positive form transfer, and
validates the union property I1 whose special case I2 collapses equiprobability into
certainty ([halpern-2003]); Hamblin's account validates I1, I2 and its own collapse I3, and
Conjunctivitis; the probability space account validates V1–V12 and none of I1–I3 or E1.

## Implementation notes

* Each account is a likelihood relation on `Set W` registered with the comparative
  probability mixins, so V1–V5 and (where valid) V8–V12 come from
  `Logic/ComparativeProbability/Patterns` by instance resolution; V6 and V7 take each
  account's own modals, [kratzer-1991]'s human necessity and possibility for the relative
  likelihood account and, for the other two, the quantifiers over the epistemic space
  (`A = Set.univ` and `A.Nonempty`, simple necessity and possibility over the empty base), and
  V8–V10 take Kratzer's restricted necessity or, for the probability space, entailment.
* The refutations are the paper's: the two tied worlds of footnote 8's limit-assumption
  variant against V11, the coin against I1 and I2, the twelve-sided die against E1.
* Two of the paper's verdicts do not survive formalization. Complement transfer V12, which
  the paper counts among Kratzer's failures alongside V11, holds for the lift of every
  preorder (`kratzer_V12`): footnote 8's countermodel refutes only V11. And Hamblin's
  account, which the paper credits with V11, refutes it (`hamblin_refutes_V11`): a
  proposition can be as possible as a probable one while its complement is also fully
  possible. The paper's claim that Kratzer's account does not validate Conjunctivitis is
  confirmed by a four-world countermodel with two incomparable tied pairs
  (`kratzer_refutes_E1`).
* Section numbers and example labels follow the author's June 2010 draft, the copy attached
  in Zotero, and are unverified against the Philosophy Compass pagination.

## References

* [yalcin-2010]
* [kratzer-1991]
* [lewis-1973]
* [hamblin-1959]
* [halpern-2003]
-/

@[expose] public section

namespace Yalcin2010

open ComparativeProbability Modality

/-! ### §3: the relative likelihood approach

The ordering source `O` induces the preorder `v ≤[O] u`, `v` at least as high as `u`
(`Modality.atLeastAsGoodAs`); the comparative is [lewis-1973]'s lift of it. -/

section Kratzer

variable {W : Type*} (O : List (W → Prop))

instance : IsPreorder W (atLeastAsGoodAs O) where
  refl := atLeastAsGoodAs_refl O
  trans _ _ _ := atLeastAsGoodAs_trans

/-- Kratzer's *at least as likely as*: every world of the second proposition is matched by an
at least as high world of the first. -/
abbrev likelihood : Set W → Set W → Prop := LewisLift (atLeastAsGoodAs O)

/-- Epistemic *must* at `w`: [kratzer-1991]'s human necessity over the whole space. -/
def must (A : Set W) (w : W) : Prop :=
  humanNecessity emptyBackground (fun _ ↦ O) (· ∈ A) w

/-- Epistemic *might* at `w`: human possibility, the dual of `must`. -/
def might (A : Set W) (w : W) : Prop :=
  humanPossibility emptyBackground (fun _ ↦ O) (· ∈ A) w

/-- The indicative *if A, B* with its tacit *must*: human necessity over the base restricted
by the antecedent, Kratzer's restrictor analysis. -/
def ifThen (A B : Set W) (w : W) : Prop :=
  humanNecessity (ModalBase.restrict emptyBackground (· ∈ A)) (fun _ ↦ O) (· ∈ B) w

theorem must_iff (A : Set W) (w : W) :
    must O A w ↔ ∀ u, ∃ v, (v ≤[O] u) ∧ ∀ z, (z ≤[O] v) → z ∈ A := by
  simp [must, humanNecessity, accessibleWorlds_emptyBackground]

theorem ifThen_iff (A B : Set W) (w : W) :
    ifThen O A B w ↔
      ∀ u ∈ A, ∃ v ∈ A, (v ≤[O] u) ∧ ∀ z ∈ A, (z ≤[O] v) → z ∈ B := by
  simp only [ifThen, humanNecessity, mem_accessibleWorlds_restrict,
    accessibleWorlds_emptyBackground, Set.mem_univ, true_and]

theorem kratzer_V1 : ProbablyToNotProbablyNot (likelihood O) := probablyToNotProbablyNot
theorem kratzer_V2 : ProbablyDistribInf (likelihood O) := probablyDistribInf_of
theorem kratzer_V3 : ChancyDisjunctionIntro (likelihood O) := chancyDisjunctionIntro_of
theorem kratzer_V4 : Minimality (likelihood O) := minimality_of
theorem kratzer_V5 : Maximality (likelihood O) := maximality_of

/-- V6 for Kratzer's modals: a necessary proposition is probable, since its complement is
dominated by the witnesses of necessity and cannot dominate them. -/
theorem kratzer_V6 [Nonempty W] (w : W) : MustToProbably (likelihood O) (must O · w) := by
  intro A hA
  rw [must_iff] at hA
  refine ⟨fun u _ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨v, hvu, hv⟩ := hA u
    exact ⟨v, hv v (atLeastAsGoodAs_refl O v), hvu⟩
  · obtain ⟨w₀⟩ := ‹Nonempty W›
    obtain ⟨v, -, hv⟩ := hA w₀
    obtain ⟨u, hu, huv⟩ := h (hv v (atLeastAsGoodAs_refl O v))
    exact hu (hv u huv)

/-- V7 for Kratzer's modals, from V6 and V1. -/
theorem kratzer_V7 [Nonempty W] (w : W) : ProbablyToMight (likelihood O) (might O · w) :=
  fun A hA hmust ↦ probablyToNotProbablyNot A hA (kratzer_V6 O w Aᶜ hmust)

/-- V10 for the restricted necessity: the antecedent's worlds are matched by the witnesses,
which are consequent worlds. -/
theorem kratzer_V10 (w : W) : ConditionalToComparative (likelihood O) (ifThen O · · w) := by
  intro A B hAB u hu
  obtain ⟨v, hvA, hvu, hall⟩ := (ifThen_iff O A B w).1 hAB u hu
  exact ⟨v, hall v hvA (atLeastAsGoodAs_refl O v), hvu⟩

/-- V8 for the restricted necessity: a world outside the consequent is dominated through the
antecedent, and a consequent world undominated by the complement is found above the
antecedent world the probability of the antecedent leaves undominated. -/
theorem kratzer_V8 (w : W) : ChancyModusPonens (likelihood O) (ifThen O · · w) := by
  intro A B hAB ⟨hA, hAnot⟩
  rw [ifThen_iff] at hAB
  refine ⟨fun u hu ↦ ?_, fun h ↦ ?_⟩
  · by_cases huA : u ∈ A
    · obtain ⟨v, hvA, hvu, hall⟩ := hAB u huA
      exact ⟨v, hall v hvA (atLeastAsGoodAs_refl O v), hvu⟩
    · obtain ⟨a, ha, hau⟩ := hA huA
      obtain ⟨v, hvA, hva, hall⟩ := hAB a ha
      exact ⟨v, hall v hvA (atLeastAsGoodAs_refl O v), atLeastAsGoodAs_trans hva hau⟩
  · apply hAnot
    by_contra hcon
    have hex : ∃ a ∈ A, ∀ u ∈ Aᶜ, ¬(u ≤[O] a) := by
      by_contra hall
      push Not at hall
      exact hcon fun a ha ↦ hall a ha
    obtain ⟨a, ha, hnone⟩ := hex
    obtain ⟨v, hvA, hva, hall⟩ := hAB a ha
    obtain ⟨u, hu, huv⟩ := h (hall v hvA (atLeastAsGoodAs_refl O v))
    have huA : u ∈ A := by
      by_contra huA
      exact hnone u huA (atLeastAsGoodAs_trans huv hva)
    exact hu (hall u huA huv)

/-- V9 for the restricted necessity, the contrapositive of V8. -/
theorem kratzer_V9 (w : W) : ChancyModusTollens (likelihood O) (ifThen O · · w) :=
  fun A B hAB hB hA ↦ hB (kratzer_V8 O w A B hAB hA)

/-- Complement transfer holds for the lift of every preorder: a world of `Bᶜ` outside `A` is
dominated through `A` and then through `B`. The paper lists V12 with V11 among Kratzer's
failures; its footnote 8 countermodel refutes only V11. -/
theorem kratzer_V12 : ComplementTransfer (likelihood O) := by
  intro A B hBA hA y hy
  by_cases hyA : y ∈ A
  · exact hBA hyA
  · obtain ⟨a, ha, hay⟩ := hA hyA
    obtain ⟨b, hb, hba⟩ := hBA ha
    exact ⟨b, hb, atLeastAsGoodAs_trans hba hay⟩

/-- The union property I1 is the lift's right-union closure ([halpern-2003]). -/
theorem kratzer_I1 : RightUnion (likelihood O) := rightUnion_lewisLift

/-- I2, the collapse of equiprobability into certainty. -/
theorem kratzer_I2 : EquiprobabilityCollapse (likelihood O) := fun A B hA ↦
  (rightUnion_lewisLift A A Aᶜ (refl_of _ A) hA).anti_right
    (by show B ⊆ A ∪ Aᶜ; rw [Set.union_compl_self]; exact Set.subset_univ B)

end Kratzer

/-- Footnote 8, the limit-assumption variant: with two tied maximal worlds, the empty ordering
source, `p` the whole space and `q` one world, `p` is probable and `q` as likely as `p`, but
`q` is not probable, since its complement is as high as it. -/
theorem kratzer_refutes_V11 : ¬PositiveFormTransfer (likelihood ([] : List (Fin 2 → Prop))) := by
  intro h
  have hA : Probably (likelihood ([] : List (Fin 2 → Prop))) Set.univ := by
    rw [Probably, Strict, Set.compl_univ]
    exact ⟨lewisLift_empty _,
      fun h ↦ Set.univ_nonempty.ne_empty (lewisLift_empty_left_iff.1 h)⟩
  exact (h Set.univ {0} (fun _ _ ↦ ⟨0, rfl, atLeastAsGoodAs_nil _ _⟩) hA).2
    fun _ _ ↦ ⟨1, by simp, atLeastAsGoodAs_nil _ _⟩

/-- Two incomparable tied pairs of worlds: `{0, 2, 3}` and `{1, 2, 3}` are each probable, since
the one world each lacks is tied with a world it has, but their conjunction `{2, 3}` is not,
since it dominates neither `0` nor `1`. So Kratzer's account does not validate
Conjunctivitis, as the paper says. -/
theorem kratzer_refutes_E1 :
    ¬Conjunctivitis (likelihood [(· ∈ ({0, 1} : Set (Fin 4))), (· ∈ ({2, 3} : Set (Fin 4)))]) := by
  intro h
  have hle : ∀ v u : Fin 4, (v ≤[[(· ∈ ({0, 1} : Set (Fin 4))), (· ∈ ({2, 3} : Set (Fin 4)))]] u)
      ↔ (u ∈ ({0, 1} : Set (Fin 4)) → v ∈ ({0, 1} : Set (Fin 4))) ∧
        (u ∈ ({2, 3} : Set (Fin 4)) → v ∈ ({2, 3} : Set (Fin 4))) := fun v u ↦ by
    simp [atLeastAsGoodAs_iff]
  have hφ : Probably (likelihood [(· ∈ ({0, 1} : Set (Fin 4))), (· ∈ ({2, 3} : Set (Fin 4)))])
      {0, 2, 3} := by
    refine ⟨fun u hu ↦ ⟨0, by simp, ?_⟩, fun hc ↦ ?_⟩
    · simp only [Set.mem_ofPred_eq]
      rw [hle]
      have : u = 1 := by
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu
        omega
      subst this; simp
    · obtain ⟨u, hu, hu2⟩ := @hc 2 (by simp)
      simp only [Set.mem_ofPred_eq] at hu2
      rw [hle] at hu2
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu
      have : u = 1 := by omega
      subst this; simp at hu2
  have hψ : Probably (likelihood [(· ∈ ({0, 1} : Set (Fin 4))), (· ∈ ({2, 3} : Set (Fin 4)))])
      {1, 2, 3} := by
    refine ⟨fun u hu ↦ ⟨1, by simp, ?_⟩, fun hc ↦ ?_⟩
    · simp only [Set.mem_ofPred_eq]
      rw [hle]
      have : u = 0 := by
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu
        omega
      subst this; simp
    · obtain ⟨u, hu, hu2⟩ := @hc 2 (by simp)
      simp only [Set.mem_ofPred_eq] at hu2
      rw [hle] at hu2
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu
      have : u = 0 := by omega
      subst this; simp at hu2
  have hinter : ({0, 2, 3} : Set (Fin 4)) ∩ {1, 2, 3} = {2, 3} := by
    ext x; fin_cases x <;> simp
  have := (h _ _ hφ hψ).1
  simp only [Set.inf_eq_inter, hinter] at this
  obtain ⟨a, ha, ha0⟩ := @this 0 (by simp)
  simp only [Set.mem_ofPred_eq] at ha0
  rw [hle] at ha0
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl <;> simp at ha0

/-! ### §4: the possibility space approach -/

section Hamblin

variable {W : Type*} [Fintype W]

/-- [hamblin-1959]'s plausibility, a possibility measure on a finite epistemic space, given by
its values on worlds: at most `1`, with `1` attained, so that the measure of the whole space
is `1` and every proposition or its complement is fully possible. -/
structure Possibility (W : Type*) where
  /-- The possibility of a world. -/
  poss : W → ℚ≥0
  le_one : ∀ w, poss w ≤ 1
  exists_eq_one : ∃ w, poss w = 1

namespace Possibility

variable (m : Possibility W)

open scoped Classical in
/-- The possibility of a proposition: the greatest possibility of its worlds. -/
noncomputable def measure (A : Set W) : ℚ≥0 := (Finset.univ.filter (· ∈ A)).sup m.poss

theorem measure_le_one (A : Set W) : m.measure A ≤ 1 :=
  Finset.sup_le fun v _ ↦ m.le_one v

theorem measure_eq_one_iff (A : Set W) : m.measure A = 1 ↔ ∃ w ∈ A, m.poss w = 1 := by
  classical
  constructor
  · intro h
    by_cases hA : (Finset.univ.filter (· ∈ A)).Nonempty
    · obtain ⟨w, hw, hsup⟩ := Finset.exists_mem_eq_sup' hA m.poss
      refine ⟨w, (Finset.mem_filter.1 hw).2, ?_⟩
      rw [← hsup, Finset.sup'_eq_sup hA]
      exact h
    · rw [Finset.not_nonempty_iff_eq_empty] at hA
      simp [measure, hA, bot_eq_zero] at h
  · rintro ⟨w, hw, hw1⟩
    refine le_antisymm (m.measure_le_one A) ?_
    rw [← hw1]
    exact Finset.le_sup (f := m.poss) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hw⟩)

theorem measure_mono {A B : Set W} (h : A ⊆ B) : m.measure A ≤ m.measure B := by
  classical
  exact Finset.sup_mono fun x hx ↦
    Finset.mem_filter.2 ⟨Finset.mem_univ _, h (Finset.mem_filter.1 hx).2⟩

theorem measure_empty : m.measure ∅ = 0 := by simp [measure, bot_eq_zero]

theorem measure_univ : m.measure Set.univ = 1 :=
  (m.measure_eq_one_iff _).2 (let ⟨w, hw⟩ := m.exists_eq_one; ⟨w, Set.mem_univ w, hw⟩)

theorem measure_singleton (w : W) : m.measure {w} = m.poss w := by
  classical
  rw [measure, show Finset.univ.filter (· ∈ ({w} : Set W)) = {w} by ext; simp,
    Finset.sup_singleton]

/-- The measure of a union is the greater measure. -/
theorem measure_union (A B : Set W) : m.measure (A ∪ B) = m.measure A ⊔ m.measure B := by
  classical
  simp only [measure]
  rw [← Finset.sup_union]
  congr 1
  ext; simp

/-- Every proposition or its complement is fully possible. -/
theorem measure_eq_one_or_compl (A : Set W) : m.measure A = 1 ∨ m.measure Aᶜ = 1 := by
  have h := m.measure_union A Aᶜ
  rw [Set.union_compl_self, m.measure_univ] at h
  rcases le_total (m.measure A) (m.measure Aᶜ) with hle | hle
  · exact Or.inr (by rw [sup_eq_right.2 hle] at h; exact h.symm)
  · exact Or.inl (by rw [sup_eq_left.2 hle] at h; exact h.symm)

/-- Hamblin's *at least as likely as*: at least as possible. -/
def likelihood (A B : Set W) : Prop := m.measure B ≤ m.measure A

instance : IsLikelihoodMono m.likelihood := ⟨fun _ _ h ↦ m.measure_mono h⟩
instance : IsTrans (Set W) m.likelihood := ⟨fun _ _ _ hab hbc ↦ le_trans hbc hab⟩
instance : Std.Refl m.likelihood := ⟨fun _ ↦ le_rfl⟩

/-- A probable proposition is fully possible and its complement is not. -/
theorem measure_eq_one_of_probably {A : Set W} (h : Probably m.likelihood A) :
    m.measure A = 1 ∧ m.measure Aᶜ < 1 := by
  obtain ⟨hle, hnot⟩ := h
  have hlt : m.measure Aᶜ < m.measure A := lt_of_le_not_ge hle hnot
  rcases m.measure_eq_one_or_compl A with h1 | h1
  · exact ⟨h1, h1 ▸ hlt⟩
  · exact absurd (h1 ▸ hlt) (not_lt.2 (m.measure_le_one A))

theorem hamblin_V1 : ProbablyToNotProbablyNot m.likelihood := probablyToNotProbablyNot
theorem hamblin_V2 : ProbablyDistribInf m.likelihood := probablyDistribInf_of
theorem hamblin_V3 : ChancyDisjunctionIntro m.likelihood := chancyDisjunctionIntro_of
theorem hamblin_V4 : Minimality m.likelihood := minimality_of
theorem hamblin_V5 : Maximality m.likelihood := maximality_of

/-- V6 with the quantificational *must* of §4, simple necessity over the whole space. -/
theorem hamblin_V6 : MustToProbably m.likelihood (· = Set.univ) := by
  rintro A rfl
  rw [Probably, Strict, likelihood, likelihood, Set.compl_univ, m.measure_univ, m.measure_empty]
  exact ⟨zero_le_one, fun h ↦ absurd h (not_le.2 zero_lt_one)⟩

/-- V7 with the quantificational *might*, simple possibility over the whole space. -/
theorem hamblin_V7 : ProbablyToMight m.likelihood Set.Nonempty := by
  intro A hA
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  subst hne
  have := (m.measure_eq_one_of_probably hA).2
  rw [Set.compl_empty, m.measure_univ] at this
  exact lt_irrefl _ this

/-- V12: the more likely of two fully possible propositions is fully possible. -/
theorem hamblin_V12 : ComplementTransfer m.likelihood := by
  intro A B hBA hA
  have h1 : m.measure A = 1 := by
    rcases m.measure_eq_one_or_compl A with h | h
    · exact h
    · exact le_antisymm (m.measure_le_one A) (h ▸ hA)
  show m.measure Bᶜ ≤ m.measure B
  exact (m.measure_le_one Bᶜ).trans (h1 ▸ hBA)

/-- Conjunctivitis holds: the fully possible worlds of two probable propositions lie in both,
and the complement of the conjunction is the join of two complements below `1`. -/
theorem hamblin_E1 : Conjunctivitis m.likelihood := by
  intro A B hA hB
  obtain ⟨hA1, hAc⟩ := m.measure_eq_one_of_probably hA
  obtain ⟨hB1, hBc⟩ := m.measure_eq_one_of_probably hB
  obtain ⟨w, hwA, hw⟩ := (m.measure_eq_one_iff A).1 hA1
  have hwB : w ∈ B := by
    by_contra hwB
    have := m.measure_mono (Set.singleton_subset_iff.2 (Set.mem_compl hwB))
    rw [m.measure_singleton, hw] at this
    exact absurd (this.trans_lt hBc) (lt_irrefl _)
  have hAB : m.measure (A ⊓ B) = 1 :=
    (m.measure_eq_one_iff _).2 ⟨w, ⟨hwA, hwB⟩, hw⟩
  have hABc : m.measure (A ⊓ B)ᶜ < 1 := by
    show m.measure (A ∩ B)ᶜ < 1
    rw [Set.compl_inter, m.measure_union]
    exact max_lt hAc hBc
  exact ⟨by rw [likelihood, hAB]; exact m.measure_le_one _,
    fun h ↦ absurd (hAB ▸ h) (not_le.2 hABc)⟩

/-- I1, the union property, since the measure of a union is the greater measure. -/
theorem hamblin_I1 : RightUnion m.likelihood := fun A B C hAB hAC ↦ by
  show m.measure (B ∪ C) ≤ m.measure A
  rw [m.measure_union]; exact max_le hAB hAC

/-- I2: a proposition at least as possible as its complement is fully possible. -/
theorem hamblin_I2 : EquiprobabilityCollapse m.likelihood := fun A B hA ↦ by
  have h1 : m.measure A = 1 := by
    rcases m.measure_eq_one_or_compl A with h | h
    · exact h
    · exact le_antisymm (m.measure_le_one A) (h ▸ hA)
  show m.measure B ≤ m.measure A
  exact h1 ▸ m.measure_le_one B

/-- I3, Hamblin's collapse: a probable proposition is at least as possible as any. -/
theorem hamblin_I3 : HamblinCollapse m.likelihood := fun A B hA ↦ hamblin_I2 m A B hA.1

end Possibility

/-- Three worlds, the first two fully possible and the third half possible: `{0, 1}` is
probable, `{0, 2}` is as possible as it, yet `{0, 2}` is not probable, since its complement
`{1}` is fully possible. The paper credits Hamblin's account with positive form transfer;
it fails. -/
def threeWorlds : Possibility (Fin 3) :=
  ⟨![1, 1, 1 / 2], fun w ↦ by fin_cases w <;> norm_num, ⟨0, rfl⟩⟩

theorem hamblin_refutes_V11 : ¬PositiveFormTransfer threeWorlds.likelihood := by
  intro h
  have hpair : ∀ a b : Fin 3, threeWorlds.measure {a, b} =
      threeWorlds.poss a ⊔ threeWorlds.poss b := fun a b ↦ by
    rw [Set.insert_eq, Possibility.measure_union, Possibility.measure_singleton,
      Possibility.measure_singleton]
  have hc01 : ({0, 1} : Set (Fin 3))ᶜ = {2} := by ext x; fin_cases x <;> simp
  have hc02 : ({0, 2} : Set (Fin 3))ᶜ = {1} := by ext x; fin_cases x <;> simp
  have half_lt : (1 / 2 : ℚ≥0) < 1 := by rw [← NNRat.coe_lt_coe]; push_cast; norm_num
  have h0 : threeWorlds.poss 0 = 1 := rfl
  have h1 : threeWorlds.poss 1 = 1 := rfl
  have h2 : threeWorlds.poss 2 = 1 / 2 := rfl
  have m01 : threeWorlds.measure {0, 1} = 1 := by rw [hpair, h0, h1, sup_idem]
  have m02 : threeWorlds.measure {0, 2} = 1 := by rw [hpair, h0, h2, sup_eq_left.2 half_lt.le]
  have m2 : threeWorlds.measure {2} = 1 / 2 := by rw [Possibility.measure_singleton, h2]
  have m1 : threeWorlds.measure {1} = 1 := by rw [Possibility.measure_singleton, h1]
  have hA : Probably threeWorlds.likelihood {0, 1} := by
    refine ⟨?_, fun h ↦ ?_⟩
    · show threeWorlds.measure ({0, 1} : Set (Fin 3))ᶜ ≤ threeWorlds.measure {0, 1}
      rw [hc01, m2, m01]; exact half_lt.le
    · have : threeWorlds.measure {0, 1} ≤ threeWorlds.measure ({0, 1} : Set (Fin 3))ᶜ := h
      rw [hc01, m2, m01] at this
      exact absurd this (not_le.2 half_lt)
  have hBA : threeWorlds.likelihood {0, 2} {0, 1} := by
    show threeWorlds.measure {0, 1} ≤ threeWorlds.measure {0, 2}
    rw [m01, m02]
  apply (h _ _ hBA hA).2
  show threeWorlds.measure {0, 2} ≤ threeWorlds.measure ({0, 2} : Set (Fin 3))ᶜ
  rw [hc02, m1, m02]

end Hamblin

/-! ### §5: semantics with probability spaces -/

section Probability

variable {W : Type*} (P : FinAddMeasure ℚ W)

theorem prob_V1 : ProbablyToNotProbablyNot P.inducedGe := probablyToNotProbablyNot
theorem prob_V2 : ProbablyDistribInf P.inducedGe := probablyDistribInf_of
theorem prob_V3 : ChancyDisjunctionIntro P.inducedGe := chancyDisjunctionIntro_of
theorem prob_V4 : Minimality P.inducedGe := minimality_of
theorem prob_V5 : Maximality P.inducedGe := maximality_of

/-- V6 with the quantificational *must*: the whole space has probability one. -/
theorem prob_V6 : MustToProbably P.inducedGe (· = Set.univ) := by
  rintro A rfl
  simp only [Probably, Strict, FinAddMeasure.inducedGe, Set.compl_univ, P.total, P.mu_empty]
  norm_num

/-- V7 with the quantificational *might*: the empty proposition is not probable. -/
theorem prob_V7 : ProbablyToMight P.inducedGe Set.Nonempty := by
  intro A hA
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  subst hne
  simp only [Probably, Strict, FinAddMeasure.inducedGe, Set.compl_empty, P.total,
    P.mu_empty] at hA
  norm_num at hA

theorem prob_V8 : ChancyModusPonens P.inducedGe (· ⊆ ·) := chancyModusPonens_of
theorem prob_V9 : ChancyModusTollens P.inducedGe (· ⊆ ·) := chancyModusTollens_of
theorem prob_V10 : ConditionalToComparative P.inducedGe (· ⊆ ·) := conditionalToComparative_of
theorem prob_V11 : PositiveFormTransfer P.inducedGe := positiveFormTransfer_of
theorem prob_V12 : ComplementTransfer P.inducedGe := complementTransfer_of

end Probability

/-- The fair coin: heads is at least as likely as tails and as heads, but not as heads or
tails, refuting the union property I1, and heads is as likely as its complement without
being as likely as everything, refuting I2. -/
theorem prob_refutes_I1_I2 :
    ¬RightUnion (FinAddMeasure.uniform (K := ℚ) (Fin 2)).inducedGe ∧
      ¬EquiprobabilityCollapse (FinAddMeasure.uniform (K := ℚ) (Fin 2)).inducedGe := by
  have h0 : (FinAddMeasure.uniform (K := ℚ) (Fin 2)) {0} = 1 / 2 := by simp
  have h1 : (FinAddMeasure.uniform (K := ℚ) (Fin 2)) {1} = 1 / 2 := by simp
  have hc : ({0} : Set (Fin 2))ᶜ = {1} := by ext x; fin_cases x <;> simp
  have hu : ({1} : Set (Fin 2)) ∪ {0} = Set.univ := by ext x; fin_cases x <;> simp
  constructor
  · intro h
    have := h {0} {1} {0} (by simp [FinAddMeasure.inducedGe, h0, h1])
      (by simp [FinAddMeasure.inducedGe])
    simp only [FinAddMeasure.inducedGe, Set.sup_eq_union, hu, FinAddMeasure.total, h0] at this
    norm_num at this
  · intro h
    have := h {0} Set.univ (by simp [FinAddMeasure.inducedGe, hc, h0, h1])
    simp only [FinAddMeasure.inducedGe, FinAddMeasure.total, h0] at this
    norm_num at this

/-- Three equiprobable worlds: `{0, 1}` is probable but not as likely as everything, refuting
Hamblin's collapse I3. -/
theorem prob_refutes_I3 : ¬HamblinCollapse (FinAddMeasure.uniform (K := ℚ) (Fin 3)).inducedGe := by
  intro h
  have hA : (FinAddMeasure.uniform (K := ℚ) (Fin 3)) {0, 1} = 2 / 3 := by
    rw [FinAddMeasure.uniform_apply, Set.ncard_pair (by decide)]; norm_num
  have hc : ({0, 1} : Set (Fin 3))ᶜ = {2} := by ext x; fin_cases x <;> simp
  have hAc : (FinAddMeasure.uniform (K := ℚ) (Fin 3)) ({0, 1} : Set (Fin 3))ᶜ = 1 / 3 := by
    rw [hc, FinAddMeasure.uniform_singleton]; norm_num
  have := h {0, 1} Set.univ ⟨by simp [FinAddMeasure.inducedGe, hA, hAc]; norm_num,
    by simp [FinAddMeasure.inducedGe, hA, hAc]; norm_num⟩
  simp only [FinAddMeasure.inducedGe, FinAddMeasure.total, hA] at this
  norm_num at this

/-- The twelve-sided die of §4: a number below nine and a number above four are each probable,
eight faces of twelve, but a number above four and below nine is not, four faces. Conjunctivitis
fails for the probability space semantics. -/
theorem prob_refutes_E1 : ¬Conjunctivitis (FinAddMeasure.uniform (K := ℚ) (Fin 12)).inducedGe := by
  intro h
  have hval : ∀ A : Set (Fin 12), (FinAddMeasure.uniform (K := ℚ) (Fin 12)) A = A.ncard / 12 :=
    fun A ↦ by rw [FinAddMeasure.uniform_apply]; simp
  have hprob : ∀ A : Set (Fin 12), 6 < A.ncard → A.ncard + Aᶜ.ncard = 12 →
      Probably (FinAddMeasure.uniform (K := ℚ) (Fin 12)).inducedGe A := fun A hA hsum ↦ by
    constructor <;> simp only [FinAddMeasure.inducedGe, hval] <;>
      [skip; intro hle] <;>
      (have : (A.ncard : ℚ) + Aᶜ.ncard = 12 := by exact_mod_cast hsum) <;>
      (have : (6 : ℚ) < A.ncard := by exact_mod_cast hA) <;>
      linarith
  have hcard : ∀ A : Set (Fin 12), A.ncard + Aᶜ.ncard = 12 := fun A ↦ by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hlow : ({n : Fin 12 | n.val < 8} : Set (Fin 12)).ncard = 8 := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]; decide
  have hhigh : ({n : Fin 12 | 4 ≤ n.val} : Set (Fin 12)).ncard = 8 := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]; decide
  have hint : ({n : Fin 12 | n.val < 8} ⊓ {n : Fin 12 | 4 ≤ n.val} : Set (Fin 12)) =
      {n : Fin 12 | 4 ≤ n.val ∧ n.val < 8} := by
    ext n; simp [and_comm]
  have hmid : ({n : Fin 12 | n.val < 8} ⊓ {n : Fin 12 | 4 ≤ n.val} : Set (Fin 12)).ncard = 4 := by
    rw [hint, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]; decide
  have hmidc : ({n : Fin 12 | n.val < 8} ⊓ {n : Fin 12 | 4 ≤ n.val} : Set (Fin 12))ᶜ.ncard = 8 := by
    have := hcard ({n : Fin 12 | n.val < 8} ⊓ {n : Fin 12 | 4 ≤ n.val})
    omega
  have := (h _ _ (hprob _ (by rw [hlow]; norm_num) (hcard _))
    (hprob _ (by rw [hhigh]; norm_num) (hcard _))).2
  apply this
  simp only [FinAddMeasure.inducedGe, hval, hmid, hmidc]
  norm_num

/-! ### §6: scales

*Probably* as a relative adjective compares the probability with a contextual threshold
`n`; V1 survives exactly the thresholds at or above one half. -/

section Threshold

variable {W : Type*} (P : FinAddMeasure ℚ W)

/-- *Probably* with threshold `n`: `Pr(A) > n`, the strict form of the positive-form threshold
semantics `EpistemicThreshold.meetsThreshold` (which reads `≥`). -/
def probablyAt (n : ℚ) (A : Set W) : Prop := n < P A

/-- With a threshold of at least one half, a proposition and its complement are not both
probable. -/
theorem probablyAt_V1 {n : ℚ} (hn : 1 / 2 ≤ n) (A : Set W) :
    probablyAt P n A → ¬probablyAt P n Aᶜ := by
  intro hA hAc
  have := P.mu_compl A
  simp only [probablyAt] at hA hAc
  linarith

end Threshold

/-- Below one half the pattern fails: with the threshold one third, the fair coin's heads and
tails are both probable. -/
theorem probablyAt_refutes_V1 :
    probablyAt (FinAddMeasure.uniform (K := ℚ) (Fin 2)) (1 / 3) {0} ∧
      probablyAt (FinAddMeasure.uniform (K := ℚ) (Fin 2)) (1 / 3) ({0} : Set (Fin 2))ᶜ := by
  have hc : ({0} : Set (Fin 2))ᶜ = {1} := by ext x; fin_cases x <;> simp
  simp only [probablyAt, hc, FinAddMeasure.uniform_singleton, Fintype.card_fin]
  norm_num

end Yalcin2010
