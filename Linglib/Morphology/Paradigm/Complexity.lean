import Linglib.Morphology.Paradigm.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Paradigm complexity: implicative structure and entropy over cells

This file defines the two faces of the paradigm cell filling problem over a `ParadigmSystem`.
The qualitative face is categorical: a set of cells *predicts* another when the forms filling it
determine the form filling the target across the inflection classes, a *principal-part set*
predicts every cell, and a system is *vocabularly clear* when every single cell does. The
quantitative face measures the same relations by entropy: the entropy of the class assignment, of
the form distribution at a cell, and the conditional entropy of one cell given another — the
integrand of average conditional entropy. The two faces meet at zero: a cell predicted by another
has zero conditional entropy given it, so a vocabularly clear system is transparent. Enumerative
complexity is counted by the realizations of each cell, whose product bounds the number of
classes.

## Main definitions

* `ParadigmSystem.Predicts`, `ParadigmSystem.IsPrincipalPartSet`,
  `ParadigmSystem.IsVocabularClear`: the implicative relations.
* `ParadigmSystem.realizations`, `ParadigmSystem.maxRealizations`,
  `ParadigmSystem.ParadigmEconomy`: enumerative counts and the paradigm economy principle.
* `ParadigmSystem.declensionEntropy`, `ParadigmSystem.cellEntropy`,
  `ParadigmSystem.conditionalCellEntropy`: entropies in nats, from the class weights.
* `ParadigmSystem.IsImplicative`, `ParadigmSystem.IsTransparent`: zero conditional entropy.

## Main statements

* `ParadigmSystem.conditionalCellEntropy_eq_zero_of_predicts`,
  `ParadigmSystem.isTransparent_of_isVocabularClear`: prediction is zero conditional entropy.
* `ParadigmSystem.cellEntropy_eq_zero_of_card_le_one`: a cell with one realization has zero
  entropy.
* `ParadigmSystem.card_paradigms_le_prod_card_realizations`: classes are bounded by the product
  of realizations.

## References

* [ackerman-malouf-2013]
* [bonami-beniamine-2016]
* [carstairs-mccarthy-2010]
-/

namespace Morphology

namespace ParadigmSystem

variable {n : ℕ} {Form : Type*} (ps : ParadigmSystem n Form)

/-! ### Implicative structure -/

/-- A set of cells `S` predicts cell `j` when any two classes agreeing on every cell of `S`
agree at `j`. -/
def Predicts (S : Finset (Fin n)) (j : Fin n) : Prop :=
  ∀ p ∈ ps.entries, ∀ q ∈ ps.entries, (∀ c ∈ S, p.1 c = q.1 c) → p.1 j = q.1 j

/-- A principal-part set predicts every cell. -/
def IsPrincipalPartSet (S : Finset (Fin n)) : Prop := ∀ j, ps.Predicts S j

/-- Vocabular clarity: every cell on its own predicts every cell — each realization identifies
the class. -/
def IsVocabularClear : Prop := ∀ c, ps.IsPrincipalPartSet {c}

variable {ps}

theorem Predicts.mono {S T : Finset (Fin n)} {j : Fin n} (hST : S ⊆ T) (h : ps.Predicts S j) :
    ps.Predicts T j :=
  fun p hp q hq hag => h p hp q hq fun c hc => hag c (hST hc)

theorem predicts_of_mem {S : Finset (Fin n)} {j : Fin n} (hj : j ∈ S) : ps.Predicts S j :=
  fun _ _ _ _ hag => hag j hj

variable (ps) [DecidableEq Form]

instance {S : Finset (Fin n)} {j : Fin n} : Decidable (ps.Predicts S j) :=
  inferInstanceAs (Decidable (∀ p ∈ ps.entries, ∀ q ∈ ps.entries, _ → _))

instance {S : Finset (Fin n)} : Decidable (ps.IsPrincipalPartSet S) :=
  inferInstanceAs (Decidable (∀ j, ps.Predicts S j))

instance : Decidable ps.IsVocabularClear :=
  inferInstanceAs (Decidable (∀ c, ps.IsPrincipalPartSet {c}))

/-! ### Enumerative counts -/

/-- The forms realizing cell `c`. -/
def realizations (c : Fin n) : Finset Form := (ps.entries.map fun e => e.1 c).toFinset

theorem mem_realizations {c : Fin n} {r : Form} :
    r ∈ ps.realizations c ↔ ∃ e ∈ ps.entries, e.1 c = r := by
  simp [realizations]

/-- The largest number of rival realizations of a single cell. -/
def maxRealizations : ℕ := Finset.univ.sup fun c => (ps.realizations c).card

/-- Paradigm economy: no more classes than rival realizations of the most varied cell. -/
def ParadigmEconomy : Prop := ps.eComplexity ≤ ps.maxRealizations

instance : Decidable ps.ParadigmEconomy := inferInstanceAs (Decidable (_ ≤ _))

/-- The distinct paradigms of the system are bounded by the product of the realizations of the
cells. -/
theorem card_paradigms_le_prod_card_realizations :
    (ps.entries.map Prod.fst).toFinset.card ≤ ∏ c, (ps.realizations c).card := by
  rw [← Fintype.card_piFinset]
  refine Finset.card_le_card_of_injOn id (fun p hp => ?_) (Set.injOn_id _)
  simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map] at hp
  obtain ⟨e, he, rfl⟩ := hp
  exact Finset.mem_coe.2 (Fintype.mem_piFinset.2 fun c => ps.mem_realizations.2 ⟨e, he, rfl⟩)

/-! ### Entropy -/

/-- The total weight of the classes. -/
def total : ℚ := (ps.entries.map Prod.snd).sum

/-- The weight of the classes realizing `r` at `c`. -/
def cellWeight (c : Fin n) (r : Form) : ℚ :=
  ((ps.entries.filter fun e => e.1 c = r).map Prod.snd).sum

/-- The weight of the classes realizing `ri` at `ci` and `rj` at `cj`. -/
def jointWeight (ci cj : Fin n) (ri rj : Form) : ℚ :=
  ((ps.entries.filter fun e => e.1 ci = ri ∧ e.1 cj = rj).map Prod.snd).sum

/-- The pairs of forms realized at a pair of cells. -/
def jointRealizations (ci cj : Fin n) : Finset (Form × Form) :=
  (ps.entries.map fun e => (e.1 ci, e.1 cj)).toFinset

theorem mem_jointRealizations {ci cj : Fin n} {p : Form × Form} :
    p ∈ ps.jointRealizations ci cj ↔ ∃ e ∈ ps.entries, (e.1 ci, e.1 cj) = p := by
  simp [jointRealizations]

/-- The entropy (in nats) of the class assignment. -/
noncomputable def declensionEntropy : ℝ :=
  (ps.entries.map fun e => Real.negMulLog ((e.2 / ps.total : ℚ) : ℝ)).sum

/-- The entropy (in nats) of the form distribution at cell `c`. -/
noncomputable def cellEntropy (c : Fin n) : ℝ :=
  ∑ r ∈ ps.realizations c, Real.negMulLog ((ps.cellWeight c r / ps.total : ℚ) : ℝ)

/-- The joint entropy (in nats) of two cells. -/
noncomputable def jointCellEntropy (ci cj : Fin n) : ℝ :=
  ∑ p ∈ ps.jointRealizations ci cj,
    Real.negMulLog ((ps.jointWeight ci cj p.1 p.2 / ps.total : ℚ) : ℝ)

/-- The conditional entropy `H(cᵢ | cⱼ) = H(cᵢ, cⱼ) − H(cⱼ)` of cell `ci` given cell `cj`. -/
noncomputable def conditionalCellEntropy (ci cj : Fin n) : ℝ :=
  ps.jointCellEntropy ci cj - ps.cellEntropy cj

/-- Knowing cell `cj` leaves no uncertainty about cell `ci`. -/
def IsImplicative (ci cj : Fin n) : Prop := ps.conditionalCellEntropy ci cj = 0

/-- Every cell predicts every other cell. -/
def IsTransparent : Prop := ∀ ci cj, ci ≠ cj → ps.IsImplicative ci cj

/-- A cell with at most one realization has zero entropy. -/
theorem cellEntropy_eq_zero_of_card_le_one {c : Fin n} (h : (ps.realizations c).card ≤ 1) :
    ps.cellEntropy c = 0 := by
  refine Finset.sum_eq_zero fun r hr => ?_
  have hall : ps.cellWeight c r = ps.total := by
    unfold cellWeight total
    congr 1
    exact congrArg _ (List.filter_eq_self.2 fun e he => decide_eq_true
      (Finset.card_le_one.1 h _ (ps.mem_realizations.2 ⟨e, he, rfl⟩) r hr))
  rcases eq_or_ne ps.total 0 with h0 | h0 <;> simp [hall, h0]

/-- A cell predicted by another has zero conditional entropy given it. -/
theorem conditionalCellEntropy_eq_zero_of_predicts {ci cj : Fin n} (h : ps.Predicts {cj} ci) :
    ps.conditionalCellEntropy ci cj = 0 := by
  refine sub_eq_zero.2 (Finset.sum_bij (fun p _ => p.2) (fun p hp => ?_) (fun p hp q hq hpq => ?_)
    (fun r hr => ?_) fun p hp => ?_)
  · obtain ⟨e, he, rfl⟩ := ps.mem_jointRealizations.1 hp
    exact ps.mem_realizations.2 ⟨e, he, rfl⟩
  · obtain ⟨e, he, rfl⟩ := ps.mem_jointRealizations.1 hp
    obtain ⟨e', he', rfl⟩ := ps.mem_jointRealizations.1 hq
    exact Prod.ext (h e he e' he' fun _ hc => (Finset.mem_singleton.1 hc) ▸ hpq) hpq
  · obtain ⟨e, he, rfl⟩ := ps.mem_realizations.1 hr
    exact ⟨_, ps.mem_jointRealizations.2 ⟨e, he, rfl⟩, rfl⟩
  · obtain ⟨e, he, rfl⟩ := ps.mem_jointRealizations.1 hp
    congr 3
    unfold jointWeight cellWeight
    congr 1
    exact congrArg _ (List.filter_congr fun e' he' => by
      simp only [decide_eq_decide]
      exact ⟨fun h' => h'.2, fun h' =>
        ⟨(h e' he' e he fun _ hc => (Finset.mem_singleton.1 hc) ▸ h'), h'⟩⟩)

/-- A vocabularly clear system is transparent. -/
theorem isTransparent_of_isVocabularClear (h : ps.IsVocabularClear) : ps.IsTransparent :=
  fun ci cj _ => ps.conditionalCellEntropy_eq_zero_of_predicts (h cj ci)

end ParadigmSystem

end Morphology
