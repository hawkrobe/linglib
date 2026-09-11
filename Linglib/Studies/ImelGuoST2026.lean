import Linglib.Semantics.Modality.Typology
import Linglib.Fragments.Washo.Modals
import Linglib.Fragments.Koryak.Modals
import Linglib.Fragments.Greek.StandardModern.Modals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Imel, Guo and Steinert-Threlkeld (2026): An Efficient Communication Analysis of Modal Typology

This file formalizes the efficient-communication model of [imel-guo-steinert-threlkeld-2026]:
modal meanings are subsets of a space of force-flavor pairs (`Space`, two forces by three
flavors), the complexity of a meaning is the minimum number of atoms of a formula of a Boolean
Language of Thought denoting it, Equation (1) (`Formula`, `complexity`), and the informativeness
of a language, a multiset of meanings, is the expected utility of literal communication under a
communicative need distribution, Equations (2) and (3) (`informativeness`), with the half-credit
utility of guessing one axis right. Languages are compared by Pareto dominance on complexity
and communicative cost (`Dominates`), and naturalness is the fraction of a vocabulary satisfying
the Independence of Force and Flavor universal of [steinert-threlkeld-imel-guo-2023], the
substrate's `Modality.Typology.satisfiesIFF`.

The paper's three results, that every Pareto-optimal system consists of IFF modals, that
naturalness correlates with optimality, and that the attested inventories are more optimal than
the sampled ones, are computational and are not formalized. What is proved are the properties
of the measures the results rest on: a language with a modal for each point is maximally
informative and a single all-purpose modal is not, a product meaning's listener utility depends
only on its two axis sizes, and synonyms of a modal are dominated by the modal alone.

## Implementation notes

* Table 2 illustrates complexity over a four-flavor space with a teleological flavor the
  library folds into circumstantial. Over the experiment's six-point space *may* is denoted by
  *w ∧ ¬c* and has complexity two, not the table's three.
* The Koryak verb *ivək* of the fragment expresses one flavor, doxastic and assertive both
  mapping to epistemic, so in this encoding it satisfies the Single Axis of Variability
  universal; Washo *-eʔ* is the counterexample proved here.

## References

* [imel-guo-steinert-threlkeld-2026]
* [steinert-threlkeld-imel-guo-2023]
* [nauze-2008]
* [rullmann-matthewson-davis-2008]
* [bochnak-2015a]
-/

namespace ImelGuoST2026

open Modality Modality.Typology Finset

/-- The meaning space of the experiment: weak and strong force by epistemic, deontic and
circumstantial flavor. -/
def Space : Finset ForceFlavor :=
  {⟨.possibility, .epistemic⟩, ⟨.possibility, .deontic⟩, ⟨.possibility, .circumstantial⟩,
   ⟨.necessity, .epistemic⟩, ⟨.necessity, .deontic⟩, ⟨.necessity, .circumstantial⟩}

/-- A modal meaning: the force-flavor pairs a modal can express. -/
abbrev Meaning := Finset ForceFlavor

/-- The meaning of a fragment entry within the space. -/
def meaningOf (e : ModalExpression) : Meaning := e.meaning.toFinset ∩ Space

/-! ### The Language of Thought and complexity -/

/-- The atoms of the Language of Thought: one per force and one per flavor. -/
inductive Atom
  | weak
  | strong
  | epistemic
  | deontic
  | circumstantial
  deriving DecidableEq

/-- The points at which an atom holds. -/
def Atom.Holds : Atom → ForceFlavor → Prop
  | .weak, p => p.force = .possibility
  | .strong, p => p.force = .necessity
  | .epistemic, p => p.flavor = .epistemic
  | .deontic, p => p.flavor = .deontic
  | .circumstantial, p => p.flavor = .circumstantial

instance (a : Atom) (p : ForceFlavor) : Decidable (a.Holds p) := by
  cases a <;> exact inferInstanceAs (Decidable (_ = _))

/-- Formulas of the Boolean Language of Thought. -/
inductive Formula
  | atom (a : Atom)
  | not (φ : Formula)
  | and (φ ψ : Formula)
  | or (φ ψ : Formula)

namespace Formula

/-- The number of atom occurrences, the length in literals of the complexity measure. -/
def atoms : Formula → ℕ
  | atom _ => 1
  | not φ => φ.atoms
  | and φ ψ | or φ ψ => φ.atoms + ψ.atoms

/-- Satisfaction at a point. -/
def Holds : Formula → ForceFlavor → Prop
  | atom a, p => a.Holds p
  | not φ, p => ¬ φ.Holds p
  | and φ ψ, p => φ.Holds p ∧ ψ.Holds p
  | or φ ψ, p => φ.Holds p ∨ ψ.Holds p

instance decHolds : ∀ (φ : Formula) (p : ForceFlavor), Decidable (φ.Holds p)
  | atom a, p => inferInstanceAs (Decidable (a.Holds p))
  | not φ, p => letI := decHolds φ p; inferInstanceAs (Decidable (¬ φ.Holds p))
  | and φ ψ, p => letI := decHolds φ p; letI := decHolds ψ p
      inferInstanceAs (Decidable (φ.Holds p ∧ ψ.Holds p))
  | or φ ψ, p => letI := decHolds φ p; letI := decHolds ψ p
      inferInstanceAs (Decidable (φ.Holds p ∨ ψ.Holds p))

/-- The denotation of a formula: the points of the space at which it holds. -/
def den (φ : Formula) : Meaning := Space.filter φ.Holds

theorem one_le_atoms (φ : Formula) : 1 ≤ φ.atoms := by
  induction φ <;> simp only [atoms] <;> omega

theorem den_subset (φ : Formula) : φ.den ⊆ Space := filter_subset _ _

theorem den_not (φ : Formula) : (not φ).den = Space \ φ.den := filter_not _ _

theorem den_and (φ ψ : Formula) : (and φ ψ).den = φ.den ∩ ψ.den := filter_and _ _ _

theorem den_or (φ ψ : Formula) : (or φ ψ).den = φ.den ∪ ψ.den := filter_or _ _ _

/-- A conjunction of a force atom and a flavor atom denoting one point of the space. -/
def point (p : ForceFlavor) : Formula :=
  and (atom (if p.force = .necessity then .strong else .weak))
    (atom (match p.flavor with
      | .epistemic => .epistemic
      | .deontic => .deontic
      | .bouletic | .circumstantial => .circumstantial))

theorem den_point (p : ForceFlavor) (hp : p ∈ Space) : (point p).den = {p} := by
  revert hp
  rcases p with ⟨f, fl⟩
  cases f <;> cases fl <;> decide

/-- Every meaning within the space is denoted, by the disjunction of its points. -/
theorem exists_den (m : Meaning) (hm : m ⊆ Space) : ∃ φ : Formula, φ.den = m := by
  induction m using Finset.induction_on with
  | empty => exact ⟨and (atom .weak) (atom .strong), by decide⟩
  | insert p s _ ih =>
    obtain ⟨φ, hφ⟩ := ih ((subset_insert _ _).trans hm)
    exact ⟨or (point p) φ, by
      rw [den_or, hφ, den_point p (hm (mem_insert_self _ _)), insert_eq]⟩

/-- A formula with one atom is an atom under negations, so it denotes an atom's points or
the complement of them. -/
theorem den_of_atoms_eq_one :
    ∀ φ : Formula, φ.atoms = 1 → ∃ a : Atom, φ.den = (atom a).den ∨ φ.den = Space \ (atom a).den
  | atom a, _ => ⟨a, Or.inl rfl⟩
  | not φ, h => by
    obtain ⟨a, ha | ha⟩ := den_of_atoms_eq_one φ h
    · exact ⟨a, Or.inr (by rw [den_not, ha])⟩
    · exact ⟨a, Or.inl (by rw [den_not, ha, Finset.sdiff_sdiff_eq_self (den_subset _)])⟩
  | and φ ψ, h | or φ ψ, h => by
    have := one_le_atoms φ; have := one_le_atoms ψ; simp only [atoms] at h; omega

end Formula

open Classical in
/-- Equation (1) for one modal: the least number of atoms of a formula denoting it. -/
noncomputable def complexity (m : Meaning) : ℕ :=
  if h : m ⊆ Space then
    Nat.find (p := λ n => ∃ φ : Formula, φ.atoms = n ∧ φ.den = m)
      ⟨_, (Formula.exists_den m h).choose, rfl, (Formula.exists_den m h).choose_spec⟩
  else 0

theorem complexity_le {m : Meaning} (φ : Formula) (h : φ.den = m) : complexity m ≤ φ.atoms := by
  classical
  unfold complexity
  rw [dif_pos (h ▸ φ.den_subset)]
  exact Nat.find_le ⟨φ, rfl, h⟩

theorem exists_den_atoms {m : Meaning} (hm : m ⊆ Space) :
    ∃ φ : Formula, φ.atoms = complexity m ∧ φ.den = m := by
  classical
  unfold complexity
  rw [dif_pos hm]
  exact Nat.find_spec (p := λ n => ∃ φ : Formula, φ.atoms = n ∧ φ.den = m) _

theorem one_le_complexity {m : Meaning} (hm : m ⊆ Space) : 1 ≤ complexity m := by
  obtain ⟨φ, hφ, -⟩ := exists_den_atoms hm
  exact hφ ▸ φ.one_le_atoms

/-- English *may* of Table 2, weak force with epistemic or deontic flavor. -/
def may : Meaning := {⟨.possibility, .epistemic⟩, ⟨.possibility, .deontic⟩}

/-- The hypothetical *mought* of Table 2, weak epistemic or strong deontic. -/
def mought : Meaning := {⟨.possibility, .epistemic⟩, ⟨.necessity, .deontic⟩}

/-- The hypothetical *notcirc* of Table 2: everything but circumstantial. -/
def notcirc : Meaning := Space \ (Formula.atom .circumstantial).den

/-- *notcirc* is denoted by the single literal *¬c*. -/
theorem complexity_notcirc : complexity notcirc = 1 :=
  le_antisymm (complexity_le (.not (.atom .circumstantial)) (Formula.den_not _))
    (one_le_complexity sdiff_subset)

/-- Over the six-point space *may* is *w ∧ ¬c*, two atoms; no single literal denotes it. -/
theorem complexity_may : complexity may = 2 := by
  refine le_antisymm
    (complexity_le (.and (.atom .weak) (.not (.atom .circumstantial))) (by decide)) ?_
  obtain ⟨φ, hφ, hden⟩ := exists_den_atoms (m := may) (by decide)
  rw [← hφ]
  by_contra h
  have h1 : φ.atoms = 1 := by have := φ.one_le_atoms; omega
  obtain ⟨a, ha | ha⟩ := Formula.den_of_atoms_eq_one φ h1 <;> rw [hden] at ha <;>
    revert ha <;> cases a <;> decide

/-- Complexity of a language: the sum over its modals, Equation (1). -/
noncomputable def totalComplexity (L : List Meaning) : ℕ := (L.map complexity).sum

theorem totalComplexity_replicate (k : ℕ) (m : Meaning) :
    totalComplexity (List.replicate k m) = k * complexity m := by
  simp [totalComplexity, List.map_replicate, List.sum_replicate]

/-! ### Informativeness -/

/-- Equation (3): half credit for each axis of the intended point guessed right. -/
def utility (p q : ForceFlavor) : ℚ :=
  (if p.force = q.force then 1 / 2 else 0) + (if p.flavor = q.flavor then 1 / 2 else 0)

/-- A literal listener guesses uniformly among the points a modal expresses: the expected
utility when the speaker intends `p`. -/
def listen (m : Meaning) (p : ForceFlavor) : ℚ := (∑ q ∈ m, utility p q) / m.card

/-- The modals of a language a literal speaker chooses among to express `p`. -/
def speakers (L : List Meaning) (p : ForceFlavor) : List Meaning := L.filter (p ∈ ·)

/-- Equation (2): the expected utility of literal communication under a communicative need
distribution, the speaker uniform over the modals expressing the intended point. -/
def informativeness (need : ForceFlavor → ℚ) (L : List Meaning) : ℚ :=
  ∑ p ∈ Space, need p * (((speakers L p).map (listen · p)).sum / (speakers L p).length)

/-- Communicative cost, the inverse of informativeness. -/
def cost (need : ForceFlavor → ℚ) (L : List Meaning) : ℚ := 1 - informativeness need L

/-- Table 5: the communicative need distribution estimated from the corpus. -/
def needTable5 : ForceFlavor → ℚ
  | ⟨.possibility, .epistemic⟩ => 139 / 1000
  | ⟨.possibility, .deontic⟩ => 42 / 1000
  | ⟨.possibility, .circumstantial⟩ => 143 / 1000
  | ⟨.necessity, .epistemic⟩ => 104 / 1000
  | ⟨.necessity, .deontic⟩ => 254 / 1000
  | ⟨.necessity, .circumstantial⟩ => 318 / 1000
  | _ => 0

theorem sum_needTable5 : ∑ p ∈ Space, needTable5 p = 1 := by decide +kernel

/-- A language with a modal for each point of the space. -/
def singletons : List Meaning :=
  [{⟨.possibility, .epistemic⟩}, {⟨.possibility, .deontic⟩}, {⟨.possibility, .circumstantial⟩},
   {⟨.necessity, .epistemic⟩}, {⟨.necessity, .deontic⟩}, {⟨.necessity, .circumstantial⟩}]

/-- The language of one modal expressing every point. -/
def whole : List Meaning := [Space]

/-- A modal for each point is maximally informative: every point is conveyed exactly. -/
theorem informativeness_singletons (need : ForceFlavor → ℚ) :
    informativeness need singletons = ∑ p ∈ Space, need p := by
  refine sum_congr rfl λ p hp => ?_
  suffices h :
      ((speakers singletons p).map (listen · p)).sum / (speakers singletons p).length = 1 by
    rw [h, mul_one]
  revert hp; rcases p with ⟨f, fl⟩; cases f <;> cases fl <;> decide +kernel

/-- One all-purpose modal conveys five twelfths of a point on average whatever the need. -/
theorem informativeness_whole (need : ForceFlavor → ℚ) :
    informativeness need whole = 5 / 12 * ∑ p ∈ Space, need p := by
  rw [mul_sum]
  refine sum_congr rfl λ p hp => ?_
  suffices h : ((speakers whole p).map (listen · p)).sum / (speakers whole p).length = 5 / 12 by
    rw [h, mul_comm]
  revert hp; rcases p with ⟨f, fl⟩; cases f <;> cases fl <;> decide +kernel

/-- The grid of a set of forces and a set of flavors, the meaning of a modal satisfying the
universal in its alternative formulation. -/
def grid (F : Finset ModalForce) (Φ : Finset ModalFlavor) : Meaning :=
  (F ×ˢ Φ).image λ x => ⟨x.1, x.2⟩

/-- A listener hearing a grid modal earns half the reciprocal of each axis size: the utility of
an IFF modal depends only on how many forces and how many flavors it leaves open. -/
theorem listen_grid {F : Finset ModalForce} {Φ : Finset ModalFlavor} {p : ForceFlavor}
    (hF : p.force ∈ F) (hΦ : p.flavor ∈ Φ) :
    listen (grid F Φ) p = (1 / F.card + 1 / Φ.card) / 2 := by
  have hinj : Function.Injective (λ x : ModalForce × ModalFlavor => (⟨x.1, x.2⟩ : ForceFlavor)) :=
    λ x y h => Prod.ext (congrArg ForceFlavor.force h) (congrArg ForceFlavor.flavor h)
  have hF0 : (F.card : ℚ) ≠ 0 := by exact_mod_cast (card_pos.2 ⟨_, hF⟩).ne'
  have hΦ0 : (Φ.card : ℚ) ≠ 0 := by exact_mod_cast (card_pos.2 ⟨_, hΦ⟩).ne'
  rw [listen, grid, card_image_of_injective _ hinj, sum_image (λ x _ y _ h => hinj h), card_product]
  simp only [utility, sum_add_distrib, sum_product, sum_ite_eq, if_pos hF, if_pos hΦ,
    sum_const, nsmul_eq_mul, sum_comm (s := F) (t := Φ)]
  push_cast
  field_simp

/-- Table 2's *may* and *mought* have two points each; the IFF one is the more informative,
sharing an axis with any guess. -/
theorem listen_may_mought :
    listen may ⟨.possibility, .epistemic⟩ = 3 / 4 ∧
      listen mought ⟨.possibility, .epistemic⟩ = 1 / 2 := by
  decide +kernel

/-! ### Synonymy and dominance -/

/-- `L` dominates `L'` on the trade-off: no worse on either measure, better on one. -/
def Dominates (need : ForceFlavor → ℚ) (L L' : List Meaning) : Prop :=
  totalComplexity L ≤ totalComplexity L' ∧ cost need L ≤ cost need L' ∧
    (totalComplexity L < totalComplexity L' ∨ cost need L < cost need L')

/-- Pareto optimality within a pool of languages. -/
def ParetoOptimal (need : ForceFlavor → ℚ) (pool : Set (List Meaning)) (L : List Meaning) :
    Prop :=
  L ∈ pool ∧ ∀ L' ∈ pool, ¬ Dominates need L' L

/-- Copies of one modal are as informative as the modal alone. -/
theorem informativeness_replicate (need : ForceFlavor → ℚ) {k : ℕ} (hk : k ≠ 0) (m : Meaning) :
    informativeness need (List.replicate k m) = informativeness need [m] := by
  refine sum_congr rfl λ p _ => ?_
  by_cases hp : p ∈ m <;>
    simp [speakers, hp, List.map_replicate, List.sum_replicate, hk]

/-- Synonymy hurts the trade-off: copies of a modal cost the same and add complexity. -/
theorem dominates_replicate (need : ForceFlavor → ℚ) {m : Meaning} (hm : m ⊆ Space) {k : ℕ}
    (hk : 2 ≤ k) : Dominates need [m] (List.replicate k m) := by
  have h1 := one_le_complexity hm
  have hc : totalComplexity [m] = complexity m := by simp [totalComplexity]
  have hcost : cost need [m] = cost need (List.replicate k m) := by
    rw [cost, cost, informativeness_replicate need (by omega)]
  refine ⟨?_, hcost.le, Or.inl ?_⟩ <;> rw [hc, totalComplexity_replicate] <;> nlinarith

/-! ### The universals and naturalness -/

/-- Naturalness: the fraction of an inventory satisfying the IFF universal. -/
def naturalness (inv : ModalInventory) : ℚ := inv.iffCount / inv.size

/-- Washo *-eʔ* varies on both axes, against the Single Axis of Variability universal of
[nauze-2008], and satisfies IFF, its meaning being the full grid of two forces and two flavors. -/
theorem washo_not_sav_iff :
    satisfiesSAV Washo.Modals.modalEq.meaning = false ∧
      satisfiesIFF Washo.Modals.modalEq.meaning = true := by
  decide

/-- The meaning the universal rules out: epistemic necessity with circumstantial possibility. -/
theorem not_iff_diagonal :
    satisfiesIFF [⟨.necessity, .epistemic⟩, ⟨.possibility, .circumstantial⟩] = false := by
  decide

/-- Naturalness is graded: Modern Greek, one of the sampled languages, has one IFF modal in
three, where the Washo and Koryak inventories are fully natural. -/
theorem naturalness_greek_washo_koryak :
    naturalness ⟨"Modern Greek", "Indo-European", "", Greek.StandardModern.Modals.allExpressions⟩
        = 1 / 3 ∧
      naturalness ⟨"Washo", "isolate", "", Washo.Modals.allExpressions⟩ = 1 ∧
      naturalness ⟨"Koryak", "Chukotko-Kamchatkan", "", Koryak.Modals.allExpressions⟩ = 1 := by
  decide +kernel

end ImelGuoST2026
