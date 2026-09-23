module

public import Linglib.Semantics.Modality.Universals
public import Linglib.Data.Examples.ImelGuoSteinertThrelkeld2026
public import Linglib.Fragments.Washo.Modals
public import Linglib.Fragments.Koryak.Modals
public import Linglib.Fragments.Greek.StandardModern.Modals
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Imel, Guo and Steinert-Threlkeld (2026): An Efficient Communication Analysis of Modal Typology

This file formalizes the efficient-communication model of [imel-guo-steinert-threlkeld-2026].
A modal meaning is a subset of the six-point space `space`, weak and strong force by epistemic,
deontic and circumstantial flavor, and a language is a multiset of meanings. The complexity of
a meaning, Equation (1), is the least number of atoms of a formula of a Boolean Language of
Thought denoting it, computed here from the denotations of formulas with a given number of
atoms (`Formula.dens`, `complexity`). The informativeness of a language, Equations (2) and (3),
is the expected utility of literal communication under a communicative need distribution, a
literal listener guessing uniformly among the points of the modal heard and earning half credit
for each axis guessed right (`listen`, `informativeness`). Languages are compared by Pareto
dominance on complexity and communicative cost (`Dominates`), and naturalness is the fraction
of a vocabulary satisfying the Independence of Force and Flavor universal of
[steinert-threlkeld-imel-guo-2023], the substrate's `Modality.ForceFlavorIndependent`.

The paper's three results, that every Pareto-optimal system consists of IFF modals, that
naturalness correlates with optimality, and that the attested inventories are more optimal than
the sampled ones, are computational and are not formalized. What is proved are the properties
of the measures the results rest on. Table 2's complexities are recomputed over the experiment's
space, a language with a modal for each point is maximally informative and a single all-purpose
modal is not, a product meaning's listener utility depends only on its two axis sizes, and a
language with synonyms is dominated by, and so never Pareto-optimal against, the same language
without them.

## Implementation notes

* Table 2 illustrates complexity over a four-flavor space with a teleological flavor the
  library folds into circumstantial. Over the experiment's six-point space *may* is denoted by
  *w ∧ ¬c* and has complexity two, not the table's three, so the table's language has total
  complexity seven rather than eight.
* *may* and St'át'imcets *k'a* are read off the paper's examples (2) and (3), whose rows record
  a force and a flavor each.
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

@[expose] public section

namespace ImelGuoSteinertThrelkeld2026

open Modality Finset
open scoped BigOperators

/-- The forces of the experiment's space, weak and strong. -/
def forces : Finset ModalForce := {.possibility, .necessity}

/-- The flavors of the experiment's space. -/
def flavors : Finset ModalFlavor := {.epistemic, .deontic, .circumstantial}

/-- The meaning space `P`, six force-flavor pairs. -/
def space : Finset ForceFlavor := forces ×ˢ flavors

/-- A modal meaning, the force-flavor pairs a modal can express. -/
abbrev Meaning := Finset ForceFlavor

/-! ### The paper's examples -/

/-- The force-flavor pair a row's annotation records. -/
def Examples.forceFlavor (e : Data.Examples.LinguisticExample) : Option ForceFlavor := do
  let fo ← match e.paperFeatures.lookup "force" with
    | some "weak" => some ModalForce.possibility
    | some "strong" => some ModalForce.necessity
    | _ => none
  let fl ← match e.paperFeatures.lookup "flavor" with
    | some "epistemic" => some ModalFlavor.epistemic
    | some "deontic" => some ModalFlavor.deontic
    | some "circumstantial" => some ModalFlavor.circumstantial
    | _ => none
  return (fo, fl)

/-- English *may*, the pairs of examples (2a) and (2b). -/
def may : Meaning := ([Examples.s2a, Examples.s2b].filterMap Examples.forceFlavor).toFinset

/-- St'át'imcets *k'a*, the pairs of examples (3a) and (3b), after
[rullmann-matthewson-davis-2008]. -/
def ka : Meaning := ([Examples.s3a, Examples.s3b].filterMap Examples.forceFlavor).toFinset

theorem may_eq : may = {(.possibility, .epistemic), (.possibility, .deontic)} := by decide

theorem ka_eq : ka = {(.necessity, .epistemic), (.possibility, .epistemic)} := by decide

/-- Table 1: *may* varies in flavor and *k'a* in force, each on a single axis. -/
theorem singleAxis_may_ka : SingleAxis may ∧ SingleAxis ka := by
  rw [may_eq, ka_eq]; decide

/-! ### The Language of Thought and complexity -/

/-- The atoms of the Language of Thought, one per force and one per flavor of the space. -/
inductive Atom
  | weak
  | strong
  | epistemic
  | deontic
  | circumstantial
  deriving DecidableEq, Fintype

/-- The points at which an atom holds, a row or a column of the space. -/
def Atom.den : Atom → Meaning
  | .weak => {.possibility} ×ˢ flavors
  | .strong => {.necessity} ×ˢ flavors
  | .epistemic => forces ×ˢ {.epistemic}
  | .deontic => forces ×ˢ {.deontic}
  | .circumstantial => forces ×ˢ {.circumstantial}

/-- The atom for a force of the space. -/
def Atom.ofForce : ModalForce → Atom
  | .possibility => .weak
  | _ => .strong

/-- The atom for a flavor of the space. -/
def Atom.ofFlavor : ModalFlavor → Atom
  | .epistemic => .epistemic
  | .deontic => .deontic
  | _ => .circumstantial

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

/-- The points of the space at which a formula holds. -/
def den : Formula → Meaning
  | atom a => a.den
  | not φ => space \ φ.den
  | and φ ψ => φ.den ∩ ψ.den
  | or φ ψ => φ.den ∪ ψ.den

theorem one_le_atoms (φ : Formula) : 1 ≤ φ.atoms := by
  induction φ <;> simp only [atoms] <;> omega

theorem den_subset : ∀ φ : Formula, φ.den ⊆ space
  | atom a => by cases a <;> exact product_subset_product (by decide) (by decide)
  | not _ => sdiff_subset
  | and φ _ => inter_subset_left.trans φ.den_subset
  | or φ ψ => union_subset φ.den_subset ψ.den_subset

/-- The conjunction of a force atom and a flavor atom denoting one point of the space. -/
def point (p : ForceFlavor) : Formula :=
  and (atom (.ofForce p.force)) (atom (.ofFlavor p.flavor))

theorem den_point {p : ForceFlavor} (hp : p ∈ space) : (point p).den = {p} := by
  revert hp
  rcases p with ⟨f, fl⟩
  cases f <;> cases fl <;> decide

/-- Every meaning within the space is denoted, by the disjunction of its points. -/
theorem exists_den (m : Meaning) (hm : m ⊆ space) : ∃ φ : Formula, φ.den = m := by
  induction m using Finset.induction_on with
  | empty => exact ⟨and (atom .weak) (atom .strong), by decide⟩
  | insert p s _ ih =>
    obtain ⟨φ, hφ⟩ := ih ((subset_insert _ _).trans hm)
    exact ⟨or (point p) φ, by rw [den, hφ, den_point (hm (mem_insert_self _ _)), insert_eq]⟩

/-! #### Denotations by number of atoms

`dens n` is the set of denotations of formulas with exactly `n` atoms: the literals for one
atom, and for more the meets and joins of denotations of formulas whose atoms add up to `n`.
The recursion is fuelled so that it computes. -/

/-- The denotations of literals, an atom's points or their complement in the space. -/
def literals : Finset Meaning := univ.image Atom.den ∪ univ.image (space \ Atom.den ·)

/-- The meets and joins of a member of each set. -/
def combine (A B : Finset Meaning) : Finset Meaning :=
  (A ×ˢ B).image (λ x => x.1 ∩ x.2) ∪ (A ×ˢ B).image (λ x => x.1 ∪ x.2)

theorem inter_mem_combine {A B : Finset Meaning} {a b : Meaning} (ha : a ∈ A) (hb : b ∈ B) :
    a ∩ b ∈ combine A B :=
  mem_union_left _ (mem_image_of_mem _ (mk_mem_product ha hb))

theorem union_mem_combine {A B : Finset Meaning} {a b : Meaning} (ha : a ∈ A) (hb : b ∈ B) :
    a ∪ b ∈ combine A B :=
  mem_union_right _ (mem_image_of_mem _ (mk_mem_product ha hb))

theorem mem_combine {A B : Finset Meaning} {m : Meaning} :
    m ∈ combine A B ↔ ∃ a ∈ A, ∃ b ∈ B, m = a ∩ b ∨ m = a ∪ b := by
  simp only [combine, mem_union, mem_image, mem_product, Prod.exists]
  constructor
  · rintro (⟨a, b, ⟨ha, hb⟩, rfl⟩ | ⟨a, b, ⟨ha, hb⟩, rfl⟩)
    exacts [⟨a, ha, b, hb, Or.inl rfl⟩, ⟨a, ha, b, hb, Or.inr rfl⟩]
  · rintro ⟨a, ha, b, hb, rfl | rfl⟩
    exacts [Or.inl ⟨a, b, ⟨ha, hb⟩, rfl⟩, Or.inr ⟨a, b, ⟨ha, hb⟩, rfl⟩]

/-- `densAux fuel n` is `dens n` once `n ≤ fuel`. -/
def densAux : ℕ → ℕ → Finset Meaning
  | 0, _ => ∅
  | fuel + 1, n =>
    if n = 1 then literals
    else (range (n - 1)).biUnion λ i => combine (densAux fuel (i + 1)) (densAux fuel (n - 1 - i))

/-- The denotations of formulas with exactly `n` atoms. -/
def dens (n : ℕ) : Finset Meaning := densAux n n

theorem densAux_succ (f n : ℕ) :
    densAux (f + 1) n = if n = 1 then literals
      else (range (n - 1)).biUnion λ i => combine (densAux f (i + 1)) (densAux f (n - 1 - i)) :=
  rfl

theorem densAux_eq : ∀ {n f g : ℕ}, n ≤ f → n ≤ g → densAux f n = densAux g n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f g hf hg
    rcases f with _ | f <;> rcases g with _ | g
    · rfl
    · obtain rfl : n = 0 := by omega
      simp [densAux]
    · obtain rfl : n = 0 := by omega
      simp [densAux]
    · rw [densAux_succ, densAux_succ]
      split_ifs
      · rfl
      · refine biUnion_congr rfl λ i hi => ?_
        rw [mem_range] at hi
        rw [ih (i + 1) (by omega) (f := f) (g := g) (by omega) (by omega),
          ih (n - 1 - i) (by omega) (f := f) (g := g) (by omega) (by omega)]

theorem dens_one : dens 1 = literals := rfl

theorem dens_eq_biUnion {n : ℕ} (hn : 2 ≤ n) :
    dens n = (range (n - 1)).biUnion λ i => combine (dens (i + 1)) (dens (n - 1 - i)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [dens, densAux_succ, ite_eq_right (show k + 1 ≠ 1 by omega)]
  refine biUnion_congr rfl λ i hi => ?_
  rw [mem_range] at hi
  rw [densAux_eq (n := i + 1) (f := k) (g := i + 1) (by omega) le_rfl,
    densAux_eq (n := k + 1 - 1 - i) (f := k) (g := k + 1 - 1 - i) (by omega) le_rfl]
  rfl

theorem combine_dens_subset {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    combine (dens a) (dens b) ⊆ dens (a + b) := by
  rw [dens_eq_biUnion (n := a + b) (by omega)]
  have h : combine (dens a) (dens b) = combine (dens (a - 1 + 1)) (dens (a + b - 1 - (a - 1))) := by
    congr 2 <;> omega
  rw [h]
  exact subset_biUnion_of_mem (λ i => combine (dens (i + 1)) (dens (a + b - 1 - i)))
    (mem_range.2 (by omega))

/-- A formula's denotation, and its complement in the space, lie in the denotations of its
number of atoms. -/
theorem den_mem_dens : ∀ φ : Formula, φ.den ∈ dens φ.atoms ∧ space \ φ.den ∈ dens φ.atoms
  | atom a => ⟨mem_union_left _ (mem_image_of_mem _ (mem_univ a)),
      mem_union_right _ (mem_image_of_mem _ (mem_univ a))⟩
  | not φ => by
    obtain ⟨h₁, h₂⟩ := den_mem_dens φ
    exact ⟨h₂, by rw [den, Finset.sdiff_sdiff_eq_self φ.den_subset]; exact h₁⟩
  | and φ ψ => by
    obtain ⟨h₁, h₂⟩ := den_mem_dens φ
    obtain ⟨h₃, h₄⟩ := den_mem_dens ψ
    refine ⟨combine_dens_subset φ.one_le_atoms ψ.one_le_atoms (inter_mem_combine h₁ h₃), ?_⟩
    rw [den, sdiff_inter_distrib_right]
    exact combine_dens_subset φ.one_le_atoms ψ.one_le_atoms (union_mem_combine h₂ h₄)
  | or φ ψ => by
    obtain ⟨h₁, h₂⟩ := den_mem_dens φ
    obtain ⟨h₃, h₄⟩ := den_mem_dens ψ
    refine ⟨combine_dens_subset φ.one_le_atoms ψ.one_le_atoms (union_mem_combine h₁ h₃), ?_⟩
    rw [den, sdiff_union_distrib]
    exact combine_dens_subset φ.one_le_atoms ψ.one_le_atoms (inter_mem_combine h₂ h₄)

/-- Every denotation with `n` atoms is the denotation of a formula with `n` atoms. -/
theorem exists_den_of_mem_dens : ∀ {n : ℕ} {m : Meaning}, m ∈ dens n →
    ∃ φ : Formula, φ.atoms = n ∧ φ.den = m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m hm
    rcases n with _ | _ | n
    · exact absurd hm (by simp [dens, densAux])
    · rw [dens_one, literals, mem_union, mem_image, mem_image] at hm
      rcases hm with ⟨a, -, rfl⟩ | ⟨a, -, rfl⟩
      exacts [⟨atom a, rfl, rfl⟩, ⟨not (atom a), rfl, rfl⟩]
    · rw [dens_eq_biUnion (by omega), mem_biUnion] at hm
      obtain ⟨i, hi, hm⟩ := hm
      rw [mem_range] at hi
      obtain ⟨a, ha, b, hb, rfl | rfl⟩ := mem_combine.1 hm
      · obtain ⟨φ, hφ, rfl⟩ := ih (i + 1) (by omega) ha
        obtain ⟨ψ, hψ, rfl⟩ := ih (n + 2 - 1 - i) (by omega) hb
        exact ⟨and φ ψ, by simp only [atoms]; omega, rfl⟩
      · obtain ⟨φ, hφ, rfl⟩ := ih (i + 1) (by omega) ha
        obtain ⟨ψ, hψ, rfl⟩ := ih (n + 2 - 1 - i) (by omega) hb
        exact ⟨or φ ψ, by simp only [atoms]; omega, rfl⟩

theorem exists_mem_dens {m : Meaning} (hm : m ⊆ space) : ∃ n, m ∈ dens n :=
  let ⟨φ, hφ⟩ := exists_den m hm
  ⟨_, hφ ▸ (den_mem_dens φ).1⟩

end Formula

/-- Equation (1) for one modal, the least number of atoms of a formula denoting it. -/
def complexity (m : Meaning) : ℕ :=
  if h : m ⊆ space then Nat.find (Formula.exists_mem_dens h) else 0

theorem complexity_eq_iff {m : Meaning} (hm : m ⊆ space) {n : ℕ} :
    complexity m = n ↔ m ∈ Formula.dens n ∧ ∀ k < n, m ∉ Formula.dens k := by
  rw [complexity, dite_eq_left hm, Nat.find_eq_iff]

theorem complexity_le {m : Meaning} (φ : Formula) (h : φ.den = m) : complexity m ≤ φ.atoms := by
  rw [complexity, dite_eq_left (h ▸ φ.den_subset)]
  exact Nat.find_le (h ▸ (Formula.den_mem_dens φ).1)

theorem exists_den_atoms {m : Meaning} (hm : m ⊆ space) :
    ∃ φ : Formula, φ.atoms = complexity m ∧ φ.den = m := by
  rw [complexity, dite_eq_left hm]
  exact Formula.exists_den_of_mem_dens (Nat.find_spec (Formula.exists_mem_dens hm))

theorem one_le_complexity {m : Meaning} (hm : m ⊆ space) : 1 ≤ complexity m := by
  obtain ⟨φ, hφ, -⟩ := exists_den_atoms hm
  exact hφ ▸ φ.one_le_atoms

/-- The hypothetical *mought* of Table 2, weak epistemic or strong deontic. -/
def mought : Meaning := {(.possibility, .epistemic), (.necessity, .deontic)}

/-- The hypothetical *notcirc* of Table 2, everything but circumstantial. -/
def notcirc : Meaning := forces ×ˢ {.epistemic, .deontic}

/-- Over the six-point space *may* is *w ∧ ¬c*, two atoms, where Table 2's four-flavor space
needs three. -/
theorem complexity_may : complexity may = 2 := by
  rw [may_eq, complexity_eq_iff (by decide)]; decide +kernel

/-- *mought* needs four atoms, *(w ∧ e) ∨ (s ∧ d)*. -/
theorem complexity_mought : complexity mought = 4 := by
  rw [complexity_eq_iff (by decide)]; decide +kernel

/-- *notcirc* is the single literal *¬c*. -/
theorem complexity_notcirc : complexity notcirc = 1 := by
  rw [complexity_eq_iff (by decide)]; decide +kernel

/-- Complexity of a language, the sum over its modals, Equation (1). -/
def totalComplexity (L : Multiset Meaning) : ℕ := (L.map complexity).sum

/-- Table 2's language costs seven atoms over the experiment's space, one fewer than the
paper's eight over its illustration space. -/
theorem totalComplexity_table2 : totalComplexity {may, mought, notcirc} = 7 := by
  simp [totalComplexity, complexity_may, complexity_mought, complexity_notcirc]

theorem totalComplexity_replicate (k : ℕ) (m : Meaning) :
    totalComplexity (Multiset.replicate k m) = k * complexity m := by
  simp [totalComplexity, Multiset.map_replicate, Multiset.sum_replicate]

/-! ### Informativeness -/

/-- Equation (3), half credit for each axis of the intended point guessed right. -/
def utility (p q : ForceFlavor) : ℚ :=
  (if p.force = q.force then 1 / 2 else 0) + (if p.flavor = q.flavor then 1 / 2 else 0)

/-- The expected utility when the speaker intends `p` and a literal listener guesses uniformly
among the points a modal expresses. -/
def listen (m : Meaning) (p : ForceFlavor) : ℚ := 𝔼 q ∈ m, utility p q

/-- The modals of a language a literal speaker chooses among to express `p`. -/
def speakers (L : Multiset Meaning) (p : ForceFlavor) : Multiset Meaning := L.filter (p ∈ ·)

/-- Equation (2), the expected utility of literal communication under a communicative need
distribution, the speaker uniform over the modals expressing the intended point. -/
def informativeness (need : ForceFlavor → ℚ) (L : Multiset Meaning) : ℚ :=
  ∑ p ∈ space,
    need p * (((speakers L p).map (listen · p)).sum / Multiset.card (speakers L p))

/-- Communicative cost, the inverse of informativeness. -/
def cost (need : ForceFlavor → ℚ) (L : Multiset Meaning) : ℚ := 1 - informativeness need L

/-- Table 5, the communicative need distribution estimated from the corpus. -/
def needTable5 : ForceFlavor → ℚ
  | (.possibility, .epistemic) => 139 / 1000
  | (.possibility, .deontic) => 42 / 1000
  | (.possibility, .circumstantial) => 143 / 1000
  | (.necessity, .epistemic) => 104 / 1000
  | (.necessity, .deontic) => 254 / 1000
  | (.necessity, .circumstantial) => 318 / 1000
  | _ => 0

theorem sum_needTable5 : ∑ p ∈ space, needTable5 p = 1 := by decide +kernel

theorem listen_singleton (p : ForceFlavor) : listen {p} p = 1 := by
  simp [listen, expect_eq_sum_div_card, utility]; norm_num

/-- A listener hearing a product modal earns half the reciprocal of each axis size, so the
utility of an IFF modal depends only on how many forces and how many flavors it leaves open. -/
theorem listen_product {F : Finset ModalForce} {Φ : Finset ModalFlavor} {p : ForceFlavor}
    (hF : p.force ∈ F) (hΦ : p.flavor ∈ Φ) :
    listen (F ×ˢ Φ) p = (1 / F.card + 1 / Φ.card) / 2 := by
  have hF0 : (F.card : ℚ) ≠ 0 := by exact_mod_cast (card_pos.2 ⟨_, hF⟩).ne'
  have hΦ0 : (Φ.card : ℚ) ≠ 0 := by exact_mod_cast (card_pos.2 ⟨_, hΦ⟩).ne'
  rw [listen, expect_eq_sum_div_card, card_product]
  simp only [utility, sum_add_distrib, sum_product, sum_ite_eq, ite_eq_left hF, ite_eq_left hΦ,
    sum_const, nsmul_eq_mul, sum_comm (s := F) (t := Φ)]
  push_cast
  field_simp

/-- Table 2's *may* and *mought* have two points each; the IFF one is the more informative,
sharing an axis with any guess. -/
theorem listen_may_mought :
    listen may (.possibility, .epistemic) = 3 / 4 ∧
      listen mought (.possibility, .epistemic) = 1 / 2 := by
  rw [may_eq]; decide +kernel

/-- A language with a modal for each point of the space. -/
def singletons : Multiset Meaning := space.val.map ({·})

/-- The language of one modal expressing every point. -/
def whole : Multiset Meaning := {space}

theorem speakers_singletons {p : ForceFlavor} (hp : p ∈ space) : speakers singletons p = {{p}} := by
  rw [speakers, singletons, Multiset.filter_map]
  simp only [Function.comp_def, mem_singleton]
  rw [Multiset.filter_eq, Multiset.count_eq_one_of_mem space.nodup hp, Multiset.replicate_one,
    Multiset.map_singleton]

/-- A modal for each point is maximally informative: every point is conveyed exactly. -/
theorem informativeness_singletons (need : ForceFlavor → ℚ) :
    informativeness need singletons = ∑ p ∈ space, need p :=
  sum_congr rfl λ p hp => by
    rw [speakers_singletons hp, Multiset.map_singleton, Multiset.sum_singleton,
      Multiset.card_singleton, listen_singleton]
    simp

/-- One all-purpose modal conveys five twelfths of a point on average whatever the need, half
of a half plus a third. -/
theorem informativeness_whole (need : ForceFlavor → ℚ) :
    informativeness need whole = 5 / 12 * ∑ p ∈ space, need p := by
  rw [mul_sum]
  refine sum_congr rfl λ p hp => ?_
  have hs : speakers whole p = {space} := by
    rw [speakers, whole, Multiset.filter_singleton, ite_eq_left hp]
  rw [hs, Multiset.map_singleton, Multiset.sum_singleton, Multiset.card_singleton, space,
    listen_product (mem_product.1 hp).1 (mem_product.1 hp).2]
  simp [forces, flavors]
  ring

/-! ### Synonymy and dominance -/

/-- `L` dominates `L'` on the trade-off: no worse on either measure, better on one. -/
def Dominates (need : ForceFlavor → ℚ) (L L' : Multiset Meaning) : Prop :=
  totalComplexity L ≤ totalComplexity L' ∧ cost need L ≤ cost need L' ∧
    (totalComplexity L < totalComplexity L' ∨ cost need L < cost need L')

/-- Pareto optimality within a pool of languages. -/
def ParetoOptimal (need : ForceFlavor → ℚ) (pool : Set (Multiset Meaning))
    (L : Multiset Meaning) : Prop :=
  L ∈ pool ∧ ∀ L' ∈ pool, ¬ Dominates need L' L

theorem speakers_replicate (k : ℕ) (m : Meaning) (p : ForceFlavor) :
    speakers (Multiset.replicate k m) p = if p ∈ m then Multiset.replicate k m else 0 := by
  split_ifs with hp
  · exact Multiset.filter_eq_self.2 λ a ha => Multiset.eq_of_mem_replicate ha ▸ hp
  · exact Multiset.filter_eq_nil.2 λ a ha => Multiset.eq_of_mem_replicate ha ▸ hp

/-- Copies of one modal are as informative as the modal alone. -/
theorem informativeness_replicate (need : ForceFlavor → ℚ) {k : ℕ} (hk : k ≠ 0) (m : Meaning) :
    informativeness need (Multiset.replicate k m) = informativeness need {m} := by
  refine sum_congr rfl λ p _ => ?_
  rw [← Multiset.replicate_one m, speakers_replicate, speakers_replicate]
  split_ifs <;> simp [Multiset.map_replicate, Multiset.sum_replicate, hk]

/-- Synonymy hurts the trade-off: copies of a modal cost the same and add complexity. -/
theorem dominates_replicate (need : ForceFlavor → ℚ) {m : Meaning} (hm : m ⊆ space) {k : ℕ}
    (hk : 2 ≤ k) : Dominates need {m} (Multiset.replicate k m) := by
  have h1 := one_le_complexity hm
  have hc : totalComplexity {m} = complexity m := by simp [totalComplexity]
  have hcost : cost need {m} = cost need (Multiset.replicate k m) := by
    rw [cost, cost, informativeness_replicate need (by omega)]
  refine ⟨?_, hcost.le, Or.inl ?_⟩ <;> rw [hc, totalComplexity_replicate] <;> nlinarith

/-- A language of copies of one modal is not Pareto-optimal in any pool containing the modal
alone. -/
theorem not_paretoOptimal_replicate (need : ForceFlavor → ℚ) {pool : Set (Multiset Meaning)}
    {m : Meaning} (hm : m ⊆ space) (hpool : {m} ∈ pool) {k : ℕ} (hk : 2 ≤ k) :
    ¬ ParetoOptimal need pool (Multiset.replicate k m) :=
  λ h => h.2 _ hpool (dominates_replicate need hm hk)

/-! ### The universals and naturalness -/

/-- Naturalness, the fraction of an inventory satisfying the IFF universal. -/
def naturalness (L : List ModalItem) : ℚ :=
  (L.countP (ForceFlavorIndependent ·.meaning) : ℚ) / L.length

/-- Washo *-eʔ* varies on both axes, against the Single Axis of Variability universal of
[nauze-2008], and satisfies IFF, its meaning being the full grid of two forces and two flavors. -/
theorem washo_not_singleAxis_forceFlavorIndependent :
    ¬ SingleAxis Washo.modalEq.meaning ∧
      ForceFlavorIndependent Washo.modalEq.meaning := by
  decide

/-- The meaning the universal rules out, epistemic necessity with circumstantial possibility. -/
theorem not_forceFlavorIndependent_diagonal :
    ¬ ForceFlavorIndependent {(.necessity, .epistemic), (.possibility, .circumstantial)} := by
  decide

/-- Naturalness is graded: Modern Greek, one of the sampled languages, has one IFF modal in
three, where the Washo and Koryak inventories are fully natural. -/
theorem naturalness_greek_washo_koryak :
    naturalness Greek.StandardModern.modals = 1 / 3 ∧
      naturalness Washo.modals = 1 ∧
      naturalness Koryak.modals = 1 := by
  decide +kernel

end ImelGuoSteinertThrelkeld2026
