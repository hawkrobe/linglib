import Linglib.Semantics.Exhaustification.Disjunctive
import Linglib.Semantics.Questions.Partition.Basic
import Linglib.Semantics.Homogeneity.Plural
import Linglib.Data.Generalizations.HomogeneityGap
import Linglib.Data.Examples.BarLev2021

/-!
# Bar-Lev 2021: an implicature account of homogeneity and non-maximality

In this file we formalize the implicature account of homogeneity. Plural predication is the
existential `existsPlural D x P`, that some atom of `x` in the domain `D` satisfies `P`, and
its alternatives `subdomainAlts D x P` replace `D` by its subsets. Writing `∃-PL` as the
disjunction of its atoms and applying `Exhaustification.exhIEII_subDisjs`, we prove that
exhaustification over the alternatives yields the universal reading
(`exhIEII_existsPlural`), that over the negated alternatives of the negated sentence it is
vacuous (`exhIEII_compl_existsPlural`), and that over the alternatives with subdomains of
size `m` it yields "at least `n + 1 - m`" (`exhIEII_prunedAlts`). A partition `Q : Setoid W`
selects the strongest of these readings it decides (`IsReading`), which for the polar
question whether at least `k` atoms satisfy `P` is "at least `k`" (`isReading_polar_atLeast`).
A world is `Gappy` when it verifies the reading of one partition and falsifies another's,
which happens exactly where Križ's trivalent plural predication is undefined
(`gappy_iff_barePlural_eq_indet`). The paper's examples are instances in the model whose
worlds are the sets of atoms satisfying the predicate.

## Implementation notes

`readings` are the threshold readings, obtained by pruning to a fixed subdomain size; the
paper's asymmetric conjunctions of alternatives are omitted, so `IsReading` agrees with the
paper's selection on the partitions whose only decided readings are thresholds, which
includes the polar questions of (66), (80) and (81). The maximality constraint on prunings
is not formalized. `Gappy` ranges over all partitions and is context-free; that a context
fixing the partition removes the gap is carried by `reading_80` and `reading_81`.

## TODO

* The negative sentence is modelled only at the LF with negation over `∃-PL`; the LF with
  `∃-PL` over negation and the cover-restricted `∃-PL` of §5.3, the paper's source of the
  marginal negative non-maximal readings and of the pooled negative gap rows, are not
  formalized.
* The paper's full set of readings, and the non-distributive extension of §8.

## References

* [bar-lev-2021]
* [magri-2009]
* [magri-2014]
* [fox-2007]
* [fox-spector-2018]
* [crnic-chemla-fox-2015]
* [bar-lev-fox-2020]
* [malamud-2012]
* [kriz-2015]
* [kriz-2016]
* [kriz-chemla-2015]
* [kriz-spector-2021]
* [tieu-kriz-chemla-2019]
-/

namespace BarLev2021

open Exhaustification

variable {Atom W : Type*} {D x : Finset Atom} {P : Atom → W → Prop}

/-! ### Existential pluralization and its subdomain alternatives -/

variable (D x P) in
/-- The existential pluralization operator `∃-PL_D`: some atom of `x` in the domain `D`
satisfies `P`. Replacing `D` by a subset yields the subdomain alternatives. -/
def existsPlural : Set W := {w | ∃ a ∈ x, a ∈ D ∧ P a w}

instance [DecidableEq Atom] [∀ a w, Decidable (P a w)] :
    DecidablePred (· ∈ existsPlural D x P) :=
  fun w ↦ inferInstanceAs (Decidable (∃ a ∈ x, a ∈ D ∧ P a w))

/-- Under negation the universal reading is the basic meaning. -/
theorem notMem_existsPlural_iff {w : W} :
    w ∉ existsPlural D x P ↔ ∀ a ∈ x, a ∈ D → ¬ P a w := by
  simp [existsPlural]

variable [DecidableEq Atom]

variable (P) in
/-- The proposition `a` satisfies `P`. -/
def atom (a : Atom) : Set W := {w | P a w}

instance [∀ a w, Decidable (P a w)] (w : W) (a : Atom) : Decidable (w ∈ atom P a) :=
  inferInstanceAs (Decidable (P a w))

/-- `∃-PL_D P x` is the disjunction of the atoms of `x ∩ D`. -/
theorem existsPlural_eq_disj : existsPlural D x P = disj (x ∩ D) (atom P) := by
  ext w; simp [existsPlural, atom, disj, subDisj, Finset.mem_inter, and_assoc]

variable (D x P) in
/-- The subdomain alternatives: `∃-PL_{D'} P x` for `D' ⊆ D` meeting `x`. -/
def subdomainAlts : Set (Set W) :=
  {q | ∃ D' ⊆ D, (x ∩ D').Nonempty ∧ q = existsPlural D' x P}

/-- They are the sub-disjunctions of the atoms. -/
theorem subdomainAlts_eq : subdomainAlts D x P = subDisjs (x ∩ D) (atom P) := by
  ext q
  constructor
  · rintro ⟨D', hD', hne, rfl⟩
    exact ⟨x ∩ D', Finset.inter_subset_inter le_rfl hD', hne, existsPlural_eq_disj⟩
  · rintro ⟨S, hS, hne, rfl⟩
    have hSx := Finset.inter_eq_right.2 (hS.trans Finset.inter_subset_left)
    exact ⟨S, hS.trans Finset.inter_subset_right, by rwa [hSx], by rw [existsPlural_eq_disj, hSx]⟩

variable (D x P) in
/-- Every atom laughs alone at some world, and all laugh together at some world. -/
structure Separating : Prop where
  /-- Each atom of `x ∩ D` satisfies `P` alone at some world. -/
  single : ∀ a ∈ x ∩ D, ∃ w, ∀ b ∈ x ∩ D, P b w ↔ b = a
  /-- All atoms of `x ∩ D` satisfy `P` together at some world. -/
  all : ∃ w, ∀ a ∈ x ∩ D, P a w

/-! ### Homogeneity -/

/-- The maximality implicature: exhaustifying `∃-PL` over its subdomain alternatives gives the
universal reading. -/
theorem exhIEII_existsPlural (h : Separating D x P) (hne : (x ∩ D).Nonempty) :
    exhIEII (subdomainAlts D x P) (existsPlural D x P) = {w | ∀ a ∈ x, a ∈ D → P a w} := by
  rw [subdomainAlts_eq, existsPlural_eq_disj, exhIEII_subDisjs (p := atom P) h.single hne h.all]
  ext w; simp [atom, Finset.mem_inter]

/-- The asymmetry: with negation over `∃-PL`, every negated subdomain alternative is entailed
by the negated prejacent, so exhaustification over any of them is vacuous and no pruning yields
a non-maximal reading. -/
theorem exhIEII_compl_existsPlural {C : Set (Set W)} (hC : C ⊆ compl '' subdomainAlts D x P)
    (hsat : (existsPlural D x P)ᶜ.Nonempty) :
    exhIEII C (existsPlural D x P)ᶜ = (existsPlural D x P)ᶜ := by
  refine exhIEII_eq_self_of_forall_subset (fun q hq ↦ ?_) hsat
  obtain ⟨_, ⟨D', hD', -, rfl⟩, rfl⟩ := hC hq
  exact Set.compl_subset_compl.2 fun v ⟨a, ha, haD', hPa⟩ ↦ ⟨a, ha, hD' haD', hPa⟩

/-- (6a): the existential basic meaning does not entail that a given kid laughed. -/
theorem exists_mem_existsPlural_and_not (h : Separating D x P) {a : Atom} (ha : a ∈ x ∩ D)
    (h2 : 2 ≤ (x ∩ D).card) : ∃ w ∈ existsPlural D x P, ¬ P a w := by
  obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (by omega : 1 < (x ∩ D).card) a
  obtain ⟨w, hw⟩ := h.single b hb
  exact ⟨w, ⟨b, (Finset.mem_inter.1 hb).1, (Finset.mem_inter.1 hb).2, (hw b hb).2 rfl⟩,
    fun hPa ↦ hba ((hw a ha).1 hPa).symm⟩

/-- (6b): its negation entails that no given kid did. -/
theorem not_of_notMem_existsPlural {w : W} (hw : w ∉ existsPlural D x P) {a : Atom}
    (ha : a ∈ x ∩ D) : ¬ P a w :=
  notMem_existsPlural_iff.1 hw a (Finset.mem_inter.1 ha).1 (Finset.mem_inter.1 ha).2

/-- Simple disjunction, whose alternatives include the conjunction, is strengthened the other
way: the conjunction is denied. -/
theorem not_forall_of_mem_exhIEII_insert_iInter (h : Separating D x P) (h2 : 2 ≤ (x ∩ D).card)
    {w : W} (hw : w ∈ exhIEII (insert (⋂ a ∈ x ∩ D, atom P a) (subdomainAlts D x P))
      (existsPlural D x P)) : ¬ ∀ a ∈ x ∩ D, P a w := by
  rw [subdomainAlts_eq, existsPlural_eq_disj] at hw
  exact fun hall ↦ hw.2.1 _ (isInnocentlyExcludable_iInter_of_insert (p := atom P) h.single h2)
    (Set.mem_iInter₂.2 fun a ha ↦ hall a ha)

/-! ### Non-maximality by pruning -/

variable (D x P) in
/-- The alternatives over the subdomains of size `m`, with the prejacent. -/
def prunedAlts (m : ℕ) : Set (Set W) :=
  insert (existsPlural D x P) {q | ∃ D' ⊆ D, (x ∩ D').card = m ∧ q = existsPlural D' x P}

/-- They are the sub-disjunctions of size `m` with the disjunction itself. -/
theorem prunedAlts_eq {m : ℕ} : prunedAlts D x P m = subDisjsOfCard (x ∩ D) (atom P) m := by
  rw [prunedAlts, subDisjsOfCard, ← existsPlural_eq_disj]
  congr 1
  ext q
  constructor
  · rintro ⟨D', hD', hcard, rfl⟩
    exact ⟨x ∩ D', Finset.inter_subset_inter le_rfl hD', hcard, existsPlural_eq_disj⟩
  · rintro ⟨S, hS, hcard, rfl⟩
    have hSx := Finset.inter_eq_right.2 (hS.trans Finset.inter_subset_left)
    exact ⟨S, hS.trans Finset.inter_subset_right, by rwa [hSx], by rw [existsPlural_eq_disj, hSx]⟩

section Pruning

variable [∀ a w, Decidable (P a w)]

variable (D x P) in
/-- How many atoms of the plurality satisfy `P` at `w`. -/
def count (w : W) : ℕ := ((x ∩ D).filter (P · w)).card

variable (D x P) in
/-- "At least `k` of the kids laughed". -/
def atLeast (k : ℕ) : Set W := {w | k ≤ count D x P w}

@[simp] theorem mem_atLeast {k : ℕ} {w : W} : w ∈ atLeast D x P k ↔ k ≤ count D x P w := Iff.rfl

theorem count_le_card (w : W) : count D x P w ≤ (x ∩ D).card := Finset.card_filter_le _ _

theorem atLeast_antitone : Antitone (atLeast D x P) :=
  fun _ _ hkl _ hw ↦ hkl.trans hw

/-- The maximal reading is the threshold at the whole plurality. -/
theorem atLeast_card : atLeast D x P (x ∩ D).card = {w | ∀ a ∈ x, a ∈ D → P a w} := by
  ext w
  simp only [mem_atLeast, count, Set.mem_ofPred_eq]
  refine ⟨fun h a ha haD ↦ ?_, fun h ↦ ?_⟩
  · have := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) h
    rw [Finset.filter_eq_self] at this
    exact this a (Finset.mem_inter.2 ⟨ha, haD⟩)
  · rw [Finset.filter_true_of_mem fun a ha ↦
      h a (Finset.mem_inter.1 ha).1 (Finset.mem_inter.1 ha).2]

/-- Exhaustifying over the size-`m` alternatives yields "at least `n + 1 - m` of the kids
laughed". -/
theorem exhIEII_prunedAlts (h : Separating D x P) {m : ℕ} (hm : 0 < m)
    (hmn : m ≤ (x ∩ D).card) :
    exhIEII (prunedAlts D x P m) (existsPlural D x P) = atLeast D x P ((x ∩ D).card + 1 - m) := by
  rw [prunedAlts_eq, existsPlural_eq_disj,
    exhIEII_subDisjsOfCard (p := atom P) h.single h.all hm hmn]
  ext w
  change (x ∩ D).card < m + count D x P w ↔ (x ∩ D).card + 1 - m ≤ count D x P w
  omega

variable (D x P) in
/-- The readings of *the kids laughed*: the maximal one and the pruned ones. -/
def readings : Set (Set W) :=
  {q | ∃ m, 0 < m ∧ m ≤ (x ∩ D).card ∧ q = exhIEII (prunedAlts D x P m) (existsPlural D x P)}

/-- The readings are the thresholds from one to the whole plurality. -/
theorem mem_readings_iff (h : Separating D x P) {q : Set W} :
    q ∈ readings D x P ↔ ∃ k, 0 < k ∧ k ≤ (x ∩ D).card ∧ q = atLeast D x P k := by
  constructor
  · rintro ⟨m, hm, hmn, rfl⟩
    exact ⟨_, by omega, by omega, exhIEII_prunedAlts h hm hmn⟩
  · rintro ⟨k, hk, hkn, rfl⟩
    refine ⟨(x ∩ D).card + 1 - k, by omega, by omega, ?_⟩
    rw [exhIEII_prunedAlts h (by omega) (by omega)]
    congr 1; omega

/-- Pruning only weakens: the maximal reading entails every pruned one. -/
theorem exhIEII_subdomainAlts_subset_exhIEII_prunedAlts (h : Separating D x P)
    (hne : (x ∩ D).Nonempty) {m : ℕ} (hm : 0 < m) (hmn : m ≤ (x ∩ D).card) :
    exhIEII (subdomainAlts D x P) (existsPlural D x P) ⊆
      exhIEII (prunedAlts D x P m) (existsPlural D x P) := by
  rw [exhIEII_existsPlural h hne, exhIEII_prunedAlts h hm hmn, ← atLeast_card]
  exact atLeast_antitone (by omega)

/-! ### Relevance and gappiness -/

variable (D x P) in
/-- The reading given a partition: the strongest reading the partition decides. -/
def IsReading (Q : Setoid W) (q : Set W) : Prop :=
  q ∈ readings D x P ∧ Q.Decides q ∧ ∀ r ∈ readings D x P, Q.Decides r → q ⊆ r

/-- Given the polar question whether at least `k` of the kids laughed, *the kids laughed* means
that at least `k` did, provided every number of laughers is realized at some world. -/
theorem isReading_polar_atLeast (h : Separating D x P)
    (hcount : ∀ k ≤ (x ∩ D).card, ∃ w, count D x P w = k) {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ (x ∩ D).card) :
    IsReading D x P (Setoid.polar (atLeast D x P k)) (atLeast D x P k) := by
  refine ⟨(mem_readings_iff h).2 ⟨k, hk, hkn, rfl⟩, Setoid.polar_decides, fun r hr hQ ↦ ?_⟩
  obtain ⟨l, hl, hln, rfl⟩ := (mem_readings_iff h).1 hr
  refine atLeast_antitone (not_lt.1 fun hkl ↦ ?_)
  obtain ⟨w, hw⟩ := hcount l hln
  obtain ⟨v, hv⟩ := hcount k hkn
  have := hQ.iff (w := w) (v := v) (Setoid.polar_iff.2 (by simp only [mem_atLeast]; omega))
  simp only [mem_atLeast, hw, hv] at this
  omega

variable (D x P) in
/-- Gappiness: true given the reading some partition selects, false given another's. -/
def Gappy (w : W) : Prop :=
  (∃ (Q : Setoid W) (q : Set W), IsReading D x P Q q ∧ w ∈ q) ∧
    ∃ (Q : Setoid W) (q : Set W), IsReading D x P Q q ∧ w ∉ q

/-- The worlds judged neither true nor false are those where some but not all of the kids
laughed. -/
theorem gappy_iff (h : Separating D x P) (hcount : ∀ k ≤ (x ∩ D).card, ∃ w, count D x P w = k)
    (w : W) : Gappy D x P w ↔ 0 < count D x P w ∧ count D x P w < (x ∩ D).card := by
  constructor
  · rintro ⟨⟨_, q, ⟨hq, -, -⟩, hwq⟩, ⟨_, q', ⟨hq', -, -⟩, hwq'⟩⟩
    obtain ⟨k, hk, hkn, rfl⟩ := (mem_readings_iff h).1 hq
    obtain ⟨l, hl, hln, rfl⟩ := (mem_readings_iff h).1 hq'
    simp only [mem_atLeast, not_le] at hwq hwq'
    omega
  · rintro ⟨hpos, hlt⟩
    exact ⟨⟨_, _, isReading_polar_atLeast h hcount hpos (count_le_card w), mem_atLeast.2 le_rfl⟩,
      ⟨_, _, isReading_polar_atLeast h hcount (Nat.succ_pos _) hlt, by simp⟩⟩

/-- Where the accounts agree: a plain positive definite plural is gappy exactly where
[kriz-2016]'s trivalent plural predication is literally undefined. -/
theorem gappy_iff_barePlural_eq_indet (h : Separating D x P)
    (hcount : ∀ k ≤ (x ∩ D).card, ∃ w, count D x P w = k) (w : W) :
    Gappy D x P w ↔ Homogeneity.barePlural P (x ∩ D) w = .indet := by
  rw [gappy_iff h hcount, Homogeneity.barePlural, Trivalent.dist_eq_indet_iff, count,
    ← Finset.filter_ssubset, ← Finset.filter_nonempty_iff, Finset.card_pos]
  exact and_congr_right fun _ ↦ ⟨fun hlt ↦ Finset.ssubset_iff_subset_ne.2
    ⟨Finset.filter_subset _ _, ne_of_apply_ne _ hlt.ne⟩, Finset.card_lt_card⟩

/-- Where the accounts part: at a gappy world the trivalent negation is still undefined, while
the negative sentence with negation over `∃-PL`, exhaustified over any of its alternatives, is
plainly false. -/
theorem neg_barePlural_eq_indet_and_notMem_exhIEII_compl (h : Separating D x P)
    (hcount : ∀ k ≤ (x ∩ D).card, ∃ w, count D x P w = k) {w : W} (hw : Gappy D x P w)
    (C : Set (Set W)) :
    (Homogeneity.barePlural P (x ∩ D) w).neg = .indet ∧ w ∉ exhIEII C (existsPlural D x P)ᶜ := by
  refine ⟨Trivalent.neg_eq_indet_iff.2 ((gappy_iff_barePlural_eq_indet h hcount w).1 hw), ?_⟩
  obtain ⟨a, ha⟩ := Finset.card_pos.1 ((gappy_iff h hcount w).1 hw).1
  obtain ⟨ha, hPa⟩ := Finset.mem_filter.1 ha
  exact fun hmem ↦ hmem.1 ⟨a, (Finset.mem_inter.1 ha).1, (Finset.mem_inter.1 ha).2, hPa⟩

end Pruning

/-! ### The model whose worlds record who laughed -/

section Model

/-- The model whose worlds record which atoms satisfy the predicate: `a` satisfies it at the
world `w`, the set of atoms that do, when `a ∈ w`. -/
abbrev holds (a : Atom) (w : Finset Atom) : Prop := a ∈ w

variable (D x)

/-- Every atom satisfies the predicate alone at some world and all do at some world. -/
theorem separating_holds : Separating D x holds :=
  ⟨fun a _ ↦ ⟨{a}, fun _ _ ↦ Finset.mem_singleton⟩, ⟨x ∩ D, fun _ ↦ id⟩⟩

theorem count_holds (w : Finset Atom) : count D x holds w = (x ∩ D ∩ w).card := by
  rw [count, Finset.filter_mem_eq_inter]

/-- Every number of laughers up to the size of the plurality is realized. -/
theorem exists_count_holds_eq (k : ℕ) (hk : k ≤ (x ∩ D).card) : ∃ w, count D x holds w = k := by
  obtain ⟨S, hS, rfl⟩ := Finset.exists_subset_card_eq hk
  exact ⟨S, by rw [count_holds, Finset.inter_eq_right.2 hS]⟩

theorem isReading_polar_atLeast_holds {k : ℕ} (hk : 0 < k) (hkn : k ≤ (x ∩ D).card) :
    IsReading D x holds (Setoid.polar (atLeast D x holds k)) (atLeast D x holds k) :=
  isReading_polar_atLeast (separating_holds D x) (exists_count_holds_eq D x) hk hkn

end Model

/-! ### The paper's examples -/

/-- Kelly, Jane and Bill. -/
inductive Kid | kelly | jane | bill
  deriving DecidableEq, Fintype

/-- The kids. -/
def kids : Finset Kid := Finset.univ

/-- Kelly and Jane, the kids of (41). -/
def pair : Finset Kid := {.kelly, .jane}

/-- *Kelly laughed*. -/
abbrev kellyLaughed : Set (Finset Kid) := atom holds .kelly

/-- *Jane laughed*. -/
abbrev janeLaughed : Set (Finset Kid) := atom holds .jane

/-- (41a): *Kelly or Jane laughed*, whose alternatives include the conjunction, is strengthened
to "not both". -/
theorem disjunction_not_both :
    exhIEII {kellyLaughed ∪ janeLaughed, kellyLaughed, janeLaughed, kellyLaughed ∩ janeLaughed}
        (kellyLaughed ∪ janeLaughed) =
      (kellyLaughed ∪ janeLaughed) \ (kellyLaughed ∩ janeLaughed) :=
  exhIEII_pair_inter le_rfl
    ⟨{.kelly}, ⟨Or.inl (Finset.mem_singleton_self _), Finset.mem_singleton_self _⟩, by decide⟩
    ⟨{.jane}, ⟨Or.inr (Finset.mem_singleton_self _), Finset.mem_singleton_self _⟩, by decide⟩

/-- (41b): *the kids laughed*, whose alternatives are the subdomain alternatives alone, is
strengthened to "both". -/
theorem plural_both :
    exhIEII (subdomainAlts pair pair holds) (existsPlural pair pair holds) = {w | pair ⊆ w} := by
  rw [exhIEII_existsPlural (separating_holds _ _) (by decide)]
  exact Set.ext fun w ↦ ⟨fun h _ ha ↦ h _ ha ha, fun h a ha _ ↦ h ha⟩

/-- Given the partition (66) — at most one kid laughed, or two or three did — *the kids
laughed* means that at least two of the kids laughed. -/
theorem reading_66 :
    IsReading kids kids holds (Setoid.polar (atLeast kids kids holds 2))
      (atLeast kids kids holds 2) :=
  isReading_polar_atLeast_holds kids kids (by decide) (by decide)

/-- The ten books on the reading list. -/
abbrev Book := Fin 10

/-- The books. -/
def books : Finset Book := Finset.univ

/-- In the context of (80), where reading any five of the ten books passes the test, *Mary
read the books* means that she read at least five of them; the paper offers the prediction
that a fixed partition removes the gap tentatively. -/
theorem reading_80 :
    IsReading books books holds (Setoid.polar (atLeast books books holds 5))
      (atLeast books books holds 5) :=
  isReading_polar_atLeast_holds books books (by decide) (by decide)

/-- In the context of (81), where only reading all ten passes, *Mary read the books* has its
maximal reading. -/
theorem reading_81 :
    IsReading books books holds (Setoid.polar (atLeast books books holds 10))
      (atLeast books books holds 10) :=
  isReading_polar_atLeast_holds books books (by decide) (by decide)

/-! ### The example rows and the pooled gap rows -/

open Generalizations.HomogeneityGap (GapDatum allData)

/-- The pooled unembedded homogeneity-gap rows of the plural-definite papers available to the
paper. -/
def pluralDefiniteRows : List GapDatum :=
  allData.filter fun d ↦ d.source.bibkey == "kriz-2015" || d.source.bibkey == "kriz-chemla-2015"

/-- The pooled positive rows are judged neither true nor false exactly in the some-but-not-all
cells, as `gappy_iff` predicts; the negative rows, also gappy there, are the residue the paper
attributes to the LF with `∃-PL` over negation. -/
theorem pool_indet_iff_gap : ∀ d ∈ pluralDefiniteRows, d.polarity = .positive →
    (d.observed = .indet ↔ d.scenario = .gap) := by
  decide

/-- The paper's examples report gappiness for positive sentences and reduced gappiness for the
negative (82b), the asymmetry `neg_barePlural_eq_indet_and_notMem_exhIEII_compl` idealizes. -/
theorem rows_gappiness_positive : ∀ e ∈ Examples.all,
    e.feature? "gappiness" = some "yes" → e.feature? "polarity" = some "positive" := by
  decide

end BarLev2021
