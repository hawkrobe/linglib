import Linglib.Semantics.Exhaustification.Disjunctive
import Linglib.Semantics.Plurality.Implicature
import Linglib.Data.Generalizations.HomogeneityGap
import Linglib.Data.Examples.BarLev2021

/-!
# Bar-Lev 2021: an implicature account of homogeneity and non-maximality

*The kids laughed* conveys that all the kids laughed and *the kids didn't laugh* that none
did. On the implicature account the basic meaning is existential — plural predication is
carried out by an existential pluralization operator `∃-PL` over a domain variable — and
the positive sentence is strengthened by exhaustification over its subdomain alternatives,
the sentences with the domain replaced by its subsets. Those alternatives are the
sub-disjunctions of the existential and include no conjunction, so, as with free choice,
nothing is innocently excludable and everything is innocently includable: `Exh` returns the
conjunction, the universal reading. Under negation the universal reading is the basic
meaning itself, which makes the account asymmetric: children who lack the implicature are
permissive with positive sentences only, and non-maximal readings — pruning some
alternatives, which can only weaken — arise for positive sentences and only marginally for
negative ones. Keeping just the alternatives over subdomains of size `m` yields "at least
`n + 1 - m` of the kids laughed", and the context's partition selects the strongest such
reading that is relevant to it; a "neither true nor false" judgment is uncertainty about that
partition, so expressions without non-maximal readings show no gap.

The general theorem is `Exhaustification.exhIEII_subDisjs` and its pruned form
`exhIEII_subDisjsOfCard`; this file instantiates them on `∃-PL`, states the asymmetry,
relevance and gappiness claims, and works the paper's two- and three-kid models. The
non-distributive extension of §8 is not formalized.

## References

* [bar-lev-2021]
* [magri-2014]
* [fox-2007]
* [bar-lev-fox-2020]
* [malamud-2012]
* [kriz-2015]
* [kriz-chemla-2015]
* [tieu-kriz-chemla-2019]
-/

namespace BarLev2021

open Exhaustification Semantics.Plurality.Implicature

variable {Atom W : Type*} {D x : Finset Atom} {P : Atom → W → Prop}

/-- Under negation the universal reading is the basic meaning. -/
theorem not_existPL_iff (w : W) : ¬ existPL D P x w ↔ ∀ a ∈ x, a ∈ D → ¬ P a w := by
  simp [existPL]

variable [DecidableEq Atom]

/-! ### Existential pluralization and its subdomain alternatives -/

/-- The proposition `a` satisfies `P`. -/
def atom (P : Atom → W → Prop) (a : Atom) : Set W := {w | P a w}

instance [∀ a w, Decidable (P a w)] (w : W) (a : Atom) : Decidable (w ∈ atom P a) :=
  inferInstanceAs (Decidable (P a w))

/-- `∃-PL_D P x` is the disjunction of the atoms of `x ∩ D`. -/
theorem existPL_eq_disj : {w | existPL D P x w} = disj (x ∩ D) (atom P) := by
  ext w; simp [existPL, atom, disj, subDisj, Finset.mem_inter, and_assoc]

/-- The subdomain alternatives: `∃-PL_{D'} P x` for `D' ⊆ D` meeting `x`. -/
def subdomainAlts (D x : Finset Atom) (P : Atom → W → Prop) : Set (Set W) :=
  {q | ∃ D' ⊆ D, (x ∩ D').Nonempty ∧ q = {w | existPL D' P x w}}

/-- They are the sub-disjunctions of the atoms. -/
theorem subdomainAlts_eq : subdomainAlts D x P = subDisjs (x ∩ D) (atom P) := by
  ext q
  constructor
  · rintro ⟨D', hD', hne, rfl⟩
    refine ⟨x ∩ D', Finset.inter_subset_inter le_rfl hD', hne, ?_⟩
    ext w; simp [existPL, atom, subDisj, Finset.mem_inter, and_assoc]
  · rintro ⟨S, hS, hne, rfl⟩
    refine ⟨S, hS.trans Finset.inter_subset_right, ?_, ?_⟩
    · rwa [Finset.inter_eq_right.2 (hS.trans Finset.inter_subset_left)]
    · ext w
      simp only [atom, subDisj, Set.mem_iUnion, Set.mem_ofPred_eq, existPL, exists_prop]
      exact ⟨λ ⟨i, hi, hw⟩ => ⟨i, (Finset.mem_inter.1 (hS hi)).1, hi, hw⟩,
        λ ⟨i, _, hi, hw⟩ => ⟨i, hi, hw⟩⟩

/-- Every atom laughs alone at some world, and all laugh together at some world. -/
structure Separating (D x : Finset Atom) (P : Atom → W → Prop) : Prop where
  single : ∀ a ∈ x ∩ D, ∃ w, ∀ b ∈ x ∩ D, P b w ↔ b = a
  all : ∃ w, ∀ a ∈ x ∩ D, P a w

/-! ### Homogeneity -/

/-- The maximality implicature: exhaustifying `∃-PL` over its subdomain alternatives gives the
universal reading. -/
theorem exhIEII_existPL (h : Separating D x P) (hne : (x ∩ D).Nonempty) :
    exhIEII (subdomainAlts D x P) {w | existPL D P x w} = {w | ∀ a ∈ x, a ∈ D → P a w} := by
  rw [subdomainAlts_eq, existPL_eq_disj, exhIEII_subDisjs (p := atom P) h.single hne h.all]
  ext w; simp [atom, Finset.mem_inter]

/-- The asymmetry: the existential basic meaning does not entail that a given kid laughed,
its negation entails that no given kid did. -/
theorem asymmetry (h : Separating D x P) {a : Atom} (ha : a ∈ x ∩ D) (h2 : 2 ≤ (x ∩ D).card) :
    (∃ w, existPL D P x w ∧ ¬ P a w) ∧ ∀ w, ¬ existPL D P x w → ¬ P a w := by
  refine ⟨?_, λ w hw => (not_existPL_iff w).1 hw a (Finset.mem_inter.1 ha).1
    (Finset.mem_inter.1 ha).2⟩
  obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (by omega : 1 < (x ∩ D).card) a
  obtain ⟨w, hw⟩ := h.single b hb
  exact ⟨w, ⟨b, (Finset.mem_inter.1 hb).1, (Finset.mem_inter.1 hb).2, (hw b hb).2 rfl⟩,
    λ hPa => hba ((hw a ha).1 hPa).symm⟩

/-- Simple disjunction, whose alternatives include the conjunction, is strengthened the other
way: the conjunction is denied. -/
theorem exhIEII_with_conjunction (h : Separating D x P) (h2 : 2 ≤ (x ∩ D).card) (w : W) :
    w ∈ exhIEII (insert (⋂ a ∈ x ∩ D, atom P a) (subdomainAlts D x P)) {w | existPL D P x w} →
      ¬ ∀ a ∈ x ∩ D, P a w := by
  rw [subdomainAlts_eq, existPL_eq_disj]
  intro hw hall
  exact hw.2.1 _ (isInnocentlyExcludable_iInter_of_insert (p := atom P) h.single h2)
    (Set.mem_iInter₂.2 λ a ha => hall a ha)

/-! ### Non-maximality by pruning -/

/-- The alternatives over the subdomains of size `m`, with the prejacent. -/
def prunedAlts (D x : Finset Atom) (P : Atom → W → Prop) (m : ℕ) : Set (Set W) :=
  subDisjsOfCard (x ∩ D) (atom P) m

/-- Exhaustifying over the size-`m` alternatives yields "at least `n + 1 - m` of the kids
laughed". -/
theorem exhIEII_prunedAlts [∀ a w, Decidable (P a w)] (h : Separating D x P) {m : ℕ}
    (hm : 0 < m) (hmn : m ≤ (x ∩ D).card) :
    exhIEII (prunedAlts D x P m) {w | existPL D P x w} =
      {w | (x ∩ D).card < m + ((x ∩ D).filter λ a => P a w).card} := by
  rw [prunedAlts, existPL_eq_disj, exhIEII_subDisjsOfCard (p := atom P) h.single h.all hm hmn]
  rfl

/-- Pruning only weakens: the maximal reading entails every pruned one. -/
theorem pruning_weakens [∀ a w, Decidable (P a w)] (h : Separating D x P)
    (hne : (x ∩ D).Nonempty) {m : ℕ} (hm : 0 < m) (hmn : m ≤ (x ∩ D).card) :
    exhIEII (subdomainAlts D x P) {w | existPL D P x w} ⊆
      exhIEII (prunedAlts D x P m) {w | existPL D P x w} := by
  rw [exhIEII_existPL h hne, exhIEII_prunedAlts h hm hmn]
  intro w hw
  have : (x ∩ D).filter (λ a => P a w) = x ∩ D :=
    Finset.filter_true_of_mem λ a ha => hw a (Finset.mem_inter.1 ha).1 (Finset.mem_inter.1 ha).2
  simp only [Set.mem_ofPred_eq, this]; omega

/-! ### Relevance and gappiness -/

/-- A proposition is relevant to a partition, given by its cell map, when it is a union of
cells. -/
def Relevant {κ : Type*} (cell : W → κ) (q : Set W) : Prop :=
  ∀ w v, cell w = cell v → (w ∈ q ↔ v ∈ q)

/-- The readings of *the kids laughed*: the maximal one and the pruned ones. -/
def readings (D x : Finset Atom) (P : Atom → W → Prop) : Set (Set W) :=
  {q | ∃ m, 0 < m ∧ m ≤ (x ∩ D).card ∧ q = exhIEII (prunedAlts D x P m) {w | existPL D P x w}}

/-- The reading given a partition: the strongest relevant reading. -/
def IsReading {κ : Type*} (D x : Finset Atom) (P : Atom → W → Prop) (cell : W → κ)
    (q : Set W) : Prop :=
  q ∈ readings D x P ∧ Relevant cell q ∧ ∀ r ∈ readings D x P, Relevant cell r → q ⊆ r

/-- Gappiness: true under some partition and false under another. -/
def Gappy (D x : Finset Atom) (P : Atom → W → Prop) (w : W) : Prop :=
  (∃ q ∈ readings D x P, w ∈ q) ∧ ∃ q ∈ readings D x P, w ∉ q

/-- The worlds judged neither true nor false are those where some but not all of the kids
laughed. -/
theorem gappy_iff [∀ a w, Decidable (P a w)] (h : Separating D x P) (h2 : 2 ≤ (x ∩ D).card)
    (w : W) : Gappy D x P w ↔
      0 < ((x ∩ D).filter λ a => P a w).card ∧
        ((x ∩ D).filter λ a => P a w).card < (x ∩ D).card := by
  have hcard := Finset.card_filter_le (x ∩ D) (λ a => P a w)
  constructor
  · rintro ⟨⟨q, ⟨m, hm, hmn, rfl⟩, hwq⟩, ⟨q', ⟨m', hm', hmn', rfl⟩, hwq'⟩⟩
    rw [exhIEII_prunedAlts h hm hmn] at hwq
    rw [exhIEII_prunedAlts h hm' hmn'] at hwq'
    simp only [Set.mem_ofPred_eq, not_lt] at hwq hwq'
    omega
  · rintro ⟨hpos, hlt⟩
    refine ⟨⟨_, ⟨(x ∩ D).card + 1 - ((x ∩ D).filter λ a => P a w).card, by omega, by omega,
      rfl⟩, ?_⟩,
      ⟨_, ⟨1, one_pos, by omega, rfl⟩, ?_⟩⟩
    · rw [exhIEII_prunedAlts h (by omega) (by omega)]; simp only [Set.mem_ofPred_eq]; omega
    · rw [exhIEII_prunedAlts h one_pos (by omega)]; simp only [Set.mem_ofPred_eq]; omega


/-! ### The three-kid model -/

/-- Kelly, Jane and Bill. -/
inductive Kid | kelly | jane | bill
  deriving DecidableEq, Fintype

/-- A world records who laughed. -/
abbrev W3 := Kid → Bool

def laughed (a : Kid) (w : W3) : Prop := w a = true

instance (a : Kid) (w : W3) : Decidable (laughed a w) := inferInstanceAs (Decidable (_ = _))

/-- The kids. -/
def kids : Finset Kid := Finset.univ

theorem separating : Separating kids kids laughed :=
  ⟨λ a _ => ⟨λ b => decide (b = a), λ b _ => by simp [laughed]⟩, ⟨λ _ => true, λ _ _ => rfl⟩⟩

/-- How many kids laughed. -/
def count (w : W3) : ℕ := ((kids ∩ kids).filter λ a => laughed a w).card

/-- The partition (66): at most one kid laughed, or two or three did. -/
def funny (w : W3) : Bool := decide (2 ≤ count w)

/-- Given (66), *the kids laughed* means that at least two of the kids laughed: the size-two
pruning is the one relevant reading. -/
theorem reading_66 :
    IsReading kids kids laughed funny (exhIEII (prunedAlts kids kids laughed 2)
      {w | existPL kids laughed kids w}) := by
  have hn : (kids ∩ kids).card = 3 := by decide
  have hform : ∀ m, 0 < m → m ≤ 3 → exhIEII (prunedAlts kids kids laughed m)
      {w | existPL kids laughed kids w} = {w | 3 < m + count w} := λ m hm hmn => by
    rw [exhIEII_prunedAlts separating hm (hn ▸ hmn), hn]; rfl
  refine ⟨⟨2, by omega, by omega, rfl⟩, ?_, ?_⟩
  · rw [hform 2 (by omega) (by omega)]
    intro w v hwv
    simp only [funny, decide_eq_decide] at hwv
    simp only [Set.mem_ofPred_eq]; omega
  · rintro r ⟨m, hm, hmn, rfl⟩ hrel
    rw [hn] at hmn
    rw [hform m hm hmn] at hrel
    rw [hform m hm hmn, hform 2 (by omega) (by omega)]
    rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3) with rfl | rfl | rfl
    · exact absurd ((hrel (λ _ => true) (λ a => decide (a ≠ .bill)) (by decide)).1 (by decide))
        (by decide)
    · exact le_rfl
    · exact absurd ((hrel (λ _ => false) (λ a => decide (a = .bill)) (by decide)).2 (by decide))
        (by decide)

/-! ### The paper's examples and the pooled gap rows -/

open Generalizations.HomogeneityGap (GapDatum allData)

/-- The pooled unembedded homogeneity-gap rows of the plural-definite papers available to the
paper. -/
def pluralDefiniteRows : List GapDatum :=
  allData.filter λ d => d.source.bibkey == "kriz-2015" || d.source.bibkey == "kriz-chemla-2015"

/-- Gap judgments occur only in the some-but-not-all cells, as `gappy_iff` predicts. -/
theorem pool_gap_only_between :
    (pluralDefiniteRows.filter λ d => d.scenario != .gap).all (λ d => d.observed != .indet) =
      true := by
  decide

/-- The paper's examples: gappiness reported only where non-maximal readings are. -/
theorem rows_gappiness_needs_nonmaximality : ∀ e ∈ Examples.all,
    e.feature? "gappiness" = some "yes" → e.feature? "non_maximality" ≠ some "no" := by
  decide

end BarLev2021
