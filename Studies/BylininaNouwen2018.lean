module

public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Semantics.Exhaustification.Pointwise
public import Linglib.Data.Examples.BylininaNouwen2018
public import Mathlib.Data.Set.Card
public import Linglib.Fragments.English.PolarityItems
public import Linglib.Semantics.Polarity.Licensing

/-!
# Bylinina and Nouwen (2018): On *zero* and semantic plurality

This file formalizes the argument of Bylinina and Nouwen that *zero* is a numeral, not a negative
quantifier like *no*, and that its semantics needs an empty plurality. A numeral contributes a
cardinality, `∃x[#x = n ∧ A(x) ∧ B(x)]`, with an at least reading ((20)–(28)). With Link's
pluralization `*` ((29)), which excludes the sum of the empty set, *zero A B* is a contradiction
((36)); with the full lattice `×` ((30)), which has the empty plurality `⊥`, it is a tautology
((37), (39)), and exhaustifying it against the higher numerals gives *no A B* ((40)).

The polarity of *zero* follows from the split between the two meanings. Weak negative polarity
items need their environment non-trivially downward entailing, downward and not upward entailing,
in the meaning below the exhaustivity operator, and strong items in the meaning above it as well
((53)). Below the operator *zero A B* is a tautology, downward and upward entailing at once, so
*zero* licenses neither kind of item ((54)), while *few* licenses weak items only ((48)) and *no*
both. An analysis with a basic exactly meaning has no such split: Kennedy's degree quantifier
*zero*, `λP. max(P) = 0`, is *no A B* under `×` ((73)) and never true under `*` ((72)), and as *no*
it licenses both kinds of item (Section 6.3).

The empty plurality is needed elsewhere: under `×` a downward monotone degree quantifier such as
*fewer than ten* is downward monotone in its scope, under `*` it is not ((65), (66)). On scope the
two analyses agree (Section 6.2): exhaustifying the lower bound at a site and raising Kennedy's
quantifier to that site give the same reading, so the split-scope reading (77b) of *every student
read zero books*, which the sentence lacks ((78)), is blocked only for the degree quantifier, by
the Heim-Kennedy generalization ((80)).

## Main results

* `exhAgainst_zero_iff_no`, `zero_mem_countDegrees`: exhaustified *zero* is *no*, and the
  unexhaustified *zero* is a tautology.
* `not_licenses_zero`, `rows_predicted`: *zero* licenses no polarity item, *few* weak ones only
  and *no* both, as the paper's judgments have it.
* `kennedyZero_eq_nobody`: Kennedy's *zero* is the context of *no*.
* `antitone_maxIn_countDegrees`, `not_antitone_maxIn_countDegrees_sdiff`: *fewer than ten* is
  downward monotone with `×` and not with `*`.

## Implementation notes

* Pluralities are the finite sets of atoms, so `plural Z`, the pluralities of members of `Z`, is
  the full lattice `×Z`, and Link's `*Z` is `plural Z \ {∅}`. A distributive predicate `B` holds of
  a plurality that is in `plural B`.
* Degrees are natural numbers; Kennedy's numeral is `Degree.MaxIn {n}` and its two scopes are
  `Degree.LowScope` and `Degree.HighScope`. Exhaustification against the higher numerals is
  `Exhaustification.exhAgainst (· < ·)`.
* Licensing is the library's: *zero* is a scalar `PolarityItem.LicensingContext`, and every item
  needs the meaning below the exhaustivity operator non-trivially downward entailing. For strong
  items the library asks Zwarts's anti-additivity of the meaning above it where (53) asks for
  non-trivial downward entailment; *zero* fails the first condition, so the two agree on it.

## TODO

The tag-question and neg-inversion contrasts (Section 2), the existential operator `E` for bare
plurals ((58)), plural definites with `⊥` ((60)–(64)), and the stipulation `max(∅) = 0` that would
let the de-Fregean analysis do without `⊥` (Section 6.1) are not formalized.

## References

* [bylinina-nouwen-2018]
* [link-1983]
* [gajewski-2011]
* [lahiri-1998]
* [kennedy-2015]
* [heim-2000]
-/

@[expose] public section
namespace BylininaNouwen2018

open Degree Exhaustification Quantifier Quantifier.GQ Set

variable {α : Type*}

/-! ### Pluralities and numerals -/

/-- The pluralities of members of `Z`, the sums `⊔X` of the subsets `X ⊆ Z` ((30)), the empty sum
`⊥` among them. -/
def plural (Z : Set α) : Set (Finset α) := {x | ↑x ⊆ Z}

/-- The degree property `λi. ∃x[#x = i ∧ A(x) ∧ C(x)]` of the pluralities of members of `A` that
are `C`, which a numeral `n` holds of at its lower bound ((27)) and Kennedy's numeral quantifies
over ((71)). -/
def countDegrees (A : Set α) (C : Set (Finset α)) : Set ℕ :=
  {n | ∃ x : Finset α, x.card = n ∧ x ∈ plural A ∩ C}

/-- With a distributive predicate the degree property is a lower set, so the numeral has an at
least reading ((20), (22)). -/
theorem isLowerSet_countDegrees_plural (A B : Set α) : IsLowerSet (countDegrees A (plural B)) := by
  rintro d e hed ⟨x, rfl, hA, hB⟩
  obtain ⟨y, hyx, rfl⟩ := Finset.exists_subset_card_eq hed
  exact ⟨y, rfl, (Finset.coe_subset.2 hyx).trans hA, (Finset.coe_subset.2 hyx).trans hB⟩

/-- With a collective predicate true of the plurality `s` alone, the degree property holds at `#s`
alone, so the numeral has no at least reading. -/
theorem countDegrees_singleton {A : Set α} {s : Finset α} (hs : ↑s ⊆ A) :
    countDegrees A {s} = {s.card} :=
  Set.ext fun _ ↦ ⟨fun ⟨_, hx, _, hxs⟩ ↦ (hxs ▸ hx : s.card = _).symm,
    fun h ↦ ⟨s, h.symm, hs, rfl⟩⟩

/-- With finitely many members of `A ∩ B` the degree property under `×` is `{0, …, n}` for their
number `n` ((73)), the measured degree property of `Degree.LowScope`. -/
theorem countDegrees_plural_eq_Iic {A B : Set α} (h : (A ∩ B).Finite) :
    countDegrees A (plural B) = Iic (A ∩ B).ncard := by
  ext d
  simp only [countDegrees, plural, mem_inter_iff, mem_ofPred_eq, mem_Iic, ← subset_inter_iff,
    ← h.subset_toFinset, ncard_eq_toFinset_card _ h]
  exact ⟨fun ⟨x, hx, hs⟩ ↦ hx ▸ Finset.card_le_card hs,
    fun hd ↦ let ⟨y, hy, hc⟩ := Finset.exists_subset_card_eq hd; ⟨y, hc, hy⟩⟩

/-! ### *Zero*

Under `*` the at least *zero* is a contradiction and under `×` a tautology; exhaustification
against the higher numerals turns the tautology into *no*. -/

/-- Under `*`, *zero A B* is a contradiction ((36)). -/
theorem zero_notMem_countDegrees_sdiff (A B : Set α) :
    0 ∉ countDegrees A (plural B \ {∅}) :=
  fun ⟨_, hx, _, _, hne⟩ ↦ hne (Finset.card_eq_zero.1 hx)

/-- Under `×`, *zero A B* is a tautology ((37), (39)). -/
theorem zero_mem_countDegrees (A B : Set α) : 0 ∈ countDegrees A (plural B) :=
  ⟨∅, Finset.card_empty, by simp [plural]⟩

/-- Kennedy's quantifier holds of a degree property when the lower bound, exhaustified against the
higher numerals, does: both say that `n` is its greatest degree. -/
theorem maxIn_singleton_iff_exhAgainst {D : Type*} [LinearOrder D] {P : Set D} {n : D} :
    MaxIn {n} P ↔ exhAgainst (· < ·) (· ∈ P) n :=
  maxIn_singleton.trans <| and_congr_right' ⟨fun h _ hm hmP ↦ (h hmP).not_gt hm,
    fun h m hmP ↦ not_lt.1 fun hm ↦ h m hm hmP⟩

/-- Under `×`, Kennedy's *zero A B* is *no A B* ((73)). -/
theorem maxIn_zero_countDegrees_iff {A B : Set α} :
    MaxIn {0} (countDegrees A (plural B)) ↔ GQ.no A B := by
  refine maxIn_singleton.trans ⟨fun h a ha hb ↦ ?_, fun h ↦ ⟨zero_mem_countDegrees A B, ?_⟩⟩
  · have : 1 ≤ 0 := h.2 ⟨{a}, Finset.card_singleton a, by
      simp only [plural, mem_inter_iff, mem_ofPred_eq, Finset.coe_singleton, singleton_subset_iff]
      exact ⟨ha, hb⟩⟩
    omega
  · rintro _ ⟨x, rfl, hA, hB⟩
    exact Nat.le_zero.2 <| Finset.card_eq_zero.2 <|
      Finset.eq_empty_of_forall_notMem fun a hx ↦ h a (hA hx) (hB hx)

/-- Under `*`, Kennedy's *zero A B* is never true ((72)): the degree property lacks `0`. -/
theorem not_maxIn_zero_countDegrees_sdiff (A B : Set α) :
    ¬ MaxIn {0} (countDegrees A (plural B \ {∅})) :=
  fun h ↦ zero_notMem_countDegrees_sdiff A B (maxIn_singleton.1 h).1

/-- Exhaustified *zero A B* is *no A B* ((40)). -/
theorem exhAgainst_zero_iff_no {A B : Set α} :
    exhAgainst (· < ·) (· ∈ countDegrees A (plural B)) 0 ↔ GQ.no A B :=
  maxIn_singleton_iff_exhAgainst.symm.trans maxIn_zero_countDegrees_iff

/-! ### Negative polarity items

*Zero* is a scalar licenser, the at least numeral below the exhaustivity operator and the numeral
exhaustified against the higher numerals above it, so the library's licensing applies to it as
stated in (53). -/

section Polarity

open PolarityItem (LicensingContext NonemptyPredicate)
open PolarityItem.LicensingContext

/-- *Zero* NP over a restrictor, the at least numeral and its exhaustification against the higher
numerals ((39), (40)). -/
def zero : LicensingContext :=
  ⟨.scalar ⟨⟨NonemptyPredicate, fun p ↦ p.ι → Prop, fun _ ↦ Prop,
      fun p B ↦ 0 ∈ countDegrees p.A (plural B)⟩,
    fun p B ↦ exhAgainst (· < ·) (· ∈ countDegrees p.A (plural B)) 0⟩, none⟩

/-- Above the exhaustivity operator *zero* is *no*, non-trivially downward entailing ((54a)). -/
theorem exhaustified_zero : zero.licenser.exhaustified = nobody.licenser := by
  simp only [zero, nobody, PolarityItem.Licenser.exhaustified]
  congr
  funext p B
  exact propext exhAgainst_zero_iff_no

/-- Below it *zero* is a tautology, downward and upward entailing at once ((54b)). -/
theorem isStrawsonUE_zero : zero.licenser.IsStrawsonUE :=
  fun p _ B _ _ ↦ zero_mem_countDegrees p.A B

/-- So *zero* licenses no negative polarity item, weak or strong. -/
@[simp] theorem not_licenses_zero (e : PolarityItem) : ¬ zero.Licenses e := by
  rintro (⟨_, _, h⟩ | ⟨h, _⟩ | ⟨h, _⟩)
  exacts [h.weak.2 isStrawsonUE_zero, h.elim, h.elim]

instance : DecidablePred zero.Licenses := fun e ↦ isFalse (not_licenses_zero e)

/-- Kennedy's *zero*, with its exactly meaning basic and so no exhaustivity operator to split its
meaning. -/
def kennedyZero : LicensingContext :=
  ⟨.classical ⟨NonemptyPredicate, fun p ↦ p.ι → Prop, fun _ ↦ Prop,
    fun p B ↦ MaxIn {0} (countDegrees p.A (plural B))⟩, none⟩

/-- Kennedy's *zero* is *no* ((73)), so it licenses what *no* licenses, strong items included,
against (13), (15) and (16) (Section 6.3). -/
theorem kennedyZero_eq_nobody : kennedyZero = nobody := by
  simp only [kennedyZero, nobody]
  congr
  funext p B
  exact propext maxIn_zero_countDegrees_iff

/-- The paper's licensers. -/
inductive Licenser
  | no | few | zero
  deriving DecidableEq, Repr

/-- The library's context for each licenser. -/
def Licenser.context : Licenser → LicensingContext
  | .no => .nobody
  | .few => .few
  | .zero => BylininaNouwen2018.zero

instance (L : Licenser) : DecidablePred L.context.Licenses := by
  cases L <;> dsimp only [Licenser.context] <;> infer_instance

/-- A sentence of the paper records its licenser, its polarity item as an entry of the English
fragment, and the judgment. -/
structure Row where
  licenser : Licenser
  item : PolarityItem
  judgment : Judgment

def Row.ofDatum (ex : Datum) : Option Row :=
  match ex.parse? "licenser"
      ([("no", .no), ("few", .few), ("zero", .zero)] : List (String × BylininaNouwen2018.Licenser)),
    ex.parse? "npi" [("in years", English.PolarityItems.inYears),
      ("ever", English.PolarityItems.ever), ("anything", English.PolarityItems.any),
      ("any", English.PolarityItems.any)] with
  | some L, some e => some ⟨L, e, ex.judgment⟩
  | _, _ => none

def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- Every judgment is the library's verdict: a sentence is acceptable exactly when its licenser
licenses its item. -/
theorem rows_predicted :
    ∀ r ∈ rows, (r.judgment = .acceptable ↔ r.licenser.context.Licenses r.item) := by
  decide

end Polarity

/-! ### Downward monotone degree quantifiers

A degree quantifier at a lower set, *fewer than ten* or *at most ten*, is downward monotone in its
scope under `×`, since `0` keeps the degree property nonempty, and not under `*` ((65), (66)). -/

theorem antitone_maxIn_countDegrees {U : Set ℕ} (hU : IsLowerSet U) {A : Set α} (hA : A.Finite) :
    Antitone fun B ↦ MaxIn U (countDegrees A (plural B)) := fun _ _ hB h ↦ by
  dsimp only at h ⊢
  rw [countDegrees_plural_eq_Iic (hA.inter_of_left _), maxIn_Iic] at h ⊢
  exact hU (ncard_le_ncard (inter_subset_inter_right A hB) (hA.inter_of_left _)) h

/-- Under `*`, *fewer than ten students passed* is false when no student passed. -/
theorem not_antitone_maxIn_countDegrees_sdiff :
    ¬ Antitone fun B : Set Unit ↦ MaxIn (Iio 10) (countDegrees univ (plural B \ {∅})) := by
  intro h
  obtain ⟨_, -, ⟨x, -, -, hx, hne⟩, -⟩ := h (empty_subset univ) ⟨1, by decide,
    ⟨{()}, rfl, subset_univ _, subset_univ _, by simp⟩,
    fun _ ⟨x, hx, _⟩ ↦ hx ▸ Finset.card_le_univ x⟩
  exact hne (Finset.eq_empty_of_forall_notMem fun a ha ↦ hx ha)

/-! ### Scope

Exhaustifying the lower bound at a site and raising Kennedy's quantifier to that site give the same
reading ((75), (76)), so the analyses differ only in the sites they reach. -/

section Scope

variable {Q : NP α} {μ : α → ℕ} {n : ℕ}

/-- Exhaustification above `Q` is the numeral raised over `Q`. -/
theorem exhAgainst_iff_highScope :
    exhAgainst (· < ·) (fun m ↦ Q fun x ↦ m ≤ μ x) n ↔ HighScope (MaxIn {n}) Q μ :=
  maxIn_singleton_iff_exhAgainst.symm

/-- Exhaustification below `Q` is the numeral in situ under `Q`. -/
theorem exhAgainst_iff_lowScope :
    (Q fun x ↦ exhAgainst (· < ·) (· ≤ μ x) n) ↔ LowScope (MaxIn {n}) Q μ := by
  simp only [LowScope, maxIn_singleton_iff_exhAgainst]; rfl

end Scope

/-- Over *every student* the split-scope reading (77b), that not every student read a book, is
true when one student read none and another four, while the reading (77a), that every student
read none, is false: the continuation (78) separates them. -/
theorem highScope_every_not_lowScope :
    HighScope (MaxIn {0}) (every fun _ ↦ True) (fun i : Fin 2 ↦ 4 * (i : ℕ)) ∧
      ¬ LowScope (MaxIn {0}) (every fun _ ↦ True) (fun i : Fin 2 ↦ 4 * (i : ℕ)) :=
  ⟨highScope_maxIn_singleton_every.2 ⟨fun _ _ ↦ Nat.zero_le _, fun _ hb ↦ hb ⟨0, trivial, rfl⟩⟩,
    fun h ↦ absurd (lowScope_maxIn.1 h 1 trivial) (by simp)⟩

end BylininaNouwen2018
