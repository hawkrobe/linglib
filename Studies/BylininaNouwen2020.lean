module

public import Linglib.Semantics.Degree.Quantifier
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Card
public import Studies.Partee1987
public import Studies.Spector2013

/-!
# Bylinina and Nouwen (2020): Numeral semantics

This file formalizes the survey of numeral meanings by Bylinina and Nouwen. Once the determiner
view is set aside, a bare numeral has been taken to denote a predicate counting the atoms of a
plurality, `λx. #x = n`, a number `n`, or a quantifier over degree properties, Kennedy's
`λP. max(P) = n`, and operators relate the three: the counting operator `MANY` takes the number to
the predicate ((22), (23)), the survey's `CARD` takes the predicate back ((24), (25)), and Partee's
`BE` and `IOTA` lower the quantifier to the number ((47)–(50)). Lowering forgets the upper bound,
so the lowered numeral, interpreted in situ, has an at least reading.

The views differ in where the exactly reading comes from. On the predicate and number views a
numeral with a distributive predicate is lower-bounded ((29)) and an exhaustivity operator
strengthens it ((32), (34)); on Kennedy's view the numeral is doubly bounded and takes scope by QR
((43)–(46)). At each scope site the two coincide, since exhaustifying the lower bound against the
higher numerals says that the numeral is the greatest degree of the property abstracted there,
which is what Kennedy's quantifier says of it. Above a possibility modal both give the strong
reading (36-b), Kennedy's (46), and above *some students* both give (39), a reading the sentence is
reported to lack (fn. 9 flags the judgement). The accounts differ in which sites they reach: the
Heim-Kennedy generalization (42) keeps degree operators below nominal quantifiers, and nothing keeps
a propositional `EXH` there.

The survey's proposal keeps the quantifier type and the lower bound: the numeral is the Montague
lift of the number ((52)), and an operator `MAX` turns it into Kennedy's quantifier ((53), (54)).
At the numeral's landing site `MAX` is exhaustification, so the strengthening moves with the
numeral and obeys (42). The lower bound has to be basic because of *zero* ((51)): with the empty
plurality in the domain, the lower-bound *zero A B* is a tautology, while Kennedy's *zero A B* is
*no A B*, which licenses negative polarity items that *zero* does not.

## Main results

* `maxIn_singleton_iff_exhAgainst`: Kennedy's quantifier at a degree property is the exhaustified
  lower bound there, at every scope site (`exhAgainst_iff_highScope`, `exhAgainst_iff_lowScope`).
* `exh_poss_iff_highScope`: the exhaustified possibility reading of Spector is Kennedy's (46).
* `MAX_individual_iff_exhAgainst`: `MAX` of the lifted number is exhaustification at its site.
* `maxIn_zero_countDegrees_iff`: Kennedy's *zero* is *no*.

## Implementation notes

* Degrees are natural numbers, a degree property is a `Set ℕ` and a degree quantifier a predicate
  on them. Kennedy's numeral is the substrate's `Degree.MaxIn {n}`, and its scope relative to a
  modal or nominal quantifier `Q` over a count `μ` is `Degree.LowScope` or `Degree.HighScope`.
* Pluralities are the finite sets of atoms, so the domain has the empty plurality: it is the full
  lattice `×Z` of Bylinina and Nouwen (2018), of which Link's `*Z` ((12)) is the nonempty part.
  The two agree on every numeral but *zero*.
* `EXH` is `Exhaustification.exhAgainst (· < ·)`, denying every higher numeral. On the lower sets
  that distributive predicates give (`isLowerSet_countDegrees_plural`) the higher numerals are the
  stronger alternatives of (32).

## TODO

The determiner view (Section 2), the Dutch *hoeven* data (26)–(28), and the polarity account of
*zero* in Bylinina and Nouwen (2018), which needs non-trivial downward entailment, are not
formalized.

## References

* [bylinina-nouwen-2020]
* [bylinina-nouwen-2018]
* [kennedy-2015]
* [partee-1987]
* [spector-2013]
* [heim-2000]
* [link-1983]
-/

@[expose] public section
namespace BylininaNouwen2020

open Reference Degree Exhaustification Quantifier Quantifier.GQ Quantifier.NP Set

variable {α : Type*}

/-! ### The modifier and number views

The modifier meaning of a numeral is the counting operator at its number, so the two views differ
only in whether the counting is built into the numeral or supplied by an operator. -/

/-- `MANY d` is the property of pluralities with `d` atoms, `λx. #x = d` ((22)). -/
def MANY (d : ℕ) : Set (Finset α) := Finset.card ⁻¹' {d}

theorem mem_MANY {d : ℕ} {x : Finset α} : x ∈ MANY d ↔ x.card = d := Iff.rfl

/-- `CARD P` is the number of atoms every plurality in `P` has, `ιd. ∀x[P(x) → #x = d]` ((24)). -/
noncomputable def CARD (P : Set (Finset α)) : Option ℕ := iota fun d ↦ ∀ x ∈ P, x.card = d

/-- `CARD` recovers the number a modifier meaning counts ((25)), given a plurality of that size. -/
theorem CARD_MANY {n : ℕ} (hn : ∃ x : Finset α, x.card = n) : CARD (MANY (α := α) n) = some n :=
  (iota_eq_some_iff _).2 ⟨fun _ hx ↦ hx, fun _ h ↦ let ⟨x, hx⟩ := hn; (h x hx).symm.trans hx⟩

/-- Numbers as classes of equinumerous pluralities ((17)) are faithful exactly when there are
pluralities of every size: on a finite domain every numeral beyond its size denotes the empty
property. -/
theorem MANY_injective_iff : Function.Injective (MANY (α := α)) ↔ Infinite α := by
  refine ⟨fun h ↦ not_finite_iff_infinite.1 fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have := Fintype.ofFinite α
    have key : ∀ k, MANY (α := α) (Fintype.card α + 1 + k) = ∅ := fun k ↦
      eq_empty_of_forall_notMem fun x hx ↦ by
        have := Finset.card_le_univ x; have := mem_MANY.1 hx; omega
    exact absurd (h ((key 0).trans (key 1).symm)) (by omega)
  · exact (preimage_injective.2 (Infinite.exists_subset_card_eq α)).comp singleton_injective

/-! ### Pluralities and the lower bound

A numeral with a distributive predicate is lower-bounded ((29)), since the degrees `d` such that
some `d` atoms of `A` are `B` form a lower set; with a collective predicate they need not
(fn. 8). -/

/-- The pluralities of members of `Z`, the sums `⊔X` of the subsets `X ⊆ Z`. -/
def plural (Z : Set α) : Set (Finset α) := {x | ↑x ⊆ Z}

/-- The degree property `λd. ∃x[#x = d ∧ ×A(x) ∧ C(x)]` that the numeral of *n A C* quantifies
over after QR. -/
def countDegrees (A : Set α) (C : Set (Finset α)) : Set ℕ :=
  {d | ∃ x ∈ MANY d, x ∈ plural A ∩ C}

theorem isLowerSet_countDegrees_plural (A B : Set α) : IsLowerSet (countDegrees A (plural B)) := by
  rintro d e hed ⟨x, rfl, hA, hB⟩
  obtain ⟨y, hyx, rfl⟩ := Finset.exists_subset_card_eq hed
  exact ⟨y, rfl, (Finset.coe_subset.2 hyx).trans hA, (Finset.coe_subset.2 hyx).trans hB⟩

/-- If only the plurality `s` lifted the piano together, the degree property holds at `#s`
alone, so the numeral is not lower-bounded (fn. 8). -/
theorem countDegrees_singleton {A : Set α} {s : Finset α} (hs : ↑s ⊆ A) :
    countDegrees A {s} = {s.card} :=
  Set.ext fun _ ↦ ⟨fun ⟨_, hx, _, hxs⟩ ↦ (hxs ▸ hx : s.card = _).symm,
    fun h ↦ ⟨s, h.symm, hs, rfl⟩⟩

/-- With finitely many atoms in `A ∩ B` the degree property is the lower closure of their number,
the measured degree property of `Degree.LowScope`. -/
theorem countDegrees_plural_eq_Iic {A B : Set α} (h : (A ∩ B).Finite) :
    countDegrees A (plural B) = Iic (A ∩ B).ncard := by
  ext d
  simp only [countDegrees, plural, MANY, mem_inter_iff, mem_ofPred_eq, mem_preimage,
    mem_singleton_iff, mem_Iic, ← subset_inter_iff, ← h.subset_toFinset, ncard_eq_toFinset_card _ h]
  exact ⟨fun ⟨x, hx, hs⟩ ↦ hx ▸ Finset.card_le_card hs,
    fun hd ↦ let ⟨y, hy, hc⟩ := Finset.exists_subset_card_eq hd; ⟨y, hc, hy⟩⟩

/-! ### Exhaustification and degree quantifiers

Exhaustifying the lower bound at a scope site and raising Kennedy's quantifier to that site give
the same reading, so the accounts differ only in the sites available to them. -/

/-- Kennedy's quantifier holds of a degree property when the lower bound, exhaustified against the
higher numerals, does: both say that `n` is its greatest degree. -/
theorem maxIn_singleton_iff_exhAgainst {D : Type*} [LinearOrder D] {P : Set D} {n : D} :
    MaxIn {n} P ↔ exhAgainst (· < ·) (· ∈ P) n :=
  maxIn_singleton.trans <| and_congr_right' ⟨fun h _ hm hmP ↦ (h hmP).not_gt hm,
    fun h m hmP ↦ not_lt.1 fun hm ↦ h m hm hmP⟩

section Scope

variable {Q : NP α} {μ : α → ℕ} {n : ℕ}

/-- `EXH` above `Q` is the numeral raised over `Q`: (36-b) and Kennedy's (46) over a possibility
modal, (39) over *some students*. -/
theorem exhAgainst_iff_highScope :
    exhAgainst (· < ·) (fun m ↦ Q fun x ↦ m ≤ μ x) n ↔ HighScope (MaxIn {n}) Q μ :=
  maxIn_singleton_iff_exhAgainst.symm

/-- `EXH` below `Q` is the numeral in situ under `Q`: (36-a) under a possibility modal, and the
reading that *some students answered exactly `n` questions* under *some students* ((38)). -/
theorem exhAgainst_iff_lowScope :
    (Q fun x ↦ exhAgainst (· < ·) (· ≤ μ x) n) ↔ LowScope (MaxIn {n}) Q μ := by
  simp only [LowScope, maxIn_singleton_iff_exhAgainst]; rfl

/-- Spector's wide-scope exhaustification over a possibility modal, the reading (36-b), is
Kennedy's numeral raised over the modal ((46)). -/
theorem exh_poss_iff_highScope {W : Type*} {R : W → Prop} {count : W → ℕ} :
    exhAgainst (· < ·) (fun m ↦ Spector2013.poss (count '' {w | R w})
      (Comparison.ge.interval m)) n ↔ HighScope (MaxIn {n}) (GQ.some R) count := by
  simp only [Spector2013.poss, exists_mem_image, Comparison.interval_ge, mem_Ici, mem_ofPred_eq]
  exact exhAgainst_iff_highScope (Q := GQ.some R)

/-- The exactly reading under the possibility modal, (36-a), is Kennedy's numeral in situ. -/
theorem poss_eq_iff_lowScope {W : Type*} {R : W → Prop} {count : W → ℕ} :
    Spector2013.poss (count '' {w | R w}) (Comparison.eq.interval n) ↔
      LowScope (MaxIn {n}) (GQ.some R) count := by
  simp only [Spector2013.poss, exists_mem_image, Comparison.interval_eq, lowScope_maxIn]
  rfl

/-- Over *some students* the high reading (39) is strictly stronger than the low one: it entails
the low one (`Degree.lowScope_some_of_highScope`), and a student answering `n` questions with
another answering `n + 1` makes the low reading true and (39) false. -/
theorem lowScope_some_not_highScope (n : ℕ) :
    LowScope (MaxIn {n}) (GQ.some fun _ ↦ True) (fun i : Fin 2 ↦ n + i) ∧
      ¬ HighScope (MaxIn {n}) (GQ.some fun _ ↦ True) (fun i : Fin 2 ↦ n + i) :=
  ⟨lowScope_maxIn.2 ⟨0, trivial, rfl⟩, fun h ↦ absurd
    ((highScope_maxIn_singleton_some.1 h).2 ⟨1, trivial, rfl⟩) (by simp)⟩

end Scope

/-! ### Lowering

`BE` and `IOTA` take Kennedy's quantifier to the number as they take the lift of an entity to the
entity ((48)–(50)), and send it where they send the lower-bound quantifier. -/

/-- `BE` lowers the exactly-reading quantifier to the singleton of its number ((49)). -/
theorem BE_maxIn_singleton (n : ℕ) : BE (MaxIn {n}) = ident n :=
  funext fun x ↦ propext (maxIn_singleton.trans
    ⟨fun h ↦ (h.1 : n = x).symm, fun h ↦ h ▸ isGreatest_singleton⟩)

/-- Lowering forgets the upper bound: `BE` sends the exactly-reading quantifier where it sends the
lower-bound one. -/
theorem BE_maxIn_singleton_eq_BE_individual (n : ℕ) : BE (MaxIn {n}) = BE (individual n) := by
  rw [BE_maxIn_singleton, BE_individual]

/-- `IOTA(BE(twelve)) = 12` ((50)), as `IOTA(BE(λP.P(Mary))) = Mary` ((48)). -/
theorem iota_BE_maxIn_singleton (n : ℕ) : iota (BE (MaxIn {n})) = some n := by
  rw [BE_maxIn_singleton_eq_BE_individual]; exact Partee1987.iota_BE_lift n

/-- The exactly-reading quantifier determines the numeral, since lowering recovers it. -/
theorem maxIn_singleton_injective : Function.Injective fun n : ℕ ↦ MaxIn {n} :=
  fun a b (h : MaxIn {a} = MaxIn {b}) ↦
    ident_injective (by rw [← BE_maxIn_singleton, ← BE_maxIn_singleton, h])

/-! ### The survey's proposal

The empty slot in the type landscape is a lower-bound degree quantifier, the Montague lift
`individual n` of the number ((52)), from which `MAX` derives the exactly reading ((53), (54)). -/

/-- `MAX D` holds of the degree properties whose maximum lies in every member of `D`, as in
`λD λP. max(P) ∈ ∩D` ((53)). -/
def MAX (D : Set (Set ℕ)) : Set ℕ → Prop := MaxIn (⋂₀ D)

/-- `MAX` takes the lower-bound quantifier to Kennedy's ((54)), since the properties containing
`n` intersect to `{n}`. -/
theorem MAX_individual (n : ℕ) : MAX (individual n) = MaxIn {n} := by
  rw [MAX, sInter_individual]

/-- At its landing site `MAX` of the lower-bound quantifier is its exhaustification against the
higher numerals, a strengthening that moves with the numeral. -/
theorem MAX_individual_iff_exhAgainst {n : ℕ} {P : Set ℕ} :
    MAX (individual n) P ↔ exhAgainst (· < ·) (individual · P) n := by
  rw [MAX_individual]; exact maxIn_singleton_iff_exhAgainst

/-- The exactly-reading quantifier is strictly stronger than the lower-bound one, so `MAX` does
work: `{n, n + 1}` contains `n` without `n` being its greatest element. -/
theorem maxIn_singleton_lt_individual (n : ℕ) : MaxIn {n} < (individual n : Set ℕ → Prop) :=
  lt_of_le_not_ge (fun _ h ↦ (maxIn_singleton.1 h).1) fun h ↦
    absurd ((maxIn_singleton.1 (h {n, n + 1} (Or.inl rfl))).2 (Or.inr rfl)) (by omega)

/-- At its lower bound *zero A B* is a tautology, the empty plurality having zero atoms and being
a plurality of every predicate. -/
theorem individual_zero_countDegrees (A B : Set α) : individual 0 (countDegrees A (plural B)) :=
  ⟨∅, Finset.card_empty, by simp [plural]⟩

/-- Kennedy's *zero A B*, and so `MAX` of the lower-bound *zero*, is *no A B* ((51)). -/
theorem maxIn_zero_countDegrees_iff {A B : Set α} :
    MaxIn {0} (countDegrees A (plural B)) ↔ GQ.no A B := by
  refine maxIn_singleton.trans ⟨fun h a ha hb ↦ ?_, fun h ↦ ⟨individual_zero_countDegrees A B, ?_⟩⟩
  · have : 1 ≤ 0 := h.2 ⟨{a}, Finset.card_singleton a, by
      simp only [plural, mem_inter_iff, mem_ofPred_eq, Finset.coe_singleton, singleton_subset_iff]
      exact ⟨ha, hb⟩⟩
    omega
  · rintro _ ⟨x, rfl, hA, hB⟩
    exact Nat.le_zero.2 <| Finset.card_eq_zero.2 <|
      Finset.eq_empty_of_forall_notMem fun a hx ↦ h a (hA hx) (hB hx)

end BylininaNouwen2020
