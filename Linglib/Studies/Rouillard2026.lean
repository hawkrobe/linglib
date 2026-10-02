module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Linglib.Core.Order.Interval
public import Linglib.Core.Order.IntervalContent
public import Linglib.Semantics.Alternatives.Extremum
public import Linglib.Semantics.Aspect.SubintervalProperty
public import Linglib.Semantics.Polarity.Basic

/-!
# Rouillard 2026: temporal *in*-adverbials and maximal informativity

A temporal *in*-adverbial measures either an event, as in *Mary wrote up a paper in three days*
(an E-TIA), or a gap in which no event occurs, as in *Mary hasn't been sick in three days* (a
G-TIA). E-TIAs take telic but not atelic VPs, and G-TIAs are polarity items confined to negated
perfects. Rouillard derives both from the Maximal Informativity Principle: the numeral must be
able to be the maximally informative value of the property of numbers its constituent denotes.
An atelic VP has the subinterval property, so its E-TIA property does not depend on the numeral.
The perfect quantifies over open spans ending at speech time while run times are closed, so over
dense time no open span including a run time is smallest, though one excluding it is largest;
of the eight readings of *Mary has been sick in three days* and its negation, exactly one
survives.

## Main definitions

* `TimeMeasure`: an additive positive measure of intervals that trims and extends.
* `IsMIPLicensed`: licensing by maximal informativity, after Fox and Hackl.
* `eTIA`: the E-TIA property.
* `gTIA`: the G-TIA property.

## Main results

* `not_isMIPLicensed_eTIA`: an atelic VP does not license an E-TIA.
* `not_isMIPLicensed_gTIA`: a positive G-TIA is not licensed over dense time.
* `isMIPLicensed_gTIANeg`: a negated G-TIA is licensed.
* `table1_survivor`: the one reading of Table 1 that survives.

## Implementation notes

* Numerals live in an ordered additive monoid `α` measuring closed intervals of a linearly
  ordered time `T`. The subinterval property is the closed one of
  `Aspect/SubintervalProperty.lean`, the paper's (111).

## References

* [rouillard-2026]
* [fox-hackl-2006]
-/

@[expose] public section

namespace Rouillard2026

open Event (τ)

open Alternatives Aspect Core.Order NonemptyInterval Set

variable {W T E α : Type*} [LinearOrder T] [Event.TemporalTrace E T]
  [AddCommMonoid α] [LinearOrder α] [IsOrderedCancelAddMonoid α]

/-! ### Measuring times (§2.2) -/

/-- A temporal measure is an interval content, additive and positive, (6) and (7), such that a span
ending at a fixed time can be trimmed or extended to any measure, the right-anchored form of (13)
and of the surjectivity onto the positive numbers. -/
class TimeMeasure (μ : NonemptyInterval T → α) : Prop extends IsIntervalContent μ where
  /-- Any smaller measure is attained by a final subinterval. -/
  trim : ∀ (i : NonemptyInterval T) (m : α), m ≤ μ i → ∃ j, j.finalSubinterval i ∧ μ j = m
  /-- Any larger measure is attained by extending to the left. -/
  extend : ∀ (i : NonemptyInterval T) (m : α), μ i ≤ m → ∃ j, i.finalSubinterval j ∧ μ j = m

/-- `InOpen t i` says that the closed time `t` lies inside the open counterpart `o(i)` of `i`,
(15b). -/
def InOpen (t i : NonemptyInterval T) : Prop := i.fst < t.fst ∧ t.snd < i.snd

theorem inOpen_iff_subset_Ioo {t i : NonemptyInterval T} :
    InOpen t i ↔ (t : Set T) ⊆ Ioo i.fst i.snd := by
  rw [coe_def]; exact (Icc_subset_Ioo_iff t.fst_le_snd).symm

theorem InOpen.mono {t t' i : NonemptyInterval T} (h : t' ≤ t) (ht : InOpen t i) : InOpen t' i :=
  ⟨ht.1.trans_le (le_def.1 h).1, (le_def.1 h).2.trans_lt ht.2⟩

theorem InOpen.of_finalSubinterval {t i j : NonemptyInterval T} (h : i.finalSubinterval j)
    (ht : InOpen t i) : InOpen t j :=
  ⟨(le_def.1 h.1).1.trans_lt ht.1, h.2 ▸ ht.2⟩

/-! ### The Maximal Informativity Principle (§4.1.3) -/

/-- A property of numbers is licensed when at some world the numeral is its unique maximally
informative value, (92) with (75). -/
def IsMIPLicensed {N : Type*} (φ : N → Set W) : Prop := ∃ w, ∃! n, IsMaxInf φ n w

/-- A property that does not depend on the numeral is not licensed, the information collapse. -/
theorem not_isMIPLicensed_of_forall_eq {N : Type*} [Nontrivial N] {φ : N → Set W}
    (h : ∀ n m, φ n = φ m) : ¬ IsMIPLicensed φ := by
  rintro ⟨w, n, hn, huniq⟩
  obtain ⟨m, hm⟩ := exists_ne n
  obtain ⟨hnw, hmin⟩ := isMaxInf_iff.1 hn
  exact hm (huniq m (isMaxInf_iff.2 ⟨h n m ▸ hnw, fun k hk => h n m ▸ hmin k hk⟩))

/-- An upward scalar property with no least true value is not licensed. -/
theorem not_isMIPLicensed_of_not_isLeast {N : Type*} [LinearOrder N] {φ : N → Set W}
    (hφ : Monotone φ) (h : ∀ w n, ¬ IsLeast {m | w ∈ φ m} n) : ¬ IsMIPLicensed φ := by
  rintro ⟨w, n, hn, huniq⟩
  obtain ⟨hnw, hmin⟩ := isMaxInf_iff.1 hn
  refine h w n ⟨hnw, fun m hm => not_lt.1 fun hlt => ?_⟩
  exact hlt.ne (huniq m (isMaxInf_iff.2 ⟨hm, fun k hk => (hφ hlt.le).trans (hmin k hk)⟩))

/-- A strictly downward scalar property with a greatest true value at some world is licensed. -/
theorem isMIPLicensed_of_isGreatest {N : Type*} [LinearOrder N] {φ : N → Set W}
    (hφ : StrictAnti φ) {w : W} (h : ∃ n, IsGreatest {m | w ∈ φ m} n) : IsMIPLicensed φ := by
  obtain ⟨n, hn⟩ := (hasMaxInf_iff_isGreatest hφ).2 h
  refine ⟨w, n, hn, fun m hm => hφ.injective (subset_antisymm ?_ ?_)⟩
  exacts [(isMaxInf_iff.1 hm).2 n (isMaxInf_iff.1 hn).1,
    (isMaxInf_iff.1 hn).2 m (isMaxInf_iff.1 hm).1]

/-- A strictly upward scalar property with a least true value at some world is licensed. -/
theorem isMIPLicensed_of_isLeast {N : Type*} [LinearOrder N] {φ : N → Set W}
    (hφ : StrictMono φ) {w : W} (h : ∃ n, IsLeast {m | w ∈ φ m} n) : IsMIPLicensed φ := by
  obtain ⟨n, hn⟩ := (hasMaxInf_iff_isLeast hφ).2 h
  refine ⟨w, n, hn, fun m hm => hφ.injective (subset_antisymm ?_ ?_)⟩
  exacts [(isMaxInf_iff.1 hm).2 n (isMaxInf_iff.1 hn).1,
    (isMaxInf_iff.1 hn).2 m (isMaxInf_iff.1 hm).1]

/-! ### E-TIAs (§4.1) -/

variable (μ : NonemptyInterval T → α) [TimeMeasure μ]

/-- The E-TIA property (76) holds of `n` when `n` measures a time including a `Q`-event, `Q` being
the event predicate the rest of the LF supplies ((78) for the simple past). -/
def eTIA (Q : W → E → Prop) (n : α) : Set W :=
  {w | ∃ t, μ t = n ∧ ∃ e, Q w e ∧ τ e ≤ t}

omit [IsOrderedCancelAddMonoid α] in
/-- The E-TIA property is upward scalar, since a longer time still includes the event. -/
theorem eTIA_monotone (Q : W → E → Prop) : Monotone (eTIA μ Q) := by
  rintro n m hnm w ⟨t, rfl, e, he, het⟩
  obtain ⟨j, hj, hjm⟩ := TimeMeasure.extend t m hnm
  exact ⟨j, hjm, e, he, het.trans hj.1⟩

omit [IsOrderedCancelAddMonoid α] in
/-- Under the subinterval property the E-TIA property does not depend on the numeral, the
information collapse of (83). -/
theorem eTIA_eq_of_hasSubintervalProperty {Q : W → E → Prop}
    (hQ : HasSubintervalProperty Q) (n m : α) : eTIA μ Q n = eTIA μ Q m := by
  suffices h : ∀ n m w, w ∈ eTIA μ Q n → w ∈ eTIA μ Q m from
    Set.ext fun w => ⟨h n m w, h m n w⟩
  rintro n m w ⟨t, rfl, e, he, het⟩
  rcases le_total m (μ (τ e)) with hle | hge
  · obtain ⟨j, hj, hjm⟩ := TimeMeasure.trim (τ e) m hle
    obtain ⟨e', he'τ, he'⟩ := hasSubintervalProperty_iff_witnesses.1 hQ e w he j hj.1
    exact ⟨j, hjm, e', he', he'τ.le⟩
  · obtain ⟨j, hj, hjm⟩ := TimeMeasure.extend (τ e) m hge
    exact ⟨j, hjm, e, he, hj.1⟩

omit [IsOrderedCancelAddMonoid α] in
/-- With an atelic VP, as in *Mary was sick in three days*, the E-TIA is not licensed. -/
theorem not_isMIPLicensed_eTIA [Nontrivial α] {Q : W → E → Prop}
    (hQ : HasSubintervalProperty Q) : ¬ IsMIPLicensed (eTIA μ Q) :=
  not_isMIPLicensed_of_forall_eq (eTIA_eq_of_hasSubintervalProperty μ hQ)

/-- In the telic case, at a world whose shortest `Q`-event is `e₀`, the least true numeral is its
duration. -/
theorem isLeast_eTIA {Q : W → E → Prop} {w : W} {e₀ : E} (h₀ : Q w e₀)
    (hmin : ∀ e, Q w e → μ (τ e₀) ≤ μ (τ e)) : IsLeast {n | w ∈ eTIA μ Q n} (μ (τ e₀)) :=
  ⟨⟨τ e₀, rfl, e₀, h₀, le_rfl⟩, fun _ ⟨_, ht, e, he, het⟩ =>
    ht ▸ (hmin e he).trans (IsIntervalContent.monotone μ het)⟩

/-- In *Mary wrote up a paper in three days*, when worlds differ in the event's duration, a telic
VP is licensed at the world whose shortest event lasts the numeral's measure. -/
theorem isMIPLicensed_eTIA {Q : W → E → Prop} (hφ : StrictMono (eTIA μ Q)) {w : W}
    {e₀ : E} (h₀ : Q w e₀) (hmin : ∀ e, Q w e → μ (τ e₀) ≤ μ (τ e)) :
    IsMIPLicensed (eTIA μ Q) :=
  isMIPLicensed_of_isLeast hφ ⟨_, isLeast_eTIA μ h₀ hmin⟩

/-! ### G-TIAs (§4.2) -/

/-- The G-TIA property (101) holds of `n` when the open prior time span of measure `n` ending at
`s` includes
the closed run-time of a `P`-event. -/
def gTIA (P : W → E → Prop) (s : T) (n : α) : Set W :=
  {w | ∃ i : NonemptyInterval T, i.snd = s ∧ μ i = n ∧ ∃ e, P w e ∧ InOpen (τ e) i}

/-- `gTIANeg` is the negated G-TIA property (104). -/
def gTIANeg (P : W → E → Prop) (s : T) (n : α) : Set W := (gTIA μ P s n)ᶜ

omit [IsOrderedCancelAddMonoid α] in
theorem gTIA_monotone (P : W → E → Prop) (s : T) : Monotone (gTIA μ P s) := by
  rintro n m hnm w ⟨i, rfl, rfl, e, he, hei⟩
  obtain ⟨j, hj, hjm⟩ := TimeMeasure.extend i m hnm
  exact ⟨j, hj.2.symm, hjm, e, he, hei.of_finalSubinterval hj⟩

omit [IsOrderedCancelAddMonoid α] in
theorem gTIANeg_antitone (P : W → E → Prop) (s : T) : Antitone (gTIANeg μ P s) :=
  fun _ _ h => compl_subset_compl.2 (gTIA_monotone μ P s h)

/-- Under density every witnessing open span shrinks to a strictly smaller one, still
positive in measure, that includes the same run-time (§4.2.2). -/
theorem exists_lt_of_mem_gTIA [DenselyOrdered T] {P : W → E → Prop} {s : T} {w : W}
    {n : α} (h : w ∈ gTIA μ P s n) : ∃ m, 0 < m ∧ m < n ∧ w ∈ gTIA μ P s m := by
  obtain ⟨i, rfl, rfl, e, he, hei⟩ := h
  obtain ⟨l, hil, hle⟩ := exists_between hei.1
  have hls : l < i.snd := (hle.trans_le (τ e).fst_le_snd).trans hei.2
  refine ⟨μ ⟨⟨l, i.snd⟩, hls.le⟩, IsIntervalContent.positive l i.snd hls, ?_,
    ⟨⟨l, i.snd⟩, hls.le⟩, rfl, rfl, e, he, hle, hei.2⟩
  exact IsIntervalContent.measure_lt_of_left_lt μ hil hls.le

/-- There is no smallest open span including a closed run-time. -/
theorem not_isLeast_gTIA [DenselyOrdered T] (P : W → E → Prop) (s : T) (w : W) (n : α) :
    ¬ IsLeast {m | w ∈ gTIA μ P s m} n := fun ⟨hn, hlb⟩ =>
  let ⟨_, _, hmn, hm⟩ := exists_lt_of_mem_gTIA μ hn
  hmn.not_ge (hlb hm)

/-- A positive G-TIA, as in *Mary has been sick in three days*, is not licensed over dense time. -/
theorem not_isMIPLicensed_gTIA [DenselyOrdered T] (P : W → E → Prop) (s : T) :
    ¬ IsMIPLicensed (gTIA μ P s) :=
  not_isMIPLicensed_of_not_isLeast (gTIA_monotone μ P s) (not_isLeast_gTIA μ P s)

/-- When every `P`-event starts by `l₀`, and one starts exactly at `l₀` and ends before `s`,
the open span from `l₀` to `s` is the largest excluding every `P`-event (§4.2.2): the greatest
true numeral of the negated property is its measure. -/
theorem isGreatest_gTIANeg {P : W → E → Prop} {s : T} {w : W} {l₀ : T}
    (hall : ∀ e, P w e → (τ e).fst ≤ l₀) (hwit : ∃ e, P w e ∧ (τ e).fst = l₀ ∧ (τ e).snd < s)
    (hl : l₀ ≤ s) : IsGreatest {n | w ∈ gTIANeg μ P s n} (μ ⟨⟨l₀, s⟩, hl⟩) := by
  obtain ⟨e₀, he₀, hfst, hsnd⟩ := hwit
  refine ⟨fun ⟨i, his, hiμ, e, he, hei⟩ => ?_, fun n hn => ?_⟩
  · have h₁ : i.fst < l₀ := hei.1.trans_le (hall e he)
    have hi : (⟨⟨i.fst, s⟩, h₁.le.trans hl⟩ : NonemptyInterval T) = i :=
      NonemptyInterval.ext (Prod.ext rfl his.symm)
    have := IsIntervalContent.measure_lt_of_left_lt μ h₁ hl
    rw [hi, hiμ] at this
    exact lt_irrefl _ this
  · refine not_lt.1 fun hlt => ?_
    obtain ⟨j, hj, hjn⟩ := TimeMeasure.extend ⟨⟨l₀, s⟩, hl⟩ n hlt.le
    have hjs : j.snd = s := hj.2.symm
    have hjl : j.fst < l₀ := by
      rcases (le_def.1 hj.1).1.lt_or_eq with h | h
      · exact h
      · have hjeq : j = ⟨⟨l₀, s⟩, hl⟩ := NonemptyInterval.ext (Prod.ext h hjs)
        exact absurd (hjeq ▸ hjn).symm hlt.ne'
    exact hn ⟨j, hjs, hjn, e₀, he₀, hfst ▸ hjl, hsnd.trans_eq hjs.symm⟩

/-- In *Mary hasn't been sick in three days*, when worlds separate the gap's length, a negated
G-TIA is licensed at the world where the last event abuts the span. -/
theorem isMIPLicensed_gTIANeg {P : W → E → Prop} {s : T} (hφ : StrictAnti (gTIANeg μ P s))
    {w : W} {l₀ : T} (hall : ∀ e, P w e → (τ e).fst ≤ l₀)
    (hwit : ∃ e, P w e ∧ (τ e).fst = l₀ ∧ (τ e).snd < s) (hl : l₀ ≤ s) :
    IsMIPLicensed (gTIANeg μ P s) :=
  isMIPLicensed_of_isGreatest hφ ⟨_, isGreatest_gTIANeg μ hall hwit hl⟩

/-! ### The rational model -/

/-- `ratLength` measures an interval of rational time by its length. -/
def ratLength (i : NonemptyInterval ℚ) : ℚ≥0 := ⟨i.snd - i.fst, sub_nonneg.2 i.fst_le_snd⟩

instance : TimeMeasure ratLength where
  additive a b c _ _ := NNRat.ext (by show c - a = (b - a) + (c - b); ring)
  positive a b h := by rw [← NNRat.coe_pos]; show (0 : ℚ) < b - a; linarith
  trim i m h := by
    have hm : (m : ℚ) ≤ i.snd - i.fst := NNRat.coe_le_coe.2 h
    refine ⟨⟨(i.snd - m, i.snd), by linarith [m.coe_nonneg]⟩,
      ⟨le_def.2 ⟨by linarith, le_rfl⟩, rfl⟩, NNRat.ext ?_⟩
    show i.snd - (i.snd - (m : ℚ)) = m
    ring
  extend i m h := by
    have hm : i.snd - i.fst ≤ (m : ℚ) := NNRat.coe_le_coe.2 h
    refine ⟨⟨(i.snd - m, i.snd), by linarith [m.coe_nonneg]⟩,
      ⟨le_def.2 ⟨by linarith, le_rfl⟩, rfl⟩, NNRat.ext ?_⟩
    show i.snd - (i.snd - (m : ℚ)) = m
    ring

/-- The blocking theorem's hypotheses are jointly satisfiable at rational time. -/
example (P : W → NonemptyInterval ℚ → Prop) (s : ℚ) : ¬ IsMIPLicensed (gTIA ratLength P s) :=
  not_isMIPLicensed_gTIA ratLength P s

/-! ### Table 1 (§5.1.1)

The four readings of *Mary has been sick in three days* — E- or G-TIA under an E- or U-perfect
(perfective or imperfective aspect) — and their negations, over the positive numerals. -/

/-- The E-perfect hands an E-TIA the event predicate (114) of a `P`-event inside an open span
ending at `s`. -/
def ePerfFrame (P : W → E → Prop) (s : T) (w : W) (e : E) : Prop :=
  P w e ∧ ∃ i : NonemptyInterval T, i.snd = s ∧ InOpen (τ e) i

/-- The U-perfect hands an E-TIA the event predicate (117) of a `P`-event including a nondegenerate
open span ending at `s`. -/
def uPerfFrame (P : W → E → Prop) (s : T) (w : W) (e : E) : Prop :=
  P w e ∧ ∃ l < s, Ioo l s ⊆ (τ e : Set T)

/-- The G-TIA property under a U-perfect, (122), holds when some nondegenerate open span ending at
`s` lies inside a `P`-event and inside a time of measure `n`. -/
def uPerfGTIA (P : W → E → Prop) (s : T) (n : α) : Set W :=
  {w | ∃ i : NonemptyInterval T, i.fst < i.snd ∧ i.snd = s ∧ (∃ t, μ t = n ∧ i ≤ t) ∧
    ∃ e, P w e ∧ Ioo i.fst i.snd ⊆ (τ e : Set T)}

/-- The E-perfect frame inherits the subinterval property. -/
theorem hasSubintervalProperty_ePerfFrame {P : W → E → Prop} {s : T}
    (hP : HasSubintervalProperty P) : HasSubintervalProperty (ePerfFrame P s) :=
  hasSubintervalProperty_iff_witnesses.2 fun e w ⟨he, i, his, hei⟩ t ht =>
    let ⟨e', he'τ, he'⟩ := hasSubintervalProperty_iff_witnesses.1 hP e w he t ht
    ⟨e', he'τ, he', i, his, he'τ ▸ hei.mono ht⟩

/-- A span of positive measure is nondegenerate. -/
private theorem fst_lt_snd_of_pos {i : NonemptyInterval T} (h : 0 < μ i) : i.fst < i.snd :=
  lt_of_le_of_ne i.fst_le_snd fun h' => h.ne' (IsIntervalContent.eq_zero_of_fst_eq_snd μ h')

/-- For positive numerals the U-perfect E-TIA property (117) collapses to (118) and does not
depend on the numeral. -/
theorem eTIA_uPerfFrame_eq [DenselyOrdered T] {P : W → E → Prop} {s : T}
    (hP : HasSubintervalProperty P) {n m : α} (hn : 0 < n) (hm : 0 < m) :
    eTIA μ (uPerfFrame P s) n = eTIA μ (uPerfFrame P s) m := by
  suffices h : ∀ n m : α, 0 < m → ∀ w, w ∈ eTIA μ (uPerfFrame P s) n →
      w ∈ eTIA μ (uPerfFrame P s) m from Set.ext fun w => ⟨h n m hm w, h m n hn w⟩
  rintro n m hm w ⟨t, rfl, e, ⟨he, l, hls, hle⟩, het⟩
  rw [coe_def] at hle
  have hel : (τ e).toProd.1 ≤ l := not_lt.1 fun h => by
    obtain ⟨m, hlm, hm⟩ := exists_between (lt_min h hls)
    exact ((hle ⟨hlm, hm.trans_le (min_le_right _ _)⟩).1.trans_lt
      (hm.trans_le (min_le_left _ _))).false
  have hse : s ≤ (τ e).toProd.2 := not_lt.1 fun h => by
    obtain ⟨m, hm, hms⟩ := exists_between (max_lt h hls)
    exact ((le_max_left _ _).trans_lt hm).not_ge
      (hle ⟨(le_max_right _ _).trans_lt hm, hms⟩).2
  have hpos : 0 < μ ⟨⟨l, s⟩, hls.le⟩ := IsIntervalContent.positive l s hls
  obtain ⟨j, hj, hjμ⟩ := TimeMeasure.trim ⟨⟨l, s⟩, hls.le⟩ (min m (μ ⟨⟨l, s⟩, hls.le⟩))
    (min_le_right _ _)
  have hjpos : 0 < μ j := hjμ ▸ lt_min hm hpos
  have hjs : j.snd = s := hj.2
  have hje : j ≤ τ e := hj.1.trans (le_def.2 ⟨hel, hse⟩)
  obtain ⟨e', he'τ, he'⟩ := hasSubintervalProperty_iff_witnesses.1 hP e w he j hje
  obtain ⟨t', ht', ht'μ⟩ := TimeMeasure.extend j m (hjμ ▸ min_le_left _ _)
  refine ⟨t', ht'μ, e', ⟨he', j.fst, hjs ▸ fst_lt_snd_of_pos μ hjpos, ?_⟩, he'τ ▸ ht'.1⟩
  rw [he'τ, coe_def, ← hjs]
  exact Ioo_subset_Icc_self

/-- For positive numerals the U-perfect G-TIA property (122) collapses to (123) and does not
depend on the numeral. -/
theorem uPerfGTIA_eq {P : W → E → Prop} {s : T} {n m : α} (hn : 0 < n) (hm : 0 < m) :
    uPerfGTIA μ P s n = uPerfGTIA μ P s m := by
  suffices h : ∀ n m : α, 0 < m → ∀ w, w ∈ uPerfGTIA μ P s n → w ∈ uPerfGTIA μ P s m from
    Set.ext fun w => ⟨h n m hm w, h m n hn w⟩
  rintro n m hm w ⟨i, hi, rfl, -, e, he, hei⟩
  have hpos : 0 < μ i := IsIntervalContent.positive' μ hi
  obtain ⟨j, hj, hjμ⟩ := TimeMeasure.trim i (min m (μ i)) (min_le_right _ _)
  have hjpos : 0 < μ j := hjμ ▸ lt_min hm hpos
  obtain ⟨t, ht, htμ⟩ := TimeMeasure.extend j m (hjμ ▸ min_le_left _ _)
  refine ⟨j, fst_lt_snd_of_pos μ hjpos, hj.2, ⟨t, htμ, ht.1⟩, e, he, ?_⟩
  rw [hj.2]
  exact (Ioo_subset_Ioo_left (le_def.1 hj.1).1).trans hei

/-- An `Adverbial` is event-level or gap-level. -/
inductive Adverbial | event | gap
  deriving DecidableEq

/-- A `Viewpoint` is perfective (E-perfect) or imperfective (U-perfect) aspect under the perfect. -/
inductive Viewpoint | pfv | impv
  deriving DecidableEq

/-- `positiveReading` gives the four positive readings of *Mary has been sick in three days*. -/
def positiveReading (P : W → E → Prop) (s : T) : Adverbial → Viewpoint → α → Set W
  | .event, .pfv => eTIA μ (ePerfFrame P s)
  | .event, .impv => eTIA μ (uPerfFrame P s)
  | .gap, .pfv => gTIA μ P s
  | .gap, .impv => uPerfGTIA μ P s

/-- `reading` gives a cell of Table 1 over the positive numerals, the positive reading under the
row's polarity. -/
def reading (P : W → E → Prop) (s : T) (pol : Polarity) (a : Adverbial) (v : Viewpoint)
    (n : {n : α // 0 < n}) : Set W :=
  pol • positiveReading μ P s a v n

private instance [NoMaxOrder α] : Nontrivial {n : α // 0 < n} :=
  let ⟨n, hn⟩ := exists_gt (0 : α)
  let ⟨m, hm⟩ := exists_gt n
  ⟨⟨⟨n, hn⟩, ⟨m, hn.trans hm⟩, fun h => hm.ne (congrArg Subtype.val h)⟩⟩

/-- In Table 1 every cell but negated G-TIA under perfective aspect is blocked, the E-TIA
cells and the imperfective G-TIA cell by information collapse, the positive perfective G-TIA
by density, and negation preserves collapse. -/
theorem table1_blocked [DenselyOrdered T] [NoMaxOrder α] {P : W → E → Prop} {s : T}
    (hP : HasSubintervalProperty P) (pol : Polarity) (a : Adverbial) (v : Viewpoint)
    (h : (pol, a, v) ≠ (.negative, .gap, .pfv)) : ¬ IsMIPLicensed (reading μ P s pol a v) := by
  have hconst : ∀ a v, (a, v) ≠ (.gap, .pfv) → ∀ n m : {n : α // 0 < n},
      positiveReading μ P s a v n = positiveReading μ P s a v m := by
    rintro a v h ⟨n, hn⟩ ⟨m, hm⟩
    cases a <;> cases v
    · exact eTIA_eq_of_hasSubintervalProperty μ (hasSubintervalProperty_ePerfFrame hP) n m
    · exact eTIA_uPerfFrame_eq μ hP hn hm
    · exact absurd rfl h
    · exact uPerfGTIA_eq μ hn hm
  cases pol
  · cases a <;> cases v
    · exact not_isMIPLicensed_of_forall_eq (hconst .event .pfv (by decide))
    · exact not_isMIPLicensed_of_forall_eq (hconst .event .impv (by decide))
    · refine not_isMIPLicensed_of_not_isLeast (fun n m hnm => gTIA_monotone μ P s hnm)
        fun w n ⟨hn, hlb⟩ => ?_
      obtain ⟨m, hm, hmn, hw⟩ := exists_lt_of_mem_gTIA μ hn
      exact hmn.not_ge (hlb (a := ⟨m, hm⟩) hw)
    · exact not_isMIPLicensed_of_forall_eq (hconst .gap .impv (by decide))
  · refine not_isMIPLicensed_of_forall_eq fun n m => congrArg compl (hconst a v ?_ n m)
    exact fun hav => h (congrArg (Prod.mk Polarity.negative) hav)

/-- The survivor of Table 1 is negated G-TIA under perfective aspect, licensed where worlds separate
gap lengths and some world's last event abuts the span. -/
theorem table1_survivor {P : W → E → Prop} {s : T} (hφ : StrictAnti (gTIANeg μ P s))
    {w : W} {l₀ : T} (hall : ∀ e, P w e → (τ e).fst ≤ l₀)
    (hwit : ∃ e, P w e ∧ (τ e).fst = l₀ ∧ (τ e).snd < s) :
    IsMIPLicensed (reading μ P s .negative .gap .pfv) := by
  obtain ⟨e₀, he₀, hfst, hsnd⟩ := hwit
  have hl : l₀ < s := hfst ▸ (τ e₀).fst_le_snd.trans_lt hsnd
  refine isMIPLicensed_of_isGreatest (w := w) (fun n m hnm => hφ (Subtype.coe_lt_coe.2 hnm))
    ⟨⟨μ ⟨⟨l₀, s⟩, hl.le⟩, IsIntervalContent.positive l₀ s hl⟩, ?_⟩
  have hg := isGreatest_gTIANeg μ hall ⟨e₀, he₀, hfst, hsnd⟩ hl.le
  exact ⟨hg.1, fun m hm => Subtype.coe_le_coe.1 (hg.2 hm)⟩

end Rouillard2026
