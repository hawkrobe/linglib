import Linglib.Data.Examples.FoxHackl2006
import Linglib.Semantics.Alternatives.Extremum
import Linglib.Logic.Modal.Defs

/-!
# Fox and Hackl 2006: the universal density of measurement

This file formalizes the paper's Universal Density of Measurement — measurement scales in
natural language semantics are always dense — and the single mechanism it drives through
scalar implicatures, *only*, degree questions and definite descriptions. Each of the four
maximizes a property of degrees with MAXinf, the most informative true degree
(`Alternatives.IsMaxInf`), and the Constraint on Interval Maximization says this fails on a
property that necessarily describes an open interval (`NOpen`). On a strictly antitone family
the most informative degree is the greatest true one (`Alternatives.hasMaxInf_iff_isGreatest`),
so density removes it exactly when the true set is open at its informative end; a universal
modal can close the interval and an existential modal cannot. A bare numeral's *at least d* is
closed at the count (`Alternatives.hasMaxInf_ge_over`), exhaustification is MAXinf
(`Alternatives.exhChain_iff_isMaxInf`), and the paper's example sentences are the rows of
`Examples.all`.

## Main results

* `cim`, `cim_below`: the Constraint on Interval Maximization for upward and downward
  monotone properties.
* `moreThan_not_hasMaxInf`, `negation_not_hasMaxInf`: *more than d* has no most informative
  degree (no implicature, no *only*), and neither does *not … d* (negative islands).
* `hasMaxInf_box`, `not_isGreatest_diamond` and their duals: a universal modal closes the
  interval, an existential modal does not.
* `moreThan_exact_nat`: at cardinality granularity *more than n* exhaustifies to
  *exactly n + 1*.

## References

* [D. Fox and M. Hackl, *The universal density of measurement* (2006)][fox-hackl-2006]
* [H. Rullmann, *Maximality in the semantics of wh-constructions* (1995)][rullmann-1995]
* [S. Beck and H. Rullmann, *A flexible approach to exhaustivity in questions*
  (1999)][beck-rullmann-1999]
* [V. Dayal, *Locality in WH quantification* (1996)][dayal-1996]
* [M. Hackl, *Comparative quantifiers* (2000)][hackl-2000]
-/

namespace FoxHackl2006

open Alternatives ModalLogic OrderDual Set
open Degree (Comparison)

variable {D W : Type*} [LinearOrder D]

/-! ### Necessarily open properties -/

/-- A property of degrees necessarily describes an open interval: at every world some degree
fails it and every smaller degree satisfies it. -/
def NOpen (φ : D → Set W) : Prop :=
  ∀ w, ∃ d, w ∉ φ d ∧ ∀ d' < d, w ∈ φ d'

/-- The downward-monotone mirror image: some degree fails and every larger degree holds. -/
abbrev NOpenBelow (φ : D → Set W) : Prop :=
  NOpen fun d : Dᵒᵈ => φ (ofDual d)

/-- (42) The Constraint on Interval Maximization: on a dense scale a necessarily open
upward-monotone property has no most informative degree. -/
theorem cim [DenselyOrdered D] {φ : D → Set W} (hφ : StrictAnti φ) (hopen : NOpen φ)
    (w : W) : ¬ HasMaxInf φ w :=
  (hasMaxInf_iff_isGreatest hφ).not.2 fun ⟨_, hm⟩ =>
    let ⟨_, hd, hlt⟩ := hopen w
    let ⟨y, hmy, hyd⟩ := exists_between (lt_of_not_ge fun h => hd (hφ.antitone h hm.1))
    not_le.2 hmy (hm.2 (hlt y hyd))

/-- (42) for downward-monotone properties. -/
theorem cim_below [DenselyOrdered D] {φ : D → Set W} (hφ : StrictMono φ)
    (hopen : NOpenBelow φ) (w : W) : ¬ HasMaxInf φ w :=
  cim (φ := fun d : Dᵒᵈ => φ (ofDual d)) (fun _ _ h => hφ h) hopen w

/-! ### Implicatures and *only* -/

/-- *More than d* necessarily describes an open interval: the true degrees at `w` are those
below the count. -/
theorem nOpen_gt_over (μ : W → D) : NOpen (Comparison.gt.over μ) :=
  fun w => ⟨μ w, lt_irrefl _, fun _ h => h⟩

/-- (2), (5), (7b–c): on a dense scale *more than d* has no most informative degree, so it
carries no scalar implicature and rejects *only*. -/
theorem moreThan_not_hasMaxInf [DenselyOrdered D] (μ : W → D) (hμ : Function.Surjective μ)
    (w : W) : ¬ HasMaxInf (Comparison.gt.over μ) w :=
  cim (Comparison.strictAnti_gt_over μ hμ) (nOpen_gt_over μ) w

/-! ### Modal operators -/

/-- The deontic modal base whose only requirement is `φ a`: the worlds where `φ` holds of
some degree above `a`. -/
abbrev requirementBase (φ : D → Set W) (a : D) : W → W → Prop :=
  fun _ w' => ∃ d, a < d ∧ w' ∈ φ d

/-- (46) Under `requirementBase φ a`, *required to φ d* describes the closed interval
`Iic a`. -/
theorem box_eq_Iic [DenselyOrdered D] {φ : D → Set W} (hφ : StrictAnti φ) (a : D) (w : W) :
    {d | box (requirementBase φ a) (φ d) w} = Iic a := by
  ext d'
  constructor
  · intro h
    by_contra hd'
    obtain ⟨m, ham, hmd'⟩ := exists_between (not_le.1 hd')
    obtain ⟨u, hu, hu'⟩ := Set.exists_of_ssubset (hφ hmd')
    exact hu' (h u ⟨m, ham, hu⟩)
  · intro hd' u hu
    obtain ⟨d, had, hu⟩ := hu
    exact hφ.antitone ((hd' : d' ≤ a).trans had.le) hu

/-- (13), (46): a universal modal closes the interval, so *required to φ more than d* has a
most informative degree, `a` itself. -/
theorem hasMaxInf_box [DenselyOrdered D] {φ : D → Set W} (hφ : StrictAnti φ) (a : D)
    (w : W) : HasMaxInf (fun d => {w | box (requirementBase φ a) (φ d) w}) w := by
  have hanti : Antitone fun d => {w | box (requirementBase φ a) (φ d) w} :=
    fun _ _ h _ hv u hu => hφ.antitone h (hv u hu)
  exact ⟨a, hanti.map_isGreatest (box_eq_Iic hφ a w ▸ isGreatest_Iic)⟩

/-- (14), (47): no existential modal closes the interval — the true degrees of *allowed to
φ d* have no greatest element, so the constraint still applies. -/
theorem not_isGreatest_diamond [DenselyOrdered D] {φ : D → Set W} (hφ : StrictAnti φ)
    (hopen : NOpen φ) (R : W → W → Prop) (w : W) :
    ¬ ∃ m, IsGreatest {d | diamond R (φ d) w} m := by
  rintro ⟨m, ⟨v, hv, hvm⟩, hub⟩
  obtain ⟨d, hd, hlt⟩ := hopen v
  have hmd : m < d := lt_of_not_ge fun h => hd (hφ.antitone h hvm)
  obtain ⟨y, hmy, hyd⟩ := exists_between hmd
  exact not_le.2 hmy (hub ⟨v, hv, hlt y hyd⟩)

/-! ### Negative islands -/

/-- *Not … d* is necessarily open from below: the true degrees are those above the measure. -/
theorem nOpenBelow_lt_over (μ : W → D) : NOpenBelow (Comparison.lt.over μ) :=
  nOpen_gt_over (toDual ∘ μ)

/-- (16), (19a), (25): on a dense scale the negated degree property has no most informative
(least true) degree, so a degree question or definite description over it is undefined. -/
theorem negation_not_hasMaxInf [DenselyOrdered D] (μ : W → D) (hμ : Function.Surjective μ)
    (w : W) : ¬ HasMaxInf (Comparison.lt.over μ) w :=
  cim_below (Comparison.strictMono_lt_over μ hμ) (nOpenBelow_lt_over μ) w

/-- (27b), (28a), (29a): *required not to φ d* — a universal modal over a downward-monotone
property closes the interval from below. -/
theorem hasMaxInf_box_below [DenselyOrdered D] {φ : D → Set W} (hφ : StrictMono φ) (a : D)
    (w : W) : HasMaxInf (fun d => {w | box (fun _ w' => ∃ d, d < a ∧ w' ∈ φ d) (φ d) w}) w :=
  hasMaxInf_box (φ := fun d : Dᵒᵈ => φ (ofDual d)) (fun _ _ h => hφ h) (toDual a) w

/-- (28b), (29b), (47): *allowed not to φ d* stays open from below. -/
theorem not_isLeast_diamond [DenselyOrdered D] {φ : D → Set W} (hφ : StrictMono φ)
    (hopen : NOpenBelow φ) (R : W → W → Prop) (w : W) :
    ¬ ∃ m, IsLeast {d | diamond R (φ d) w} m :=
  not_isGreatest_diamond (φ := fun d : Dᵒᵈ => φ (ofDual d)) (fun _ _ h => hφ h) hopen R w

/-! ### Cardinality as a level of granularity -/

/-- (73)–(75): at cardinality granularity *more than n* is *at least n + 1*, whose most
informative degree is the count, so *only more than 15F* means *exactly 16*. -/
theorem moreThan_exact_nat (μ : W → ℕ) (hμ : Function.Surjective μ) (m : ℕ) (w : W) :
    IsMaxInf (Comparison.gt.over μ) m w ↔ μ w = m + 1 := by
  refine isMaxInf_iff.trans ⟨fun ⟨h1, h2⟩ => ?_, fun h => ⟨?_, fun y hy => ?_⟩⟩
  · obtain ⟨v, hv⟩ := hμ (m + 1)
    by_contra hne
    have h1 : m < μ w := h1
    have h3 : m + 1 < μ v :=
      h2 (m + 1) (by change m + 1 < μ w; omega) (by change m < μ v; omega)
    omega
  · change m < μ w; omega
  · exact Comparison.antitone_gt_over μ (by change y < μ w at hy; omega)

end FoxHackl2006
