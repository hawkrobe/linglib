module

public import Linglib.Semantics.Degree.Background
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Cariani, Santorio and Wellwood 2024: confidence reports

[cariani-santorio-wellwood-2024] give adjectival *confident* and nominal *confidence* one
denotation, a property of confidence states (38). A holder's confidence states each carry a
proposition as their theme, and a background ordering, one per holder, ranks them across themes
(§4.1). *σ is confident that p* says that some state of σ's with theme `p` lies at or above a
contrast state (40), so the positive form needs no covert *pos*; *certain* is the same ordering
with a higher contrast state, at the top (§5.2). The comparative (47) discards the contrast
state and compares degrees, assigned by [wellwood-2015]'s *more* through a measure that must
preserve the strict ordering (21). This is the two-component analysis of
[cariani-santorio-wellwood-2023], `Semantics/Degree/Background.lean`, with themes for holders
and the region above a contrast state for the threshold property.

The positive form lives on the background ordering and the comparative on the degree scale, and
this file sorts the paper's logic (§4.6, §5.2) by which of the two each inference uses.
Transitivity (54), antisymmetry (55) and connectedness (56) are facts about the degree scale:
they hold of the max-quantified comparative and equative whatever the background ordering and
whatever the measure (`Degree.maxComparative_trans`, `Degree.maxEquative_antisymm`,
`Degree.maxEquative_total`). Upward monotonicity (53) is the one inference that crosses from a
comparative back to a positive form, the earlier paper's (19). It needs both the admissibility
of the measure and the totality of the ordering (`Degree.mem_image_of_maxComparative`), and on
a non-total ordering any incomparable pair that an admissible measure separates refutes it
(`Degree.not_mem_image_Ici_of_not_le`). Making the ordering partial, the paper's way of dropping
Connectedness (§4.6), therefore costs (53) but not (56): on a linear degree scale the three
alternatives of (58) still exhaust the cases (`Degree.maxComparative_trichotomy`). The
comparative does not entail the positive form (§3.2, §4.3;
`Degree.maxComparative_and_not_mem_image`).

The conjunction fallacy (52) is consistent with the semantics, since the ordering ranks states
and not their contents (`exists_conjunctionFallacy`), while a threshold on a probability
measure, the off-the-shelf alternative of §2 on the scalar semantics of [lassiter-2017],
validates conjunction elimination, so no such threshold reproduces the confidence of a holder who
commits the fallacy (`image_Ici_ne_ge_over`). *Certain* entails *confident* because its contrast
state is maximal (`image_Ici_subset_image_Ici_of_isMax`), and the entailment is asymmetric
whenever *confident*'s contrast state is not (`not_image_Ici_subset_image_Ici`).

## Main results

* `maxComparative_theme_iff`: with one state per theme the comparative (47) compares measures.
* `exists_conjunctionFallacy`, `image_Ici_ne_ge_over`: (52a) and (52b) are true together on
  some total ordering, and on no threshold of a probability measure.
* `image_Ici_subset_image_Ici_of_isMax`, `not_image_Ici_subset_image_Ici`: *certain* entails
  *confident* asymmetrically (65), (66).
* `Ici_eq_setOf_isMax`: the region above a maximal contrast state (71) is the set of maximal
  states of Figure 3.
* `not_maxComparative_of_isMax`, `maxComparative_of_isMax`: nothing is more confident than a
  certainty (68) when the measure also respects ties, and under admissibility alone something
  can be.

## Implementation notes

A holder's confidence states form a type `S` with its background preorder, and `θ : S → Set W`
assigns themes; thematic relations are functions of the state (fn. 12). Fixing `S` fixes the
holder, so `ho(s) = a` in (40) and (47) is membership in `S`. The states of all holders at once
are the disjoint sum `Σ a, S a` under mathlib's `Sigma.LE`, where only states of one holder are
comparable, as the per-holder orderings of §4.1 require; no inference of §4.6 compares holders.
The positive form (40), (71) is `p ∈ θ '' Set.Ici c` for a contrast state `c`, and *certain*
is `p ∈ θ '' {s | IsMax s}` (Figure 3). The comparative (47) is
`Degree.maxComparative (θ · = p) (θ · = q) μ` and the equative of (55) `Degree.maxEquative`,
with *equally confident* the coincidence of the two degree sets; an admissible measure is
`StrictMono μ`. Totality of the ordering (§4.1, "(at least) a total pre-order") is a hypothesis
of the theorems that use it. Condition (21) constrains only strictly ordered states, so tied
states, like the stacked states of Figures 2 and 3, may be measured differently; (68) needs the
measure to be monotone as well.

The paper states no semantics for *doubt*, so (63c) is not formalized.

## TODO

* The conditional (59) under a contrast that maps a proposition to its negation, and the two
  objections to it, (60) and fn. 31. With the weak positive form (40) the entailment needs the
  `p`-state strictly above the `¬p`-state, since a tie satisfies (59a) and refutes (59b); the
  paper's gloss ("ranked higher") reads the contrast strictly.
* Conditional confidence (61), (62), with the ordering indexed by an information state.

## References

* [cariani-santorio-wellwood-2024]
* [cariani-santorio-wellwood-2023]
* [wellwood-2015]
* [tversky-kahneman-1983]
* [lassiter-2017]
-/

@[expose] public section

namespace CarianiSantorioWellwood2024

open Set Degree
open MeasureTheory
open scoped ENNReal

variable {S W D : Type*} [Preorder S] [Preorder D] {θ : S → Set W} {μ : S → D}

/-! ### The comparative and the positive form -/

omit [Preorder S] in
/-- With one state per theme, the comparative (47) compares the two states' measures: σ's
confidence that `p` exceeds the than-clause degree (37). -/
theorem maxComparative_theme_iff (hθ : θ.Injective) (s t : S) :
    maxComparative (θ · = θ s) (θ · = θ t) μ ↔ μ t < μ s := by
  simp only [hθ.eq_iff]
  exact maxComparative_eq_iff μ s t

/-- Upward monotonicity (53) is the framework's, over the region above a contrast state: if σ is
confident that `p` and more confident of `q` than of `p`, then σ is confident that `q`. -/
example [@Std.Total S (· ≤ ·)] (hμ : admissibleMeasure μ) {c : S} {p q : Set W}
    (hp : p ∈ θ '' Ici c) (h : maxComparative (θ · = q) (θ · = p) μ) : q ∈ θ '' Ici c :=
  mem_image_of_maxComparative (isUpperSet_Ici c) hμ hp h

/-! ### The conjunction fallacy (52) -/

/-- (52a) *John is not confident that Linda is a bankteller* and (52b) *John is confident that
Linda is a feminist bankteller* are true together: whenever `φ ∩ ψ` differs from `φ`, a two-state
total ordering with the `φ ∩ ψ`-state above the `φ`-state and the contrast state at the top
makes the holder confident of the conjunction but not of the conjunct. -/
theorem exists_conjunctionFallacy {φ ψ : Set W} (h : ¬ φ ⊆ ψ) :
    ∃ θ : Bool → Set W, φ ∩ ψ ∈ θ '' Ici true ∧ φ ∉ θ '' Ici true := by
  refine ⟨fun b ↦ if b then φ ∩ ψ else φ, ⟨true, mem_Ici.2 le_rfl, rfl⟩, ?_⟩
  rintro ⟨b, hb, hbφ⟩
  obtain rfl : b = true := top_le_iff.1 hb
  exact h (by simpa using hbφ.symm ▸ inter_subset_right (s := φ) (t := ψ))

/-- A holder confident of a conjunction but not of its conjunct is confident of no set of
propositions that the threshold account of §2 (7) delivers: whatever the threshold, the
propositions whose probability meets it are closed under conjunction elimination, since a
measure is monotone. -/
theorem image_Ici_ne_ge_over [MeasurableSpace W] (P : Measure W) (t : ℝ≥0∞) {c : S}
    {φ ψ : Set W} (h₁ : φ ∩ ψ ∈ θ '' Ici c) (h₂ : φ ∉ θ '' Ici c) :
    θ '' Ici c ≠ Comparison.ge.over P t :=
  fun h ↦ h₂ (h ▸ Comparison.mem_ge_over_of_le P (h ▸ h₁) (measure_mono inter_subset_left))

/-! ### *Certain* and *confident* (§5.2) -/

/-- *Certain* entails *confident* (65b), (66b). The paper's reason is that *certain* picks out a
smaller segment of the ordering than *confident*, which is `Ici_subset_Ici` once *confident*'s
contrast state lies below *certain*'s; on a total ordering that holds of every contrast state
once *certain*'s is maximal. -/
theorem image_Ici_subset_image_Ici_of_isMax [@Std.Total S (· ≤ ·)] {m : S} (hm : IsMax m)
    (c : S) : θ '' Ici m ⊆ θ '' Ici c :=
  image_mono (Ici_subset_Ici.2 ((total_of (· ≤ ·) c m).elim id fun h ↦ hm h))

/-- The entailment is asymmetric (65a), (66a): when *confident*'s contrast state `c` is not
above *certain*'s `m`, the holder is confident but not certain of `c`'s theme. -/
theorem not_image_Ici_subset_image_Ici (hθ : θ.Injective) {c m : S} (hmc : ¬ m ≤ c) :
    ¬ θ '' Ici c ⊆ θ '' Ici m :=
  fun h ↦ hmc (Ici_subset_Ici.1 ((image_subset_image_iff hθ).1 h))

/-- On a total ordering the region above a maximal contrast state (71) is the set of maximal
states, what *certain* denotes in Figure 3. -/
theorem Ici_eq_setOf_isMax [@Std.Total S (· ≤ ·)] {m : S} (hm : IsMax m) :
    Ici m = {s | IsMax s} := by
  ext s
  exact ⟨fun hs t hst ↦ (hm (hs.trans hst)).trans hs,
    fun hs ↦ (total_of (· ≤ ·) m s).elim id fun h ↦ hs h⟩

/-- Nothing is more confident than a certainty (68): if σ is certain that `p`, σ is not more
confident of any `q` than of `p`. Admissibility (21) is not enough, since it leaves tied maximal
states free to be measured apart; the measure must also be monotone. -/
theorem not_maxComparative_of_isMax [@Std.Total S (· ≤ ·)] (hμ : Monotone μ) {s : S}
    (hs : IsMax s) {p q : Set W} (hsp : θ s = p) : ¬ maxComparative (θ · = q) (θ · = p) μ :=
  fun h ↦
    let ⟨y, _, hlt⟩ := h.exists_lt hsp
    (hμ ((total_of (· ≤ ·) y s).elim id fun h ↦ hs h)).not_gt hlt

/-- Under admissibility alone (68) fails: a maximal state measured below another state makes σ
certain of its theme and more confident of the other's. -/
theorem maxComparative_of_isMax (hθ : θ.Injective) {s t : S} (hs : IsMax s) (hlt : μ s < μ t) :
    θ s ∈ θ '' {s | IsMax s} ∧ maxComparative (θ · = θ t) (θ · = θ s) μ :=
  ⟨⟨s, hs, rfl⟩, (maxComparative_theme_iff hθ t s).2 hlt⟩

/-- Two tied maximal states, as at the top of Figure 3, can be measured apart by an admissible
measure: with every state tied, every measure is admissible. The preorder is passed explicitly,
since `Bool`'s own order would otherwise be found. -/
example :
    let tied : Preorder Bool := Preorder.lift fun _ ↦ ()
    @admissibleMeasure _ _ tied _ Bool.toNat ∧ @IsMax _ tied.toLE false ∧
      Bool.toNat false < Bool.toNat true :=
  ⟨fun _ _ h ↦ absurd h (lt_irrefl ()), fun _ _ ↦ trivial, Nat.zero_lt_one⟩

end CarianiSantorioWellwood2024
