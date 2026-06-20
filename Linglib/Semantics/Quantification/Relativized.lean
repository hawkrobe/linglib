/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Quantification.Counting

/-!
# Generalized quantifiers relativized to an explicit finite domain

[barwise-cooper-1981] [peters-westerstahl-2006]

The canonical generalized-quantifier denotations in `Quantification.Basic`
(`every_sem`/`some_sem`/`no_sem`) and `Quantification.Counting`
(`count`/`most_sem`/…) quantify over the **whole carrier** `α` and recover
decidability via `[Fintype α]`. Many consumers — covert operators (GEN, HAB),
and the finite toy models in `Studies/` — instead carry an **explicit finite
domain** `s : Finset α` over a carrier that is *not* a `Fintype` (e.g.
`structure Situation where id : Nat`). The `List`/`Bool` covert-quantifier hub
was reinventing exactly these quantifiers in an inferior representation.

This module provides the **relativized** layer: the same generalized
quantifiers ranging over a `Finset s`, decidable from the explicit domain
(via `Finset.decidableDforallFinset`) with **no `Fintype α`**. The whole-carrier
denotations are recovered as the `s = Finset.univ` fibre (`*_univ` lemmas) — the
`Probability.Kernel.Defs` (general) / `Probability.Kernel.Deterministic`
(specialization) + equivalence-lemma discipline, applied to GQ theory.

* `every_on`/`some_on`/`no_on` — relativized ∀/∃ (Prop, `[DecidablePred]`).
* `countOn` — `(s.filter P).card`; `countOn Finset.univ = count` by `rfl`.
* `most_on` — cross-multiplied "most" over `s` (division-free, `decide`-able).
* `thresholdOn`/`thresholdGtOn` — `denom·|s∩R∩S| ▷ num·|s∩R|` for a rational
  threshold `num/denom`, with `▷ ∈ {≥, >}`. Division-free; this is the canonical
  decidable threshold predicate (the ℚ ratio is a *derived view*, `prevalenceOn`).
* `prevalenceOn` — the ℚ ratio `|s∩R∩S| / |s∩R|`; the analogue of
  `Rel.edgeDensity`. Demoted to a derived numeric view, related to `thresholdGtOn`
  by `thresholdGtOn_iff_prevalenceOn`.

The List-relativized ∀/∃ already exist in `Quantification.Generators` as
`conjGQ`/`disjGQ` (with `conjGQ_iff_forall`); `every_on`/`some_on` are their
`Finset` presentation.
-/

namespace Quantification

variable {α : Type*}

/-! ### Relativized denotations -/

/-- `s`-relativized restricted universal: every `R` in `s` is `S`.
    `every_on Finset.univ = every_sem` (`every_on_univ`). -/
def every_on (s : Finset α) (R S : α → Prop) : Prop := ∀ x ∈ s, R x → S x

/-- `s`-relativized existential. -/
def some_on (s : Finset α) (R S : α → Prop) : Prop := ∃ x ∈ s, R x ∧ S x

/-- `s`-relativized `no`. -/
def no_on (s : Finset α) (R S : α → Prop) : Prop := ∀ x ∈ s, R x → ¬ S x

/-- Decidable from the explicit domain `s` — **no `Fintype α`**, via
    `Finset.decidableDforallFinset`. -/
instance every_on.decidable (s : Finset α) (R S : α → Prop)
    [DecidablePred R] [DecidablePred S] : Decidable (every_on s R S) := by
  unfold every_on; infer_instance

instance some_on.decidable (s : Finset α) (R S : α → Prop)
    [DecidablePred R] [DecidablePred S] : Decidable (some_on s R S) := by
  unfold some_on; infer_instance

instance no_on.decidable (s : Finset α) (R S : α → Prop)
    [DecidablePred R] [DecidablePred S] : Decidable (no_on s R S) := by
  unfold no_on; infer_instance

/-- `s`-relativized count: `|{x ∈ s | P x}|`. The `Fintype`-free `count`;
    `countOn Finset.univ = count` by `rfl`. -/
def countOn (s : Finset α) (P : α → Prop) [DecidablePred P] : Nat :=
  (s.filter P).card

/-- "most" over `s`: strictly more `R∧S` than `R∧¬S` in `s`. Division-free;
    `Decidable` via `Nat.decLt`. `most_on Finset.univ = most_sem` (`most_on_univ`). -/
def most_on (s : Finset α) (R S : α → Prop)
    [DecidablePred R] [DecidablePred S] : Prop :=
  countOn s (fun x => R x ∧ S x) > countOn s (fun x => R x ∧ ¬ S x)

/-- Threshold generic (`≥` form, matching the Montague `genThreshold` body):
    at least `num/denom` of the `R`'s in `s` are `S`. Cross-multiplied — no division. -/
def thresholdOn (s : Finset α) (R S : α → Prop) (num denom : Nat)
    [DecidablePred R] [DecidablePred S] : Prop :=
  denom * countOn s (fun x => R x ∧ S x) ≥ num * countOn s R

/-- Threshold generic (`>` form, matching `thresholdGeneric`/`measure > θ`):
    more than `num/denom` of the `R`'s in `s` are `S`. Cross-multiplied — no division. -/
def thresholdGtOn (s : Finset α) (R S : α → Prop) (num denom : Nat)
    [DecidablePred R] [DecidablePred S] : Prop :=
  denom * countOn s (fun x => R x ∧ S x) > num * countOn s R

instance most_on.decidable (s : Finset α) (R S : α → Prop)
    [DecidablePred R] [DecidablePred S] : Decidable (most_on s R S) := by
  unfold most_on; infer_instance

instance thresholdOn.decidable (s : Finset α) (R S : α → Prop) (num denom : Nat)
    [DecidablePred R] [DecidablePred S] : Decidable (thresholdOn s R S num denom) := by
  unfold thresholdOn; infer_instance

instance thresholdGtOn.decidable (s : Finset α) (R S : α → Prop) (num denom : Nat)
    [DecidablePred R] [DecidablePred S] : Decidable (thresholdGtOn s R S num denom) := by
  unfold thresholdGtOn; infer_instance

/-- The ℚ prevalence *view* (the analogue of `Rel.edgeDensity`): the proportion of
    `R`-in-`s` that are `S`. Demoted from a truth-maker to a derived numeric value;
    related to the canonical `thresholdGtOn` by `thresholdGtOn_iff_prevalenceOn`. -/
def prevalenceOn (s : Finset α) (R S : α → Prop)
    [DecidablePred R] [DecidablePred S] : ℚ :=
  if countOn s R = 0 then 0
  else (countOn s (fun x => R x ∧ S x) : ℚ) / (countOn s R : ℚ)

/-! ### Whole-domain recovery (`s = Finset.univ`)

These reduce the relativized layer to the canonical `Quantification.Basic` /
`Quantification.Counting` denotations, exhibiting the relativized operators as
the general layer's specialization. -/

@[simp] theorem countOn_univ [Fintype α] (P : α → Prop) [DecidablePred P] :
    countOn Finset.univ P = count P := rfl

@[simp] theorem every_on_univ [Fintype α] (R S : α → Prop) :
    every_on Finset.univ R S ↔ every_sem R S := by
  simp [every_on, every_sem]

@[simp] theorem some_on_univ [Fintype α] (R S : α → Prop) :
    some_on Finset.univ R S ↔ some_sem R S := by
  simp [some_on, some_sem]

@[simp] theorem no_on_univ [Fintype α] (R S : α → Prop) :
    no_on Finset.univ R S ↔ no_sem R S := by
  simp [no_on, no_sem]

-- `most_on_univ : most_on Finset.univ R S ↔ most_sem R S` and the inherited
-- `Proportional` corollary are deferred to PR3 (they require bridging the
-- classical `DecidablePred` instances baked into `most_sem` against the explicit
-- ones here, alongside the other property-transport lemmas).

/-! ### Counting facts -/

/-- `|s∩R| = |s∩R∩S| + |s∩R\S|` (relativized `count_decompose`). -/
theorem countOn_decompose (s : Finset α) (R S : α → Prop)
    [DecidablePred R] [DecidablePred S] :
    countOn s R =
      countOn s (fun x => R x ∧ S x) + countOn s (fun x => R x ∧ ¬ S x) := by
  simp only [countOn]
  rw [← Finset.filter_filter R S s, ← Finset.filter_filter R (fun x => ¬ S x) s,
      Finset.card_filter_add_card_filter_not]

/-! ### Threshold ↔ prevalence

The canonical division-free `thresholdGtOn` agrees with "`prevalenceOn` exceeds
`num/denom`", justifying the demotion of the ℚ ratio to a derived view. -/

theorem thresholdGtOn_iff_prevalenceOn (s : Finset α) (R S : α → Prop)
    [DecidablePred R] [DecidablePred S] (num denom : Nat)
    (hdenom : 0 < denom) (hR : 0 < countOn s R) :
    thresholdGtOn s R S num denom ↔ prevalenceOn s R S > (num : ℚ) / (denom : ℚ) := by
  unfold thresholdGtOn prevalenceOn
  rw [if_neg (Nat.pos_iff_ne_zero.mp hR)]
  have hdQ : (0 : ℚ) < denom := by exact_mod_cast hdenom
  have hRQ : (0 : ℚ) < countOn s R := by exact_mod_cast hR
  rw [gt_iff_lt, gt_iff_lt, div_lt_iff₀ hdQ, div_mul_eq_mul_div, lt_div_iff₀ hRQ,
      mul_comm (countOn s (fun x => R x ∧ S x) : ℚ) (denom : ℚ),
      ← Nat.cast_mul, ← Nat.cast_mul, Nat.cast_lt]

/-! ### Decidability check

The relativized operators kernel-`decide` over an explicit finite domain with no
`Fintype` on the carrier — the property that lets the finite toy models in
`Studies/` retire `native_decide`. -/

example : every_on ({0, 1, 2} : Finset (Fin 5)) (fun x => x.val < 3) (fun x => x.val < 4) := by
  decide

example : ¬ every_on ({0, 1, 2} : Finset (Fin 5)) (fun x => x.val < 3) (fun x => x.val < 1) := by
  decide

example : thresholdGtOn ({0, 1, 2, 3} : Finset (Fin 5))
    (fun x => x.val < 4) (fun x => x.val < 3) 1 2 := by decide

end Quantification
