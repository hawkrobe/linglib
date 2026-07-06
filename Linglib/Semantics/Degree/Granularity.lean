/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.Basic
import Mathlib.Data.Finset.Max
import Linglib.Core.Algebra.Order.ToIntervalMod
import Mathlib.Algebra.Order.Group.Defs
import Linglib.Semantics.Questions.Partition.QUD
import Linglib.Semantics.Questions.PrecisionProjection
import Linglib.Discourse.QUD.Basic
import Linglib.Semantics.Questions.Partition.Lattice

/-!
# Granularity-Sensitive Degree Semantics [thomas-deo-2020]

The underlying granularity apparatus — granularity functions partitioning a
scale into equal-width intervals and the finer/coarser ordering — is
[sauerland-stateva-2011]'s (their (15)–(16)), following [krifka-2007];
[thomas-deo-2020]'s contributions are the granularity-*level* convenience
g(d) = (d − ε, d + ε) (their (43)) and the semantics of approximative *just*
(their (44)).

## Overview

A granularity level maps each degree d on a scale to an open interval
g(d) = (d − ε, d + ε) of width 2ε (the "grain", eq. 43). Equatives
compare μ_x against the interval's **infimum** (eq. 45); comparatives
compare against the **supremum** (eq. 49). Both use strict >.

Since the infimum and supremum move in **opposite directions** as ε
varies, the entailment patterns reverse:
- Finer grain (smaller ε) → larger infimum → **stronger** equative
- Finer grain (smaller ε) → smaller supremum → **weaker** comparative

This reversal explains why approximative *just* yields different readings:
- *just as tall as* ≈ "exactly" (negative component vacuous)
- *just taller than* ≈ "barely" (negative component substantive)

## Structure

- § 1: Granularity intervals (eq. 43), construction from ε (eqs. 40–42),
  and degree morphology (eqs. 45, 49).
- § 2: Entailment reversal — from interval endpoint monotonicity.
- § 3: Approximative *just* (eq. 44) — vacuous vs substantive negative
  component derived from the reversal.
-/

namespace Degree.Granularity

/-! ### Granularity Intervals (eqs. 43, 45, 49) -/

/-- A granularity interval: the open interval (lo, hi) around a degree.

    Paper eq. (43): g(d) = (d − ε, d + ε) for non-endpoint d.
    Endpoints are handled asymmetrically:
    - g(min(S)) = (min(S), min(S) + ε)
    - g(max(S)) = (max(S) − ε, max(S)) -/
structure GranInterval (D : Type*) where
  /-- Infimum of the grain cell — used by equatives (eq. 45). -/
  lo : D
  /-- Supremum of the grain cell — used by comparatives (eq. 49). -/
  hi : D

/-! ### Granularity Construction (eqs. 40–42) -/

/-! ### [sauerland-stateva-2011] granularity framework

Eqs. (40a-c) define the properties of a granularity function γ:
- (40a) s ∈ γ(s) — every degree is in its own cell
- (40b) γ(s) is an interval — (already guaranteed by `GranInterval`)
- (40c) |γ(s)| = |γ(s')| for all s, s' — all cells have equal width
  (guaranteed by parametric construction from ε)

Eq. (41): γ is finer than γ' iff cells of γ are strictly narrower.
Eq. (42): The concrete construction γ(d) = (d − ε, d + ε). -/

section GranularityFunction

variable {D : Type*} [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]

/-- Eq. (42): Construct a granularity interval from grain size ε.
    g(d) = (d − ε, d + ε) — the open interval of width 2ε around d.
    (Eq. 43 refines this for scale endpoints; see `GranInterval` docstring.) -/
def mkGranInterval (ε d : D) : GranInterval D := ⟨d - ε, d + ε⟩

/-- Eq. (40a): d ∈ g(d) for positive grain — every degree is in the
    interior of its own cell. For open interval (lo, hi): lo < d < hi. -/
theorem containsSelf (ε d : D) (hε : 0 < ε) :
    (mkGranInterval ε d).lo < d ∧ d < (mkGranInterval ε d).hi :=
  ⟨sub_lt_self d hε, lt_add_of_pos_right d hε⟩

/-- Eq. (41): Finer granularity → narrower intervals → containment.
    If ε₁ ≤ ε₂, then g_{ε₁}(d) ⊆ g_{ε₂}(d):
    - lo: d − ε₂ ≤ d − ε₁ (finer has larger infimum)
    - hi: d + ε₁ ≤ d + ε₂ (finer has smaller supremum) -/
theorem finer_contained (ε₁ ε₂ d : D) (h : ε₁ ≤ ε₂) :
    (mkGranInterval ε₂ d).lo ≤ (mkGranInterval ε₁ d).lo ∧
    (mkGranInterval ε₁ d).hi ≤ (mkGranInterval ε₂ d).hi :=
  ⟨sub_le_sub_left h d, add_le_add_right h d⟩

end GranularityFunction

variable {D : Type*} [LinearOrder D]

/-! ### Granularity selection ([sauerland-stateva-2011] (18)–(19), (41))

A context supplies a set of available granularities; scalar approximators
*reset* it ([sauerland-stateva-2011] (18)–(19)): *exactly* to the finest,
*approximately* to the coarsest. With uniform-width granularities the
finer-than order (their (41)) is width comparison, so selection is
`Finset.min'`/`max'`. Resetting leaves a singleton, on which any further
reset is vacuous — the engine of approximator-stacking oddity
(their §6.3.5). -/

section GranSelection

variable (𝒢 : Finset D) (h𝒢 : 𝒢.Nonempty)

/-- The finest available grain width — the reset target of *exactly*
([sauerland-stateva-2011] (19a)). -/
def finestWidth : D := 𝒢.min' h𝒢

/-- The coarsest available grain width — the reset target of
*approximately* ([sauerland-stateva-2011] (19b)). -/
def coarsestWidth : D := 𝒢.max' h𝒢

theorem finestWidth_le {ε : D} (hε : ε ∈ 𝒢) : finestWidth 𝒢 h𝒢 ≤ ε :=
  Finset.min'_le _ _ hε

theorem le_coarsestWidth {ε : D} (hε : ε ∈ 𝒢) : ε ≤ coarsestWidth 𝒢 h𝒢 :=
  Finset.le_max' _ _ hε

@[simp] theorem finestWidth_singleton (ε : D) :
    finestWidth {ε} (Finset.singleton_nonempty ε) = ε :=
  Finset.min'_singleton ε

@[simp] theorem coarsestWidth_singleton (ε : D) :
    coarsestWidth {ε} (Finset.singleton_nonempty ε) = ε :=
  Finset.max'_singleton ε

end GranSelection

/-! ### Entailment Reversal -/

/-! ### The central observation (§4.2)

Equatives and comparatives use **opposite ends** of the same interval.
Since `>` is anti-monotone in its right argument (lower threshold →
easier to exceed), the entailment direction reverses:

- **Equatives** use `lo = d_c − ε`, which **decreases** as ε grows.
  Lower bar → weaker claim. So fine ⊢ coarse.
- **Comparatives** use `hi = d_c + ε`, which **increases** as ε grows.
  Higher bar → stronger claim. So coarse ⊢ fine.

The proofs are one-liners: transitivity of `<` and `≤`. -/

/-- Equatives: finer grain (larger lo) entails coarser grain (smaller lo).

    The equative "as Adj as d_c" (eq. 45) at grain cell `gi`, for
    upward-monotone G, reduces to `μ_x > gi.lo` (the cell's infimum).
    If μ_x exceeds the fine-grain infimum, it a fortiori exceeds the
    coarse-grain infimum (which is smaller). -/
theorem eq_fine_entails_coarse (gi₁ gi₂ : GranInterval D)
    (hlo : gi₂.lo ≤ gi₁.lo)
    (μ_x : D) (h : μ_x > gi₁.lo) : μ_x > gi₂.lo :=
  lt_of_le_of_lt hlo h

/-- Comparatives: coarser grain (larger hi) entails finer grain (smaller hi).

    The comparative "Adj-er than d_c" (eq. 49) at grain cell `gi`, for
    upward-monotone G, reduces to `μ_x > gi.hi` (the cell's supremum).
    If μ_x exceeds the coarse-grain supremum, it a fortiori exceeds the
    fine-grain supremum (which is smaller). -/
theorem comp_coarse_entails_fine (gi₁ gi₂ : GranInterval D)
    (hhi : gi₁.hi ≤ gi₂.hi)
    (μ_x : D) (h : μ_x > gi₂.hi) : μ_x > gi₁.hi :=
  lt_of_le_of_lt hhi h

/-! ### Approximative *just* (eq. 44) -/

/-! ### Approximative *just*

Paper eq. (44): ⟦just⟧ = λp λw. p^{g_finest}(w) ∧ ∀g ∈ 𝒢[p^g(w) → p^{g_finest} ≥_S p^g]

Generic over any grain type G and degree type D. -/

section JustTheory

variable {G : Type*}

/-- Propositional strength (paper's ≥_S, footnote 10):
    p at g₁ is at least as strong as p at g₂ iff g₁-truth entails
    g₂-truth for all degree values.

    Paper: p^{g₁} ≥_S p^{g₂} ≡ ∀w[p^{g₁}(w) → p^{g₂}(w)]. -/
def atLeastAsStrong (p : G → D → Prop) (g₁ g₂ : G) : Prop :=
  ∀ μ_x, p g₁ μ_x → p g₂ μ_x

/-- Approximative *just* (paper eq. 44).

    Positive component: the prejacent holds at the finest grain.
    Negative component: at every grain where the prejacent holds,
    the finest-grain version is at least as strong.

    The paper restricts quantification to a finite contextual set 𝒢.
    We quantify over all G for simplicity; the structural results
    (vacuous/substantive) hold either way. -/
def approxJust (p : G → D → Prop) (finest : G) (μ_x : D) : Prop :=
  p finest μ_x ∧ ∀ g : G, p g μ_x → atLeastAsStrong p finest g

omit [LinearOrder D] in
/-- Equative prediction: if the finest grain is the strongest for p,
    then *just*'s negative component is vacuous — *just* adds nothing.
    "Just as tall as" ≈ "exactly as tall as".

    This holds for equatives because `eq_fine_entails_coarse` shows
    the finest equative (largest lo) entails all coarser equatives. -/
theorem just_vacuous_iff (p : G → D → Prop) (finest : G)
    (h_strongest : ∀ g, atLeastAsStrong p finest g) (μ_x : D) :
    approxJust p finest μ_x ↔ p finest μ_x := by
  constructor
  · exact fun ⟨h, _⟩ => h
  · intro h; exact ⟨h, fun _ _ => h_strongest _⟩

omit [LinearOrder D] in
/-- Comparative prediction: if the finest grain is NOT the strongest
    at some coarser grain g, then *just* rules out g.
    "Just taller than d_c" entails "not taller at grain g".

    This holds for comparatives because `comp_coarse_entails_fine`
    shows the finest comparative (smallest hi) does NOT entail
    coarser comparatives (larger hi). -/
theorem just_rules_out (p : G → D → Prop) (finest g : G)
    (h_not_strongest : ¬ atLeastAsStrong p finest g)
    (μ_x : D) (hjust : approxJust p finest μ_x) : ¬ p g μ_x := by
  intro hg; exact h_not_strongest (hjust.2 g hg)

end JustTheory

/-! ### Granularity–Question Bridge -/

/-! ### Grain width → partition → question width

The degree-level infrastructure above handles what happens *within* a
grain cell (equatives compare against infimum, comparatives against
supremum). This section connects to the *question* level: how grain
width determines a partition on the scale, and how finer grains produce
wider questions ([deo-thomas-2025] §3.1.2–3.2).

The key chain:
- Grain width ε induces a partition via ⌊d/ε⌋ (integer division)
- If ε₁ ∣ ε₂, the ε₁-partition refines the ε₂-partition
- Partition refinement implies question width (`refinement_implies_wider`)

The first two steps live here; the third is composed in the study file
since it requires `toIssue` from inquisitive semantics. -/

section GranularityQuestion

/-- A granularity QUD on `Fin n`, parameterized by grain width ε.

    Maps each degree d to grain index ⌊d/ε⌋, inducing a partition where
    degrees in the same grain cell are indistinguishable — the ℕ grain
    partition (`Setoid.ker (· / ε)`, `Core/Algebra/Order/Grain.lean`)
    restricted to `Fin n` and packaged as a `QUD`.

    [deo-thomas-2025] definition (22): γ maps each point p to a cell I
    of a partition such that p ∈ I. For uniform grain width ε on a discrete
    scale, this is exactly integer division by ε. -/
def granQUD (n : Nat) (ε : Nat) : QUD (Fin n) :=
  QUD.ofProject (λ w => w.val / ε)

/-- Finer granularity induces partition refinement.

    [deo-thomas-2025] §3.1.2, (23): if ε₁ divides ε₂ (finer grain
    fits evenly into coarser grain), then the ε₁-partition refines the
    ε₂-partition. Every fine cell is contained in exactly one coarse cell. -/
theorem finer_granularity_refines (n ε₁ ε₂ : Nat) (hdvd : ε₁ ∣ ε₂) :
    QUD.refines (granQUD n ε₁) (granQUD n ε₂) := by
  intro w v h
  simp only [granQUD, QUD.ofProject_sameAnswer_iff] at *
  exact Nat.ker_div_le_of_dvd hdvd h

end GranularityQuestion

end Degree.Granularity
