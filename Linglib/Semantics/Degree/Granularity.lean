/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Basic
public import Mathlib.Data.Finset.Max
public import Linglib.Core.Algebra.Order.ToIntervalMod
public import Mathlib.Algebra.Order.Group.Defs
public import Linglib.Semantics.Questions.Partition.Basic

/-!
# Scale granularity

This file defines the granularity apparatus of [sauerland-stateva-2011], following
[krifka-2007]: a granularity function partitions a scale into cells of one width, the grain,
and a finer granularity has narrower cells. A grain cell around a degree is the open interval
of the grain's width centred on the degree, `mkGranInterval`, which contains the degree and
shrinks as the grain gets finer. A context supplies a finite set of available grain widths, and
scalar approximators select from it, *exactly* the finest and *approximately* the coarsest,
`finestWidth` and `coarsestWidth`. On a discrete scale a grain width induces the partition by
integer division, `granQUD`, which a dividing width refines, the bridge to the question
widths of [deo-thomas-2025].

## References

* [sauerland-stateva-2011]
* [krifka-2007]
* [deo-thomas-2025]
-/

@[expose] public section

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
- Partition refinement implies question width,
  `DeoThomas2025.widerThan_fromSetoid`

The first two steps live here. The paper's own grains are centred on the
multiples of ε rather than aligned at 0, `DeoThomas2025.grain`, and a finer
centred grain is wider without refining the coarser one. -/

section GranularityQuestion

/-- A granularity QUD on `Fin n`, parameterized by grain width ε.

    Maps each degree d to grain index ⌊d/ε⌋, inducing a partition where
    degrees in the same grain cell are indistinguishable — the ℕ grain
    partition (`Setoid.ker (· / ε)`, `Core/Algebra/Order/Grain.lean`)
    restricted to `Fin n`.

    [deo-thomas-2025] definition (22): γ maps each point p to a cell I
    of a partition such that p ∈ I. For uniform grain width ε on a discrete
    scale with cells aligned at 0, this is integer division by ε. -/
abbrev granQUD (n : Nat) (ε : Nat) : Setoid (Fin n) := Setoid.ker (λ w => w.val / ε)

/-- Finer granularity induces partition refinement.

    [deo-thomas-2025] §3.1.2, (23): if ε₁ divides ε₂ (finer grain
    fits evenly into coarser grain), then the ε₁-partition refines the
    ε₂-partition. Every fine cell is contained in exactly one coarse cell. -/
theorem finer_granularity_refines (n ε₁ ε₂ : Nat) (hdvd : ε₁ ∣ ε₂) :
    granQUD n ε₁ ≤ granQUD n ε₂ :=
  Setoid.le_def.2 λ h => Setoid.le_def.1 (Nat.ker_div_le_of_dvd hdvd) h

end GranularityQuestion

end Degree.Granularity
