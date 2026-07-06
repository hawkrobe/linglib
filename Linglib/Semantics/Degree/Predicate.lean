import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Max
import Mathlib.Tactic.NormNum
import Linglib.Core.Order.Boundedness
import Linglib.Core.Order.Comparison

/-!
# Degree predicates + monotonicity
[fox-hackl-2006] [kennedy-2015] [geurts-nouwen-2007] [nouwen-2010] [partee-1987]

Predicate transformers over a measure function `μ : W → α`:

- `IsUpwardMonotone` / `IsDownwardMonotone` / `IsConstant` / `AdmitsOptimum`
- `typeLower` (Partee 1987 existential lowering)
- monotonicity / anti-Horn-scale lemmas about the `Core.Order.Comparison.over`
  degree predicates (general)

The five degree predicates ("exactly", "at least", "more than", "at most",
"less than") are `Core.Order.Comparison.{eq,ge,gt,le,lt}.over μ` directly: the
reified `Core.Order.Comparison` IS the canonical scale-comparison primitive, so
there is no separate named family. `c.over μ n` is a `Set W`; `w ∈ c.over μ n ↔
c.rel (μ w) n` (`Comparison.mem_over`), and `c.rel` unfolds to the order
relation per case.
-/

namespace Degree

open Core.Order

/-! ### Informativity on Scales -/

variable {α : Type*} [LinearOrder α]

/-- A family of propositions indexed by scale values is **upward monotone**
    (entailments go from smaller to larger values).
    Kennedy: "tall" — if x is tall, x is tall-or-more.
    Rouillard: E-TIA with telic VP — if event fits in n days, it fits in m ≥ n days. -/
def IsUpwardMonotone {W : Type*} (P : α → W → Prop) : Prop :=
  ∀ (x y : α), x ≤ y → ∀ w, P x w → P y w

/-- A family is **downward monotone**: entailments go from larger to smaller.
    Rouillard: E-TIA with atelic VP — if sick during n-day time, sick during m ≤ n day time. -/
def IsDownwardMonotone {W : Type*} (P : α → W → Prop) : Prop :=
  ∀ (x y : α), x ≤ y → ∀ w, P y w → P x w

/-- A family is **constant**: every value yields the same proposition.
    This is information collapse — no value is more informative than another.
    Occurs when a family is both upward and downward monotone. -/
def IsConstant {W : Type*} (P : α → W → Prop) : Prop :=
  ∀ (x y : α) (w : W), P x w ↔ P y w

/-- If P is both upward and downward monotone, it is constant. -/
theorem bimonotone_constant {W : Type*} (P : α → W → Prop)
    (hUp : IsUpwardMonotone P) (hDown : IsDownwardMonotone P) :
    IsConstant P := by
  intro x y w
  constructor
  · intro hx
    rcases le_total x y with h | h
    · exact hUp x y h w hx
    · exact hDown y x h w hx
  · intro hy
    rcases le_total y x with h | h
    · exact hUp y x h w hy
    · exact hDown x y h w hy

/-- **Informativity licensing**: a scale admits a well-defined optimum iff
    it is NOT constant. When the family is constant (information collapse),
    no grammatical element operating on that scale is felicitous.

    This is the abstract pattern shared by:
    - Kennedy's Interpretive Economy: degree modifiers require non-trivial
      scale contribution
    - Rouillard's MIP: TIA numerals require maximally informative values -/
def AdmitsOptimum {W : Type*} (P : α → W → Prop) : Prop :=
  ¬ IsConstant P

/-- Bimonotone families do not admit an optimum: if a family is both upward
    and downward monotone, it collapses to a constant and no element is
    maximally informative. This is the abstract core of why open-scale
    degree modification and atelic-VP E-TIAs are both blocked. -/
theorem bimonotone_no_optimum {W : Type*} (P : α → W → Prop)
    (hUp : IsUpwardMonotone P) (hDown : IsDownwardMonotone P) :
    ¬ AdmitsOptimum P :=
  fun h => h (bimonotone_constant P hUp hDown)

/-! ### Maximal informativity is downstream -/

/-! The cross-world entailment-based `IsMaxInf` (Fox 2007 / vFFI 2014 /
    Beck-Rullmann 1999 / Rouillard 2026) is linguistic substrate, not
    pure order theory — it lives in
    `Semantics/Entailment/Extremum.lean`. The per-world
    specialization is just `IsLeast {y | P y w} x` from mathlib
    (`Mathlib.Order.Bounds.Defs`); the per-world↔cross-world bridge under
    monotonicity is mathlib's `MonotoneOn.map_isLeast` family
    (`Mathlib.Order.Bounds.Image`). -/

/-! ### Licensing Predictions (Data-Level) -/

/-- Closed scales predict licensing (Kennedy: "completely full" ✓;
    Rouillard: telic VP E-TIA ✓). -/
theorem closed_isLicensed : Boundedness.closed.IsLicensed := trivial

/-- Open scales predict blocking (Kennedy: "??completely tall";
    Rouillard: atelic VP E-TIA ✗). -/
theorem open_notLicensed : ¬ Boundedness.open_.IsLicensed := id

/-! ### Degree Properties ([fox-hackl-2006]) -/

/-! ### Degree properties as `Comparison.over`

The five degree predicates covering all comparison relations are
`Core.Order.Comparison.{eq,ge,gt,le,lt}.over μ` directly — there is no separate
named family. `c.over μ d : Set W`, with `w ∈ c.over μ d ↔ c.rel (μ w) d`
(`Comparison.mem_over`). These are the building blocks for the named numeral
meanings (`Semantics.Numerals.atLeastMeaning` etc.) and degree question
semantics.

- `Comparison.ge.over μ`: closed `≥`, always has max⊨
- `Comparison.gt.over μ`: open `>`, fails on dense scales
- `Comparison.eq.over μ`: equality `=`, trivially has max⊨
- `Comparison.le.over μ`: closed `≤`
- `Comparison.lt.over μ`: open `<`

The key divergence: on ℕ, `>` collapses to `≥` with successor, so both
have `HasMaxInf`. On dense scales, `>` yields an open set with no max⊨.
This is the UDM prediction ([fox-hackl-2006]). -/

/-- "At least" is downward monotone: weaker thresholds are easier to satisfy. -/
theorem geOver_downMono {W : Type*} (μ : W → α) : IsDownwardMonotone (Comparison.ge.over μ) :=
  fun _ _ hxy _ hy => le_trans hxy hy

/-- "More than" is downward monotone: weaker thresholds are easier to satisfy. -/
theorem gtOver_downMono {W : Type*} (μ : W → α) : IsDownwardMonotone (Comparison.gt.over μ) :=
  fun _ _ hxy _ hy => lt_of_le_of_lt hxy hy

/-- On ℕ, `>` collapses to `≥` with successor: "more than m" ↔ "at least m+1".
    This is the discrete equivalence that density breaks. -/
theorem gtOver_eq_geOver_succ {W : Type*} (μ : W → ℕ) (m : ℕ) (w : W) :
    w ∈ Comparison.gt.over μ m ↔ w ∈ Comparison.ge.over μ (m + 1) :=
  Iff.rfl

/-! IsMaxInf-flavored consequences of these degree predicates
    (`atLeast_hasMaxInf`, `moreThan_noMaxInf`, `isMaxInf_atLeast_iff_eq`,
    `moreThan_nat_hasMaxInf`) live in
    `Semantics/Entailment/Extremum.lean` since they depend on
    the linguistic-substrate `IsMaxInf` predicate. -/

/-! ### Existential Lowering (Type-Shifting) -/

/-! ## Existential lowering: exact → "at least"

[partee-1987]'s BE + iota + existential closure, applied to a degree
property: from an exact reading `exact d w` ("the measure equals `d`"),
existentially close to `∃ d' ≥ d, exact d' w`. On any reflexive linear
order this collapses to `Comparison.ge.over μ d w` — witness `d' := μ w`.

This is the formal content of [kennedy-2015]'s "de-Fregean" derivation
of the lower-bound numeral reading from the exact reading. The collapse
generalizes Numeral type-shifting to arbitrary scales. -/

/-- Existentially lower an exact-style degree property to its lower-bound
    counterpart: there exists some `d' ≥ d` such that the exact property
    holds at `d'`. -/
def typeLower {W : Type*} (exact : α → W → Prop) (d : α) (w : W) : Prop :=
  ∃ d', d' ≥ d ∧ exact d' w

/-- **Type-shift collapse**: existentially lowering the exact property
    `Comparison.eq.over μ` yields the lower-bound property `Comparison.ge.over μ`. -/
theorem typeLower_eqOver_iff {W : Type*} (μ : W → α) (d : α) (w : W) :
    typeLower (fun d' w => w ∈ Comparison.eq.over μ d') d w ↔ w ∈ Comparison.ge.over μ d := by
  simp only [Comparison.mem_over, Comparison.rel, typeLower, ge_iff_le]
  refine ⟨?_, fun h => ⟨μ w, h, rfl⟩⟩
  rintro ⟨d', hd', heq⟩
  exact heq.symm ▸ hd'

/-! ### [kennedy-2015]'s De-Fregean GQ -/

/-! ## A unified GQ denotation via `Core.Order.Comparison`

[kennedy-2015] proposes a single denotation for modified and
unmodified numerals: `λP. max{d | #P ≥ d} REL m`, where the only parameter
distinguishing surface forms is the relation `REL ∈ {=, ≥, >, ≤, <}`.

Specialised to a property of the form `Comparison.ge.over μ`, the maximum degree
satisfying `Comparison.ge.over μ d w` is `μ w` itself, so Kennedy's denotation
collapses to `c.rel (μ w) m` — i.e. `w ∈ c.over μ m` (`Comparison.mem_over`).
The reified `Core.Order.Comparison` (in `Comparison.lean`) IS this canonical
comparison primitive; it selects which `rel`/`interval` to use, and the Class
A vs Class B distinction ([geurts-nouwen-2007], [nouwen-2010]) is its
`Comparison.boundary_mem` (non-strict comparisons keep the endpoint). -/

/-! ### Anti-Horn-Scale Lemmas (general) -/

/-! ## Why exact bare numerals are not part of a Horn scale

[kennedy-2015] argues that bare numerals (under their exact reading) are
**not monotone in their numerical argument** — neither upward nor downward —
so they fail the Horn-scale criterion. The classic Horn scale `⟨1, 2, 3, …⟩`
presupposes upward monotonicity; the dual scale `⟨…, 3, 2, 1⟩` presupposes
downward monotonicity. Kennedy's unified GQ accommodates both modifier
directions without needing a Horn scale at all.

The lemmas below state the failure-of-monotonicity and weakness-vs-exact
results purely in terms of `Comparison.{eq,ge,gt}.over` — independent of any
specific scale. The Nat-specific results in `Semantics/Numerals/Basic.lean`
are immediate corollaries. -/

/-- "More than `d`" and "exactly `d`" are disjoint (general). -/
theorem gtOver_disjoint_eqOver {W : Type*} (μ : W → α) (d : α) (w : W) :
    ¬ (w ∈ Comparison.eq.over μ d ∧ w ∈ Comparison.gt.over μ d) := by
  simp only [Comparison.mem_over, Comparison.rel, gt_iff_lt]
  rintro ⟨h₁, h₂⟩
  exact lt_irrefl d (h₁ ▸ h₂)

/-- "Less than `d`" and "exactly `d`" are disjoint (general). -/
theorem ltOver_disjoint_eqOver {W : Type*} (μ : W → α) (d : α) (w : W) :
    ¬ (w ∈ Comparison.eq.over μ d ∧ w ∈ Comparison.lt.over μ d) := by
  simp only [Comparison.mem_over, Comparison.rel]
  rintro ⟨h₁, h₂⟩
  exact lt_irrefl d (h₁ ▸ h₂)

/-- Bare exact meaning entails "at least" (general half of Class B inclusion). -/
theorem eqOver_imp_geOver {W : Type*} (μ : W → α) (d : α) (w : W) :
    w ∈ Comparison.eq.over μ d → w ∈ Comparison.ge.over μ d := by
  simp only [Comparison.mem_over, Comparison.rel, ge_iff_le]
  exact fun h => h ▸ le_refl _

/-- Bare exact meaning entails "at most" (general; symmetric to above). -/
theorem eqOver_imp_leOver {W : Type*} (μ : W → α) (d : α) (w : W) :
    w ∈ Comparison.eq.over μ d → w ∈ Comparison.le.over μ d := by
  simp only [Comparison.mem_over, Comparison.rel]
  exact fun h => h ▸ le_refl _

/-- "At least `d`" is strictly weaker than "exactly `d`" (general). Given a
    witness world `w` with `μ w = d'` where `d < d'`, "at least `d`" holds
    but "exactly `d`" fails. -/
theorem geOver_strictly_weaker_than_eqOver {W : Type*} (μ : W → α)
    {d d' : α} (hlt : d < d') {w : W} (hμ : μ w = d') :
    w ∈ Comparison.ge.over μ d ∧ w ∉ Comparison.eq.over μ d := by
  simp only [Comparison.mem_over, Comparison.rel, ge_iff_le]
  refine ⟨?_, ?_⟩
  · rw [hμ]; exact le_of_lt hlt
  · rw [hμ]; exact ne_of_gt hlt

/-- Exact equality is **not upward-monotone** (general). Given two distinct
    boundary values `d ≤ d'` and a witness world with `μ w = d`, the universal
    "if exact at `d` then exact at `d'`" fails — `μ w` cannot equal both. -/
theorem eqOver_not_upward_monotone {W : Type*} (μ : W → α)
    {d d' : α} (hne : d ≠ d') (hle : d ≤ d') {w : W} (hμ : μ w = d) :
    ¬ ∀ x y, x ≤ y → w ∈ Comparison.eq.over μ x → w ∈ Comparison.eq.over μ y := by
  simp only [Comparison.mem_over, Comparison.rel]
  intro h
  exact hne ((h d d' hle hμ).symm.trans hμ).symm

/-- Exact equality is **not downward-monotone** (general). Symmetric to above. -/
theorem eqOver_not_downward_monotone {W : Type*} (μ : W → α)
    {d d' : α} (hne : d ≠ d') (hle : d' ≤ d) {w : W} (hμ : μ w = d) :
    ¬ ∀ x y, y ≤ x → w ∈ Comparison.eq.over μ x → w ∈ Comparison.eq.over μ y := by
  simp only [Comparison.mem_over, Comparison.rel]
  intro h
  exact hne ((h d d' hle hμ).symm.trans hμ).symm

/-- Universal closure (the alternative to existential closure) is
    unsatisfiable when the closure range contains two distinct values:
    no single `x` can equal two different `k`s. This rules out the
    universal-closure reading of Partee's iota generally. -/
theorem distinct_no_universal_witness {α : Type*} (k₁ k₂ : α) (hne : k₁ ≠ k₂) :
    ¬ ∃ x, ∀ k, k = k₁ ∨ k = k₂ → x = k := by
  rintro ⟨x, h⟩
  exact hne ((h k₁ (Or.inl rfl)).symm.trans (h k₂ (Or.inr rfl)))

/-! ### "At most" Symmetry (Rouillard's direction) -/

/-- "At most" is upward monotone: larger thresholds are easier to satisfy. -/
theorem leOver_upMono {W : Type*} (μ : W → α) : IsUpwardMonotone (Comparison.le.over μ) :=
  fun _ _ hxy _ hy => le_trans hy hxy

/-! IsMaxInf-flavored consequences of "at most" (`atMost_hasMaxInf`,
    `isMaxInf_atMost_iff_eq`) live in
    `Semantics/Entailment/Extremum.lean`. -/

end Degree
