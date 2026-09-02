import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Max
import Mathlib.Tactic.NormNum
import Linglib.Semantics.Degree.Boundedness
import Linglib.Semantics.Degree.Comparison

/-!
# Degree predicates + monotonicity
[fox-hackl-2006] [kennedy-2015] [geurts-nouwen-2007] [nouwen-2010] [partee-1987]

Predicate transformers over a measure function `μ : W → α`:

- `IsConstant` (information collapse; monotonicity is mathlib's
  `Monotone`/`Antitone` under the pointwise order on `W → Prop`)
- `typeLower` (Partee 1987 existential lowering)
- monotonicity / anti-Horn-scale lemmas about the `Degree.Comparison.over`
  degree predicates (general)

The five degree predicates ("exactly", "at least", "more than", "at most",
"less than") are `Degree.Comparison.{eq,ge,gt,le,lt}.over μ` directly: the
reified `Degree.Comparison` IS the canonical scale-comparison primitive, so
there is no separate named family. `c.over μ n` is a `Set W`; `w ∈ c.over μ n ↔
c.rel (μ w) n` (`Comparison.mem_over`), and `c.rel` unfolds to the order
relation per case.
-/

namespace Degree


/-! ### Informativity on Scales -/

variable {α : Type*} [LinearOrder α]

-- A family of propositions indexed by scale values is **upward monotone**
-- (entailments go from smaller to larger; Kennedy: if x is tall, x is
-- tall-or-more; Rouillard: telic E-TIA) exactly when it is mathlib's
-- `Monotone` under the pointwise order on `W → Prop` (`p ≤ q ↔ p → q`);
-- downward monotone (atelic E-TIA) is `Antitone`. No local aliases.

/-- A family is **constant**: every value yields the same proposition.
    This is information collapse — no value is more informative than another.
    Occurs when a family is both upward and downward monotone. -/
def IsConstant {W : Type*} (P : α → W → Prop) : Prop :=
  ∀ (x y : α) (w : W), P x w ↔ P y w

/-- If P is both upward and downward monotone, it is constant. -/
theorem bimonotone_constant {W : Type*} (P : α → W → Prop)
    (hUp : Monotone P) (hDown : Antitone P) :
    IsConstant P := by
  intro x y w
  constructor
  · intro hx
    rcases le_total x y with h | h
    · exact hUp h w hx
    · exact hDown h w hx
  · intro hy
    rcases le_total y x with h | h
    · exact hUp h w hy
    · exact hDown h w hy

/-! ### Maximal informativity is downstream -/

/-! The cross-world `IsMaxInf` (`IsLeast` of the image of the true set under the degree
    property) lives in `Semantics/Alternatives/Extremum.lean`; the per-world reading is
    `IsLeast {y | w ∈ P y} x`, and mathlib's `Monotone.map_isLeast` bridges the two. -/

/-! ### Licensing Predictions (Data-Level) -/

/-! ### Degree Properties ([fox-hackl-2006]) -/

/-! ### Degree properties as `Comparison.over`

The five degree predicates covering all comparison relations are
`Degree.Comparison.{eq,ge,gt,le,lt}.over μ` directly — there is no separate
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

-- "At least"/"more than" are threshold-antitone and "at most" is
-- threshold-monotone: `Comparison.antitone_ge_over`, `antitone_gt_over`,
-- `monotone_le_over` (Core/Order/Comparison.lean).

/-- On ℕ, `>` collapses to `≥` with successor: "more than m" ↔ "at least m+1".
    This is the discrete equivalence that density breaks. -/
theorem gtOver_eq_geOver_succ {W : Type*} (μ : W → ℕ) (m : ℕ) (w : W) :
    w ∈ Comparison.gt.over μ m ↔ w ∈ Comparison.ge.over μ (m + 1) :=
  Iff.rfl

/-! IsMaxInf-flavored consequences of these degree predicates
    (`hasMaxInf_ge_over`, `not_hasMaxInf_gt_over`, `isMaxInf_ge_over_iff`,
    `hasMaxInf_gt_over_nat`) live in `Semantics/Alternatives/Extremum.lean`. -/

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

/-! ## A unified GQ denotation via `Degree.Comparison`

[kennedy-2015] proposes a single denotation for modified and
unmodified numerals: `λP. max{d | #P ≥ d} REL m`, where the only parameter
distinguishing surface forms is the relation `REL ∈ {=, ≥, >, ≤, <}`.

Specialised to a property of the form `Comparison.ge.over μ`, the maximum degree
satisfying `Comparison.ge.over μ d w` is `μ w` itself, so Kennedy's denotation
collapses to `c.rel (μ w) m` — i.e. `w ∈ c.over μ m` (`Comparison.mem_over`).
The reified `Degree.Comparison` (in `Comparison.lean`) IS this canonical
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

/-! IsMaxInf-flavored consequences of "at most" (`hasMaxInf_le_over`,
    `isMaxInf_le_over_iff`) live in
    `Semantics/Alternatives/Extremum.lean`. -/

end Degree
