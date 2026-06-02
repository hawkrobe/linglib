import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Max
import Mathlib.Tactic.NormNum
import Linglib.Core.Scales.Defs

/-!
# Core/Scales/Predicate.lean — degree predicates + monotonicity
@cite{fox-2007} @cite{kennedy-2015} @cite{geurts-nouwen-2007} @cite{nouwen-2010} @cite{partee-1987}

Predicate transformers and degree-relative comparison primitives, parameterized
by a measure function `μ : W → α`:

- `IsUpwardMonotone` / `IsDownwardMonotone` / `IsConstant` / `AdmitsOptimum`
- `eqDeg` / `atLeastDeg` / `moreThanDeg` / `atMostDeg` / `lessThanDeg` (Fox 2007 §2)
- `relationalGQ` (unified Kennedy 2015 GQ denotation)
- `typeLower` (Partee 1987 existential lowering)
- Anti-Horn-scale lemmas (general)

This file is part of the Phase A decomposition of the legacy
`Core/Scales/Scale.lean` dumping ground (master plan v4).

`relationalGQ` stays here as the canonical scale-comparison primitive: it is
domain-general (numerals, measure phrases, and gradable comparatives all reduce
to it), and the reified `Core.Scale.Comparison` interprets into it.
-/

namespace Core.Scale

-- ════════════════════════════════════════════════════
-- § 3. Informativity on Scales
-- ════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════
-- § 3b. Maximal informativity is downstream
-- ════════════════════════════════════════════════════

/-! The cross-world entailment-based `IsMaxInf` (Fox 2007 / vFFI 2014 /
    Beck-Rullmann 1999 / Rouillard 2026) is linguistic substrate, not
    pure order theory — it lives in
    `Semantics/Entailment/Extremum.lean`. The per-world
    specialization is just `IsLeast {y | P y w} x` from mathlib
    (`Mathlib.Order.Bounds.Defs`); the per-world↔cross-world bridge under
    monotonicity is mathlib's `MonotoneOn.map_isLeast` family
    (`Mathlib.Order.Bounds.Image`). -/

-- ════════════════════════════════════════════════════
-- § 5. Licensing Predictions (Data-Level)
-- ════════════════════════════════════════════════════

/-- Closed scales predict licensing (Kennedy: "completely full" ✓;
    Rouillard: telic VP E-TIA ✓). -/
theorem closed_isLicensed : Boundedness.closed.isLicensed = true := rfl

/-- Open scales predict blocking (Kennedy: "??completely tall";
    Rouillard: atelic VP E-TIA ✗). -/
theorem open_notLicensed : Boundedness.open_.isLicensed = false := rfl

-- ════════════════════════════════════════════════════
-- § 6. Degree Properties (@cite{fox-2007} §2)
-- ════════════════════════════════════════════════════

/-! ### Degree properties for comparison relations

Five degree properties covering all comparison relations, parameterized by
a measure function `μ : W → α`. These are the building blocks for the named
numeral meanings (`Semantics.Numerals.atLeastMeaning` etc.) and degree
question semantics.

- `atLeastDeg`: closed `≥`, always has max⊨
- `moreThanDeg`: open `>`, fails on dense scales
- `eqDeg`: equality `=`, trivially has max⊨
- `atMostDeg`: closed `≤`
- `lessThanDeg`: open `<`

The key divergence: on ℕ, `>` collapses to `≥` with successor, so both
have `HasMaxInf`. On dense scales, `>` yields an open set with no max⊨.
This is the UDM prediction (@cite{fox-2007} §2). -/

/-- Degree property for "exactly d": the measure at w equals d. -/
def eqDeg {W : Type*} (μ : W → α) : α → W → Prop :=
  fun d w => μ w = d

/-- Degree property for "at least d": the measure at w meets or exceeds d. -/
def atLeastDeg {W : Type*} (μ : W → α) : α → W → Prop :=
  fun d w => μ w ≥ d

/-- Degree property for "more than d": the measure strictly exceeds d. -/
def moreThanDeg {W : Type*} (μ : W → α) : α → W → Prop :=
  fun d w => μ w > d

/-- Degree property for "at most d": the measure at w is at most d. -/
def atMostDeg {W : Type*} (μ : W → α) : α → W → Prop :=
  fun d w => μ w ≤ d

/-- Degree property for "less than d": the measure is strictly less than d. -/
def lessThanDeg {W : Type*} (μ : W → α) : α → W → Prop :=
  fun d w => μ w < d

/-- "At least" is downward monotone: weaker thresholds are easier to satisfy. -/
theorem atLeastDeg_downMono {W : Type*} (μ : W → α) : IsDownwardMonotone (atLeastDeg μ) :=
  fun _ _ hxy _ hy => le_trans hxy hy

/-- "More than" is downward monotone: weaker thresholds are easier to satisfy. -/
theorem moreThanDeg_downMono {W : Type*} (μ : W → α) : IsDownwardMonotone (moreThanDeg μ) :=
  fun _ _ hxy _ hy => lt_of_le_of_lt hxy hy

/-- On ℕ, `>` collapses to `≥` with successor: "more than m" ↔ "at least m+1".
    This is the discrete equivalence that density breaks. -/
theorem moreThan_eq_atLeast_succ {W : Type*} (μ : W → ℕ) (m : ℕ) (w : W) :
    moreThanDeg μ m w ↔ atLeastDeg μ (m + 1) w :=
  Iff.rfl

/-! IsMaxInf-flavored consequences of these degree predicates
    (`atLeast_hasMaxInf`, `moreThan_noMaxInf`, `isMaxInf_atLeast_iff_eq`,
    `moreThan_nat_hasMaxInf`) live in
    `Semantics/Entailment/Extremum.lean` since they depend on
    the linguistic-substrate `IsMaxInf` predicate. -/

-- ════════════════════════════════════════════════════
-- § 6c. Existential Lowering (Type-Shifting)
-- ════════════════════════════════════════════════════

/-! ## Existential lowering: exact → "at least"

@cite{partee-1987}'s BE + iota + existential closure, applied to a degree
property: from an exact reading `exact d w` ("the measure equals `d`"),
existentially close to `∃ d' ≥ d, exact d' w`. On any reflexive linear
order this collapses to `atLeastDeg μ d w` — witness `d' := μ w`.

This is the formal content of @cite{kennedy-2015}'s "de-Fregean" derivation
of the lower-bound numeral reading from the exact reading. The collapse
generalizes Numeral type-shifting to arbitrary scales. -/

/-- Existentially lower an exact-style degree property to its lower-bound
    counterpart: there exists some `d' ≥ d` such that the exact property
    holds at `d'`. -/
def typeLower {W : Type*} (exact : α → W → Prop) (d : α) (w : W) : Prop :=
  ∃ d', d' ≥ d ∧ exact d' w

/-- **Type-shift collapse**: `typeLower (eqDeg μ) = atLeastDeg μ`. -/
theorem typeLower_eqDeg_iff {W : Type*} (μ : W → α) (d : α) (w : W) :
    typeLower (eqDeg μ) d w ↔ atLeastDeg μ d w := by
  refine ⟨?_, fun h => ⟨μ w, h, rfl⟩⟩
  rintro ⟨d', hd', heq⟩
  -- heq : eqDeg μ d' w  unfolds to  μ w = d'
  have heq' : μ w = d' := heq
  show μ w ≥ d
  exact heq'.symm ▸ hd'

instance atLeastDeg.decidable {W : Type*} [DecidableLE α] (μ : W → α)
    (d : α) (w : W) : Decidable (atLeastDeg μ d w) := by
  unfold atLeastDeg; infer_instance

instance atMostDeg.decidable {W : Type*} [DecidableLE α] (μ : W → α)
    (d : α) (w : W) : Decidable (atMostDeg μ d w) := by
  unfold atMostDeg; infer_instance

instance moreThanDeg.decidable {W : Type*} [DecidableLT α] (μ : W → α)
    (d : α) (w : W) : Decidable (moreThanDeg μ d w) := by
  unfold moreThanDeg; infer_instance

instance lessThanDeg.decidable {W : Type*} [DecidableLT α] (μ : W → α)
    (d : α) (w : W) : Decidable (lessThanDeg μ d w) := by
  unfold lessThanDeg; infer_instance

instance eqDeg.decidable {W : Type*} [DecidableEq α] (μ : W → α)
    (d : α) (w : W) : Decidable (eqDeg μ d w) := by
  unfold eqDeg; infer_instance

instance typeLower_eqDeg.decidable {W : Type*} (μ : W → α) (d : α) (w : W) :
    Decidable (typeLower (eqDeg μ) d w) :=
  decidable_of_iff _ (typeLower_eqDeg_iff μ d w).symm

-- ════════════════════════════════════════════════════
-- § 6d. @cite{kennedy-2015}'s De-Fregean GQ
-- ════════════════════════════════════════════════════

/-! ## A unified GQ denotation parameterized by the comparison relation

@cite{kennedy-2015} proposes a single denotation for modified and
unmodified numerals: `λP. max{d | #P ≥ d} REL m`, where the only parameter
distinguishing surface forms is the relation `REL ∈ {=, ≥, >, ≤, <}`.

Specialised to a property of the form `atLeastDeg μ`, the maximum degree
satisfying `atLeastDeg μ d w` is `μ w` itself, so Kennedy's denotation
collapses to `rel (μ w) m` — captured here as `relationalGQ rel μ m w`.

The five existing degree properties (`eqDeg`, `atLeastDeg`, `moreThanDeg`,
`atMostDeg`, `lessThanDeg`) are definitionally `relationalGQ` instantiated at
the corresponding relation. The Class A vs Class B distinction
(@cite{geurts-nouwen-2007}, @cite{nouwen-2010}) collapses to a structural
property of `rel`: Class B ↔ `IsRefl α rel`; Class A ↔ `IsIrrefl α rel`.

This is the canonical comparison primitive of the scale substrate; the reified
`Core.Scale.Comparison` (in `Comparison.lean`) selects which `rel` to use. -/

/-- Kennedy's unified GQ denotation: `(rel) (μ w) d`. The five named degree
    properties are definitionally equal to instantiations of this. -/
def relationalGQ {W : Type*} (rel : α → α → Prop) (μ : W → α) (d : α) (w : W) : Prop :=
  rel (μ w) d

omit [LinearOrder α] in
/-- Specialisation to `(· = ·)` recovers `eqDeg`. -/
theorem relationalGQ_eq_eqDeg {W : Type*} (μ : W → α) :
    relationalGQ (· = ·) μ = eqDeg μ := rfl

/-- Specialisation to `(· ≥ ·)` recovers `atLeastDeg`. -/
theorem relationalGQ_ge_eq_atLeastDeg {W : Type*} (μ : W → α) :
    relationalGQ (· ≥ ·) μ = atLeastDeg μ := rfl

/-- Specialisation to `(· > ·)` recovers `moreThanDeg`. -/
theorem relationalGQ_gt_eq_moreThanDeg {W : Type*} (μ : W → α) :
    relationalGQ (· > ·) μ = moreThanDeg μ := rfl

/-- Specialisation to `(· ≤ ·)` recovers `atMostDeg`. -/
theorem relationalGQ_le_eq_atMostDeg {W : Type*} (μ : W → α) :
    relationalGQ (· ≤ ·) μ = atMostDeg μ := rfl

/-- Specialisation to `(· < ·)` recovers `lessThanDeg`. -/
theorem relationalGQ_lt_eq_lessThanDeg {W : Type*} (μ : W → α) :
    relationalGQ (· < ·) μ = lessThanDeg μ := rfl

omit [LinearOrder α] in
/-- **Class B inclusion at the boundary** (general). If `rel` is reflexive,
    Kennedy's GQ holds at any world `w` whose measure equals the boundary `d`.
    Specialised to numerals: "at least 3" / "at most 3" hold at `w = 3`. -/
theorem relationalGQ_refl_at_boundary {W : Type*} {rel : α → α → Prop}
    [Std.Refl rel] (μ : W → α) {d : α} {w : W} (h : μ w = d) :
    relationalGQ rel μ d w := by
  show rel (μ w) d
  rw [h]; exact Std.Refl.refl _

omit [LinearOrder α] in
/-- **Class A exclusion at the boundary** (general). If `rel` is irreflexive,
    Kennedy's GQ fails at any world `w` whose measure equals the boundary `d`.
    Specialised to numerals: "more than 3" / "fewer than 3" fail at `w = 3`. -/
theorem relationalGQ_irrefl_at_boundary {W : Type*} {rel : α → α → Prop}
    [Std.Irrefl rel] (μ : W → α) {d : α} {w : W} (h : μ w = d) :
    ¬ relationalGQ rel μ d w := by
  intro hk
  have hdd : rel d d := h ▸ (hk : rel (μ w) d)
  exact (Std.Irrefl.irrefl (r := rel) d) hdd

-- ════════════════════════════════════════════════════
-- § 6e. Anti-Horn-Scale Lemmas (general)
-- ════════════════════════════════════════════════════

/-! ## Why exact bare numerals are not part of a Horn scale

@cite{kennedy-2015} argues that bare numerals (under their exact reading) are
**not monotone in their numerical argument** — neither upward nor downward —
so they fail the Horn-scale criterion. The classic Horn scale `⟨1, 2, 3, …⟩`
presupposes upward monotonicity; the dual scale `⟨…, 3, 2, 1⟩` presupposes
downward monotonicity. Kennedy's unified GQ accommodates both modifier
directions without needing a Horn scale at all.

The lemmas below state the failure-of-monotonicity and weakness-vs-exact
results purely in terms of `eqDeg` / `atLeastDeg` / `moreThanDeg` —
independent of any specific scale. The Nat-specific results in
`Semantics/Numerals/Basic.lean` are immediate corollaries. -/

/-- "More than `d`" and "exactly `d`" are disjoint (general). -/
theorem moreThanDeg_disjoint_eqDeg {W : Type*} (μ : W → α) (d : α) (w : W) :
    ¬ (eqDeg μ d w ∧ moreThanDeg μ d w) := by
  rintro ⟨h₁, h₂⟩
  exact lt_irrefl d (h₁ ▸ h₂)

/-- "Less than `d`" and "exactly `d`" are disjoint (general). -/
theorem lessThanDeg_disjoint_eqDeg {W : Type*} (μ : W → α) (d : α) (w : W) :
    ¬ (eqDeg μ d w ∧ lessThanDeg μ d w) := by
  rintro ⟨h₁, h₂⟩
  exact lt_irrefl d (h₁ ▸ h₂)

/-- Bare exact meaning entails "at least" (general half of Class B inclusion). -/
theorem eqDeg_imp_atLeastDeg {W : Type*} (μ : W → α) (d : α) (w : W) :
    eqDeg μ d w → atLeastDeg μ d w := fun h => h ▸ le_refl _

/-- Bare exact meaning entails "at most" (general; symmetric to above). -/
theorem eqDeg_imp_atMostDeg {W : Type*} (μ : W → α) (d : α) (w : W) :
    eqDeg μ d w → atMostDeg μ d w := fun h => h ▸ le_refl _

/-- "At least `d`" is strictly weaker than "exactly `d`" (general). Given a
    witness world `w` with `μ w = d'` where `d < d'`, "at least `d`" holds
    but "exactly `d`" fails. -/
theorem atLeastDeg_strictly_weaker_than_eqDeg {W : Type*} (μ : W → α)
    {d d' : α} (hlt : d < d') {w : W} (hμ : μ w = d') :
    atLeastDeg μ d w ∧ ¬ eqDeg μ d w := by
  refine ⟨?_, ?_⟩
  · show μ w ≥ d; rw [hμ]; exact le_of_lt hlt
  · show ¬ μ w = d; rw [hμ]; exact ne_of_gt hlt

/-- Exact `eqDeg` is **not upward-monotone** (general). Given two distinct
    boundary values `d ≤ d'` and a witness world with `μ w = d`, the universal
    "if exact at `d` then exact at `d'`" fails — `μ w` cannot equal both. -/
theorem eqDeg_not_upward_monotone {W : Type*} (μ : W → α)
    {d d' : α} (hne : d ≠ d') (hle : d ≤ d') {w : W} (hμ : μ w = d) :
    ¬ ∀ x y, x ≤ y → eqDeg μ x w → eqDeg μ y w := by
  intro h
  exact hne ((h d d' hle hμ).symm.trans hμ).symm

/-- Exact `eqDeg` is **not downward-monotone** (general). Symmetric to above. -/
theorem eqDeg_not_downward_monotone {W : Type*} (μ : W → α)
    {d d' : α} (hne : d ≠ d') (hle : d' ≤ d) {w : W} (hμ : μ w = d) :
    ¬ ∀ x y, y ≤ x → eqDeg μ x w → eqDeg μ y w := by
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

-- ════════════════════════════════════════════════════
-- § 7. "At most" Symmetry (Rouillard's direction)
-- ════════════════════════════════════════════════════

/-- "At most" is upward monotone: larger thresholds are easier to satisfy. -/
theorem atMostDeg_upMono {W : Type*} (μ : W → α) : IsUpwardMonotone (atMostDeg μ) :=
  fun _ _ hxy _ hy => le_trans hy hxy

/-! IsMaxInf-flavored consequences of `atMostDeg` (`atMost_hasMaxInf`,
    `isMaxInf_atMost_iff_eq`) live in
    `Semantics/Entailment/Extremum.lean`. -/

end Core.Scale
