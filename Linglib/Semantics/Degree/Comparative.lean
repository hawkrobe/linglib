import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Bounds.Basic
import Linglib.Semantics.Entailment.AntiAdditivity
import Linglib.Core.Order.Comparison
import Linglib.Core.Order.Boundedness

/-!
# Framework-Independent Comparative Semantics
[rett-2026] [schwarzschild-2008] [von-stechow-1984] [hoeksema-1983]

Comparative semantics shared across all degree frameworks: the binary
`comparativeSem` / `equativeSem`, antonymy as scale reversal, and
downward-entailingness of *than*-clauses. Both binary comparators are
measure-pullback predications of the reified `Core.Order.Comparison`
(`over` at a point standard, `overSet` at a set standard);
`comparativeSem_positive_eq_over` makes that an identity. The set-of-degrees
S-comparative ([hoeksema-1983]) *is* `Comparison.gt.overSet μ` directly — there is
no separate clausal-comparison definition; its properties are stated about `overSet`
here (anti-additivity) and reuse the `Comparison.overSet`/`over` API for the rest.
Framework-specific content for [rett-2026] (MAX, ambidirectionality, manner
implicature) lives in `Studies/Rett2026.lean`; [hoeksema-1983]'s polarity-asymmetry
consumers in `Studies/Hoeksema1983.lean`.

## Main declarations

* `comparativeSem` / `equativeSem` — "A is Adj-er / as-Adj-as B" via a directed
  measure on a scale.
* `gtOverSet_isAntiAdditive` — the S-comparative `Comparison.gt.overSet μ`
  ([hoeksema-1983]) is anti-additive in its standard: the algebraic source of
  *than*-clause NPI licensing.
* `mem_gtOverSet_iff_subset_Iio` — the set-of-degrees comparative as `Set.Iio`
  interval inclusion (strict mirror of mathlib's `mem_upperBounds_iff_subset_Iic`),
  collapsing to the binary comparator at a singleton via `Comparison.overSet_singleton`.
* `gtOverSet_eq_singleton_of_isGreatest` — a than-clause with a greatest degree
  reduces to that degree ([bhatt-pancheva-2004], order-theoretic form).
* `maxComparative` — the max-quantified clausal comparative ([von-stechow-1984],
  [rullmann-1995]): independent matrix/than witness predicates over `thanDegrees`,
  with the unique-witness collapse `maxComparative_unique`.
* `taller_shorter_antonymy` — antonymy is argument swap plus direction reversal.
* `comparative_iff_Iic_ssubset` — comparison as extent inclusion ([kennedy-1999]).
-/

namespace Degree

open Core.Order (ScalePolarity Comparison)

/-! ### Scale direction -/

/-- Comparative direction reuses scale polarity from `Core.Order`.
`positive` ("taller") makes MAX pick the highest degrees; `negative`
("shorter") the lowest. -/
abbrev ScaleDirection := ScalePolarity

/-- The compositional structure of a Degree Phrase (DegP).

In all degree frameworks, DegP is the syntactic locus where degree
comparison happens. The internal structure varies — Kennedy posits
`[DegP [Deg -er/as/est] [DegComplement than-clause]]`, Heim posits a
sentential `-er` operator — but the framework-independent taxonomy is
captured here. -/
inductive DegPType where
  /-- `-er` / *more*. -/
  | comparative
  /-- `as...as`. -/
  | equative
  /-- `-est` / *most*. -/
  | superlative
  /-- *too*. -/
  | excessive
  /-- *enough*. -/
  | sufficiency
  deriving DecidableEq, Repr

/-! ### Order-Sensitive MAX ([rett-2026]) -/

/-! ### Scale-sensitive maximality operator

[rett-2026]: MAX_c(X) picks the element(s)
of X that c-dominate all other members. For the `<` scale (`.lt`) this is the GLB
(earliest / smallest), for `>` (`.gt`) the LUB (latest / largest). The same operator
underlies both temporal connectives (*before*/*after*) and degree comparatives.

- Rett, J. (2026). Semantic ambivalence and expletive negation. Ms.
-/

/-- Order-sensitive maximality ([rett-2026], def. 1):
    MAX_c(X) = { x ∈ X | ∀ x' ∈ X, x' ≠ x → c.rel x x' }.
    The dominance relation is the reified `Core.Order.Comparison` rather than a
    lawless `R : α → α → Prop` — removing the "fake generality" of an unconstrained
    relation parameter. Each concrete `c` (`.lt`, `.gt`, `.ge`, …) names an
    order relation via `Comparison.rel`. -/
def maxOnScale {α : Type*} [Preorder α] (c : Comparison) (X : Set α) : Set α :=
  { x | x ∈ X ∧ ∀ x' ∈ X, x' ≠ x → c.rel x x' }

/-- MAX on a singleton is that singleton: MAX_c({x}) = {x}.
    The universal quantifier is vacuously satisfied, so this holds for any `c`. -/
theorem maxOnScale_singleton {α : Type*} [Preorder α] (c : Comparison) (x : α) :
    maxOnScale c {x} = {x} := by
  ext y
  simp only [maxOnScale, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨rfl, _⟩; rfl
  · rintro rfl
    exact ⟨rfl, fun x' hx' hne => absurd hx' hne⟩

/-- MAX₍<₎ on a closed interval `{x | s ≤ x ∧ x ≤ f}` is the singleton `{s}`.
    The minimum element s R-dominates all others on the `<` scale.
    Dual: MAX₍>₎ on the same interval is `{f}`. -/
theorem maxOnScale_lt_closedInterval {α : Type*} [LinearOrder α]
    (s f : α) (hsf : s ≤ f) :
    maxOnScale .lt { x : α | s ≤ x ∧ x ≤ f } = {s} := by
  ext x
  simp only [maxOnScale, Comparison.rel, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hxs, _⟩, hdom⟩
    by_contra hne
    have : s < x := lt_of_le_of_ne hxs (Ne.symm hne)
    have := hdom s ⟨le_refl _, hsf⟩ (ne_of_lt ‹s < x›)
    exact absurd ‹s < x› (not_lt.mpr (le_of_lt this))
  · rintro rfl
    exact ⟨⟨le_refl _, hsf⟩, fun x' ⟨hx's, _⟩ hne =>
      lt_of_le_of_ne hx's (Ne.symm hne)⟩

/-- MAX₍>₎ on a closed interval `{x | s ≤ x ∧ x ≤ f}` is the singleton `{f}`.
    The maximum element R-dominates all others on the `>` scale. -/
theorem maxOnScale_gt_closedInterval {α : Type*} [LinearOrder α]
    (s f : α) (hsf : s ≤ f) :
    maxOnScale .gt { x : α | s ≤ x ∧ x ≤ f } = {f} := by
  ext x
  simp only [maxOnScale, Comparison.rel, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨_, hxf⟩, hdom⟩
    by_contra hne
    have : x < f := lt_of_le_of_ne hxf hne
    have := hdom f ⟨hsf, le_refl _⟩ (ne_of_gt ‹x < f›)
    exact absurd ‹x < f› (not_lt.mpr (le_of_lt this))
  · rintro rfl
    exact ⟨⟨hsf, le_refl _⟩, fun x' ⟨_, hx'f⟩ hne =>
      lt_of_le_of_ne hx'f hne⟩

/-- A scalar construction f is **ambidirectional** iff
    applying f to a set B and to its complement Bᶜ yields the same result,
    because MAX picks the same informative boundary from both.
    This is the mechanism behind expletive negation licensing: when
    f(B) ↔ f(Bᶜ), negating B is truth-conditionally vacuous. -/
def isAmbidirectional {α : Type*} (f : Set α → Prop) (B : Set α) : Prop :=
  f B ↔ f Bᶜ


/-- **Bridge**: `maxOnScale .ge` applied to the "at least" degree set
    `{d | d ≤ μ(w)}` yields `{μ(w)}` — the singleton containing the true
    value. This connects the relational MAX to `IsMaxInf`.

    The convention: `maxOnScale c X` picks elements x ∈ X with `c.rel x x'` for
    all other x'. With `c = .ge`, this picks elements ≥ all others,
    i.e., the maximum. -/
theorem maxOnScale_atLeast_singleton {W α : Type*} [LinearOrder α] (μ : W → α) (w : W) :
    maxOnScale .ge { d : α | d ≤ μ w } = { μ w } := by
  ext x
  simp only [maxOnScale, Comparison.rel, Set.mem_setOf_eq, Set.mem_singleton_iff, ge_iff_le]
  constructor
  · rintro ⟨hx, hdom⟩
    by_contra hne
    have hlt : x < μ w := lt_of_le_of_ne hx hne
    have := hdom (μ w) (le_refl _) (Ne.symm hne)
    exact not_le.mpr hlt this
  · rintro rfl
    exact ⟨le_refl _, fun x' hx' hne => le_of_lt (lt_of_le_of_ne hx' hne)⟩

/-- MAX₍≥₎ on {d | d ≤ b} is {b}. Corollary of `maxOnScale_atLeast_singleton`
    with `μ = id`. Used by the comparative boundary theorems. -/
theorem maxOnScale_ge_atMost {α : Type*} [LinearOrder α] (b : α) :
    maxOnScale .ge {d | d ≤ b} = {b} :=
  maxOnScale_atLeast_singleton id b

/-- Grounding: `MAX₍≥₎` is mathlib's `IsGreatest` (the `x' = x` case of the
    dominance quantifier holds by reflexivity). -/
theorem maxOnScale_ge_eq {α : Type*} [Preorder α] (X : Set α) :
    maxOnScale .ge X = {x | IsGreatest X x} := by
  ext x
  simp only [maxOnScale, Comparison.rel, Set.mem_setOf_eq, IsGreatest,
    upperBounds, ge_iff_le]
  refine ⟨fun ⟨hx, hdom⟩ => ⟨hx, fun y hy => ?_⟩,
    fun ⟨hx, hub⟩ => ⟨hx, fun y hy _ => hub hy⟩⟩
  rcases eq_or_ne y x with rfl | hne
  · exact le_refl _
  · exact hdom y hy hne

/-! ### Comparative and equative semantics -/

section Direct
variable {Entity : Type*} {α : Type*} [Preorder α]

/-- Comparative semantics ([rett-2026], [schwarzschild-2008]): "A is Adj-er
than B" iff `μ a` exceeds `μ b` on the directed scale. Only `[Preorder α]`
— connectedness-agnostic background orderings (CSW confidence states)
are in scope. -/
def comparativeSem (μ : Entity → α) (a b : Entity) (dir : ScaleDirection) : Prop :=
  match dir with
  | .positive => μ a > μ b
  | .negative => μ a < μ b

/-- Equative semantics: "A is as Adj as B" iff `μ a ≥ μ b` on the directed scale. -/
def equativeSem (μ : Entity → α) (a b : Entity) (dir : ScaleDirection) : Prop :=
  match dir with
  | .positive => μ a ≥ μ b
  | .negative => μ a ≤ μ b

/-- **Grounding**: the positive binary comparative is the strict-`>` point
predication of `Core.Order.Comparison` at the standard `μ b` — not a reinvention. -/
theorem comparativeSem_positive_eq_over (μ : Entity → α) (a b : Entity) :
    comparativeSem μ a b .positive ↔ a ∈ Comparison.gt.over μ (μ b) := by
  simp only [comparativeSem, Comparison.mem_over, Comparison.rel]

/-- **Grounding**: the positive equative is the `≥` point predication of
`Core.Order.Comparison` at the standard `μ b`. -/
theorem equativeSem_positive_eq_over (μ : Entity → α) (a b : Entity) :
    equativeSem μ a b .positive ↔ a ∈ Comparison.ge.over μ (μ b) := by
  simp only [equativeSem, Comparison.mem_over, Comparison.rel]

/-- **MAX–direct bridge**: the direct comparison `μ a > μ b` is equivalent to
the MAX-based formulation. -/
theorem comparativeSem_eq_MAX {β : Type*} [LinearOrder β] (μ : Entity → β)
    (a b : Entity) :
    comparativeSem μ a b .positive ↔
      ∃ m ∈ maxOnScale .gt ({μ b} : Set β), μ a > m := by
  simp only [comparativeSem, maxOnScale_singleton, Set.mem_singleton_iff, exists_eq_left]

/-! ### Antonymy as scale reversal -/

/-- "A taller than B" ↔ "B shorter than A" — antonymy is argument swap plus
direction reversal. -/
theorem taller_shorter_antonymy (μ : Entity → α) (a b : Entity) :
    comparativeSem μ a b .positive ↔ comparativeSem μ b a .negative :=
  Iff.rfl

/-- Equative antonymy: "A as tall as B" ↔ "B as short as A". -/
theorem equative_antonymy (μ : Entity → α) (a b : Entity) :
    equativeSem μ a b .positive ↔ equativeSem μ b a .negative :=
  Iff.rfl

end Direct

/-! ### Boundary dependence -/

section Boundary
variable {α : Type*} [LinearOrder α]

/-- The comparative depends only on the boundary `μ_b`. -/
theorem comparative_boundary (μ_a μ_b : α) :
    (∃ m ∈ maxOnScale .ge {d | d ≤ μ_b}, μ_a > m) ↔ μ_a > μ_b := by
  rw [maxOnScale_ge_atMost]
  simp only [Set.mem_singleton_iff, exists_eq_left]

/-- The equative depends only on the boundary `μ_b`. -/
theorem equative_boundary (μ_a μ_b : α) :
    (∃ m ∈ maxOnScale .ge {d | d ≤ μ_b}, μ_a ≥ m) ↔ μ_a ≥ μ_b := by
  rw [maxOnScale_ge_atMost]
  simp only [Set.mem_singleton_iff, exists_eq_left]

end Boundary

/-! ### Set-of-degrees comparative

The S-comparative ([hoeksema-1983] §3.8 Def 7) generalizes `comparativeSem` from a
single standard to an arbitrary degree-set standard. It *is* `Comparison.gt.overSet μ`
(`μ ⁻¹' strictUpperBounds Δ`) — the strict-`>` set-standard predication of
`Core.Order.Comparison` — not a separate definition; the binary comparator is its
singleton case (`Comparison.overSet_singleton`). The properties below are stated
about `Comparison.gt.overSet μ` directly. Needs only `[Preorder D]`. -/

section SetOfDegrees
variable {Entity D : Type*} [Preorder D]

/-- The set-of-degrees comparative `Comparison.gt.overSet μ` ([hoeksema-1983]) as a
strict-interval inclusion: `y` clears the than-clause iff every standard degree lies
strictly below `μ y`. Strict mirror of mathlib's `mem_upperBounds_iff_subset_Iic`;
both faces are `Iff.rfl` siblings. -/
theorem mem_gtOverSet_iff_subset_Iio (μ : Entity → D) (Δ : Set D) (y : Entity) :
    y ∈ Comparison.gt.overSet μ Δ ↔ Δ ⊆ Set.Iio (μ y) :=
  Iff.rfl

/-- [hoeksema-1983] Fact 4: the S-comparative `Comparison.gt.overSet μ` is
anti-additive in its set-of-degrees argument — the algebraic source of NPI licensing
in clausal *than*-comparatives. -/
theorem gtOverSet_isAntiAdditive (μ : Entity → D) :
    Entailment.IsAntiAdditive (Comparison.gt.overSet μ) :=
  Entailment.isAntiAdditive_forall_mem (fun d y => d < μ y)

/-- **Reduction lemma** ([bhatt-pancheva-2004] §3, order-theoretic form): the
S-comparative `Comparison.gt.overSet μ` is determined by the *greatest* element of its
degree-set argument. Needs neither linearity nor density — only `[Preorder D]` and the
`IsGreatest` witness. -/
theorem gtOverSet_eq_singleton_of_isGreatest (μ : Entity → D) {Δ : Set D}
    {m : D} (hm : IsGreatest Δ m) :
    Comparison.gt.overSet μ Δ = Comparison.gt.overSet μ ({m} : Set D) := by
  ext y
  refine ⟨fun h d hd => ?_, fun h d hd => ?_⟩
  · rw [Set.mem_singleton_iff] at hd
    exact hd ▸ h hm.1
  · exact lt_of_le_of_lt (hm.2 hd) (h rfl)

end SetOfDegrees

/-! ### Max-quantified comparative
[von-stechow-1984] [rullmann-1995]

The clausal comparative: some matrix witness measures strictly above the
maximum of the *than*-clause degree set. Matrix and *than* restrictions are
independent predicates over an arbitrary witness sort, so heterogeneous
comparatives are the general case. Shared by `Studies/Wellwood2015`,
`Studies/Pasternak2019`, and `Semantics/Attitudes/Confidence`. -/

section MaxQuantified
variable {α D : Type*} [Preorder D]

/-- The than-clause degree set: degrees reached by some `Pthan`-witness.
Generalizes the phrasal principal-downset standard (`thanDegrees_singleton`)
to clausal standards with arbitrary witness predicates. -/
def thanDegrees (Pthan : α → Prop) (μ : α → D) : Set D :=
  {d | ∃ x, Pthan x ∧ d ≤ μ x}

/-- A unique standard collapses the than-clause degree set to the principal
downset of its measure — the phrasal standard (`ThanClause.thanClauseDenotation`). -/
theorem thanDegrees_singleton (μ : α → D) (b : α) :
    thanDegrees (· = b) μ = Set.Iic (μ b) := by
  ext d; simp [thanDegrees]

/-- The max-quantified comparative: the `Pthan` degree set has a greatest
element δ, and some `Pmatrix`-witness measures strictly above δ. -/
def maxComparative (Pmatrix Pthan : α → Prop) (μ : α → D) : Prop :=
  ∃ δ, IsGreatest (thanDegrees Pthan μ) δ ∧ ∃ x, Pmatrix x ∧ δ < μ x

/-- A unique `Pthan`-witness makes its measure the greatest than-clause degree. -/
theorem isGreatest_thanDegrees_of_unique {Pthan : α → Prop} {μ : α → D} {xb : α}
    (hb : Pthan xb) (hb_unique : ∀ x, Pthan x → x = xb) :
    IsGreatest (thanDegrees Pthan μ) (μ xb) :=
  ⟨⟨xb, hb, le_refl _⟩, fun _ ⟨x, hx, hle⟩ => hb_unique x hx ▸ hle⟩

/-- Under unique matrix and than witnesses, the max-quantified comparative
reduces to direct measure comparison. -/
theorem maxComparative_unique {Pmatrix Pthan : α → Prop} {μ : α → D} {xa xb : α}
    (ha : Pmatrix xa) (ha_unique : ∀ x, Pmatrix x → x = xa)
    (hb : Pthan xb) (hb_unique : ∀ x, Pthan x → x = xb) :
    maxComparative Pmatrix Pthan μ ↔ μ xb < μ xa := by
  constructor
  · rintro ⟨δ, hδ, x, hx, hlt⟩
    rw [ha_unique x hx] at hlt
    exact lt_of_le_of_lt (hδ.2 ⟨xb, hb, le_refl _⟩) hlt
  · exact fun hlt =>
      ⟨μ xb, isGreatest_thanDegrees_of_unique hb hb_unique, xa, ha, hlt⟩

/-- Max-quantified equative: the `Pthan` degree set has a greatest element
δ, and some `Pmatrix`-witness measures at least δ — `maxComparative` with
the weak threshold. -/
def maxEquative (Pmatrix Pthan : α → Prop) (μ : α → D) : Prop :=
  ∃ δ, IsGreatest (thanDegrees Pthan μ) δ ∧ ∃ x, Pmatrix x ∧ δ ≤ μ x

/-- The strict comparative entails the equative. -/
theorem maxComparative_entails_maxEquative (Pmatrix Pthan : α → Prop) (μ : α → D) :
    maxComparative Pmatrix Pthan μ → maxEquative Pmatrix Pthan μ :=
  fun ⟨δ, hδ, x, hx, hlt⟩ => ⟨δ, hδ, x, hx, hlt.le⟩

/-- Singleton collapse: comparing unique individuals is direct measure
comparison. -/
theorem maxComparative_eq_iff (μ : α → D) (xa xb : α) :
    maxComparative (· = xa) (· = xb) μ ↔ μ xb < μ xa :=
  maxComparative_unique rfl (fun _ h => h) rfl (fun _ h => h)

/-- Grounding in the S-comparative: when the than-clause degree set has a
maximum, a matrix witness clears it iff it clears the whole set
(`Comparison.gt.overSet`, via `gtOverSet_eq_singleton_of_isGreatest`). -/
theorem maxComparative_iff_gtOverSet (Pmatrix Pthan : α → Prop) (μ : α → D) :
    maxComparative Pmatrix Pthan μ ↔
      (∃ δ, IsGreatest (thanDegrees Pthan μ) δ) ∧
        ∃ x, Pmatrix x ∧ x ∈ Comparison.gt.overSet μ (thanDegrees Pthan μ) := by
  constructor
  · rintro ⟨δ, hδ, x, hx, hlt⟩
    exact ⟨⟨δ, hδ⟩, x, hx, fun d hd => lt_of_le_of_lt (hδ.2 hd) hlt⟩
  · rintro ⟨⟨δ, hδ⟩, x, hx, hclear⟩
    exact ⟨δ, hδ, x, hx, hclear hδ.1⟩

end MaxQuantified

/-! ### Downward-entailingness of than-clauses -/

/-- Universal quantification over a domain is antitone in the domain — the
generic monotonicity fact behind *than*-clauses being downward-entailing (not
[hoeksema-1983]'s specific anti-additivity result, which is in
`Studies/Hoeksema1983.lean`). -/
theorem comparative_than_DE {α : Type*} (R : α → α → Prop) (μ_a : α)
    (D₁ D₂ : Set α) (h_sub : D₁ ⊆ D₂) (h : ∀ d ∈ D₂, R μ_a d) :
    ∀ d ∈ D₁, R μ_a d :=
  fun d hd => h d (h_sub hd)

/-! ### Comparison as extent inclusion

Kennedy's positive/negative extents are `Set.Iic (μ x)` / `Set.Ioi (μ x)`
directly ([kennedy-1999]); the binary comparator equals strict extent
inclusion, and antonymy follows from extent complementarity rather than
being stipulated. -/

section Extent
variable {Entity D : Type*} [LinearOrder D]

/-- Bridge: the atomic S-comparative `Comparison.gt.overSet μ {μ b}` coincides with
the binary `comparativeSem` on a `LinearOrder`. The set-of-degrees schema strictly
generalizes the binary comparator, collapsing at a singleton via
`Comparison.overSet_singleton`. -/
theorem gtOverSet_atomic_eq_comparativeSem (μ : Entity → D) (a b : Entity) :
    a ∈ Comparison.gt.overSet μ {μ b} ↔ comparativeSem μ a b .positive := by
  rw [Comparison.overSet_singleton, ← comparativeSem_positive_eq_over]

/-- "A is taller than B" iff A's positive extent (`Set.Iic (μ a)`,
[kennedy-1999]) strictly contains B's. -/
theorem comparative_iff_Iic_ssubset (μ : Entity → D) (a b : Entity) :
    comparativeSem μ a b .positive ↔ Set.Iic (μ b) ⊂ Set.Iic (μ a) :=
  Set.Iic_ssubset_Iic.symm

/-- "A taller than B" iff "B shorter than A" on the negative extents
(`Set.Ioi`), derived rather than stipulated ([kennedy-1999]). -/
theorem comparative_iff_Ioi_ssubset (μ : Entity → D) (a b : Entity) :
    comparativeSem μ a b .positive ↔ Set.Ioi (μ a) ⊂ Set.Ioi (μ b) :=
  Set.Ioi_ssubset_Ioi_iff.symm

end Extent

/-! ### Strengthened, negated, and extent-theoretic equatives
[kennedy-2007] [rett-2020] [schwarzschild-2008] [thomas-deo-2020]

The literal equative is "at least as" (`equativeSem .positive`); the "exactly
as" reading is derived by scalar implicature (choosing *as tall as* over the
stronger *taller than*). A granularity-based alternative is in
`Degree.Granularity`. -/

section Equative
variable {Entity D : Type*}

/-- Equative strengthened semantics: "A is as tall as B" iff `μ a = μ b` — the
"exactly as" reading, derived by implicature. -/
def equativeStrengthened [Preorder D] (μ : Entity → D) (a b : Entity) : Prop :=
  μ a = μ b

/-- The strengthened reading entails the literal `≥` reading. -/
theorem equativeStrengthened_entails_sem [LinearOrder D] (μ : Entity → D) (a b : Entity)
    (h : equativeStrengthened μ a b) : equativeSem μ a b .positive :=
  le_of_eq h.symm

/-- Negated equative: "A is not as tall as B" iff `μ a < μ b`. -/
def negatedEquative [LinearOrder D] (μ : Entity → D) (a b : Entity) : Prop :=
  μ a < μ b

/-- Negated equative is the negation of the literal equative. -/
theorem negatedEquative_iff_not_sem [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    negatedEquative μ a b ↔ ¬ equativeSem μ a b .positive := by
  simp only [negatedEquative, equativeSem, ge_iff_le, not_le]

/-- Equative as positive extent inclusion ([kennedy-1999]): "A is as tall as B"
iff every degree B has (`Set.Iic (μ b)`), A also has. -/
theorem equativeSem_iff_Iic_subset [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    equativeSem μ a b .positive ↔ Set.Iic (μ b) ⊆ Set.Iic (μ a) :=
  Set.Iic_subset_Iic.symm

/-- Negated equative as strict extent inclusion: B has strictly more degrees
than A. -/
theorem negatedEquative_iff_Iic_ssubset [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    negatedEquative μ a b ↔ Set.Iic (μ a) ⊂ Set.Iic (μ b) :=
  Set.Iic_ssubset_Iic.symm

end Equative

/-! ### Subcomparatives
[schwarzschild-wilkinson-2002] -/

/-- Subcomparative ("longer than it is wide"): two commensurable measure
functions compared in shared units. -/
def subcomparative {Entity D : Type*} [LinearOrder D]
    (μ₁ μ₂ : Entity → D) (a b : Entity) : Prop :=
  μ₁ a > μ₂ b

/-! ### Superlatives
[heim-1999] [szabolcsi-1986] [bobaljik-2012]

`-est` universally quantifies the comparative over a comparison class
([heim-1999]; the semantic reflex of [bobaljik-2012]'s containment
`[[[ADJ] CMPR] SPRL]`): absolute readings fix the class extensionally,
relative readings via focus alternatives. -/

section Superlative
variable {Entity D : Type*} [LinearOrder D]

/-- Absolute superlative: `x` is the G-est entity in comparison class `C` —
`x` beats every other member on the comparative. -/
def absoluteSuperlative (μ : Entity → D) (C : Set Entity) (x : Entity) : Prop :=
  x ∈ C ∧ ∀ y ∈ C, y ≠ x → comparativeSem μ x y .positive

/-- Relative superlative ([heim-1999]): the focused alternative's entity
outranks every other alternative's under `f`. -/
def relativeSuperlative {Alt : Type*} (μ : Entity → D) (f : Alt → Entity)
    (focusedAlt : Alt) (alternatives : Set Alt) : Prop :=
  ∀ a ∈ alternatives, a ≠ focusedAlt →
    comparativeSem μ (f focusedAlt) (f a) .positive

/-- At most one entity satisfies the absolute superlative. -/
theorem absolute_unique (μ : Entity → D) (C : Set Entity) (x y : Entity)
    (hx : absoluteSuperlative μ C x) (hy : absoluteSuperlative μ C y) :
    x = y := by
  by_contra hne
  exact absurd (hx.2 y hy.1 (Ne.symm hne))
    (not_lt.mpr (le_of_lt (hy.2 x hx.1 hne)))

/-- The absolute superlative makes `μ x` the greatest element of the degree
image `μ '' C`; the converse fails (ties). -/
theorem absoluteSuperlative_isGreatest (μ : Entity → D) (C : Set Entity)
    (x : Entity) (h : absoluteSuperlative μ C x) :
    IsGreatest (μ '' C) (μ x) := by
  refine ⟨Set.mem_image_of_mem μ h.1, fun d hd => ?_⟩
  obtain ⟨y, hy, rfl⟩ := hd
  rcases eq_or_ne y x with rfl | hne
  · exact le_refl _
  · exact le_of_lt (h.2 y hy hne)

end Superlative

end Degree
