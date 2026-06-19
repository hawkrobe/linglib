import Linglib.Semantics.Degree.Extent
import Linglib.Semantics.Degree.Bounds
import Linglib.Semantics.Degree.Basic
import Linglib.Semantics.Entailment.AntiAdditivity
import Linglib.Core.Order.Comparison

/-!
# Framework-Independent Comparative Semantics
[rett-2026] [schwarzschild-2008] [von-stechow-1984] [hoeksema-1983]

Comparative semantics shared across all degree frameworks: the binary
`comparativeSem` / `equativeSem`, the set-of-degrees generalization
`clausalComparison`, antonymy as scale reversal, and downward-entailingness of
*than*-clauses. All three are the measure-pullback predications of the reified
`Core.Order.Comparison` (`over` at a point standard, `overSet` at a set standard);
`clausalComparison_eq_overSet` / `comparativeSem_positive_eq_over` make that an identity.
Framework-specific content for [rett-2026] (MAX, ambidirectionality, manner
implicature) lives in `Studies/Rett2026.lean`; [hoeksema-1983]'s polarity-asymmetry
consumers in `Studies/Hoeksema1983.lean`.

## Main declarations

* `comparativeSem` / `equativeSem` — "A is Adj-er / as-Adj-as B" via a directed
  measure on a scale.
* `clausalComparison` — set-of-degrees comparative ([hoeksema-1983]), anti-additive in
  its standard (`clausalComparison_isAntiAdditive`): the algebraic source of
  *than*-clause NPI licensing.
* `mem_clausalComparison_iff_subset_Iio` / `clausalComparison_singleton` — the set-of-degrees
  comparative as `Set.Iio` interval inclusion (strict mirror of mathlib's
  `mem_upperBounds_iff_subset_Iic`), collapsing to the binary comparator at a singleton.
* `clausalComparison_eq_singleton_of_isGreatest` — a than-clause with a greatest degree
  reduces to that degree ([bhatt-pancheva-2004], order-theoretic form).
* `taller_shorter_antonymy` — antonymy is argument swap plus direction reversal.
* `comparative_iff_posExt_ssubset` — comparison as extent inclusion ([kennedy-1999]).
-/

namespace Semantics.Degree

open Core.Order (ScalePolarity Comparison)

/-! ### Scale direction -/

/-- Comparative direction reuses scale polarity from `Core.Order`.
`positive` ("taller") makes MAX pick the highest degrees; `negative`
("shorter") the lowest. -/
abbrev ScaleDirection := ScalePolarity

/-! ### Comparative and equative semantics -/

section Direct
variable {Entity : Type*} {α : Type*} [LinearOrder α]

/-- Comparative semantics ([rett-2026], [schwarzschild-2008]): "A is Adj-er
than B" iff `μ a` exceeds `μ b` on the directed scale. -/
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
theorem comparativeSem_eq_MAX (μ : Entity → α) (a b : Entity) :
    comparativeSem μ a b .positive ↔
      ∃ m ∈ maxOnScale .gt ({μ b} : Set α), μ a > m := by
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

The S-comparative `clausalComparison` ([hoeksema-1983] §3.8 Def 7) generalizes
`comparativeSem` from a single standard to an arbitrary degree-set standard.
It needs only `[Preorder D]`. -/

section SetOfDegrees
variable {Entity D : Type*} [Preorder D]

/-- S-comparative on a set of degrees ([hoeksema-1983] §3.8 Def 7):
`y ∈ clausalComparison μ Δ` iff `μ y` strictly exceeds every degree in `Δ`. The
than-clause supplies the degree set `Δ` (typically existentially closed). -/
def clausalComparison (μ : Entity → D) (Δ : Set D) : Set Entity :=
  fun y => ∀ d ∈ Δ, d < μ y

/-- **Grounding**: the set-of-degrees comparative is the strict-`>` *set-standard*
predication of `Core.Order.Comparison` (`μ ⁻¹' strictUpperBounds Δ`) — the
fundamental object, with the binary comparator its singleton case
(`Comparison.overSet_singleton`). True by `rfl`: this is not a reinvention. -/
theorem clausalComparison_eq_overSet (μ : Entity → D) (Δ : Set D) :
    clausalComparison μ Δ = Comparison.gt.overSet μ Δ :=
  rfl

/-- The set-of-degrees comparative as a strict-interval inclusion: `y` clears the
than-clause iff every standard degree lies strictly below `μ y`. Strict mirror of
mathlib's `mem_upperBounds_iff_subset_Iic`; both faces are `Iff.rfl` siblings. -/
theorem mem_clausalComparison_iff_subset_Iio (μ : Entity → D) (Δ : Set D) (y : Entity) :
    y ∈ clausalComparison μ Δ ↔ Δ ⊆ Set.Iio (μ y) :=
  Iff.rfl

/-- A than-clause whose denotation is the single degree `d` reduces to the binary
comparator `d < μ y`. Strict mirror of mathlib's
`upperBounds_singleton : upperBounds {a} = Ici a`. -/
theorem clausalComparison_singleton (μ : Entity → D) (d : D) :
    clausalComparison μ {d} = {y | d < μ y} := by
  ext y
  refine ⟨fun h => h d rfl, ?_⟩
  intro h x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  exact h

/-- [hoeksema-1983] Fact 4: the S-comparative is anti-additive in its
set-of-degrees argument — the algebraic source of NPI licensing in clausal
*than*-comparatives. -/
theorem clausalComparison_isAntiAdditive (μ : Entity → D) :
    Entailment.IsAntiAdditive (clausalComparison μ) :=
  Entailment.isAntiAdditive_forall_mem (fun d y => d < μ y)

/-- Atomic specialization: at the singleton `{μ b}`, S-comparative membership
reduces to the binary "taller than `b`" relation. Corollary of
`clausalComparison_singleton`. -/
theorem clausalComparison_atomic (μ : Entity → D) (a b : Entity) :
    a ∈ clausalComparison μ {μ b} ↔ μ b < μ a := by
  simp only [clausalComparison_singleton, Set.mem_setOf_eq]

/-- **Reduction lemma** ([bhatt-pancheva-2004] §3, order-theoretic form): the
S-comparative is determined by the *greatest* element of its degree-set
argument. Needs neither linearity nor density — only `[Preorder D]` and the
`IsGreatest` witness. -/
theorem clausalComparison_eq_singleton_of_isGreatest (μ : Entity → D) {Δ : Set D}
    {m : D} (hm : IsGreatest Δ m) :
    clausalComparison μ Δ = clausalComparison μ ({m} : Set D) := by
  ext y
  refine ⟨fun h d hd => ?_, fun h d hd => ?_⟩
  · rw [Set.mem_singleton_iff] at hd
    exact hd ▸ h m hm.1
  · exact lt_of_le_of_lt (hm.2 hd) (h m rfl)

end SetOfDegrees

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

Three faces of the `posExt` / `negExt` correspondence ([kennedy-1999]): the
binary comparator equals strict extent inclusion, and antonymy follows from
extent complementarity rather than being stipulated. -/

section Extent
variable {Entity D : Type*} [LinearOrder D]

/-- Bridge: the atomic S-comparative coincides with the binary `comparativeSem`
on a `LinearOrder`. The set-of-degrees schema strictly generalizes the binary
comparator. -/
theorem clausalComparison_atomic_eq_comparativeSem (μ : Entity → D) (a b : Entity) :
    a ∈ clausalComparison μ {μ b} ↔ comparativeSem μ a b .positive :=
  clausalComparison_atomic μ a b

/-- "A is taller than B" iff A's positive extent strictly contains B's
([kennedy-1999]). Bridges the point comparison to `posExt_ssubset_iff`. -/
theorem comparative_iff_posExt_ssubset (μ : Entity → D) (a b : Entity) :
    comparativeSem μ a b .positive ↔ posExt μ b ⊂ posExt μ a :=
  (posExt_ssubset_iff μ b a).symm

/-- "A taller than B" iff "B shorter than A", derived from the complementarity
of positive and negative extents rather than stipulated as a lexical property
of antonym pairs ([kennedy-1999]). -/
theorem comparative_iff_negExt_ssubset (μ : Entity → D) (a b : Entity) :
    comparativeSem μ a b .positive ↔ negExt μ a ⊂ negExt μ b := by
  rw [comparative_iff_posExt_ssubset, antonymy_biconditional]

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
iff `posExt μ b ⊆ posExt μ a` — every degree B has, A also has. -/
theorem equativeSem_iff_posExt_subset [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    equativeSem μ a b .positive ↔ posExt μ b ⊆ posExt μ a :=
  (posExt_subset_iff μ b a).symm

/-- Negated equative as strict extent inclusion: B has strictly more degrees
than A. -/
theorem negatedEquative_iff_posExt_ssubset [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    negatedEquative μ a b ↔ posExt μ a ⊂ posExt μ b :=
  (posExt_ssubset_iff μ a b).symm

end Equative

end Semantics.Degree
