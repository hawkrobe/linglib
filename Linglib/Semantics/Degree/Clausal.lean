import Linglib.Semantics.Degree.Basic
import Linglib.Semantics.Entailment.AntiAdditivity

/-!
# Clausal comparatives: set and max standards
[hoeksema-1983] [von-stechow-1984] [rullmann-1995] [heim-2001]

Comparison against a *than*-clause denotation rather than a point: the
set-of-degrees S-comparative (`Comparison.gt.overSet μ` directly), the
max-quantified reading (`thanDegrees`/`maxComparative`/`maxEquative`,
`IsGreatest`-based), and downward-entailingness of *than*-clauses.
The point-standard collapse (`overSet_singleton`,
`maxComparative_eq_iff`) makes the binary `comparativeSem` the atomic
special case.
-/

namespace Degree

open Core.Order (Comparison)

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
