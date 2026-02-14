import Mathlib.Data.Rat.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

/-!
# Algebraic Mereology

Framework-agnostic mereological infrastructure formalized over Mathlib's
`SemilatticeSup` (binary join = mereological sum ⊕) and `PartialOrder`
(part-of = ≤). All definitions are polymorphic over any semilattice,
making them usable for entities, events, times, paths, or any domain
with part-whole structure.

## Sections

1. Algebraic Closure (*P)
2. Higher-Order Properties: CUM, DIV, QUA, Atom
3. Key Theorems (CUM/DIV/QUA interactions)
4. Sum Homomorphism
5. Overlap and Extensive Measures (Krifka 1998 §2.2)
6. QMOD: Quantizing Modification (Krifka 1989)

## References

- Champollion, L. (2017). *Parts of a Whole: Distributivity as a Bridge
  Between Aspect and Measurement*. OUP.
- Krifka, M. (1998). The origins of telicity. In S. Rothstein (ed.),
  *Events and Grammar*, 197–235. Kluwer.
- Krifka, M. (1989). Nominal reference, temporal constitution and
  quantification in event semantics.
- Link, G. (1983). The logical analysis of plurals and mass terms.
- Simons, P. (1987). *Parts: A Study in Ontology*. OUP.
-/

namespace Mereology

-- ════════════════════════════════════════════════════
-- § 1. Algebraic Closure (*P)
-- ════════════════════════════════════════════════════

/-- Algebraic closure of a predicate P under join (⊔):
    *P is the smallest set containing P and closed under ⊔.
    Corresponds to Champollion (2017) Ch. 2, §2.3.4. -/
inductive AlgClosure {α : Type*} [SemilatticeSup α] (P : α → Prop) : α → Prop where
  /-- Base case: everything in P is in *P. -/
  | base {x : α} : P x → AlgClosure P x
  /-- Closure: if x, y ∈ *P then x ⊔ y ∈ *P. -/
  | sum {x y : α} : AlgClosure P x → AlgClosure P y → AlgClosure P (x ⊔ y)

-- ════════════════════════════════════════════════════
-- § 2. Higher-Order Mereological Properties
-- ════════════════════════════════════════════════════

/-- Cumulative reference (CUM): P is closed under join.
    Champollion (2017) §2.3.2: CUM(P) ⇔ ∀x,y. P(x) ∧ P(y) → P(x ⊕ y).
    Activities and states are canonically cumulative. -/
def CUM {α : Type*} [SemilatticeSup α] (P : α → Prop) : Prop :=
  ∀ (x y : α), P x → P y → P (x ⊔ y)

/-- Divisive reference (DIV): P is closed downward under ≤.
    Champollion (2017) §2.3.3: DIV(P) ⇔ ∀x,y. P(x) ∧ y ≤ x → P(y).
    This is the mereological analog of the subinterval property. -/
def DIV {α : Type*} [PartialOrder α] (P : α → Prop) : Prop :=
  ∀ (x y : α), P x → y ≤ x → P y

/-- Quantized reference (QUA): no proper part of a P-entity is also P.
    Champollion (2017) §2.3.5: QUA(P) ⇔ ∀x,y. P(x) ∧ y < x → ¬P(y).
    Telic predicates are canonically quantized. -/
def QUA {α : Type*} [PartialOrder α] (P : α → Prop) : Prop :=
  ∀ (x y : α), P x → y < x → ¬ P y

/-- Mereological atom: x has no proper part.
    Champollion (2017) §2.2: Atom(x) ⇔ ¬∃y. y < x.
    Defined without OrderBot since many domains lack a natural
    bottom element. -/
def Atom {α : Type*} [PartialOrder α] (x : α) : Prop :=
  ∀ (y : α), y ≤ x → y = x

-- ════════════════════════════════════════════════════
-- § 3. Key Theorems
-- ════════════════════════════════════════════════════

/-- *P is always cumulative (Champollion 2017, §2.3.4).
    This is the fundamental property of algebraic closure. -/
theorem algClosure_cum {α : Type*} [SemilatticeSup α]
    {P : α → Prop} : CUM (AlgClosure P) :=
  λ _ _ hx hy => AlgClosure.sum hx hy

/-- P ⊆ *P: algebraic closure extends the original predicate. -/
theorem subset_algClosure {α : Type*} [SemilatticeSup α]
    {P : α → Prop} {x : α} (h : P x) :
    AlgClosure P x :=
  AlgClosure.base h

/-- QUA predicates cannot be cumulative (for predicates with ≥ 2 elements).
    Champollion (2017) §2.3.5: QUA and CUM are incompatible for non-singletons. -/
theorem qua_cum_incompatible {α : Type*} [SemilatticeSup α]
    {P : α → Prop} (hQ : QUA P)
    {x y : α} (hx : P x) (hy : P y) (hne : x ≠ y) :
    ¬ CUM P := by
  intro hC
  have hxy := hC x y hx hy
  have hle : x ≤ x ⊔ y := le_sup_left
  by_cases heq : x = x ⊔ y
  · have : y ≤ x := heq ▸ le_sup_right
    by_cases hyx : y = x
    · exact hne hyx.symm
    · have hlt : y < x := lt_of_le_of_ne this hyx
      exact hQ x y hx hlt hy
  · have hlt : x < x ⊔ y := lt_of_le_of_ne hle heq
    exact hQ (x ⊔ y) x hxy hlt hx

/-- Atoms are trivially quantized: the singleton {x} is QUA when x is an atom. -/
theorem atom_qua {α : Type*} [PartialOrder α]
    {x : α} (hAtom : Atom x) : QUA (· = x) := by
  intro a b ha hlt hn
  subst ha; subst hn
  exact absurd (hAtom b (le_of_lt hlt)) (ne_of_lt hlt).symm

/-- DIV allows extracting parts: if P is DIV and P(z), then P(w) for any w ≤ z. -/
theorem div_closed_under_le {α : Type*} [PartialOrder α]
    {P : α → Prop}
    (hDiv : DIV P)
    {z : α} (hz : P z) {w : α} (hle : w ≤ z) :
    P w :=
  hDiv z w hz hle

/-- CUM and QUA partition event predicates (for non-trivial predicates):
    a predicate with ≥ 2 distinct elements cannot be both CUM and QUA.
    Champollion (2017) §2.3.5. -/
theorem cum_qua_disjoint {α : Type*} [SemilatticeSup α]
    {P : α → Prop}
    (hne : ∃ (x y : α), P x ∧ P y ∧ x ≠ y) :
    ¬ (CUM P ∧ QUA P) := by
  intro ⟨hC, hQ⟩
  obtain ⟨x, y, hpx, hpy, hxy⟩ := hne
  exact qua_cum_incompatible hQ hpx hpy hxy hC

/-- AlgClosure preserves membership: if P x, then AlgClosure P x. -/
theorem algClosure_of_mem {α : Type*} [SemilatticeSup α]
    {P : α → Prop} {x : α} (h : P x) : AlgClosure P x :=
  AlgClosure.base h

/-- AlgClosure is monotone: P ⊆ Q implies *P ⊆ *Q. -/
theorem algClosure_mono {α : Type*} [SemilatticeSup α]
    {P Q : α → Prop} (h : ∀ (x : α), P x → Q x) :
    ∀ (x : α), AlgClosure P x → AlgClosure Q x := by
  intro x hx
  induction hx with
  | base hp => exact AlgClosure.base (h _ hp)
  | sum _ _ ih₁ ih₂ => exact AlgClosure.sum ih₁ ih₂

/-- AlgClosure is idempotent: *(∗P) = *P. -/
theorem algClosure_idempotent {α : Type*} [SemilatticeSup α]
    {P : α → Prop} :
    ∀ (x : α), AlgClosure (AlgClosure P) x → AlgClosure P x := by
  intro x hx
  induction hx with
  | base hp => exact hp
  | sum _ _ ih₁ ih₂ => exact AlgClosure.sum ih₁ ih₂

-- ════════════════════════════════════════════════════
-- § 4. Sum Homomorphism
-- ════════════════════════════════════════════════════

/-- A sum homomorphism preserves the join operation.
    Champollion (2017) §2.5: thematic roles and τ are sum homomorphisms.
    f(x ⊕ y) = f(x) ⊕ f(y). -/
class IsSumHom {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    (f : α → β) : Prop where
  /-- f preserves binary join. -/
  map_sup : ∀ (x y : α), f (x ⊔ y) = f x ⊔ f y

/-- Sum homomorphisms are order-preserving (monotone).
    If x ≤ y then f(x) ≤ f(y). -/
theorem IsSumHom.monotone {α β : Type*}
    [SemilatticeSup α] [SemilatticeSup β]
    {f : α → β} (hf : IsSumHom f) :
    Monotone f := by
  intro x y hle
  have : x ⊔ y = y := sup_eq_right.mpr hle
  calc f x ≤ f x ⊔ f y := le_sup_left
    _ = f (x ⊔ y) := (hf.map_sup x y).symm
    _ = f y := by rw [this]

/-- Sum homomorphisms preserve CUM: if P is CUM then P ∘ f⁻¹ is CUM.
    More precisely: if P is CUM then (fun x => P (f x)) is CUM. -/
theorem IsSumHom.cum_preimage {α β : Type*}
    [SemilatticeSup α] [SemilatticeSup β]
    {f : α → β} (hf : IsSumHom f)
    {P : β → Prop} (hCum : CUM P) :
    CUM (P ∘ f) := by
  intro x y hx hy
  simp only [Function.comp] at *
  rw [hf.map_sup]
  exact hCum _ _ hx hy

-- ════════════════════════════════════════════════════
-- § 5. Overlap and Extensive Measures (Krifka 1998 §2.2)
-- ════════════════════════════════════════════════════

/-- Mereological overlap: x and y share a common part.
    Krifka (1998) eq. (1e): O(x, y) ⇔ ∃z. z ≤ x ∧ z ≤ y. -/
def Overlap {γ : Type*} [PartialOrder γ] (x y : γ) : Prop :=
  ∃ z, z ≤ x ∧ z ≤ y

/-- Extensive measure function: additive over non-overlapping entities.
    Krifka (1998) §2.2, eq. (7): μ(x ⊕ y) = μ(x) + μ(y) when ¬O(x,y).
    Examples: weight, volume, number (cardinality). -/
class ExtMeasure (α : Type*) [SemilatticeSup α]
    (μ : α → ℚ) : Prop where
  /-- Additivity: μ is additive over non-overlapping entities. -/
  additive : ∀ (x y : α), ¬ Overlap x y → μ (x ⊔ y) = μ x + μ y
  /-- Positivity: every entity has positive measure. -/
  positive : ∀ (x : α), 0 < μ x
  /-- Strict monotonicity: proper parts have strictly smaller measure.
      In a CEM with complementation, this follows from additivity + positivity:
      y < x implies x = y ⊔ z with ¬O(y,z), so μ(x) = μ(y) + μ(z) > μ(y).
      We axiomatize it directly since `SemilatticeSup` lacks complementation. -/
  strict_mono : ∀ (x y : α), y < x → μ y < μ x

/-- Measure phrases create QUA predicates: {x : μ(x) = n} is QUA
    whenever μ is an extensive measure.
    Krifka (1998) §2.2: "two kilograms of flour" is QUA because
    no proper part of a 2kg entity also weighs 2kg. -/
theorem extMeasure_qua {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} [hμ : ExtMeasure α μ] (n : ℚ) (_hn : 0 < n) :
    QUA (fun x => μ x = n) := by
  intro x y hx hlt hy
  have hsm := hμ.strict_mono x y hlt
  rw [hy, hx] at hsm
  exact absurd hsm (Rat.not_lt.mpr Rat.le_refl)

-- ════════════════════════════════════════════════════
-- § 6. QMOD: Quantizing Modification (Krifka 1989)
-- ════════════════════════════════════════════════════

/-- Quantizing modification: intersect predicate R with a measure constraint.
    Krifka (1989): QMOD(R, μ, n) = λx. R(x) ∧ μ(x) = n.
    "three kilos of rice" = QMOD(rice, μ_kg, 3).
    This is the operation that turns a CUM mass noun into a QUA measure phrase. -/
def QMOD {α μTy : Type*} (R : α → Prop) (μ : α → μTy) (n : μTy) : α → Prop :=
  λ x => R x ∧ μ x = n

/-- QMOD(R, μ, n) ⊆ R: quantizing modification restricts the base predicate. -/
theorem qmod_sub {α μTy : Type*} {R : α → Prop} {μ : α → μTy} {n : μTy}
    {x : α} (h : QMOD R μ n x) : R x :=
  h.1

-- ════════════════════════════════════════════════════
-- § 7. Maximality and Atom Counting (Charlow 2021)
-- ════════════════════════════════════════════════════

/-- Maximal in P under ≤: x is in P and no proper extension of x is in P.
    Used by Charlow (2021) for the M_v operator (mereological maximization). -/
def isMaximal {α : Type*} [PartialOrder α] (P : α → Prop) (x : α) : Prop :=
  P x ∧ ∀ (y : α), P y → x ≤ y → x = y

/-- Count atoms below x, using classical decidability.
    Used by Charlow (2021) for cardinality tests on plural individuals. -/
noncomputable def atomCount (α : Type*) [PartialOrder α] [Fintype α]
    (x : α) : Nat :=
  @Finset.card α (Finset.univ.filter (λ a => @decide (Atom a ∧ a ≤ x) (Classical.dec _)))

/-- If P is CUM and x, y are both maximal in P, then x = y.
    Cumulative predicates have at most one maximal element: the join of all P-elements. -/
theorem cum_maximal_unique {α : Type*} [SemilatticeSup α]
    {P : α → Prop} (hCum : CUM P)
    {x y : α} (hx : isMaximal P x) (hy : isMaximal P y) : x = y := by
  have hxy := hCum x y hx.1 hy.1
  have hle_x : x ≤ x ⊔ y := le_sup_left
  have hle_y : y ≤ x ⊔ y := le_sup_right
  have heq_x : x = x ⊔ y := hx.2 (x ⊔ y) hxy hle_x
  have heq_y : y = x ⊔ y := hy.2 (x ⊔ y) hxy hle_y
  exact heq_x.trans heq_y.symm

/-- Atom count is additive over non-overlapping sums.
    TODO: Prove from extensivity of cardinality.  -/
theorem atomCount_sup_disjoint (α : Type*) [SemilatticeSup α]
    [Fintype α]
    {x y : α} (_hDisj : ¬ Overlap x y) :
    atomCount α (x ⊔ y) = atomCount α x + atomCount α y := by
  sorry

end Mereology
