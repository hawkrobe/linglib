import Mathlib.Data.Rat.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Order.Closure
import Mathlib.Order.Hom.Lattice

/-!
# Algebraic Mereology
@cite{champollion-2017} @cite{krifka-1989} @cite{krifka-1998} @cite{link-1983}

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
5. Overlap and Extensive Measures (@cite{krifka-1998} §2.2)
6. QMOD: Quantizing Modification
7. Maximality and Atom Counting
8. QUA/CUM Pullback (contravariant functoriality)
9. ExtMeasure → StrictMono Bridge
10. IsSumHom + Injective → StrictMono
11. Functional QUA propagation
12. CUM/QUA Pullback Interaction

-/

namespace Mereology

-- ════════════════════════════════════════════════════
-- § 1. Algebraic Closure (*P)
-- ════════════════════════════════════════════════════

/-- Algebraic closure of a predicate P under join (⊔):
    *P is the smallest set containing P and closed under ⊔.
    Originates in @cite{link-1983} (D.32); formulation follows
    @cite{champollion-2017} Ch. 2. -/
inductive AlgClosure {α : Type*} [SemilatticeSup α] (P : α → Prop) : α → Prop where
  /-- Base case: everything in P is in *P. -/
  | base {x : α} : P x → AlgClosure P x
  /-- Closure: if x, y ∈ *P then x ⊔ y ∈ *P. -/
  | sum {x y : α} : AlgClosure P x → AlgClosure P y → AlgClosure P (x ⊔ y)

-- ════════════════════════════════════════════════════
-- § 2. Higher-Order Mereological Properties
-- ════════════════════════════════════════════════════

/-- Cumulative reference (CUM): P is closed under join.
    @cite{link-1983} (T.11); @cite{champollion-2017} §2.3.2:
    CUM(P) ⇔ ∀x,y. P(x) ∧ P(y) → P(x ⊕ y).
    Activities and states are canonically cumulative. -/
def CUM {α : Type*} [SemilatticeSup α] (P : α → Prop) : Prop :=
  ∀ (x y : α), P x → P y → P (x ⊔ y)

/-- Divisive reference (DIV): P is closed downward under ≤.
    @cite{champollion-2017} §2.3.3: DIV(P) ⇔ ∀x,y. P(x) ∧ y ≤ x → P(y).
    This is the mereological analog of the subinterval property. -/
def DIV {α : Type*} [PartialOrder α] (P : α → Prop) : Prop :=
  ∀ (x y : α), P x → y ≤ x → P y

/-- Quantized reference (QUA): no proper part of a P-entity is also P.
    @cite{champollion-2017} §2.3.5: QUA(P) ⇔ ∀x,y. P(x) ∧ y < x → ¬P(y).
    Telic predicates are canonically quantized. -/
def QUA {α : Type*} [PartialOrder α] (P : α → Prop) : Prop :=
  ∀ (x y : α), P x → y < x → ¬ P y

/-- Mereological atom: x has no proper part.
    @cite{link-1983} (D.10, D.22 condition 2);
    @cite{champollion-2017} §2.2: Atom(x) ⇔ ¬∃y. y < x.
    Defined without OrderBot since many domains lack a natural
    bottom element. -/
def Atom {α : Type*} [PartialOrder α] (x : α) : Prop :=
  ∀ (y : α), y ≤ x → y = x

-- ════════════════════════════════════════════════════
-- § 3. Key Theorems
-- ════════════════════════════════════════════════════

/-- *P is always cumulative.
    This is the fundamental property of algebraic closure. -/
theorem algClosure_cum {α : Type*} [SemilatticeSup α]
    {P : α → Prop} : CUM (AlgClosure P) :=
  λ _ _ hx hy => AlgClosure.sum hx hy

/-- P ⊆ *P: algebraic closure extends the original predicate. -/
theorem subset_algClosure {α : Type*} [SemilatticeSup α]
    {P : α → Prop} {x : α} (h : P x) :
    AlgClosure P x :=
  AlgClosure.base h

/-- Every element of *P has a base element below it:
    if x ∈ *P, then ∃ a ∈ P, a ≤ x.
    Useful for extracting witnesses from algebraic closures. -/
theorem algClosure_has_base {α : Type*} [SemilatticeSup α]
    {P : α → Prop} {x : α} (h : AlgClosure P x) :
    ∃ a, P a ∧ a ≤ x := by
  induction h with
  | base hp => exact ⟨_, hp, le_refl _⟩
  | sum _ _ ih₁ _ =>
    obtain ⟨a, ha, hle⟩ := ih₁
    exact ⟨a, ha, le_trans hle le_sup_left⟩

/-- Closure of a cumulative predicate is itself: *P = P when CUM(P).
    Mass nouns and bare plurals are already cumulative, so
    closure is a no-op — the key to Krifka's absorption rule ⊔⊔S = ⊔S. -/
theorem algClosure_of_cum {α : Type*} [SemilatticeSup α]
    {P : α → Prop} (hCUM : CUM P) {x : α} :
    AlgClosure P x ↔ P x :=
  ⟨fun h => by induction h with
    | base h => exact h
    | sum _ _ ihx ihy => exact hCUM _ _ ihx ihy,
   fun h => AlgClosure.base h⟩

/-- QUA predicates cannot be cumulative (for predicates with ≥ 2 elements).
    @cite{champollion-2017} §2.3.5: QUA and CUM are incompatible for non-singletons. -/
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
    @cite{champollion-2017} §2.3.5. -/
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

/-- `AlgClosure` is a **closure operator** on the predicate lattice `(α → Prop, ⊆)`.

    The three axioms — extensive, monotone, idempotent — are grounded
    in Mathlib's `ClosureOperator`. (Compare with the causal-SEM
    operator `Core.Causal.normalDevelopment`: that operator is
    info-extensive but NOT order-monotone, per Schulz @cite{schulz-2011}
    footnote 7, so it does NOT instantiate `ClosureOperator`. The
    mereological case is genuinely closure-operator-shaped.)

    - `subset_algClosure` → `le_closure'` (extensive)
    - `algClosure_mono` → `monotone'` (monotone)
    - `algClosure_idempotent` + `subset_algClosure` → `idempotent'` -/
def algClosureOp {α : Type*} [SemilatticeSup α] :
    ClosureOperator (α → Prop) where
  toOrderHom := {
    toFun := AlgClosure
    monotone' := fun {_a} {_b} hab => algClosure_mono (fun x hx => hab x hx)
  }
  le_closure' := fun _P _x hPx => subset_algClosure hPx
  idempotent' := fun P => funext fun x =>
    propext ⟨algClosure_idempotent x, fun h => subset_algClosure h⟩

-- ════════════════════════════════════════════════════
-- § 4. Sum Homomorphism
-- ════════════════════════════════════════════════════

/-- A sum homomorphism preserves the join operation.
    @cite{champollion-2017} §2.5: thematic roles and τ are sum homomorphisms.
    f(x ⊕ y) = f(x) ⊕ f(y). -/
class IsSumHom {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    (f : α → β) : Prop where
  /-- f preserves binary join. -/
  map_sup : ∀ (x y : α), f (x ⊔ y) = f x ⊔ f y

/-- Convert an `IsSumHom` witness to Mathlib's bundled `SupHom`.

    This grounds linglib's unbundled `IsSumHom` typeclass in Mathlib's
    bundled `SupHom α β`, the hom-set in **SLat** (join semilattices
    with join-preserving maps). -/
def IsSumHom.toSupHom {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    {f : α → β} (hf : IsSumHom f) : SupHom α β where
  toFun := f
  map_sup' := hf.map_sup

/-- Every Mathlib `SupHom` satisfies `IsSumHom`. -/
def SupHom.toIsSumHom {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    (f : SupHom α β) : IsSumHom f.toFun where
  map_sup := f.map_sup'

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
-- § 5. Overlap and Extensive Measures (@cite{krifka-1998} §2.2)
-- ════════════════════════════════════════════════════

/-- Mereological overlap: x and y share a common part.
    @cite{krifka-1998} eq. (1e): O(x, y) ⇔ ∃z. z ≤ x ∧ z ≤ y. -/
def Overlap {γ : Type*} [PartialOrder γ] (x y : γ) : Prop :=
  ∃ z, z ≤ x ∧ z ≤ y

/-- Overlap is reflexive: every element overlaps itself (via x ≤ x). -/
theorem Overlap.refl {γ : Type*} [PartialOrder γ] (x : γ) : Overlap x x :=
  ⟨x, le_refl x, le_refl x⟩

/-- Overlap is symmetric. -/
theorem Overlap.symm {γ : Type*} [PartialOrder γ] {x y : γ}
    (h : Overlap x y) : Overlap y x :=
  let ⟨z, hzx, hzy⟩ := h; ⟨z, hzy, hzx⟩

/-- Extensive measure function: additive over non-overlapping entities.
    @cite{krifka-1998} §2.2, eq. (7): μ(x ⊕ y) = μ(x) + μ(y) when ¬O(x,y).
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
    @cite{krifka-1998} §2.2: "two kilograms of flour" is QUA because
    no proper part of a 2kg entity also weighs 2kg. -/
theorem extMeasure_qua {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} [hμ : ExtMeasure α μ] (n : ℚ) (_hn : 0 < n) :
    QUA (fun x => μ x = n) := by
  intro x y hx hlt hy
  have hsm := hμ.strict_mono x y hlt
  rw [hy, hx] at hsm
  exact absurd hsm (lt_irrefl _)

-- ════════════════════════════════════════════════════
-- § 6. QMOD: Quantizing Modification (@cite{krifka-1989})
-- ════════════════════════════════════════════════════

/-- Quantizing modification: intersect predicate R with a measure constraint.
    @cite{krifka-1989}: QMOD(R, μ, n) = λx. R(x) ∧ μ(x) = n.
    "three kilos of rice" = QMOD(rice, μ_kg, 3).
    This is the operation that turns a CUM mass noun into a QUA measure phrase. -/
def QMOD {α μTy : Type*} (R : α → Prop) (μ : α → μTy) (n : μTy) : α → Prop :=
  λ x => R x ∧ μ x = n

/-- QMOD(R, μ, n) ⊆ R: quantizing modification restricts the base predicate. -/
theorem qmod_sub {α μTy : Type*} {R : α → Prop} {μ : α → μTy} {n : μTy}
    {x : α} (h : QMOD R μ n x) : R x :=
  h.1

-- ════════════════════════════════════════════════════
-- § 6b. Atomization (@cite{little-moroney-royer-2022})
-- ════════════════════════════════════════════════════

/-- Atomize a predicate: restrict P to its atomic members.
    @cite{little-moroney-royer-2022} eq. (13):
    ⟦CLF⟧ = λPλx.[P(x) ∧ ¬∃y[P(y) ∧ y < x]]

    In classifier-for-noun theories (@cite{chierchia-1998}; @cite{jenks-2011};
    @cite{dayal-2012}; @cite{nomoto-2013}), the classifier atomizes the noun
    denotation so the numeral can count individual entities. This is the
    semantic contribution that distinguishes CLF-for-N from CLF-for-NUM. -/
def atomize {α : Type*} [PartialOrder α] (P : α → Prop) : α → Prop :=
  fun x => P x ∧ Atom x

/-- Atomize restricts: atomize P ⊆ P. -/
theorem atomize_sub {α : Type*} [PartialOrder α]
    {P : α → Prop} {x : α} (h : atomize P x) : P x :=
  h.1

/-- Atomized predicates are quantized: no proper part of an atom is an atom. -/
theorem atomize_qua {α : Type*} [PartialOrder α]
    {P : α → Prop} : QUA (atomize P) := by
  intro x y ⟨_, hAtom⟩ hlt _
  exact absurd (hAtom y (le_of_lt hlt)) (ne_of_lt hlt)

/-- Atomize turns cumulative predicates into quantized ones.
    This is the core of CLF-for-N semantics: the classifier takes a
    cumulative noun denotation (an atomic join-semilattice) and produces
    a quantized set of atoms suitable for counting. -/
theorem atomize_of_cum_is_qua {α : Type*} [SemilatticeSup α]
    {P : α → Prop} (_hCum : CUM P) : QUA (atomize P) :=
  atomize_qua

-- ════════════════════════════════════════════════════
-- § 7. Maximality and Atom Counting (@cite{charlow-2021})
-- ════════════════════════════════════════════════════

/-- Maximal in P under ≤: x is in P and no proper extension of x is in P.
    Used by @cite{charlow-2021} for the M_v operator (mereological maximization). -/
def isMaximal {α : Type*} [PartialOrder α] (P : α → Prop) (x : α) : Prop :=
  P x ∧ ∀ (y : α), P y → x ≤ y → x = y

/-- Count atoms below x, using classical decidability.
    Used by @cite{charlow-2021} for cardinality tests on plural individuals. -/
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

/-- Atom count is additive over non-overlapping sums, provided atoms are
    join-prime (i.e., `a ≤ x ⊔ y → a ≤ x ∨ a ≤ y` for atoms `a`).
    Join-primality holds in distributive lattices but fails in general
    semilattices (e.g., the M₃ lattice). -/
theorem atomCount_sup_disjoint (α : Type*) [SemilatticeSup α]
    [Fintype α]
    (hJP : ∀ (a : α), Atom a → ∀ (u v : α), a ≤ u ⊔ v → a ≤ u ∨ a ≤ v)
    {x y : α} (hDisj : ¬ Overlap x y) :
    atomCount α (x ⊔ y) = atomCount α x + atomCount α y := by
  classical
  unfold atomCount
  have hdisj : Disjoint
      (Finset.univ.filter (fun a => @decide (Atom a ∧ a ≤ x) (Classical.dec _)))
      (Finset.univ.filter (fun a => @decide (Atom a ∧ a ≤ y) (Classical.dec _))) := by
    apply Finset.disjoint_left.mpr
    intro a ha_x ha_y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at ha_x ha_y
    exact hDisj ⟨a, ha_x.2, ha_y.2⟩
  have heq : (Finset.univ.filter (fun a => @decide (Atom a ∧ a ≤ x ⊔ y) (Classical.dec _)))
      = (Finset.univ.filter (fun a => @decide (Atom a ∧ a ≤ x) (Classical.dec _)))
      ∪ (Finset.univ.filter (fun a => @decide (Atom a ∧ a ≤ y) (Classical.dec _))) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and, decide_eq_true_eq]
    constructor
    · rintro ⟨hatom, hle⟩
      rcases hJP a hatom x y hle with h | h
      · exact Or.inl ⟨hatom, h⟩
      · exact Or.inr ⟨hatom, h⟩
    · rintro (⟨hatom, hle⟩ | ⟨hatom, hle⟩)
      · exact ⟨hatom, le_trans hle le_sup_left⟩
      · exact ⟨hatom, le_trans hle le_sup_right⟩
  rw [heq]
  exact Finset.card_union_of_disjoint hdisj

-- ════════════════════════════════════════════════════
-- § 8. QUA/CUM Pullback (contravariant functoriality)
-- ════════════════════════════════════════════════════

/-- QUA pullback along strictly monotone maps.

    If `d : α → β` is strictly monotone and `P` is quantized over `β`,
    then `P ∘ d` is quantized over `α`. This is the general theorem
    subsuming both `extMeasure_qua` (where d = μ) and the functional
    version of `qua_propagation` (where d = θ as a function).

    Categorically: QUA is a contravariant functor from the category of
    partially ordered types with StrictMono morphisms to Prop.

    The relational `qua_propagation` in Krifka1998.lean (using MSO + UP
    on a binary relation θ) is genuinely different — it operates on
    relations, not functions. Both coexist: the functional case is a
    special case of this theorem. -/
theorem qua_pullback {α β : Type*} [PartialOrder α] [PartialOrder β]
    {d : α → β} (hd : StrictMono d)
    {P : β → Prop} (hP : QUA P) :
    QUA (P ∘ d) :=
  fun _x _y hx hlt hy => hP _ _ hx (hd hlt) hy

/-- CUM pullback along sum homomorphisms.

    If `d : α → β` is a sum homomorphism and `P` is cumulative over `β`,
    then `P ∘ d` is cumulative over `α`. Wrapper for `IsSumHom.cum_preimage`,
    named for symmetry with `qua_pullback`.

    Categorically: CUM is a contravariant functor from the category of
    join semilattices with IsSumHom morphisms to Prop. -/
theorem cum_pullback {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    {d : α → β} (hd : IsSumHom d)
    {P : β → Prop} (hP : CUM P) :
    CUM (P ∘ d) :=
  hd.cum_preimage hP

-- ════════════════════════════════════════════════════
-- § 9. ExtMeasure → StrictMono Bridge
-- ════════════════════════════════════════════════════

/-- Extract `StrictMono` from an extensive measure.
    `ExtMeasure.strict_mono` axiomatizes that proper parts have strictly
    smaller measure; this is exactly `StrictMono μ`. -/
theorem extMeasure_strictMono {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} (hμ : ExtMeasure α μ) : StrictMono μ :=
  fun _a _b hab => hμ.strict_mono _ _ hab

/-- Singleton predicates are quantized on any partial order.
    `{x | x = n}` is QUA because `y < n → y ≠ n` (by irreflexivity
    of `<` after substitution).

    This generalizes `atom_qua`, which required `Atom x`. The Atom
    hypothesis is unnecessary for singletons. -/
theorem singleton_qua {α : Type*} [PartialOrder α]
    (n : α) : QUA (· = n) := by
  intro x y hx hlt hy
  subst hx; subst hy
  exact absurd hlt (lt_irrefl _)

/-- `extMeasure_qua` derived from `qua_pullback` + `singleton_qua`.
    This shows that `extMeasure_qua` is a special case of QUA pullback:

      {x | μ(x) = n} = (· = n) ∘ μ

    and QUA pulls back along the StrictMono map μ.

    Note: unlike the original `extMeasure_qua`, this derivation does not
    require `0 < n`. The positivity hypothesis was an artifact of the
    direct proof; the pullback route is strictly more general.

    The original `extMeasure_qua` is preserved for backward compatibility. -/
theorem extMeasure_qua' {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} [hμ : ExtMeasure α μ] (n : ℚ) :
    QUA (fun x => μ x = n) :=
  qua_pullback (extMeasure_strictMono hμ) (singleton_qua n)

/-- QUA pullback composes: if `d₁ : α → β` and `d₂ : β → γ` are both
    StrictMono, then `QUA P → QUA (P ∘ d₂ ∘ d₁)`.

    This captures the Krifka dimension chain:
      Events →θ Entities →μ ℚ
    where θ extracts the incremental theme and μ measures it. The
    composition `μ ∘ θ` is StrictMono, so QUA predicates on ℚ
    (measure phrases like "two kilograms") pull back to QUA predicates
    on Events (telic VPs like "eat two kilograms of flour"). -/
theorem qua_pullback_comp {α β γ : Type*}
    [PartialOrder α] [PartialOrder β] [PartialOrder γ]
    {d₁ : α → β} {d₂ : β → γ}
    (hd₁ : StrictMono d₁) (hd₂ : StrictMono d₂)
    {P : γ → Prop} (hP : QUA P) :
    QUA (P ∘ d₂ ∘ d₁) :=
  qua_pullback hd₁ (qua_pullback hd₂ hP)

-- ════════════════════════════════════════════════════
-- § 10. IsSumHom + Injective → StrictMono
-- ════════════════════════════════════════════════════

/-- A sum homomorphism that is injective is strictly monotone.

    `IsSumHom.monotone` gives `Monotone f` (x ≤ y → f(x) ≤ f(y)).
    Adding injectivity strengthens this: x < y means x ≤ y ∧ x ≠ y,
    so f(x) ≤ f(y) ∧ f(x) ≠ f(y), i.e., f(x) < f(y).

    This bridges `IsSumHom` (the CUM pullback morphism class) to
    `StrictMono` (the QUA pullback morphism class): an injective sum
    homomorphism supports both CUM and QUA pullback.

    Linguistically: a sum-homomorphic thematic role that is also
    injective (unique participant assignment, Krifka's UE/UO
    conditions) supports telicity transfer via `qua_pullback`. -/
theorem IsSumHom.strictMono_of_injective {α β : Type*}
    [SemilatticeSup α] [SemilatticeSup β]
    {f : α → β} (hf : IsSumHom f) (hinj : Function.Injective f) :
    StrictMono f := by
  intro x y hlt
  exact lt_of_le_of_ne (hf.monotone hlt.le) (fun h => hlt.ne (hinj h))

-- ════════════════════════════════════════════════════
-- § 11. Functional QUA propagation
-- ════════════════════════════════════════════════════

/-- QUA propagation through an injective sum homomorphism.

    When the relational θ in Krifka's `qua_propagation` (Krifka1998.lean)
    is actually a function `f` with `IsSumHom` + injectivity, the
    relational proof (needing UP + MSO) reduces to functional
    `qua_pullback` via `StrictMono`.

    This is the functional special case of @cite{krifka-1998} §3.3:
    SINC(θ) ∧ QUA(OBJ) → QUA(VP θ OBJ), where θ is a function
    rather than a relation, and SINC reduces to IsSumHom + Injective.

    See also: `qua_propagation` in Krifka1998.lean for the relational
    version using UP + MSO + UO. -/
theorem qua_of_injective_sumHom {α β : Type*}
    [SemilatticeSup α] [SemilatticeSup β]
    {f : α → β} (hf : IsSumHom f) (hinj : Function.Injective f)
    {P : β → Prop} (hP : QUA P) :
    QUA (P ∘ f) :=
  qua_pullback (hf.strictMono_of_injective hinj) hP

-- ════════════════════════════════════════════════════
-- § 12. CUM/QUA Pullback Interaction
-- ════════════════════════════════════════════════════

/-- CUM/QUA incompatibility is preserved through composition.

    If P ∘ f has two distinct witnesses x ≠ y, then P ∘ f cannot be
    both CUM and QUA. This is `cum_qua_disjoint` instantiated to the
    composed predicate. -/
theorem cum_qua_dimension_disjoint {α β : Type*}
    [SemilatticeSup α] [SemilatticeSup β]
    {f : α → β} {P : β → Prop}
    {x y : α} (hx : (P ∘ f) x) (hy : (P ∘ f) y) (hne : x ≠ y) :
    ¬ (CUM (P ∘ f) ∧ QUA (P ∘ f)) :=
  cum_qua_disjoint ⟨x, y, hx, hy, hne⟩

-- ════════════════════════════════════════════════════
-- § 13. g-Homogeneity (@cite{deal-2017})
-- ════════════════════════════════════════════════════

/-- g-homogeneous reference (@cite{deal-2017}): every proper part of a
    P-entity has a P-part below it.

      DIV → g-homogeneous    (proved: `div_implies_gHomogeneous`)

    g-Homogeneity and CUM are independent: a predicate can be
    g-homogeneous without being CUM (e.g., `{a, b}` where atoms have no
    proper parts — vacuously g-homogeneous — but `a ⊔ b ∉ P`), and CUM
    without being g-homogeneous (fake mass nouns, see `FakeMass`).

    NOTE: this is a simplified version of @cite{deal-2017}'s full
    definition, which involves CUM conjoined with one of four conditions
    about minimal parts (divisive, lacking stable/non-overlapping/
    non-strongly-connected minimal parts). Our formalization captures the
    intuitive core that Deal extracts as the common thread.

    Mass nouns are g-homogeneous: every part of water contains water.
    Fake mass nouns (English "furniture", Shan bare nouns per
    @cite{moroney-2021}) are CUM but NOT g-homogeneous: a leg of a
    chair is part of the furniture but is not itself furniture. -/
def gHomogeneous {α : Type*} [PartialOrder α] (P : α → Prop) : Prop :=
  ∀ (x y : α), P x → y < x → ∃ z, z ≤ y ∧ P z

/-- DIV implies g-homogeneity: if every part of a P-entity is P, then
    a fortiori every proper part has a P-part (itself). -/
theorem div_implies_gHomogeneous {α : Type*} [PartialOrder α]
    {P : α → Prop} (hDiv : DIV P) : gHomogeneous P :=
  fun x y hPx hlt => ⟨y, le_refl y, hDiv x y hPx (le_of_lt hlt)⟩

/-- g-Homogeneity is vacuously satisfied at atoms: since atoms have
    no proper parts, the universal condition `∀ y < a, ∃ z ≤ y, P z`
    holds trivially.

    This means g-homogeneity failures arise at *non-atomic* P-entities
    whose proper parts include non-P elements. For fake mass nouns like
    "furniture", the sum of two chairs is a non-atomic furniture-entity
    whose proper part (a chair leg) has no furniture-part below it. -/
theorem atom_gHomogeneous_trivial {α : Type*} [PartialOrder α]
    {P : α → Prop} {a : α} (_hP : P a) (hAtom : Atom a) :
    ∀ y, y < a → ∃ z, z ≤ y ∧ P z := by
  intro y hlt
  exact absurd (hAtom y (le_of_lt hlt)) (ne_of_lt hlt)

/-- A predicate that is cumulative but NOT g-homogeneous has "fake mass"
    behavior (@cite{deal-2017}; @cite{moroney-2021} §2.4): sums of
    P-entities are P-entities (CUM), but parts of P-entities need not
    contain any P-entity (failure of g-homogeneity). English "furniture"
    and Shan bare nouns exhibit this pattern: the sum of two chairs is
    furniture (CUM), but a chair leg is part of furniture without itself
    being furniture (¬g-homogeneous).

    This is a definitional wrapper for naming the property combination. -/
def FakeMass {α : Type*} [SemilatticeSup α] (P : α → Prop) : Prop :=
  CUM P ∧ ¬ gHomogeneous P

-- ════════════════════════════════════════════════════
-- § 14. Convex Closure (@cite{kriz-spector-2021} def. 21)
-- ════════════════════════════════════════════════════

/-- Convex closure under a partial order: add all elements "in between"
    existing members. z is in-between x and y if x ≤ z ≤ y.
    @cite{kriz-spector-2021} def. 21: Conv_⊑(A) is the smallest superset
    of A such that for any x, y ∈ A, every z with x ⊑ z ⊑ y is also in
    Conv_⊑(A). One step suffices because ⊑ is transitive. -/
def convexClosure {α : Type*} [PartialOrder α] (S : Set α) : Set α :=
  { c | ∃ a ∈ S, ∃ b ∈ S, a ≤ c ∧ c ≤ b }

/-- S ⊆ convexClosure S. -/
theorem subset_convexClosure {α : Type*} [PartialOrder α] (S : Set α) :
    S ⊆ convexClosure S :=
  fun x hx => ⟨x, hx, x, hx, le_refl x, le_refl x⟩

/-- convexClosure is idempotent: Conv(Conv(S)) = Conv(S).
    If c ∈ Conv(Conv(S)), then a₁ ≤ c ≤ b₂ for some a₁, b₂ ∈ S. -/
theorem convexClosure_idempotent {α : Type*} [PartialOrder α] (S : Set α) :
    convexClosure (convexClosure S) = convexClosure S := by
  ext c; constructor
  · rintro ⟨a, ⟨a₁, ha₁, a₂, _, ha₁a, _⟩, b, ⟨_, _, b₂, hb₂, _, hbb₂⟩, hac, hcb⟩
    exact ⟨a₁, ha₁, b₂, hb₂, le_trans ha₁a (le_trans hac (le_refl c)),
           le_trans (le_refl c) (le_trans hcb hbb₂)⟩
  · exact fun hc => subset_convexClosure _ hc

/-- Convex closure is monotone: S ⊆ T → Conv(S) ⊆ Conv(T). -/
theorem convexClosure_mono {α : Type*} [PartialOrder α] {S T : Set α}
    (h : S ⊆ T) : convexClosure S ⊆ convexClosure T :=
  fun _ ⟨a, ha, b, hb, hac, hcb⟩ => ⟨a, h ha, b, h hb, hac, hcb⟩

/-- A set is **convex** under the partial order: every element between
    two members is itself a member. The fixed-point of `convexClosure`. -/
def IsConvex {α : Type*} [PartialOrder α] (S : Set α) : Prop :=
  ∀ ⦃s u : α⦄, s ∈ S → u ∈ S → ∀ ⦃t : α⦄, s ≤ t → t ≤ u → t ∈ S

theorem IsConvex.convexClosure {α : Type*} [PartialOrder α] (S : Set α) :
    IsConvex (convexClosure S) := by
  rintro s u ⟨a, ha, _, _, hale, _⟩ ⟨_, _, b, hb, _, hleb⟩ t hst htu
  exact ⟨a, ha, b, hb, le_trans hale hst, le_trans htu hleb⟩

/-- `convexClosure` as a mathlib `ClosureOperator (Set α)`.
    Sibling to `algClosureOp`. -/
def convexClosureOp {α : Type*} [PartialOrder α] :
    ClosureOperator (Set α) where
  toOrderHom := {
    toFun := convexClosure
    monotone' := fun _ _ hST => convexClosure_mono hST
  }
  le_closure' := fun S _ hx => subset_convexClosure S hx
  idempotent' := convexClosure_idempotent

-- ════════════════════════════════════════════════════
-- § 15. Conjunctive Parthood (Jago Def 5; @cite{jago-2026})
-- ════════════════════════════════════════════════════

/-- **Down clause** of conjunctive parthood: every element of `p` has a
    part in `q`. Generic poset relation; specialized in
    `Theories/Semantics/Truthmaker/Basic.lean` to content parthood. -/
def IsSubsumedBy {α : Type*} [Preorder α] (q p : α → Prop) : Prop :=
  ∀ s, p s → ∃ t, q t ∧ t ≤ s

/-- **Up clause** of conjunctive parthood: every element of `q` extends
    to an element of `p`. -/
def Subserves {α : Type*} [Preorder α] (q p : α → Prop) : Prop :=
  ∀ s, q s → ∃ t, p t ∧ s ≤ t

/-- **Conjunctive parthood** (@cite{jago-2026} Def 5):
    `q` is a content part of `p` iff both Down (`IsSubsumedBy`) and Up
    (`Subserves`) clauses hold. -/
def IsContentPart {α : Type*} [Preorder α] (q p : α → Prop) : Prop :=
  IsSubsumedBy q p ∧ Subserves q p

namespace IsSubsumedBy

@[refl] theorem refl {α : Type*} [Preorder α] (p : α → Prop) :
    IsSubsumedBy p p :=
  fun s hp => ⟨s, hp, le_refl s⟩

theorem trans {α : Type*} [Preorder α] {p q r : α → Prop}
    (hpq : IsSubsumedBy p q) (hqr : IsSubsumedBy q r) : IsSubsumedBy p r := by
  intro s hr
  obtain ⟨t, hqt, htles⟩ := hqr s hr
  obtain ⟨u, hpu, hulet⟩ := hpq t hqt
  exact ⟨u, hpu, le_trans hulet htles⟩

end IsSubsumedBy

namespace Subserves

@[refl] theorem refl {α : Type*} [Preorder α] (p : α → Prop) :
    Subserves p p :=
  fun s hp => ⟨s, hp, le_refl s⟩

theorem trans {α : Type*} [Preorder α] {p q r : α → Prop}
    (hpq : Subserves p q) (hqr : Subserves q r) : Subserves p r := by
  intro s hp
  obtain ⟨t, hqt, hslet⟩ := hpq s hp
  obtain ⟨u, hru, htleu⟩ := hqr t hqt
  exact ⟨u, hru, le_trans hslet htleu⟩

end Subserves

namespace IsContentPart

@[refl] theorem refl {α : Type*} [Preorder α] (p : α → Prop) :
    IsContentPart p p :=
  ⟨IsSubsumedBy.refl p, Subserves.refl p⟩

theorem trans {α : Type*} [Preorder α] {p q r : α → Prop}
    (hpq : IsContentPart p q) (hqr : IsContentPart q r) : IsContentPart p r :=
  ⟨hpq.1.trans hqr.1, hpq.2.trans hqr.2⟩

theorem subsumed {α : Type*} [Preorder α] {q p : α → Prop}
    (h : IsContentPart q p) : IsSubsumedBy q p := h.1

theorem subserves {α : Type*} [Preorder α] {q p : α → Prop}
    (h : IsContentPart q p) : Subserves q p := h.2

end IsContentPart

end Mereology
