import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Card
import Mathlib.Order.Antichain
import Mathlib.Order.Basic
import Mathlib.Order.Closure
import Mathlib.Order.Hom.Lattice
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.Lattice
import Mathlib.Order.Minimal
import Mathlib.Order.SupClosed
import Mathlib.Order.UpperLower.Closure

/-!
# Algebraic Mereology
[champollion-2017] [krifka-1989] [krifka-1998] [link-1983]

Framework-agnostic mereological infrastructure formalized over Mathlib's
`SemilatticeSup` (binary join = mereological sum ⊕) and `PartialOrder`
(part-of = ≤). All definitions are polymorphic over any semilattice,
making them usable for entities, events, times, paths, or any domain
with part-whole structure.

-/

namespace Mereology

/-! ### Algebraic Closure (*P) -/

/-- Algebraic closure of a predicate P under join (⊔):
    *P is the smallest set containing P and closed under ⊔.
    Originates in [link-1983] (D.32); formulation follows
    [champollion-2017] Ch. 2. -/
inductive AlgClosure {α : Type*} [SemilatticeSup α] (P : α → Prop) : α → Prop where
  /-- Base case: everything in P is in *P. -/
  | base {x : α} : P x → AlgClosure P x
  /-- Closure: if x, y ∈ *P then x ⊔ y ∈ *P. -/
  | sum {x y : α} : AlgClosure P x → AlgClosure P y → AlgClosure P (x ⊔ y)

/-! ### Higher-Order Mereological Properties -/

/-- Cumulative reference (CUM): P is closed under join. Grounded in mathlib's
    `SupClosed` — `CUM P` **is** `SupClosed {x | P x}` (the sup-closed-set
    predicate). Apply a `CUM` hypothesis directly (`hC hx hy : P (x ⊔ y)`);
    construct one with a direct lambda (`fun _ hx _ hy => …`), as for any
    `SupClosed` (cf. mathlib `IsUpperSet.supClosed`).
    [link-1983] (T.11); [krifka-1989] D 12; [champollion-2017] §2.3.2:
    `CUMₛ(P) ⇔ ∀x,y. P(x) ∧ P(y) → P(x ∪ₛ y)`.
    Activities and states are canonically cumulative. -/
abbrev CUM {α : Type*} [SemilatticeSup α] (P : α → Prop) : Prop :=
  SupClosed {x | P x}

/-- Divisive reference (DIV): P is closed downward under ≤. Grounded in
    mathlib's `IsLowerSet` — `DIV P` **is** `IsLowerSet {x | P x}`. Apply a
    `DIV` hypothesis directly (`hDiv hle hz : P w` from `hle : w ≤ z`,
    `hz : P z`); construct one with a direct lambda (`fun _ _ hba ha => …`).
    Equivalently `DIV P ↔ Antitone P` via mathlib's `isLowerSet_setOf`.
    [champollion-2017] §2.3.3: DIV(P) ⇔ ∀x,y. P(x) ∧ y ≤ x → P(y).
    This is the mereological analog of the subinterval property.
    Only requires `Preorder` since the definition only uses `≤`. -/
abbrev DIV {α : Type*} [Preorder α] (P : α → Prop) : Prop :=
  IsLowerSet {x | P x}

/-- Quantized reference (QUA): no proper part of a P-entity is also P.

    [krifka-1989] D 14: `QUAₛ(P) ⇔ ∀x,y. P(x) ∧ P(y) → ¬ y ⊂ₛ x`.
    [champollion-2017] §2.3.5 reformulates as `∀x,y. P(x) ∧ y < x → ¬P(y)`,
    which is propositionally equivalent (`(A → B → ¬C) ↔ (A → C → ¬B)`).
    Grounded in mathlib's `IsAntichain` — `QUA P` **is**
    `IsAntichain (· ≤ ·) {x | P x}` (a quantized predicate's extension is an
    antichain: its members are pairwise incomparable). A `QUA` hypothesis is
    *applied directly* as an antichain (`hQ hPx hPy hne : ¬ x ≤ y`); to build one
    from Champollion's paper form, use `qua_of_forall`. -/
abbrev QUA {α : Type*} [PartialOrder α] (P : α → Prop) : Prop :=
  IsAntichain (· ≤ ·) {x | P x}

/-- Converge Champollion's paper condition into the mathlib `IsAntichain` normal
    form: if no P-element sits strictly below another P-element, the extension is
    an antichain. This is the *construction* direction (paper form ⟹ `QUA`); to
    *use* a `QUA` hypothesis, apply it directly as an antichain. There is no
    `QUA ⟹ ∀ x y` unfold by design — that runs against the simp grain. -/
theorem qua_of_forall {α : Type*} [PartialOrder α] {P : α → Prop}
    (h : ∀ x y, P x → y < x → ¬ P y) : QUA P := by
  rintro a ha b hb hab hab_le
  exact h b a hb (lt_of_le_of_ne hab_le hab) ha

/-- Mereological atom: x has no proper part — grounded as mathlib's `IsMin`
    (minimal element). [link-1983] (D.10); [champollion-2017] §2.2:
    `Atom(x) ⇔ ¬∃y. y < x`. This is the **absolute** (P-independent) notion;
    the P-relative one (Krifka D17, "no proper *P*-part") is `atomize` /
    mathlib `Minimal P`. No `OrderBot` needed — many mereological domains lack
    a bottom. -/
abbrev Atom {α : Type*} [PartialOrder α] (x : α) : Prop := IsMin x

/-- An atom's only part is itself — the `y = x` elimination form of `IsMin`. -/
theorem Atom.eq {α : Type*} [PartialOrder α] {x y : α} (h : Atom x) (hy : y ≤ x) :
    y = x :=
  le_antisymm hy (h hy)

/-! ### Key Theorems -/

/-- *P is always cumulative.
    This is the fundamental property of algebraic closure. -/
theorem algClosure_cum {α : Type*} [SemilatticeSup α]
    {P : α → Prop} : CUM (AlgClosure P) :=
  fun _ hx _ hy => AlgClosure.sum hx hy

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
    | sum _ _ ihx ihy => exact hCUM ihx ihy,
   fun h => AlgClosure.base h⟩

/-- QUA predicates cannot be cumulative (for predicates with ≥ 2 elements).
    [champollion-2017] §2.3.5: QUA and CUM are incompatible for non-singletons. -/
theorem qua_cum_incompatible {α : Type*} [SemilatticeSup α]
    {P : α → Prop} (hQ : QUA P)
    {x y : α} (hx : P x) (hy : P y) (hne : x ≠ y) :
    ¬ CUM P := by
  intro hC
  have hxy : P (x ⊔ y) := hC hx hy
  rcases eq_or_lt_of_le (le_sup_left : x ≤ x ⊔ y) with hx_eq | hx_lt
  · rcases eq_or_lt_of_le (le_sup_right : y ≤ x ⊔ y) with hy_eq | hy_lt
    · exact hne (hx_eq.trans hy_eq.symm)
    · exact hQ hy hxy hy_lt.ne hy_lt.le
  · exact hQ hx hxy hx_lt.ne hx_lt.le

/-- Atoms form an antichain — the absolute case of mathlib's
    `setOf_minimal_antichain` (atoms are the `Minimal (fun _ => True)` elements,
    via `minimal_true`). The engine behind `qua_of_atom`. -/
theorem isAntichain_setOf_atom {α : Type*} [PartialOrder α] :
    IsAntichain (· ≤ ·) {x : α | Atom x} := by
  simp only [Atom, ← minimal_true]; exact setOf_minimal_antichain _

/-- **Combinator**: a predicate holding only of atoms is quantized — its
    extension is a subset of the atoms, which form an antichain
    (`IsAntichain.subset`). Factors the recurring "atomic ⟹ QUA" pattern
    (mass-noun part predicates, classifier atoms). -/
theorem qua_of_atom {α : Type*} [PartialOrder α] {P : α → Prop}
    (h : ∀ ⦃x⦄, P x → Atom x) : QUA P :=
  isAntichain_setOf_atom.subset h

/-- Atoms are trivially quantized: the singleton `{x}` is QUA when x is an atom. -/
theorem atom_qua {α : Type*} [PartialOrder α]
    {x : α} (hAtom : Atom x) : QUA (· = x) :=
  qua_of_atom fun _ hz => hz ▸ hAtom

/-- DIV allows extracting parts: if P is DIV and P(z), then P(w) for any w ≤ z. -/
theorem div_closed_under_le {α : Type*} [PartialOrder α]
    {P : α → Prop}
    (hDiv : DIV P)
    {z : α} (hz : P z) {w : α} (hle : w ≤ z) :
    P w :=
  hDiv hle hz

/-- CUM and QUA partition event predicates (for non-trivial predicates):
    a predicate with ≥ 2 distinct elements cannot be both CUM and QUA.
    [champollion-2017] §2.3.5. -/
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

/-- `AlgClosure` is a **closure operator** on the predicate lattice `(α → Prop, ⊆)`,
    grounded in mathlib's `ClosureOperator` via its three axioms:

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

/-! ### Sum Homomorphism -/

/-- A sum homomorphism preserves the join operation.
    [champollion-2017] §2.5: thematic roles and τ are sum homomorphisms.
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
    CUM (P ∘ f) :=
  hCum.preimage hf.toSupHom

/-! ### Overlap and Extensive Measures ([krifka-1998]) -/

/-- Mereological overlap: x and y share a common part.
    [krifka-1998] eq. (1e): O(x, y) ⇔ ∃z. z ≤ x ∧ z ≤ y. -/
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
    [krifka-1998] §2.2, eq. (7): μ(x ⊕ y) = μ(x) + μ(y) when ¬O(x,y).
    Examples: weight, volume, number (cardinality). Order-interval sibling:
    `IsIntervalContent` (`Core/Order/IntervalContent.lean`) — disjoint
    intervals have no interval join, so the two substrates coexist. -/
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

/-! Measure phrases create QUA predicates: `{x : μ(x) = n}` is QUA whenever
μ is an extensive measure ([krifka-1998] §2.2: "two kilograms of flour" is
QUA because no proper part of a 2kg entity also weighs 2kg). The theorem
`extMeasure_qua` is stated in §9 below, derived via `qua_pullback`. -/

/-! ### QMOD: Quantizing Modification ([krifka-1989]) -/

/-- Quantizing modification: intersect predicate R with a measure constraint.
    [krifka-1989]: QMOD(R, μ, n) = λx. R(x) ∧ μ(x) = n.
    "three kilos of rice" = QMOD(rice, μ_kg, 3).
    This is the operation that turns a CUM mass noun into a QUA measure phrase. -/
def QMOD {α μTy : Type*} (R : α → Prop) (μ : α → μTy) (n : μTy) : α → Prop :=
  λ x => R x ∧ μ x = n

/-- QMOD(R, μ, n) ⊆ R: quantizing modification restricts the base predicate. -/
theorem qmod_sub {α μTy : Type*} {R : α → Prop} {μ : α → μTy} {n : μTy}
    {x : α} (h : QMOD R μ n x) : R x :=
  h.1

/-! ### Atomization ([little-moroney-royer-2022]) -/

/-- Atomize a predicate to its **P-relative** minimal members — mathlib's
    `Minimal P`. [little-moroney-royer-2022] eq. (13):
    `⟦CLF⟧ = λPλx.[P(x) ∧ ¬∃y[P(y) ∧ y < x]]`, which is exactly `Minimal P x`
    (`minimal_iff_forall_lt`). NB this is *P-relative* (no *P*-element strictly
    below x), distinct from the absolute `Atom`/`IsMin`; for a divisive P the
    two coincide (`minimal_iff_isMin`).

    In classifier-for-noun theories ([chierchia-1998]; [jenks-2011];
    [dayal-2012]; [nomoto-2013]), the classifier atomizes the noun
    denotation so the numeral can count individual entities. -/
abbrev atomize {α : Type*} [PartialOrder α] (P : α → Prop) : α → Prop := Minimal P

/-- Atomize restricts: atomize P ⊆ P. -/
theorem atomize_sub {α : Type*} [PartialOrder α]
    {P : α → Prop} {x : α} (h : atomize P x) : P x :=
  h.1

/-- Atomized predicates are quantized: the P-minimal elements form an antichain
    (mathlib's `setOf_minimal_antichain`). -/
theorem atomize_qua {α : Type*} [PartialOrder α]
    {P : α → Prop} : QUA (atomize P) :=
  setOf_minimal_antichain P

/-- Atomize turns cumulative predicates into quantized ones.
    This is the core of CLF-for-N semantics: the classifier takes a
    cumulative noun denotation (an atomic join-semilattice) and produces
    a quantized set of atoms suitable for counting. -/
theorem atomize_of_cum_is_qua {α : Type*} [SemilatticeSup α]
    {P : α → Prop} (_hCum : CUM P) : QUA (atomize P) :=
  atomize_qua

/-! ### Maximality and Atom Counting ([charlow-2021]) -/

/-- Maximal in P under ≤: x is in P and no proper extension of x is in P.
    Used by [charlow-2021] for the M_v operator (mereological maximization). -/
def isMaximal {α : Type*} [PartialOrder α] (P : α → Prop) (x : α) : Prop :=
  P x ∧ ∀ (y : α), P y → x ≤ y → x = y

/-- Count atoms below `x`, as the cardinality of the (classically finite)
    set of atomic parts. Used by [charlow-2021] for cardinality tests on
    plural individuals. -/
noncomputable def atomCount (α : Type*) [PartialOrder α] [Fintype α]
    (x : α) : ℕ :=
  {a : α | Atom a ∧ a ≤ x}.ncard

/-- If P is CUM and x, y are both maximal in P, then x = y.
    Cumulative predicates have at most one maximal element: the join of all P-elements. -/
theorem cum_maximal_unique {α : Type*} [SemilatticeSup α]
    {P : α → Prop} (hCum : CUM P)
    {x y : α} (hx : isMaximal P x) (hy : isMaximal P y) : x = y := by
  have hxy := hCum hx.1 hy.1
  exact (hx.2 _ hxy le_sup_left).trans (hy.2 _ hxy le_sup_right).symm

/-- The atoms below a join are exactly the atoms below either operand,
    when atoms are join-prime (`a ≤ u ⊔ v → a ≤ u ∨ a ≤ v`). -/
theorem atomsBelow_sup {α : Type*} [SemilatticeSup α]
    (hJP : ∀ (a : α), Atom a → ∀ (u v : α), a ≤ u ⊔ v → a ≤ u ∨ a ≤ v) (x y : α) :
    {a : α | Atom a ∧ a ≤ x ⊔ y}
      = {a | Atom a ∧ a ≤ x} ∪ {a | Atom a ∧ a ≤ y} := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_union]
  exact ⟨fun ⟨h, hle⟩ => (hJP a h x y hle).imp (⟨h, ·⟩) (⟨h, ·⟩),
    fun h => h.elim (fun ⟨h, hl⟩ => ⟨h, hl.trans le_sup_left⟩)
                    (fun ⟨h, hl⟩ => ⟨h, hl.trans le_sup_right⟩)⟩

/-- Atom count is additive over non-overlapping sums, provided atoms are
    join-prime (i.e., `a ≤ x ⊔ y → a ≤ x ∨ a ≤ y` for atoms `a`).
    Join-primality holds in distributive lattices but fails in general
    semilattices (e.g., the M₃ lattice). -/
theorem atomCount_sup_disjoint (α : Type*) [SemilatticeSup α]
    [Fintype α]
    (hJP : ∀ (a : α), Atom a → ∀ (u v : α), a ≤ u ⊔ v → a ≤ u ∨ a ≤ v)
    {x y : α} (hDisj : ¬ Overlap x y) :
    atomCount α (x ⊔ y) = atomCount α x + atomCount α y := by
  unfold atomCount
  rw [atomsBelow_sup hJP, Set.ncard_union_eq
    (Set.disjoint_left.mpr fun a ha hb => hDisj ⟨a, ha.2, hb.2⟩)
    (Set.toFinite _) (Set.toFinite _)]

/-! ### QUA/CUM Pullback (contravariant functoriality) -/

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
    QUA (P ∘ d) := by
  rintro a ha b hb hab hab_le
  have hlt := hd (lt_of_le_of_ne hab_le hab)
  exact hP ha hb hlt.ne hlt.le

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

/-! ### ExtMeasure → StrictMono Bridge -/

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
    (n : α) : QUA (· = n) :=
  Set.Subsingleton.isAntichain (fun _ ha _ hb => ha.trans hb.symm) _

/-- Measure phrases create QUA predicates: `{x : μ(x) = n}` is QUA
    whenever μ is an extensive measure ([krifka-1998] §2.2).
    A special case of QUA pullback:

      {x | μ(x) = n} = (· = n) ∘ μ

    and QUA pulls back along the StrictMono map μ. No positivity
    hypothesis on `n` is needed — the pullback route is fully general. -/
theorem extMeasure_qua {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} [hμ : ExtMeasure α μ] (n : ℚ) :
    QUA (fun x => μ x = n) :=
  qua_pullback (extMeasure_strictMono hμ) (singleton_qua n)

/-- **Combinator**: a measure-quantizing modification is quantized.
    `QMOD R μ n ⊆ {μ = n}`, an antichain by `extMeasure_qua`, so any subset is
    too (`IsAntichain.subset`). -/
theorem qmod_qua {α : Type*} [SemilatticeSup α] {μ : α → ℚ} [ExtMeasure α μ]
    (R : α → Prop) (n : ℚ) : QUA (QMOD R μ n) :=
  (extMeasure_qua n).subset fun _ h => h.2

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

/-! ### IsSumHom + Injective → StrictMono -/

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

/-! ### Functional QUA propagation -/

/-- QUA propagation through an injective sum homomorphism.

    When the relational θ in Krifka's `qua_propagation` (Krifka1998.lean)
    is actually a function `f` with `IsSumHom` + injectivity, the
    relational proof (needing UP + MSO) reduces to functional
    `qua_pullback` via `StrictMono`.

    This is the functional special case of [krifka-1998] §3.3:
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

/-! ### CUM/QUA Pullback Interaction -/

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

/-! ### g-Homogeneity ([deal-2017]) -/

/-- g-homogeneous reference ([deal-2017]): every proper part of a
    P-entity has a P-part below it.

      DIV → g-homogeneous    (proved: `div_implies_gHomogeneous`)

    g-Homogeneity and CUM are independent: a predicate can be
    g-homogeneous without being CUM (e.g., `{a, b}` where atoms have no
    proper parts — vacuously g-homogeneous — but `a ⊔ b ∉ P`), and CUM
    without being g-homogeneous (fake mass nouns, see `FakeMass`).

    NOTE: this is a simplified version of [deal-2017]'s full
    definition, which involves CUM conjoined with one of four conditions
    about minimal parts (divisive, lacking stable/non-overlapping/
    non-strongly-connected minimal parts). Our formalization captures the
    intuitive core that Deal extracts as the common thread.

    Mass nouns are g-homogeneous: every part of water contains water.
    Fake mass nouns (English "furniture", Shan bare nouns per
    [moroney-2021]) are CUM but NOT g-homogeneous: a leg of a
    chair is part of the furniture but is not itself furniture. -/
def gHomogeneous {α : Type*} [PartialOrder α] (P : α → Prop) : Prop :=
  ∀ (x y : α), P x → y < x → ∃ z, z ≤ y ∧ P z

/-- DIV implies g-homogeneity: if every part of a P-entity is P, then
    a fortiori every proper part has a P-part (itself). -/
theorem div_implies_gHomogeneous {α : Type*} [PartialOrder α]
    {P : α → Prop} (hDiv : DIV P) : gHomogeneous P :=
  fun x y hPx hlt => ⟨y, le_refl y, hDiv (le_of_lt hlt) hPx⟩

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
  exact absurd (Atom.eq hAtom (le_of_lt hlt)) (ne_of_lt hlt)

/-- A predicate that is cumulative but NOT g-homogeneous has "fake mass"
    behavior ([deal-2017]; [moroney-2021] §2.4): sums of
    P-entities are P-entities (CUM), but parts of P-entities need not
    contain any P-entity (failure of g-homogeneity). English "furniture"
    and Shan bare nouns exhibit this pattern: the sum of two chairs is
    furniture (CUM), but a chair leg is part of furniture without itself
    being furniture (¬g-homogeneous).

    This is a definitional wrapper for naming the property combination. -/
def FakeMass {α : Type*} [SemilatticeSup α] (P : α → Prop) : Prop :=
  CUM P ∧ ¬ gHomogeneous P

/-! ### Convex Closure ([kriz-spector-2021]) -/

/-- Convex closure under a partial order: add all elements "in between"
    existing members. z is in-between x and y if x ≤ z ≤ y.
    [kriz-spector-2021] def. 21: Conv_⊑(A) is the smallest superset
    of A such that for any x, y ∈ A, every z with x ⊑ z ⊑ y is also in
    Conv_⊑(A). One step suffices because ⊑ is transitive. -/
def convexClosure {α : Type*} [PartialOrder α] (S : Set α) : Set α :=
  { c | ∃ a ∈ S, ∃ b ∈ S, a ≤ c ∧ c ≤ b }

/-- `convexClosure` is mathlib's order-convex hull: the intersection of the
    upper and lower closures. The construction is consumed, not
    re-stipulated (same discipline as `Core/Logic/Team/Closure.lean`). -/
theorem convexClosure_eq_upperClosure_inter_lowerClosure {α : Type*}
    [PartialOrder α] (S : Set α) :
    convexClosure S = ↑(upperClosure S) ∩ ↑(lowerClosure S) := by
  ext c
  simp only [convexClosure, Set.mem_setOf_eq, Set.mem_inter_iff,
    SetLike.mem_coe, mem_upperClosure, mem_lowerClosure]
  tauto

/-- S ⊆ convexClosure S. -/
theorem subset_convexClosure {α : Type*} [PartialOrder α] (S : Set α) :
    S ⊆ convexClosure S :=
  fun x hx => ⟨x, hx, x, hx, le_refl x, le_refl x⟩

/-- Convex closure is monotone: S ⊆ T → Conv(S) ⊆ Conv(T). -/
theorem convexClosure_mono {α : Type*} [PartialOrder α] {S T : Set α}
    (h : S ⊆ T) : convexClosure S ⊆ convexClosure T :=
  fun _ ⟨a, ha, b, hb, hac, hcb⟩ => ⟨a, h ha, b, h hb, hac, hcb⟩

/-- The convex closure is order-convex: an intersection of an upper and a
    lower set (`IsUpperSet.ordConnected`, `IsLowerSet.ordConnected`). -/
theorem ordConnected_convexClosure {α : Type*} [PartialOrder α] (S : Set α) :
    (convexClosure S).OrdConnected := by
  rw [convexClosure_eq_upperClosure_inter_lowerClosure]
  exact ((upperClosure S).upper.ordConnected).inter
    ((lowerClosure S).lower.ordConnected)

/-- A set is order-convex (`Set.OrdConnected`) iff it is a fixed point of
    `convexClosure` — [kriz-spector-2021] def. 21 and [harbour-2014] (33)
    are mathlib's `ordConnected_iff_upperClosure_inter_lowerClosure` in
    closure form. -/
theorem ordConnected_iff_convexClosure_eq {α : Type*} [PartialOrder α]
    (S : Set α) : S.OrdConnected ↔ convexClosure S = S := by
  rw [convexClosure_eq_upperClosure_inter_lowerClosure]
  exact ordConnected_iff_upperClosure_inter_lowerClosure

/-- convexClosure is idempotent: a corollary of its order-convexity. -/
theorem convexClosure_idempotent {α : Type*} [PartialOrder α] (S : Set α) :
    convexClosure (convexClosure S) = convexClosure S :=
  (ordConnected_iff_convexClosure_eq _).mp (ordConnected_convexClosure S)

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

/-! ### Predicate disjointness and individuation perspectives

A predicate is *overlapping* if two distinct members share a part, and
*disjoint* otherwise; a maximally disjoint subset is an individuation
perspective ([landman-2011]'s variants; [landman-2020]'s disjointness
thesis: counting requires a disjoint base). The null schema unions all
perspectives ([sutton-filip-2021]). Parameterized over an arbitrary
overlap relation `ov` (mereologically, `x ⊓ y ≠ ⊥`); graduated from
`Studies/SuttonFilip2021.lean` on gaining its second consumer
(`Studies/Landman2020.lean`). -/

section Individuation

variable {α : Type*} (ov : α → α → Prop)

/-- Two distinct members of `P` share a part. -/
def OverlapPred (P : Set α) : Prop :=
  ∃ x ∈ P, ∃ y ∈ P, x ≠ y ∧ ov x y

/-- No two distinct members of `P` share a part. -/
def DisjointPred (P : Set α) : Prop := ¬ OverlapPred ov P

/-- `OverlapPred` is monotone under inclusion. -/
theorem overlapPred_mono {P Q : Set α} (h : P ⊆ Q)
    (hP : OverlapPred ov P) : OverlapPred ov Q :=
  let ⟨x, hx, y, hy, hne, hov⟩ := hP
  ⟨x, h hx, y, h hy, hne, hov⟩

/-- A subset of a disjoint predicate is disjoint. -/
theorem DisjointPred.anti {P Q : Set α} (h : P ⊆ Q)
    (hQ : DisjointPred ov Q) : DisjointPred ov P :=
  fun hP => hQ (overlapPred_mono ov h hP)

/-- A maximally disjoint subset of `P`: disjoint, and unextendable within
    `P` — an individuation perspective. -/
def IsMaxDisjointIn (D P : Set α) : Prop :=
  D ⊆ P ∧ DisjointPred ov D ∧ ∀ x ∈ P, x ∉ D → OverlapPred ov (insert x D)

/-- The null individuation schema: the union of *all* maximally disjoint
    subsets — what counts as 'one' under any perspective
    ([sutton-filip-2021] (32), after [landman-2011]). -/
def nullSchema (P : Set α) : Set α :=
  {x | ∃ D, IsMaxDisjointIn ov D P ∧ x ∈ D}

/-- The union of two distinct maximal disjoint subsets overlaps: if `x`
    distinguishes `D₂` from `D₁`, then `D₁`'s maximality makes
    `insert x D₁` overlap, and the offending pair lies in `D₁ ∪ D₂`. -/
theorem overlapPred_union_of_maxDisjoint_ne {D₁ D₂ P : Set α}
    (h₁ : IsMaxDisjointIn ov D₁ P) (h₂ : IsMaxDisjointIn ov D₂ P)
    (hne : D₁ ≠ D₂) : OverlapPred ov (D₁ ∪ D₂) := by
  obtain ⟨x, hx₂, hx₁⟩ | ⟨x, hx₁, hx₂⟩ :
      (∃ x, x ∈ D₂ ∧ x ∉ D₁) ∨ (∃ x, x ∈ D₁ ∧ x ∉ D₂) := by
    by_contra hcon
    push_neg at hcon
    exact hne (Set.Subset.antisymm hcon.2 hcon.1)
  · exact overlapPred_mono ov
      (Set.insert_subset_iff.mpr ⟨Or.inr hx₂, fun a ha => Or.inl ha⟩)
      (h₁.2.2 x (h₂.1 hx₂) hx₁)
  · exact overlapPred_mono ov
      (Set.insert_subset_iff.mpr ⟨Or.inl hx₁, fun a ha => Or.inr ha⟩)
      (h₂.2.2 x (h₁.1 hx₁) hx₂)

/-- If two distinct maximal disjoint subsets exist, the null schema is
    overlapping: null-schema counting bases are mass exactly when
    individuation is perspectival. -/
theorem overlapPred_nullSchema {D₁ D₂ P : Set α}
    (h₁ : IsMaxDisjointIn ov D₁ P) (h₂ : IsMaxDisjointIn ov D₂ P)
    (hne : D₁ ≠ D₂) : OverlapPred ov (nullSchema ov P) :=
  overlapPred_mono ov
    (Set.union_subset (fun a ha => ⟨D₁, h₁, ha⟩) (fun a ha => ⟨D₂, h₂, ha⟩))
    (overlapPred_union_of_maxDisjoint_ne ov h₁ h₂ hne)

/-- A disjoint predicate is its own unique perspective: the null schema
    returns it unchanged. -/
theorem nullSchema_eq_of_disjoint {P : Set α} (h : DisjointPred ov P) :
    nullSchema ov P = P := by
  ext x
  constructor
  · rintro ⟨D, hD, hx⟩
    exact hD.1 hx
  · intro hx
    exact ⟨P, ⟨Set.Subset.rfl, h, fun y hy hny => absurd hy hny⟩, hx⟩

end Individuation

/-! ### Conjunctive Parthood ([jago-2026]) -/

/-- **Down clause** of conjunctive parthood: every element of `p` has a
    part in `q`. Generic poset relation; specialized in
    `Semantics/Truthmaker/Basic.lean` to content parthood. -/
def IsSubsumedBy {α : Type*} [Preorder α] (q p : α → Prop) : Prop :=
  ∀ s, p s → ∃ t, q t ∧ t ≤ s

/-- **Up clause** of conjunctive parthood: every element of `q` extends
    to an element of `p`. -/
def Subserves {α : Type*} [Preorder α] (q p : α → Prop) : Prop :=
  ∀ s, q s → ∃ t, p t ∧ s ≤ t

/-- **Conjunctive parthood** ([jago-2026] Def 5):
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


/-! ### Mereological dimensions

Strictly monotone maps along which QUA pulls back — the dimension
chains of [krifka-1989]'s linking theory (`Events →θ Entities →μ ℚ`),
bundling the three sources of `StrictMono` (`ExtMeasure`, injective
`IsSumHom`, compositions). -/

/-- CUM predicates with incomparable elements can always produce larger
    measure values via sum.

    If P is CUM and has elements x, y where x ≤ y fails (they are
    incomparable), then x ⊔ y satisfies P (by CUM) and μ(x ⊔ y) > μ(y)
    (because y < x ⊔ y and μ is StrictMono).

    This is the structural mechanism behind open/unbounded scales for
    CUM predicates: given fresh material, CUM can always produce a
    larger measurement. The incomparability condition is satisfied
    whenever two P-elements have non-overlapping parts (e.g., two
    distinct portions of rice, two non-overlapping running events). -/
theorem cum_sum_exceeds {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} [hμ : ExtMeasure α μ]
    {P : α → Prop} (hCum : CUM P)
    {x y : α} (hx : P x) (hy : P y) (h_not_le : ¬ x ≤ y) :
    P (x ⊔ y) ∧ μ (x ⊔ y) > μ y := by
  constructor
  · exact hCum hx hy
  · have hle : y ≤ x ⊔ y := le_sup_right
    have hne : y ≠ x ⊔ y := by
      intro heq; exact h_not_le (heq ▸ le_sup_left)
    exact hμ.strict_mono _ _ (lt_of_le_of_ne hle hne)

/-- CUM predicates with incomparable elements yield measure values
    strictly exceeding both inputs.

    Symmetric version of `cum_sum_exceeds`: μ(x ⊔ y) > μ(x) AND
    μ(x ⊔ y) > μ(y) when x and y are incomparable. -/
theorem cum_sum_exceeds_both {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} [hμ : ExtMeasure α μ]
    {P : α → Prop} (hCum : CUM P)
    {x y : α} (hx : P x) (hy : P y)
    (hxy : ¬ x ≤ y) (hyx : ¬ y ≤ x) :
    P (x ⊔ y) ∧ μ (x ⊔ y) > μ x ∧ μ (x ⊔ y) > μ y := by
  refine ⟨hCum hx hy, ?_, (cum_sum_exceeds hCum hx hy hxy).2⟩
  have hle : x ≤ x ⊔ y := le_sup_left
  have hne : x ≠ x ⊔ y := by
    intro heq; exact hyx (heq ▸ le_sup_right)
  exact hμ.strict_mono _ _ (lt_of_le_of_ne hle hne)

/-- Morphism class of Mereo^op: the category of partially ordered types
    with strictly monotone maps. A `MereoDim d` instance witnesses that
    `d` is a mereological dimension — a map along which QUA pulls back.

    Unifies three sources of `StrictMono`:
    - `ExtMeasure` (via `extMeasure_strictMono`)
    - `IsSumHom` + `Injective` (via `strictMono_of_injective`)
    - Compositions of the above (Krifka dimension chains) -/
class MereoDim {α β : Type*} [PartialOrder α] [PartialOrder β]
    (d : α → β) : Prop where
  /-- The underlying strict monotonicity proof. -/
  toStrictMono : StrictMono d

/-! ### MereoDim Instances and Constructors -/

/-- Any `ExtMeasure` is automatically a `MereoDim`: extensive measures
    are strictly monotone by `extMeasure_strictMono`. -/
instance instMereoDimOfExtMeasure {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} [hμ : ExtMeasure α μ] : MereoDim μ :=
  ⟨extMeasure_strictMono hμ⟩

/-- An injective sum homomorphism is a `MereoDim`. Not an instance because
    `Function.Injective` is not inferrable by typeclass search. -/
def MereoDim.ofInjSumHom {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    {f : α → β} [hf : IsSumHom f] (hinj : Function.Injective f) : MereoDim f :=
  ⟨hf.strictMono_of_injective hinj⟩

/-! ### MereoDim Composition -/

/-- Composition of `MereoDim` morphisms. Captures Krifka's dimension
    chains: `Events →θ Entities →μ ℚ` gives `MereoDim (μ ∘ θ)` when
    both components are `MereoDim`.

    Stated as a theorem (not an instance) to avoid typeclass inference
    loops from decomposing arbitrary composed functions. -/
theorem MereoDim.comp {α β γ : Type*}
    [PartialOrder α] [PartialOrder β] [PartialOrder γ]
    {f : β → γ} {g : α → β} (hf : MereoDim f) (hg : MereoDim g) :
    MereoDim (f ∘ g) :=
  ⟨hf.toStrictMono.comp hg.toStrictMono⟩

/-! ### MereoDim QUA Pullback -/

/-- QUA pullback via `MereoDim`: typeclass-dispatched version of
    `qua_pullback`. When `[MereoDim d]` is available (automatically
    for any `ExtMeasure`), QUA pulls back without manual `StrictMono`
    threading. -/
theorem qua_pullback_mereoDim {α β : Type*} [PartialOrder α] [PartialOrder β]
    {d : α → β} [hd : MereoDim d] {P : β → Prop} (hP : QUA P) :
    QUA (P ∘ d) :=
  qua_pullback hd.toStrictMono hP

/-- QUA pullback along a composed dimension chain. Given two `MereoDim`
    morphisms `d₁ : α → β` and `d₂ : β → γ`, QUA on γ pulls back to
    QUA on α through the chain `d₂ ∘ d₁`. -/
theorem qua_pullback_mereoDim_comp {α β γ : Type*}
    [PartialOrder α] [PartialOrder β] [PartialOrder γ]
    {d₁ : α → β} {d₂ : β → γ} (hd₁ : MereoDim d₁) (hd₂ : MereoDim d₂)
    {P : γ → Prop} (hP : QUA P) :
    QUA (P ∘ d₂ ∘ d₁) :=
  qua_pullback (hd₂.comp hd₁).toStrictMono hP

/-- Every `MereoDim d` is `Monotone`: the forgetful map from the category
    of partial orders with strict monotone maps to the category of
    preorders with monotone maps. -/
theorem mereoDim_monotone {α β : Type*}
    [PartialOrder α] [PartialOrder β]
    {d : α → β} (hd : MereoDim d) :
    Monotone d :=
  hd.toStrictMono.monotone

/-- Every `ExtMeasure μ` gives a monotone map to (ℚ, ≤). -/
theorem extMeasure_monotone {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} (hμ : ExtMeasure α μ) :
    Monotone μ :=
  (extMeasure_strictMono hμ).monotone

/-- A mereological dimension chain: a two-leg pipeline
    Source →f Inter →μ Measure where both legs are MereoDim.
    The three canonical instances:
    - Temporal: Events →τ Intervals →dur ℚ
    - Spatial: Events →σ Paths →dist ℚ
    - Object: Events →θ Entities →μ ℚ -/
structure DimensionChain
    {Source Inter Measure : Type*}
    [PartialOrder Source] [PartialOrder Inter] [PartialOrder Measure]
    (f : Source → Inter) (μ : Inter → Measure) where
  leg₁ : MereoDim f
  leg₂ : MereoDim μ

namespace DimensionChain

variable {Source Inter Measure : Type*}
    [PartialOrder Source] [PartialOrder Inter] [PartialOrder Measure]
    {f : Source → Inter} {μ : Inter → Measure}

/-- The composed map is a MereoDim. -/
def composed (dc : DimensionChain f μ) : MereoDim (μ ∘ f) :=
  MereoDim.comp dc.leg₂ dc.leg₁

/-- QUA on Measure pulls back to QUA on Source through the full chain. -/
theorem qua_transfer (dc : DimensionChain f μ)
    {P : Measure → Prop} (hP : QUA P) :
    QUA (P ∘ μ ∘ f) := by
  haveI := dc.composed
  exact qua_pullback_mereoDim hP

/-- QUA on Inter pulls back to QUA on Source through the first leg. -/
theorem qua_transfer_leg₁ (dc : DimensionChain f μ)
    {P : Inter → Prop} (hP : QUA P) :
    QUA (P ∘ f) := by
  haveI := dc.leg₁
  exact qua_pullback_mereoDim hP

/-- QUA on Measure pulls back to QUA on Inter through the second leg. -/
theorem qua_transfer_leg₂ (dc : DimensionChain f μ)
    {P : Measure → Prop} (hP : QUA P) :
    QUA (P ∘ μ) := by
  haveI := dc.leg₂
  exact qua_pullback_mereoDim hP

end DimensionChain

/-- CUM + fresh incomparable element → exists P-element with strictly
    larger measure. The structural content of "CUM → open scale."

    Given P(x) and fresh y with P(y) and ¬ y ≤ x, then x ⊔ y satisfies P
    (by CUM) and μ(x ⊔ y) > μ(x) (by StrictMono, since x < x ⊔ y). -/
theorem cum_exceeds_source {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} [hμ : ExtMeasure α μ]
    {P : α → Prop} (hCum : CUM P)
    {x y : α} (hx : P x) (hy : P y) (hyx : ¬ y ≤ x) :
    P (x ⊔ y) ∧ μ (x ⊔ y) > μ x := by
  constructor
  · exact hCum hx hy
  · have hle : x ≤ x ⊔ y := le_sup_left
    have hne : x ≠ x ⊔ y := fun heq => hyx (heq ▸ le_sup_right)
    exact hμ.strict_mono _ _ (lt_of_le_of_ne hle hne)

/-- CUM + disjoint fresh supply with minimum measure → measurement unbounded.

    If P is CUM and for every P-element x there exists a disjoint P-element y
    with μ(y) ≥ δ > 0, then P-elements achieve arbitrarily large measure.
    This is the structural content of information collapse: CUM predicates
    with enough disjoint material have no inherent measurement ceiling.

    The hypothesis requires `¬ Overlap x y` (not merely `¬ y ≤ x`) because
    overlap allows the increment μ(x ⊔ y) - μ(x) to shrink to zero, making
    the series of increments convergent. With `¬ Overlap`, additivity gives
    μ(x ⊔ y) = μ(x) + μ(y) ≥ μ(x) + δ, guaranteeing linear growth.

    The proof iterates `k` disjoint extensions from `x₀`, each adding at
    least δ to the measure. By the Archimedean property of ℚ, choosing
    k > (M - μ(x₀)) / δ suffices. -/
theorem cum_measure_unbounded {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} [hμ : ExtMeasure α μ]
    {P : α → Prop} (hCum : CUM P)
    {δ : ℚ} (hδ : 0 < δ)
    (hSupply : ∀ (x : α), P x → ∃ (y : α), P y ∧ ¬ Overlap x y ∧ δ ≤ μ y)
    (x₀ : α) (hx₀ : P x₀) (M : ℚ) :
    ∃ (z : α), P z ∧ μ z > M := by
  -- After k disjoint extensions from any P-element, measure grows by ≥ k * δ
  have iterate : ∀ (k : ℕ) (x : α), P x →
      ∃ (z : α), P z ∧ μ z ≥ μ x + ↑k * δ := by
    intro k
    induction k with
    | zero => intro x hx; exact ⟨x, hx, by simp⟩
    | succ k ih =>
      intro x hx
      obtain ⟨z, hPz, hμz⟩ := ih x hx
      obtain ⟨y, hPy, hDisj, hμy⟩ := hSupply z hPz
      refine ⟨z ⊔ y, hCum hPz hPy, ?_⟩
      rw [hμ.additive z y hDisj, Nat.cast_succ, add_mul, one_mul]
      linarith
  -- By Archimedean ℚ, find n with n * δ > M - μ(x₀)
  obtain ⟨n, hn⟩ := exists_nat_gt ((M - μ x₀) / δ)
  obtain ⟨z, hPz, hμz⟩ := iterate n x₀ hx₀
  exact ⟨z, hPz, by rw [div_lt_iff₀ hδ] at hn; linarith⟩

/-- The three dimension chains all instantiate the same pattern:
    IsSumHom + Injective → MereoDim → QUA pullback.
    This theorem states the pattern for any sum homomorphism. -/
theorem sumHom_qua_pullback_pattern {α β : Type*}
    [SemilatticeSup α] [SemilatticeSup β]
    {f : α → β} [hf : IsSumHom f] (hinj : Function.Injective f)
    {P : β → Prop} (hP : QUA P) :
    QUA (P ∘ f) := by
  haveI := MereoDim.ofInjSumHom hinj
  exact qua_pullback_mereoDim hP

/-- CUM always pulls back through any sum homomorphism (no injectivity needed).
    All three dimension chains preserve atelicity/cumulativity. -/
theorem sumHom_cum_pullback_pattern {α β : Type*}
    [SemilatticeSup α] [SemilatticeSup β]
    {f : α → β} [hf : IsSumHom f]
    {P : β → Prop} (hP : CUM P) :
    CUM (P ∘ f) :=
  cum_pullback hf hP

end Mereology
