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
import Linglib.Core.Order.Antichain

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

theorem cum_qua_disjoint {α : Type*} [SemilatticeSup α]
    {P : α → Prop}
    (hne : ∃ (x y : α), P x ∧ P y ∧ x ≠ y) :
    ¬ (CUM P ∧ QUA P) := by
  intro ⟨hC, hQ⟩
  obtain ⟨x, y, hpx, hpy, hxy⟩ := hne
  exact qua_cum_incompatible hQ hpx hpy hxy hC

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
theorem SupHom.toIsSumHom {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    (f : SupHom α β) : IsSumHom f.toFun :=
  ⟨f.map_sup'⟩

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

/-! ### Classical (extensional) mereology ([hovda-2009])

[hovda-2009] catalogs the equivalent axiomatizations of *classical mereology*.
We adopt his headline characterization: classical mereology is the partial-order
parthood axioms together with **type-2 fusion existence** (`Fusion2E`) and
**weak supplementation** (`WeakSup`); equivalently (Tarski) a complete Boolean
algebra with the zero element removed. `Overlap` is Hovda's `∘`, proper part is
the order `<`, and disjointness is `¬ Overlap`. Mathlib's `IsLUB` plays the role
of Hovda's minimal upper bound `Mub` (minimal coincides with least under
antisymmetry), so the fusion-existence axiom delivers binary sums for free. -/

/-- Type-2 (Tarski) fusion ([hovda-2009] §1.1.2): `t` fuses the `P`-things iff
`t` is an upper bound on `P` and every part of `t` overlaps some `P`-thing. -/
def IsFusion {α : Type*} [PartialOrder α] (P : α → Prop) (t : α) : Prop :=
  (∀ x, P x → x ≤ t) ∧ ∀ y, y ≤ t → ∃ x, P x ∧ Overlap y x

/-- Classical (extensional) mereology ([hovda-2009] §3): parthood is a partial
order closed under type-2 fusion of every inhabited predicate (`Fusion2E`) and
satisfying weak supplementation (`WeakSup`). -/
class ClassicalMereology (α : Type*) [PartialOrder α] : Prop where
  /-- `Fusion2E`: every inhabited predicate has a type-2 fusion. -/
  fusion_exists : ∀ P : α → Prop, (∃ x, P x) → ∃ t, IsFusion P t
  /-- `WeakSup`: a proper part is supplemented by a disjoint part. -/
  weak_supplementation : ∀ x y : α, x < y → ∃ z, z ≤ y ∧ ¬ Overlap z x

/-- A type-2 fusion of `P` is the least upper bound of `P` ([hovda-2009] Fu2MUB):
weak supplementation forces the fusion (which is by definition *an* upper bound)
to be the *least* one. -/
theorem IsFusion.isLUB {α : Type*} [PartialOrder α] [ClassicalMereology α]
    {P : α → Prop} {t : α} (h : IsFusion P t) : IsLUB {x | P x} t := by
  refine ⟨fun a ha => h.1 a ha, fun w hw => ?_⟩
  -- `w` is an upper bound on `P`; show the fusion `t ≤ w` via the sum of `{w, t}`.
  obtain ⟨v, hv⟩ :=
    ClassicalMereology.fusion_exists (fun u => u = w ∨ u = t) ⟨w, Or.inl rfl⟩
  have hwv : w ≤ v := hv.1 w (Or.inl rfl)
  have htv : t ≤ v := hv.1 t (Or.inr rfl)
  suffices hvw : v = w by rw [hvw] at htv; exact htv
  by_contra hne
  obtain ⟨s, hsv, hsw⟩ :=
    ClassicalMereology.weak_supplementation w v (lt_of_le_of_ne hwv (Ne.symm hne))
  obtain ⟨u, hu, p, hps, hpu⟩ := hv.2 s hsv
  rcases hu with rfl | rfl
  · exact hsw ⟨p, hps, hpu⟩
  · obtain ⟨a, hPa, q, hqp, hqa⟩ := h.2 p hpu
    exact hsw ⟨q, hqp.trans hps, hqa.trans (hw hPa)⟩

/-- Type-2 fusions are unique ([hovda-2009] Fu2Uniqueness): immediate from
`IsFusion.isLUB` and antisymmetry of the parthood order. -/
theorem IsFusion.unique {α : Type*} [PartialOrder α] [ClassicalMereology α]
    {P : α → Prop} {s t : α} (hs : IsFusion P s) (ht : IsFusion P t) : s = t :=
  hs.isLUB.unique ht.isLUB

/-- In a classical mereology every pair has a least upper bound (the binary sum
`a ⊕ b`), obtained by fusing `{a, b}`. -/
theorem ClassicalMereology.exists_isLUB_pair {α : Type*} [PartialOrder α]
    [ClassicalMereology α] (a b : α) : ∃ s, IsLUB {a, b} s := by
  obtain ⟨t, ht⟩ := ClassicalMereology.fusion_exists (fun u => u = a ∨ u = b) ⟨a, Or.inl rfl⟩
  refine ⟨t, ?_⟩
  have h := ht.isLUB
  rwa [show {x | x = a ∨ x = b} = ({a, b} : Set α) from by ext x; simp [Set.mem_insert_iff]] at h

/-- The binary-sum (join-semilattice) structure carried by every classical
mereology, with parthood `≤` as its order. The join `a ⊔ b` is the unique
type-2 fusion of `{a, b}`; noncomputable because it is extracted by choice from
the fusion-existence axiom. -/
@[reducible] noncomputable def ClassicalMereology.toSemilatticeSup {α : Type*}
    [PartialOrder α] [ClassicalMereology α] : SemilatticeSup α :=
  { ‹PartialOrder α› with
    sup := fun a b => Classical.choose (ClassicalMereology.exists_isLUB_pair a b)
    le_sup_left := fun a b =>
      (Classical.choose_spec (ClassicalMereology.exists_isLUB_pair a b)).1 (Set.mem_insert _ _)
    le_sup_right := fun a b =>
      (Classical.choose_spec (ClassicalMereology.exists_isLUB_pair a b)).1
        (Set.mem_insert_of_mem _ rfl)
    sup_le := fun a b c ha hb =>
      (Classical.choose_spec (ClassicalMereology.exists_isLUB_pair a b)).2
        (fun x hx => by rcases hx with rfl | rfl
                        · exact ha
                        · exact hb) }

/-! ### Atomic domains (discrete orders)

The sort-level, instance-resolvable companion of `QUA`. An `IsAtomicDomain` is a
`PartialOrder` every element of which is an `Atom` (`IsMin`) — equivalently a
discrete order (`a ≤ b ↔ a = b`), equivalently a sort on which
`QUA (fun _ => True)` holds. It is the single consolidation point for the
"flat/atomic domain" that recurs across studies (the `Student`-style fixtures)
and that distributive determiners (English *each*, the `ONE_AT` presupposition)
require of their restrictor sort: a sort with a non-atomic element (time
intervals) simply has no instance. Everything below reduces to the existing
`Atom`/`QUA`/`IsAntichain` machinery — this class adds resolution ergonomics, not
a new notion. -/

/-- A `PartialOrder` all of whose elements are atoms (`IsMin`) — a discrete order
/ a `≤`-antichain on the whole type. -/
class IsAtomicDomain (α : Type*) [PartialOrder α] : Prop where
  /-- Every element is an atom. -/
  all_atoms : ∀ x : α, Atom x

/-- A discrete order (`a ≤ b ↔ a = b`) is an atomic domain — the canonical way to
discharge the instance for `Student`-style flat fixtures. -/
theorem isAtomicDomain_of_le_iff_eq {α : Type*} [PartialOrder α]
    (h : ∀ a b : α, a ≤ b ↔ a = b) : IsAtomicDomain α where
  all_atoms x := fun {b} hbx => le_of_eq ((h b x).1 hbx).symm

/-- The whole type of an atomic domain is quantized — the sort-level face of
`QUA`, routed through `qua_of_atom`. -/
theorem IsAtomicDomain.qua_true {α : Type*} [PartialOrder α] [IsAtomicDomain α] :
    QUA (fun _ : α => True) :=
  qua_of_atom fun x _ => IsAtomicDomain.all_atoms x

/-- In an atomic domain, overlapping elements are equal (atoms are disjoint). -/
theorem IsAtomicDomain.eq_of_overlap {α : Type*} [PartialOrder α] [IsAtomicDomain α]
    {x y : α} (h : Overlap x y) : x = y :=
  let ⟨_, hzx, hzy⟩ := h
  (Atom.eq (IsAtomicDomain.all_atoms x) hzx).symm.trans
    (Atom.eq (IsAtomicDomain.all_atoms y) hzy)

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
    {x y : α} (hx : Maximal P x) (hy : Maximal P y) : x = y := by
  have hxy := hCum hx.1 hy.1
  exact (le_antisymm le_sup_left (hx.2 hxy le_sup_left)).trans
    (le_antisymm le_sup_right (hy.2 hxy le_sup_right)).symm

theorem qua_pullback {α β : Type*} [PartialOrder α] [PartialOrder β]
    {d : α → β} (hd : StrictMono d)
    {P : β → Prop} (hP : QUA P) :
    QUA (P ∘ d) :=
  hP.preimage_strictMono hd

/-- CUM pullback along a sum homomorphism: `CUM P → CUM (P ∘ d)`. The CUM twin
    of `qua_pullback`; wraps `IsSumHom.cum_preimage`. -/
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

/-- Singleton predicates are quantized: `{x | x = n}` is QUA on any partial
    order (a subsingleton is an antichain). -/
theorem singleton_qua {α : Type*} [PartialOrder α]
    (n : α) : QUA (· = n) :=
  Set.Subsingleton.isAntichain (fun _ ha _ hb => ha.trans hb.symm) _

/-- Measure phrases are quantized: `{x | μ x = n}` is QUA when μ is an extensive
    measure ([krifka-1998] §2.2) — `singleton_qua` pulled back along μ. -/
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

theorem IsSumHom.strictMono_of_injective {α β : Type*}
    [SemilatticeSup α] [SemilatticeSup β]
    {f : α → β} (hf : IsSumHom f) (hinj : Function.Injective f) :
    StrictMono f := by
  intro x y hlt
  exact lt_of_le_of_ne (hf.monotone hlt.le) (fun h => hlt.ne (hinj h))

/-! ### Functional QUA propagation -/

/-- QUA propagation through an injective sum homomorphism: the functional case
    of [krifka-1998] §3.3 (SINC reduces to `IsSumHom` + injective), where the
    relational `qua_propagation` (Krifka1998.lean) becomes `qua_pullback`. -/
theorem qua_of_injective_sumHom {α β : Type*}
    [SemilatticeSup α] [SemilatticeSup β]
    {f : α → β} (hf : IsSumHom f) (hinj : Function.Injective f)
    {P : β → Prop} (hP : QUA P) :
    QUA (P ∘ f) :=
  qua_pullback (hf.strictMono_of_injective hinj) hP

/-! ### CUM/QUA Pullback Interaction -/

def gHomogeneous {α : Type*} [PartialOrder α] (P : α → Prop) : Prop :=
  ∀ (x y : α), P x → y < x → ∃ z, z ≤ y ∧ P z

/-- DIV implies g-homogeneity: if every part of a P-entity is P, then
    a fortiori every proper part has a P-part (itself). -/
theorem div_implies_gHomogeneous {α : Type*} [PartialOrder α]
    {P : α → Prop} (hDiv : DIV P) : gHomogeneous P :=
  fun _ y hPx hlt => ⟨y, le_refl y, hDiv (le_of_lt hlt) hPx⟩

def FakeMass {α : Type*} [SemilatticeSup α] (P : α → Prop) : Prop :=
  CUM P ∧ ¬ gHomogeneous P

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
    push Not at hcon
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
    (Set.union_subset (fun _ ha => ⟨D₁, h₁, ha⟩) (fun _ ha => ⟨D₂, h₂, ha⟩))
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

class MereoDim {α β : Type*} [PartialOrder α] [PartialOrder β]
    (d : α → β) : Prop where
  /-- The underlying strict monotonicity proof. -/
  toStrictMono : StrictMono d

theorem MereoDim.ofInjSumHom {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    {f : α → β} [hf : IsSumHom f] (hinj : Function.Injective f) : MereoDim f :=
  ⟨hf.strictMono_of_injective hinj⟩

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

/-- QUA pullback via `MereoDim`: typeclass-dispatched version of
    `qua_pullback`. When `[MereoDim d]` is available (automatically
    for any `ExtMeasure`), QUA pulls back without manual `StrictMono`
    threading. -/
theorem qua_pullback_mereoDim {α β : Type*} [PartialOrder α] [PartialOrder β]
    {d : α → β} [hd : MereoDim d] {P : β → Prop} (hP : QUA P) :
    QUA (P ∘ d) :=
  qua_pullback hd.toStrictMono hP

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
theorem composed (dc : DimensionChain f μ) : MereoDim (μ ∘ f) :=
  MereoDim.comp dc.leg₂ dc.leg₁

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

