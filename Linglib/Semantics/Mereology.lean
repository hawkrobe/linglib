import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Atoms
import Mathlib.Order.SupClosed
import Linglib.Core.Order.Antichain
import Linglib.Core.Order.Valuation

/-!
# Algebraic mereology

This file defines the mereological vocabulary of algebraic semantics over mathlib's
order hierarchy: parthood is `≤` on a `PartialOrder`, mereological sum is `⊔` on a
`SemilatticeSup`, and the reference properties of [link-1983] and [krifka-1989] are
the corresponding mathlib set predicates — cumulativity is `SupClosed`, divisiveness
is `IsLowerSet`, quantization is `IsAntichain (· ≤ ·)`, and Link's closure `*P` is
`supClosure`.

A carrier may or may not contain a null individual: a Boolean-algebra model has
`⊥ = ∅`, whereas classical mereology in [hovda-2009]'s sense has none. Mathlib's
`IsBot` marks it in either case, so atoms, overlap, extensive measures and atom
counts are stated relative to `IsBot`: on an `OrderBot` carrier they are mathlib's
`IsAtom` and `¬ Disjoint`, and on a `NoBotOrder` carrier `IsMin` and shared-part
overlap.

## Main definitions

* `CUM`, `DIV`, `QUA` — cumulative, divisive and quantized reference.
* `AlgClosure P` — the closure of `P` under binary sum, as an inductive predicate;
  `setOf_algClosure` identifies it with `supClosure`.
* `Atom`, `Overlap` — atoms and overlap, relative to the null individual `IsBot`.
* `ClassicalMereology α` — [hovda-2009]'s axiomatization by type-2 fusion and weak
  supplementation.
* `IsAtomicDomain α` — a carrier all of whose non-null elements are atoms.
* `ExtMeasure μ` — [krifka-1998]'s extensive measure functions; positive lattice
  valuations are extensive (`ExtMeasure.ofPositiveValuation`).
* `QMOD`, `atomize`, `atomCount` — quantizing modification, the `P`-atoms, and the
  number of atoms below an element.
* `IsMaxDisjointIn`, `nullSchema` — individuation perspectives ([landman-2020],
  [sutton-filip-2021]).

## Main results

* `qua_cum_incompatible` — a quantized predicate with two members is not cumulative.
* `atom_iff_isAtom`, `atom_iff_isMin`, `overlap_iff_not_disjoint` — the bounded and
  bottomless faces of atoms and overlap.
* `IsFusion.isLUB`, `ClassicalMereology.toSemilatticeSup` — fusions are least upper
  bounds, so a classical mereology carries binary sums.
* `extMeasure_qua`, `qmod_qua` — measure phrases are quantized.
* `cum_measure_unbounded` — a cumulative predicate with a supply of disjoint
  extensions has unbounded measure.

## References

* [champollion-2017], [hovda-2009], [krifka-1989], [krifka-1998], [link-1983]
-/

namespace Mereology

variable {α β : Type*}

/-! ### Reference properties

Cumulative, divisive and quantized reference are the mathlib set predicates
`SupClosed`, `IsLowerSet` and `IsAntichain (· ≤ ·)` on the extension of a predicate,
so hypotheses of these forms are applied directly: `hC hx hy : P (x ⊔ y)`,
`hD hle hx : P y`, `hQ hx hy hne : ¬ x ≤ y`. -/

/-- Divisive reference: every part of a `P`-element is `P`. -/
abbrev DIV [Preorder α] (P : α → Prop) : Prop := IsLowerSet {x | P x}

section PartialOrder

variable [PartialOrder α] {P : α → Prop}

/-- Quantized reference ([krifka-1989]): no proper part of a `P`-element is `P`. -/
abbrev QUA (P : α → Prop) : Prop := IsAntichain (· ≤ ·) {x | P x}

/-- The paper form of quantization: no `P`-element lies strictly below another. -/
theorem qua_of_forall (h : ∀ x y, P x → y < x → ¬ P y) : QUA P :=
  fun _ ha _ hb hne hle => h _ _ hb (lt_of_le_of_ne hle hne) ha

/-- A singleton predicate is quantized. -/
theorem singleton_qua (n : α) : QUA (· = n) :=
  Set.Subsingleton.isAntichain (fun _ ha _ hb => ha.trans hb.symm) _

/-- Quantization pulls back along strictly monotone maps. -/
theorem qua_pullback [PartialOrder β] {d : α → β} (hd : StrictMono d) {P : β → Prop}
    (hP : QUA P) : QUA (P ∘ d) :=
  hP.preimage_strictMono hd

/-- The `P`-atoms ([krifka-1989]): the minimal `P`-elements. -/
abbrev atomize (P : α → Prop) : α → Prop := Minimal P

instance [Fintype α] [DecidableLE α] [DecidablePred P] (x : α) : Decidable (Minimal P x) :=
  decidable_of_iff (P x ∧ ∀ y, P y → y ≤ x → x ≤ y) Iff.rfl

theorem atomize_sub {x : α} (h : atomize P x) : P x := h.1

/-- The `P`-atoms are quantized. -/
theorem atomize_qua : QUA (atomize P) := setOfPred_minimal_antichain P

end PartialOrder

section SemilatticeSup

variable [SemilatticeSup α] {P : α → Prop}

/-- Cumulative reference ([link-1983], [krifka-1989]): `P` is closed under sum. -/
abbrev CUM (P : α → Prop) : Prop := SupClosed {x | P x}

instance [Fintype α] [DecidablePred P] : Decidable (CUM P) :=
  decidable_of_iff (∀ x, P x → ∀ y, P y → P (x ⊔ y)) Iff.rfl

/-- A quantized predicate with two members is not cumulative. -/
theorem qua_cum_incompatible (hQ : QUA P) {x y : α} (hx : P x) (hy : P y) (hne : x ≠ y) :
    ¬ CUM P := by
  intro hC
  have hxy : P (x ⊔ y) := hC hx hy
  rcases eq_or_lt_of_le (le_sup_left : x ≤ x ⊔ y) with hx_eq | hx_lt
  · rcases eq_or_lt_of_le (le_sup_right : y ≤ x ⊔ y) with hy_eq | hy_lt
    · exact hne (hx_eq.trans hy_eq.symm)
    · exact hQ hy hxy hy_lt.ne hy_lt.le
  · exact hQ hx hxy hx_lt.ne hx_lt.le

/-- A cumulative predicate has at most one maximal element. -/
theorem cum_maximal_unique (hCum : CUM P) {x y : α} (hx : Maximal P x) (hy : Maximal P y) :
    x = y :=
  have hxy := hCum hx.1 hy.1
  (le_antisymm le_sup_left (hx.2 hxy le_sup_left)).trans
    (le_antisymm le_sup_right (hy.2 hxy le_sup_right)).symm

/-! ### Algebraic closure -/

/-- The closure `*P` of `P` under binary sum ([link-1983]; [champollion-2017]). The
inductive presentation supports induction on sums; `setOf_algClosure` identifies it with
mathlib's `supClosure`. -/
inductive AlgClosure (P : α → Prop) : α → Prop where
  /-- Every `P`-element is in `*P`. -/
  | base {x : α} : P x → AlgClosure P x
  /-- `*P` is closed under sum. -/
  | sum {x y : α} : AlgClosure P x → AlgClosure P y → AlgClosure P (x ⊔ y)

theorem algClosure_cum : CUM (AlgClosure P) := fun _ hx _ hy => .sum hx hy

theorem subset_algClosure {x : α} (h : P x) : AlgClosure P x := .base h

theorem algClosure_mono {Q : α → Prop} (h : ∀ x, P x → Q x) :
    ∀ x, AlgClosure P x → AlgClosure Q x := by
  intro x hx
  induction hx with
  | base hp => exact .base (h _ hp)
  | sum _ _ ih₁ ih₂ => exact .sum ih₁ ih₂

/-- Every element of `*P` has a `P`-element below it. -/
theorem algClosure_has_base {x : α} (h : AlgClosure P x) : ∃ a, P a ∧ a ≤ x := by
  induction h with
  | base hp => exact ⟨_, hp, le_rfl⟩
  | sum _ _ ih₁ _ => obtain ⟨a, ha, hle⟩ := ih₁; exact ⟨a, ha, hle.trans le_sup_left⟩

/-- A cumulative predicate is its own closure. -/
theorem algClosure_of_cum (hCum : CUM P) {x : α} : AlgClosure P x ↔ P x :=
  ⟨fun h => by induction h with
    | base h => exact h
    | sum _ _ ihx ihy => exact hCum ihx ihy,
   .base⟩

/-- `*P` is mathlib's `supClosure` of the extension of `P`. -/
theorem setOf_algClosure (P : α → Prop) : {x | AlgClosure P x} = supClosure {x | P x} :=
  Set.Subset.antisymm
    (fun _ h => by
      induction (h : AlgClosure P _) with
      | base h => exact subset_supClosure h
      | sum _ _ ihx ihy => exact supClosed_supClosure ihx ihy)
    (supClosure_min (fun _ => .base) algClosure_cum)

end SemilatticeSup

/-! ### Atoms and overlap

The null individual of a carrier, if it has one, is its `IsBot` element: `⊥` on an
`OrderBot` carrier, and nothing on a `NoBotOrder` carrier such as a classical
mereology in [hovda-2009]'s sense. -/

section Atoms

variable [PartialOrder α] {x y : α}

instance [OrderBot α] [DecidableEq α] (x : α) : Decidable (IsBot x) :=
  decidable_of_iff (x = ⊥) isBot_iff_eq_bot.symm

instance [Fintype α] [DecidableLE α] (x : α) : Decidable (IsBot x) :=
  inferInstanceAs (Decidable (∀ y, x ≤ y))

/-- An atom ([link-1983]): a non-null element with no non-null proper part, i.e.
`Minimal` over the non-null elements. The `P`-relative notion is `atomize`. -/
abbrev Atom (x : α) : Prop := Minimal (¬ IsBot ·) x

theorem Atom.not_isBot (h : Atom x) : ¬ IsBot x := h.1

/-- An atom's only non-null part is itself. -/
theorem Atom.eq (h : Atom x) (hle : y ≤ x) (hy : ¬ IsBot y) : y = x :=
  le_antisymm hle (h.2 hy hle)

theorem isAntichain_setOf_atom : IsAntichain (· ≤ ·) {x : α | Atom x} :=
  setOfPred_minimal_antichain _

/-- A predicate holding only of atoms is quantized. -/
theorem qua_of_atom {P : α → Prop} (h : ∀ ⦃x⦄, P x → Atom x) : QUA P :=
  isAntichain_setOf_atom.subset h

theorem atom_qua (hAtom : Atom x) : QUA (· = x) := qua_of_atom fun _ hz => hz ▸ hAtom

variable (α) in
/-- The number of atoms below `x`. -/
noncomputable def atomCount [Fintype α] (x : α) : ℕ := {a : α | Atom a ∧ a ≤ x}.ncard

/-- `x` and `y` overlap ([krifka-1998]) if they share a non-null part. -/
def Overlap (x y : α) : Prop := ∃ z, ¬ IsBot z ∧ z ≤ x ∧ z ≤ y

theorem Overlap.refl (h : ¬ IsBot x) : Overlap x x := ⟨x, h, le_rfl, le_rfl⟩

theorem Overlap.symm (h : Overlap x y) : Overlap y x :=
  let ⟨z, hz, hzx, hzy⟩ := h; ⟨z, hz, hzy, hzx⟩

theorem Overlap.not_isBot_left (h : Overlap x y) : ¬ IsBot x :=
  let ⟨_, hz, hzx, _⟩ := h; fun hx => hz (hx.mono hzx)

theorem Overlap.not_isBot_right (h : Overlap x y) : ¬ IsBot y := h.symm.not_isBot_left

end Atoms

/-- The sum of two distinct atoms is not an atom. -/
theorem not_atom_sup_of_ne [SemilatticeSup α] {x y : α} (hx : Atom x) (hy : Atom y) (hne : x ≠ y) :
    ¬ Atom (x ⊔ y) :=
  fun h => hne ((h.eq le_sup_left hx.not_isBot).trans (h.eq le_sup_right hy.not_isBot).symm)

/-! ### Bounded and bottomless carriers -/

section OrderBot

variable [PartialOrder α] [OrderBot α] {x y : α}

theorem atom_iff_isAtom : Atom x ↔ IsAtom x := by
  simp only [Atom, Minimal, isBot_iff_eq_bot, isAtom_iff_le_of_ge, ne_eq]

theorem overlap_iff_not_disjoint : Overlap x y ↔ ¬ Disjoint x y := by
  constructor
  · rintro ⟨z, hz, hzx, hzy⟩ hd
    exact hz (isBot_iff_eq_bot.2 (le_bot_iff.mp (hd hzx hzy)))
  · intro hd
    by_contra h
    exact hd fun z hzx hzy => le_bot_iff.mpr
      (by_contra fun hz => h ⟨z, mt isBot_iff_eq_bot.1 hz, hzx, hzy⟩)

/-- The atoms of the non-null predicate on a bounded carrier are its `IsAtom`s. -/
theorem atomize_ne_bot : atomize (· ≠ (⊥ : α)) = IsAtom := by
  funext x; exact propext isAtom_iff_le_of_ge.symm

end OrderBot

/-- Without a null individual, the atoms are the minimal elements. -/
theorem atom_iff_isMin [PartialOrder α] [NoBotOrder α] {x : α} : Atom x ↔ IsMin x :=
  ⟨fun h _ hy => h.2 (not_isBot _) hy, fun h => ⟨not_isBot x, fun _ _ hy => h hy⟩⟩

/-! ### Classical mereology

[hovda-2009] characterizes classical mereology as the partial-order parthood axioms
together with type-2 fusion existence (`Fusion2E`) and weak supplementation (`WeakSup`);
equivalently, a complete Boolean algebra with its zero removed. `Overlap` is Hovda's
`∘`, proper parthood is `<`, and `IsLUB` plays the role of his minimal upper bound,
so fusion existence delivers binary sums. -/

section Classical

variable [PartialOrder α]

/-- Type-2 fusion: `t` fuses the `P`-elements if it bounds them above and every part of
`t` overlaps a `P`-element. -/
def IsFusion (P : α → Prop) (t : α) : Prop :=
  (∀ x, P x → x ≤ t) ∧ ∀ y, y ≤ t → ∃ x, P x ∧ Overlap y x

/-- Classical mereology: every inhabited predicate has a type-2 fusion, and every proper
part is supplemented by a disjoint part. -/
class ClassicalMereology (α : Type*) [PartialOrder α] : Prop where
  /-- `Fusion2E`: every inhabited predicate has a type-2 fusion. -/
  fusion_exists : ∀ P : α → Prop, (∃ x, P x) → ∃ t, IsFusion P t
  /-- `WeakSup`: a proper part is supplemented by a disjoint part. -/
  weak_supplementation : ∀ x y : α, x < y → ∃ z, z ≤ y ∧ ¬ Overlap z x

variable [ClassicalMereology α]

/-- A type-2 fusion is a least upper bound: weak supplementation forces the fusion, an
upper bound by definition, to be the least one. -/
theorem IsFusion.isLUB {P : α → Prop} {t : α} (h : IsFusion P t) : IsLUB {x | P x} t := by
  refine ⟨fun a ha => h.1 a ha, fun w hw => ?_⟩
  obtain ⟨v, hv⟩ :=
    ClassicalMereology.fusion_exists (fun u => u = w ∨ u = t) ⟨w, Or.inl rfl⟩
  have hwv : w ≤ v := hv.1 w (Or.inl rfl)
  have htv : t ≤ v := hv.1 t (Or.inr rfl)
  suffices hvw : v = w by rw [hvw] at htv; exact htv
  by_contra hne
  obtain ⟨s, hsv, hsw⟩ :=
    ClassicalMereology.weak_supplementation w v (lt_of_le_of_ne hwv (Ne.symm hne))
  obtain ⟨u, hu, p, hp, hps, hpu⟩ := hv.2 s hsv
  rcases hu with rfl | rfl
  · exact hsw ⟨p, hp, hps, hpu⟩
  · obtain ⟨a, hPa, q, hq, hqp, hqa⟩ := h.2 p hpu
    exact hsw ⟨q, hq, hqp.trans hps, hqa.trans (hw hPa)⟩

theorem IsFusion.unique {P : α → Prop} {s t : α} (hs : IsFusion P s) (ht : IsFusion P t) :
    s = t :=
  hs.isLUB.unique ht.isLUB

/-- Every pair has a least upper bound, the fusion of `{a, b}`. -/
theorem ClassicalMereology.exists_isLUB_pair (a b : α) : ∃ s, IsLUB {a, b} s := by
  obtain ⟨t, ht⟩ := ClassicalMereology.fusion_exists (fun u => u = a ∨ u = b) ⟨a, Or.inl rfl⟩
  refine ⟨t, ?_⟩
  have h := ht.isLUB
  rwa [show {x | x = a ∨ x = b} = ({a, b} : Set α) from by ext x; simp [Set.mem_insert_iff]] at h

/-- The sum structure of a classical mereology: `a ⊔ b` is the fusion of `{a, b}`,
extracted by choice from fusion existence. -/
@[reducible] noncomputable def ClassicalMereology.toSemilatticeSup : SemilatticeSup α :=
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

end Classical

/-! ### Atomic domains -/

section AtomicDomain

variable [PartialOrder α]

/-- A carrier all of whose non-null elements are atoms — a discrete order, the sort on
which distributive determiners find only atoms. -/
class IsAtomicDomain (α : Type*) [PartialOrder α] : Prop where
  /-- Every non-null element is an atom. -/
  all_atoms : ∀ x : α, ¬ IsBot x → Atom x

/-- A discrete order is an atomic domain. -/
theorem isAtomicDomain_of_le_iff_eq (h : ∀ a b : α, a ≤ b ↔ a = b) : IsAtomicDomain α where
  all_atoms x hx := ⟨hx, fun _ _ hbx => le_of_eq ((h _ x).1 hbx).symm⟩

/-- In an atomic domain, overlapping elements are equal. -/
theorem IsAtomicDomain.eq_of_overlap [IsAtomicDomain α] {x y : α} (h : Overlap x y) :
    x = y := by
  obtain ⟨z, hz, hzx, hzy⟩ := h
  rw [← Atom.eq (IsAtomicDomain.all_atoms x fun hx => hz (hx.mono hzx)) hzx hz,
    ← Atom.eq (IsAtomicDomain.all_atoms y fun hy => hz (hy.mono hzy)) hzy hz]

end AtomicDomain

/-! ### Extensive measures -/

/-- Quantizing modification ([krifka-1989]): the `R`-elements of measure `n`. -/
def QMOD {M : Type*} (R : α → Prop) (μ : α → M) (n : M) : α → Prop := fun x => R x ∧ μ x = n

section ExtMeasure

variable {M : Type*} [SemilatticeSup α] [AddCommMonoid M] [PartialOrder M]

/-- An extensive measure function ([krifka-1998]): additive over non-overlapping
elements, positive on non-null elements, and strictly monotone. On a bounded carrier
additivity is disjoint additivity, so positive lattice valuations vanishing at `⊥` are
extensive (`ExtMeasure.ofPositiveValuation`); `Finset.card` is the model instance. -/
class ExtMeasure (μ : α → M) : Prop where
  /-- `μ` is additive over non-overlapping elements. -/
  additive : ∀ x y, ¬ Overlap x y → μ (x ⊔ y) = μ x + μ y
  /-- Non-null elements have positive measure. -/
  positive : ∀ x, ¬ IsBot x → 0 < μ x
  /-- Proper parts have strictly smaller measure. -/
  strictMono : StrictMono μ

variable {μ : α → M} [ExtMeasure μ]

/-- Measure phrases are quantized ([krifka-1998]): the elements of measure `n` form an
antichain. -/
theorem extMeasure_qua (n : M) : QUA (μ · = n) :=
  qua_pullback ExtMeasure.strictMono (singleton_qua n)

/-- A quantizing modification by an extensive measure is quantized. -/
theorem qmod_qua (R : α → Prop) (n : M) : QUA (QMOD R μ n) :=
  (extMeasure_qua n).subset fun _ h => h.2

/-- A cumulative predicate each of whose members extends by a non-overlapping member of
measure at least `δ > 0` has unbounded measure. -/
theorem cum_measure_unbounded {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Archimedean K] {μ : α → K} [hμ : ExtMeasure μ] {P : α → Prop} (hCum : CUM P) {δ : K}
    (hδ : 0 < δ) (hSupply : ∀ x, P x → ∃ y, P y ∧ ¬ Overlap x y ∧ δ ≤ μ y) {x₀ : α}
    (hx₀ : P x₀) (b : K) : ∃ z, P z ∧ b < μ z := by
  have iterate : ∀ (k : ℕ) (x : α), P x → ∃ z, P z ∧ μ x + k * δ ≤ μ z := by
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
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - μ x₀) / δ)
  obtain ⟨z, hPz, hμz⟩ := iterate n x₀ hx₀
  exact ⟨z, hPz, by rw [div_lt_iff₀ hδ] at hn; linarith⟩

end ExtMeasure

section Valuation

variable {M : Type*} [Lattice α] [OrderBot α] [AddCommMonoid M] [PartialOrder M]

/-- A positive lattice valuation vanishing at `⊥` is an extensive measure. -/
theorem ExtMeasure.ofPositiveValuation (v : α → M) [IsPositiveValuation v] (h0 : v ⊥ = 0) :
    ExtMeasure v where
  additive _ _ h :=
    IsLatticeValuation.map_sup_of_disjoint v h0 (not_not.mp (overlap_iff_not_disjoint.not.mp h))
  positive _ hx :=
    h0 ▸ IsPositiveValuation.strictMono (bot_lt_iff_ne_bot.mpr (mt isBot_iff_eq_bot.2 hx))
  strictMono := IsPositiveValuation.strictMono

instance [DecidableEq β] : ExtMeasure (Finset.card : Finset β → ℕ) :=
  ExtMeasure.ofPositiveValuation _ Finset.card_empty

end Valuation

/-! ### Individuation perspectives

A predicate is overlapping if two distinct members share a part, and disjoint otherwise; a
maximally disjoint subset is an individuation perspective ([landman-2011], [landman-2020]),
and the null schema of [sutton-filip-2021] unions all perspectives. The overlap relation
`ov` is a parameter (mereologically, `Overlap`). -/

section Individuation

variable (ov : α → α → Prop)

/-- Two distinct members of `P` share a part. -/
def OverlapPred (P : Set α) : Prop := ∃ x ∈ P, ∃ y ∈ P, x ≠ y ∧ ov x y

/-- No two distinct members of `P` share a part. -/
def DisjointPred (P : Set α) : Prop := ¬ OverlapPred ov P

theorem overlapPred_mono {P Q : Set α} (h : P ⊆ Q) (hP : OverlapPred ov P) : OverlapPred ov Q :=
  let ⟨x, hx, y, hy, hne, hov⟩ := hP; ⟨x, h hx, y, h hy, hne, hov⟩

theorem DisjointPred.anti {P Q : Set α} (h : P ⊆ Q) (hQ : DisjointPred ov Q) :
    DisjointPred ov P :=
  fun hP => hQ (overlapPred_mono ov h hP)

/-- `D` is a maximally disjoint subset of `P`: disjoint, and not extendable within `P`. -/
def IsMaxDisjointIn (D P : Set α) : Prop :=
  D ⊆ P ∧ DisjointPred ov D ∧ ∀ x ∈ P, x ∉ D → OverlapPred ov (insert x D)

/-- The null individuation schema: the union of all maximally disjoint subsets of `P`. -/
def nullSchema (P : Set α) : Set α := {x | ∃ D, IsMaxDisjointIn ov D P ∧ x ∈ D}

/-- The union of two distinct maximally disjoint subsets overlaps. -/
theorem overlapPred_union_of_maxDisjoint_ne {D₁ D₂ P : Set α} (h₁ : IsMaxDisjointIn ov D₁ P)
    (h₂ : IsMaxDisjointIn ov D₂ P) (hne : D₁ ≠ D₂) : OverlapPred ov (D₁ ∪ D₂) := by
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

/-- The null schema of a predicate with two distinct perspectives overlaps. -/
theorem overlapPred_nullSchema {D₁ D₂ P : Set α} (h₁ : IsMaxDisjointIn ov D₁ P)
    (h₂ : IsMaxDisjointIn ov D₂ P) (hne : D₁ ≠ D₂) : OverlapPred ov (nullSchema ov P) :=
  overlapPred_mono ov
    (Set.union_subset (fun _ ha => ⟨D₁, h₁, ha⟩) (fun _ ha => ⟨D₂, h₂, ha⟩))
    (overlapPred_union_of_maxDisjoint_ne ov h₁ h₂ hne)

/-- A disjoint predicate is its own null schema. -/
theorem nullSchema_eq_of_disjoint {P : Set α} (h : DisjointPred ov P) : nullSchema ov P = P := by
  ext x
  constructor
  · rintro ⟨D, hD, hx⟩
    exact hD.1 hx
  · intro hx
    exact ⟨P, ⟨Set.Subset.rfl, h, fun y hy hny => absurd hy hny⟩, hx⟩

end Individuation

end Mereology
