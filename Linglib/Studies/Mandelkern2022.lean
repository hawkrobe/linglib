module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.ModelTheory.Basic
public import Mathlib.Tactic.FinCases
public import Linglib.Logic.Assignment
public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Semantics.Presupposition.Context

/-!
# Mandelkern (2022): Witnesses

This file formalizes the bounded theory of definites and indefinites of [mandelkern-2022]. The
language is first-order with a two-place indefinite `ɜx(p, q)` and a two-place definite `ιx(p, q)`,
and a pronoun is a definite with the tautological restrictor `⊤x`. Truth at an assignment–world
pair is classical: an indefinite is an existential quantifier, a definite the conjunction of its
restrictor and scope. A second dimension, the bounds, is satisfied (*satt*) relative to a context,
a set of such pairs. An indefinite carries a witness bound, that if it is true its variable denotes
a witness, and a definite carries a familiarity bound in the sense of [heim-1982], that its
restrictor is true and satt throughout the context. Bounds project through the local contexts of
[schlenker-2009], and updating a context keeps, as in [stalnaker-1978], the points at which a
sentence is true and satt.

At a context the two dimensions form a `Presupposition.PartialProp` over assignment–world pairs
(`Formula.toPartialProp`), so bound entailment is the Strawson entailment of [von-fintel-1999] at
every context, the generalization the paper names (`BoundEntails`). Updates obey a small calculus:
a conjunction updates in sequence (`update_conj`), an indefinite updates as its body at the points
where it is true (`update_indef`), and a definite updates as the conjunction of its restrictor
and scope when its restrictor is idle on the context, and empties the context otherwise
(`update_iota_of_update_eq`, `update_iota_eq_empty`).

The paper's predictions follow. An indefinite keeps the points whose variable is a witness, so a
later definite or pronoun finds it familiar (`update_indef_then_the`, `update_indef_then_it`),
while a negated indefinite updates as a negated existential and licenses no pronoun, (19)
(`truthSet_neg_indef_atom₁`, `update_null_neg_indef_then_it`). The three renderings of open scope
in (20) are true and satt at the same indices (`truthSet_ex20a`, `truthSet_ex20b`,
`truthSet_ex20c`) without being logically equivalent. Double negation leaves both dimensions
unchanged, so the doubly negated indefinites of [karttunen-1976] license definites, and the
bathroom disjunction is true and satt where there is no F that is G and where `x` is an F, a G
and an H (`truthSet_bathroom`).

Footnote 20 of the paper extends the bound equivalences of (20) to any substitution instances of
`Fx`, `Gx`, `Hx` by formulae free in `x`. Three of the six bound entailments hold for all
formulae. The other three need the restrictor's truth to value `x`, as the truth of every atom
with `x` among its arguments does; this is the assumption the paper's argument on p. 1108
leaves tacit. Two of them, those into (20-c), still hold for all formulae at the points of the
context, where the pronoun's familiarity bound values `x` (`realize_ex20c_of_realize_ex20a`,
`realize_ex20c_of_realize_ex20b`). The third fails at a point of the null context for the
restrictor `¬ɜy(⊤y, R(x, y))`, which is free in `x` but true where `x` is unvalued
(`not_boundEntails_ex20b_ex20a`). Whether the footnote meant to admit such formulae the paper
leaves open; the refutation is of its literal wording.

## Main definitions

* `Mandelkern2022.Formula`: the language, with truth `Formula.Realize` and satisfaction of the
  bounds `Formula.Satt`.
* `Mandelkern2022.Formula.update`: the update of a context, which is also the local context `cᵖ`.
* `Mandelkern2022.BoundEntails`, `Mandelkern2022.LogicallyEntails`: the two consequence
  relations.

## Implementation notes

* An atomic valuation is a world-indexed family of first-order structures `I : W → L.Structure E`
  on the domain `E`, as in `Core/ModelTheory/StructureFamily.lean`; atoms take variables only, as
  in the paper, so function symbols go unused.
* Bounds fill the presupposition slot of `PartialProp`. The paper leaves open whether bounds are
  presuppositions, and its update keeps the points where a sentence is true and satt instead of
  requiring the context to admit the sentence; `not_admits_indef_atom₁` shows why.
* `BoundEntails` and `LogicallyEntails` are relative to a model `I`. The paper's relations
  quantify over all intended models, which is what the general theorems state; the refutations of
  footnote 20 exhibit one model.
* Local contexts are the asymmetric ones the paper spells out; the symmetric alternative it
  mentions is not formalized.

## TODO

* The generalized quantifiers of the paper's §5.8, whose domain variables take sets of
  individual–assignment pairs as values.
* The cross-world witness bound for modal subordination sketched in the conclusion.

## References

* [mandelkern-2022]
* [heim-1982]
* [karttunen-1976]
* [schlenker-2009]
* [stalnaker-1978]
* [von-fintel-1999]
-/

@[expose] public section

open FirstOrder Presupposition

namespace Mandelkern2022

/-- The language of the paper (p. 1101): atoms over variables, the pronoun restrictor `⊤x`,
the classical connectives, and the two-place indefinite and definite. -/
inductive Formula (L : Language) (V : Type*) where
  /-- The atom `A(x₁, …, xₙ)`. -/
  | atom {n : ℕ} (R : L.Relations n) (xs : Fin n → V)
  /-- The tautological restrictor `⊤x` of a pronoun. -/
  | top (x : V)
  /-- Conjunction `p & q`. -/
  | conj (p q : Formula L V)
  /-- Disjunction `p ∨ q`. -/
  | disj (p q : Formula L V)
  /-- Negation `¬p`. -/
  | neg (p : Formula L V)
  /-- The indefinite `ɜx(p, q)`, *some p is q*. -/
  | indef (x : V) (p q : Formula L V)
  /-- The definite `ιx(p, q)`, *the p is q*. -/
  | iota (x : V) (p q : Formula L V)

namespace Formula

variable {L : Language} {V W E : Type*} [DecidableEq V] (I : W → L.Structure E)

/-- Truth at an assignment and a world (p. 1101 and p. 1114). An atom is true when its variables
are valued and their values stand in the relation; `⊤x` is true when `x` is valued. -/
def Realize : Formula L V → PartialAssign V E → W → Prop
  | atom R xs, g, w => ∃ es : Fin _ → E, (∀ i, g (xs i) = es i) ∧ (I w).RelMap R es
  | top x, g, _ => g x ≠ ⊥
  | conj p q, g, w => p.Realize g w ∧ q.Realize g w
  | disj p q, g, w => p.Realize g w ∨ q.Realize g w
  | neg p, g, w => ¬ p.Realize g w
  | indef x p q, g, w => ∃ a, p.Realize (g.update x a) w ∧ q.Realize (g.update x a) w
  | iota _ p q, g, w => p.Realize g w ∧ q.Realize g w

/-- The bounds of a formula are satisfied (*satt*) at a context, an assignment and a world
(p. 1114). The set `{i ∈ c | p true and satt at c, i}` is the local context `cᵖ`, which `update`
names below. -/
def Satt : Formula L V → Set (PartialAssign V E × W) → PartialAssign V E → W → Prop
  | atom _ xs, _, g, _ => ∀ i, g (xs i) ≠ ⊥
  | top x, _, g, _ => g x ≠ ⊥
  | conj p q, c, g, w =>
      p.Satt c g w ∧ q.Satt {i ∈ c | p.Realize I i.1 i.2 ∧ p.Satt c i.1 i.2} g w
  | disj p q, c, g, w =>
      p.Satt c g w ∧ q.Satt {i ∈ c | ¬ p.Realize I i.1 i.2 ∧ p.Satt c i.1 i.2} g w
  | neg p, c, g, w => p.Satt c g w
  | indef x p q, c, g, w =>
      (∃ g', p.Satt c g' w ∧ q.Satt {i ∈ c | p.Realize I i.1 i.2 ∧ p.Satt c i.1 i.2} g' w) ∧
      ((∃ a, p.Realize I (g.update x a) w ∧ q.Realize I (g.update x a) w) →
        (p.Realize I g w ∧ q.Realize I g w) ∧
          p.Satt c g w ∧ q.Satt {i ∈ c | p.Realize I i.1 i.2 ∧ p.Satt c i.1 i.2} g w)
  | iota _ p q, c, g, w =>
      (∀ i ∈ c, p.Realize I i.1 i.2 ∧ p.Satt c i.1 i.2) ∧
      (p.Realize I g w → q.Satt {i ∈ c | p.Realize I i.1 i.2 ∧ p.Satt c i.1 i.2} g w)

/-- The two dimensions of a formula's meaning at a context, bounds and truth. -/
def toPartialProp (c : Set (PartialAssign V E × W)) (p : Formula L V) :
    PartialProp (PartialAssign V E × W) where
  presup i := p.Satt I c i.1 i.2
  assertion i := p.Realize I i.1 i.2

/-- Updating `c` with `p` keeps the points of `c` at which `p` is true and satt (p. 1103). This
set is also the local context `cᵖ` of the projection clauses. -/
def update (c : Set (PartialAssign V E × W)) (p : Formula L V) : Set (PartialAssign V E × W) :=
  {i ∈ c | p.Realize I i.1 i.2 ∧ p.Satt I c i.1 i.2}

variable {I} {c : Set (PartialAssign V E × W)} {g : PartialAssign V E} {w : W}
  {p q : Formula L V} {x : V}

/-! ### Truth and bounds -/

@[simp] theorem realize_atom {n : ℕ} {R : L.Relations n} {xs : Fin n → V} :
    (atom R xs).Realize I g w ↔ ∃ es : Fin n → E, (∀ i, g (xs i) = es i) ∧ (I w).RelMap R es :=
  Iff.rfl

@[simp] theorem realize_top : (top x : Formula L V).Realize I g w ↔ g x ≠ ⊥ := Iff.rfl

@[simp] theorem realize_conj : (conj p q).Realize I g w ↔ p.Realize I g w ∧ q.Realize I g w :=
  Iff.rfl

@[simp] theorem realize_disj : (disj p q).Realize I g w ↔ p.Realize I g w ∨ q.Realize I g w :=
  Iff.rfl

@[simp] theorem realize_neg : (neg p).Realize I g w ↔ ¬ p.Realize I g w := Iff.rfl

@[simp] theorem realize_indef :
    (indef x p q).Realize I g w ↔
      ∃ a, p.Realize I (g.update x a) w ∧ q.Realize I (g.update x a) w :=
  Iff.rfl

@[simp] theorem realize_iota : (iota x p q).Realize I g w ↔ p.Realize I g w ∧ q.Realize I g w :=
  Iff.rfl

@[simp] theorem mem_update {i : PartialAssign V E × W} :
    i ∈ update I c p ↔ i ∈ c ∧ p.Realize I i.1 i.2 ∧ p.Satt I c i.1 i.2 :=
  Iff.rfl

theorem update_subset : update I c p ⊆ c := Set.sep_subset _ _

@[simp] theorem mem_truthSet_toPartialProp {i : PartialAssign V E × W} :
    i ∈ (p.toPartialProp I c).truthSet ↔ p.Satt I c i.1 i.2 ∧ p.Realize I i.1 i.2 :=
  Iff.rfl

/-- Updating keeps the points of the context in the truth set of the meaning there. -/
theorem update_eq_inter_truthSet : update I c p = c ∩ (p.toPartialProp I c).truthSet :=
  Set.ext fun _ ↦ ⟨fun ⟨hc, hr, hs⟩ ↦ ⟨hc, hs, hr⟩, fun ⟨hc, hs, hr⟩ ↦ ⟨hc, hr, hs⟩⟩

@[simp] theorem satt_atom {n : ℕ} {R : L.Relations n} {xs : Fin n → V} :
    (atom R xs).Satt I c g w ↔ ∀ i, g (xs i) ≠ ⊥ :=
  Iff.rfl

@[simp] theorem satt_top : (top x : Formula L V).Satt I c g w ↔ g x ≠ ⊥ := Iff.rfl

theorem satt_conj :
    (conj p q).Satt I c g w ↔ p.Satt I c g w ∧ q.Satt I (update I c p) g w :=
  Iff.rfl

/-- The right disjunct is satt at the local context `c¬ᵖ`. -/
theorem satt_disj :
    (disj p q).Satt I c g w ↔ p.Satt I c g w ∧ q.Satt I (update I c (neg p)) g w :=
  Iff.rfl

@[simp] theorem satt_neg : (neg p).Satt I c g w ↔ p.Satt I c g w := Iff.rfl

/-- The witness bound and the projection of an indefinite (p. 1114): its body is satt at some
assignment, and if the indefinite is true its body is true and satt at the given one. -/
theorem satt_indef :
    (indef x p q).Satt I c g w ↔ (∃ g', (conj p q).Satt I c g' w) ∧
      ((indef x p q).Realize I g w → (conj p q).Realize I g w ∧ (conj p q).Satt I c g w) :=
  Iff.rfl

/-- The familiarity bound and the projection of a definite (p. 1114): updating with the
restrictor leaves the context unchanged, and the scope is satt at `cᵖ` if the restrictor is
true. -/
theorem satt_iota :
    (iota x p q).Satt I c g w ↔
      update I c p = c ∧ (p.Realize I g w → q.Satt I (update I c p) g w) :=
  and_congr_left' Set.sep_eq_self_iff_mem_true.symm

theorem realize_indef_of_ne_bot (hx : g x ≠ ⊥) (hp : p.Realize I g w) (hq : q.Realize I g w) :
    (indef x p q).Realize I g w := by
  obtain ⟨a, ha⟩ := Flat.ne_bot_iff_exists.1 hx
  exact ⟨a, by rwa [PartialAssign.update_self ha], by rwa [PartialAssign.update_self ha]⟩

/-- The witness bound at work: a true indefinite whose bounds hold has a true body. -/
theorem realize_conj_of_satt_indef (hs : (indef x p q).Satt I c g w)
    (hr : (indef x p q).Realize I g w) : p.Realize I g w ∧ q.Realize I g w :=
  (hs.2 hr).1

/-! ### The calculus of truth sets

The points at which a formula is true and satt at a context, `(p.toPartialProp I c).truthSet`,
decompose along the connectives; updating a context intersects it with this set
(`update_eq_inter_truthSet`). -/

/-- A conjunction is true and satt where its left conjunct is, at the context, and its right
conjunct is, at the left conjunct's local context. -/
theorem truthSet_conj : ((conj p q).toPartialProp I c).truthSet =
    (p.toPartialProp I c).truthSet ∩ (q.toPartialProp I (update I c p)).truthSet := by
  ext
  simp only [mem_truthSet_toPartialProp, satt_conj, realize_conj, Set.mem_inter_iff]
  tauto

/-- An indefinite is true and satt where its body is and the indefinite is true. -/
theorem truthSet_indef : ((indef x p q).toPartialProp I c).truthSet =
    {i ∈ ((conj p q).toPartialProp I c).truthSet | (indef x p q).Realize I i.1 i.2} := by
  ext ⟨g, w⟩
  exact ⟨fun ⟨hs, hr⟩ ↦ ⟨⟨(hs.2 hr).2, (hs.2 hr).1⟩, hr⟩,
    fun ⟨⟨hs, hr⟩, hi⟩ ↦ ⟨⟨⟨g, hs⟩, fun _ ↦ ⟨hr, hs⟩⟩, hi⟩⟩

/-- An indefinite whose restrictor values its variable is true and satt where its body is. -/
theorem truthSet_indef_of_ne_bot (hp : ∀ g w, p.Realize I g w → g x ≠ ⊥) :
    ((indef x p q).toPartialProp I c).truthSet = ((conj p q).toPartialProp I c).truthSet := by
  rw [truthSet_indef]
  exact Set.sep_eq_self_iff_mem_true.2 fun _ hi ↦
    realize_indef_of_ne_bot (hp _ _ hi.2.1) hi.2.1 hi.2.2

/-- A definite whose restrictor is idle on the context is true and satt where its restrictor is
true and its scope true and satt. -/
theorem truthSet_iota_of_update_eq (h : update I c p = c) :
    ((iota x p q).toPartialProp I c).truthSet =
      {i | p.Realize I i.1 i.2} ∩ (q.toPartialProp I c).truthSet := by
  ext
  simp only [mem_truthSet_toPartialProp, satt_iota, h, realize_iota, Set.mem_inter_iff,
    Set.mem_ofPred_eq, true_and]
  tauto

/-- A definite whose restrictor is not idle on the context is satt nowhere: the familiarity bound
holds at all points of a context or at none (p. 1104). -/
theorem truthSet_iota_eq_empty (h : update I c p ≠ c) :
    ((iota x p q).toPartialProp I c).truthSet = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hi ↦ h ((satt_iota (x := x) (q := q)).1 hi.1).1

/-- Double negation changes neither dimension of a meaning (p. 1109). -/
@[simp] theorem toPartialProp_neg_neg : (neg (neg p)).toPartialProp I c = p.toPartialProp I c := by
  ext i <;> simp [toPartialProp]

/-! ### The update calculus -/

/-- A conjunction updates in sequence, the reason the paper's points carry over to sequences
(fn. 20). -/
theorem update_conj : update I c (conj p q) = update I (update I c p) q := by
  rw [update_eq_inter_truthSet, truthSet_conj, ← Set.inter_assoc, ← update_eq_inter_truthSet,
    ← update_eq_inter_truthSet]

/-- An indefinite updates as its body does, at the points where it is true. -/
theorem update_indef :
    update I c (indef x p q) = {i ∈ update I c (conj p q) | (indef x p q).Realize I i.1 i.2} := by
  rw [update_eq_inter_truthSet, truthSet_indef, update_eq_inter_truthSet]
  exact Set.ext fun _ ↦ and_assoc.symm

/-- An indefinite whose restrictor values its variable updates as its body. -/
theorem update_indef_of_ne_bot (hp : ∀ g w, p.Realize I g w → g x ≠ ⊥) :
    update I c (indef x p q) = update I c (conj p q) := by
  rw [update_eq_inter_truthSet, truthSet_indef_of_ne_bot hp, ← update_eq_inter_truthSet]

/-- A definite whose restrictor is idle on the context updates as the conjunction of its
restrictor and scope. -/
theorem update_iota_of_update_eq (h : update I c p = c) :
    update I c (iota x p q) = update I c (conj p q) := by
  have hp : c ⊆ {i | p.Realize I i.1 i.2} := fun i hi ↦ (h.ge hi).2.1
  rw [update_conj, h, update_eq_inter_truthSet, truthSet_iota_of_update_eq h,
    ← Set.inter_assoc, Set.inter_eq_left.2 hp, ← update_eq_inter_truthSet]

/-- A definite whose restrictor is not idle on the context empties it (p. 1104). -/
theorem update_iota_eq_empty (h : update I c p ≠ c) : update I c (iota x p q) = ∅ := by
  rw [update_eq_inter_truthSet, truthSet_iota_eq_empty h, Set.inter_empty]

/-- A pronoun whose variable is unvalued at some point of the context empties it. -/
theorem update_iota_top_eq_empty (h : ∃ i ∈ c, i.1 x = ⊥) :
    update I c (iota x (top x) q) = ∅ := by
  obtain ⟨i, hi, hx⟩ := h
  exact update_iota_eq_empty fun he ↦ (he.ge hi).2.1 hx

@[simp] theorem update_neg_neg : update I c (neg (neg p)) = update I c p := by
  rw [update_eq_inter_truthSet, toPartialProp_neg_neg, ← update_eq_inter_truthSet]

/-! ### One-place atoms -/

/-- The one-place atom `Rx`. -/
def atom₁ (R : L.Relations 1) (x : V) : Formula L V := atom R ![x]

/-- The extension `A_w` of a one-place relation symbol at a world (p. 1103). -/
def extension (I : W → L.Structure E) (R : L.Relations 1) (w : W) : Set E :=
  {a | (I w).RelMap R ![a]}

/-- The points at which `x` has a value in `S`, as given at the point's world. -/
def valuedIn (x : V) (S : W → Set E) : Set (PartialAssign V E × W) :=
  {i | ∃ a ∈ S i.2, i.1 x = a}

variable {S T : W → Set E} {R : L.Relations 1}

@[simp] theorem mem_extension {a : E} : a ∈ extension I R w ↔ (I w).RelMap R ![a] := Iff.rfl

omit [DecidableEq V] in
@[simp] theorem mem_valuedIn {i : PartialAssign V E × W} :
    i ∈ valuedIn x S ↔ ∃ a ∈ S i.2, i.1 x = a :=
  Iff.rfl

omit [DecidableEq V] in
theorem valuedIn_inter_valuedIn : valuedIn x S ∩ valuedIn x T = valuedIn x (S ⊓ T) := by
  ext ⟨g, w⟩
  simp only [Set.mem_inter_iff, mem_valuedIn, Pi.inf_apply, Set.inf_eq_inter]
  constructor
  · rintro ⟨⟨a, hS, ha⟩, b, hT, hb⟩
    obtain rfl : b = a := Flat.coe_injective (hb.symm.trans ha)
    exact ⟨b, ⟨hS, hT⟩, ha⟩
  · rintro ⟨a, ⟨hS, hT⟩, ha⟩
    exact ⟨⟨a, hS, ha⟩, a, hT, ha⟩

omit [DecidableEq V] in
theorem valuedIn_mono (h : S ≤ T) : valuedIn x S ⊆ valuedIn x T :=
  fun _ ⟨a, ha, hx⟩ ↦ ⟨a, h _ ha, hx⟩

omit [DecidableEq V] in
theorem ne_bot_of_mem_valuedIn {i : PartialAssign V E × W} (h : i ∈ valuedIn x S) : i.1 x ≠ ⊥ :=
  Flat.ne_bot_iff_exists.2 (h.imp fun _ ↦ And.right)

@[simp] theorem realize_atom₁ : (atom₁ R x).Realize I g w ↔ ∃ a ∈ extension I R w, g x = a := by
  refine ⟨fun ⟨es, h, hR⟩ ↦ ⟨es 0, ?_, h 0⟩, fun ⟨a, ha, hx⟩ ↦ ⟨![a], fun i ↦ ?_, ha⟩⟩
  · rw [mem_extension]; convert hR; ext i; fin_cases i; rfl
  · fin_cases i; exact hx

@[simp] theorem satt_atom₁ : (atom₁ R x).Satt I c g w ↔ g x ≠ ⊥ := by
  simp [atom₁]

theorem ne_bot_of_realize_atom₁ (h : (atom₁ R x).Realize I g w) : g x ≠ ⊥ :=
  ne_bot_of_mem_valuedIn (S := extension I R) (i := (g, w)) (realize_atom₁.1 h)

theorem setOf_realize_atom₁ : {i | (atom₁ R x).Realize I i.1 i.2} = valuedIn x (extension I R) :=
  Set.ext fun _ ↦ realize_atom₁

theorem truthSet_atom₁ : ((atom₁ R x).toPartialProp I c).truthSet = valuedIn x (extension I R) := by
  ext
  rw [mem_truthSet_toPartialProp, satt_atom₁, realize_atom₁]
  exact ⟨And.right, fun h ↦ ⟨ne_bot_of_mem_valuedIn h, h⟩⟩

theorem truthSet_top : ((top x : Formula L V).toPartialProp I c).truthSet = {i | i.1 x ≠ ⊥} :=
  Set.ext fun _ ↦ and_self_iff

theorem update_atom₁ : update I c (atom₁ R x) = c ∩ valuedIn x (extension I R) := by
  rw [update_eq_inter_truthSet, truthSet_atom₁]

/-- An atom true throughout a context is idle on it. -/
theorem update_atom₁_of_subset (h : c ⊆ valuedIn x (extension I R)) :
    update I c (atom₁ R x) = c := by
  rw [update_atom₁, Set.inter_eq_left.2 h]

/-- A pronoun restrictor is idle on a context that values its variable throughout. -/
theorem update_top_of_subset (h : c ⊆ valuedIn x S) : update I c (top x) = c := by
  have hx : c ⊆ {i | i.1 x ≠ ⊥} := fun i hi ↦ ne_bot_of_mem_valuedIn (h hi)
  rw [update_eq_inter_truthSet, truthSet_top, Set.inter_eq_left.2 hx]

end Formula

open Formula

variable {L : Language} {V W E : Type*} [DecidableEq V] {I : W → L.Structure E}
  {c : Set (PartialAssign V E × W)} {g : PartialAssign V E} {w : W} {p q : Formula L V} {x : V}

/-! ### Indefinites open files (§5.4) -/

section Updating

variable (F G H : L.Relations 1)

theorem truthSet_indef_atom₁ :
    ((indef x (atom₁ F x) (atom₁ G x)).toPartialProp I c).truthSet =
      valuedIn x (extension I F ⊓ extension I G) := by
  rw [truthSet_indef_of_ne_bot fun _ _ ↦ ne_bot_of_realize_atom₁, truthSet_conj, truthSet_atom₁,
    truthSet_atom₁, valuedIn_inter_valuedIn]

/-- Updating with `ɜx(Fx, Gx)` keeps the points whose `x` is an `F` and a `G` (p. 1103). -/
theorem update_indef_atom₁ :
    update I c (indef x (atom₁ F x) (atom₁ G x)) =
      c ∩ valuedIn x (extension I F ⊓ extension I G) := by
  rw [update_eq_inter_truthSet, truthSet_indef_atom₁]

/-- The null context does not admit `ɜx(Fx, Gx)` in Stalnaker's sense once some world has an
`F` that is `G`: the point of the empty assignment there violates the witness bound. This is why
updating keeps the points where a sentence is satt instead of requiring all of them to be
(p. 1103). -/
theorem not_admits_indef_atom₁ (h : ∃ w, (extension I F w ∩ extension I G w).Nonempty) :
    ¬ (toPartialProp I Set.univ (indef x (atom₁ F x) (atom₁ G x))).Admits Set.univ := by
  obtain ⟨w, a, hF, hG⟩ := h
  intro hadm
  have hs : (indef x (atom₁ F x) (atom₁ G x)).Satt I Set.univ ⊥ w := hadm (Set.mem_univ (⊥, w))
  have hr : (indef x (atom₁ F x) (atom₁ G x)).Realize I ⊥ w :=
    ⟨a, realize_atom₁.2 ⟨a, hF, by simp⟩, realize_atom₁.2 ⟨a, hG, by simp⟩⟩
  exact ne_bot_of_realize_atom₁ (realize_conj_of_satt_indef hs hr).1 rfl

/-- After `ɜx(Fx, Gx)`, the definite `ιx(Fx, Hx)` is familiar, and true and satt where `x` is an
`F` and an `H` (p. 1104). -/
theorem truthSet_iota_after_indef_atom₁ :
    ((iota x (atom₁ F x) (atom₁ H x)).toPartialProp I
        (update I c (indef x (atom₁ F x) (atom₁ G x)))).truthSet =
      valuedIn x (extension I F ⊓ extension I H) := by
  have hc : update I c (indef x (atom₁ F x) (atom₁ G x)) ⊆ valuedIn x (extension I F) := by
    rw [update_indef_atom₁]
    exact fun i hi ↦ valuedIn_mono inf_le_left hi.2
  rw [truthSet_iota_of_update_eq (update_atom₁_of_subset hc), setOf_realize_atom₁,
    truthSet_atom₁, valuedIn_inter_valuedIn]

/-- After `ɜx(Fx, Gx)`, the pronoun `ιx(⊤x, Hx)` is familiar, and true and satt where `x` is an
`H` (p. 1104). -/
theorem truthSet_iota_top_after_indef_atom₁ :
    ((iota x (top x) (atom₁ H x)).toPartialProp I
        (update I c (indef x (atom₁ F x) (atom₁ G x)))).truthSet =
      valuedIn x (extension I H) := by
  have hc : update I c (indef x (atom₁ F x) (atom₁ G x)) ⊆ valuedIn x (extension I F) := by
    rw [update_indef_atom₁]
    exact fun i hi ↦ valuedIn_mono inf_le_left hi.2
  rw [truthSet_iota_of_update_eq (update_top_of_subset hc), truthSet_atom₁]
  exact Set.inter_eq_right.2 fun _ hi ↦ ne_bot_of_mem_valuedIn hi

/-- *There is a cat. The cat is tabby.* keeps the points whose `x` is a cat that exists and is
tabby (p. 1104). -/
theorem update_indef_then_the :
    update I (update I c (indef x (atom₁ F x) (atom₁ G x))) (iota x (atom₁ F x) (atom₁ H x)) =
      c ∩ valuedIn x (extension I F ⊓ extension I G ⊓ extension I H) := by
  rw [update_eq_inter_truthSet, truthSet_iota_after_indef_atom₁, update_indef_atom₁,
    Set.inter_assoc, valuedIn_inter_valuedIn, ← inf_inf_distrib_left, ← inf_assoc]

/-- *There is a cat. It is tabby.* keeps the same points (p. 1104). -/
theorem update_indef_then_it :
    update I (update I c (indef x (atom₁ F x) (atom₁ G x))) (iota x (top x) (atom₁ H x)) =
      c ∩ valuedIn x (extension I F ⊓ extension I G ⊓ extension I H) := by
  rw [update_eq_inter_truthSet, truthSet_iota_top_after_indef_atom₁, update_indef_atom₁,
    Set.inter_assoc, valuedIn_inter_valuedIn]

/-! ### Negated indefinites (§5.5) -/

/-- A negated indefinite is true and satt where the negated existential is true
(pp. 1106–1107): at the worlds with no `F` that is `G`. -/
theorem truthSet_neg_indef_atom₁ [Nonempty E] :
    ((neg (indef x (atom₁ F x) (atom₁ G x))).toPartialProp I c).truthSet =
      {i | extension I F i.2 ∩ extension I G i.2 = ∅} := by
  have key : ∀ g w, (indef x (atom₁ F x) (atom₁ G x)).Realize I g w ↔
      (extension I F w ∩ extension I G w).Nonempty := fun g w ↦ by
    simp [Set.Nonempty]
  obtain ⟨e⟩ := ‹Nonempty E›
  ext ⟨g, w⟩
  simp only [mem_truthSet_toPartialProp, realize_neg, satt_neg, Set.mem_ofPred_eq, key,
    Set.not_nonempty_iff_eq_empty]
  refine ⟨fun ⟨_, hr⟩ ↦ hr, fun hr ↦ ⟨⟨⟨fun _ ↦ e, ?_⟩, fun h ↦ ?_⟩, hr⟩⟩
  · simp
  · exact absurd ((key g w).1 h) (Set.not_nonempty_iff_eq_empty.2 hr)

/-- (19) *We don't have a cat. # She is a tabby.* Updating the null context with a negated
indefinite and then a pronoun on its variable leaves no point, once some world has no `F` that is
`G` (p. 1106). -/
theorem update_null_neg_indef_then_it (h : ∃ w, extension I F w ∩ extension I G w = ∅) :
    update I (update I Set.univ (neg (indef x (atom₁ F x) (atom₁ G x))))
      (iota x (top x) (atom₁ H x)) = ∅ := by
  cases isEmpty_or_nonempty E
  · refine Set.subset_eq_empty (update_subset.trans fun i hi ↦ ?_) rfl
    obtain ⟨⟨g', hg', -⟩, -⟩ := hi.2.2
    obtain ⟨a, -⟩ := Flat.ne_bot_iff_exists.1 (satt_atom₁.1 hg')
    exact isEmptyElim a
  obtain ⟨w, hw⟩ := h
  refine update_iota_top_eq_empty ⟨(⊥, w), ?_, rfl⟩
  rw [update_eq_inter_truthSet, truthSet_neg_indef_atom₁]
  exact ⟨Set.mem_univ _, hw⟩

end Updating

/-! ### Bound entailment (§5.6) -/

section Entailment

variable (I) in
/-- Bound entailment (p. 1108): at every context `p` Strawson-entails `q`, the bounds in the role
of presuppositions; wherever both are satt and `p` is true, `q` is true. -/
def BoundEntails (p q : Formula L V) : Prop :=
  ∀ c, (p.toPartialProp I c).strawsonEntails (q.toPartialProp I c)

variable (I) in
/-- Bound equivalence: bound entailment in both directions. -/
def BoundEquiv (p q : Formula L V) : Prop := AntisymmRel (BoundEntails I) p q

variable (I) in
/-- Logical entailment (p. 1108): wherever `p` is true, `q` is. -/
def LogicallyEntails (p q : Formula L V) : Prop := ∀ g w, p.Realize I g w → q.Realize I g w

@[refl] protected theorem BoundEntails.refl (p : Formula L V) : BoundEntails I p p :=
  fun _ _ _ _ ↦ id

instance : Std.Refl (BoundEntails (V := V) I) := ⟨BoundEntails.refl⟩

/-- The bounded logic extends the logic (p. 1109). -/
theorem LogicallyEntails.boundEntails (h : LogicallyEntails I p q) : BoundEntails I p q :=
  fun _ i _ _ ↦ h i.1 i.2

end Entailment

/-! ### Open scope (§5.6) -/

section OpenScope

/-- (20-a) `ɜx(F, G & H)`, *some F is G and H*. -/
def ex20a (x : V) (F G H : Formula L V) : Formula L V := indef x F (conj G H)

/-- (20-b) `ɜx(F, G) & ιx(F, H)`, *some F is G, and the F is H*. -/
def ex20b (x : V) (F G H : Formula L V) : Formula L V := conj (indef x F G) (iota x F H)

/-- (20-c) `ɜx(F, G) & ιx(⊤x, H)`, *some F is G, and it is H*. -/
def ex20c (x : V) (F G H : Formula L V) : Formula L V := conj (indef x F G) (iota x (top x) H)

variable {F G H : Formula L V}

theorem boundEntails_ex20a_ex20b : BoundEntails I (ex20a x F G H) (ex20b x F G H) := by
  rintro c ⟨g, w⟩ hs - hr
  obtain ⟨hF, -, hH⟩ := realize_conj_of_satt_indef hs hr
  obtain ⟨a, haF, haG, -⟩ := hr
  exact ⟨⟨a, haF, haG⟩, hF, hH⟩

theorem boundEntails_ex20c_ex20b : BoundEntails I (ex20c x F G H) (ex20b x F G H) := by
  rintro c ⟨g, w⟩ hs - ⟨hl, -, hH⟩
  exact ⟨hl, (realize_conj_of_satt_indef hs.1 hl).1, hH⟩

theorem boundEntails_ex20c_ex20a : BoundEntails I (ex20c x F G H) (ex20a x F G H) := by
  rintro c ⟨g, w⟩ hs - ⟨hl, hx, hH⟩
  obtain ⟨hF, hG⟩ := realize_conj_of_satt_indef hs.1 hl
  exact realize_indef_of_ne_bot hx hF ⟨hG, hH⟩

theorem boundEntails_ex20b_ex20a (hF : ∀ g w, F.Realize I g w → g x ≠ ⊥) :
    BoundEntails I (ex20b x F G H) (ex20a x F G H) := by
  rintro c ⟨g, w⟩ hs - ⟨hl, hFg, hH⟩
  exact realize_indef_of_ne_bot (hF g w hFg) hFg ⟨(realize_conj_of_satt_indef hs.1 hl).2, hH⟩

theorem boundEntails_ex20b_ex20c (hF : ∀ g w, F.Realize I g w → g x ≠ ⊥) :
    BoundEntails I (ex20b x F G H) (ex20c x F G H) := by
  rintro c ⟨g, w⟩ - - ⟨hl, hFg, hH⟩
  exact ⟨hl, hF g w hFg, hH⟩

theorem boundEntails_ex20a_ex20c (hF : ∀ g w, F.Realize I g w → g x ≠ ⊥) :
    BoundEntails I (ex20a x F G H) (ex20c x F G H) := by
  rintro c ⟨g, w⟩ hs - hr
  obtain ⟨hFg, -, hH⟩ := realize_conj_of_satt_indef hs hr
  obtain ⟨a, haF, haG, -⟩ := hr
  exact ⟨⟨a, haF, haG⟩, hF g w hFg, hH⟩

/-- (20-a) and (20-b) are bound-equivalent when the restrictor's truth values `x` (p. 1108). -/
theorem boundEquiv_ex20a_ex20b (hF : ∀ g w, F.Realize I g w → g x ≠ ⊥) :
    BoundEquiv I (ex20a x F G H) (ex20b x F G H) :=
  ⟨boundEntails_ex20a_ex20b, boundEntails_ex20b_ex20a hF⟩

/-- (20-b) and (20-c) are bound-equivalent when the restrictor's truth values `x` (p. 1108). -/
theorem boundEquiv_ex20b_ex20c (hF : ∀ g w, F.Realize I g w → g x ≠ ⊥) :
    BoundEquiv I (ex20b x F G H) (ex20c x F G H) :=
  ⟨boundEntails_ex20b_ex20c hF, boundEntails_ex20c_ex20b⟩

/-- (20-a) and (20-c) are bound-equivalent when the restrictor's truth values `x` (p. 1108). -/
theorem boundEquiv_ex20a_ex20c (hF : ∀ g w, F.Realize I g w → g x ≠ ⊥) :
    BoundEquiv I (ex20a x F G H) (ex20c x F G H) :=
  ⟨boundEntails_ex20a_ex20c hF, boundEntails_ex20c_ex20a⟩

/-- At a point of its context, (20-a) bound-entails (20-c) for any formulae: the pronoun's
familiarity bound values `x` throughout the local context of the indefinite, which contains the
point. -/
theorem realize_ex20c_of_realize_ex20a (hc : (g, w) ∈ c) (hs : (ex20a x F G H).Satt I c g w)
    (hs' : (ex20c x F G H).Satt I c g w) (hr : (ex20a x F G H).Realize I g w) :
    (ex20c x F G H).Realize I g w := by
  obtain ⟨hFg, hG, hH⟩ := realize_conj_of_satt_indef hs hr
  obtain ⟨a, haF, haG, haH⟩ := hr
  obtain ⟨⟨g', hg'F, hg'G, -⟩, hw⟩ := hs
  have hmem : (g, w) ∈ update I c (indef x F G) :=
    ⟨hc, ⟨a, haF, haG⟩, ⟨g', hg'F, hg'G⟩, fun _ ↦
      ⟨⟨hFg, hG⟩, (hw ⟨a, haF, haG, haH⟩).2.1, (hw ⟨a, haF, haG, haH⟩).2.2.1⟩⟩
  exact ⟨⟨a, haF, haG⟩, ((satt_iota.1 hs'.2).1.ge hmem).2.1, hH⟩

/-- At a point of its context, (20-b) bound-entails (20-c) for any formulae. -/
theorem realize_ex20c_of_realize_ex20b (hc : (g, w) ∈ c) (hs : (ex20b x F G H).Satt I c g w)
    (hs' : (ex20c x F G H).Satt I c g w) (hr : (ex20b x F G H).Realize I g w) :
    (ex20c x F G H).Realize I g w :=
  ⟨hr.1, ((satt_iota.1 hs'.2).1.ge ⟨hc, hr.1, hs.1⟩).2.1, hr.2.2⟩

variable (F G H : L.Relations 1)

/-- (20-a) is true and satt exactly where `x` is an `F`, a `G` and an `H` (p. 1108). -/
theorem truthSet_ex20a :
    ((ex20a x (atom₁ F x) (atom₁ G x) (atom₁ H x)).toPartialProp I c).truthSet =
      valuedIn x (extension I F ⊓ extension I G ⊓ extension I H) := by
  rw [ex20a, truthSet_indef_of_ne_bot fun _ _ ↦ ne_bot_of_realize_atom₁, truthSet_conj,
    truthSet_conj, truthSet_atom₁, truthSet_atom₁, truthSet_atom₁, ← Set.inter_assoc,
    valuedIn_inter_valuedIn, valuedIn_inter_valuedIn]

/-- So is (20-b) (p. 1108). -/
theorem truthSet_ex20b :
    ((ex20b x (atom₁ F x) (atom₁ G x) (atom₁ H x)).toPartialProp I c).truthSet =
      valuedIn x (extension I F ⊓ extension I G ⊓ extension I H) := by
  rw [ex20b, truthSet_conj, truthSet_indef_atom₁, truthSet_iota_after_indef_atom₁,
    valuedIn_inter_valuedIn, ← inf_inf_distrib_left, ← inf_assoc]

/-- So is (20-c) (p. 1108). Hence, as footnote 23 has it, any one of (20-a)–(20-c) is satt and
true where all three are, and updating with any of them has the same effect. -/
theorem truthSet_ex20c :
    ((ex20c x (atom₁ F x) (atom₁ G x) (atom₁ H x)).toPartialProp I c).truthSet =
      valuedIn x (extension I F ⊓ extension I G ⊓ extension I H) := by
  rw [ex20c, truthSet_conj, truthSet_indef_atom₁, truthSet_iota_top_after_indef_atom₁,
    valuedIn_inter_valuedIn]

/-- The formulations of (20) are not logically equivalent (p. 1108): at a point whose world has
an `F` that is `G` and `H` but whose `x` is not an `H`, (20-a) is true and (20-b) is false. -/
theorem realize_ex20a_and_not_realize_ex20b
    (h : (extension I F w ∩ extension I G w ∩ extension I H w).Nonempty) {b : E}
    (hb : g x = b) (hH : b ∉ extension I H w) :
    (ex20a x (atom₁ F x) (atom₁ G x) (atom₁ H x)).Realize I g w ∧
      ¬ (ex20b x (atom₁ F x) (atom₁ G x) (atom₁ H x)).Realize I g w := by
  obtain ⟨a, ⟨hF, hG⟩, haH⟩ := h
  refine ⟨⟨a, by simpa using hF, by simpa using hG, by simpa using haH⟩, fun ⟨_, _, h⟩ ↦ ?_⟩
  obtain ⟨c, hc, hgc⟩ := realize_atom₁.1 h
  exact hH (Flat.coe_injective (hb.symm.trans hgc) ▸ hc)

end OpenScope

/-! ### Classicality (§5.7) -/

section Classicality

/-- `¬¬p` and `p` are logically, hence bound-, equivalent (p. 1109). -/
theorem boundEquiv_neg_neg : BoundEquiv I (neg (neg p)) p :=
  ⟨LogicallyEntails.boundEntails fun _ _ ↦ by simp,
    LogicallyEntails.boundEntails fun _ _ ↦ by simp⟩

/-- `¬p ∨ q` and `¬p ∨ (p & q)` are logically, hence bound-, equivalent (p. 1109). -/
theorem boundEquiv_disj_neg_conj : BoundEquiv I (disj (neg p) q) (disj (neg p) (conj p q)) :=
  ⟨LogicallyEntails.boundEntails fun _ _ ↦ by simp; tauto,
    LogicallyEntails.boundEntails fun _ _ ↦ by simp; tauto⟩

variable (F G H : L.Relations 1)

/-- A doubly negated indefinite licenses a subsequent definite as the indefinite does: *It's not
the case that Susie doesn't have a child. The child is at boarding school.* (p. 1109). -/
theorem update_neg_neg_indef_then_the :
    update I (update I c (neg (neg (indef x (atom₁ F x) (atom₁ G x)))))
        (iota x (atom₁ F x) (atom₁ H x)) =
      c ∩ valuedIn x (extension I F ⊓ extension I G ⊓ extension I H) := by
  rw [update_neg_neg, update_indef_then_the]

/-- The bathroom disjunction *Either Susie doesn't have a child, or the child is at boarding
school* is true and satt exactly where Susie is childless or `x` is Susie's child and at
boarding school (p. 1109). -/
theorem truthSet_bathroom [Nonempty E] :
    ((disj (neg (indef x (atom₁ F x) (atom₁ G x))) (iota x (atom₁ F x) (atom₁ H x))).toPartialProp
        I c).truthSet =
      {i | extension I F i.2 ∩ extension I G i.2 = ∅} ∪
        valuedIn x (extension I F ⊓ extension I G ⊓ extension I H) := by
  obtain ⟨e⟩ := ‹Nonempty E›
  have hι : ∀ g w, (iota x (atom₁ F x) (atom₁ H x)).Satt I
      (update I c (neg (neg (indef x (atom₁ F x) (atom₁ G x))))) g w := fun g w ↦ by
    rw [update_neg_neg, satt_iota, update_atom₁_of_subset fun i hi ↦ by
      rw [update_indef_atom₁] at hi; exact valuedIn_mono inf_le_left hi.2]
    exact ⟨rfl, fun h ↦ satt_atom₁.2 (ne_bot_of_realize_atom₁ h)⟩
  have hex : ∀ g w, (indef x (atom₁ F x) (atom₁ G x)).Realize I g w ↔
      (extension I F w ∩ extension I G w).Nonempty := fun g w ↦ by
    simp [Set.Nonempty]
  ext ⟨g, w⟩
  simp only [mem_truthSet_toPartialProp, satt_disj, hι, and_true, satt_neg, satt_indef,
    satt_conj, satt_atom₁, realize_disj, realize_neg, realize_conj, realize_iota, hex,
    Set.mem_union, Set.mem_ofPred_eq, mem_valuedIn, ← Set.not_nonempty_iff_eq_empty]
  simp only [show ∃ g' : PartialAssign V E, g' x ≠ ⊥ ∧ g' x ≠ ⊥ from ⟨fun _ ↦ e, by simp⟩,
    true_and]
  obtain hgx | ⟨b, hgx⟩ := (em (g x = ⊥)).imp_right Flat.ne_bot_iff_exists.1
  · simp [hgx]
  · simp only [Set.Nonempty, Set.mem_inter_iff, mem_extension, realize_atom₁, hgx, Flat.coe_inj,
      exists_eq_right', ne_eq, Flat.coe_ne_bot, not_false_eq_true, and_self, and_true,
      forall_exists_index, and_imp, not_exists, not_and, Pi.inf_apply, Set.inf_eq_inter]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact .inl h2
      · by_cases hA : ∀ a : E, (I w).RelMap F ![a] → ¬ (I w).RelMap G ![a]
        · exact .inl hA
        · obtain ⟨a, hF, hG⟩ : ∃ a : E, (I w).RelMap F ![a] ∧ (I w).RelMap G ![a] := by
            simpa using hA
          exact .inr ⟨h1 a hF hG, h2.2⟩
    · rintro (hA | ⟨hFG, hH⟩)
      · exact ⟨fun a hF hG ↦ (hA a hF hG).elim, .inl hA⟩
      · exact ⟨fun _ _ _ ↦ hFG, .inr ⟨hFG.1, hH⟩⟩

end Classicality

/-! ### Footnote 20 -/

section Footnote20

/-- A language with two relation symbols of each arity, `false` and `true`. -/
abbrev L₂ : Language := ⟨fun _ ↦ Empty, fun _ ↦ Bool⟩

/-- Two worlds over a one-element domain: the relation `false` is empty at both, the relation
`true` is full at world `true` and empty at world `false`. -/
@[reducible] def I₂ (w : Bool) : L₂.Structure Unit where
  funMap f := f.elim
  RelMap r _ := r = true ∧ w = true

@[simp] theorem relMap_I₂ {w : Bool} {n : ℕ} {r : L₂.Relations n} {es : Fin n → Unit} :
    (I₂ w).RelMap r es ↔ r = true ∧ w = true :=
  Iff.rfl

/-- `¬ɜy(⊤y, r(x, y))` with `x = 0` and `y = 1`: `x` bears `r` to nothing. The formula is free
in `x`, yet true when `x` is unvalued. -/
def bearsNothing (r : Bool) : Formula L₂ ℕ :=
  neg (indef 1 (top 1) (atom (show L₂.Relations 2 from r) ![0, 1]))

theorem realize_bearsNothing_false (g : PartialAssign ℕ Unit) (w : Bool) :
    (bearsNothing false).Realize I₂ g w := by
  simp [bearsNothing]

theorem realize_bearsNothing_bot (r w : Bool) : (bearsNothing r).Realize I₂ ⊥ w := by
  simp [bearsNothing]

theorem realize_bearsNothing_true_iff (a : Unit) (w : Bool) :
    (bearsNothing true).Realize I₂ ((⊥ : PartialAssign ℕ Unit).update 0 a) w ↔ w = false := by
  cases w <;> simp [bearsNothing]

theorem satt_bearsNothing_false (c) (g : PartialAssign ℕ Unit) (w : Bool) :
    (bearsNothing false).Satt I₂ c g w :=
  ⟨⟨fun _ ↦ (↑() : Flat Unit), by simp, by simp⟩,
    fun h ↦ absurd h (realize_neg.1 (realize_bearsNothing_false g w))⟩

theorem satt_bearsNothing_bot (r : Bool) (c) (w : Bool) : (bearsNothing r).Satt I₂ c ⊥ w :=
  ⟨⟨fun _ ↦ (↑() : Flat Unit), by simp, by simp⟩,
    fun h ↦ absurd h (realize_neg.1 (realize_bearsNothing_bot r w))⟩

local notation "F₀" => bearsNothing false
local notation "H₀" => bearsNothing true

/-- (20-b) is satt and true at every context and the empty assignment. -/
theorem holds_ex20b (c) (w : Bool) :
    (ex20b 0 F₀ F₀ H₀).Satt I₂ c ⊥ w ∧ (ex20b 0 F₀ F₀ H₀).Realize I₂ ⊥ w :=
  ⟨⟨⟨⟨⊥, satt_bearsNothing_false _ _ _, satt_bearsNothing_false _ _ _⟩, fun _ ↦
      ⟨⟨realize_bearsNothing_false _ _, realize_bearsNothing_false _ _⟩,
        satt_bearsNothing_false _ _ _, satt_bearsNothing_false _ _ _⟩⟩,
      fun _ _ ↦ ⟨realize_bearsNothing_false _ _, satt_bearsNothing_false _ _ _⟩,
      fun _ ↦ satt_bearsNothing_bot _ _ _⟩,
    ⟨⟨(), realize_bearsNothing_false _ _, realize_bearsNothing_false _ _⟩,
      realize_bearsNothing_bot _ _, realize_bearsNothing_bot _ _⟩⟩

theorem realize_ex20a_iff (w : Bool) : (ex20a 0 F₀ F₀ H₀).Realize I₂ ⊥ w ↔ w = false := by
  simp only [ex20a, realize_indef, realize_conj, realize_bearsNothing_true_iff,
    realize_bearsNothing_false, true_and, exists_const]

theorem satt_ex20a (c) (w : Bool) : (ex20a 0 F₀ F₀ H₀).Satt I₂ c ⊥ w :=
  ⟨⟨⊥, satt_bearsNothing_false _ _ _, satt_bearsNothing_false _ _ _, satt_bearsNothing_bot _ _ _⟩,
    fun _ ↦ ⟨⟨realize_bearsNothing_bot _ _, realize_bearsNothing_bot _ _,
      realize_bearsNothing_bot _ _⟩, satt_bearsNothing_bot _ _ _, satt_bearsNothing_bot _ _ _,
      satt_bearsNothing_bot _ _ _⟩⟩

/-- (20-c) is satt but false at the empty context and assignment: its pronoun's variable is
unvalued. -/
theorem satt_ex20c (w : Bool) : (ex20c 0 F₀ F₀ H₀).Satt I₂ ∅ ⊥ w :=
  ⟨(holds_ex20b ∅ w).1.1, fun _ hi ↦ absurd hi.1 (Set.notMem_empty _), fun h ↦ (h rfl).elim⟩

theorem not_realize_ex20c (w : Bool) : ¬ (ex20c 0 F₀ F₀ H₀).Realize I₂ ⊥ w :=
  fun h ↦ h.2.1 rfl

/-- (20-b) does not bound-entail (20-a) when the restrictor is `¬ɜy(⊤y, R(x, y))`: at the null
context, the empty assignment, and a world where something bears `S` to something, (20-b) is
satt and true, (20-a) satt and false. -/
theorem not_boundEntails_ex20b_ex20a :
    ¬ BoundEntails I₂ (ex20b 0 F₀ F₀ H₀) (ex20a 0 F₀ F₀ H₀) :=
  fun h ↦ Bool.noConfusion <| (realize_ex20a_iff true).1 <|
    h Set.univ (⊥, true) (holds_ex20b _ _).1 (satt_ex20a _ _) (holds_ex20b Set.univ _).2

/-- (20-a) does not bound-entail (20-c) for the same restrictor. The refuting index is a point
outside its context, the empty one; at points of the context the entailment holds
(`realize_ex20c_of_realize_ex20a`). -/
theorem not_boundEntails_ex20a_ex20c :
    ¬ BoundEntails I₂ (ex20a 0 F₀ F₀ H₀) (ex20c 0 F₀ F₀ H₀) :=
  fun h ↦ not_realize_ex20c false <|
    h ∅ (⊥, false) (satt_ex20a _ _) (satt_ex20c _) ((realize_ex20a_iff false).2 rfl)

/-- Nor does (20-b) bound-entail (20-c), again at a point outside the empty context
(`realize_ex20c_of_realize_ex20b`). -/
theorem not_boundEntails_ex20b_ex20c :
    ¬ BoundEntails I₂ (ex20b 0 F₀ F₀ H₀) (ex20c 0 F₀ F₀ H₀) :=
  fun h ↦ not_realize_ex20c true <|
    h ∅ (⊥, true) (holds_ex20b _ _).1 (satt_ex20c _) (holds_ex20b ∅ _).2

end Footnote20

end Mandelkern2022
