module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.RelClasses

/-!
# Neighborhoods

The local environment a postsyntactic rule inspects: a focus terminal with
the terminals to either side, nearest first. Vocabulary Items and
Impoverishment rules are stated over the same neighborhoods. An item's site is
itself a neighborhood of feature lists, and the item applies wherever each
feature the site mentions sits at the same offset from the focus: the Subset
Principle's inclusion of sites, `⊆`.

## Main definitions

* `Neighborhood`: focus, left context, right context.
* `Neighborhood.nth`: the terminal at an integer offset from the focus.
* `(i, f) ∈ n`: the terminal at offset `i` bears the feature `f`; `s ⊆ n` when
  every positioned feature of `s` is one of `n`.
* `Neighborhood.positioned`, `Neighborhood.toFinset`: the positioned features,
  listed and as a finite set.

## Main results

* `Neighborhood.mem_positioned`: `positioned` lists exactly the positioned
  features, so it decides `⊆`.
* `Neighborhood.subset_iff_nth`: inclusion compares terminal by terminal.
* `Neighborhood.ofBundle_subset_iff`: a context-free site is included where its
  features are on the focus.
* `Neighborhood.card_toFinset_strictMono`: a strictly larger site has strictly
  more positioned features, the ground of the Subset Principle's specificity.

## Implementation notes

Offsets are integers, indexed as for `Turing.Tape.nth`: `0` is the focus,
`-(k + 1)` the `k`-th terminal to the left (toward the root), `k + 1` the `k`-th
to the right (toward the clause), and past either end `nth` returns `default`,
for a feature list `[]`. Inclusion ignores the order and repetition of features
on a terminal and empty terminals past the ends, so it is a preorder and not a
partial order; as for `PSet`, the preorder is written `⊆`.

A bare bundle coerces to the context-free neighborhood and `∅` is the empty
site, so a context-free Vocabulary Item is written `⟨[f₁, f₂], e⟩` and the
Elsewhere item `⟨∅, e⟩`.

## References

* [M. Halle and A. Marantz, *Distributed Morphology and the pieces of
  inflection*][halle-marantz-1993]
* [M. Halle, *Distributed Morphology: Impoverishment and Fission*][halle-1997]
-/

@[expose] public section

namespace DistributedMorphology

variable {Bundle F : Type*}

/-- The local context a postsyntactic rule may inspect: the `focus` terminal
and the terminals to either side, nearest first. A condition that only
inspects `focus` is paradigmatic; one that reads `leftCtx` or `rightCtx` is
syntagmatic. -/
@[use_set_notation_for_order]
structure Neighborhood (Bundle : Type*) where
  /-- The terminal the rule inspects. -/
  focus    : Bundle
  /-- The terminals to its left, nearest first. -/
  leftCtx  : List Bundle := []
  /-- The terminals to its right, nearest first. -/
  rightCtx : List Bundle := []
  deriving Repr, DecidableEq

namespace Neighborhood

/-- A bundle, viewed as a context-free neighborhood. -/
@[coe] def ofBundle (fb : Bundle) : Neighborhood Bundle := { focus := fb }

instance : Coe Bundle (Neighborhood Bundle) := ⟨ofBundle⟩

instance [EmptyCollection Bundle] : EmptyCollection (Neighborhood Bundle) := ⟨ofBundle ∅⟩

@[simp] theorem focus_ofBundle (fb : Bundle) : (ofBundle fb).focus = fb := rfl

@[simp] theorem leftCtx_ofBundle (fb : Bundle) : (ofBundle fb).leftCtx = [] := rfl

@[simp] theorem rightCtx_ofBundle (fb : Bundle) : (ofBundle fb).rightCtx = [] := rfl

@[simp] theorem ofBundle_nil : ofBundle ([] : List F) = ∅ := rfl

/-! ### Offsets -/

/-- The terminal at offset `i` from the focus: `0` is the focus, `-(k + 1)` the
`k`-th terminal to the left, `k + 1` the `k`-th to the right, and `default` past
either end. -/
def nth [Inhabited Bundle] (n : Neighborhood Bundle) : ℤ → Bundle
  | 0 => n.focus
  | (k + 1 : ℕ) => n.rightCtx.getD k default
  | -(k + 1 : ℕ) => n.leftCtx.getD k default

section nth

variable [Inhabited Bundle] (n : Neighborhood Bundle) (k : ℕ)

@[simp] theorem nth_zero : n.nth 0 = n.focus := rfl

@[simp] theorem nth_natCast_add_one : n.nth (k + 1) = n.rightCtx.getD k default := rfl

@[simp] theorem nth_neg_natCast_add_one : n.nth (-(k + 1)) = n.leftCtx.getD k default := rfl

end nth

/-! ### Positioned features -/

variable {s n : Neighborhood (List F)} {x : ℤ × F}

/-- `(i, f) ∈ n`: the terminal at offset `i` from the focus bears the feature `f`. -/
instance : Membership (ℤ × F) (Neighborhood (List F)) := ⟨fun n x ↦ x.2 ∈ n.nth x.1⟩

theorem mem_def : x ∈ n ↔ x.2 ∈ n.nth x.1 := Iff.rfl

instance [DecidableEq F] (x : ℤ × F) (n : Neighborhood (List F)) : Decidable (x ∈ n) :=
  inferInstanceAs (Decidable (x.2 ∈ n.nth x.1))

/-- The positioned features of a neighborhood of feature lists, listed: the
focus's at offset `0`, then the left context's, then the right context's. -/
def positioned (n : Neighborhood (List F)) : List (ℤ × F) :=
  n.focus.map (0, ·) ++
    n.leftCtx.zipIdx.flatMap (fun p ↦ p.1.map (-(p.2 + 1 : ℤ), ·)) ++
    n.rightCtx.zipIdx.flatMap (fun p ↦ p.1.map ((p.2 + 1 : ℤ), ·))

private theorem mem_flatMap_zipIdx {l : List (List F)} {g : ℕ → ℤ} {i : ℤ} {f : F} :
    (i, f) ∈ l.zipIdx.flatMap (fun p ↦ p.1.map (g p.2, ·)) ↔ ∃ k, g k = i ∧ f ∈ l.getD k [] := by
  simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq, List.getD_eq_getElem?_getD,
    Prod.exists, List.mem_zipIdx_iff_getElem?]
  grind

@[simp] theorem mem_positioned : x ∈ n.positioned ↔ x ∈ n := by
  obtain ⟨i, f⟩ := x
  simp only [positioned, List.mem_append, mem_flatMap_zipIdx (g := fun k : ℕ ↦ -(k + 1 : ℤ)),
    mem_flatMap_zipIdx (g := fun k : ℕ ↦ (k + 1 : ℤ)), List.mem_map, Prod.mk.injEq, mem_def]
  constructor
  · rintro ((⟨a, ha, rfl, rfl⟩ | ⟨k, rfl, hf⟩) | ⟨k, rfl, hf⟩) <;> assumption
  · rcases i with (_ | k) | k <;> intro hf
    · exact .inl (.inl ⟨f, hf, rfl, rfl⟩)
    · exact .inr ⟨k, rfl, hf⟩
    · exact .inl (.inr ⟨k, rfl, hf⟩)

@[simp] theorem positioned_ofBundle (fs : List F) :
    (ofBundle fs : Neighborhood (List F)).positioned = fs.map (0, ·) := by
  simp [positioned, ofBundle]

@[simp] theorem positioned_empty : (∅ : Neighborhood (List F)).positioned = [] := rfl

@[simp] theorem mem_ofBundle {fs : List F} :
    x ∈ (fs : Neighborhood (List F)) ↔ x.1 = 0 ∧ x.2 ∈ fs := by
  rw [← mem_positioned, positioned_ofBundle]
  obtain ⟨i, f⟩ := x
  simp [eq_comm, and_comm]

@[simp] theorem notMem_empty : x ∉ (∅ : Neighborhood (List F)) := by
  simp [← mem_positioned]

/-! ### Inclusion -/

/-- A site is included in a neighborhood when every positioned feature it
mentions is present; a terminal it does not mention is unconstrained. This is
the Subset Principle's inclusion. -/
instance : Preorder (Neighborhood (List F)) where
  le s n := ∀ ⦃x⦄, x ∈ s → x ∈ n
  le_refl _ _ := id
  le_trans _ _ _ h₁ h₂ _ hx := h₂ (h₁ hx)

theorem subset_iff : s ⊆ n ↔ ∀ ⦃x⦄, x ∈ s → x ∈ n := Iff.rfl

theorem mem_of_subset (h : s ⊆ n) (hx : x ∈ s) : x ∈ n := h hx

/-- Inclusion compares terminal by terminal. -/
theorem subset_iff_nth : s ⊆ n ↔ ∀ i, s.nth i ⊆ n.nth i :=
  ⟨fun h i _ hf ↦ h (x := (i, _)) hf, fun h x hx ↦ h x.1 hx⟩

theorem subset_iff_positioned : s ⊆ n ↔ s.positioned ⊆ n.positioned := by
  simp [subset_iff, List.subset_def]

instance [DecidableEq F] : DecidableLE (Neighborhood (List F)) :=
  fun _ _ ↦ decidable_of_iff _ subset_iff_positioned.symm

@[simp] theorem empty_subset (n : Neighborhood (List F)) : ∅ ⊆ n := fun _ h ↦ absurd h notMem_empty

/-- A context-free site is included in a neighborhood exactly when its features
are on the focus. -/
@[simp] theorem ofBundle_subset_iff {fs : List F} :
    (fs : Neighborhood (List F)) ⊆ n ↔ fs ⊆ n.focus :=
  ⟨fun h _ hf ↦ h (x := (0, _)) (mem_ofBundle.mpr ⟨rfl, hf⟩),
    fun h _ hx ↦ by obtain ⟨hi, hf⟩ := mem_ofBundle.mp hx; exact mem_def.mpr (hi ▸ h hf)⟩

/-! ### Counting positioned features -/

section toFinset

variable [DecidableEq F]

/-- The positioned features of a neighborhood of feature lists, as a finite set. -/
def toFinset (n : Neighborhood (List F)) : Finset (ℤ × F) := n.positioned.toFinset

@[simp] theorem mem_toFinset : x ∈ n.toFinset ↔ x ∈ n := by simp [toFinset]

@[simp] theorem toFinset_empty : (∅ : Neighborhood (List F)).toFinset = ∅ := rfl

@[simp] theorem toFinset_subset_toFinset : s.toFinset ⊆ n.toFinset ↔ s ⊆ n := by
  simp [Finset.subset_iff, subset_iff]

@[simp] theorem toFinset_ssubset_toFinset : s.toFinset ⊂ n.toFinset ↔ s ⊂ n := by
  simp [ssubset_iff_subset_not_subset]

/-- A strictly larger site has strictly more positioned features. -/
theorem card_toFinset_strictMono :
    StrictMono fun n : Neighborhood (List F) ↦ n.toFinset.card :=
  fun _ _ h ↦ Finset.card_lt_card (toFinset_ssubset_toFinset.mpr h)

end toFinset

end Neighborhood

end DistributedMorphology
