/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Order.PartialUnify
import Linglib.Syntax.HPSG.Signature
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false

/-!
# Sign-Based Construction Grammar: the construct type hierarchy
[carpenter-1992] [richter-2024] [sag-2012]

The substrate for SBCG-style **construction type hierarchies with multiple inheritance**, built on
the project's Carpenter unification layer (`Core.Order.PartialUnify`, `Core.Order.Flat`) rather than
a bespoke lattice. A construction constrains a mother–daughter configuration (`MTR` + `HD-DTR` +
filler `DTR`); construction types are ordered by **subsumption** (more specific = higher, the
information order); and **multiple inheritance is unification** (`PartialUnify.unify`, the partial
least-upper-bound). A subtype's constraints are the join of its supertypes', so each supertype's
constraint is *inherited* — and inheritance is just the pointwise `≤` of the join.

## Foundations (reused, not re-derived)

* `Core.Order.PartialUnify` is [carpenter-1992]'s bounded-complete partial order with the join as
  primitive (Ch. 2, Def. 2.1): `unify` is the partial LUB, **`unify = none` is unification failure**
  (inconsistency), and `Compat` is consistency. The unification laws (`unify_comm`/`assoc`/`mono`)
  and the **`Pi` instance** (componentwise unification = feature bundles) are proved there once.
* `Core.Order.Flat` is the atomic discrete feature slot (clause type, agreement); this file adds the
  *subsumption* carrier `Cat` (`nonverbal ≤ nominal`), the partial join of a category **forest** —
  the piece `Flat` (discrete) does not cover.
* Orientation is Carpenter's: `⊥` (`Cat.any`) is the unconstrained/least-informative category,
  more-specific categories are higher, and unification climbs toward more information.

## Scope

`Construct := Position → Cat` (a binary headed construct: `MTR`, `HD-DTR`, one filler `DTR`) gets its
`PartialOrder`/`PartialUnify` from the `Pi` instance for free. General n-ary `DTRS`, multi-feature
sign constraints (a second `Flat`-valued clause-type dimension, etc.), and the Sag2010 port follow.
-/

namespace HPSG.Construction

open HPSG.RSRL (partialOrderOfBool)

/-! ### The category subsumption forest

A small HEAD/category sort hierarchy in the information order: `any` is the unconstrained `⊥`;
`verbal`/`nonverbal` are its immediate refinements; `s`/`cp`/`vp` refine `verbal` and
`nominal`/`prepositional`/`adjectival`/`adverbial` refine `nonverbal`. -/

/-- Syntactic categories as a subsumption forest (`any` = unconstrained `⊥`). -/
inductive Cat
  | any
  | verbal | nonverbal
  | s | cp | vp
  | nominal | prepositional | adjectival | adverbial
  deriving DecidableEq, Fintype, Repr

/-- Subsumption as a boolean order: `catLe a b` is "`b` is at least as specific as `a`" (`a`
subsumes `b`). The information order, so `any` (unconstrained) is below everything. -/
def catLe : Cat → Cat → Bool
  | .any, _ => true
  | .verbal, .s => true
  | .verbal, .cp => true
  | .verbal, .vp => true
  | .nonverbal, .nominal => true
  | .nonverbal, .prepositional => true
  | .nonverbal, .adjectival => true
  | .nonverbal, .adverbial => true
  | a, b => decide (a = b)

instance : PartialOrder Cat :=
  partialOrderOfBool catLe (by decide) (by decide) (by decide)

instance : DecidableLE Cat := fun a b => inferInstanceAs (Decidable (catLe a b = true))

/-- The `PartialOrder` `≤` is the boolean subsumption `catLe` (the join below uses `catLe`
directly). -/
theorem cat_le_iff (a b : Cat) : a ≤ b ↔ catLe a b = true := Iff.rfl

instance : OrderBot Cat where
  bot := .any
  bot_le := by decide

/-- Unification of categories: the more specific of two comparable categories (their least upper
bound in the subsumption order), or `none` when they are incomparable (no common refinement —
unification failure, [carpenter-1992] Ch. 2). -/
def catUnify (a b : Cat) : Option Cat :=
  if catLe a b then some b else if catLe b a then some a else none

/-- Comparable-or-incomparable is decidable on the finite forest; a common upper bound forces
comparability (ancestors in a forest form a chain). -/
private theorem cat_common_ub_comparable :
    ∀ a b u : Cat, catLe a u → catLe b u → catLe a b ∨ catLe b a := by decide

/-- `Cat` is a Carpenter unification domain: the partial join is `catUnify`. -/
instance : PartialUnify Cat where
  unify := catUnify
  isLUB_of_unify_eq_some := by
    intro a b c h
    unfold catUnify at h
    split at h
    · rename_i hab
      obtain rfl := Option.some.inj h
      exact ⟨PartialUnify.mem_upperBounds_pair.mpr ⟨(cat_le_iff a b).mpr hab, le_rfl⟩,
        fun _ hu => (PartialUnify.mem_upperBounds_pair.mp hu).2⟩
    · split at h
      · rename_i hba
        obtain rfl := Option.some.inj h
        exact ⟨PartialUnify.mem_upperBounds_pair.mpr ⟨le_rfl, (cat_le_iff b a).mpr hba⟩,
          fun _ hu => (PartialUnify.mem_upperBounds_pair.mp hu).1⟩
      · exact absurd h (by simp)
  isSome_unify_of_bddAbove := by
    intro a b hbdd
    obtain ⟨u, hu⟩ := hbdd
    obtain ⟨hau, hbu⟩ := PartialUnify.mem_upperBounds_pair.mp hu
    have comp := cat_common_ub_comparable a b u ((cat_le_iff a u).mp hau) ((cat_le_iff b u).mp hbu)
    unfold catUnify
    rcases comp with h | h
    · rw [if_pos h]; rfl
    · by_cases hab : catLe a b = true
      · rw [if_pos hab]; rfl
      · rw [if_neg hab, if_pos h]; rfl

/-! ### Constructions

A `Construct` constrains a binary headed configuration: the mother (`MTR`), the head daughter
(`HD-DTR`), and the filler daughter. As a `Pi` type over the finite `Position` index it inherits its
`PartialOrder` and `PartialUnify` (unification = multiple inheritance) from `Core.Order.PartialUnify`. -/

/-- The positions of a binary headed construct. -/
inductive Position
  | mtr | hdDtr | fillerDtr
  deriving DecidableEq, Fintype, Repr

/-- A construction: a category constraint at each position. Subsumption, unification, and `Compat`
come from the `Pi` instance. -/
abbrev Construct := Position → Cat

/-- `c` refines `s` (`c` is a subtype: at least as specific at every position). The information
order, so refinement is `s ≤ c`. -/
def Refines (c s : Construct) : Prop := s ≤ c

/-! ### The filler-head construction and subtypes -/

/-- `filler-head-cxt`: the head daughter is `[CAT verbal]` ([sag-2012] (139)) and the filler daughter
is `[CAT nonverbal]` (following [sag-2010]'s superordinate constraint); the mother is unconstrained. -/
def fillerHeadCxt : Construct
  | .mtr => .any
  | .hdDtr => .verbal
  | .fillerDtr => .nonverbal

/-- A subtype refining the filler to a nominal (NP) — a typed-category refinement that the
value-equality core could not express, since `nominal ≠ nonverbal`. -/
def nominalFillerCxt : Construct
  | .mtr => .any
  | .hdDtr => .verbal
  | .fillerDtr => .nominal

/-- A finite-clause head subtype: the head daughter refined to `s` (a verbal subtype). Cross-
classifies with `filler-head-cxt`. -/
def finiteHeadCxt : Construct
  | .mtr => .any
  | .hdDtr => .s
  | .fillerDtr => .any

/-- A common refinement of `filler-head-cxt` and `finiteHeadCxt`: head `s`, filler `nonverbal`. -/
def fhFiniteUB : Construct
  | .mtr => .any
  | .hdDtr => .s
  | .fillerDtr => .nonverbal

/-! ### Inheritance is the pointwise order of the join

A subtype refines its supertype, so at every position it is at least as specific — inheritance is
`Pi` `≤`, no enumeration of feature values. -/

/-- Every refiner of `filler-head-cxt` has a head daughter that is (a subtype of) `verbal` —
inherited, for the whole family, from the pointwise order. -/
theorem refiner_head_verbal {c : Construct} (h : Refines c fillerHeadCxt) :
    (Cat.verbal : Cat) ≤ c Position.hdDtr :=
  h Position.hdDtr

/-- Every refiner of `filler-head-cxt` has a filler daughter that is (a subtype of) `nonverbal` —
the SBCG inheritance the Sag2010 flattening could not express. -/
theorem refiner_filler_nonverbal {c : Construct} (h : Refines c fillerHeadCxt) :
    (Cat.nonverbal : Cat) ≤ c Position.fillerDtr :=
  h Position.fillerDtr

/-- The NP-filler subtype refines `filler-head-cxt` precisely because `nominal` refines
`nonverbal` (`nonverbal ≤ nominal` in the subsumption order). -/
theorem nominalFillerCxt_refines : Refines nominalFillerCxt fillerHeadCxt := by
  intro i; cases i <;> decide

/-- ...and it therefore inherits a nonverbal filler — by the theorem above, not by reading its
filler value. -/
theorem nominalFillerCxt_filler_nonverbal :
    (Cat.nonverbal : Cat) ≤ nominalFillerCxt Position.fillerDtr :=
  refiner_filler_nonverbal nominalFillerCxt_refines

/-! ### Multiple inheritance is unification

A subtype built as the unification of two supertypes refines both — the least-upper-bound property,
free from `PartialUnify`. -/

/-- Cross-classification: `filler-head-cxt` and the finite-head construction unify (they are
compatible), and the result refines both — multiple inheritance composes. -/
theorem cross_classification :
    ∃ d : Construct, PartialUnify.unify fillerHeadCxt finiteHeadCxt = some d ∧
      Refines d fillerHeadCxt ∧ Refines d finiteHeadCxt := by
  have hcompat : Compat fillerHeadCxt finiteHeadCxt :=
    Compat.of_le (u := fhFiniteUB)
      (by intro i; cases i <;> decide) (by intro i; cases i <;> decide)
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (compat_iff_isSome_unify.mp hcompat)
  refine ⟨d, hd, ?_, ?_⟩
  · exact (PartialUnify.isLUB_of_unify_eq_some hd).1 (Set.mem_insert _ _)
  · exact (PartialUnify.isLUB_of_unify_eq_some hd).1 (Set.mem_insert_of_mem _ rfl)

/-! ### Conflict is unification failure ([carpenter-1992])

Pinning the filler to `verbal` conflicts with `filler-head-cxt`'s `nonverbal`: no common refinement,
so the constructs are incompatible and do not unify. -/

/-- A construct pinning the filler daughter to `verbal`. -/
def verbalFillerCxt : Construct
  | .fillerDtr => .verbal
  | _ => .any

/-- `verbal` and `nonverbal` have no common refinement. -/
private theorem no_common_refinement (u : Cat) : ¬ ((Cat.nonverbal : Cat) ≤ u ∧ (Cat.verbal : Cat) ≤ u) := by
  revert u; decide

/-- `filler-head-cxt` and the verbal-filler construct are incompatible — the conflict is detectable,
not silently inherited. -/
theorem fillerHead_verbalFiller_incompatible : ¬ Compat fillerHeadCxt verbalFillerCxt := by
  intro ⟨u, hu⟩
  obtain ⟨h1, h2⟩ := PartialUnify.mem_upperBounds_pair.mp hu
  exact no_common_refinement (u Position.fillerDtr) ⟨h1 Position.fillerDtr, h2 Position.fillerDtr⟩

/-- Equivalently, their unification fails. -/
theorem fillerHead_verbalFiller_unify_none :
    PartialUnify.unify fillerHeadCxt verbalFillerCxt = none :=
  PartialUnify.unify_eq_none_iff.mpr fillerHead_verbalFiller_incompatible

end HPSG.Construction
