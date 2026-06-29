/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Basic
import Mathlib.Logic.Equiv.Defs
import Linglib.Core.Order.Flat

/-!
# Element Theory

Standard Element Theory ([backley-2011], [breit-2013]): segments built from six
**privative** elements |A I U ʔ H L|, each a `Fundamental × Polarity` pairing
[backley-2011]. A *melodic representation* (`MR`) is a `Finset Element` with an
optional head (the Single Optional Headedness Condition); a `Segment` carries one
`MR` per subsegmental node (manner / place / laryngeal), so one element may dock
at different nodes in different segments [cavirani-vandenwyngaerd-2026].

## Main definitions

* `Element`, `Fundamental`, `Polarity` — the six elements as a 3×2 grid;
  `Element.Antagonistic` — two distinct elements sharing a fundamental.
* `MR` — a melodic representation, with `dock`/`compose`/`decompose` and the
  refinement order `Refines`.
* `Segment` — a node-structured `MR`, with `Refines`, `NoAntagonisticHeads`
  (Backley's at-most-one-head-per-fundamental), and node-hosting `WellFormed`.

## Implementation notes

Headedness is positional (the `head` field), following Breit's SOHC rather than
the multiple-heads variant of [backley-2017]. The inventory is Standard ET's, not
Conservative or Progressive ET ([backley-2012]): elements are shared — |L| for
nasality/voicing/low tone, |U| for labials/velars, |H| for
frication/voicelessness/high tone.
-/

namespace ElementTheory

/-! ### The six elements -/

/-- The three fundamentals of spoken language. -/
inductive Fundamental
  /-- Colour: |U| (dark) vs |I| (light). -/
  | colour
  /-- Resonance: |A| (dark) vs |ʔ| (light). -/
  | resonance
  /-- Frequency: |L| (dark) vs |H| (light). -/
  | frequency
  deriving DecidableEq, Repr

/-- The two polar values of a fundamental. -/
inductive Polarity
  | dark
  | light
  deriving DecidableEq, Repr

/-- The six privative elements |A I U ʔ H L|. -/
inductive Element
  /-- |A| — resonance, dark. Aperture; high F1. -/
  | A
  /-- |I| — colour, light. Palatality; high F2. -/
  | I
  /-- |U| — colour, dark. Labiality / velarity; lowering of all formants. -/
  | U
  /-- |ʔ| — resonance, light. Occlusion; abrupt, sustained amplitude drop. -/
  | glottal
  /-- |H| — frequency, light. Noise / frication / voicelessness / high tone. -/
  | H
  /-- |L| — frequency, dark. Nasality / voicing / low tone. -/
  | L
  deriving DecidableEq, Repr

namespace Element

/-! ### The 3×2 grid -/

/-- The six elements **are** the 3×2 grid `Fundamental × Polarity`: each is its
    `(fundamental, polarity)` pair, and every pair is realized. -/
def gridEquiv : Element ≃ Fundamental × Polarity where
  toFun
    | .A => (.resonance, .dark)    | .I => (.colour, .light)
    | .U => (.colour, .dark)       | .glottal => (.resonance, .light)
    | .H => (.frequency, .light)   | .L => (.frequency, .dark)
  invFun
    | (.colour, .dark) => .U       | (.colour, .light) => .I
    | (.resonance, .dark) => .A    | (.resonance, .light) => .glottal
    | (.frequency, .dark) => .L    | (.frequency, .light) => .H
  left_inv e := by cases e <;> rfl
  right_inv := by rintro ⟨f, p⟩; cases f <;> cases p <;> rfl

/-- The fundamental an element belongs to. -/
def fundamental (e : Element) : Fundamental := (gridEquiv e).1

/-- The polar value of an element. -/
def polarity (e : Element) : Polarity := (gridEquiv e).2

/-- `e` is a dark element: |U|, |A|, or |L|. -/
def IsDark (e : Element) : Prop := e.polarity = .dark

instance : DecidablePred IsDark := fun e => inferInstanceAs (Decidable (e.polarity = .dark))

/-! ### Antagonism -/

/-- Two distinct elements sharing a fundamental. -/
def Antagonistic (e₁ e₂ : Element) : Prop := e₁ ≠ e₂ ∧ e₁.fundamental = e₂.fundamental

instance (e₁ e₂ : Element) : Decidable (Antagonistic e₁ e₂) := inferInstanceAs (Decidable (_ ∧ _))

theorem Antagonistic.symm {e₁ e₂ : Element} (h : Antagonistic e₁ e₂) : Antagonistic e₂ e₁ :=
  ⟨h.1.symm, h.2.symm⟩

end Element

/-! ### Melodic representations -/

/-- A **melodic representation**: a numeration with an optional head (SOHC). -/
@[ext]
structure MR where
  /-- The numeration — Breit's complement-position `C`: every element present. -/
  elements : Finset Element
  /-- The optional head (SOHC: at most one). -/
  head : Option Element
  /-- The head, if any, is among the elements (Breit: `H ⊆ C`). -/
  head_mem : ∀ e ∈ head, e ∈ elements
  deriving DecidableEq

namespace MR

variable (m : MR) (e : Element)

/-! ### Set-merge constructors -/

/-- The empty MR | |: the empty representation (usually [ə]). -/
def empty : MR := ⟨∅, none, by simp⟩

/-- The **unheaded simplex** |e|: a single bare element. -/
def simplex : MR := ⟨{e}, none, by simp⟩

/-- The **headed simplex** |e̲|: a single element that is also its own head. -/
def headedSimplex : MR := ⟨{e}, some e, by simp⟩

/-- |h̲ op|: a head `h` with one operator `op`. -/
def headPlusOp (h op : Element) : MR := ⟨{h, op}, some h, by simp⟩

/-- An **unheaded numeration**: a bare set of elements with no head. -/
def numeration (es : Finset Element) : MR := ⟨es, none, by simp⟩

/-! ### Head, complement, operators -/

/-- `e` is present in the MR (head or operator): Breit's complement membership. -/
def HasElement : Prop := e ∈ m.elements

instance : Decidable (m.HasElement e) := inferInstanceAs (Decidable (e ∈ m.elements))

/-- `e` is the head of the MR. -/
def IsHead : Prop := m.head = some e

instance : Decidable (m.IsHead e) := inferInstanceAs (Decidable (m.head = some e))

/-- The MR has a head. -/
def IsHeaded : Prop := m.head ≠ none

/-- The **operators** (dependents): all but the head ([kaye-lowenstamm-vergnaud-1985]). -/
def ops : Finset Element :=
  match m.head with
  | none => m.elements
  | some h => m.elements.erase h

/-! ### Antagonism -/

/-- No two co-present elements share a fundamental. -/
def AntagonismFree : Prop := ∀ e₁ ∈ m.elements, ∀ e₂ ∈ m.elements, ¬ Element.Antagonistic e₁ e₂

instance : Decidable (AntagonismFree m) := by unfold AntagonismFree; infer_instance

/-! ### Basic theorems -/

@[simp] theorem headedSimplex_isHead : (headedSimplex e).IsHead e := rfl

@[simp] theorem simplex_hasElement : (simplex e).HasElement e := Finset.mem_singleton_self e

theorem simplex_not_headed : ¬ (simplex e).IsHeaded := fun h => h rfl

theorem empty_not_headed : ¬ empty.IsHeaded := fun h => h rfl

/-- Every element has a headed simplex |e̲|. -/
theorem exists_headedSimplex : ∃ m : MR, m.IsHead e := ⟨headedSimplex e, rfl⟩

/-! ### Compose and decompose -/

/-- Add element `e` as an operator (complement-composition). -/
def compose : MR where
  elements := insert e m.elements
  head := m.head
  head_mem := fun x hx => Finset.mem_insert_of_mem (m.head_mem x hx)

/-- Remove element `e`, demoting it from head if present (complement-decomposition). -/
def decompose : MR where
  elements := m.elements.erase e
  head := if m.head = some e then none else m.head
  head_mem := by grind [MR.head_mem, Option.mem_def]

/-- Promote `e` to head, adding it if absent (head-composition). -/
def headCompose : MR where
  elements := insert e m.elements
  head := some e
  head_mem := by grind [Finset.mem_insert_self, Option.mem_def]

/-- Remove the head, leaving the elements bare (head-decomposition). -/
def headDecompose : MR := ⟨m.elements, none, by simp⟩

/-- Union `host` and `floater`, the floater's head overriding (non-monotone, so
    not the order-join). -/
def dock (host floater : MR) : MR where
  elements := host.elements ∪ floater.elements
  head := match floater.head with
    | some f => some f
    | none   => host.head
  head_mem := by grind [MR.head_mem, Option.mem_def]

/-! ### Elemental refinement order -/

/-- Refinement: inclusion on elements, flat order (`Option.FlatLE`) on the head
    ([cavirani-vandenwyngaerd-2026]). -/
def Refines (m₁ m₂ : MR) : Prop :=
  m₁.elements ⊆ m₂.elements ∧ Option.FlatLE m₁.head m₂.head

instance (m₁ m₂ : MR) : Decidable (Refines m₁ m₂) := inferInstanceAs (Decidable (_ ∧ _))

instance : PartialOrder MR where
  le := Refines
  le_refl _ := ⟨Finset.Subset.refl _, Option.FlatLE.refl _⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ :=
    MR.ext (Finset.Subset.antisymm h₁.1 h₂.1) (Option.FlatLE.antisymm h₁.2 h₂.2)

instance (m₁ m₂ : MR) : Decidable (m₁ ≤ m₂) := inferInstanceAs (Decidable (Refines m₁ m₂))

example : (simplex .I) ≤ (headPlusOp .H .I) := by decide

end MR

/-! ### Nodes: the subsegmental geometry -/

/-- The three subsegmental nodes ([harris-1994]): docking sites, contrastive
    unlike a `Fundamental`. -/
inductive Node
  | manner
  | place
  | laryngeal
  deriving DecidableEq, Repr

/-! ### Segments: node-structured melodic representations -/

/-- A **segment**: one `MR` per node (per-node SOHC) — so up to three heads. -/
@[ext]
structure Segment where
  manner : MR
  place : MR
  laryngeal : MR
  deriving DecidableEq

namespace Segment

variable (s : Segment)

/-! ### Projections -/

/-- The MR at a given node. -/
def atNode : Node → MR
  | .manner => s.manner
  | .place => s.place
  | .laryngeal => s.laryngeal

/-- All elements across all nodes. -/
def allElements : Finset Element := s.manner.elements ∪ s.place.elements ∪ s.laryngeal.elements

/-- The number of headed nodes (0–3). -/
def headCount : ℕ :=
  (if s.manner.head.isSome then 1 else 0)
    + (if s.place.head.isSome then 1 else 0)
    + (if s.laryngeal.head.isSome then 1 else 0)

/-- At most three heads — one per node. -/
theorem headCount_le_three : s.headCount ≤ 3 := by unfold headCount; split_ifs <;> omega

/-- The headed elements across all nodes (0–3 of them). -/
def headList : List Element := [s.manner.head, s.place.head, s.laryngeal.head].reduceOption

/-! ### Antagonism -/

/-- **Backley's headedness constraint**: at most one head per fundamental ([backley-2017]). -/
def NoAntagonisticHeads : Prop :=
  ∀ e₁ ∈ s.headList, ∀ e₂ ∈ s.headList, ¬ Element.Antagonistic e₁ e₂

instance : Decidable (NoAntagonisticHeads s) := by unfold NoAntagonisticHeads; infer_instance

/-- Heads from different fundamentals (|A̲| manner, |I̲| place) are licit. -/
example : NoAntagonisticHeads ⟨MR.headedSimplex .A, MR.headedSimplex .I, .empty⟩ := by decide

/-- Two heads from one antagonistic pair (|A̲|, |ʔ̲|) are illicit. -/
example : ¬ NoAntagonisticHeads ⟨MR.headedSimplex .glottal, MR.headedSimplex .A, .empty⟩ := by decide

/-! ### Operations -/

/-- Embed an `MR` at a single node (others empty); recovers a flat ET MR. -/
def ofMR (m : MR) : Node → Segment
  | .manner => ⟨m, .empty, .empty⟩
  | .place => ⟨.empty, m, .empty⟩
  | .laryngeal => ⟨.empty, .empty, m⟩

/-- `MR.dock` lifted node-by-node. -/
def dock (host floater : Segment) : Segment :=
  ⟨host.manner.dock floater.manner, host.place.dock floater.place,
   host.laryngeal.dock floater.laryngeal⟩

/-! ### Well-formedness -/

/-- Node-hosting well-formedness ([harris-1994]): place |I U A|, laryngeal |L H|,
    manner |ʔ H L A|. -/
def WellFormed : Prop :=
  (∀ e ∈ s.place.elements, e = .I ∨ e = .U ∨ e = .A) ∧
  (∀ e ∈ s.laryngeal.elements, e = .L ∨ e = .H) ∧
  (∀ e ∈ s.manner.elements, e = .glottal ∨ e = .H ∨ e = .L ∨ e = .A)

instance : Decidable (WellFormed s) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ### Refinement order -/

/-- Pointwise MR-refinement across nodes (the palataliser chain). -/
def Refines (s₁ s₂ : Segment) : Prop :=
  s₁.manner ≤ s₂.manner ∧ s₁.place ≤ s₂.place ∧ s₁.laryngeal ≤ s₂.laryngeal

instance (s₁ s₂ : Segment) : Decidable (Refines s₁ s₂) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance : PartialOrder Segment where
  le := Refines
  le_refl s := ⟨le_refl _, le_refl _, le_refl _⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.trans h₂.2.2⟩
  le_antisymm _ _ h₁ h₂ :=
    Segment.ext (le_antisymm h₁.1 h₂.1) (le_antisymm h₁.2.1 h₂.2.1) (le_antisymm h₁.2.2 h₂.2.2)

instance (s₁ s₂ : Segment) : Decidable (s₁ ≤ s₂) := inferInstanceAs (Decidable (Refines s₁ s₂))

end Segment

end ElementTheory
