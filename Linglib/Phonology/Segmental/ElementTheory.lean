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
  `Element.AntagonismFree` — at most one element per fundamental.
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

/-- A finset of elements is **antagonism-free** when no two distinct members share a
    fundamental — i.e. `fundamental` is injective on it (at most one per fundamental). -/
def AntagonismFree (s : Finset Element) : Prop := Set.InjOn fundamental ↑s

instance (s : Finset Element) : Decidable (AntagonismFree s) :=
  inferInstanceAs (Decidable (Set.InjOn _ _))

end Element

/-! ### Melodic representations -/

/-- A **melodic representation**: a numeration with an optional head (SOHC). -/
@[ext]
structure MR where
  /-- The numeration — Breit's complement-position `C`: every element present. -/
  elements : Finset Element
  /-- The optional head (SOHC: at most one), a `Flat` slot: `⊥` = unheaded. -/
  head : Flat Element
  /-- The head, if any, is among the elements (Breit: `H ⊆ C`). -/
  head_mem : ∀ e : Element, head = ↑e → e ∈ elements
  deriving DecidableEq

namespace MR

variable (m : MR) (e : Element)

/-! ### Set-merge constructors -/

/-- The empty MR | |: the empty representation (usually [ə]). -/
def empty : MR := ⟨∅, ⊥, by simp⟩

/-- The **unheaded simplex** |e|: a single bare element. -/
def simplex : MR := ⟨{e}, ⊥, by simp⟩

/-- The **headed simplex** |e̲|: a single element that is also its own head. -/
def headedSimplex : MR := ⟨{e}, ↑e, by simp⟩

/-- |h̲ op|: a head `h` with one operator `op`. -/
def headPlusOp (h op : Element) : MR := ⟨{h, op}, ↑h, by simp⟩

/-- An **unheaded numeration**: a bare set of elements with no head. -/
def numeration (es : Finset Element) : MR := ⟨es, ⊥, by simp⟩

/-! ### Head, complement, operators -/

/-- `e` is present in the MR (head or operator): Breit's complement membership. -/
def HasElement : Prop := e ∈ m.elements

instance : Decidable (m.HasElement e) := inferInstanceAs (Decidable (e ∈ m.elements))

/-- `e` is the head of the MR. -/
def IsHead : Prop := m.head = ↑e

instance : Decidable (m.IsHead e) := inferInstanceAs (Decidable (m.head = ↑e))

/-- The MR has a head. -/
def IsHeaded : Prop := m.head ≠ ⊥

/-- The **operators** (dependents): all but the head ([kaye-lowenstamm-vergnaud-1985]). -/
def ops : Finset Element :=
  match m.head with
  | ⊥ => m.elements
  | (h : Element) => m.elements.erase h

/-! ### Antagonism -/

/-- No two co-present elements share a fundamental. -/
def AntagonismFree : Prop := Element.AntagonismFree m.elements

instance : Decidable m.AntagonismFree := inferInstanceAs (Decidable (Element.AntagonismFree _))

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
  head := if m.head = ↑e then ⊥ else m.head
  head_mem := by
    intro x hx
    split at hx
    · exact absurd hx Flat.bot_ne_coe
    · next h => exact Finset.mem_erase.mpr ⟨fun hxe => h (hxe ▸ hx), m.head_mem x hx⟩

/-- Promote `e` to head, adding it if absent (head-composition). -/
def headCompose : MR where
  elements := insert e m.elements
  head := ↑e
  head_mem := by simp

/-- Remove the head, leaving the elements bare (head-decomposition). -/
def headDecompose : MR := ⟨m.elements, ⊥, by simp⟩

/-- Union `host` and `floater`, the floater's head overriding (non-monotone, so
    not the order-join). -/
def dock (host floater : MR) : MR where
  elements := host.elements ∪ floater.elements
  head := floater.head.or host.head
  head_mem := by
    intro x hx
    cases hf : floater.head with
    | bot =>
      rw [hf, Flat.bot_or] at hx
      exact Finset.mem_union_left _ (host.head_mem x hx)
    | coe f =>
      rw [hf, Flat.coe_or] at hx
      exact Finset.mem_union_right _ (floater.head_mem x (hf.trans hx))

/-! ### Elemental refinement order -/

/-- Refinement: inclusion on elements, flat order (`≤` on `Flat`) on the head
    ([cavirani-vandenwyngaerd-2026]). -/
def Refines (m₁ m₂ : MR) : Prop :=
  m₁.elements ⊆ m₂.elements ∧ m₁.head ≤ m₂.head

instance (m₁ m₂ : MR) : Decidable (Refines m₁ m₂) := inferInstanceAs (Decidable (_ ∧ _))

instance : PartialOrder MR where
  le := Refines
  le_refl _ := ⟨Finset.Subset.refl _, le_rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ :=
    MR.ext (Finset.Subset.antisymm h₁.1 h₂.1) (h₁.2.antisymm h₂.2)

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

/-- The heads across all nodes (0–3), deduplicated. -/
def headFinset : Finset Element := [s.manner.head, s.place.head, s.laryngeal.head].reduceOption.toFinset

/-! ### Antagonism -/

/-- **Backley's headedness constraint**: at most one head per fundamental ([backley-2017]). -/
def NoAntagonisticHeads : Prop := Element.AntagonismFree s.headFinset

instance : Decidable s.NoAntagonisticHeads := inferInstanceAs (Decidable (Element.AntagonismFree _))

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
