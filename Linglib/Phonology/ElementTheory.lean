/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Basic

/-!
# Element Theory

Standard Element Theory ([backley-2011], [breit-2013]): segments built from six
**privative** elements |A I U ʔ H L|, each a `Fundamental × Polarity` pairing
[backley-2017]. A *melodic representation* (`MR`) is a `Finset Element` with an
optional head (the Single Optional Headedness Condition); a `Segment` carries one
`MR` per subsegmental node (manner / place / laryngeal), so one element may dock
at different nodes in different segments [cavirani-vandenwyngaerd-2026].

## Main definitions

* `Element`, `Fundamental`, `Polarity` — the six elements as a 3×2 grid;
  `Antagonistic` — two elements sharing a fundamental (the marked combinations).
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

/-! ### Fundamentals, polarity, and the six elements -/

/-- The three **fundamentals** of spoken language [backley-2017] organising the
    six elements. A fundamental is *intrinsic* to an element, unlike the `Node`
    it docks at, which is *contrastive*. -/
inductive Fundamental
  /-- Colour: |U| (dark) vs |I| (light). Place properties in C and V. -/
  | colour
  /-- Resonance: |A| (dark) vs |ʔ| (light). -/
  | resonance
  /-- Frequency: |L| (dark) vs |H| (light). -/
  | frequency
  deriving DecidableEq, Repr

/-- The two polar values of a fundamental [backley-2017]: dark (low frequency)
    vs light (high). -/
inductive Polarity
  | dark
  | light
  deriving DecidableEq, Repr

/-- The six privative elements |A I U ʔ H L| of Standard ET [backley-2011]
    [breit-2013]; `glottal` is |ʔ| (its glyph is not a Lean identifier). -/
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

/-- The fundamental an element belongs to [backley-2017] (Table 6). -/
def Element.fundamental : Element → Fundamental
  | .U | .I => .colour
  | .A | .glottal => .resonance
  | .L | .H => .frequency

/-- The polar value of an element [backley-2017] (Table 6): dark elements
    |U A L|, light elements |I ʔ H|. -/
def Element.polarity : Element → Polarity
  | .U | .A | .L => .dark
  | .I | .glottal | .H => .light

/-- Recover the unique element with a given fundamental and polarity
    [backley-2017] (Table 6): the six elements are exactly the 3×2 grid. -/
def Element.ofFundPol : Fundamental → Polarity → Element
  | .colour, .dark => .U      | .colour, .light => .I
  | .resonance, .dark => .A   | .resonance, .light => .glottal
  | .frequency, .dark => .L   | .frequency, .light => .H

@[simp] theorem ofFundPol_fundamental (f : Fundamental) (p : Polarity) :
    (Element.ofFundPol f p).fundamental = f := by cases f <;> cases p <;> rfl

@[simp] theorem ofFundPol_polarity (f : Fundamental) (p : Polarity) :
    (Element.ofFundPol f p).polarity = p := by cases f <;> cases p <;> rfl

@[simp] theorem ofFundPol_fund_pol (e : Element) :
    Element.ofFundPol e.fundamental e.polarity = e := by cases e <;> rfl

/-- `e` is a **dark** element [backley-2017]: |U|, |A|, or |L|. -/
def Element.IsDark (e : Element) : Prop := e.polarity = .dark

instance : DecidablePred Element.IsDark :=
  fun e => inferInstanceAs (Decidable (e.polarity = .dark))

/-- Two distinct elements are **antagonistic** [backley-2011] iff they share a
    fundamental: |U|+|I|, |A|+|ʔ|, |L|+|H| — the marked combinations (front
    rounded vowels, uvular stops, voiced aspirates). -/
def Antagonistic (e₁ e₂ : Element) : Prop :=
  e₁ ≠ e₂ ∧ e₁.fundamental = e₂.fundamental

instance (e₁ e₂ : Element) : Decidable (Antagonistic e₁ e₂) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem antagonistic_symm {e₁ e₂ : Element} (h : Antagonistic e₁ e₂) :
    Antagonistic e₂ e₁ :=
  ⟨h.1.symm, h.2.symm⟩

example : Antagonistic .U .I := by decide
example : Antagonistic .A .glottal := by decide
example : Antagonistic .L .H := by decide
example : ¬ Antagonistic .U .A := by decide   -- different fundamentals
example : ¬ Antagonistic .A .A := by decide   -- not distinct

/-! ### Melodic representations -/

/-- A **melodic representation** [breit-2013]: a numeration `elements` with an
    optional `head` ⊆ `elements` (the Single Optional Headedness Condition). -/
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

/-! ### Set-merge constructors [breit-2013] -/

/-- The empty MR | | [breit-2013]: the empty representation (usually [ə]). -/
def empty : MR := ⟨∅, none, by simp⟩

/-- The **unheaded simplex** |e|: a single bare element. -/
def simplex : MR := ⟨{e}, none, by simp⟩

/-- The **headed simplex** (singleton) |e̲|: a single element that is also the
    head [breit-2013]. -/
def headedSimplex : MR := ⟨{e}, some e, by simp⟩

/-- |h̲ op|: a head `h` with one operator `op` [breit-2013]. -/
def headPlusOp (h op : Element) : MR := ⟨{h, op}, some h, by simp⟩

/-- An **unheaded numeration** [breit-2013]: a bare set of elements with no head
    (Breit's first-merge object). -/
def numeration (es : Finset Element) : MR := ⟨es, none, by simp⟩

/-! ### Head, complement, operators -/

/-- `e` is present in the MR (head or operator): Breit's complement membership. -/
def HasElement : Prop := e ∈ m.elements

instance : Decidable (m.HasElement e) :=
  inferInstanceAs (Decidable (e ∈ m.elements))

/-- `e` is the head of the MR. -/
def IsHead : Prop := m.head = some e

instance : Decidable (m.IsHead e) :=
  inferInstanceAs (Decidable (m.head = some e))

/-- The MR has a head. -/
def IsHeaded : Prop := m.head.isSome

/-- The **operators** (dependents) [breit-2013] [kaye-lowenstamm-vergnaud-1985]:
    all elements except the head. -/
def ops : Finset Element :=
  match m.head with
  | none => m.elements
  | some h => m.elements.erase h

/-! ### Basic theorems -/

@[simp] theorem headedSimplex_isHead : (headedSimplex e).IsHead e := rfl

@[simp] theorem simplex_hasElement : (simplex e).HasElement e :=
  Finset.mem_singleton_self e

theorem simplex_not_headed : ¬ (simplex e).IsHeaded := by simp [simplex, IsHeaded]

theorem empty_not_headed : ¬ empty.IsHeaded := by simp [empty, IsHeaded]

/-- Every element has a headed simplex |e̲| [breit-2013]. -/
theorem exists_headedSimplex : ∃ m : MR, m.IsHead e := ⟨headedSimplex e, rfl⟩

/-! ### Compose and decompose [breit-2013] -/

/-- Add element `e` as an operator (Breit's complement-composition). -/
def compose : MR where
  elements := insert e m.elements
  head := m.head
  head_mem := fun x hx => Finset.mem_insert_of_mem (m.head_mem x hx)

/-- Remove element `e`, demoting it from head if necessary (Breit's
    complement-decomposition). -/
def decompose : MR where
  elements := m.elements.erase e
  head := if m.head = some e then none else m.head
  head_mem := by
    intro x hx
    by_cases h : m.head = some e
    · simp [h] at hx
    · rw [if_neg h] at hx
      refine Finset.mem_erase.mpr ⟨?_, m.head_mem x hx⟩
      rintro rfl
      exact h hx

/-- Promote `e` to head, adding it if absent (Breit's head-composition). -/
def headCompose : MR where
  elements := insert e m.elements
  head := some e
  head_mem := by
    intro x hx
    rw [Option.mem_some_iff] at hx
    subst hx
    exact Finset.mem_insert_self _ _

/-- Remove the head, leaving the elements bare (Breit's head-decomposition). -/
def headDecompose : MR := ⟨m.elements, none, by simp⟩

/-- Union `host` and `floater`, the floater's head overriding (floating-element
    association; not the order-join, as head-override is non-monotone). -/
def dock (host floater : MR) : MR where
  elements := host.elements ∪ floater.elements
  head := match floater.head with
    | some f => some f
    | none   => host.head
  head_mem := by
    intro e he
    rw [Finset.mem_union]
    rcases hh : floater.head with _ | f
    · left; rw [hh] at he; exact host.head_mem e he
    · right; apply floater.head_mem; rw [hh] at he ⊢; exact he

/-- No two co-present elements are antagonistic [backley-2011] — the element-level
    analogue of `Segment.NoAntagonisticHeads` (e.g. a place node cannot host
    both |U| and |I|). -/
def AntagonismFree : Prop :=
  ∀ e₁ ∈ m.elements, ∀ e₂ ∈ m.elements, ¬ Antagonistic e₁ e₂

instance : Decidable (AntagonismFree m) := by
  unfold AntagonismFree; infer_instance

/-! ### Elemental refinement order -/

/-- `m₁` refines to `m₂`: more elements, head preserved if present
    [cavirani-vandenwyngaerd-2026]. -/
def Refines (m₁ m₂ : MR) : Prop :=
  m₁.elements ⊆ m₂.elements ∧ (m₁.head = none ∨ m₁.head = m₂.head)

instance (m₁ m₂ : MR) : Decidable (Refines m₁ m₂) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem Refines.refl : Refines m m := ⟨Finset.Subset.refl _, Or.inr rfl⟩

theorem Refines.trans {a b c : MR} (hab : Refines a b) (hbc : Refines b c) :
    Refines a c := by
  refine ⟨hab.1.trans hbc.1, ?_⟩
  rcases hab.2 with h | h
  · exact Or.inl h
  · rcases hbc.2 with h' | h'
    · exact Or.inl (h.trans h')
    · exact Or.inr (h.trans h')

theorem Refines.antisymm {a b : MR} (hab : Refines a b) (hba : Refines b a) :
    a = b := by
  refine MR.ext (Finset.Subset.antisymm hab.1 hba.1) ?_
  rcases hab.2 with h | h
  · rcases hba.2 with h' | h'
    · rw [h, h']
    · exact h'.symm
  · exact h

instance : PartialOrder MR where
  le := Refines
  le_refl := Refines.refl
  le_trans _ _ _ := Refines.trans
  le_antisymm _ _ := Refines.antisymm

instance (m₁ m₂ : MR) : Decidable (m₁ ≤ m₂) :=
  inferInstanceAs (Decidable (Refines m₁ m₂))

example : (simplex .I) ≤ (headPlusOp .H .I) := by decide

end MR

/-! ### Nodes: the subsegmental geometry -/

/-- The three subsegmental nodes [harris-1994] [breit-2013]: a *docking site*
    (contrastive, unlike a `Fundamental`) [cavirani-vandenwyngaerd-2026]. -/
inductive Node
  | manner
  | place
  | laryngeal
  deriving DecidableEq, Repr

/-! ### Segments: node-structured melodic representations -/

/-- A **segment**: one `MR` per node (per-node SOHC), so up to three heads — one
    per node [cavirani-vandenwyngaerd-2026]. -/
@[ext]
structure Segment where
  manner : MR
  place : MR
  laryngeal : MR
  deriving DecidableEq

namespace Segment

variable (s : Segment)

/-- The MR at a given node. -/
def atNode : Node → MR
  | .manner => s.manner
  | .place => s.place
  | .laryngeal => s.laryngeal

/-- All elements across all nodes. -/
def allElements : Finset Element :=
  s.manner.elements ∪ s.place.elements ∪ s.laryngeal.elements

/-- The number of headed nodes (0–3): a segment's total head count. -/
def headCount : ℕ :=
  (if s.manner.head.isSome then 1 else 0)
    + (if s.place.head.isSome then 1 else 0)
    + (if s.laryngeal.head.isSome then 1 else 0)

/-- At most three heads — one per node. -/
theorem headCount_le_three : s.headCount ≤ 3 := by
  unfold headCount; split_ifs <;> omega

/-- The headed elements across all nodes (0–3 of them). -/
def headList : List Element :=
  [s.manner.head, s.place.head, s.laryngeal.head].filterMap id

/-- **Backley's headedness constraint** [backley-2011]: no two heads are
    antagonistic, i.e. at most one head per fundamental [backley-2017]. -/
def NoAntagonisticHeads : Prop :=
  ∀ e₁ ∈ s.headList, ∀ e₂ ∈ s.headList, ¬ Antagonistic e₁ e₂

instance : Decidable (NoAntagonisticHeads s) := by
  unfold NoAntagonisticHeads; infer_instance

/-- Heads from different fundamentals (|A̲| manner, |I̲| place) are licit. -/
example : NoAntagonisticHeads ⟨MR.headedSimplex .A, MR.headedSimplex .I, .empty⟩ := by
  decide

/-- Two heads from one antagonistic pair (|A̲|, |ʔ̲|) are illicit. -/
example : ¬ NoAntagonisticHeads ⟨MR.headedSimplex .glottal, MR.headedSimplex .A, .empty⟩ := by
  decide

/-- Embed an `MR` at a single node (others empty); recovers a flat ET MR
    [breit-2013]. -/
def ofMR (m : MR) : Node → Segment
  | .manner => ⟨m, .empty, .empty⟩
  | .place => ⟨.empty, m, .empty⟩
  | .laryngeal => ⟨.empty, .empty, m⟩

/-- `MR.dock` lifted node-by-node. -/
def dock (host floater : Segment) : Segment :=
  ⟨host.manner.dock floater.manner, host.place.dock floater.place,
   host.laryngeal.dock floater.laryngeal⟩

/-- Node-hosting well-formedness [harris-1994] [cavirani-vandenwyngaerd-2026]:
    place hosts |I U A|, laryngeal |L H|, manner |ʔ H L A|. -/
def WellFormed : Prop :=
  (∀ e ∈ s.place.elements, e = .I ∨ e = .U ∨ e = .A) ∧
  (∀ e ∈ s.laryngeal.elements, e = .L ∨ e = .H) ∧
  (∀ e ∈ s.manner.elements, e = .glottal ∨ e = .H ∨ e = .L ∨ e = .A)

instance : Decidable (WellFormed s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Pointwise MR-refinement across nodes; the palatalisers form a chain
    [cavirani-vandenwyngaerd-2026]. -/
def Refines (s₁ s₂ : Segment) : Prop :=
  s₁.manner ≤ s₂.manner ∧ s₁.place ≤ s₂.place ∧ s₁.laryngeal ≤ s₂.laryngeal

instance (s₁ s₂ : Segment) : Decidable (Refines s₁ s₂) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance : PartialOrder Segment where
  le := Refines
  le_refl s := ⟨le_refl _, le_refl _, le_refl _⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.trans h₂.2.2⟩
  le_antisymm _ _ h₁ h₂ :=
    Segment.ext (le_antisymm h₁.1 h₂.1) (le_antisymm h₁.2.1 h₂.2.1) (le_antisymm h₁.2.2 h₂.2.2)

instance (s₁ s₂ : Segment) : Decidable (s₁ ≤ s₂) :=
  inferInstanceAs (Decidable (Refines s₁ s₂))

end Segment

end ElementTheory
