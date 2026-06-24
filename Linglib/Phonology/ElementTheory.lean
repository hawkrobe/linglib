/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Basic

/-!
# Element Theory: the Backley-six elements and Breit's melodic representations
[backley-2011] [backley-2017] [breit-2013] [kaye-lowenstamm-vergnaud-1985]
[harris-1994]

Element Theory (ET) builds segments from a small set of **privative** primes
called *elements*. This file formalises the **Standard ET** of [backley-2011]
and [breit-2013], with the deep structure of [backley-2017], as one layered
substrate that subsumes three otherwise-divergent strands of ET.

## The three layers

1. **Elements** as a `Fundamental × Polarity` grid [backley-2017]. The six
   elements |A I U ʔ H L| are exactly the pairing of three *fundamentals*
   (colour, resonance, frequency) with two *polar values* (dark, light).
   Antagonistic pairs and the dark/light split are *derived* from the grid,
   not stipulated.

2. **Melodic representations** (`MR`) as [breit-2013]'s set-theoretic objects:
   a numeration `Finset Element` plus an optional head obeying the **Single
   Optional Headedness Condition** (SOHC). A faithful Standard-ET segment, with
   `head`/`ops`, set-merge constructors, compose/decompose, and an elemental
   refinement order.

3. **Segments** as node-structured MRs (`Segment`): one MR per subsegmental
   node (manner / place / laryngeal). This *generalises* (1)-(2):

   * a single-node segment is a flat Standard-ET MR [breit-2013];
   * per-node SOHC (each node's MR has ≤1 head, Breit's choice) bounds heads at
     one *per node*; Backley's own headedness theory — multiple heads, but at
     most one *per fundamental* ([backley-2011] §5.3.4, [backley-2017]) — is
     carried separately as the `Segment.NoAntagonisticHeads` predicate;
   * the *same* element may dock at different nodes in different segments
     (|A| in the manner node of /r/ vs the place node of /s/), the contrastive
     geometry of [cavirani-vandenwyngaerd-2026], which goes beyond Breit's
     universal element-partition geometry.

## Relation to the rest of the library

The privative-element-with-headedness shape is the multiple-heads variant
([backley-2011] §5.3.4, [backley-2017]) of a per-node MR, and corresponds to a
`FeatureBundle Element Headedness` over `Phonology/Featural/Bundle.lean`; here
we follow Breit's SOHC model instead, so headedness is *positional* (the `head`
field) rather than a per-element value. The |H| and |L| primes are the coarse
Backley tone primes (among many other roles [backley-2017]); the finer
register-tier theory of tone lives in `Phonology/Tone`.

## Inventory: Standard ET

The six elements are those of **Standard ET** [backley-2011] [backley-2012] —
the version Backley argues strikes the best balance between expressiveness and
restrictiveness. Standard ET's distinctive move is to use *shared* elements
where Conservative ET splits them, so the substrate inherits these commitments:

* |L| carries nasality, obstruent voicing, *and* low tone (Conservative ET
  splits nasality off as a separate |N|);
* |U| carries both labial and velar resonance (Conservative ET splits velars
  off as the neutral element |@|);
* |H| carries frication, voicelessness, *and* high tone (older inventories add a
  separate noise element |h| — hence the `noise`-to-`H` migration here);
* ATR is derived from element compounds (Conservative ET posits a dedicated |Ɨ|).

Conservative ET (more elements: |N| |@| |Ɨ| |R|) and Progressive ET (fewer —
elements replaced by inter-element licensing structure) are documented
alternatives [backley-2012]; the substrate does not implement them, but a
`Studies/` file analysing a Con.ET or Prog.ET account would extend `Element`
rather than reuse it.
-/

namespace ElementTheory

-- ============================================================================
-- § 1: Fundamentals, polarity, and the six elements
-- ============================================================================

/-- The three **fundamentals** of spoken language [backley-2017]: the polar
    dimensions along which the six elements are organised. Van der Hulst's
    Radical CV Phonology identifies them with the subsegmental nodes place /
    manner / laryngeal, but a fundamental is *intrinsic* to an element, whereas
    the `Node` an element
    docks at (§4) is *contrastive*. -/
inductive Fundamental
  /-- Colour: |U| (dark) vs |I| (light). Place properties in C and V. -/
  | colour
  /-- Resonance: |A| (dark) vs |ʔ| (light). -/
  | resonance
  /-- Frequency: |L| (dark) vs |H| (light). -/
  | frequency
  deriving DecidableEq, Repr

/-- The two **polar values** of every fundamental [backley-2017]: dark elements
    concentrate acoustic energy at low frequencies, light elements at
    high/dispersed frequencies. -/
inductive Polarity
  | dark
  | light
  deriving DecidableEq, Repr

/-- The six elements of Standard Element Theory [backley-2011] [breit-2013]: the
    privative melodic primes. Named for their conventional symbols |A I U ʔ H L|.
    `glottal` is |ʔ| (the occlusion / "edge" element; its glyph is not a valid
    Lean identifier). -/
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

/-- Two distinct elements form an **antagonistic pair** [backley-2011]
    [backley-2017] iff they share a fundamental (hence opposite polarity):
    |U|+|I|, |A|+|ʔ|, |L|+|H|. These are the marked element combinations (front
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

-- ============================================================================
-- § 2: Melodic representations (Breit's set-theoretic segment)
-- ============================================================================

/-- A **melodic representation** (MR) [breit-2013]: the set-theoretic object of
    Standard Element Theory. An MR is a *numeration* `elements` together with an
    *optional head* drawn from that numeration. The **Single Optional Headedness
    Condition** (SOHC) — at most one head — is built in by `Option`; `head_mem`
    enforces `head ⊆ elements`. MRs are **achiral** (distinguished solely by
    elements + head), which is exactly structure equality here.

    Breit encodes this as nested sets `{H, C}` with `H ⊆ C`, `|H| ≤ 1`; this
    structure carries the same data with `head : Option Element` for the head
    position `H` and `elements : Finset Element` for the complement position `C`. -/
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

/-! ### Set-merge constructors [breit-2013] -/

/-- The empty MR | | [breit-2013]: the empty representation (usually [ə]). -/
def empty : MR := ⟨∅, none, by simp⟩

/-- The **unheaded simplex** |e|: a single bare element. -/
def simplex (e : Element) : MR := ⟨{e}, none, by simp⟩

/-- The **headed simplex** (singleton) |e̲|: a single element that is also the
    head [breit-2013]. -/
def headedSimplex (e : Element) : MR := ⟨{e}, some e, by simp⟩

/-- |h̲ op|: a head `h` with one operator `op` [breit-2013]. -/
def headPlusOp (h op : Element) : MR := ⟨{h, op}, some h, by simp⟩

/-- An **unheaded numeration** [breit-2013]: a bare set of elements with no head
    (Breit's first-merge object). -/
def numeration (es : Finset Element) : MR := ⟨es, none, by simp⟩

/-! ### Head, complement, operators -/

/-- `e` is present in the MR (head or operator): Breit's complement membership. -/
def HasElement (m : MR) (e : Element) : Prop := e ∈ m.elements

instance (m : MR) (e : Element) : Decidable (m.HasElement e) :=
  inferInstanceAs (Decidable (e ∈ m.elements))

/-- `e` is the head of the MR. -/
def IsHead (m : MR) (e : Element) : Prop := m.head = some e

instance (m : MR) (e : Element) : Decidable (m.IsHead e) :=
  inferInstanceAs (Decidable (m.head = some e))

/-- The MR has a head. -/
def IsHeaded (m : MR) : Prop := m.head.isSome

/-- The **operators** (dependents) [breit-2013] [kaye-lowenstamm-vergnaud-1985]:
    all elements except the head. -/
def ops (m : MR) : Finset Element :=
  match m.head with
  | none => m.elements
  | some h => m.elements.erase h

/-! ### Basic theorems -/

@[simp] theorem headedSimplex_isHead (e : Element) :
    (headedSimplex e).IsHead e := rfl

@[simp] theorem simplex_hasElement (e : Element) :
    (simplex e).HasElement e := by simp [simplex, HasElement]

theorem simplex_not_headed (e : Element) : ¬ (simplex e).IsHeaded := by
  simp [simplex, IsHeaded]

theorem empty_not_headed : ¬ empty.IsHeaded := by simp [empty, IsHeaded]

/-- Every element has a headed simplex |e̲| — Breit's existence theorem for
    singletons, here by construction. -/
theorem exists_headedSimplex (e : Element) : ∃ m : MR, m.IsHead e :=
  ⟨headedSimplex e, rfl⟩

/-! ### Compose and decompose [breit-2013]

The four element-level operations on MRs: add/remove an element from the
complement (`compose`/`decompose`), or set/clear the head (`headCompose`/
`headDecompose`). -/

/-- Add element `e` as an operator (Breit's complement-composition). -/
def compose (m : MR) (e : Element) : MR where
  elements := insert e m.elements
  head := m.head
  head_mem := fun x hx => Finset.mem_insert_of_mem (m.head_mem x hx)

/-- Remove element `e`, demoting it from head if necessary (Breit's
    complement-decomposition). -/
def decompose (m : MR) (e : Element) : MR where
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
def headCompose (m : MR) (e : Element) : MR where
  elements := insert e m.elements
  head := some e
  head_mem := by
    intro x hx
    rw [Option.mem_some_iff] at hx
    subst hx
    exact Finset.mem_insert_self _ _

/-- Remove the head, leaving the elements bare (Breit's head-decomposition). -/
def headDecompose (m : MR) : MR := ⟨m.elements, none, by simp⟩

/-- **Dock** a floating MR onto a host (floating-element association): union the
    elements; the floater's head, if any, overrides (a floating headed element
    heads the result). This is *not* the order's join — head-override is
    non-monotone when the two heads differ — so it is its own operation. Drives
    palatalisation and spreading analyses. -/
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

/-- An MR is **antagonism-free** if no two co-present elements form an
    antagonistic pair ([backley-2011] §5.3.1): the element-level analogue of
    `Segment.NoAntagonisticHeads` (which bounds *heads*; this bounds co-present
    *operators*). A node hosting an antagonistic pair such as |U I| is marked,
    and in many languages ill-formed. -/
def AntagonismFree (m : MR) : Prop :=
  ∀ e₁ ∈ m.elements, ∀ e₂ ∈ m.elements, ¬ Antagonistic e₁ e₂

instance (m : MR) : Decidable (AntagonismFree m) := by
  unfold AntagonismFree; infer_instance

/-! ### Elemental refinement order

`m₁ ⊑ m₂` — `m₂` is at least as complex: it has all of `m₁`'s elements, and
preserves `m₁`'s head if any. The three Czech palatalisers
[cavirani-vandenwyngaerd-2026] form a chain in this order. -/

/-- `m₁` refines to `m₂`: more elements, head preserved if present. -/
def Refines (m₁ m₂ : MR) : Prop :=
  m₁.elements ⊆ m₂.elements ∧ (m₁.head = none ∨ m₁.head = m₂.head)

instance (m₁ m₂ : MR) : Decidable (Refines m₁ m₂) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem Refines.refl (m : MR) : Refines m m := ⟨Finset.Subset.refl _, Or.inr rfl⟩

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

-- ============================================================================
-- § 3: The subsegmental geometry — nodes
-- ============================================================================

end MR

/-- The three subsegmental **nodes** of the Element-Theory geometry
    [harris-1994] [breit-2013] (consonant structure): the manner, place, and
    laryngeal nodes dominated by the root node. Unlike a `Fundamental`, a node
    is a *docking site* — the same element may sit at different nodes in
    different segments (|A| in the manner node of /r/ vs the place node of /s/,
    [cavirani-vandenwyngaerd-2026]). -/
inductive Node
  | manner
  | place
  | laryngeal
  deriving DecidableEq, Repr

-- ============================================================================
-- § 4: Segments — node-structured melodic representations
-- ============================================================================

/-- A **segment**: the node-structured melodic representation. Each node carries
    its own `MR` (per-node SOHC), so a segment has up to three heads — one per
    node. Backley's own headedness constraint (multiple heads, but at most one
    per fundamental; [backley-2011] §5.3.4) is `NoAntagonisticHeads` below. A
    single-node segment is a Standard-ET MR [breit-2013]; the same element may
    sit at different nodes [cavirani-vandenwyngaerd-2026]. -/
@[ext]
structure Segment where
  manner : MR
  place : MR
  laryngeal : MR
  deriving DecidableEq

namespace Segment

/-- The MR at a given node. -/
def atNode (s : Segment) : Node → MR
  | .manner => s.manner
  | .place => s.place
  | .laryngeal => s.laryngeal

/-- All elements across all nodes. -/
def allElements (s : Segment) : Finset Element :=
  s.manner.elements ∪ s.place.elements ∪ s.laryngeal.elements

/-- The number of headed nodes (0–3): a segment's total head count. -/
def headCount (s : Segment) : ℕ :=
  (if s.manner.head.isSome then 1 else 0)
    + (if s.place.head.isSome then 1 else 0)
    + (if s.laryngeal.head.isSome then 1 else 0)

/-- A segment has at most three heads — one per node (each node is per-node
    SOHC). Backley's stronger ≤1-head-*per-fundamental* bound is
    `NoAntagonisticHeads`. -/
theorem headCount_le_three (s : Segment) : s.headCount ≤ 3 := by
  unfold headCount; split_ifs <;> omega

/-- The headed elements across all nodes (0–3 of them). -/
def headList (s : Segment) : List Element :=
  [s.manner.head, s.place.head, s.laryngeal.head].filterMap id

/-- **Backley's headedness constraint** [backley-2011] §5.3.4: an
    expression may have several heads, but no two headed elements may come from
    the same antagonistic pair (`*|A̲ʔ̲|`, `*|L̲H̲|`, `*|I̲U̲|`). Heads from
    *different* fundamentals are fine (`[pʼ] = |U̲ H ʔ̲|`, `[ʃ] = |I̲ H̲|`), so a
    well-formed segment has at most one head per fundamental — [backley-2017]'s
    "up to three heads, one per fundamental". -/
def NoAntagonisticHeads (s : Segment) : Prop :=
  ∀ e₁ ∈ s.headList, ∀ e₂ ∈ s.headList, ¬ Antagonistic e₁ e₂

instance (s : Segment) : Decidable (NoAntagonisticHeads s) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, ∀ _ ∈ _, _))

/-- Heads from different fundamentals are licit ([pʼ]-style |U̲ … ʔ̲| would be,
    here |A̲| manner + |I̲| place — resonance vs colour). -/
example : NoAntagonisticHeads ⟨MR.headedSimplex .A, MR.headedSimplex .I, .empty⟩ := by
  decide

/-- Two heads from the same antagonistic pair are illicit (|A̲| and |ʔ̲| both
    head the resonance fundamental — `*|A̲ʔ̲|`). -/
example : ¬ NoAntagonisticHeads ⟨MR.headedSimplex .glottal, MR.headedSimplex .A, .empty⟩ := by
  decide

/-- Embed a Standard-ET MR at a single node (the others empty): the single-node
    segment recovers [breit-2013]'s flat melodic representation. -/
def ofMR (m : MR) : Node → Segment
  | .manner => ⟨m, .empty, .empty⟩
  | .place => ⟨.empty, m, .empty⟩
  | .laryngeal => ⟨.empty, .empty, m⟩

/-- Dock a floating segment onto a host, node by node (`MR.dock` lifted across
    the three nodes). -/
def dock (host floater : Segment) : Segment :=
  ⟨host.manner.dock floater.manner, host.place.dock floater.place,
   host.laryngeal.dock floater.laryngeal⟩

/-- **Node-hosting well-formedness** [harris-1994] [breit-2013] (the consensus
    consonant geometry), [cavirani-vandenwyngaerd-2026] (eq. 6): the place node
    hosts only |I U A|,
    the laryngeal node only |L H|, the manner node only |ʔ H L A|. -/
def WellFormed (s : Segment) : Prop :=
  (∀ e ∈ s.place.elements, e = .I ∨ e = .U ∨ e = .A) ∧
  (∀ e ∈ s.laryngeal.elements, e = .L ∨ e = .H) ∧
  (∀ e ∈ s.manner.elements, e = .glottal ∨ e = .H ∨ e = .L ∨ e = .A)

instance (s : Segment) : Decidable (WellFormed s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **Segment refinement**: pointwise MR-refinement across all three nodes. The
    Czech palatalisers PAL₁ ⊑ PAL₂ ⊑ PAL₃ form a chain in this order
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
