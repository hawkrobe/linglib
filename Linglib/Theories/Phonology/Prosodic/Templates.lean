import Linglib.Core.Morphology.ConsonantalRoot
import Linglib.Theories.Phonology.OptimalityTheory.Constraints

/-!
# CV-Skeletal Templates and Root–Template Association
@cite{mccarthy-1981} @cite{lowenstamm-1996} @cite{faust-2026}

The McCarthy 1981 / Strict-CV (Lowenstamm 1996) representation of
nonconcatenative morphology: a *template* is a sequence of CV slots,
optionally specified for [+consonantal]; a *root* is associated to the
template by mapping root segments to slots (left-to-right by default).

## Single source of truth

This module provides one `Template` type, one `Association` type, and one
`RootTemplateMatch` carrier — used by every templatic-morphology study in the
library. The `Root α` segment type is imported from `Core.Lexical`, so that
the same root data is shared between phonology (this module), morphology
(template-satisfaction analyses), and fragments (Hebrew, Amharic, Tarifit).

## *Misalignment

Following @cite{faust-2026}, a derived predicate `RootTemplateMatch.isMisaligned`
fires when a *nonfinal* root segment lands in the *final* template slot. The
predicate distinguishes associations from the root proper (`AssocSource.root`)
from associations from a sister exponent (`AssocSource.intruder`, e.g. the
feminine [t] in Hebrew taQTiL or Amharic gerund and INF). Intruder associations
are exempt from *Misalignment because the intruder is not a root segment in
the first place — the central analytical move of @cite{faust-2026} §4.
-/

namespace Phonology.Templates

open Core.Morphology
open Core.Constraint.OT (NamedConstraint)
open Phonology.Constraints (mkAlign)

-- ============================================================================
-- § 1: CV Slots
-- ============================================================================

/-- A slot in a CV-skeletal template (@cite{mccarthy-1981}, @cite{lowenstamm-1996}):

    - `C`: a bare consonantal timing slot.
    - `V`: a vowel timing slot.
    - `Cspec`: a C-slot bearing the [+consonantal] feature, blocking association
      from glides like /j/ — this is the slot type that triggers the
      QaTaT–QaTa problem when paired with a [j]-final root
      (@cite{faust-2026} (4)). -/
inductive CVSlot where
  | C
  | V
  | Cspec
  deriving DecidableEq, Repr

namespace CVSlot

/-- Is this slot a C-slot (bare or [+c]-specified)? -/
def IsC : CVSlot → Prop
  | .C | .Cspec => True
  | .V => False

instance : DecidablePred IsC := fun s => by
  cases s <;> unfold IsC <;> infer_instance

/-- Is this slot a V-slot? -/
def IsV : CVSlot → Prop
  | .V => True
  | _ => False

instance : DecidablePred IsV := fun s => by
  cases s <;> unfold IsV <;> infer_instance

/-- Does this slot require a [+consonantal] segment? -/
def RequiresConsonantal : CVSlot → Prop
  | .Cspec => True
  | _ => False

instance : DecidablePred RequiresConsonantal := fun s => by
  cases s <;> unfold RequiresConsonantal <;> infer_instance

end CVSlot

-- ============================================================================
-- § 2: Templates
-- ============================================================================

/-- A CV-skeletal template: an ordered sequence of slots. -/
structure Template where
  slots : List CVSlot
  deriving Repr, DecidableEq

namespace Template

/-- The number of slots in the template. -/
def length (t : Template) : Nat := t.slots.length

/-- The number of C-slots (consonant timing positions). -/
def cCount (t : Template) : Nat :=
  (t.slots.filter (fun s => decide (CVSlot.IsC s))).length

/-- Slot `i` is the final slot of the template. -/
def isFinalSlot (t : Template) (i : Nat) : Bool := i + 1 == t.length

/-- The slot at position `i`, if in range. -/
def slotAt (t : Template) (i : Nat) : Option CVSlot := t.slots[i]?

end Template

-- ============================================================================
-- § 3: Root–Template Association
-- ============================================================================

/-- The morphological source of an association.

    Faust 2026's analysis turns on this distinction: a `.root` association
    is subject to *Misalignment, an `.intruder` association is not. Intruders
    are sister exponents (e.g. the feminine [t] in Hebrew taQTiL nouns,
    @cite{faust-2026} (10)) that satisfy the template without being root
    segments themselves. -/
inductive AssocSource where
  | root
  | intruder
  deriving DecidableEq, Repr

/-- A single root-to-slot association line (@cite{mccarthy-1981}).

    `rootIndex` is interpreted relative to the root for `.root` associations,
    or as an opaque tag for `.intruder` associations (intruder identity is
    handled at the fragment level — this module is segment-agnostic).

    Defaults to `.root` so that "ordinary" associations stay terse. -/
structure Association where
  source : AssocSource := .root
  rootIndex : Nat
  slotIndex : Nat
  deriving DecidableEq, Repr

/-- A root paired with a template and a list of associations.

    Different *candidate* realizations of the same root × template pair are
    different `RootTemplateMatch` values that share `root` and `template` but
    differ in `associations`. The Faust 2026 analysis compares such candidates
    via the derived `isMisaligned` predicate. -/
structure RootTemplateMatch (α : Type) where
  root : Root α
  template : Template
  associations : List Association
  deriving Repr, DecidableEq

namespace RootTemplateMatch

variable {α : Type}

/-- An association is a *root-to-final* link iff it comes from the root proper
    and lands at the template-final slot. -/
def isRootFinal (m : RootTemplateMatch α) (a : Association) : Bool :=
  a.source == .root && m.template.isFinalSlot a.slotIndex

/-- *Misalignment* (@cite{faust-2026} (2)): the match has a nonfinal root
    segment associated to the template-final slot. Intruder associations do
    not count — see `AssocSource`. -/
def isMisaligned (m : RootTemplateMatch α) : Bool :=
  m.associations.any fun a =>
    a.source == .root &&
    m.root.isNonfinal a.rootIndex &&
    m.template.isFinalSlot a.slotIndex

/-- Every C-slot of the template is filled by *some* association
    (root or intruder). -/
def allCSlotsFilled (m : RootTemplateMatch α) : Bool :=
  (List.range m.template.length).all fun i =>
    match m.template.slotAt i with
    | some s => !decide (CVSlot.IsC s) || m.associations.any (·.slotIndex == i)
    | none => true

/-- The template is *satisfied* iff all C-slots are filled and the result
    is not misaligned. The two requirements are independent — the central
    point of @cite{faust-2026} is that for [j]-final biradicals in Hebrew,
    one cannot satisfy the first without violating the second. -/
def satisfies (m : RootTemplateMatch α) : Bool :=
  m.allCSlotsFilled && !m.isMisaligned

/-- Every association points to an in-range root segment and slot. -/
def inBounds (m : RootTemplateMatch α) : Bool :=
  m.associations.all fun a =>
    decide (a.slotIndex < m.template.length) &&
    (a.source != .root || decide (a.rootIndex < m.root.arity))

/-- The list of C-slot indices that are NOT filled by any association.
    Used by hollow-root analyses (@cite{faust-2026} (13)): when the
    medial radical is non-consonantal, the medial C-slot is unfilled,
    and the position of the unfilled slot determines whether
    [t]-intrusion is licensed (final-empty: licit; medial-empty: blocked
    by the No-Crossing Constraint). -/
def unfilledCSlots (m : RootTemplateMatch α) : List Nat :=
  (List.range m.template.length).filter fun i =>
    match m.template.slotAt i with
    | some s => decide (CVSlot.IsC s) && !m.associations.any (·.slotIndex == i)
    | none => false

/-- The No-Crossing Constraint (@cite{goldsmith-1976}): an intruder
    association at slot `i` crosses an existing association at slot `j > i`.
    Right-edge intruders (e.g. the feminine /t/ suffix in Hebrew taQTiL
    and Amharic gerunds) associate inward from the right, so any root
    segment to the right of the intruder forces line-crossing.

    This is the predicate that explains @cite{faust-2026} (13b–c):
    [t]-intrusion does not fill the medial C[+c] of [mäsam]/[mähid]
    because the final C-slot is *already* filled by the final root
    radical, so an intruder at the medial position would have to cross
    the final root association line. -/
def violatesNCC (m : RootTemplateMatch α) : Bool :=
  m.associations.any fun a =>
    a.source == .intruder &&
    m.associations.any fun b =>
      b.source == .root && a.slotIndex < b.slotIndex

/-- Does this match contain any intruder associations?
    Templates without intruders are licit in any morphosyntactic context
    (verbal or nominal); templates with intruders require external
    licensing — see `intrusionLicensed`. -/
def hasIntruder (m : RootTemplateMatch α) : Bool :=
  m.associations.any (·.source == .intruder)

/-- A `RootTemplateMatch` is *intrusion-licensed* under an external
    licensing predicate iff either (a) the predicate is `true`
    (the morphosyntactic context licenses an intruding sister bound
    root, à la @cite{lowenstamm-2014}), or (b) the match contains no
    intruder associations.

    The licensing predicate is supplied by the morphological theory
    above — for @cite{faust-2026}'s analysis, it evaluates to `true`
    iff the template is realized at an `n[+gen]` head in
    @cite{kramer-2020}'s sense (verbal templates, whose gender lives
    on a higher Agr head, evaluate to `false` and so admit no
    intrusion). The predicate is `Bool`-valued rather than a
    `MorphologicalLocus` enum so that `Templates.lean` need not
    depend on `Morphology.DM`. -/
def intrusionLicensed (m : RootTemplateMatch α) (licensed : Bool) : Bool :=
  licensed || !m.hasIntruder

end RootTemplateMatch

-- ============================================================================
-- § 4: Basic Properties
-- ============================================================================

variable {α : Type}

/-- A match with no associations is trivially not misaligned. -/
theorem isMisaligned_empty (r : Root α) (t : Template) :
    (RootTemplateMatch.mk r t []).isMisaligned = false := rfl

/-- *Misalignment cannot fire from intruder associations alone. -/
theorem isMisaligned_intruder_only (r : Root α) (t : Template)
    (assocs : List Association)
    (h : assocs.all (fun a => a.source == .intruder) = true) :
    (RootTemplateMatch.mk r t assocs).isMisaligned = false := by
  simp only [RootTemplateMatch.isMisaligned]
  induction assocs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    simp only [List.any_cons, Bool.or_eq_false_iff]
    refine ⟨?_, ih h2⟩
    simp only [Bool.and_eq_false_iff]
    left
    -- a.source == .intruder, so a.source ≠ .root, so (a.source == .root) = false
    have hsrc : a.source = .intruder := by simpa [beq_iff_eq] using h1
    exact Or.inl (by rw [hsrc]; rfl)

/-- Structural characterization of `isMisaligned`: there exists a root
    association at a nonfinal root position landing at a template-final
    slot. Lets later proofs reason about misalignment via a witness rather
    than unfolding `List.any`. -/
theorem isMisaligned_iff (m : RootTemplateMatch α) :
    m.isMisaligned = true ↔
      ∃ a ∈ m.associations,
        a.source = .root ∧
        m.root.isNonfinal a.rootIndex = true ∧
        m.template.isFinalSlot a.slotIndex = true := by
  simp only [RootTemplateMatch.isMisaligned, List.any_eq_true,
    Bool.and_eq_true, beq_iff_eq, and_assoc]

/-- Structural characterization of `violatesNCC`: there exist an
    intruder association and a root association with the intruder
    strictly to the left of the root association. -/
theorem violatesNCC_iff (m : RootTemplateMatch α) :
    m.violatesNCC = true ↔
      ∃ a ∈ m.associations, a.source = .intruder ∧
        ∃ b ∈ m.associations, b.source = .root ∧
          a.slotIndex < b.slotIndex := by
  simp only [RootTemplateMatch.violatesNCC, List.any_eq_true,
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]

/-- `satisfies` decomposes into its two conjuncts: all C-slots filled
    AND not misaligned. The reading the squib's central argument depends on. -/
theorem satisfies_iff (m : RootTemplateMatch α) :
    m.satisfies = true ↔
      m.allCSlotsFilled = true ∧ m.isMisaligned = false := by
  simp [RootTemplateMatch.satisfies]

/-- Structural characterization of `intrusionLicensed`: a match passes
    licensing iff either the external predicate licenses intrusion OR
    the match is intruder-free. The disjunction is the formal content
    of the verbal/nominal asymmetry — verbal templates require
    intruder-free derivations; nominal templates with `n[+gen]` admit
    either. -/
theorem intrusionLicensed_iff (m : RootTemplateMatch α) (licensed : Bool) :
    m.intrusionLicensed licensed = true ↔
      licensed = true ∨ m.hasIntruder = false := by
  simp [RootTemplateMatch.intrusionLicensed]

/-- Intruder-free matches are licensed in any morphosyntactic context. -/
theorem intrusionLicensed_of_no_intruder (m : RootTemplateMatch α)
    (h : m.hasIntruder = false) (licensed : Bool) :
    m.intrusionLicensed licensed = true := by
  simp [RootTemplateMatch.intrusionLicensed, h]

/-- An intruder-bearing match is licensed iff the external predicate is
    `true` — the contrapositive that delivers the verbal/nominal split. -/
theorem intrusionLicensed_with_intruder (m : RootTemplateMatch α)
    (h : m.hasIntruder = true) (licensed : Bool) :
    m.intrusionLicensed licensed = licensed := by
  simp [RootTemplateMatch.intrusionLicensed, h]

-- ============================================================================
-- § 5: *Misalignment as an Alignment Constraint
-- ============================================================================

/-- The \*Misalignment constraint of @cite{faust-2026} (2): a markedness
    constraint that fires on `RootTemplateMatch` candidates whose
    `isMisaligned` predicate is true. Built via the generic `mkAlign`
    constructor from `Phonology.Constraints`. -/
def starMisalign {α : Type} : NamedConstraint (RootTemplateMatch α) :=
  mkAlign "*Misalign" RootTemplateMatch.isMisaligned

/-- \*Misalignment is classified as markedness, not faithfulness. -/
theorem starMisalign_is_markedness {α : Type} :
    (starMisalign (α := α)).family = .markedness := rfl

/-- The FILL constraint (@cite{prince-smolensky-1993}): a markedness
    constraint penalizing unfilled C-slots in the template. Used by
    @cite{faust-2026}'s implicit ranking \*Misalign >> FILL: spreading
    a nonfinal root segment to a final [+c] slot satisfies FILL but
    violates \*Misalign, and the grammar prefers the FILL-violating
    candidate. -/
def fill {α : Type} : NamedConstraint (RootTemplateMatch α) :=
  Phonology.Constraints.mkMark "FILL"
    (fun m => !RootTemplateMatch.allCSlotsFilled m)

/-- FILL is classified as markedness. -/
theorem fill_is_markedness {α : Type} :
    (fill (α := α)).family = .markedness := rfl

/-- NoCross (@cite{goldsmith-1976}): a markedness constraint penalizing
    candidates whose intruder associations cross root associations. -/
def noCross {α : Type} : NamedConstraint (RootTemplateMatch α) :=
  Phonology.Constraints.mkMark "NoCross" RootTemplateMatch.violatesNCC

/-- NoCross is classified as markedness. -/
theorem noCross_is_markedness {α : Type} :
    (noCross (α := α)).family = .markedness := rfl

end Phonology.Templates
