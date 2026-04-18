import Linglib.Core.Morphology.ConsonantalRoot
import Linglib.Theories.Phonology.Constraints

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
open Core.OT (NamedConstraint)
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
def isC : CVSlot → Bool
  | .C | .Cspec => true
  | .V => false

/-- Is this slot a V-slot? -/
def isV : CVSlot → Bool
  | .V => true
  | _ => false

/-- Does this slot require a [+consonantal] segment? -/
def requiresConsonantal : CVSlot → Bool
  | .Cspec => true
  | _ => false

end CVSlot

-- ============================================================================
-- § 2: Templates
-- ============================================================================

/-- A CV-skeletal template: an ordered sequence of slots. -/
structure Template where
  slots : List CVSlot
  deriving Repr

namespace Template

/-- The number of slots in the template. -/
def length (t : Template) : Nat := t.slots.length

/-- The number of C-slots (consonant timing positions). -/
def cCount (t : Template) : Nat := (t.slots.filter CVSlot.isC).length

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
  deriving Repr

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
    | some s => !s.isC || m.associations.any (·.slotIndex == i)
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
    cases hsrc : a.source <;> simp_all

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

end Phonology.Templates
