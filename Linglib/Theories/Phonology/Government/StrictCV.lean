/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

/-!
# Strict CV Government Phonology — Proper Government, ECP, Licensing
@cite{kaye-lowenstamm-vergnaud-1985} @cite{kaye-lowenstamm-vergnaud-1990}
@cite{charette-1991} @cite{lowenstamm-1996} @cite{scheer-2004}
@cite{scheer-segeral-2001}

Government Phonology (GP) and its Strict-CV (CVCV) descendant
(@cite{lowenstamm-1996}, @cite{scheer-2004}) build phonological
representations as alternating C-V skeletal sequences, with three
core lateral relations between V-slots:

* **Proper Government** (@cite{kaye-lowenstamm-vergnaud-1990}): a
  contentful nucleus governs a preceding empty nucleus, allowing the
  empty nucleus to remain phonetically silent.
* **Empty Category Principle** (ECP, simplified): an empty nucleus
  may be phonetically non-interpreted iff it is properly governed.
* **Licensing** (@cite{scheer-segeral-2001}): a contentful nucleus
  licenses an adjacent position (typically the preceding onset)
  to bear lexical features.

The substrate here gives the **simplified** form of these definitions
used in @cite{faust-lampitelli-2026} (Tigrinya/Tigre guttural
synseresis), which acknowledges the simplification (paper n. 16).
The full GP literature gives more elaborate definitions (e.g.
@cite{charette-1991} adds licensee strength conditions); the simplified
form suffices for the Faust & Lampitelli analysis.

## What this file does NOT define

* **Self-licensing domains** (@cite{faust-lampitelli-2026} eq. 25, 28).
  The "licensing overrides government" stipulation (paper n. 18: "this
  cannot be a general principle in Strict CV") is **paper-specific**
  apparatus and lives in `Studies/FaustLampitelli2026.lean`,
  not here.
* **Templatic structure** (root-template association, *Misalignment).
  That lives in `Theories/Phonology/Prosodic/Templates.lean`, anchored
  on @cite{mccarthy-1981} + @cite{lowenstamm-1996} + @cite{faust-2026}.
  The two substrates are siblings: CV templates carry slot kinds
  (`C | V | Cspec`); CV sequences here carry per-V-slot melodic status
  (`full | empty`). They are different abstractions over CV skeletons,
  consumed by different paper traditions.
* **Coda Mirror** (@cite{scheer-segeral-2001}, @cite{scheer-zikova-2010}).
  The coda-licensing apparatus is a downstream extension, deferred
  until a study consumer arrives.
-/

namespace Phonology.Government

-- ============================================================================
-- § 1: V-slot status
-- ============================================================================

/-- A V-slot's melodic status. Per Strict CV (@cite{lowenstamm-1996}),
    every consonant-cluster representation interpolates empty V-slots,
    so the same skeletal position may surface silently if properly
    governed, or with an epenthetic vowel if not.

    This is **distinct** from `Phonology.Templates.CVSlot` (which
    distinguishes `C | V | Cspec` slot *kinds* on the skeleton); a
    `VStatus` annotates a known V-position with melodic-content data,
    which the kind-only `CVSlot` does not carry. The two abstractions
    are siblings, not duplicates. -/
inductive VStatus where
  /-- The V-slot has melodic content (an associated vowel or |A|
      element from a guttural's representation). -/
  | full
  /-- The V-slot has no melodic content. Whether it surfaces as
      silent or as an epenthetic vowel is determined by Proper
      Government + ECP. -/
  | empty
  deriving DecidableEq, Repr

namespace VStatus

/-- The V-slot status is `.full`. -/
def IsFull : VStatus → Prop
  | .full  => True
  | .empty => False

instance : DecidablePred IsFull
  | .full  => isTrue trivial
  | .empty => isFalse not_false

/-- The V-slot status is `.empty`. -/
def IsEmpty : VStatus → Prop
  | .empty => True
  | .full  => False

instance : DecidablePred IsEmpty
  | .empty => isTrue trivial
  | .full  => isFalse not_false

end VStatus

-- ============================================================================
-- § 2: CV sequences
-- ============================================================================

/-- A **Strict-CV sequence** is a list of V-slot statuses. C-slots are
    implicit between each pair (Strict-CV convention,
    @cite{lowenstamm-1996}). The list `[v₁, v₂, v₃]` represents the
    skeleton `C₁ V₁ C₂ V₂ C₃ V₃`. -/
structure CVSeq where
  /-- Per-V-slot melodic status, indexed left-to-right. -/
  vStatus : List VStatus
  deriving Repr, DecidableEq

namespace CVSeq

/-- The number of V-slots in this sequence. -/
def vCount (s : CVSeq) : Nat := s.vStatus.length

/-- The V-slot status at index `i`, if in range. -/
def vAt (s : CVSeq) (i : Nat) : Option VStatus := s.vStatus[i]?

/-- Construct a sequence from a list (convenience). -/
def ofList (vs : List VStatus) : CVSeq := ⟨vs⟩

end CVSeq

-- ============================================================================
-- § 3: Proper Government
-- ============================================================================

/-- **Proper Government** (@cite{kaye-lowenstamm-vergnaud-1990},
    simplified per @cite{faust-lampitelli-2026} eq. 23a): the V-slot
    at index `i` is *properly governed* iff the immediately following
    V-slot (index `i+1`) exists and is *contentful* (`.full`).

    Per the paper's simplification (n. 16): adjacency is on the
    nuclear projection — i.e., adjacent in the V-slot indexing — and
    the governor must be contentful. This excludes a long-distance
    governor and an empty governor. -/
def CVSeq.ProperlyGoverned (s : CVSeq) (i : Nat) : Prop :=
  s.vAt (i + 1) = some .full

instance (s : CVSeq) (i : Nat) : Decidable (s.ProperlyGoverned i) :=
  inferInstanceAs (Decidable (s.vAt (i + 1) = some .full))

/-- **Empty Category Principle** (@cite{kaye-1992}, simplified per
    @cite{faust-lampitelli-2026} eq. 23b): an empty V-slot may surface
    silently iff it is properly governed; a non-empty (full) V-slot is
    always realized; out-of-range positions vacuously hold. -/
def CVSeq.ECPSatisfied (s : CVSeq) (i : Nat) : Prop :=
  match s.vAt i with
  | some .empty => s.ProperlyGoverned i
  | _           => True

instance (s : CVSeq) (i : Nat) : Decidable (s.ECPSatisfied i) := by
  unfold CVSeq.ECPSatisfied
  split <;> infer_instance

-- ============================================================================
-- § 4: Licensing
-- ============================================================================

/-- **Licensing** (@cite{scheer-segeral-2001}, simplified per
    @cite{faust-lampitelli-2026} eq. 24): the V-slot at index `i`
    *licenses* its preceding C-position iff `i` is contentful
    (`.full`). A licensed C-position can be associated with lexical
    features.

    Per the paper's simplification (eq. 24): "Licensing is a
    strengthening lateral force emanating from a full nucleus and
    targeting either its onset or the preceding nucleus." This file
    captures the onset-licensing direction; the preceding-nucleus
    direction is exercised by paper-specific self-licensing apparatus
    in study files. -/
def CVSeq.LicensesPrecedingC (s : CVSeq) (i : Nat) : Prop :=
  s.vAt i = some .full

instance (s : CVSeq) (i : Nat) : Decidable (s.LicensesPrecedingC i) :=
  inferInstanceAs (Decidable (s.vAt i = some .full))

-- ============================================================================
-- § 5: Basic Properties
-- ============================================================================

/-- An empty nucleus that is *not* properly governed violates ECP.
    Direct consequence of `ECPSatisfied`'s definition: on `.empty` the
    predicate reduces to `ProperlyGoverned`. -/
theorem CVSeq.empty_not_governed_violates_ecp (s : CVSeq) (i : Nat)
    (hempty : s.vAt i = some .empty) (hpg : ¬ s.ProperlyGoverned i) :
    ¬ s.ECPSatisfied i := by
  unfold ECPSatisfied
  rw [hempty]
  exact hpg

/-- A full nucleus is always ECP-satisfied (vacuous). -/
theorem CVSeq.full_ecp_satisfied (s : CVSeq) (i : Nat)
    (hfull : s.vAt i = some .full) :
    s.ECPSatisfied i := by
  unfold ECPSatisfied
  rw [hfull]
  trivial

end Phonology.Government
