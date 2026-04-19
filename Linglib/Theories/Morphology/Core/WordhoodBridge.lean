import Linglib.Core.Morphology.Wordhood
import Linglib.Core.Lexical.MorphRule
import Linglib.Theories.Morphology.Core.CliticVsAffix
import Linglib.Theories.Phonology.Prosodic.Word

/-!
# Wordhood ↔ Clitic/Affix Diagnostic Bridge
@cite{zwicky-pullum-1983} @cite{kalin-bjorkman-etal-2026}

This module connects two independent formalizations:

- **Wordhood typology** (`Core.Morphology.Wordhood`): the two-dimensional
  classification from @cite{kalin-bjorkman-etal-2026} §3.2 crossing
  ms-boundedness (morphosyntactic) with p-boundedness (phonological/prosodic)
  to yield four wordhood classes (canonical word, simple clitic, non-cohering
  affix, canonical affix).

- **Clitic vs. affix diagnostics** (`Morphology.Diagnostics`): the six
  criteria from @cite{zwicky-pullum-1983} for determining whether a bound
  morpheme is an inflectional affix or a clitic.

The bridge: Zwicky & Pullum's criteria diagnose **ms-boundedness** — the
morphosyntactic dimension of the Wordhood typology. A morpheme that scores
affix-like on all six ZP criteria is ms-bound; one that scores clitic-like
is ms-free. The p-boundedness dimension is orthogonal (determined by
prosodic diagnostics, not the ZP criteria).
-/

namespace Morphology.WordhoodBridge

open Core.Morphology.Wordhood
open Core.Morphology (MorphStatus)
open Morphology.Diagnostics (CliticAffixProfile)

-- ============================================================================
-- §1: MorphStatus → MSBoundedness
-- ============================================================================

/-- Map a morpheme's morphological status to its ms-boundedness.

    The key mapping:
    - **Free words** are ms-free (they are independent ms-words).
    - **Clitics** (simple or special) are ms-free: they are
      syntactically independent despite being phonologically bound.
      This is the defining property of clitics in the
      @cite{kalin-bjorkman-etal-2026} framework.
    - **Affixes** (inflectional or derivational) are ms-bound: they
      must be internal to a host ms-word. -/
def morphStatusToMSBound : MorphStatus → MSBoundedness
  | .freeWord      => .free
  | .simpleClitic  => .free
  | .specialClitic => .free
  | .inflAffix     => .bound
  | .derivAffix    => .bound

-- ============================================================================
-- §2: Verification
-- ============================================================================

/-- Free words are ms-free. -/
theorem freeWord_is_ms_free :
    morphStatusToMSBound .freeWord = .free := rfl

/-- Simple clitics are ms-free (the defining property). -/
theorem simpleClitic_is_ms_free :
    morphStatusToMSBound .simpleClitic = .free := rfl

/-- Inflectional affixes are ms-bound. -/
theorem inflAffix_is_ms_bound :
    morphStatusToMSBound .inflAffix = .bound := rfl

/-- Derivational affixes are ms-bound. -/
theorem derivAffix_is_ms_bound :
    morphStatusToMSBound .derivAffix = .bound := rfl

-- ============================================================================
-- §3: ZP Diagnostics → MSBoundedness
-- ============================================================================

/-- A morpheme that is an unambiguous affix by the ZP criteria is
    ms-bound. This connects the *diagnostic procedure* (how you
    determine ms-boundedness empirically) to the *typological
    classification* (what that boundedness means). -/
theorem zpAffix_implies_ms_bound (p : CliticAffixProfile)
    (h : p.classify = .inflAffix) :
    morphStatusToMSBound p.classify = .bound := by
  simp [h, morphStatusToMSBound]

/-- A morpheme that is an unambiguous clitic by the ZP criteria is
    ms-free. -/
theorem zpClitic_implies_ms_free (p : CliticAffixProfile)
    (h : p.classify = .simpleClitic) :
    morphStatusToMSBound p.classify = .free := by
  simp [h, morphStatusToMSBound]

-- ============================================================================
-- §4: Wordhood Profile from MorphStatus + PBoundedness
-- ============================================================================

/-- Construct a full wordhood profile from a morpheme's MorphStatus
    (which determines ms-boundedness) and its prosodic boundedness
    (which must be determined independently, e.g., by phonological
    diagnostics).

    This is the function that connects the ZP diagnostic tradition
    to the @cite{kalin-bjorkman-etal-2026} wordhood typology. -/
def wordhoodProfile (status : MorphStatus) (prosody : PBoundedness) :
    WordhoodProfile :=
  ⟨morphStatusToMSBound status, prosody⟩

/-- A simple clitic (ms-free) that is p-bound classifies as
    `simpleClitic` in the wordhood typology. -/
theorem simpleClitic_p_bound_is_simpleClitic :
    (wordhoodProfile .simpleClitic .bound).classify = .simpleClitic := rfl

/-- An inflectional affix (ms-bound) that is p-bound classifies as
    `canonicalAffix` in the wordhood typology. -/
theorem inflAffix_p_bound_is_canonicalAffix :
    (wordhoodProfile .inflAffix .bound).classify = .canonicalAffix := rfl

/-- An inflectional affix (ms-bound) that is p-free classifies as
    `nonCoheringAffix` (e.g., Dutch non-cohering prefixes). -/
theorem inflAffix_p_free_is_nonCoheringAffix :
    (wordhoodProfile .inflAffix .free).classify = .nonCoheringAffix := rfl

/-- A free word that is p-free is a canonical word. -/
theorem freeWord_p_free_is_canonicalWord :
    (wordhoodProfile .freeWord .free).classify = .canonicalWord := rfl

-- ============================================================================
-- §5: Exhaustiveness
-- ============================================================================

/-- Every MorphStatus maps to a definite MSBoundedness. -/
theorem morphStatus_exhaustive (s : MorphStatus) :
    morphStatusToMSBound s = .free ∨ morphStatusToMSBound s = .bound := by
  cases s <;> simp [morphStatusToMSBound]

/-- Affixhood (in MorphStatus) is equivalent to ms-boundedness. -/
theorem affix_iff_ms_bound (s : MorphStatus) :
    s.isAffix = true ↔ morphStatusToMSBound s = .bound := by
  cases s <;> simp [MorphStatus.isAffix, morphStatusToMSBound]

/-- Clitichood (in MorphStatus) implies ms-freedom. -/
theorem clitic_implies_ms_free (s : MorphStatus) (h : s.isClitic = true) :
    morphStatusToMSBound s = .free := by
  cases s <;> simp_all [MorphStatus.isClitic, morphStatusToMSBound]

-- ============================================================================
-- §6: ProsodicWord → PBoundedness
-- ============================================================================

/-- Map PrWd membership to p-boundedness.

    Elements parsed inside the PrWd with the stem are p-bound
    (they don't form their own prosodic word). Elements that are
    PrWd-external are p-free (they form their own prosodic word,
    satisfying minimal word constraints independently).

    This connects `Phonology.ProsodicWord` (which provides
    phonological diagnostics for PrWd membership) to the p-boundedness
    dimension of the @cite{kalin-bjorkman-etal-2026} wordhood typology. -/
def prWdMembershipToPBound (isPrWdInternal : Bool) : PBoundedness :=
  if isPrWdInternal then .bound else .free

open Phonology.ProsodicWord in
/-- Inflectional suffixes are PrWd-internal → p-bound. -/
theorem inflectional_is_p_bound :
    prWdMembershipToPBound MorphStatus.inflectional.isPrWdInternal = .bound := rfl

open Phonology.ProsodicWord in
/-- Agreement markers are PrWd-internal → p-bound. -/
theorem agreement_is_p_bound :
    prWdMembershipToPBound MorphStatus.agreement.isPrWdInternal = .bound := rfl

open Phonology.ProsodicWord in
/-- Derivational affixes are PrWd-internal → p-bound. -/
theorem derivational_is_p_bound :
    prWdMembershipToPBound MorphStatus.derivational.isPrWdInternal = .bound := rfl

open Phonology.ProsodicWord in
/-- Postpositions are PrWd-external → p-free. -/
theorem postposition_is_p_free :
    prWdMembershipToPBound MorphStatus.postposition.isPrWdInternal = .free := rfl

-- ============================================================================
-- §7: Full Wordhood from ZP Diagnostics + PrWd Diagnostics
-- ============================================================================

open Phonology.ProsodicWord in
/-- An inflectional affix (ms-bound by ZP criteria) that is also
    PrWd-internal (p-bound by prosodic diagnostics) is a canonical
    affix — the prototypical affix that is internal to its host on
    both dimensions. Example: English *-ed*, Telugu case suffixes. -/
theorem inflAffix_prWdInternal_is_canonicalAffix :
    (wordhoodProfile .inflAffix
      (prWdMembershipToPBound MorphStatus.inflectional.isPrWdInternal)
    ).classify = .canonicalAffix := rfl

open Phonology.ProsodicWord in
/-- A postposition (ms-free by ZP criteria) that is PrWd-external
    (p-free by prosodic diagnostics) is a canonical word — independent
    on both dimensions. Example: Telugu postpositions. -/
theorem postposition_prWdExternal_is_canonicalWord :
    (wordhoodProfile .freeWord
      (prWdMembershipToPBound MorphStatus.postposition.isPrWdInternal)
    ).classify = .canonicalWord := rfl

end Morphology.WordhoodBridge
