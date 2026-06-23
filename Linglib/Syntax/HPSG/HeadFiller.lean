import Linglib.Syntax.HPSG.Basic
import Linglib.Syntax.HPSG.Categories

/-!
# Head-Filler Schema and SLASH Feature
[ginzburg-sag-2000] [pollard-sag-1994] [mueller-2013]

HPSG's third combination schema: the Head-Filler Schema handles long-distance
dependencies (extraction, wh-movement). A filler XP combines with a sentence
containing a gap (SLASH feature) of matching category.

This schema is realized **dynamically** through the SLASH feature: a gap is introduced
(`gapComplement`), amalgamated up the tree (`amalgamateHead*`), and discharged when a filler
combines with the gapped clause (`SlashValue.dischargeCompatible`). The head-complement and
head-subject schemata are the model-theoretic construct hierarchy of `Syntax/HPSG/Construction`.

## Key types

- `SlashValue` — the set of categories expected to fill gaps
- `SynsemSlash` — extends `Synsem` with SLASH
- `TrackedSign` — sign paired with its SLASH value

Islands are **not** modeled here: the model-theoretic `[GAP ⟨⟩]` island taxonomy lives over the
canonical RSRL signature (`Syntax/HPSG/Construction`, consumed by `Studies/SagWasowBender2003` and
`Studies/Sag2010`), which subsumes the former coarse `GapRestriction` enum.

## Connection to [mueller-2013]

Müller §2.3: "the formalization of internal Merge and that of the head-filler
schema are very similar" — both handle displacement by pairing a moved element
with its extraction site.

-/

namespace HPSG

/-! ## SLASH features -/

/-- The SLASH value: a set of categories for which gaps exist.

In HPSG, SLASH is a set-valued feature on phrases. A phrase with
`SLASH {NP}` contains an NP gap somewhere inside it. The Head-Filler
schema discharges one element from this set. -/
structure SlashValue where
  /-- Categories of gaps in this phrase -/
  gaps : List UD.UPOS
  deriving Repr, DecidableEq

/-- Empty SLASH value (no gaps). -/
def SlashValue.empty : SlashValue := ⟨[]⟩

/-- Check if SLASH contains a specific category. -/
def SlashValue.contains (sv : SlashValue) (c : UD.UPOS) : Bool :=
  sv.gaps.contains c

/-- Remove a category from SLASH (when a gap is filled). -/
def SlashValue.discharge (sv : SlashValue) (c : UD.UPOS) : SlashValue :=
  ⟨sv.gaps.erase c⟩

/-- Is this SLASH value empty (no gaps)? -/
def SlashValue.isEmpty (sv : SlashValue) : Bool :=
  sv.gaps.isEmpty

/-- Union of two SLASH values. -/
def SlashValue.union (s1 s2 : SlashValue) : SlashValue :=
  ⟨s1.gaps ++ s2.gaps⟩

instance : BEq SlashValue where
  beq a b := a.gaps == b.gaps

/-! ## Nominal Category Compatibility

Category compatibility for SLASH matching is `categoriesMatch` (`Syntax/HPSG/Categories`), grounded in
the HPSG cat hierarchy via `udToCat`: all nominals (`NOUN`/`PRON`/`PROPN` → `noun`) match each other. -/

/-- Check if SLASH contains a compatible category (using nominal matching). -/
def SlashValue.containsCompatible (sv : SlashValue) (c : UD.UPOS) : Bool :=
  sv.gaps.any (categoriesMatch c)

/-- Discharge a compatible category from SLASH. -/
def SlashValue.dischargeCompatible (sv : SlashValue) (c : UD.UPOS) : SlashValue :=
  match sv.gaps.findIdx? (categoriesMatch c) with
  | some idx => ⟨sv.gaps.eraseIdx idx⟩
  | none => sv

/-! ## Extended SYNSEM with SLASH -/

/-- Extended SYNSEM value including the SLASH feature.

This extends the basic `Synsem` from HPSG.Basic with nonlocal features. -/
structure SynsemSlash where
  /-- Local syntax-semantics features -/
  local_ : Synsem
  /-- Nonlocal SLASH feature (gap set) -/
  slash : SlashValue := .empty
  deriving Repr

/-- Get the category from an extended synsem. -/
def SynsemSlash.cat (ss : SynsemSlash) : UD.UPOS := ss.local_.cat

/-! ## Gap Introduction (Argument Realization Principle)

Per [sag-wasow-bender-2003] Ch. 6, a gap arises when one of a word's
ARG-ST elements is realized as GAP rather than COMPS. The GAP value becomes
the word's local SLASH contribution.

    ARG-ST = SPR ⊕ COMPS ⊕ GAP

A verb with ARG-ST ⟨NP_subj, NP_obj⟩ can realize as:
- Normal: SPR ⟨NP_subj⟩, COMPS ⟨NP_obj⟩, GAP ⟨⟩
- Gapped: SPR ⟨NP_subj⟩, COMPS ⟨⟩, GAP ⟨NP_obj⟩ → SLASH {NP}
-/

/-- Create a gapped version of a word sign: one complement is removed from
COMPS and becomes a SLASH element (via GAP).

Returns the gapped sign and the resulting SLASH value. -/
def gapComplement (w : Word) (ss : Synsem) (gapIdx : Nat) : Option (Sign × SlashValue) :=
  if h : gapIdx < ss.val.comps.length then
    let gapCat := ss.val.comps[gapIdx]
    let newComps := ss.val.comps.eraseIdx gapIdx
    let gappedSS := { ss with val := { ss.val with comps := newComps } }
    some (.word w gappedSS, ⟨[gapCat]⟩)
  else
    none

/-- A sign paired with its SLASH value.

Tracks the nonlocal SLASH feature alongside a locally-typed sign,
avoiding modification of the Sign type itself. -/
structure TrackedSign where
  sign : Sign
  slash : SlashValue := .empty
  deriving Repr

/-! ## SLASH Amalgamation (Nonlocal Feature Principle)

[sag-wasow-bender-2003] Ch. 6: In a headed phrase, the mother's SLASH
is the union of its daughters' SLASH values, minus any elements discharged
by the Head-Filler Schema. -/

/-- Amalgamate SLASH through Head-Complement: head's SLASH ∪ comp's SLASH. -/
def amalgamateHeadComp (head comp : TrackedSign) : TrackedSign :=
  { sign := head.sign
    slash := head.slash.union comp.slash }

/-- Amalgamate SLASH through Head-Subject: subject's SLASH ∪ head's SLASH. -/
def amalgamateHeadSubj (subj head : TrackedSign) : TrackedSign :=
  { sign := head.sign
    slash := subj.slash.union head.slash }

-- ============================================================================
-- GAP Restrictions and Island Constraints ([hofmeister-sag-2010])
-- ============================================================================

/-! ### Islands as GAP restrictions

[hofmeister-sag-2010] argues that island constraints are construction-specific
restrictions on the GAP value, not universal Subjacency. This eliminates
the need for a separate island module in the grammar.

- **Absolute islands**: `[GAP ⟨⟩]` on the mother — no F-G dependency can
  penetrate (topicalization, exclamatives)
- **Weak islands**: `[GAP list(NP)]` — only NP gaps pass through
  (e.g., wh-islands allow NP extraction but not PP)
- **Unrestricted**: any GAP value permeates (no island constraint) -/

-- ============================================================================
-- Derivation Examples
-- ============================================================================

/-! ### Object extraction: "What did John see ___?"

Derivation sketch:
1. "see" has COMPS ⟨NP⟩
2. Gap complement: COMPS ⟨⟩, SLASH {NP}
3. Head-Subject with "John": S[SLASH {NP}]
4. Head-Filler with "what": S[SLASH {}] — gap discharged
-/

section DerivationExamples

-- Lexical entries for the derivation
private def see_word : Word := { form :="see", cat := .VERB}
private def see_synsem : Synsem :=
  { cat := .VERB, val := { subj := [.NOUN], comps := [.NOUN] } }

private def john_word : Word := { form :="John", cat := .PROPN, features := { number := some .Sing }}
private def what_word : Word := { form :="what", cat := .PRON, features := { pronType := some .Int }}

-- Step 1: Gap the complement of "see"
-- gapComplement returns (gapped_sign, slash_value)
#guard (gapComplement see_word see_synsem 0).isSome

-- Extract the gapped sign and slash using match
private def gapped_sign : Sign :=
  match gapComplement see_word see_synsem 0 with
  | some (s, _) => s
  | none => .word see_word see_synsem  -- unreachable

private def gapped_slash : SlashValue :=
  match gapComplement see_word see_synsem 0 with
  | some (_, sv) => sv
  | none => .empty  -- unreachable

-- Verify: gap creates SLASH {NOUN} and removes the complement
#guard gapped_slash.gaps == [.NOUN]
#guard gapped_sign.synsem.val.comps == []
#guard gapped_sign.synsem.val.subj == [.NOUN]

-- Step 2: Track SLASH through Head-Subject
private def see_tracked : TrackedSign :=
  { sign := gapped_sign, slash := gapped_slash }

private def john_sign : Sign := .word john_word { cat := .PROPN }
private def john_tracked : TrackedSign :=
  { sign := john_sign, slash := .empty }

private def clause_tracked : TrackedSign :=
  amalgamateHeadSubj john_tracked see_tracked

-- After Head-Subject, SLASH {NP} persists (NFP)
#guard clause_tracked.slash.gaps == [.NOUN]

-- Step 3: "what" (PRON) can fill the NP gap (nominal compatibility)
#guard categoriesMatch .PRON .NOUN
#guard clause_tracked.slash.containsCompatible what_word.cat

-- Step 4: Head-Filler discharges the gap
private def result_slash : SlashValue :=
  clause_tracked.slash.dischargeCompatible what_word.cat

-- After Head-Filler, SLASH is empty — the dependency is complete
#guard result_slash.isEmpty

/-- Full end-to-end derivation: gap introduction → SLASH amalgamation →
Head-Filler discharge → empty SLASH. -/
theorem extraction_complete :
    result_slash.isEmpty = true := by
  decide

end DerivationExamples

end HPSG
