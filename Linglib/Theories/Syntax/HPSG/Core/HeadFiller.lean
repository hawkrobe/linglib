import Linglib.Theories.Syntax.HPSG.Core.Basic

/-!
# Head-Filler Schema and SLASH Feature
@cite{ginzburg-sag-2000} @cite{pollard-sag-1994} @cite{mueller-2013}

HPSG's third combination schema: the Head-Filler Schema handles long-distance
dependencies (extraction, wh-movement). A filler XP combines with a sentence
containing a gap (SLASH feature) of matching category.

Together with Head-Complement and Head-Subject (in Basic.lean), this completes
HPSG's three immediate dominance schemata.

## Key types

- `SlashValue` — the set of categories expected to fill gaps
- `SynsemSlash` — extends `Synsem` with SLASH
- `HeadFillerRule` — filler combines with `S[SLASH {XP}]`, discharging the gap
- `HPSGSchema` — unifies all three schemata
- `TrackedSign` — sign paired with its SLASH value
- `GapRestriction` — island constraints via GAP restrictions

## Connection to @cite{mueller-2013}

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

In HPSG, all nominals share a single head type (noun). Our UD-based system
distinguishes NOUN, PRON, and PROPN. For SLASH matching, these are compatible. -/

/-- Are two categories compatible for SLASH matching?
All nominal categories (NOUN, PRON, PROPN) match each other. -/
def categoriesMatch (c1 c2 : UD.UPOS) : Bool :=
  let isNom (c : UD.UPOS) : Bool := c == .NOUN || c == .PRON || c == .PROPN
  if isNom c1 && isNom c2 then true
  else c1 == c2

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

/-! ## Head-Filler Schema -/

/-- Head-Filler Schema: filler XP combines with a clause containing a gap.

Schema 3:
```
       S
      / \
   XP S[SLASH {XP}]
(filler) (head)
```

The filler's category must match one of the gaps in the head's SLASH set.
The result has that gap discharged from SLASH. -/
structure HeadFillerRule where
  /-- The filler phrase (the extracted constituent) -/
  filler : Sign
  /-- The head phrase (sentence with a gap) -/
  headPhrase : Sign
  /-- The SLASH value on the head phrase before combination -/
  headSlash : SlashValue
  /-- The result phrase -/
  result : Sign
  /-- The filler's category matches a gap in the head -/
  slashMatch : headSlash.contains (filler.synsem.cat) = true
  /-- The result has the gap discharged -/
  resultSlash : SlashValue := headSlash.discharge (filler.synsem.cat)

/-! ## Unified schema type -/

/-- All four HPSG immediate dominance schemata, unified.

This inductive covers the complete set of phrase structure schemata
needed for HPSG phrase building. @cite{mueller-2013} argues the first three
correspond to three universal combination modes; Head-Modifier handles
adjunction (relative clauses, adjective/PP modification). -/
inductive HPSGSchema where
  /-- Head-Complement: head combines with complements (Schema 1) -/
  | headComp : HeadCompRule → HPSGSchema
  /-- Head-Subject: subject combines with head phrase (Schema 2) -/
  | headSubj : HeadSubjRule → HPSGSchema
  /-- Head-Filler: filler combines with gapped clause (Schema 3) -/
  | headFiller : HeadFillerRule → HPSGSchema
  /-- Head-Modifier: head combines with a modifier (Schema 4) -/
  | headMod : HeadModRule → HPSGSchema

/-- Get the result sign from any schema application. -/
def HPSGSchema.result : HPSGSchema → Sign
  | .headComp r => r.result
  | .headSubj r => r.result
  | .headFiller r => r.result
  | .headMod r => r.result

/-- Get the head sign from any schema application. -/
def HPSGSchema.head : HPSGSchema → Sign
  | .headComp r => r.head
  | .headSubj r => r.headPhrase
  | .headFiller r => r.headPhrase
  | .headMod r => r.headSign

/-! ## Gap Introduction (Argument Realization Principle)

Per @cite{sag-wasow-bender-2003} Ch. 6, a gap arises when one of a word's
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

@cite{sag-wasow-bender-2003} Ch. 6: In a headed phrase, the mother's SLASH
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
-- Key Properties
-- ============================================================================

/-- The head's category propagates to the result (Head Feature Principle).

In all three schemata, the category of the result phrase equals the
category of the head daughter. This is the HPSG analogue of the
Minimalist labeling algorithm. -/
theorem head_determines_cat_headComp (r : HeadCompRule) :
    r.result.synsem.cat = r.head.synsem.cat :=
  r.hfp

/-- When constructing a HeadFillerRule with the default resultSlash,
the gap matching the filler is discharged. -/
theorem slash_discharged_default (filler headPhrase result : Sign) (headSlash : SlashValue)
    (slashMatch : headSlash.contains (filler.synsem.cat) = true) :
    ({ filler, headPhrase, headSlash, result, slashMatch : HeadFillerRule}).resultSlash
      = headSlash.discharge (filler.synsem.cat) := rfl

-- ============================================================================
-- GAP Restrictions and Island Constraints (@cite{hofmeister-sag-2010})
-- ============================================================================

/-! ### Islands as GAP restrictions

@cite{hofmeister-sag-2010} argues that island constraints are construction-specific
restrictions on the GAP value, not universal Subjacency. This eliminates
the need for a separate island module in the grammar.

- **Absolute islands**: `[GAP ⟨⟩]` on the mother — no F-G dependency can
  penetrate (topicalization, exclamatives)
- **Weak islands**: `[GAP list(NP)]` — only NP gaps pass through
  (e.g., wh-islands allow NP extraction but not PP)
- **Unrestricted**: any GAP value permeates (no island constraint) -/

/-- GAP restriction on a construction.

This classifies constructions by what kinds of gaps they permit,
deriving island effects from the same feature system used for
non-island dependencies. -/
inductive GapRestriction where
  | unrestricted  -- Any GAP value (not an island)
  | npOnly        -- [GAP list(NP)] — weak island (only NP extraction)
  | noGap         -- [GAP ⟨⟩] — absolute barrier to extraction
  deriving Repr, DecidableEq, BEq

/-- Does this GAP restriction block all extraction? -/
def GapRestriction.isAbsoluteIsland : GapRestriction → Bool
  | .noGap => true
  | _ => false

/-- Does this GAP restriction allow NP extraction? -/
def GapRestriction.allowsNPExtraction : GapRestriction → Bool
  | .unrestricted => true
  | .npOnly => true
  | .noGap => false

/-- A SLASH value satisfies a GAP restriction if all its gaps are
permitted by the restriction. -/
def SlashValue.satisfiesRestriction (sv : SlashValue) (r : GapRestriction) : Bool :=
  match r with
  | .unrestricted => true
  | .npOnly => sv.gaps.all (· == .NOUN)
  | .noGap => sv.gaps.isEmpty

/-- Empty SLASH always satisfies any restriction. -/
theorem empty_satisfies_any_restriction (r : GapRestriction) :
    SlashValue.empty.satisfiesRestriction r = true := by
  cases r <;> rfl

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
private def see_word : Word := ⟨"see", .VERB, { valence := some .transitive }⟩
private def see_synsem : Synsem :=
  { cat := .VERB, val := { subj := [.NOUN], comps := [.NOUN] } }

private def john_word : Word := ⟨"John", .PROPN, { number := some .sg }⟩
private def what_word : Word := ⟨"what", .PRON, { wh := true }⟩

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
  native_decide

end DerivationExamples

-- ============================================================================
-- Island Blocking
-- ============================================================================

/-! ### Islands block SLASH propagation

When a construction has a GAP restriction of `.noGap`, no SLASH values
can percolate through it. This blocks extraction from islands.

Example: "*What did John wonder who saw ___?"
- The embedded question "who saw ___" has SLASH {NP}
- But the embedded question construction has [GAP ⟨⟩] (`.noGap`)
- SLASH cannot pass through → extraction blocked
-/

section IslandBlocking

/-- Check that a SLASH value can propagate through a construction.
Returns the SLASH that survives the restriction. -/
def propagateSlash (sv : SlashValue) (restriction : GapRestriction) : SlashValue :=
  if sv.satisfiesRestriction restriction then sv
  else .empty

-- Extraction from a non-island succeeds: SLASH passes through
#guard (propagateSlash ⟨[.NOUN]⟩ .unrestricted).gaps == [.NOUN]

-- Extraction from an absolute island fails: SLASH is blocked
#guard (propagateSlash ⟨[.NOUN]⟩ .noGap).isEmpty

-- Extraction of NP from a weak island succeeds
#guard (propagateSlash ⟨[.NOUN]⟩ .npOnly).gaps == [.NOUN]

-- But extraction of PP from a weak island fails
#guard (propagateSlash ⟨[.ADP]⟩ .npOnly).isEmpty

/-- Extraction from a non-island construction always succeeds. -/
theorem extraction_from_nonisland (c : UD.UPOS) :
    (propagateSlash ⟨[c]⟩ .unrestricted).gaps = [c] := by
  simp [propagateSlash, SlashValue.satisfiesRestriction]

/-- Extraction from an absolute island is always blocked. -/
theorem extraction_blocked_by_island (gaps : List UD.UPOS) (h : gaps ≠ []) :
    (propagateSlash ⟨gaps⟩ .noGap).isEmpty = true := by
  simp [propagateSlash, SlashValue.satisfiesRestriction, SlashValue.isEmpty]
  cases gaps with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

end IslandBlocking

end HPSG
