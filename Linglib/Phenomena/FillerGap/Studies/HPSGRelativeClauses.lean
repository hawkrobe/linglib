import Linglib.Theories.Syntax.HPSG.Core.RelativeClauses
import Linglib.Phenomena.FillerGap.LongDistance

/-!
# Bridge: HPSG Relative Clauses to Filler-Gap Phenomena
@cite{sag-wasow-bender-2003} @cite{pollard-sag-1994}

Connects the HPSG relative clause mechanism (MOD feature + SLASH/GAP
+ Head-Modifier Schema) to empirical data in `Phenomena.FillerGap`.

## Main results

- `object_relative_licensed`: object relatives derive via complement
  gap + relativizer + Head-Modifier
- `subject_relative_licensed`: subject relatives derive via subject
  gap + relativizer + Head-Modifier
- `relClause_always_modifies`: every relative clause derivation
  produces a modifier (has MOD set)
- `modification_preserves_head_cat`: Head-Modifier preserves the
  head noun's category
-/

namespace HPSGRelativeClauses

open HPSG
open HPSG.RelativeClauses

-- ============================================================================
-- Relative Clause Licensing
-- ============================================================================

/-- Configuration for a relative clause dependency. -/
structure RelClauseConfig where
  /-- Category of the head noun being modified -/
  headCat : UD.UPOS
  /-- Category of the gap inside the clause -/
  gapCat : UD.UPOS
  /-- The relativizer used -/
  rel : Relativizer

/-- Is this relative clause configuration licensed?

A relative clause is licensed when:
1. There is a gap in the clause (modeled by gapCat)
2. The relativizer produces a modifier for the head noun's category
3. The MOD value matches the head noun -/
def relClauseLicensed (cfg : RelClauseConfig) : Bool :=
  -- The relativizer must target the right category
  categoriesMatch cfg.rel.modifiesCat cfg.headCat &&
  -- There must be a gap to fill
  cfg.gapCat != .X

-- ============================================================================
-- Object Relative Clauses
-- ============================================================================

/-- Object relative with "that": "the book that John read ___"
NP head, NP gap in object position, "that" relativizer. -/
def objectRelThat : RelClauseConfig :=
  { headCat := .NOUN, gapCat := .NOUN, rel := relThat }

/-- Object relative with "which": "the book which John read ___" -/
def objectRelWhich : RelClauseConfig :=
  { headCat := .NOUN, gapCat := .NOUN, rel := relWhich }

-- Object relatives are licensed
#guard relClauseLicensed objectRelThat
#guard relClauseLicensed objectRelWhich

-- ============================================================================
-- Subject Relative Clauses
-- ============================================================================

/-- Subject relative with "who": "the boy who saw Mary"
NP head, NP gap in subject position, "who" relativizer. -/
def subjectRelWho : RelClauseConfig :=
  { headCat := .NOUN, gapCat := .NOUN, rel := relWho }

/-- Subject relative with "that": "the boy that saw Mary" -/
def subjectRelThat : RelClauseConfig :=
  { headCat := .NOUN, gapCat := .NOUN, rel := relThat }

-- Subject relatives are licensed
#guard relClauseLicensed subjectRelWho
#guard relClauseLicensed subjectRelThat

-- ============================================================================
-- PP Relative Clauses
-- ============================================================================

/-- PP relative: "the person who(m) John talked to ___"
NP head, PP gap (prep stranded), "who" relativizer. -/
def ppRelWho : RelClauseConfig :=
  { headCat := .NOUN, gapCat := .ADP, rel := relWho }

-- PP relatives are licensed (gap is PP but head is still NP)
#guard relClauseLicensed ppRelWho

-- ============================================================================
-- Connecting to Phenomena Data
-- ============================================================================

/-- Object relative clause data matches HPSG derivation.

The empirical observation (from `LongDistance.relativeClauseData`):
  "the book that John reads" ✓
is licensed by the HPSG derivation:
  gap(read, obj) → S[GAP ⟨NP⟩] → that + S[GAP ⟨NP⟩] → [MOD NP]
  → book + [MOD NP] → NP -/
theorem object_relative_licensed :
    relClauseLicensed objectRelThat = true ∧
    relClauseLicensed objectRelWhich = true := by
  native_decide

/-- Subject relative clause data matches HPSG derivation.

The empirical observation:
  "the boy that sees Mary" ✓
is licensed by the HPSG derivation:
  gap(see, subj) → S[GAP ⟨NP⟩] → that + S[GAP ⟨NP⟩] → [MOD NP]
  → boy + [MOD NP] → NP -/
theorem subject_relative_licensed :
    relClauseLicensed subjectRelWho = true ∧
    relClauseLicensed subjectRelThat = true := by
  native_decide

/-- Every relative clause derivation produces a modifier (has MOD set). -/
theorem relClause_always_modifies (d : RelClauseDerivation) :
    d.result.sign.synsem.mod.isSome = true := by
  simp [RelClauseDerivation.result, Sign.synsem]

/-- The Head-Modifier Schema preserves the head noun's category.

This is the Head Feature Principle applied to Head-Modifier structures:
when a relative clause modifies a noun, the result is still a noun. -/
theorem modification_preserves_head_cat (headNoun : Sign)
    (relClause : TrackedSign) (result : Sign)
    (hMod : relClauseModifies headNoun relClause = some result) :
    result.synsem.cat = headNoun.synsem.cat :=
  headMod_preserves_cat headNoun relClause result hMod

end HPSGRelativeClauses
