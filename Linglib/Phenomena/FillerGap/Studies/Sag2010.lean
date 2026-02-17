/-
# Filler-Gap Construction Typology

Parametric variation across the five types of English filler-gap clauses,
following Sag (2010). The core empirical contribution: F-G clauses share
a common filler–gap structure but differ systematically along 7 parameters.

## The Five F-G Clause Types (§2.1, examples 1–5)

1. Wh-interrogative: "How foolish is he?" / "I wonder how foolish he is."
2. Wh-exclamative: "What a fool he is!" / "It's amazing how odd it is."
3. Topicalized: "The bagels, I like."
4. Wh-relative: "the person who they nominated"
5. The-clause: "The more people I met, the happier I became."

## References

- Sag, I.A. (2010). English filler-gap constructions. Language 86(3):486–545.
- Ginzburg, J. & Sag, I.A. (2000). Interrogative Investigations.
- Hofmeister, P. & Sag, I.A. (2010). Cognitive constraints and island effects.
-/

import Linglib.Phenomena.FillerGap.Islands.Data

namespace Phenomena.FillerGap.Studies.Sag2010

-- ============================================================================
-- F-G Clause Types
-- ============================================================================

/-- The five types of English filler-gap clause (Sag 2010, §2.1). -/
inductive FGClauseType where
  | whInterrogative  -- "Who did they visit?" / "I wonder who they visited."
  | whExclamative    -- "What a fool he is!" / "It's amazing how odd it is."
  | topicalized      -- "The bagels, I like."
  | whRelative       -- "the person who they nominated"
  | theClause        -- "The more people I met, the happier I became."
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- Parameters of Variation (§2.1, example 6)
-- ============================================================================

/-- What kind of distinguished wh-element appears in the filler daughter.
(§2.1, parameter 6a) -/
inductive FillerWhType where
  | none           -- No wh-element (topicalization)
  | interrogative  -- Interrogative wh (who, what, which N, how)
  | exclamative    -- Exclamative wh (what!, how!)
  | relative       -- Relative wh (who, whose, which, where)
  | the            -- Definite degree marker "the" (the-clause)
  deriving Repr, DecidableEq, BEq

/-- Constraints on head daughter inversion (§2.1, parameter 6d / example 28). -/
inductive InversionRequirement where
  | required     -- Must be inverted (matrix wh-interrogatives)
  | prohibited   -- Must not be inverted (topicalization, relative, exclamative)
  | optional     -- Optionally inverted (noninitial the-clause)
  deriving Repr, DecidableEq, BEq

/-- Whether head daughter can be infinitival (§2.1, parameter 6d / example 29). -/
inductive Finiteness where
  | finiteOnly           -- Always finite (topicalization, exclamative, the-clause)
  | infinitivalPossible  -- VP[inf] head daughter possible (interrogative, relative)
  deriving Repr, DecidableEq, BEq

/-- Semantic type of the clause (§2.1, example 30; follows G&S 2000). -/
inductive FGSemanticType where
  | question   -- Set of propositions (wh-interrogative)
  | fact       -- Fact: related to but distinct from proposition (exclamative)
  | austinean  -- Proposition or outcome (topicalization, the-clause)
  | modifier   -- Property: λx[...] (wh-relative modifies a CNP)
  deriving Repr, DecidableEq, BEq

/-- Whether the clause must/can be independent (§2.1, parameter 6g / example 31). -/
inductive Independence where
  | required    -- Must be independent (topicalized, matrix wh-interrogative)
  | prohibited  -- Must be embedded (relative)
  | either      -- Can be either (exclamative, embedded interrogative, the-clause)
  deriving Repr, DecidableEq, BEq

/-- The 7 parameters of variation across F-G clause types (§2.1, example 6).

Each parameter corresponds to a feature already formalized elsewhere in linglib;
the bridge theorems below verify consistency. -/
structure FGParameters where
  /-- (6a) What wh-element in the filler? -/
  fillerWhType : FillerWhType
  /-- (6d) Must/can head be inverted? -/
  headInversion : InversionRequirement
  /-- (6d) Can head be infinitival? -/
  headFiniteness : Finiteness
  /-- (6e) Semantic type of the clause -/
  semanticType : FGSemanticType
  /-- (6f) Is this an extraction island? -/
  isIsland : Bool
  /-- (6g) Must this be independent? -/
  independence : Independence
  /-- (6b) Allowed filler categories (NP, PP, AP, AdvP, etc.) -/
  fillerIsNonverbal : Bool  -- true for all 5; topicalization also allows AdvP
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- Parameter Values for Each Construction
-- ============================================================================

/-- Wh-interrogative parameters (§5.3, constructions 80–81).
"Who did they visit?" — interrogative wh, inverted in matrix, question semantics. -/
def whInterrogativeParams : FGParameters :=
  { fillerWhType := .interrogative
    headInversion := .required     -- (28a): inverted only in independent clause
    headFiniteness := .infinitivalPossible  -- (29b): "I know how much time to take"
    semanticType := .question      -- (30a)
    isIsland := false              -- Sag: wh-interrogatives not extraction islands
    independence := .either        -- matrix: "Who left?" / embedded: "I wonder who left"
    fillerIsNonverbal := true }    -- (25a): NP, PP, AP, AdvP

/-- Wh-exclamative parameters (§5.2, construction 70).
"What a fool he is!" — exclamative wh, uninverted, fact semantics. -/
def whExclamativeParams : FGParameters :=
  { fillerWhType := .exclamative
    headInversion := .prohibited   -- (28b): never inverted
    headFiniteness := .finiteOnly  -- (29a): always finite
    semanticType := .fact          -- (30c): fact (G&S 2000)
    isIsland := true               -- (73–74): extraction island
    independence := .either        -- (71a): independent or embedded
    fillerIsNonverbal := true }    -- (76): NP, AP, AdvP, PP; not VP

/-- Topicalization parameters (§5.1, construction 61).
"The bagels, I like." — no wh, uninverted, austinean semantics. -/
def topicalizedParams : FGParameters :=
  { fillerWhType := .none
    headInversion := .prohibited   -- (28b): never inverted
    headFiniteness := .finiteOnly  -- (29a): always finite
    semanticType := .austinean     -- (30e): austinean (proposition or outcome)
    isIsland := true               -- (67): extraction island per [GAP ⟨⟩]
    independence := .required      -- (61): [IC +] required
    fillerIsNonverbal := true }    -- (25a/63): NP, PP, AP, AdvP

/-- Wh-relative parameters (§5.4, constructions 90–92).
"the person who they nominated" — relative wh, uninverted, modifier semantics. -/
def whRelativeParams : FGParameters :=
  { fillerWhType := .relative
    headInversion := .prohibited   -- (28b): never inverted
    headFiniteness := .infinitivalPossible  -- (29b/97): infinitival wh-relatives
    semanticType := .modifier      -- (30b/90): λPλx[...], modifies CNP
    isIsland := false              -- relatives allow further extraction (variable)
    independence := .prohibited    -- (91): must be embedded (modifies a noun)
    fillerIsNonverbal := true }    -- (25b/92): NP, PP (finite); PP only (infinitival)

/-- The-clause parameters (§5.5, construction 108).
"The more you read, the more you understand." — degree marker the, optional
inversion, austinean semantics. -/
def theClauseParams : FGParameters :=
  { fillerWhType := .the
    headInversion := .optional     -- (28c): optional inversion in noninitial clause
    headFiniteness := .finiteOnly  -- (29a): always finite
    semanticType := .austinean     -- (30d): austinean
    isIsland := false              -- no island constraint mentioned
    independence := .either        -- can be independent or embedded paratactically
    fillerIsNonverbal := true }    -- (25a): NP, PP, AP, AdvP

/-- Map each F-G clause type to its parameters. -/
def fgParams : FGClauseType → FGParameters
  | .whInterrogative => whInterrogativeParams
  | .whExclamative   => whExclamativeParams
  | .topicalized     => topicalizedParams
  | .whRelative      => whRelativeParams
  | .theClause       => theClauseParams

-- ============================================================================
-- Per-Datum Verification Theorems
-- ============================================================================

/-! ### Semantic type distinctions (§2.1, example 30)
Each clause type has a distinct semantic type — this is one of Sag's
key arguments that F-G constructions are not uniform. -/

theorem interrogative_denotes_question :
    (fgParams .whInterrogative).semanticType = .question := rfl
theorem exclamative_denotes_fact :
    (fgParams .whExclamative).semanticType = .fact := rfl
theorem topicalized_denotes_austinean :
    (fgParams .topicalized).semanticType = .austinean := rfl
theorem relative_denotes_modifier :
    (fgParams .whRelative).semanticType = .modifier := rfl
theorem theClause_denotes_austinean :
    (fgParams .theClause).semanticType = .austinean := rfl

/-! ### Inversion parameter (§2.1, example 28)
Only wh-interrogatives require inversion; topicalization/relatives/exclamatives
prohibit it; the-clauses allow it optionally. -/

theorem only_interrogative_requires_inversion :
    (fgParams .whInterrogative).headInversion = .required ∧
    (fgParams .whExclamative).headInversion = .prohibited ∧
    (fgParams .topicalized).headInversion = .prohibited ∧
    (fgParams .whRelative).headInversion = .prohibited ∧
    (fgParams .theClause).headInversion = .optional := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### Island status
Topicalization and wh-exclamatives are extraction islands (§5.1 ex. 67, §5.2
ex. 73–74). Wh-interrogatives, relatives, and the-clauses are not. -/

theorem topicalized_is_island :
    (fgParams .topicalized).isIsland = true := rfl
theorem exclamative_is_island :
    (fgParams .whExclamative).isIsland = true := rfl
theorem interrogative_not_island :
    (fgParams .whInterrogative).isIsland = false := rfl
theorem relative_not_island :
    (fgParams .whRelative).isIsland = false := rfl

/-! ### Independence constraints (§2.1 / example 31)
Topicalization requires independence; relatives require embedding. -/

theorem topicalized_requires_independence :
    (fgParams .topicalized).independence = .required := rfl
theorem relative_requires_embedding :
    (fgParams .whRelative).independence = .prohibited := rfl

/-! ### All fillers are nonverbal
Sag (2010) §2.1 / example 25: filler daughter is always nonverbal across
all five F-G clause types. This is a constraint on the superordinate
filler-head construction (58), not construction-specific. -/

theorem all_fillers_nonverbal :
    [FGClauseType.whInterrogative, .whExclamative, .topicalized,
     .whRelative, .theClause].all
      (λ c => (fgParams c).fillerIsNonverbal) = true := by native_decide

-- ============================================================================
-- Bridge: Island Parameter ↔ Islands/Data.lean
-- ============================================================================

/-! ### Connection to `ConstraintType` in Islands/Data

Sag (2010, p.514) argues that island constraints are construction-specific
GAP restrictions, not universal Subjacency. The topicalization construction
has `[GAP ⟨⟩]` on its mother, making it an absolute extraction island. This
matches the `ConstraintType` classification from Islands/Data. -/

/-- The island constructions in Sag 2010 correspond to specific constraint
types in the island classification system. The CNPC (complexNP) is the
island tested in Hofmeister & Sag 2010; Sag's topicalization and exclamative
islands are additional construction-specific cases. -/
def islandConstructions : List FGClauseType :=
  [FGClauseType.whInterrogative, .whExclamative, .topicalized,
   .whRelative, .theClause].filter (λ c => (fgParams c).isIsland)

/-- Exactly topicalization and wh-exclamatives are F-G island constructions. -/
theorem island_constructions_are :
    islandConstructions = [.whExclamative, .topicalized] := by native_decide

-- ============================================================================
-- Bridge: Semantic Type ↔ ClauseType
-- ============================================================================

/-! ### Connection to `ClauseType` in Core/Basic

Sag's semantic types map to the existing `ClauseType` for the clause types
that have direct correspondences. -/

/-- Wh-interrogatives correspond to matrixQuestion or embeddedQuestion
depending on independence. -/
theorem interrogative_maps_to_question_clause :
    (fgParams .whInterrogative).semanticType = .question ∧
    (fgParams .whInterrogative).independence = .either := by
  exact ⟨rfl, rfl⟩

/-- Topicalization corresponds to declarative clauses (austinean semantics,
independent, uninverted). -/
theorem topicalized_maps_to_declarative :
    (fgParams .topicalized).semanticType = .austinean ∧
    (fgParams .topicalized).headInversion = .prohibited ∧
    (fgParams .topicalized).independence = .required := by
  exact ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- Wh-Word Inventory (Table 1)
-- ============================================================================

/-- Functions of wh-words across construction types (Sag 2010, Table 1).

Each wh-word is classified by which F-G clause types it participates in.
'+' = full participant, '%' = for some speakers, '-' = excluded. -/
structure WhWordProfile where
  form : String
  interrogative : Bool
  exclamative : Bool
  relative : Bool
  deriving Repr, DecidableEq, BEq

def whWordProfiles : List WhWordProfile := [
  { form := "who",    interrogative := true,  exclamative := false, relative := true },
  { form := "whose",  interrogative := true,  exclamative := false, relative := true },
  { form := "what",   interrogative := true,  exclamative := false, relative := false },
  { form := "which",  interrogative := false, exclamative := false, relative := true },
  { form := "how",    interrogative := true,  exclamative := true,  relative := false },
  { form := "when",   interrogative := true,  exclamative := false, relative := true },
  { form := "where",  interrogative := true,  exclamative := false, relative := true },
  { form := "why",    interrogative := true,  exclamative := false, relative := true }
]

/-- No wh-word participates in all three construction types uniformly.
This supports Sag's claim that 'wh-expression' is not a unitary category. -/
theorem no_universal_wh_word :
    whWordProfiles.all (λ w =>
      w.interrogative && w.exclamative && w.relative) = false := by native_decide

/-- 'how' participates in both interrogatives and exclamatives — one of the
few wh-words that crosses this boundary (examples 18–20). -/
theorem how_crosses_interrog_exclam :
    (whWordProfiles.filter (λ w =>
      w.interrogative && w.exclamative)).length ≥ 1 := by native_decide

end Phenomena.FillerGap.Studies.Sag2010
