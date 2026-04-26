import Linglib.Fragments.Mwaghavul.Basic
import Linglib.Core.Constraint.System
import Linglib.Theories.Pragmatics.Expressives.Basic
import Linglib.Theories.Morphology.DM.Categorizer
import Linglib.Theories.Phonology.Autosegmental.CoPScope
import Linglib.Theories.Phonology.Autosegmental.BasemapCorrespondence
import Linglib.Theories.Phonology.Autosegmental.Floating
import Linglib.Theories.Phonology.OptimalityTheory.Correspondence
import Linglib.Theories.Phonology.OptimalityTheory.CophonologyTheory
import Linglib.Theories.Phonology.Tone.Constraints
import Linglib.Core.Constraint.OT.HarmonicSerialism
import Linglib.Phenomena.Tone.Studies.Hyman2006

/-!
# Akinbo & Fwangwar (2026): Grammatical tones targeting ideophones
@cite{akinbo-fwangwar-2026}

Akinbo, S. K. & Fwangwar, T. R. (2026). Iconicity and expressiveness of
grammatical tones targeting ideophones in Mwaghavul. *Natural Language &
Linguistic Theory* 44:21.

## Core claims formalized

1. **Grammatical tone targets ideophones**: Mwaghavul derives verbs from
   ideophones through two tonal alternation patterns triggered by
   segmentally null verbalisers with M and M-H melodies.

2. **OT analysis**: The tonal alternations are accounted for by
   morpheme-specific correspondence constraints (@cite{finley-2009}):
   LEFT-ANCHOR-M_V, RIGHT-ANCHOR-M_V, INTEGRITY-M_V, and MAX-Tone,
   ranked to select the attested output. Constraints are **gradient**:
   they count the number of misaligned TBUs, not just binary violations.

3. **Expressiveness survives integration**: Derived ideophonic verbs
   retain expressive properties (affective meaning, nondisplaceability,
   ineffability) despite full morphosyntactic integration, challenging
   the inverse correlation between grammatical integration and
   expressiveness (@cite{dingemanse-akita-2017}).

4. **Iconic Phonological Disharmony**: The M-H verbaliser's tonal
   disharmony between reduplicant (M on every TBU) and base (H on every
   TBU) in pluractional verbs is iconically motivated, expressing
   "distinguishable identity" through phonological dissimilarity.

## Dependency on @cite{rolle-2018}

The analysis uses @cite{rolle-2018}'s grammatical tone framework
(formalized in `Theories/Phonology/Autosegmental/GrammaticalTone.lean`).
The verbalisers are classified as replacive-dominant grammatical tones
with the root morpheme as both target and host.

## OT candidate representation

Each output TBU records its **tone source**: lexical (from the input) or
grammatical (from the verbaliser's M or H tone). This correspondence
structure is what allows the anchor constraints to compute gradient
violations — they count TBUs where the verbaliser tone is not realized
at the expected edge of the root morpheme.
-/

namespace AkinboFwangwar2026

open Core.Constraint.OT
open Phonology.Autosegmental.RegisterTier (TRN)
open Fragments.Mwaghavul

-- ============================================================================
-- S 1: Correspondence-Based OT Candidates
-- ============================================================================

/-- The source of an output tone: lexical (from the input ideophone) or
    grammatical (from the verbaliser morpheme).

    In the paper's notation, subscript 1 = lexical, subscript 2 = from
    the M-tone verbaliser, subscript 3 = from the H-tone verbaliser
    (or subscript 4 for H in pluractional tableaux). We collapse the
    grammatical subscripts into `.gram` and use the separate M-specific
    and H-specific anchor constraint functions (`lAnchorViolations .M`,
    `rAnchorViolations .H`, etc.) to distinguish which verbaliser tone
    is being tracked. -/
inductive ToneSource where
  | lex   -- subscript 1: from the input
  | gram  -- subscripts 2, 3: from the verbaliser
  deriving DecidableEq, Repr

/-- An output TBU with correspondence: the surface tone and where it
    came from. -/
structure OutputTBU where
  tone   : TRN
  source : ToneSource
  deriving DecidableEq, Repr

/-- A candidate for a single-root-morpheme tableau (M-tone or M-H singular).
    Records the output TBUs on a single root morpheme. -/
structure SingleCand where
  label  : String
  output : List OutputTBU
  deriving DecidableEq, Repr

/-- A candidate for a two-root-morpheme tableau (pluractional M-H).
    Records output TBUs on reduplicant and base separately. -/
structure PlurCand where
  label     : String
  redOutput : List OutputTBU
  baseOutput : List OutputTBU
  deriving DecidableEq, Repr

-- ============================================================================
-- S 2: Gradient Constraint Functions
-- ============================================================================

/-! ### Constraint computation

The constraints compute violation counts from the correspondence structure
of the candidate, following @cite{akinbo-fwangwar-2026} §4.3 and
@cite{finley-2009}:

- **L-ANCH-X_V**: counts TBUs to the LEFT of the leftmost grammatical
  X-tone that are NOT grammatical X. For a fully left-anchored realization,
  this is 0. If X is not realized at all, every TBU of the root is a
  violation (the verbaliser tone has no correspondent at the left edge).

- **R-ANCH-X_V**: counts TBUs to the RIGHT of the rightmost grammatical
  X-tone that are NOT grammatical X. Same logic, mirrored.

- **INTEGRITY-M_V**: violated when the verbaliser's M tone has multiple
  output correspondents (i.e., is realized on more than one root morpheme
  via splitting). Binary: 0 or 1.

- **MAX-Tone**: counts input tones that have no output correspondent
  (i.e., lexical tones that were deleted/overwritten by grammatical tones).
-/

/-- Count L-ANCHOR violations for a given grammatical tone: number of
    TBUs to the left of the leftmost grammatical occurrence of `tone`.
    If the tone is not present, every TBU is a violation (tone not
    anchored). Parametrized over `TRN` to avoid duplicating
    the M and H variants. -/
def lAnchorViolations (tone : TRN) (tbus : List OutputTBU) : Nat :=
  match tbus.findIdx? (λ t => t.source == .gram && t.tone == tone) with
  | none   => tbus.length
  | some i => i

/-- Count R-ANCHOR violations for a given grammatical tone. -/
def rAnchorViolations (tone : TRN) (tbus : List OutputTBU) : Nat :=
  lAnchorViolations tone tbus.reverse

/-- MAX-Tone: count lexical tones that were deleted (overwritten).
    = number of input TBUs minus number of output TBUs that retain
    lexical source.

    Note: the paper counts MAX-Tone per tone **autosegment** (one-to-many
    association counts as one), while our model counts per **TBU**. This
    means our MAX-T values may be higher than the paper's star counts.
    Since MAX-Tone is lowest-ranked in all three tableaux, this
    discrepancy never affects which candidate is optimal. -/
def maxToneViolations (tbus : List OutputTBU) (inputSize : Nat) : Nat :=
  inputSize - (tbus.filter (λ t => t.source == .lex) |>.length)

-- ============================================================================
-- S 3: Named Constraints for Tableaux
-- ============================================================================

/-- Tone-parameterized L-ANCHOR for `SingleCand`: the violation count
    is the position of the leftmost gram-`t` TBU in the output. -/
def lAnchSingle (t : TRN) : NamedConstraint SingleCand :=
  { name := s!"L-ANCH-{reprStr t}ᵥ"
    family := .faithfulness
    eval := λ c => lAnchorViolations t c.output }

/-- Tone-parameterized R-ANCHOR for `SingleCand`. -/
def rAnchSingle (t : TRN) : NamedConstraint SingleCand :=
  { name := s!"R-ANCH-{reprStr t}ᵥ"
    family := .faithfulness
    eval := λ c => rAnchorViolations t c.output }

/-- Input-size-parameterized MAX-Tone for `SingleCand`. -/
def maxTSingle (inputSize : Nat) : NamedConstraint SingleCand :=
  { name := "MAX-Tone"
    family := .faithfulness
    eval := λ c => maxToneViolations c.output inputSize }

-- INTEGRITY-Mᵥ is omitted: it eliminates only (24f), where the verbaliser's
-- M tone is split into multiple copies. Since our candidate representation
-- cannot distinguish spreading (one-to-many association, no violation) from
-- copying (multiple independent copies, violation), we exclude (24f) from
-- the candidate set instead. The paper's key result is the L-ANCH >> R-ANCH
-- >> MAX-T ranking.

-- ============================================================================
-- S 4: Tableau (24) — M-tone verbaliser + wùlàʃ [L L]
-- ============================================================================

/-! ### Tableau (24) from @cite{akinbo-fwangwar-2026} §4.3

Input: (wùlàʃ)₁ + M₂   (bisyllabic, lexical L-L, verbaliser M)

Ranking: INTEG-Mᵥ >> L-ANCH-Mᵥ >> R-ANCH-Mᵥ >> MAX-Tone

| Candidate               | INTEG | L-ANCH | R-ANCH | MAX-T |
|--------------------------|-------|--------|--------|-------|
| a. (wùlàʃ)₁             |       | **!    | **     |       |
| b. (wùlàʃ)₁ M₂          |       | **!    | **     | *     |
| c. (wù)₁(làʃ)₂          |       | *!     |        | *     |
| d. (wū)₂(làʃ)₁          |       |        | *!     | *     |
| e. ☞ (wūlāʃ)₂           |       |        |        | *     |
| f. (wū)₂(lāʃ)₂          | *!    |        |        | *     |

(24a)/(24b) have no verbaliser tone associated to any TBU → L-ANCH = 2,
R-ANCH = 2. (24e)/(24f) have identical surface output but differ in
correspondence: (24e) has one M spreading (one-to-many association,
no INTEGRITY violation), while (24f) has two independent copies
(INTEGRITY violation). Since our `OutputTBU` representation cannot
distinguish spreading from copying, we exclude (24f) and INTEGRITY.
The key result — L-ANCH >> R-ANCH >> MAX-T — is unaffected.
-/

-- Candidate a: no realization of M — both TBUs retain lexical L
def t24a : SingleCand := ⟨"(wùlàʃ)₁", [⟨.L, .lex⟩, ⟨.L, .lex⟩]⟩
-- Candidate b: M floating (not associated to any TBU)
-- Anchor violations identical to (a); paper shows MAX-T=* (1 star)
-- because the verbaliser's M autosegment exists but is unassociated.
-- In our per-TBU counting: 0 lexical tones deleted → MAX-T=0.
def t24b : SingleCand := ⟨"(wùlàʃ)₁ M₂", [⟨.L, .lex⟩, ⟨.L, .lex⟩]⟩
-- Candidate c: M on right TBU only
def t24c : SingleCand := ⟨"(wù)₁(làʃ)₂", [⟨.L, .lex⟩, ⟨.M, .gram⟩]⟩
-- Candidate d: M on left TBU only
def t24d : SingleCand := ⟨"(wū)₂(làʃ)₁", [⟨.M, .gram⟩, ⟨.L, .lex⟩]⟩
-- Candidate e: M on every TBU — WINNER
def t24e : SingleCand := ⟨"(wūlāʃ)₂", [⟨.M, .gram⟩, ⟨.M, .gram⟩]⟩

-- Include a, b, c, d, e. We exclude (24f) because our representation
-- cannot distinguish it from (24e) (same OutputTBU sequence).
def t24_candidates : List SingleCand := [t24a, t24b, t24c, t24d, t24e]

def t24_ranking : List (NamedConstraint SingleCand) :=
  [lAnchSingle .M, rAnchSingle .M, maxTSingle 2]

-- Verify individual violation counts (L-ANCH, R-ANCH, MAX-T):
-- (24a): no gram → L=2, R=2; no deletions → MAX-T=0
theorem t24a_profile : mkProfile t24_ranking t24a = vpOfList [2, 2, 0] := by decide
-- (24b): same anchor profile as (a); per-TBU MAX-T=0 (paper: 1, per autosegment)
theorem t24b_profile : mkProfile t24_ranking t24b = vpOfList [2, 2, 0] := by decide
-- (24c): gram on σ2 → L=1, R=0; 1 lex deleted → MAX-T=1
theorem t24c_profile : mkProfile t24_ranking t24c = vpOfList [1, 0, 1] := by decide
-- (24d): gram on σ1 → L=0, R=1; 1 lex deleted → MAX-T=1
theorem t24d_profile : mkProfile t24_ranking t24d = vpOfList [0, 1, 1] := by decide
-- (24e): gram on both → L=0, R=0; 2 lex deleted → MAX-T=2
-- Paper: MAX-T=* (1, per autosegment). Does not affect optimality.
theorem t24e_profile : mkProfile t24_ranking t24e = vpOfList [0, 0, 2] := by decide

/-- The M-on-every-TBU candidate (24e) is optimal under the proposed ranking.
    L-ANCH-Mᵥ >> R-ANCH-Mᵥ >> MAX-Tone -/
theorem t24_optimal :
    (mkTableau t24_candidates t24_ranking).optimal = {t24e} := by
  decide

-- ============================================================================
-- S 5: Tableau (25) — M-H verbaliser + háŋláyáp [H H H]
-- ============================================================================

/-! ### Tableau (25) from @cite{akinbo-fwangwar-2026} §4.3

Input: (háŋláyáp)₁ + M₂H₃   (trisyllabic, lexical H-H-H, verbaliser M-H)

Ranking: L-ANCH-Mᵥ, R-ANCH-Hᵥ >> R-ANCH-Mᵥ >> L-ANCH-Hᵥ >> MAX-Tone

Paper's tableau (star counts are per **autosegment**; our model counts
per TBU, so MAX-T values differ — see note on `maxToneViolations`).
L-ANCH-H for (25g) differs: paper shows 1, our model gives 2 (we count
all TBUs before the first gram-H regardless of their source).

| Candidate                    | L-M | R-H | R-M | L-H | MAX-T (paper/ours) |
|------------------------------|-----|-----|-----|-----|--------------------|
| a. (háŋláyáp)₁              | 3!  | 3!  | 3   | 3   | 2 / 0              |
| b. (hāŋlā)₂(yáp)₁          | 0   | 3!  | 1   | 3   | 1 / 2              |
| c. (háŋláyáp)₃              | 3!  | 0   | 3   | 0   | 2 / 3              |
| d. (hāŋlāyāp)₂             | 0   | 3!  | 0   | 3   | 2 / 3              |
| e. ☞ (hāŋlā)₂(yáp)₃        | 0   | 0   | 1   | 2   | 1 / 3              |
| f. (hāŋ)₂(láyáp)₃           | 0   | 0   | 2!  | 1   | 1 / 3              |
| g. (hāŋ)₂(lá)₁(yáp)₃        | 0   | 0   | 2!  | 1/2 | 1 / 2              |

The key distinction: (25b) and (25e) have the same surface tones
[M M H] but different correspondence. In (25b), the final H is
**lexical** (subscript 1); in (25e), it is **grammatical** (subscript 3).
The anchor constraints track the verbaliser's H, not just surface H.
-/

-- (25a): no verbaliser tones realized — all lexical
def t25a : SingleCand :=
  ⟨"(háŋláyáp)₁", [⟨.H, .lex⟩, ⟨.H, .lex⟩, ⟨.H, .lex⟩]⟩

-- (25b): M₂ on σ1-σ2 (gram), H on σ3 is LEXICAL (subscript 1)
def t25b : SingleCand :=
  ⟨"(hāŋlā)₂(yáp)₁", [⟨.M, .gram⟩, ⟨.M, .gram⟩, ⟨.H, .lex⟩]⟩

-- (25c): H₃ on all TBUs — no M realized
def t25c : SingleCand :=
  ⟨"(háŋláyáp)₃", [⟨.H, .gram⟩, ⟨.H, .gram⟩, ⟨.H, .gram⟩]⟩

-- (25d): M₂ spreading to all TBUs — no H realized.
-- Paper notation: (hāŋlàyàp)₂ shows surface M-L-L with subscript 2 on all.
-- The IPA diacritics indicate the *surface* pitch contour, while the
-- subscript indicates morpheme correspondence. For our anchor constraints
-- to produce the paper's violation profile [0, 3, 0, 3, ...], we encode
-- all TBUs as gram-M (M₂ associated to all TBUs).
def t25d : SingleCand :=
  ⟨"(hāŋlāyāp)₂", [⟨.M, .gram⟩, ⟨.M, .gram⟩, ⟨.M, .gram⟩]⟩

-- (25e): WINNER — M₂ on σ1-σ2, H₃ on σ3 (all gram)
def t25e : SingleCand :=
  ⟨"(hāŋlā)₂(yáp)₃", [⟨.M, .gram⟩, ⟨.M, .gram⟩, ⟨.H, .gram⟩]⟩

-- (25f): M₂ on σ1 only, H₃ on σ2-σ3
def t25f : SingleCand :=
  ⟨"(hāŋ)₂(láyáp)₃", [⟨.M, .gram⟩, ⟨.H, .gram⟩, ⟨.H, .gram⟩]⟩

-- (25g): M₂ on σ1, lexical H on σ2, H₃ on σ3
def t25g : SingleCand :=
  ⟨"(hāŋ)₂(lá)₁(yáp)₃", [⟨.M, .gram⟩, ⟨.H, .lex⟩, ⟨.H, .gram⟩]⟩

-- All 7 candidates (excluding only those our representation cannot encode)
def t25_candidates : List SingleCand :=
  [t25a, t25b, t25c, t25d, t25e, t25f, t25g]

def t25_ranking : List (NamedConstraint SingleCand) :=
  [lAnchSingle .M, rAnchSingle .H, rAnchSingle .M, lAnchSingle .H, maxTSingle 3]

-- Verify violation profiles (L-ANCH-M, R-ANCH-H, R-ANCH-M, L-ANCH-H, MAX-T):
-- MAX-T is per-TBU (paper counts per autosegment; see maxToneViolations).
theorem t25a_profile : mkProfile t25_ranking t25a = vpOfList [3, 3, 3, 3, 0] := by decide
theorem t25b_profile : mkProfile t25_ranking t25b = vpOfList [0, 3, 1, 3, 2] := by decide
theorem t25c_profile : mkProfile t25_ranking t25c = vpOfList [3, 0, 3, 0, 3] := by decide
theorem t25d_profile : mkProfile t25_ranking t25d = vpOfList [0, 3, 0, 3, 3] := by decide
theorem t25e_profile : mkProfile t25_ranking t25e = vpOfList [0, 0, 1, 2, 3] := by decide
theorem t25f_profile : mkProfile t25_ranking t25f = vpOfList [0, 0, 2, 1, 3] := by decide
theorem t25g_profile : mkProfile t25_ranking t25g = vpOfList [0, 0, 2, 2, 2] := by decide

/-- The M-on-nonfinal, H-on-final candidate (25e) is optimal.
    L-ANCH-Mᵥ, R-ANCH-Hᵥ >> R-ANCH-Mᵥ >> L-ANCH-Hᵥ >> MAX-Tone -/
theorem t25_optimal :
    (mkTableau t25_candidates t25_ranking).optimal = {t25e} := by
  decide

-- ============================================================================
-- S 6: End-to-End Chain
-- ============================================================================

/-- The OT winner for háŋláyáp produces the same output tones as
    `deriveVerb` (which uses `tonalOverwrite`). Since `t25_optimal`
    proves the winner is `t25e`, we verify directly. -/
theorem t25_winner_agrees_with_deriveVerb :
    t25e.output.map OutputTBU.tone = deriveVerb hanlayap := by
  decide

/-- The OT winner for wùlàʃ produces the same output tones as
    `deriveVerb`. Since `t24_optimal` proves the winner is `t24e`,
    we verify directly. -/
theorem t24_winner_agrees_with_deriveVerb :
    t24e.output.map OutputTBU.tone = deriveVerb wuulash := by
  decide

-- ============================================================================
-- S 7: Pluractional Verbs — Reduplication + M-H
-- ============================================================================

/-! ### Pluractional verb formation

Pluractional verbs are derived from ideophones through reduplication
followed by M-H tonal alternation. Each tone of the M-H verbaliser
gets its own root morpheme as host (@cite{akinbo-fwangwar-2026} §4.1):
- M tone → every TBU of the reduplicant (leftmost copy)
- H tone → every TBU of the base (rightmost copy)

Example: jàlpàt [L L] 'hanging loose'
- Reduplicated: jàlpàt-jàlpàt
- Pluractional verb: jālpāt-jálpát [M M - H H]

### Constraint evaluation for two root morphemes

Each anchor constraint evaluates on its **host morpheme**: M-tone
anchors apply to the reduplicant (M₃'s host), H-tone anchors apply
to the base (H₄'s host). This follows from the paper's analysis
where "a root morpheme and its TBUs serve as the respective host
and valuation window of each tone" (§4.1).

This is an instance of Iconic Phonological Disharmony:
the tonal dissimilarity between reduplicant and base iconically
represents "distinguishable identity" (@cite{dingemanse-thompson-2020}).
-/

-- Constraint evaluation for PlurCand: each anchor constraint evaluates
-- on the **host morpheme** for that verbaliser tone.
-- M-tone anchors evaluate on the reduplicant (M₃'s host).
-- H-tone anchors evaluate on the base (H₄'s host).
-- This follows from §4.1: "a root morpheme and its TBUs serve as the
-- respective host and valuation window of each tone."

def lAnchM26 : NamedConstraint PlurCand :=
  { name := "L-ANCH-Mᵥ"
    family := .faithfulness
    eval := λ c => lAnchorViolations .M c.redOutput }

def rAnchH26 : NamedConstraint PlurCand :=
  { name := "R-ANCH-Hᵥ"
    family := .faithfulness
    eval := λ c => rAnchorViolations .H c.baseOutput }

def rAnchM26 : NamedConstraint PlurCand :=
  { name := "R-ANCH-Mᵥ"
    family := .faithfulness
    eval := λ c => rAnchorViolations .M c.redOutput }

def lAnchH26 : NamedConstraint PlurCand :=
  { name := "L-ANCH-Hᵥ"
    family := .faithfulness
    eval := λ c => lAnchorViolations .H c.baseOutput }

def maxT26 : NamedConstraint PlurCand :=
  { name := "MAX-Tone"
    family := .faithfulness
    eval := λ c => maxToneViolations (c.redOutput ++ c.baseOutput) 4 }

/-! ### Tableau (26) from @cite{akinbo-fwangwar-2026} §4.3

Input: (jàlpàt)₁ + (jàlpàt)₂ + M₃H₄ᵥ   (bisyllabic × 2, verbaliser M-H)

| Candidate                              | L-ANCH-M | R-ANCH-H | R-ANCH-M | L-ANCH-H | MAX-T |
|----------------------------------------|----------|----------|----------|----------|-------|
| a. (jàlpàt)₁ (jàlpàt)₂               | ****!    | ****!    | ****     | ****     |       |
| b. (jàl)₁(pāt)₃ (jàl)₂(pát)₄         | *!       |          |          |          | *     |
| c. (jàl)₃(pàt)₁ (jàl)₄(pàt)₂         |          | *!       | *        |          |       |
| d. ☞ (jālpāt)₃ (jálpát)₄             |          |          |          |          | **    |
| e. (jàl)₃(pát)₄ (jàlpàt)₂             |          |          | *!       | *        | *     |
| f. (jālpāt jāl)₃ (pát)₄               |          |          | *!       |          | **    |
| g. (jàl)₃(pàt jàl)₁ (pát)₄            |          |          | *!       | *        | *     |
-/

-- (26a): no verbaliser tones — all lexical
def t26a : PlurCand :=
  ⟨"(jàlpàt)₁(jàlpàt)₂",
   [⟨.L, .lex⟩, ⟨.L, .lex⟩],
   [⟨.L, .lex⟩, ⟨.L, .lex⟩]⟩

-- (26b): M₃ on σ2 of RED only, H₄ on σ2 of BASE only
def t26b : PlurCand :=
  ⟨"(jàl)₁(pāt)₃ (jàl)₂(pát)₄",
   [⟨.L, .lex⟩, ⟨.M, .gram⟩],
   [⟨.L, .lex⟩, ⟨.H, .gram⟩]⟩

-- (26c): M₃ on σ1 of RED, H₄ on σ1 of BASE (anchored left not right)
def t26c : PlurCand :=
  ⟨"(jàl)₃(pàt)₁ (jàl)₄(pàt)₂",
   [⟨.M, .gram⟩, ⟨.L, .lex⟩],
   [⟨.H, .gram⟩, ⟨.L, .lex⟩]⟩

-- (26d): WINNER — M₃ on all of RED, H₄ on all of BASE
def t26d : PlurCand :=
  ⟨"(jālpāt)₃(jálpát)₄",
   [⟨.M, .gram⟩, ⟨.M, .gram⟩],
   [⟨.H, .gram⟩, ⟨.H, .gram⟩]⟩

-- (26e): M₃ on σ1 of RED, H₄ on σ2 of RED + none on BASE
-- This candidate realizes both verbaliser tones on the reduplicant only.
def t26e : PlurCand :=
  ⟨"(jàl)₃(pát)₄ (jàlpàt)₂",
   [⟨.M, .gram⟩, ⟨.H, .gram⟩],
   [⟨.L, .lex⟩, ⟨.L, .lex⟩]⟩

-- (26f): M₃ spreads across RED+σ1 of BASE; H₄ on σ2 of BASE only
def t26f : PlurCand :=
  ⟨"(jālpāt jāl)₃ (pát)₄",
   [⟨.M, .gram⟩, ⟨.M, .gram⟩],
   [⟨.M, .gram⟩, ⟨.H, .gram⟩]⟩

-- (26g): M₃ on σ1 of RED, lex on σ2+σ1 of BASE, H₄ on σ2 of BASE
def t26g : PlurCand :=
  ⟨"(jàl)₃(pàt jàl)₁ (pát)₄",
   [⟨.M, .gram⟩, ⟨.L, .lex⟩],
   [⟨.L, .lex⟩, ⟨.H, .gram⟩]⟩

def t26_candidates : List PlurCand :=
  [t26a, t26b, t26c, t26d, t26e, t26f, t26g]

def t26_ranking : List (NamedConstraint PlurCand) :=
  [lAnchM26, rAnchH26, rAnchM26, lAnchH26, maxT26]

-- Verify key profiles (L-ANCH-M on RED, R-ANCH-H on BASE, R-ANCH-M on RED, L-ANCH-H on BASE, MAX-T):
-- (26a): no gram anywhere → all max violations per host (2 TBUs each)
theorem t26a_profile : mkProfile t26_ranking t26a = vpOfList [2, 2, 2, 2, 0] := by decide
-- (26d): winner — M perfectly anchored on RED, H perfectly anchored on BASE
theorem t26d_profile : mkProfile t26_ranking t26d = vpOfList [0, 0, 0, 0, 4] := by decide
-- (26e): both tones on RED, none on BASE → H-anchors on BASE penalize
theorem t26e_profile : mkProfile t26_ranking t26e = vpOfList [0, 2, 1, 2, 2] := by decide

/-- The reduplicant-M, base-H candidate (26d) is optimal. -/
theorem t26_optimal :
    (mkTableau t26_candidates t26_ranking).optimal = {t26d} := by
  decide

-- ============================================================================
-- S 8: Iconic Phonological Disharmony
-- ============================================================================

/-- The pluractional verb's tonal pattern exhibits Iconic Phonological
    Disharmony: corresponding TBUs of the reduplicant and base bear
    maximally dissimilar tones (M vs H), iconically representing the
    "distinguishable identity" expressed by the derived verb.

    This pattern is attested crosslinguistically in ideophones expressing
    distinguishable identity: reduplicant and base bear different feature
    values (@cite{dingemanse-thompson-2020}, @cite{yliniemi-2024}). -/
def iconicDisharmony (red base : List TRN) : Bool :=
  (red.zip base).all λ (r, b) => r != b

/-- The optimal pluractional verb exhibits iconic disharmony. -/
theorem t26_winner_iconic :
    iconicDisharmony
      (t26d.redOutput.map OutputTBU.tone)
      (t26d.baseOutput.map OutputTBU.tone) = true := by decide

/-- The pluractional winner has uniform M on the reduplicant —
    matching `tonalOverwrite` with VBZ₁ (M melody, whole window). -/
theorem t26_red_uniform_M :
    t26d.redOutput.map OutputTBU.tone = [.M, .M] := by decide

/-- The pluractional winner has uniform H on the base. -/
theorem t26_base_uniform_H :
    t26d.baseOutput.map OutputTBU.tone = [.H, .H] := by decide

/-- End-to-end: the pluractional reduplicant matches `tonalOverwrite`
    with the M melody (VBZ₁ applied to the reduplicant). -/
theorem t26_red_agrees_with_tonalOverwrite :
    t26d.redOutput.map OutputTBU.tone =
      (Phonology.Autosegmental.GrammaticalTone.tonalOverwrite
        (jalpat.tones.map λ t => mkTSyl jalpat.form t) verbM).map
        Phonology.Autosegmental.GrammaticalTone.TBU.tone := by
  decide

-- ============================================================================
-- S 9: Expressiveness Preservation
-- ============================================================================

/-! ### Bridge to @cite{potts-2005} expressive semantics

@cite{akinbo-fwangwar-2026} §4.2 argues that derived ideophonic verbs
retain expressive properties despite full morphosyntactic integration:

- **Affective meaning**: derived verbs have positive or negative
  affective associations that vary with context
- **Nondisplaceability**: meanings are tied to the utterance situation
- **Ineffability**: exact meanings resist paraphrase
- **Context-dependence**: interpretation depends on discourse context

These match @cite{potts-2005}'s characterization of CI expressions.
This challenges @cite{dingemanse-akita-2017}'s prediction that
grammatical integration inversely correlates with expressiveness.
-/

open Pragmatics.Expressives

/-- Derived ideophonic verbs exhibit all canonical expressive properties:
    independent, nondisplaceable, perspective-dependent, descriptively
    ineffable, immediate, repeatable, no perspective shift, no discourse
    antecedent required. -/
def ideophoneVerbProperties : SecondaryMeaningProperties :=
  { independent := true
    nondisplaceable := true
    perspectiveDependent := true
    descriptivelyIneffable := true
    immediate := true
    repeatable := true
    allowsPerspectiveShift := false
    requiresDiscourseAntecedent := false }

/-- Derived ideophonic verbs have the same secondary meaning properties as
    canonical expressives — grammatical integration does not strip
    expressiveness.

    Note: this is definitionally true because the Mwaghavul data
    instantiates the same property values. The empirical content
    is in the *claim* that these properties hold for derived verbs —
    the theorem merely records that claim in a machine-checkable form. -/
theorem expressiveness_survives_integration :
    ideophoneVerbProperties = expressiveProperties := rfl

-- ============================================================================
-- S 10: Connection to Distributed Morphology
-- ============================================================================

/-! ### Verbalisers as categorizing heads

The segmentally null verbalisers that trigger tonal alternation in
Mwaghavul are instances of the verbal categorizer v in Distributed
Morphology (@cite{marantz-1997}, @cite{harley-2014}). The ideophonic
base (noun, adjective, or adverb) is recategorized as a verb through
merger with v, whose sole phonological exponent is a tonal melody.

This connects to `Recategorization` in `Theories/Morphology/DM/Categorizer.lean`:
denominal verbs (n → v) and deadjectival verbs (a → v) are both attested
in Mwaghavul's ideophone-to-verb derivation. -/

open Morphology.DM

/-- Both M-tone and M-H verbalisers are verbal categorizers: they take
    an ideophonic base (which may be nominal, adjectival, or adverbial)
    and produce a verb. Both map to the same `CatHead.v_plain`. -/
def verbalizerCat : CatHead := CatHead.v_plain

/-- The verbaliser produces verbal category. -/
theorem verbalizer_is_verbal : verbalizerCat.cat = .v := rfl

/-- Denominal verb derivation: an ideophonic noun + verbaliser → verb.
    This is exactly the `Recategorization.denominal` pattern. -/
theorem denominal_ideophone_verb :
    Recategorization.denominal.source = .n ∧
    Recategorization.denominal.target = .v := ⟨rfl, rfl⟩

/-- Deadjectival verb derivation: an ideophonic adjective + verbaliser → verb. -/
theorem deadjectival_ideophone_verb :
    Recategorization.deadjectival.source = .a ∧
    Recategorization.deadjectival.target = .v := ⟨rfl, rfl⟩

-- ============================================================================
-- S 11: Empirical Generalizations
-- ============================================================================

/-- The M-H tonal melody is attested only in derived verbs.
    No underived Mwaghavul verb (out of ~600 surveyed) has M-H.
    We test this against the concrete ideophone data: every M-H
    output comes from an ideophone marked `.mh`. -/
theorem mh_only_from_mh_verbalizer :
    ∀ i ∈ [bishool, kitiif, kodzoong, kitfor, korjong, mondos,
           vwaplas, jalpat, hanlayap, hamhoyof],
    i.verbType = .mh := by decide

/-- All M-tone ideophones produce uniform M output. -/
theorem m_verbs_all_uniform :
    ∀ i ∈ [zut, diis, kwaaj, vjaar, shweer, wuulash, fooyoop, vjayaap],
    deriveVerb i = i.tones.map (λ _ => TRN.M) := by decide

/-- Pluractional verbs always use M-H, never M alone.
    This is generalization (13e-f): regardless of whether the
    unreduplicated form uses M or M-H, pluractionals use M-H. -/
-- This is an empirical observation about the data, not derivable
-- from the formalism alone. We record it as a checked property
-- of the M-H ideophones whose pluractional forms are in the paper.
theorem pluractional_uses_mh :
    jalpat.verbType = .mh ∧ hanlayap.verbType = .mh := ⟨rfl, rfl⟩

/-- Mwaghavul is a tone language under @cite{hyman-2006}'s definition (3):
    "an indication of pitch enters into the lexical realisation of at
    least some morphemes." This connects to the Hyman2006 study's
    word-prosodic typology, paralleling the cross-reference in
    `Lionnet2025.drubea_is_tonal_hyman`. -/
theorem mwaghavul_is_tonal_hyman :
    Hyman2006.isTonalUnderHyman wordProsodicType = true := rfl

-- ============================================================================
-- S 12: Factorial Typology
-- ============================================================================

/-- The factorial typology of the M-tone verbaliser constraints. -/
def mToneFactorialSize : Nat :=
  mkFactorialTypologySize t24_candidates t24_ranking

/-- The M-tone tableau has a restricted factorial typology —
    fewer distinct optima than the number of possible rankings of
    3 constraints (3! = 6). -/
theorem mTone_factorial_restricted : mToneFactorialSize ≤ 5 := by decide

-- ============================================================================
-- S 13: Classification under Rolle 2018
-- ============================================================================

/-! ### Rolle 2018 dominance typology

The Mwaghavul verbalisers are **replacive-dominant** grammatical tones
(@cite{rolle-2018} Def 1): the underlying tones of the ideophone root
are automatically replaced by the grammatical tune (M or M-H),
regardless of whether the root TBUs are valued or unvalued.

Both verbalisers:
- Are **dependents** (affixes) targeting the **lexical head** (root),
  consistent with the dominant GT asymmetry
- Have **independent prosodic exponence**: the verbalisers are
  segmentally null — tone is the sole exponent of verbalisation
- Operate at the **word** level (derivational morphology)

The `tonalOverwrite` function used by `deriveVerb` implements exactly
the replacive-dominant operation: it replaces all tones within the
valuation window without checking whether the input TBUs are valued. -/

open Phonology.Autosegmental.GrammaticalTone
  (GTSpec GTDominance GTLevel ExponenceType DominantGTAsymmetry)
open Phonology.Autosegmental.CoPScope
  (CoPPosition scopesOver dominant_gt_asymmetry_from_scope)

/-- The M-tone verbaliser (VBZ₁) classified under @cite{rolle-2018}:
    replacive-dominant, word-level, independent prosodic exponence. -/
def verbM_GT : GTSpec :=
  { name := "VBZ₁"
    melody := [.M]
    window := .whole
    dominance := .replaciveDominant
    level := .word
    exponence := .independent }

/-- The M-H verbaliser (VBZ₂) classified under @cite{rolle-2018}. -/
def verbMH_GT : GTSpec :=
  { name := "VBZ₂"
    melody := [.M, .H]
    window := .nonfinalFinal
    dominance := .replaciveDominant
    level := .word
    exponence := .independent }

/-- Both verbalisers are dominant: they neutralize the lexical tonal
    contrast of the target. -/
theorem verbalizers_are_dominant :
    verbM_GT.dominance.IsDominant ∧
    verbMH_GT.dominance.IsDominant := ⟨by decide, by decide⟩

/-- Mwaghavul verbalisers are dominant at the abstract prosodic level,
    bridging GT-specific and cross-domain classifications. -/
theorem verbalizers_prosodic_dominant :
    verbM_GT.dominance.toProsodicDominance = .dominant ∧
    verbMH_GT.dominance.toProsodicDominance = .dominant := ⟨rfl, rfl⟩

/-- The verbaliser-to-root relationship satisfies the dominant GT
    asymmetry, **derived from CoP-scope**: the verbaliser is in Spec
    position (dependent), the ideophone root is in Head position.
    Spec scopes over Head, so the asymmetry holds. -/
theorem verbalizer_asymmetry_holds :
    DominantGTAsymmetry.holds
      ⟨CoPPosition.isDependent .spec, !CoPPosition.isDependent .head⟩ = true :=
  dominant_gt_asymmetry_from_scope .spec .head rfl rfl

/-- The GTSpec for VBZ₁ extends the same `Spec` used by `deriveVerb`.
    The `toSpec` projection recovers the original melody and window. -/
theorem verbM_GT_toSpec_eq :
    verbM_GT.toSpec = verbM := rfl

/-- The GTSpec for VBZ₂ extends the same `Spec` used by `deriveVerb`. -/
theorem verbMH_GT_toSpec_eq :
    verbMH_GT.toSpec = verbMH := rfl

-- ============================================================================
-- S 14: Cophonology Theory Integration
-- ============================================================================

/-! ### Verbalisers as cophonological VIs

Under Cophonology Theory (@cite{rolle-2018} Ch 4, @cite{sande-jenks-2017}),
each verbaliser is a Vocabulary Item with a morpheme-specific constraint
subranking (the R component). The subranking promotes anchor constraints
above the default MAX-Tone, creating a morpheme-specific phonology that
forces the grammatical tune onto the output.

The default ranking has MAX-Tone high: without a verbaliser's cophonology,
lexical tones are preserved. Each verbaliser's cophonology promotes its
anchor constraints above MAX-Tone, forcing tone replacement — this is the
CPT account of why dominant GT erases underlying tones.

The three `cophEval` theorems below prove that `cophonologicalEval` with
each verbaliser's subranking selects the same optimal candidates as the
existing inline tableaux (24, 25, 26). -/

open Phonology.CophonologyTheory (CophVocabItem cophonologicalEval)
open Phonology.Autosegmental.BasemapCorrespondence (basemapViolations)

/-- Default ranking for the M-tone verbaliser context: MAX-Tone high,
    no anchor constraints. Without morpheme-specific effects, lexical
    tones are preserved (no overwriting). -/
def defaultRanking24 : List (NamedConstraint SingleCand) := [maxTSingle 2]

/-- Default ranking for the M-H verbaliser context (singular verbs). -/
def defaultRanking25 : List (NamedConstraint SingleCand) := [maxTSingle 3]

/-- Default ranking for the M-H pluractional context. -/
def defaultRanking26 : List (NamedConstraint PlurCand) := [maxT26]

/-- The M-tone verbaliser (VBZ₁) as a cophonological VI: segmentally
    null exponent with a subranking that promotes L-ANCH-Mᵥ and
    R-ANCH-Mᵥ above the default MAX-Tone. -/
def verbM_CophVI : CophVocabItem Unit Unit SingleCand :=
  { exponent := ""
    contextMatch := λ _ => true
    subranking := [lAnchSingle .M, rAnchSingle .M] }

/-- The M-H verbaliser (VBZ₂) as a cophonological VI for singular
    verbs: promotes L-ANCH-Mᵥ, R-ANCH-Hᵥ >> R-ANCH-Mᵥ >> L-ANCH-Hᵥ
    above MAX-Tone. -/
def verbMH_CophVI : CophVocabItem Unit Unit SingleCand :=
  { exponent := ""
    contextMatch := λ _ => true
    subranking := [lAnchSingle .M, rAnchSingle .H, rAnchSingle .M, lAnchSingle .H] }

/-- The M-H verbaliser for pluractional verbs: same anchor constraint
    logic but over `PlurCand` (two root morphemes with separate
    evaluation domains for M-anchors and H-anchors). -/
def verbMH_plur_CophVI : CophVocabItem Unit Unit PlurCand :=
  { exponent := ""
    contextMatch := λ _ => true
    subranking := [lAnchM26, rAnchH26, rAnchM26, lAnchH26] }

/-- Both verbalisers are dominant cophonologies (non-empty subranking). -/
theorem verbalizers_are_dominant_coph :
    verbM_CophVI.isDominantCoph = true ∧
    verbMH_CophVI.isDominantCoph = true := ⟨rfl, rfl⟩

/-- Cophonological evaluation with VBZ₁'s subranking selects the same
    winner as Tableau 24: (wūlāʃ)₂ with M on every TBU. -/
theorem verbM_cophEval_optimal :
    cophonologicalEval defaultRanking24 verbM_CophVI.subranking
      t24_candidates = {t24e} := by
  decide

/-- Cophonological evaluation with VBZ₂'s subranking selects the same
    winner as Tableau 25: (hāŋlā)₂(yáp)₃ with M-on-nonfinal,
    H-on-final. -/
theorem verbMH_cophEval_optimal :
    cophonologicalEval defaultRanking25 verbMH_CophVI.subranking
      t25_candidates = {t25e} := by
  decide

/-- Cophonological evaluation with VBZ₂'s pluractional subranking
    selects the same winner as Tableau 26: (jālpāt)₃(jálpát)₄. -/
theorem verbMH_plur_cophEval_optimal :
    cophonologicalEval defaultRanking26 verbMH_plur_CophVI.subranking
      t26_candidates = {t26d} := by
  decide

-- ============================================================================
-- S 15: Basemap Faithfulness of Tableau Winners
-- ============================================================================

/-! ### Connection to Matrix-Basemap Correspondence

The OT tableau winners exhibit zero basemap correspondence violations:
their surface tones exactly match what the basemap output would produce.
This structurally connects the anchor-constraint-based analysis to
@cite{rolle-2018}'s MxBM-C theory — *transparadigmatic uniformity* in
@cite{rolle-2018}'s sense, building on the OO-correspondence lineage
of @cite{benua-1997}. (Note: "transparadigmatic uniformity" is Rolle's
coinage; @cite{benua-1997}'s own term for the analogous pull is
"paradigmatic identity" / "OO-Identity".) -/

/-- The Tableau 24 winner's tones [M, M] match the basemap output
    for a whole-word M melody over a bisyllabic host. -/
theorem t24_winner_basemap_faithful :
    basemapViolations (t24e.output.map OutputTBU.tone) [.M, .M] = 0 := by
  decide

/-- The Tableau 25 winner's tones [M, M, H] match the basemap output
    for a nonfinal-M, final-H melody over a trisyllabic host. -/
theorem t25_winner_basemap_faithful :
    basemapViolations (t25e.output.map OutputTBU.tone) [.M, .M, .H] = 0 := by
  decide

/-- The Tableau 26 winner's tones [M, M, H, H] match the basemap
    output for M-on-reduplicant, H-on-base. -/
theorem t26_winner_basemap_faithful :
    basemapViolations
      (t26d.redOutput.map OutputTBU.tone ++ t26d.baseOutput.map OutputTBU.tone)
      [.M, .M, .H, .H] = 0 := by
  decide

-- ============================================================================
-- S 16: Generic ConstraintSystem Predictions
-- ============================================================================

/-! Each Mwaghavul tableau lifts to a generic `ConstraintSystem` via
`tableauSystem`. The deterministic OT winner gets probability 1
under the `argminDecoder`. -/

section PredictAPI
open Core.Constraint

/-- Tableau (24) as a generic `ConstraintSystem`. -/
noncomputable def t24System : ConstraintSystem SingleCand (LexProfile Nat 3) :=
  tableauSystem (mkTableau t24_candidates t24_ranking)

/-- Probability 1 on (24e): M on every TBU of wùlàʃ. -/
theorem t24System_predict_e : t24System.predict t24e = 1 :=
  tableauSystem_predict_unique_winner _ _ t24_optimal

/-- Tableau (25) as a generic `ConstraintSystem`. -/
noncomputable def t25System : ConstraintSystem SingleCand (LexProfile Nat 5) :=
  tableauSystem (mkTableau t25_candidates t25_ranking)

/-- Probability 1 on (25e): M-on-nonfinal, H-on-final for háŋláyáp. -/
theorem t25System_predict_e : t25System.predict t25e = 1 :=
  tableauSystem_predict_unique_winner _ _ t25_optimal

/-- Tableau (26) (pluractional) as a generic `ConstraintSystem`. -/
noncomputable def t26System : ConstraintSystem PlurCand (LexProfile Nat 5) :=
  tableauSystem (mkTableau t26_candidates t26_ranking)

/-- Probability 1 on (26d): M-on-reduplicant, H-on-base for jàlpàt. -/
theorem t26System_predict_d : t26System.predict t26d = 1 :=
  tableauSystem_predict_unique_winner _ _ t26_optimal

end PredictAPI

-- ============================================================================
-- S 17: Autosegmental Reanalysis via FloatingForm — INTEGRITY restored
-- ============================================================================

/-! ### Why this section exists

§§S1-S16 use a `OutputTBU = {tone, source : lex | gram}` candidate
type that **conflates spreading and copying**: both surface as
`[⟨M, gram⟩, ⟨M, gram⟩]` in `OutputTBU`. The paper's INTEGRITY-Mᵥ
constraint distinguishes them — paper p. 26 spells out that the
spreading candidate (24e) wins because the copying alternative (24f)
fatally violates INTEGRITY. The §S3 representation can't see this
distinction, so the existing analysis excludes (24f) by hand and omits
INTEGRITY.

The 2026 phonology mainstream — McCarthy & Prince Correspondence
Theory, Goldsmith-style autosegmental representation, McPherson 2022,
Rolle 2018, the present paper — treats spreading vs copying as
fundamentally distinct autosegmental objects: ONE multi-linked
autosegment vs MULTIPLE separate autosegments. The
`Phonology.Autosegmental.FloatingForm` substrate (originally built for
@cite{mcpherson-lamont-2026}) represents this natively via `ulTones`
(one entry per autosegment) + `surfaceLinks` (associations).

This section reanalyses tableau (24) over `FloatingForm Syl`, including
**both** spreading (24e) and copying (24f) as distinct candidates with
distinct `ulTones` lists. INTEGRITY-Mᵥ is implemented as
`integrityTone vbzMorph .M` from `Theories/Phonology/Tone/Constraints.lean`,
which counts `(alive ulTones with morpheme = vbz ∧ tone = M).card - 1`
(if positive). Spreading: 1 alive vbz M → 0 violations. Copying: 2
alive vbz Ms → 1 violation. Matches paper.

### Encoding choices

The wùlàʃ root has **one** lexical L autosegment multi-linked to both
TBUs (autosegmental convention; Goldsmith 1976). This is the right
autosegmental rep but differs from §S3's `OutputTBU` encoding (two
separate L tones). Per-autosegment MAX-T then matches paper p. 26
exactly: deleting the L = 1 violation; the §S3 per-TBU count gave 2.

Tableaux (25) and (26) are not reanalysed here — same autosegmental
treatment would apply but the candidate enumeration is larger; left
for follow-up. -/

namespace AutosegmentalReanalysis

open Phonology.Autosegmental
open Phonology.Autosegmental.RegisterTier (TRN)
open Core.Constraint.OT (DirectionalConstraint DirectionalTableau EvalMode)
open Phonology.Tone (integrityTone)

abbrev MwaghavulForm := FloatingForm Syl

/-- Morpheme IDs: `0` = root (wùlàʃ); `1` = M-tone verbaliser. Distinct
    Nats; the choice doesn't matter as long as they differ. -/
def rootMorph : MorphemeId := 0
def vbzMorph  : MorphemeId := 1

def rootSeg (s : Syl) : SegSpec Syl := { seg := s, morpheme := rootMorph }
def rootL : ToneSpec := { tone := TRN.L, morpheme := rootMorph }
def vbzM  : ToneSpec := { tone := TRN.M, morpheme := vbzMorph }

-- ----- Candidates (autosegmental encoding of paper Tableau 24) -----

/-- The faithful input shape: ulTones = [L (root, multi-linked), M (vbz,
    floating)]; ulLinks = {(0, 0), (0, 1)}. The L autosegment is one
    entry, multi-linked to both TBUs. Used as the underlying form of
    candidates (24a-e); (24f) shadows it with an extra M autosegment. -/
def baseInput : MwaghavulForm :=
  FloatingForm.mkInput
    (segs := [rootSeg ⟨"wù"⟩, rootSeg ⟨"làʃ"⟩])
    (ulTones := [rootL, vbzM])
    (ulLinks := {(0, 0), (0, 1)})

/-- (24a) Faithful: M still floating, L unchanged. -/
def t24a' : MwaghavulForm := baseInput

/-- (24b) M deleted: lexical L unchanged, verbaliser M gone. -/
def t24b' : MwaghavulForm := baseInput.deleteTone 1

/-- (24c) `(wù)₁(làʃ)₂`: L on TBU 0 only, M on TBU 1 only. Operations:
    delink L from TBU 1, link M to TBU 1. -/
def t24c' : MwaghavulForm := baseInput.deleteLink 0 1 |>.insertLink 1 1

/-- (24d) `(wū)₂(làʃ)₁`: M on TBU 0 only, L on TBU 1 only. -/
def t24d' : MwaghavulForm := baseInput.deleteLink 0 0 |>.insertLink 1 0

/-- (24e) ☞ `(wūlāʃ)₂` SPREADING: M multi-linked to both TBUs, L
    deleted. ONE M autosegment, two surface links. -/
def t24e' : MwaghavulForm :=
  baseInput.deleteTone 0 |>.insertLink 1 0 |>.insertLink 1 1

/-- (24f) `(wū)₂(lāʃ)₂` COPYING: TWO M autosegments, each linked to
    one TBU. L deleted. Different `ulTones` from (24a-e) — autosegmental
    representation has an extra M autosegment. -/
def t24f' : MwaghavulForm :=
  { baseInput with
    ulTones := [rootL, vbzM, vbzM]
    deletedTones := {0}
    surfaceLinks := {(1, 0), (2, 1)} }

def t24'_candidates : Finset MwaghavulForm :=
  {t24a', t24b', t24c', t24d', t24e', t24f'}

theorem t24'_nonempty : t24'_candidates.Nonempty := by decide

-- ----- Constraints over MwaghavulForm -----

/-- A TBU `i` bears a grammatical M tone: some surface link targets `i`
    from a vbz-morpheme M tone. -/
def isGramMTbu (f : MwaghavulForm) (i : SegIdx) : Bool :=
  (f.linksTo i).any fun k =>
    (f.ulTones[k]?).any fun ts => decide (ts.tone = TRN.M ∧ ts.morpheme = vbzMorph)

/-- L-ANCHOR-Mᵥ: number of segments before the leftmost gram-M TBU
    (or `segs.length` if no gram-M TBU exists). -/
def lAnchM (f : MwaghavulForm) : Nat :=
  match (List.range f.segs.length).findIdx? (isGramMTbu f) with
  | some i => i
  | none   => f.segs.length

/-- R-ANCHOR-Mᵥ. -/
def rAnchM (f : MwaghavulForm) : Nat :=
  match (List.range f.segs.length).reverse.findIdx? (isGramMTbu f) with
  | some i => i
  | none   => f.segs.length

/-- MAX-Tone (per autosegment): count deleted ulTones. Matches paper
    p. 26 per-autosegment counting; differs from §S2's per-TBU
    counting. -/
def maxToneAuto (f : MwaghavulForm) : Nat :=
  (List.range f.ulTones.length).countP (fun k => decide (f.IsDeleted k))

def integMv  : DirectionalConstraint MwaghavulForm := integrityTone vbzMorph TRN.M
def lAnchMv  : DirectionalConstraint MwaghavulForm where
  name := "L-ANCH-Mᵥ"
  family := .faithfulness
  eval := fun f => [lAnchM f]
def rAnchMv  : DirectionalConstraint MwaghavulForm where
  name := "R-ANCH-Mᵥ"
  family := .faithfulness
  eval := fun f => [rAnchM f]
def maxTone' : DirectionalConstraint MwaghavulForm where
  name := "MAX-Tone"
  family := .faithfulness
  eval := fun f => [maxToneAuto f]

/-- Tableau 24 ranking from paper §4.3:
    `INTEGRITY-Mᵥ ≫ L-ANCH-Mᵥ ≫ R-ANCH-Mᵥ ≫ MAX-Tone`. -/
def t24'_ranking : List (DirectionalConstraint MwaghavulForm) :=
  [integMv, lAnchMv, rAnchMv, maxTone']

def t24'_tableau : DirectionalTableau MwaghavulForm where
  candidates := t24'_candidates
  ranking := t24'_ranking
  evalMode := .parallel
  nonempty := t24'_nonempty

-- ----- Per-candidate violation profiles (matching paper Tableau 24) -----

/-- (24a) profile [INTEG, L-ANCH, R-ANCH, MAX-T] = [0, 2, 2, 0]: M
    floating, both anchors fail (no gram-M TBU), no deletions. -/
theorem t24a'_profile :
    t24'_ranking.map (fun c => c.eval t24a') = [[0], [2], [2], [0]] := by decide

/-- (24b) profile [0, 2, 2, 1]: M deleted, anchors still fail, MAX-T
    fires for the deleted M. -/
theorem t24b'_profile :
    t24'_ranking.map (fun c => c.eval t24b') = [[0], [2], [2], [1]] := by decide

/-- (24c) profile [0, 1, 0, 0]: M docks to TBU 1 only — L-ANCH violation
    (M not at left edge), R-ANCH satisfied, no deletions. -/
theorem t24c'_profile :
    t24'_ranking.map (fun c => c.eval t24c') = [[0], [1], [0], [0]] := by decide

/-- (24d) profile [0, 0, 1, 0]: M docks to TBU 0 only — L-ANCH
    satisfied, R-ANCH violation. -/
theorem t24d'_profile :
    t24'_ranking.map (fun c => c.eval t24d') = [[0], [0], [1], [0]] := by decide

/-- (24e) ☞ profile [0, 0, 0, 1]: M multi-linked to both TBUs (one
    autosegment, two links), L deleted. Anchors satisfied, INTEG
    satisfied (1 alive vbz M), MAX-T violated for L. The winner. -/
theorem t24e'_profile :
    t24'_ranking.map (fun c => c.eval t24e') = [[0], [0], [0], [1]] := by decide

/-- (24f) profile [1, 0, 0, 1]: TWO M autosegments, each linked to one
    TBU. Anchors satisfied, but INTEG fires (2 alive vbz Ms - 1 = 1).
    MAX-T = 1 for L deletion. INTEG is the fatal violation given
    INTEG ≫ L-ANCH ≫ R-ANCH ≫ MAX-T. **Newly includable** under the
    autosegmental encoding (was excluded in §S4). -/
theorem t24f'_profile :
    t24'_ranking.map (fun c => c.eval t24f') = [[1], [0], [0], [1]] := by decide

/-- **Headline**: under the paper-faithful ranking and candidate set
    (now including the copying variant (24f) excluded by §S4's
    representation), the spreading candidate (24e) is the unique
    optimum. INTEG-Mᵥ ≫ L-ANCH-Mᵥ ≫ R-ANCH-Mᵥ ≫ MAX-Tone selects (24e)
    over (24a-d) (which lose on anchors) and over (24f) (which loses
    on INTEG). -/
theorem t24'_optimal : t24'_tableau.optimal = {t24e'} := by decide

end AutosegmentalReanalysis

-- ============================================================================
-- S 18: Structural Lift to `Corr RedupRole OutputTBU`
-- ============================================================================

/-! ### Surface the substrate connection

The pluractional candidate type `PlurCand` already carries explicit
base + reduplicant outputs (`baseOutput`, `redOutput`). This section
lifts the candidate to the unifying `Corr RedupRole OutputTBU`
substrate from `Theories/Phonology/OptimalityTheory/Correspondence.lean`,
making the BR structure available to consumers expecting the
M&P 1995 correspondence-theoretic representation.

**Note on constraint derivation**: the existing constraints
(`lAnchorViolations`, `rAnchorViolations`, `maxToneViolations`) are
*predicate-positional measures* over single output strings — they
filter for output TBUs by `(source, tone)` predicate and count
positions. They are NOT naturally derived from `Corr.maxViol` /
`Corr.identViol` etc. (which are correspondence-relation operations).
The constraint *family* is faithfulness in @cite{akinbo-fwangwar-2026}'s
sense (faithfulness of the abstract verbaliser tone to its host's
edge), but the *implementation* doesn't reduce to a single Corr edge.

A future refactor could reformulate the verbaliser as an explicit
input-side morpheme with a `(.input, .reduplicant)` / `(.input, .base)`
correspondence edge for gram-source TBUs, then derive the anchor
counts from `Corr.anchorLViol`/`Corr.anchorRViol`-with-predicate.
That requires adding a `morphemeId`-tagged edge structure, which is
substantial. For now, the structural lift below provides the substrate
connection without re-deriving the constraints. -/

namespace PlurCorr

open Phonology.Correspondence (Corr RedupRole)

/-- Lift a `PlurCand` to a 3-role `Corr RedupRole OutputTBU` via
    `Corr.reduplication`. The `.input` form is the empty list (no
    explicit input segments in the paper's representation; verbaliser
    tones are abstract morphemes); `.base` and `.reduplicant` get the
    candidate's `baseOutput` and `redOutput` directly.

    The cross-role edges are the parallel-pair correspondences that
    `Corr.reduplication` builds by default. The `(.base, .reduplicant)`
    edge is structurally available for any future refactor that
    derives BR-correspondence-based constraints (e.g., a featural
    OO-IDENT comparing tone values position-by-position). -/
def toCorr (c : PlurCand) : Corr RedupRole OutputTBU :=
  Corr.reduplication [] c.baseOutput c.redOutput

@[simp] theorem toCorr_form_input (c : PlurCand) :
    (toCorr c).form .input = [] := rfl

@[simp] theorem toCorr_form_base (c : PlurCand) :
    (toCorr c).form .base = c.baseOutput := rfl

@[simp] theorem toCorr_form_reduplicant (c : PlurCand) :
    (toCorr c).form .reduplicant = c.redOutput := rfl

/-- The lifted Corr's `(.base, .reduplicant)` edge is the parallel-pair
    correspondence between the base and reduplicant outputs (truncated
    to `min` of their lengths). When the two outputs have the same
    length (the typical pluractional case where RED fully copies BASE),
    every position participates. -/
theorem toCorr_edge_base_reduplicant (c : PlurCand) :
    (toCorr c).edge .base .reduplicant =
      (Finset.range (min c.baseOutput.length c.redOutput.length)).image
        (fun i => (i, i)) := by
  simp [toCorr, Corr.reduplication, Corr.diagram_edge_of_true]

end PlurCorr

end AkinboFwangwar2026
