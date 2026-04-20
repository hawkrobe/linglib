import Linglib.Theories.Phonology.Process.Alternation
import Linglib.Theories.Phonology.OptimalityTheory.Constraints
import Linglib.Theories.Learning.TolerancePrinciple

/-!
# Belth (2026): A Learning-Based Account of Phonological Tiers @cite{belth-2026}

D2L (Distant-to-Local) is an iterative learner that constructs phonological
tiers as a *byproduct* of trying to express alternations as adjacent
dependencies. Given underlying-form / surface-form pairs, D2L starts by
projecting all segments and tries to predict the alternating segment from
its linear neighbours. When the resulting rule fails Yang's Tolerance
Principle @cite{yang-2016}, D2L deletes the offending segments from the
tier and tries again, until either a tolerated rule is found or no further
deletion helps.

The output of D2L is a tier-based alternation rule, modelled here by the
canonical `Phonology.Alternation.TierRule` schema (in
`Theories/Phonology/Alternation.lean`). This study formalizes:

- the Latin -alis / -aris allomorphy case (Belth §5.3) under D2L's *coarse*
  `[+cons]` tier, with stimulus-contrast theorems on the four worked
  examples (*navalis*, *popularis*, *floralis*, *legalis*);
- the **empirical limit** of the coarse rule: *lunaris* surfaces with
  `[r]`, but D2L's `[+cons]`-tier rule predicts `[l]` (the immediately
  preceding tier segment is the nasal `/n/`, which is `[−lat]`, so
  `Disagree` outputs `[+lat]`);
- a *finer* tier excluding nasals — the structural shape of the
  refinements proposed in @cite{cser-2010} — that captures *lunaris*
  correctly while still handling the four original examples;
- bridge theorems connecting the tier projection to the OCP constraint
  framework via `Theories/Phonology/Constraints.lean`'s `mkOCPOnTier`.

D2L's Turkish (Belth §5.1) and Finnish (§5.2) rules are sketched in §6
below. They require multi-feature dependencies and explicit Elsewhere
defaults; both extensions are admittable on demand following the
"infrastructure on demand" policy in `CLAUDE.md`.

**On verification scope.** D2L itself — the *learning* algorithm — is not
run inside Lean. Belth's empirical claim is that, given a corpus, D2L
*converges* to specific rules. Verifying that claim end-to-end would
require running D2L on naturalistic datasets (CHILDES, MorphoChallenge,
Perseus), which is out of scope for a Lean formalization. We instead
formalize the *learned rules* and verify their predictions on
representative examples.
-/

namespace Phenomena.PhonologicalAlternation.Studies.Belth2026

open Core
open Phonology.Alternation

-- ============================================================================
-- § 1: A Minimal Latin Alphabet
-- ============================================================================

/-- A minimal Latin segment alphabet sufficient for the -alis / -aris
    contrast.

    The unspecified affix-initial liquid is `L`; surface allomorphs are
    `l` and `r`. We include only the consonants and vowels appearing in
    the worked examples plus `n` (needed for *lunaris*). -/
inductive LatSeg where
  | a | e | i | o | u   -- vowels
  | l | r               -- liquids (surface)
  | L                   -- /L/, the unspecified affix-initial liquid
  | n | v | s | g | f | p | b   -- consonants from the worked examples
  deriving DecidableEq, Repr

namespace LatSeg

/-- `[+cons]` per @cite{cser-2010}'s feature inventory: every non-vowel
    is consonantal. `L` is also `[+cons]` — the underspecified `/L/`
    projects onto the consonant tier even though its `[lat]` value is
    not yet fixed. -/
def isCons : LatSeg → Bool
  | .a | .e | .i | .o | .u => false
  | _ => true

/-- `[+nasal]`: only `n` in the present inventory. Used to define the
    finer (Cser-style) tier that excludes nasals. -/
def isNasal : LatSeg → Bool
  | .n => true
  | _ => false

/-- `[+lat]` per @cite{cser-2010}: only `l` is lateral, and `L` is
    *underspecified* for `[lat]`. Returning `Option Bool` rather than
    `Bool` here avoids the older "junk default" pattern where `L` had
    to fake some concrete value — `none` is the honest answer. -/
def isLat : LatSeg → Option Bool
  | .l => some true
  | .L => none
  | _ => some false

/-- The coarse consonantal tier (Belth's learned tier for Latin). Every
    `[+cons]` segment projects. -/
def consTier : Tier LatSeg LatSeg := Tier.byClass isCons

/-- The finer (Cser-style) tier: `[+cons]` segments *minus* nasals. This
    is the structural shape of the refinements proposed in
    @cite{cser-2010} — what matters empirically is that the immediately
    preceding nasal `/n/` in /lun-aLis/ must not count as the
    tier-adjacent context. -/
def fineTier : Tier LatSeg LatSeg :=
  Tier.byClass (fun seg => isCons seg && !isNasal seg)

end LatSeg

-- ============================================================================
-- § 2: The Two Latin Rules
-- ============================================================================

/-- The rule D2L learns under the coarse `[+cons]` tier (Belth §5.3):
    `Disagree([?lat], {lat}) / [+cons] __ ∘ proj(·, [+cons])`. -/
def latinDissimCoarse : TierRule LatSeg where
  tier := LatSeg.consTier
  side := .left
  targetIsContext := LatSeg.isCons
  relation := .disagree
  featureValue := LatSeg.isLat
  default := none

/-- The empirically corrected rule using the finer tier (excluding
    nasals; cf. @cite{cser-2010}):
    `Disagree([?lat], {lat}) / [+cons,−nasal] __ ∘ proj(·, [+cons,−nasal])`.

    This rule preserves Belth's four worked examples *and* correctly
    predicts *lunaris*. -/
def latinDissimFine : TierRule LatSeg where
  tier := LatSeg.fineTier
  side := .left
  targetIsContext := fun seg => LatSeg.isCons seg && !LatSeg.isNasal seg
  relation := .disagree
  featureValue := LatSeg.isLat
  default := none

-- ============================================================================
-- § 3: Worked Examples (Belth §5.3)
-- ============================================================================

/-- Underlying form of *navalis* 'naval': /nav-aLis/. -/
def navalis_ur : List LatSeg :=
  [.n, .a, .v, .a, .L, .i, .s]

/-- Underlying form of *popularis* 'popular': /popul-aLis/. -/
def popularis_ur : List LatSeg :=
  [.p, .o, .p, .u, .l, .a, .L, .i, .s]

/-- Underlying form of *floralis* 'floral': /flor-aLis/. -/
def floralis_ur : List LatSeg :=
  [.f, .l, .o, .r, .a, .L, .i, .s]

/-- Underlying form of *legalis* 'legal': /leg-aLis/. -/
def legalis_ur : List LatSeg :=
  [.l, .e, .g, .a, .L, .i, .s]

/-- Underlying form of *lunaris* 'lunar': /lun-aLis/. The empirical
    counterexample to Belth's coarse-tier rule — surface is `[r]`, but
    the coarse rule's last `[+cons]` segment in `/lun-a/` is `/n/`,
    which is `[−lat]`, so `Disagree` would predict `[l]`. -/
def lunaris_ur : List LatSeg :=
  [.l, .u, .n, .a, .L, .i, .s]

/-- The position of `L` in each underlying form. -/
def navalis_lPos    : Nat := 4
def popularis_lPos  : Nat := 6
def floralis_lPos   : Nat := 5
def legalis_lPos    : Nat := 4
def lunaris_lPos    : Nat := 4

/-- Surface value predicted by the coarse-tier rule: `some true` =
    surfaces as `l`, `some false` = surfaces as `r`, `none` = the rule
    has no opinion. -/
def predictedCoarse (ur : List LatSeg) (lPos : Nat) : Option Bool :=
  latinDissimCoarse.applyAt (ur.take lPos)

/-- Surface value predicted by the fine-tier rule. -/
def predictedFine (ur : List LatSeg) (lPos : Nat) : Option Bool :=
  latinDissimFine.applyAt (ur.take lPos)

-- ============================================================================
-- § 4: Stimulus-Contrast Theorems for the Four Original Examples
-- ============================================================================

/-! Both the coarse and fine rules agree on Belth's four worked examples.
The contrast appears in §5 below for *lunaris*. -/

/-- *navalis*: tier-preceding consonant on the `[+cons]` tier is `v`
    (`[−lat]`), so by Disagree, /L/ surfaces as `[+lat]` = `l`. -/
theorem navalis_predicts_l_coarse :
    predictedCoarse navalis_ur navalis_lPos = some true := by decide

/-- The fine tier also handles *navalis* correctly: `/v/` is `[−nasal]`,
    so it survives the finer projection too. -/
theorem navalis_predicts_l_fine :
    predictedFine navalis_ur navalis_lPos = some true := by decide

/-- *popularis*: tier-preceding consonant is `l` (`[+lat]`), so by
    Disagree, /L/ surfaces as `[−lat]` = `r`. -/
theorem popularis_predicts_r_coarse :
    predictedCoarse popularis_ur popularis_lPos = some false := by decide

theorem popularis_predicts_r_fine :
    predictedFine popularis_ur popularis_lPos = some false := by decide

/-- *floralis*: tier-preceding consonant is `r` (`[−lat]`), so by
    Disagree, /L/ surfaces as `[+lat]` = `l`. The intervening `r` blocks
    the dissimilation that *popularis*'s preceding `l` would have
    triggered — exactly the long-distance pattern Belth's tier-projection
    is designed to capture. -/
theorem floralis_predicts_l_coarse :
    predictedCoarse floralis_ur floralis_lPos = some true := by decide

theorem floralis_predicts_l_fine :
    predictedFine floralis_ur floralis_lPos = some true := by decide

/-- *legalis*: tier-preceding consonant is `g` (`[−lat]`). The
    stem-initial `l` is hidden from /L/ by the intervening `g` on the
    consonant tier, so /L/ surfaces as `[+lat]` = `l`. -/
theorem legalis_predicts_l_coarse :
    predictedCoarse legalis_ur legalis_lPos = some true := by decide

theorem legalis_predicts_l_fine :
    predictedFine legalis_ur legalis_lPos = some true := by decide

/-- The minimal-pair contrast: *navalis* (l) vs *popularis* (r) differ
    because `v` projects onto the `[+cons]` tier with `[−lat]`, while
    `l` projects with `[+lat]`. This is the empirical signature D2L
    captures. -/
theorem navalis_popularis_minimal_pair_coarse :
    predictedCoarse navalis_ur navalis_lPos ≠
    predictedCoarse popularis_ur popularis_lPos := by decide

-- ============================================================================
-- § 5: The Empirical Limit — *lunaris*
-- ============================================================================

/-- *lunaris*: the COARSE tier rule predicts `l` (the last `[+cons]`
    segment in `/lun-a/` is the nasal `/n/`, `[−lat]`, so Disagree
    outputs `[+lat]`). This is the wrong prediction — the surface form
    is `[r]`. Belth's learned rule, on the corpus available to D2L,
    underextends. -/
theorem lunaris_coarse_predicts_l_INCORRECT :
    predictedCoarse lunaris_ur lunaris_lPos = some true := by decide

/-- *lunaris*: the FINE tier rule (nasals excluded) predicts `r`
    correctly — `/n/` is invisible to the projection, so the
    immediately preceding tier segment is `/l/`, `[+lat]`, and
    `Disagree` correctly outputs `[−lat]` = `[r]`. -/
theorem lunaris_fine_predicts_r :
    predictedFine lunaris_ur lunaris_lPos = some false := by decide

/-- The two rules disagree on *lunaris* — and the fine rule is the one
    that matches the empirical surface form. The structural lesson:
    D2L's coarse-tier output is *underextending*, missing the finer
    feature distinction that distinguishes nasal from non-nasal
    consonants in the relevant context class. -/
theorem coarse_fine_disagree_on_lunaris :
    predictedCoarse lunaris_ur lunaris_lPos ≠
    predictedFine lunaris_ur lunaris_lPos := by decide

-- ============================================================================
-- § 6: Per-Datum Coverage Rollup
-- ============================================================================

/-- Witness pairs `(underlying-form-prefix, surface-lat-value)` capturing
    the empirical surface for each worked example. -/
def latinData : List (List LatSeg × Bool) :=
  [(navalis_ur.take navalis_lPos,    true),    -- *navalis*  — l
   (popularis_ur.take popularis_lPos, false),  -- *popularis* — r
   (floralis_ur.take floralis_lPos,   true),   -- *floralis* — l
   (legalis_ur.take legalis_lPos,     true),   -- *legalis*  — l
   (lunaris_ur.take lunaris_lPos,     false)]  -- *lunaris*  — r

/-- The fine rule predicts every worked example correctly. The coarse
    rule fails on *lunaris* — see `lunaris_coarse_predicts_l_INCORRECT`
    above. -/
theorem latinDissimFine_covers_all :
    latinData.all (fun (pre, expected) =>
      latinDissimFine.applyAt pre == some expected) = true := by decide

/-- The coarse rule misses exactly one datum out of five (*lunaris*) —
    a 4/5 = 80% match on this minimal corpus. -/
theorem latinDissimCoarse_misses_lunaris :
    (latinData.filter (fun (pre, expected) =>
       !(latinDissimCoarse.applyAt pre == some expected))).length = 1 := by
  decide

-- ============================================================================
-- § 7: OCP-on-Tier Bridge (@cite{goldsmith-1976})
-- ============================================================================

/-- Belth's tier-based dissimilation rule has a natural OCP twin: the
    surface forms produced by the rule should not contain adjacent
    `[+lat]` segments on the relevant tier. We expose this connection
    via `Phonology.Constraints.mkOCPOnTier`, which already accepts a
    generic `Core.Tier` (since 0.229.875).

    `latinFineOCP` is the OCP constraint on a candidate-as-segment-list
    type evaluated against the fine consonantal tier. A tier-adjacent
    pair of identical liquids contributes one violation. -/
def latinFineOCP : Core.Constraint.OT.NamedConstraint (List LatSeg) :=
  Phonology.Constraints.mkOCPOnTier "OCP/[+cons,−nasal]" LatSeg.fineTier id

/-- The OCP constraint is a markedness constraint by construction. -/
theorem latinFineOCP_is_markedness :
    latinFineOCP.family = Core.Constraint.OT.ConstraintFamily.markedness :=
  Phonology.Constraints.mkOCPOnTier_is_markedness _ _ _

-- ============================================================================
-- § 8: D2L's Other Learned Rules (documentation only)
-- ============================================================================

/- ### Turkish (Belth §5.1)

D2L converges to two rules on Turkish CHILDES + MorphoChallenge data:

- (a) `Agree([?back], {back, round}) / [−cons] __ ∘ proj(·, [−cons])`
  — vowel harmony: an unspecified vowel takes its `[back]` value (and
  `[round]` value, if also unspecified) from the immediately
  tier-preceding vowel on the vocalic tier.
- (b) `Agree([?voice], {voice}) / [*] __`
  — voicing assimilation: the projection component is the *trivial*
  identity tier (every segment projects). This is the strict-locality
  case captured generically by
  `Phonology.Alternation.TierRule.id_tier_left_is_strict_local`.

D2L's reported test accuracy on the two corpora exceeds 0.98, beating
Hayes-Wilson generative phonotactic learners (@cite{hayes-wilson-2008})
and LSTM baselines (Belth Table 5; values not transcribed here, see paper).

### Finnish (Belth §5.2)

- (a) `Agree([?back], {back}) / [−cons] __ ∘ proj(·, [−cons] ∖ {i, e})`
  — backness harmony skipping the neutral vowels `{i, e}`. D2L learns
  that the neutral vowels must be deleted from the tier, matching the
  descriptive analysis in @cite{ringen-heinamaki-1999}.
- (b) `Elsewhere [−back]` — the default-value rule (Belth §2.3.3) for
  stems containing only neutral vowels. In our schema, this corresponds
  to `default := some false` on the corresponding `TierRule`.

These rules instantiate the same `TierRule` schema used above for
Latin, with two extensions deferred:

  1. *Multi-feature dependencies* — Turkish back/round harmony agrees
     on the *combined* `[back, round]` feature set, requiring a
     generalisation of `featureValue : α → Option Bool` to `α → List
     (Option Bool)` plus a parasitic condition (round only spreads if
     back agrees).
  2. *Default values* — Finnish (b) is already supported by the
     `default` field on `TierRule`; only the multi-feature wrinkle
     blocks a full Finnish formalization here.

Both extensions are admittable on demand. The Latin case above
suffices to demonstrate the schema, the empirical-limit pattern
(*lunaris*), and the OCP-tier bridge.
-/

end Phenomena.PhonologicalAlternation.Studies.Belth2026
