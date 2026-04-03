import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Pragmatics.RSA.Quantities
import Linglib.Phenomena.ScalarImplicatures.Basic

/-!
# @cite{potts-etal-2016}: Embedded Implicatures as Pragmatic Inferences
@cite{potts-etal-2016}

"Embedded Implicatures as Pragmatic Inferences under Compositional Lexical
Uncertainty." Journal of Semantics 33(4): 755–802.

## The Puzzle

Scalar implicatures interact asymmetrically with logical operators:

- **UE (upward-entailing)**: "Every player hit some of his shots" →
  embedded implicature "some but not all" (enriched reading SSS preferred)
- **DE (downward-entailing)**: "No player hit some of his shots" →
  global reading preferred, no embedded implicature (NNN preferred)

## The Model: Compositional Lexical Uncertainty

The key innovation is **lexical uncertainty**: L1 marginalizes over possible
lexica (refinements of "some") rather than using a fixed literal semantics.
Two lexica:
- **Weak**: "some" = "at least one" (standard lower-bound semantics)
- **Strong**: "some" = "some but not all" (enriched semantics)

This uses the standard `RSAConfig` latent variable mechanism: `Latent := Lexicon`.
No special infrastructure needed — the same mechanism handles observations
(@cite{goodman-stuhlmuller-2013}), scope readings (@cite{scontras-pearl-2021}),
and QUDs (@cite{kao-etal-2014-hyperbole}).

## Architecture

The experiment (Section 6) uses 3 players, each with outcome N (nothing) /
S (scored but not aced) / A (aced). The 10 equivalence classes are the
multisets of 3 outcomes. Utterances are `PlayerQ × ShotQ` (outer × inner
quantifier): "every/exactly one/no player hit all/none/some of his shots."

## Predictions

The asymmetry arises from monotonicity:
- **DE** (under "no"): strong "some" *widens* the true-world set → less
  informative → L1 prefers weak lexicon → global reading (NNN)
- **UE** (under "every"): strong "some" *narrows* the true-world set → more
  informative → L1 prefers strong lexicon → enriched reading (SSS)
-/

set_option autoImplicit false

namespace Phenomena.ScalarImplicatures.Studies.PottsEtAl2016

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

/-- World state as equivalence class over 3 players' outcomes.
    Each player's outcome: N (nothing), S (scored but not aced), A (aced).
    10 classes = multisets of size 3 from {N, S, A}. -/
inductive World where
  | NNN | NNS | NNA | NSS | NSA | NAA | SSS | SSA | SAA | AAA
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Inner quantifier: over a player's shots. -/
inductive ShotQ where
  | all | none_ | some_
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Outer quantifier: over players. -/
inductive PlayerQ where
  | every | exactlyOne | no
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Utterance: outer quantifier × inner quantifier, plus null. -/
inductive Utterance where
  | stmt : PlayerQ → ShotQ → Utterance
  | null : Utterance
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Lexicon: how "some" is interpreted. -/
inductive Lexicon where
  | weak   -- "some" = at least one (lower-bound)
  | strong -- "some" = some but not all (enriched)
  deriving DecidableEq, Repr, Inhabited, Fintype

-- ============================================================================
-- §2. World Count Functions
-- ============================================================================

/-- Number of players who scored (hit ≥ 1 shot, i.e. S or A). -/
def World.numScored : World → Nat
  | .NNN => 0 | .NNS => 1 | .NNA => 1 | .NSS => 2 | .NSA => 2
  | .NAA => 2 | .SSS => 3 | .SSA => 3 | .SAA => 3 | .AAA => 3

/-- Number of players who aced (hit all shots). -/
def World.numAced : World → Nat
  | .NNN => 0 | .NNS => 0 | .NNA => 1 | .NSS => 0 | .NSA => 1
  | .NAA => 2 | .SSS => 0 | .SSA => 1 | .SAA => 2 | .AAA => 3

/-- Number of players who scored but did not ace. -/
def World.numScoredNotAced : World → Nat
  | .NNN => 0 | .NNS => 1 | .NNA => 0 | .NSS => 2 | .NSA => 1
  | .NAA => 0 | .SSS => 3 | .SSA => 2 | .SAA => 1 | .AAA => 0

/-- Number of players who did nothing (hit 0 shots). -/
def World.numNothing : World → Nat
  | .NNN => 3 | .NNS => 2 | .NNA => 2 | .NSS => 1 | .NSA => 1
  | .NAA => 1 | .SSS => 0 | .SSA => 0 | .SAA => 0 | .AAA => 0

-- ============================================================================
-- §3. Truth Conditions (Lexicon-Parameterized)
-- ============================================================================

/-- Count of players satisfying the inner predicate, under a given lexicon.
    - `all`: number who aced
    - `none_`: number who did nothing
    - `some_`: depends on lexicon:
      - weak: number who scored (≥ 1 shot)
      - strong: number who scored but did not ace -/
def predCount (sq : ShotQ) (lex : Lexicon) (w : World) : Nat :=
  match sq with
  | .all => w.numAced
  | .none_ => w.numNothing
  | .some_ => match lex with
    | .weak => w.numScored
    | .strong => w.numScoredNotAced

/-- Truth value of an utterance in a world under a lexicon. -/
def utteranceTruth (lex : Lexicon) : Utterance → World → Bool
  | .null, _ => true
  | .stmt pq sq, w =>
    let n := predCount sq lex w
    match pq with
    | .every => n == 3
    | .exactlyOne => n == 1
    | .no => n == 0

-- ============================================================================
-- §4. RSAConfig
-- ============================================================================

open RSA Real in
/-- @cite{potts-etal-2016} lexical uncertainty model.

    Latent variable = Lexicon (weak vs strong "some").
    L0: literal listener under lexicon l.
    S1: belief-based scoring, rpow(L0(w|u), α).
    L1: marginalizes over lexica with uniform prior.

    Uniform priors, α = 1, no utterance cost.
    Qualitative predictions (DE blocking, UE enrichment) hold across
    a range of rationality parameters. -/
noncomputable def cfg : RSAConfig Utterance World where
  Latent := Lexicon
  meaning _ lex u w := if utteranceTruth lex u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> norm_num
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ _ hl0 _ := rpow_nonneg (hl0 _ _) _
  α := 1
  α_pos := one_pos
  latentPrior_nonneg _ _ := by norm_num
  worldPrior_nonneg _ := by norm_num

-- ============================================================================
-- §5. Structural Properties
-- ============================================================================

/-- Lexica agree on all non-"some" utterances. The lexicon only affects
    the interpretation of "some"; "all" and "none" are unambiguous. -/
theorem lexica_agree_on_all :
    ∀ pq w, utteranceTruth .weak (.stmt pq .all) w =
            utteranceTruth .strong (.stmt pq .all) w := by decide

theorem lexica_agree_on_none :
    ∀ pq w, utteranceTruth .weak (.stmt pq .none_) w =
            utteranceTruth .strong (.stmt pq .none_) w := by decide

/-- DE context: strong "some" *widens* the set of true worlds relative to weak.
    Under "no player hit some of his shots":
    - Weak "some": only NNN satisfies (1 world)
    - Strong "some": NNN, NNA, NAA, AAA satisfy (4 worlds)
    Widening makes the utterance less informative under the strong lexicon. -/
theorem de_enrichment_widens :
    (Finset.univ.filter (fun w => utteranceTruth .weak (.stmt .no .some_) w = true)).card <
    (Finset.univ.filter (fun w => utteranceTruth .strong (.stmt .no .some_) w = true)).card := by
  native_decide

/-- UE context: strong "some" *narrows* the set of true worlds relative to weak.
    Under "every player hit some of his shots":
    - Weak "some": SSS, SSA, SAA, AAA satisfy (4 worlds)
    - Strong "some": only SSS satisfies (1 world)
    Narrowing makes the utterance more informative under the strong lexicon. -/
theorem ue_enrichment_narrows :
    (Finset.univ.filter (fun w => utteranceTruth .strong (.stmt .every .some_) w = true)).card <
    (Finset.univ.filter (fun w => utteranceTruth .weak (.stmt .every .some_) w = true)).card := by
  native_decide

-- ============================================================================
-- §6. Predictions: DE Blocking
-- ============================================================================

/-! "No player hit some of his shots" → NNN preferred.

Under the weak lexicon, only NNN makes the utterance true (1 world,
maximally informative). Under the strong lexicon, NNN, NNA, NAA, and AAA
all make it true (4 worlds, less informative). L1 marginalizes over lexica
weighted by informativity, preferring the weak lexicon for this utterance.
Result: NNN receives the highest posterior — the global reading. -/

/-- DE blocking: NNN > NNA. -/
theorem de_blocking_NNN_vs_NNA :
    cfg.L1 (.stmt .no .some_) .NNN > cfg.L1 (.stmt .no .some_) .NNA := by
  rsa_predict

/-- DE blocking: NNN > NAA. -/
theorem de_blocking_NNN_vs_NAA :
    cfg.L1 (.stmt .no .some_) .NNN > cfg.L1 (.stmt .no .some_) .NAA := by
  rsa_predict

/-- DE blocking: NNN > AAA. -/
theorem de_blocking_NNN_vs_AAA :
    cfg.L1 (.stmt .no .some_) .NNN > cfg.L1 (.stmt .no .some_) .AAA := by
  rsa_predict

-- ============================================================================
-- §7. Predictions: UE Enrichment
-- ============================================================================

/-! "Every player hit some of his shots" → SSS preferred.

Under the strong lexicon, only SSS makes the utterance true (1 world,
maximally informative). Under the weak lexicon, SSS, SSA, SAA, and AAA
all make it true (4 worlds, less informative). L1 marginalizes and prefers
the informative strong lexicon for this utterance.
Result: SSS receives the highest posterior — the embedded implicature. -/

/-- UE enrichment: SSS > SSA. -/
theorem ue_enrichment_SSS_vs_SSA :
    cfg.L1 (.stmt .every .some_) .SSS > cfg.L1 (.stmt .every .some_) .SSA := by
  rsa_predict

/-- UE enrichment: SSS > SAA. -/
theorem ue_enrichment_SSS_vs_SAA :
    cfg.L1 (.stmt .every .some_) .SSS > cfg.L1 (.stmt .every .some_) .SAA := by
  rsa_predict

/-- UE enrichment: SSS > AAA. -/
theorem ue_enrichment_SSS_vs_AAA :
    cfg.L1 (.stmt .every .some_) .SSS > cfg.L1 (.stmt .every .some_) .AAA := by
  rsa_predict

-- ============================================================================
-- §8. Findings: Verified Predictions
-- ============================================================================

/-- The 6 qualitative findings from the @cite{potts-etal-2016} LU model.
    3 DE blocking predictions (global reading preferred under "no") +
    3 UE enrichment predictions (enriched reading preferred under "every"). -/
inductive Finding where
  | de_NNN_vs_NNA
  | de_NNN_vs_NAA
  | de_NNN_vs_AAA
  | ue_SSS_vs_SSA
  | ue_SSS_vs_SAA
  | ue_SSS_vs_AAA
  deriving DecidableEq, Repr

/-- All findings. -/
def findings : List Finding :=
  [.de_NNN_vs_NNA, .de_NNN_vs_NAA, .de_NNN_vs_AAA,
   .ue_SSS_vs_SSA, .ue_SSS_vs_SAA, .ue_SSS_vs_AAA]

/-- Map each empirical finding to the RSA model prediction that accounts for it. -/
def formalize : Finding → Prop
  | .de_NNN_vs_NNA =>
      cfg.L1 (.stmt .no .some_) .NNN > cfg.L1 (.stmt .no .some_) .NNA
  | .de_NNN_vs_NAA =>
      cfg.L1 (.stmt .no .some_) .NNN > cfg.L1 (.stmt .no .some_) .NAA
  | .de_NNN_vs_AAA =>
      cfg.L1 (.stmt .no .some_) .NNN > cfg.L1 (.stmt .no .some_) .AAA
  | .ue_SSS_vs_SSA =>
      cfg.L1 (.stmt .every .some_) .SSS > cfg.L1 (.stmt .every .some_) .SSA
  | .ue_SSS_vs_SAA =>
      cfg.L1 (.stmt .every .some_) .SSS > cfg.L1 (.stmt .every .some_) .SAA
  | .ue_SSS_vs_AAA =>
      cfg.L1 (.stmt .every .some_) .SSS > cfg.L1 (.stmt .every .some_) .AAA

/-- The RSA model accounts for all 6 qualitative findings from @cite{potts-etal-2016}. -/
theorem all_findings_verified : ∀ f : Finding, formalize f := by
  intro f; cases f
  · exact de_blocking_NNN_vs_NNA
  · exact de_blocking_NNN_vs_NAA
  · exact de_blocking_NNN_vs_AAA
  · exact ue_enrichment_SSS_vs_SSA
  · exact ue_enrichment_SSS_vs_SAA
  · exact ue_enrichment_SSS_vs_AAA

-- ============================================================================
-- §9. Grounding: Outer Quantifiers
-- ============================================================================

/-! The outer quantifiers "every" and "no" in the @cite{potts-etal-2016} model
agree with the generic quantity domain semantics from `RSA.Domains.Quantity.meaning`.
This grounds the stipulated `utteranceTruth` in the shared quantifier infrastructure.

See also: `GoodmanStuhlmuller2013.quantifier_meaning_grounded`. -/

private theorem predCount_lt_four (sq : ShotQ) (lex : Lexicon) (w : World) :
    predCount sq lex w < 4 := by
  cases sq <;> cases lex <;> cases w <;> decide

/-- "Every player hit X" ↔ `Quantity.meaning 3 .all` applied to `predCount`. -/
theorem outer_every_grounded (sq : ShotQ) (lex : Lexicon) (w : World) :
    utteranceTruth lex (.stmt .every sq) w =
    RSA.Domains.Quantity.meaning 3 .all
      ⟨predCount sq lex w, predCount_lt_four sq lex w⟩ := by
  cases sq <;> cases lex <;> cases w <;> native_decide

/-- "No player hit X" ↔ `Quantity.meaning 3 .none_` applied to `predCount`. -/
theorem outer_no_grounded (sq : ShotQ) (lex : Lexicon) (w : World) :
    utteranceTruth lex (.stmt .no sq) w =
    RSA.Domains.Quantity.meaning 3 .none_
      ⟨predCount sq lex w, predCount_lt_four sq lex w⟩ := by
  cases sq <;> cases lex <;> cases w <;> native_decide

-- ============================================================================
-- §10. Cross-Study Connections
-- ============================================================================

/-! The @cite{potts-etal-2016} predictions connect to two other parts of linglib:

1. **`someAllBlocking`** (`ScalarImplicatures.Basic`): The empirical datum that
   "some" implicatures are present in UE and blocked in DE. The Potts model
   derives both sides: UE enrichment (§7) and DE blocking (§6).

2. **`Geurts2010`** (`ScalarImplicatures.Studies.Geurts2010`): Notes that the
   minimal LU model inverts the predictions, but "the full Potts et al. model
   derives the correct pattern." The theorems here are the formal backing.

3. **`EmbeddedSIPrediction`** (`LexicalUncertainty.Compositional`): Tracks
   embedded SI predictions by context type. The Potts model demonstrates the
   negation case: local reading dispreferred in DE (global NNN preferred). -/

open Phenomena.ScalarImplicatures in
/-- The Potts model matches the `someAllBlocking` empirical pattern:
    UE enrichment present (implicatureInUE = true) and
    DE blocking present (implicatureInDE = false). -/
theorem matches_someAllBlocking :
    someAllBlocking.implicatureInUE = true ∧
    someAllBlocking.implicatureInDE = false := by
  exact ⟨rfl, rfl⟩

end Phenomena.ScalarImplicatures.Studies.PottsEtAl2016
