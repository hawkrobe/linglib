import Linglib.Pragmatics.RSA.Operators
import Linglib.Pragmatics.RSA.LatentOperators
import Linglib.Pragmatics.RSA.Silence
import Linglib.Core.Probability.Posterior
import Linglib.Core.Probability.Eval
import Linglib.Semantics.Alternatives.Lexical
import Mathlib.Data.ENNReal.Inv

/-!
# [potts-etal-2016]: Embedded Implicatures as Pragmatic Inferences
[potts-etal-2016] [chemla-spector-2011]

"Embedded Implicatures as Pragmatic Inferences under Compositional Lexical
Uncertainty." Journal of Semantics 33(4): 755–802.

## Empirical anchor: [chemla-spector-2011]

The 3-players × 3-outcomes architecture is structurally the same as
CS11's *every/exactly one/no* × *some/all* design (CS11 uses 6 letters
× 3 cell-states for Exp 1, 3 letters for Exp 2). The LU model's
predictions — DE prefers weak lexicon (NNN reading), UE prefers strong
(SSS embedded SI) — match CS11's qualitative findings: STRONG > WEAK
in universal contexts (Exp 1) and LOCAL > FALSE in non-monotonic
(Exp 2). The LU model is *silent* on the attitude-verb gradient that
CS11 doesn't test (think > want > all > must, from
[geurts-pouscoulous-2009]).

## The Puzzle

Scalar implicatures interact asymmetrically with logical operators:

- **UE (upward-entailing)**: "Every player hit some of his shots" →
  embedded implicature "some but not all" (enriched reading SSS preferred)
- **DE (downward-entailing)**: "No player hit some of his shots" →
  global reading preferred, no embedded implicature (NNN preferred)

## The Model: Compositional Lexical Uncertainty

The key innovation is **lexical uncertainty**: L1 marginalizes over possible
lexica (refinements of "some") rather than using a fixed literal semantics.
This file formalizes the paper's **neo-Gricean refinement** model variant
(their (19d), refining only "some" to the two-element set
`{⟦some⟧, ⟦some and not all⟧}` of (14)) — *not* their unconstrained-refinement
model (19c), whose listener marginalizes over the full refinement lattice
`℘(⟦some⟧) ∖ ∅`. The two refinements are:
- **Weak**: "some" = "at least one" (the unrefined lower-bound `⟦some⟧`)
- **Strong**: "some" = "some but not all" (the maximal enrichment)

The PMF stack mirrors [goodman-stuhlmuller-2013]'s latent-uncertainty model
on mathlib `PMF`, with `Latent := Lexicon`:

* `L0 lex u : PMF World` — `RSA.L0OfBoolMeaning` (uniform on the extension).
* `S1 lex w : PMF Utterance` — `RSA.S1Belief (L0 lex) (fun _ => 1) 1 w`
  (α = 1, no utterance cost): normalises `L0 lex u w` over utterances.
* `marginalSpeaker w : PMF Utterance` — `RSA.marginalizeKernel` of `S1`
  against the uniform `Lexicon` prior.
* `L1 u : PMF World` — `PMF.posterior marginalSpeaker (uniform World) u`.

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

open scoped ENNReal

namespace PottsEtAl2016

/-! ### Domain types -/

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

/-- Statement: outer quantifier × inner quantifier. -/
abbrev Stmt := PlayerQ × ShotQ

/-- Utterance: a statement, or silence (`none`) — the null utterance, true at
every world. -/
abbrev Utterance := RSA.WithSilence Stmt

/-- Lexicon: how "some" is interpreted. -/
inductive Lexicon where
  | weak   -- "some" = at least one (lower-bound)
  | strong -- "some" = some but not all (enriched)
  deriving DecidableEq, Repr, Inhabited, Fintype

/-! ### World count functions -/

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

/-! ### Truth conditions (lexicon-parameterized) -/

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

/-- Truth value of a statement in a world under a lexicon. -/
def stmtTruth (lex : Lexicon) : Stmt → World → Bool
  | (pq, sq), w =>
    let n := predCount sq lex w
    match pq with
    | .every => n == 3
    | .exactlyOne => n == 1
    | .no => n == 0

/-- Truth value of an utterance under a lexicon: `stmtTruth` with silence
true at every world. -/
def utteranceTruth (lex : Lexicon) : Utterance → World → Bool :=
  RSA.liftMeaning (stmtTruth lex)

/-! ### Structural properties

The lexicon affects only "some"; "all" and "none" are unambiguous. The DE/UE
asymmetry is a *widening vs. narrowing* fact about the strong lexicon's
extension under each outer quantifier. -/

/-- Lexica agree on all "all"-utterances; the lexicon only refines "some". -/
theorem lexica_agree_on_all :
    ∀ pq w, utteranceTruth .weak (some (pq, .all)) w =
            utteranceTruth .strong (some (pq, .all)) w := by decide

/-- Lexica agree on all "none"-utterances. -/
theorem lexica_agree_on_none :
    ∀ pq w, utteranceTruth .weak (some (pq, .none_)) w =
            utteranceTruth .strong (some (pq, .none_)) w := by decide

/-- DE context: strong "some" *widens* the set of true worlds relative to weak.
    Under "no player hit some of his shots":
    - Weak "some": only NNN satisfies (1 world)
    - Strong "some": NNN, NNA, NAA, AAA satisfy (4 worlds)
    Widening makes the utterance less informative under the strong lexicon. -/
theorem de_enrichment_widens :
    (Finset.univ.filter (fun w => utteranceTruth .weak (some (.no, .some_)) w = true)).card <
    (Finset.univ.filter (fun w => utteranceTruth .strong (some (.no, .some_)) w = true)).card := by
  decide

/-- UE context: strong "some" *narrows* the set of true worlds relative to weak.
    Under "every player hit some of his shots":
    - Weak "some": SSS, SSA, SAA, AAA satisfy (4 worlds)
    - Strong "some": only SSS satisfies (1 world)
    Narrowing makes the utterance more informative under the strong lexicon. -/
theorem ue_enrichment_narrows :
    (Finset.univ.filter (fun w => utteranceTruth .strong (some (.every, .some_)) w = true)).card <
    (Finset.univ.filter (fun w => utteranceTruth .weak (some (.every, .some_)) w = true)).card := by
  decide

/-! ### Literal listener `L0`

Per-lexicon literal listener via `RSA.L0OfBoolMeaning`: uniform on the
extension of the (lexicon-parameterised) meaning function. Every utterance has
a non-empty extension (every quantifier is true at some world, and `null` is
true everywhere), so the `Nonempty` precondition is universal. -/

/-- Every `(lexicon, utterance)` has a non-empty extension. -/
theorem ext_nonempty (lex : Lexicon) (u : Utterance) :
    (RSA.extensionOf (utteranceTruth lex) u).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  cases lex <;> rcases u with _ | ⟨pq, sq⟩ <;>
    first | decide | (cases pq <;> cases sq <;> decide)

/-- Per-lexicon literal listener: uniform on the extension. -/
noncomputable def L0 (lex : Lexicon) (u : Utterance) : PMF World :=
  RSA.L0OfBoolMeaning (utteranceTruth lex) u (ext_nonempty lex u)

/-- Closed-form `L0` value: `ENNReal.ofReal (1 / |extension|)` at true worlds,
`0` otherwise. The `pmf_eval_simps`-friendly if-form. -/
theorem L0_apply (lex : Lexicon) (u : Utterance) (w : World) :
    L0 lex u w =
      if utteranceTruth lex u w
      then ENNReal.ofReal (((RSA.extensionOf (utteranceTruth lex) u).card : ℝ))⁻¹
      else 0 := by
  unfold L0
  by_cases h : utteranceTruth lex u w
  · rw [if_pos h, RSA.L0OfBoolMeaning_apply_of_mem _ h,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos]
    exact_mod_cast Finset.card_pos.mpr (ext_nonempty lex u)
  · rw [if_neg h, RSA.L0OfBoolMeaning_apply_of_not_mem _ (by simpa using h)]

/-- `L0 lex none w = ofReal (1/10)`: silence is true at every world, so its
extension is all 10 worlds. Used to discharge the speaker normaliser's
positivity hypothesis. -/
theorem L0_null (lex : Lexicon) (w : World) :
    L0 lex none w = ENNReal.ofReal ((10 : ℝ))⁻¹ := by
  rw [L0_apply, if_pos (by simp [utteranceTruth]),
      show RSA.extensionOf (utteranceTruth lex) none = Finset.univ by
        simp [utteranceTruth],
      show (Finset.univ : Finset World).card = 10 by rfl]
  norm_num

/-- Sum-over-`Utterance` unfolder (silence + the 9 statements), proved by
`rfl`. Local-tagged for `pmf_eval_simps` so partition sums reduce to a
concrete 10-term sum. -/
theorem Utterance_sum_univ {β : Type*} [AddCommMonoid β] (f : Utterance → β) :
    ∑ i, f i =
      f none + (f (some (.every, .all)) + (f (some (.every, .none_)) +
      (f (some (.every, .some_)) + (f (some (.exactlyOne, .all)) +
      (f (some (.exactlyOne, .none_)) + (f (some (.exactlyOne, .some_)) +
      (f (some (.no, .all)) + (f (some (.no, .none_)) +
      (f (some (.no, .some_)) + 0))))))))) := by rfl

/-! ### Extension cardinalities

Per-`(lexicon, utterance)` extension sizes, `decide`-checked and locally tagged
for `pmf_eval_simps` so `L0_apply` reduces to concrete `ofReal((c)⁻¹)` values.
The local tag keeps these private paper-specific cards out of the substrate
simp set (audit hygiene rule, following `GoodmanStuhlmuller2013`). -/

private theorem card_w_ea : (RSA.extensionOf (utteranceTruth .weak) (some (.every, .all))).card = 1 := by decide
private theorem card_w_en : (RSA.extensionOf (utteranceTruth .weak) (some (.every, .none_))).card = 1 := by decide
private theorem card_w_es : (RSA.extensionOf (utteranceTruth .weak) (some (.every, .some_))).card = 4 := by decide
private theorem card_w_oa : (RSA.extensionOf (utteranceTruth .weak) (some (.exactlyOne, .all))).card = 3 := by decide
private theorem card_w_on : (RSA.extensionOf (utteranceTruth .weak) (some (.exactlyOne, .none_))).card = 3 := by decide
private theorem card_w_os : (RSA.extensionOf (utteranceTruth .weak) (some (.exactlyOne, .some_))).card = 2 := by decide
private theorem card_w_na : (RSA.extensionOf (utteranceTruth .weak) (some (.no, .all))).card = 4 := by decide
private theorem card_w_nn : (RSA.extensionOf (utteranceTruth .weak) (some (.no, .none_))).card = 4 := by decide
private theorem card_w_ns : (RSA.extensionOf (utteranceTruth .weak) (some (.no, .some_))).card = 1 := by decide
private theorem card_w_nu : (RSA.extensionOf (utteranceTruth .weak) none).card = 10 := by decide
private theorem card_s_ea : (RSA.extensionOf (utteranceTruth .strong) (some (.every, .all))).card = 1 := by decide
private theorem card_s_en : (RSA.extensionOf (utteranceTruth .strong) (some (.every, .none_))).card = 1 := by decide
private theorem card_s_es : (RSA.extensionOf (utteranceTruth .strong) (some (.every, .some_))).card = 1 := by decide
private theorem card_s_oa : (RSA.extensionOf (utteranceTruth .strong) (some (.exactlyOne, .all))).card = 3 := by decide
private theorem card_s_on : (RSA.extensionOf (utteranceTruth .strong) (some (.exactlyOne, .none_))).card = 3 := by decide
private theorem card_s_os : (RSA.extensionOf (utteranceTruth .strong) (some (.exactlyOne, .some_))).card = 3 := by decide
private theorem card_s_na : (RSA.extensionOf (utteranceTruth .strong) (some (.no, .all))).card = 4 := by decide
private theorem card_s_nn : (RSA.extensionOf (utteranceTruth .strong) (some (.no, .none_))).card = 4 := by decide
private theorem card_s_ns : (RSA.extensionOf (utteranceTruth .strong) (some (.no, .some_))).card = 4 := by decide
private theorem card_s_nu : (RSA.extensionOf (utteranceTruth .strong) none).card = 10 := by decide

attribute [local pmf_eval_simps] L0_apply Utterance_sum_univ
  card_w_ea card_w_en card_w_es card_w_oa card_w_on card_w_os card_w_na card_w_nn card_w_ns card_w_nu
  card_s_ea card_s_en card_s_es card_s_oa card_s_on card_s_os card_s_na card_s_nn card_s_ns card_s_nu

/-! ### Speaker normaliser `Z`

`S1Belief` with α = 1 and unit cost has score `(L0 u w)^1 · 1 = L0 u w`, so the
partition function is `Z lex w = ∑' u, L0 lex u w`. Each value is `ofReal` of a
rational; the closed forms below are computed by `simp +decide only
[pmf_eval_simps, ...]` (reducing to a sum of concrete `ofReal (c⁻¹)` terms)
followed by explicit `ENNReal.ofReal_add` folding and `norm_num`. -/

/-- With α = 1 and unit cost, the speaker score is just `L0 lex u w`. -/
theorem score_eq (lex : Lexicon) (w : World) (u : Utterance) :
    (L0 lex u w : ℝ≥0∞) ^ (1 : ℝ) * 1 = L0 lex u w := by rw [ENNReal.rpow_one, mul_one]

/-- The `S1Belief` normaliser at `(lexicon, world)`. -/
noncomputable def Z (lex : Lexicon) (w : World) : ℝ≥0∞ :=
  ∑' u, (L0 lex u w : ℝ≥0∞) ^ (1 : ℝ) * 1

theorem Z_eq_sum (lex : Lexicon) (w : World) : Z lex w = ∑' u, L0 lex u w := by
  unfold Z; simp_rw [score_eq]

theorem Z_ne_top (lex : Lexicon) (w : World) : Z lex w ≠ ∞ := by
  rw [Z_eq_sum]; exact ENNReal.tsum_ne_top_of_fintype (fun u => PMF.apply_ne_top _ _)

/-- The speaker normaliser is non-zero: `null` is true everywhere, contributing
`ofReal (1/10) ≠ 0`. -/
theorem Z_ne_zero (lex : Lexicon) (w : World) :
    (∑' u, (L0 lex u w : ℝ≥0∞) ^ (1 : ℝ) * 1) ≠ 0 := by
  rw [show (∑' u, (L0 lex u w : ℝ≥0∞) ^ (1 : ℝ) * 1) = Z lex w from rfl, Z_eq_sum]
  refine ENNReal.summable.tsum_ne_zero_iff.mpr ⟨none, ?_⟩
  rw [L0_null]; simp

-- DE partitions (under "no … some"): NNN, AAA where the comparison lives.
private theorem Z_w_NNN : Z .weak .NNN = ENNReal.ofReal (47 / 20) := by
  rw [Z_eq_sum, tsum_fintype]
  simp +decide only [pmf_eval_simps, ↓reduceIte, add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num
private theorem Z_s_NNN : Z .strong .NNN = ENNReal.ofReal (8 / 5) := by
  rw [Z_eq_sum, tsum_fintype]
  simp +decide only [pmf_eval_simps, ↓reduceIte, add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num
private theorem Z_s_NNA : Z .strong .NNA = ENNReal.ofReal (41 / 60) := by
  rw [Z_eq_sum, tsum_fintype]
  simp +decide only [pmf_eval_simps, ↓reduceIte, add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num
private theorem Z_s_NAA : Z .strong .NAA = ENNReal.ofReal (41 / 60) := by
  rw [Z_eq_sum, tsum_fintype]
  simp +decide only [pmf_eval_simps, ↓reduceIte, add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num
private theorem Z_s_AAA : Z .strong .AAA = ENNReal.ofReal (8 / 5) := by
  rw [Z_eq_sum, tsum_fintype]
  simp +decide only [pmf_eval_simps, ↓reduceIte, add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num
-- UE partitions (under "every … some"): SSS, SSA, SAA, AAA.
private theorem Z_w_SSS : Z .weak .SSS = ENNReal.ofReal (17 / 20) := by
  rw [Z_eq_sum, tsum_fintype]
  simp +decide only [pmf_eval_simps, ↓reduceIte, add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num
private theorem Z_s_SSS : Z .strong .SSS = ENNReal.ofReal (8 / 5) := by
  rw [Z_eq_sum, tsum_fintype]
  simp +decide only [pmf_eval_simps, ↓reduceIte, add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num
private theorem Z_w_SSA : Z .weak .SSA = ENNReal.ofReal (14 / 15) := by
  rw [Z_eq_sum, tsum_fintype]
  simp +decide only [pmf_eval_simps, ↓reduceIte, add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num
private theorem Z_w_SAA : Z .weak .SAA = ENNReal.ofReal (3 / 5) := by
  rw [Z_eq_sum, tsum_fintype]
  simp +decide only [pmf_eval_simps, ↓reduceIte, add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num
private theorem Z_w_AAA : Z .weak .AAA = ENNReal.ofReal (8 / 5) := by
  rw [Z_eq_sum, tsum_fintype]
  simp +decide only [pmf_eval_simps, ↓reduceIte, add_zero, zero_add]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

/-! ### Per-lexicon speaker `S1`

`RSA.S1Belief (L0 lex) (fun _ => 1) 1 w`: normalises `L0 lex u w` over
utterances at the fixed world `w`. The closed-form values are
`ofReal (L0-value · Z⁻¹)`. -/

/-- Per-lexicon speaker (α = 1, no cost). -/
noncomputable def S1 (lex : Lexicon) (w : World) : PMF Utterance :=
  RSA.S1Belief (L0 lex) (fun _ => 1) 1 w (Z_ne_zero lex w)
    (by rw [show (∑' u, (L0 lex u w : ℝ≥0∞) ^ (1 : ℝ) * 1) = Z lex w from rfl]
        exact Z_ne_top lex w)

theorem S1_apply (lex : Lexicon) (w : World) (u : Utterance) :
    S1 lex w u = (L0 lex u w) ^ (1 : ℝ) * 1 * (Z lex w)⁻¹ := by
  unfold S1; rw [RSA.S1Belief_apply]; rfl

/-- Speaker value when the utterance is **false** at the world: `L0 = 0`, so
`S1 = 0`. -/
private theorem S1_eq_zero (lex : Lexicon) (w : World) (u : Utterance)
    (h : utteranceTruth lex u w = false) : S1 lex w u = 0 := by
  rw [S1_apply, score_eq, L0_apply, if_neg (by rw [h]; simp)]; simp

/-- Speaker value when the utterance is **true**: `ofReal (1/c · 1/Z)`, computed
from the extension cardinality `c` and the partition `Z`. -/
private theorem S1_eq_ofReal (lex : Lexicon) (w : World) (u : Utterance)
    (c : ℕ) (hc : 0 < c) (zr : ℝ) (hzr : 0 < zr)
    (htrue : utteranceTruth lex u w = true)
    (hcard : (RSA.extensionOf (utteranceTruth lex) u).card = c)
    (hZ : Z lex w = ENNReal.ofReal zr) :
    S1 lex w u = ENNReal.ofReal ((c : ℝ)⁻¹ * zr⁻¹) := by
  rw [S1_apply, score_eq, L0_apply, if_pos htrue, hcard, hZ,
      ← ENNReal.ofReal_inv_of_pos hzr, ← ENNReal.ofReal_mul (by positivity)]

/-! ### Marginal speaker over lexica

`RSA.marginalizeKernel` against the uniform `Lexicon` prior. Over the 2-element
`Lexicon`, `marginalSpeaker w u = (1/2)·S1 weak w u + (1/2)·S1 strong w u`. -/

/-- Marginal speaker: marginalises `S1` over a uniform `Lexicon` prior. -/
noncomputable def marginalSpeaker (w : World) : PMF Utterance :=
  RSA.marginalizeKernel (PMF.uniformOfFintype Lexicon) (fun lex w => S1 lex w) w

private theorem Lexicon_sum_univ {β : Type*} [AddCommMonoid β] (f : Lexicon → β) :
    ∑ i, f i = f .weak + (f .strong + 0) := by rfl

private theorem uniformLex_apply (lex : Lexicon) :
    (PMF.uniformOfFintype Lexicon) lex = ENNReal.ofReal (1 / 2) := by
  rw [PMF.uniformOfFintype_apply, show Fintype.card Lexicon = 2 from by decide,
      show ((2 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num,
      ← ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- Marginal speaker as the explicit `(1/2, 1/2)`-weighted lexicon mixture. -/
theorem marginalSpeaker_apply (w : World) (u : Utterance) :
    marginalSpeaker w u =
      ENNReal.ofReal (1 / 2) * S1 .weak w u + (ENNReal.ofReal (1 / 2) * S1 .strong w u + 0) := by
  unfold marginalSpeaker
  rw [RSA.marginalizeKernel_apply, tsum_fintype, Lexicon_sum_univ,
      uniformLex_apply, uniformLex_apply]

/-! ### Marginal-speaker closed forms (per prediction cell)

The 8 cells the predictions compare, each `ofReal` of a rational. DE worlds
under "no … some"; UE worlds under "every … some". Values match the LU model's
hand-computation (α = 1, uniform priors). -/

private theorem ms_DE_NNN : marginalSpeaker .NNN (some (.no, .some_)) = ENNReal.ofReal (875 / 3008) := by
  rw [marginalSpeaker_apply,
      S1_eq_ofReal .weak .NNN _ 1 (by norm_num) (47 / 20) (by norm_num) (by decide) card_w_ns Z_w_NNN,
      S1_eq_ofReal .strong .NNN _ 4 (by norm_num) (8 / 5) (by norm_num) (by decide) card_s_ns Z_s_NNN,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      add_zero, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

private theorem ms_DE_NNA : marginalSpeaker .NNA (some (.no, .some_)) = ENNReal.ofReal (15 / 82) := by
  rw [marginalSpeaker_apply, S1_eq_zero .weak .NNA _ (by decide),
      S1_eq_ofReal .strong .NNA _ 4 (by norm_num) (41 / 60) (by norm_num) (by decide) card_s_ns Z_s_NNA,
      mul_zero, zero_add, add_zero, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; norm_num

private theorem ms_DE_NAA : marginalSpeaker .NAA (some (.no, .some_)) = ENNReal.ofReal (15 / 82) := by
  rw [marginalSpeaker_apply, S1_eq_zero .weak .NAA _ (by decide),
      S1_eq_ofReal .strong .NAA _ 4 (by norm_num) (41 / 60) (by norm_num) (by decide) card_s_ns Z_s_NAA,
      mul_zero, zero_add, add_zero, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; norm_num

private theorem ms_DE_AAA : marginalSpeaker .AAA (some (.no, .some_)) = ENNReal.ofReal (5 / 64) := by
  rw [marginalSpeaker_apply, S1_eq_zero .weak .AAA _ (by decide),
      S1_eq_ofReal .strong .AAA _ 4 (by norm_num) (8 / 5) (by norm_num) (by decide) card_s_ns Z_s_AAA,
      mul_zero, zero_add, add_zero, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; norm_num

private theorem ms_UE_SSS : marginalSpeaker .SSS (some (.every, .some_)) = ENNReal.ofReal (125 / 272) := by
  rw [marginalSpeaker_apply,
      S1_eq_ofReal .weak .SSS _ 4 (by norm_num) (17 / 20) (by norm_num) (by decide) card_w_es Z_w_SSS,
      S1_eq_ofReal .strong .SSS _ 1 (by norm_num) (8 / 5) (by norm_num) (by decide) card_s_es Z_s_SSS,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      add_zero, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

private theorem ms_UE_SSA : marginalSpeaker .SSA (some (.every, .some_)) = ENNReal.ofReal (15 / 112) := by
  rw [marginalSpeaker_apply,
      S1_eq_ofReal .weak .SSA _ 4 (by norm_num) (14 / 15) (by norm_num) (by decide) card_w_es Z_w_SSA,
      S1_eq_zero .strong .SSA _ (by decide),
      mul_zero, add_zero, add_zero, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; norm_num

private theorem ms_UE_SAA : marginalSpeaker .SAA (some (.every, .some_)) = ENNReal.ofReal (5 / 24) := by
  rw [marginalSpeaker_apply,
      S1_eq_ofReal .weak .SAA _ 4 (by norm_num) (3 / 5) (by norm_num) (by decide) card_w_es Z_w_SAA,
      S1_eq_zero .strong .SAA _ (by decide),
      mul_zero, add_zero, add_zero, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; norm_num

private theorem ms_UE_AAA : marginalSpeaker .AAA (some (.every, .some_)) = ENNReal.ofReal (5 / 64) := by
  rw [marginalSpeaker_apply,
      S1_eq_ofReal .weak .AAA _ 4 (by norm_num) (8 / 5) (by norm_num) (by decide) card_w_es Z_w_AAA,
      S1_eq_zero .strong .AAA _ (by decide),
      mul_zero, add_zero, add_zero, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; norm_num

/-! ### Pragmatic listener `L1`

`PMF.posterior marginalSpeaker (uniform World) u`. The marginal positivity
hypotheses are discharged via `PMF.marginal_ne_zero` with the target world as
witness (`marginalSpeaker w u ≠ 0` for the relevant `(w, u)`). -/

private theorem hMarg_DE :
    PMF.marginal marginalSpeaker (PMF.uniformOfFintype World) (some (.no, .some_)) ≠ 0 := by
  refine PMF.marginal_ne_zero marginalSpeaker _ _ (a := World.NNN) ?_ ?_
  · exact (PMF.uniformOfFintype World).mem_support_iff World.NNN |>.mp
      (PMF.mem_support_uniformOfFintype World.NNN)
  · rw [ms_DE_NNN]; simp

private theorem hMarg_UE :
    PMF.marginal marginalSpeaker (PMF.uniformOfFintype World) (some (.every, .some_)) ≠ 0 := by
  refine PMF.marginal_ne_zero marginalSpeaker _ _ (a := World.SSS) ?_ ?_
  · exact (PMF.uniformOfFintype World).mem_support_iff World.SSS |>.mp
      (PMF.mem_support_uniformOfFintype World.SSS)
  · rw [ms_UE_SSS]; simp

/-- Pragmatic listener: Bayesian inversion of `marginalSpeaker` against the
uniform world prior. -/
noncomputable def L1 (u : Utterance)
    (h : PMF.marginal marginalSpeaker (PMF.uniformOfFintype World) u ≠ 0) : PMF World :=
  PMF.posterior marginalSpeaker (PMF.uniformOfFintype World) u h

/-! ### Predictions: DE blocking

"No player hit some of his shots" → NNN preferred.

Under the weak lexicon, only NNN makes the utterance true (1 world, maximally
informative). Under the strong lexicon, NNN, NNA, NAA, and AAA all make it true
(4 worlds, less informative). L1 marginalizes over lexica weighted by
informativity, preferring the weak lexicon for this utterance. Result: NNN
receives the highest posterior — the global reading. -/

/-- DE blocking: NNN > NNA. -/
theorem de_blocking_NNN_vs_NNA :
    L1 (some (.no, .some_)) hMarg_DE .NNN > L1 (some (.no, .some_)) hMarg_DE .NNA := by
  rw [L1, gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform, ms_DE_NNA, ms_DE_NNN]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-- DE blocking: NNN > NAA. -/
theorem de_blocking_NNN_vs_NAA :
    L1 (some (.no, .some_)) hMarg_DE .NNN > L1 (some (.no, .some_)) hMarg_DE .NAA := by
  rw [L1, gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform, ms_DE_NAA, ms_DE_NNN]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-- DE blocking: NNN > AAA. -/
theorem de_blocking_NNN_vs_AAA :
    L1 (some (.no, .some_)) hMarg_DE .NNN > L1 (some (.no, .some_)) hMarg_DE .AAA := by
  rw [L1, gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform, ms_DE_AAA, ms_DE_NNN]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-! ### Predictions: UE enrichment

"Every player hit some of his shots" → SSS preferred.

Under the strong lexicon, only SSS makes the utterance true (1 world, maximally
informative). Under the weak lexicon, SSS, SSA, SAA, and AAA all make it true
(4 worlds, less informative). L1 marginalizes and prefers the informative
strong lexicon for this utterance. Result: SSS receives the highest posterior —
the embedded implicature. -/

/-- UE enrichment: SSS > SSA. -/
theorem ue_enrichment_SSS_vs_SSA :
    L1 (some (.every, .some_)) hMarg_UE .SSS > L1 (some (.every, .some_)) hMarg_UE .SSA := by
  rw [L1, gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform, ms_UE_SSA, ms_UE_SSS]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-- UE enrichment: SSS > SAA. -/
theorem ue_enrichment_SSS_vs_SAA :
    L1 (some (.every, .some_)) hMarg_UE .SSS > L1 (some (.every, .some_)) hMarg_UE .SAA := by
  rw [L1, gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform, ms_UE_SAA, ms_UE_SSS]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-- UE enrichment: SSS > AAA. -/
theorem ue_enrichment_SSS_vs_AAA :
    L1 (some (.every, .some_)) hMarg_UE .SSS > L1 (some (.every, .some_)) hMarg_UE .AAA := by
  rw [L1, gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform, ms_UE_AAA, ms_UE_SSS]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-! ### Grounding: outer quantifiers

The outer quantifiers "every" and "no" in the [potts-etal-2016] model agree
with the shared quantifier semantics `Alternatives.Quantifiers.worldMeaning`.
This grounds the stipulated `utteranceTruth` in the shared quantifier
infrastructure.

Compare `GoodmanStuhlmuller2013`'s `qMeaning`, an independent implementation
of the same count-threshold semantics. -/

private theorem predCount_lt_four (sq : ShotQ) (lex : Lexicon) (w : World) :
    predCount sq lex w < 4 := by
  cases sq <;> cases lex <;> cases w <;> decide

/-- "Every player hit X" ↔ `worldMeaning 3 .all` applied to `predCount`. -/
theorem outer_every_grounded (sq : ShotQ) (lex : Lexicon) (w : World) :
    utteranceTruth lex (some (.every, sq)) w =
    Alternatives.Quantifiers.worldMeaning 3 .all
      ⟨⟨predCount sq lex w, predCount_lt_four sq lex w⟩⟩ := by
  cases sq <;> cases lex <;> cases w <;> decide

/-- "No player hit X" ↔ `worldMeaning 3 .none_` applied to `predCount`. -/
theorem outer_no_grounded (sq : ShotQ) (lex : Lexicon) (w : World) :
    utteranceTruth lex (some (.no, sq)) w =
    Alternatives.Quantifiers.worldMeaning 3 .none_
      ⟨⟨predCount sq lex w, predCount_lt_four sq lex w⟩⟩ := by
  cases sq <;> cases lex <;> cases w <;> decide

/-! ### Cross-study connections

The [potts-etal-2016] predictions connect to two other parts of linglib:

1. **`Geurts2010`** (`ScalarImplicatures.Studies.Geurts2010`): Notes that the
   minimal LU model inverts the predictions, but "the full Potts et al. model
   derives the correct pattern." The theorems here are the formal backing.

2. **`EmbeddedSIPrediction`** (`LexicalUncertainty.Compositional`): Tracks
   embedded SI predictions by context type. The Potts model demonstrates the
   negation case: local reading dispreferred in DE (global NNN preferred). -/

end PottsEtAl2016
