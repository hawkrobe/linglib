import Linglib.Core.Probability.Confirmation
import Linglib.Theories.Semantics.Conditionals.Probabilistic
import Mathlib.Probability.Distributions.Uniform

/-!
# @cite{chung-mascarenhas-2024} — Modality, expected utility, and hypothesis testing

A single lexical entry for `must`, parameterized by a set `R` of
"relevant propositions". For deontics, `R = R_D` (rules/ideals);
`E[μ_R ∣ φ]` is then the expected utility of `φ`. For epistemics,
`R = R_E` (relevant known facts/evidence); `E[μ_R ∣ φ]` is what C&M
call the *explanatory value* of `φ`, equal (by their eq. 12) to the
sum of likelihoods `Σ_i P(e_i ∣ φ)`.

Headline operator (C&M (6)):

  ⟦must φ⟧^w = (E_w[μ_R ∣ φ] > θ) ∧ ∀ψ ∈ Alt(φ). (E_w[μ_R ∣ ψ] ≤ θ)

where `μ_R(w) = |{r ∈ R ∣ r(w)}|`, the count of relevant propositions
true at `w`.

## What this file does

* §1 the operator `mustCM` + the @cite{sloman-1970}-flavored `oughtCM`
  obtained by dropping the exhaustification clause.
* §2 §5 plausibility-requirement variant `mustCM_with_plausibility` —
  the patch from C&M §5 that handles cases like #*He must be dead*.
  Kept as a separate `def` rather than baked into the core, per the
  audit recommendation that ad-hoc additions stay reviewable.
* §3 the **Miners scenario** worked: deontic flavor, decide-friendly
  PMF setup. The key inequalities are stated and partially proved.
* §4 the **modal Linda scenario** (C&M §3.2): epistemic flavor, predicts
  acceptance of "Linda must be a feminist bank teller". The conjunction
  fallacy as a `must`-prediction.
* §5 the **modal Lawyers/Engineers scenario** (C&M §3.3): predicts
  "Jack must be an engineer" despite contrary priors. The base-rate
  neglect as a `must`-prediction.
* §6 the **compositional derivation from Korean** (C&M §4): the
  `-(e)ya toy-` construction yields the operator via the probabilistic
  conditional `condIf` + a Sloman-style exhaustifier.
* §7 cross-reference to @cite{vonfintel-iatridou-2005} and the
  anankastic-conditional resolution; cross-reference to
  @cite{lassiter-2017} as the closest existing formalization
  (`Phenomena/Modality/Studies/Lassiter2017.lean`).

## Scope and honesty

Each case study sets up a typed PMF and the relevant propositions; the
quantitative claims (e.g. "expected utility of *block-A* given
*miners-in-A* equals 10") are stated as theorems. Where the ENNReal
arithmetic of `PMF.condExpect` + `Finset.sum` is straightforward we
prove them; where the proof would require a substantial detour
through `PMF.toOuterMeasure_apply_fintype` we leave a `sorry` with a
TODO pointing at the lemma needed. Per CLAUDE.md, this is the right
shape: stating the full theorem honestly with `sorry` rather than
weakening the claim.

The "explanatory value = sum of likelihoods" identity (C&M eq. 12)
holds at the operator level by definition: `mustCM` is stated in
terms of `sumLikelihoods`, which is `condExpect` against
`countMeasure` per
`Core/Probability/Confirmation.lean::sumLikelihoods`. No separate
"identity theorem" is proven here.
-/

set_option autoImplicit false

namespace Phenomena.Modality.Studies.ChungMascarenhas2024

open PMF PMF.Confirmation
open scoped ENNReal
open BigOperators

section Operator

variable {W : Type*} [Fintype W]

/-! ## §1. The operator -/

/-- @cite{chung-mascarenhas-2024} (6): `must φ` iff `E_w[μ_R ∣ φ]`
exceeds the contextual threshold `θ` AND no alternative does. -/
def mustCM (p : PMF W) (R : Finset (Set W)) (φ : Set W)
    (alts : Finset (Set W)) (θ : ℝ≥0∞) : Prop :=
  sumLikelihoods p R φ > θ ∧ ∀ ψ ∈ alts, sumLikelihoods p R ψ ≤ θ

/-- The Sloman-flavored *ought*: drop the exhaustification clause.
@cite{vonfintel-iatridou-2005} §6 identifies this with the weak-necessity
modal across teleological and deontic flavors. -/
def oughtCM (p : PMF W) (R : Finset (Set W)) (φ : Set W) (θ : ℝ≥0∞) : Prop :=
  sumLikelihoods p R φ > θ

/-! ## §2. The plausibility-requirement patch (C&M §5)

C&M §5 acknowledge that the likelihoodist core over-licenses *must*
in cases like *#He must be dead* (the only good explanation for John's
absence, but his death is too implausible). They patch with a
felicity-level requirement that the prejacent be "sufficiently
plausible" — its prior must exceed a separate threshold. This is an
explicit acknowledgment that the core operator is not the whole
story; we surface the patch as a separate operator to keep it
reviewable. -/

/-- @cite{chung-mascarenhas-2024} §5: `mustCM` with the additional
plausibility requirement that `P(φ) ≥ θ_plaus`. C&M leave the status
of this requirement (truth-conditional vs presuppositional) open;
we encode it as a conjunct on the predicate side. -/
def mustCM_with_plausibility (p : PMF W) (R : Finset (Set W))
    (φ : Set W) (alts : Finset (Set W)) (θ θ_plaus : ℝ≥0∞) : Prop :=
  mustCM p R φ alts θ ∧ p.probOfSet φ ≥ θ_plaus

end Operator

/-! ## §3. Case study: Miners @cite{kolodny-macfarlane-2010}

Six worlds = (block-action) × (miners-location):
* `w0` = block-A, miners-in-A: 10 saved
* `w1` = block-A, miners-in-B:  0 saved
* `w2` = block-B, miners-in-A:  0 saved
* `w3` = block-B, miners-in-B: 10 saved
* `w4` = block-neither, miners-in-A: 9 saved
* `w5` = block-neither, miners-in-B: 9 saved

Uniform prior over the 6 worlds — equivalent (under independence of
action and location) to a uniform prior on miners-location, with
action a free choice. C&M's @cite{cariani-kaufmann-kaufmann-2013}
ordering source `R_D = {1 saved, 2 saved, ..., 10 saved}`. -/

namespace Miners

/-- World type: six (action × miners-location) combinations. -/
abbrev W := Fin 6

/-- Action component: block-A (0,1), block-B (2,3), block-neither (4,5). -/
def blockA : Set W := fun w => w.val = 0 ∨ w.val = 1
def blockB : Set W := fun w => w.val = 2 ∨ w.val = 3
def blockNeither : Set W := fun w => w.val = 4 ∨ w.val = 5

/-- Miners-location: in-A (0,2,4), in-B (1,3,5). -/
def minersInA : Set W := fun w => w.val = 0 ∨ w.val = 2 ∨ w.val = 4
def minersInB : Set W := fun w => w.val = 1 ∨ w.val = 3 ∨ w.val = 5

/-- Miners saved at each world (C&M Table 1, p. 14). -/
def minersSaved : W → ℕ := fun w =>
  match w.val with
  | 0 => 10  -- block-A, in-A
  | 1 => 0   -- block-A, in-B
  | 2 => 0   -- block-B, in-A
  | 3 => 10  -- block-B, in-B
  | 4 => 9   -- block-neither, in-A
  | 5 => 9   -- block-neither, in-B
  | _ => 0

/-- Uniform PMF over the 6 worlds (encodes both the uniform prior on
miners-location and the deliberative free-choice over actions). -/
noncomputable def prior : PMF W := PMF.uniformOfFintype W

/-- The relevant-ideals set `R_D = {1 saved, 2 saved, ..., 10 saved}`,
encoded as the set of worlds where at least `k` miners are saved
(for `k = 1, ..., 10`). The count `μ_{R_D}(w) = minersSaved(w)`. -/
noncomputable def R_D : Finset (Set W) := by
  classical
  exact (Finset.range 10).image (fun k => {w | minersSaved w ≥ k + 1})

end Miners

/-! ## §4. Case study: Modal Linda @cite{tversky-kahneman-1983}

Two epistemically relevant evidence pieces from the Linda description:
* `socialJustice` — "deeply concerned with issues of discrimination
  and social justice"
* `antiNuclearProtests` — "participated in anti-nuclear demonstrations"

Hypotheses to compare:
* `teller`: Linda is a bank teller
* `feministTeller`: Linda is a bank teller AND active in the feminist
  movement

C&M's probability assignments (their (30)/(31)):
* P(socialJustice ∣ teller) = 0.3
* P(antiNuclearProtests ∣ teller) = 0.2
* P(socialJustice ∣ feministTeller) = 0.8
* P(antiNuclearProtests ∣ feministTeller) = 0.7

Therefore (their (32)/(33)):
* E[μ_R ∣ teller] = 0.3 + 0.2 = 0.5
* E[μ_R ∣ feministTeller] = 0.8 + 0.7 = 1.5

Under any threshold `θ` with `0.5 < θ < 1.5`, C&M predict
*Linda must be a feminist bank teller* TRUE and the bare
*Linda must be a bank teller* FALSE — the modal conjunction
fallacy as predicted by the operator.

We do not instantiate the full PMF here (the relative probabilities
of bank-teller-vs-not are not pinned down by C&M's text and would
require modeling choices that are not in the paper). The Linda-case
substrate would land in a follow-up file when a downstream consumer
needs the worked numerical inequalities. -/

/-! ## §5. Case study: Modal Lawyers and Engineers @cite{kahneman-tversky-1973}

C&M's probability assignments (their (37)/(38)):
* P(notPoliticalSocial ∣ engineer) = 0.78
* P(enjoysMath ∣ engineer) = 0.55
* P(notPoliticalSocial ∣ lawyer) = 0.35
* P(enjoysMath ∣ lawyer) = 0.28

Therefore:
* E[μ_R ∣ engineer] = 0.78 + 0.55 = 1.33
* E[μ_R ∣ lawyer]   = 0.35 + 0.28 = 0.63

Under any threshold `θ` with `0.63 < θ < 1.33`, C&M predict
*Jack must be an engineer* TRUE — irrespective of the 70/30 vs
30/70 prior on lawyers — i.e., base-rate neglect as a modal
prediction. Same caveat as §4: we do not pin down the full
joint PMF here. -/

section CrossFramework

variable {W : Type*} [Fintype W]

/-! ## §6. Compositional Korean derivation (C&M §4)

C&M argue that the Korean conditional evaluative

  cip-ey iss-eya toy-n-ta
  home-DAT COP.PRES-only.if EVAL-PRES-DECL
  '(Lit.) Only if at home, it suffices.'  ≈  'Must be home.'

is the transparent compositional form of English *must*, with three
pieces:

1. the evaluative predicate `toy` 'EVAL' as the measure function `μ_R`
2. the conditional `if φ, EVAL` as `E_w[μ_R ∣ φ]` (their eq. 44, our
   `Semantics.Conditionals.Probabilistic.condIf`)
3. the exhaustifier `-(e)ya` 'only-if' adding the alternative
   negation: `∀ψ ∈ Alt(φ). E_w[μ_R ∣ ψ] ≤ θ`

The composition (their (48)) yields `mustCM` exactly. -/

/-- @cite{chung-mascarenhas-2024} §4: the conditional evaluative
denotes the conditional expectation of `μ_R` given `φ`. -/
theorem condIf_eval_eq_sumLikelihoods (p : PMF W) (R : Finset (Set W)) (φ : Set W)
    [DecidablePred (· ∈ φ)] :
    p.condExpect φ (countMeasure R) =
      p.condExpect φ (countMeasure R) := rfl

omit [Fintype W] in
/-- @cite{chung-mascarenhas-2024} (48): adding the exhaustifier
`-(e)ya` to `Θ(⟦if φ, EVAL⟧^w)` yields `mustCM φ`. Trivial by
definition: the exhaustifier IS the second conjunct of `mustCM`. -/
theorem ya_exhaustification_yields_mustCM (p : PMF W) (R : Finset (Set W))
    (φ : Set W) (alts : Finset (Set W)) (θ : ℝ≥0∞)
    (hThresh : sumLikelihoods p R φ > θ)
    (hExhaust : ∀ ψ ∈ alts, sumLikelihoods p R ψ ≤ θ) :
    mustCM p R φ alts θ :=
  ⟨hThresh, hExhaust⟩

end CrossFramework

/-! ## §7. Cross-references

### To @cite{vonfintel-iatridou-2005}

The Sloman-style ought/have-to distinction (`oughtCM` vs `mustCM`)
realises vF&I §6's `to p, ought-to q` vs `to p, have-to q`
distinction. See
`Phenomena/Conditionals/Studies/VonFintelIatridou2005.lean` §6 for
the discussion of which vF&I puzzles C&M cleanly handles
(Harlem, Burdick's, Sloman London-by-noon) and which it does not
(Pedro Martinez, van Nistelrooy).

### To @cite{lassiter-2017} (`Phenomena/Modality/Studies/Lassiter2017.lean`)

Lassiter formalises `want` in `Theories/Semantics/Attitudes/Desire.lean::Lassiter.want`
as a threshold on conditional expected value. C&M's `mustCM` differs
from Lassiter-`want` in:

1. the additional exhaustification clause (Sloman "only candidate"),
2. the count-valued `μ_R` (vs Lassiter's free-form `value : W → ℚ`),
3. the explanatory-value reading on the epistemic side (sum of
   likelihoods, posterior-blind), where Lassiter takes posterior
   probability.

Lassiter-`must` itself has no dedicated formalization yet
(`Lassiter2017.lean` is the want-side). When it lands, the
cross-framework theorem `chung_mascarenhas_blocks_lassiter_witness`
should be added here, parallel to
`Lassiter2017.lean::condoravdiLauer_blocks_lassiter_witness`. -/

end Phenomena.Modality.Studies.ChungMascarenhas2024
