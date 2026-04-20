import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Wug-Test Paradigm

@cite{berko-1958}
@cite{albright-hayes-2003}

Shared vocabulary for the *wug paradigm*: subjects are presented with
nonce (novel) lexical items and asked to produce, judge, or rate
forms. Because nonce items are by construction unlisted, a wug
response cannot be a rote recall — it must be the output of a
productive generalisation.

## Architectural role

`Paradigms/` is the contract layer between `Theories/` and
`Phenomena/Studies/`. A wug study provides a typed cell whose
`Attestation` factor can be swapped between `attested` (a real lexeme)
and `novel` (a wug). The paradigm-level predicates in §4 quantify over
the lens, so any theory whose predictions ride along the cell's other
factors can be tested for the qualitative pattern the original paper
reports.

## Anchoring on a methodological lineage

Two papers ground the contract:

- @cite{berko-1958} introduced the test as a probe for productive
  morpho-phonological knowledge: presented with the nonce *wug*,
  children produce *wugs* /wʌgz/ rather than refusing or randomising.
  The factor that matters is `Attestation`.
- @cite{albright-hayes-2003} is the modern reference for *gradient*
  wug responses: subjects rate alternative output forms, and the
  ratings track how well the input is supported by lexical
  generalisations of varying scope. This is what makes wug responses
  diagnostic for theories of how productivity is encoded
  (rule-and-analogy, MaxEnt grammars, exemplar models, lexical
  conservatism).

The contract here is deliberately minimal — a `HasAttestation` lens
plus a real-valued `Rate` observable. Studies that need additional
factors (frequency, neighbourhood density, paradigm structure) compose
with their own typeclasses on the same `Cell` type.

## Anti-UseListed discriminator

A wug paradigm is the canonical discriminator between theories that
locate productivity in the *grammar* (where novel forms inherit
lexical-frequency effects via constraints / weights) and theories that
locate productivity in *lexical listing* (where novel forms cannot
inherit anything because they are by definition unlisted). The
predicate `NovelInvariantInFrequency` is the UseListed
@cite{zuraw-2000} prediction; `NovelShowsFreqGradient` is the
prediction of indexed-constraint @cite{pater-2010} or scaled-weight
@cite{coetzee-pater-2008} accounts. The theorem
`novelGradient_inconsistent_with_invariance` proves the two are
mutually incompatible on non-vacuous cells, so a study that adopts a
typed `Cell` can pose the discrimination as a single bridge theorem.

## Out of scope (per `CLAUDE.md` Processing scope)

- The specific *form* of the rating scale (Likert, forced choice,
  reaction time) — measurement modality, not paradigm contract.
- Item-construction methodology (phonotactic legality, frequency
  matching, neighbourhood control) — study design choice.
- Statistical analysis pipelines (mixed-effects, ordinal regression) —
  analysis decisions, not paradigm contract.
- Per-paper item lists — these belong in the relevant `Studies/` file.
-/

namespace Paradigms.WugTest

-- ============================================================================
-- §1. Attestation factor
-- ============================================================================

/-- Whether a stimulus is an *attested* lexical item or a *novel*
    (nonce, wug-like) form. The basic categorical contrast that
    @cite{berko-1958} introduced and that every wug paradigm crosses. -/
inductive Attestation where
  | attested
  | novel
  deriving DecidableEq, Repr, Inhabited, Fintype

-- ============================================================================
-- §2. Cell typeclasses
-- ============================================================================

/-! Studies' `Cell` types vary in what additional factors they cross
(item, paradigm slot, frequency stratum, …). The shared minimum is
that every wug cell carries an `Attestation` factor AND a way to swap
that factor while holding the rest of the cell constant. The lens
laws (`get_set`, `set_get`, `set_set`) make `setAttestation` a proper
lens; the paradigm-level predicates rely on them to express
"swapping attested for novel changes the rate" as a statement that
quantifies over the rest of the cell uniformly. -/

/-- `Cell` has an attestation factor that can be swapped without
    touching other factors. -/
class HasAttestation (Cell : Type) where
  attestationOf : Cell → Attestation
  setAttestation : Attestation → Cell → Cell
  attestationOf_setAttestation :
      ∀ a c, attestationOf (setAttestation a c) = a
  setAttestation_attestationOf :
      ∀ c, setAttestation (attestationOf c) c = c
  setAttestation_setAttestation :
      ∀ a₁ a₂ c, setAttestation a₁ (setAttestation a₂ c) =
                 setAttestation a₁ c

/-- `Cell` exposes a real-valued frequency factor (e.g. log token
    frequency of the source lexeme; log corpus frequency of an
    analogous attested compound). The lens lets the predicates in §4
    isolate the frequency contribution from other factors.

    Frequency is `ℝ`-valued because lexical-frequency theories
    (@cite{coetzee-pater-2008}, @cite{coetzee-kawahara-2013}) operate
    on log frequencies as a continuous regressor. Studies whose
    frequency space is discrete should still express it as a real and
    let the lens enforce the structural constraint. -/
class HasFrequency (Cell : Type) where
  frequencyOf : Cell → ℝ
  setFrequency : ℝ → Cell → Cell
  frequencyOf_setFrequency :
      ∀ f c, frequencyOf (setFrequency f c) = f
  setFrequency_frequencyOf :
      ∀ c, setFrequency (frequencyOf c) c = c
  setFrequency_setFrequency :
      ∀ f₁ f₂ c, setFrequency f₁ (setFrequency f₂ c) =
                 setFrequency f₁ c

-- ============================================================================
-- §3. Observable
-- ============================================================================

/-- Per-cell numeric outcome — the wug paradigm's primary observable.
    Polymorphic over the codomain `R` so that empirical tables (`ℚ`
    proportions) and theory predictions (`ℝ` log-odds, MaxEnt
    probabilities) can both ride along the same predicate machinery. -/
abbrev Rate (Cell : Type) (R : Type) := Cell → R

-- ============================================================================
-- §4. Paradigm-level qualitative predicates
-- ============================================================================

/-! These predicates state empirical patterns at the paradigm level.
They are written in terms of `setAttestation` / `setFrequency` (the
lenses), so any `Cell` type with the relevant typeclass instance can
claim them without re-deriving the universal quantification per
study. The predicates are *abstract*; they express a shape ("novel
forms show a frequency gradient") that empirical studies and
theoretical models may or may not satisfy. -/

variable {Cell : Type} {R : Type}

/-- A rate observable shows the *novel-form frequency gradient* if,
    holding all other factors constant and fixing `attestation =
    novel`, varying the frequency factor strictly varies the rate.
    This is the prediction of indexed-constraint
    (@cite{pater-2010}), scaled-weight
    (@cite{coetzee-pater-2008}), and representation-strength
    (@cite{moore-cantwell-2021}, @cite{smolensky-goldrick-2016})
    theories: novel forms inherit a frequency-conditioned grammar
    pressure from analogous lexical items and therefore show a
    frequency gradient even though they are themselves unlisted. -/
def NovelShowsFreqGradient
    [HasAttestation Cell] [HasFrequency Cell] [LT R]
    (rate : Rate Cell R) : Prop :=
  ∀ (c : Cell) (f₁ f₂ : ℝ), f₁ < f₂ →
    rate (HasFrequency.setFrequency f₁ (HasAttestation.setAttestation .novel c)) <
    rate (HasFrequency.setFrequency f₂ (HasAttestation.setAttestation .novel c))

/-- A rate observable is *frequency-invariant on novel forms* if,
    holding all other factors constant and fixing `attestation =
    novel`, varying the frequency factor leaves the rate unchanged.
    This is the prediction of UseListed (@cite{zuraw-2000}): novel
    forms have no lexical entry, so no entry-keyed frequency lookup
    can affect their grammar pressure. The two hypotheses thus make
    opposite predictions on the same paradigm cell. -/
def NovelInvariantInFrequency
    [HasAttestation Cell] [HasFrequency Cell]
    (rate : Rate Cell R) : Prop :=
  ∀ (c : Cell) (f₁ f₂ : ℝ),
    rate (HasFrequency.setFrequency f₁ (HasAttestation.setAttestation .novel c)) =
    rate (HasFrequency.setFrequency f₂ (HasAttestation.setAttestation .novel c))

-- ============================================================================
-- §5. Discriminator theorem
-- ============================================================================

/-- The two predictions are *structurally* incompatible: any rate
    observable that satisfies both `NovelShowsFreqGradient` and
    `NovelInvariantInFrequency` must have a vacuous frequency space
    (no two distinct frequencies). On any cell whose typeclasses
    permit two distinct frequencies, the predicates are mutually
    exclusive — exactly the discriminator a wug paradigm is supposed
    to provide.

    This is the structural source of the empirical claim that wug
    paradigms can adjudicate between grammar-locus and listing-locus
    accounts of productivity: the bridge theorem is a single
    application of this lemma to a study's cell type. -/
theorem novelGradient_inconsistent_with_invariance
    [HasAttestation Cell] [HasFrequency Cell] [Preorder R]
    (rate : Rate Cell R)
    (h_grad : NovelShowsFreqGradient rate)
    (h_inv  : NovelInvariantInFrequency rate)
    (c : Cell) (f₁ f₂ : ℝ) (h_lt : f₁ < f₂) : False := by
  have h1 := h_grad c f₁ f₂ h_lt
  have h2 := h_inv c f₁ f₂
  exact absurd h2 (ne_of_lt h1)

end Paradigms.WugTest
