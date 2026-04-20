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

The contract here is deliberately minimal — a single parametric lens
class `HasFactor (Cell) (F)` plus a real-valued `Rate` observable. The
two known dimensions a wug paradigm crosses (`Attestation`,
log-frequency) are exposed as `abbrev`s `HasAttestation`/`HasFrequency`
specialising `HasFactor` at the relevant codomain. Studies that need
additional factors (neighbourhood density, paradigm structure,
binary IOR membership) instantiate `HasFactor` at their own codomain
and reuse the same predicate machinery.

## Anti-UseListed discriminator

A wug paradigm is the canonical discriminator between theories that
locate productivity in the *grammar* (where novel forms inherit
lexical-frequency effects via constraints / weights) and theories that
locate productivity in *lexical listing* (where novel forms cannot
inherit anything because they are by definition unlisted). The
predicate `NovelInvariantInFactor` is the UseListed
@cite{zuraw-2000} prediction; `NovelShowsFactorGradient` is the
prediction of indexed-constraint @cite{pater-2010} or scaled-weight
@cite{coetzee-pater-2008} accounts. The theorem
`novelGradient_inconsistent_with_invariance` proves the two are
mutually incompatible on cells with a non-vacuous factor space, so a
study that adopts a typed `Cell` can pose the discrimination as a
single bridge theorem at any factor type with `[LT]`.

## Bridge to `Theories/Phonology/LexicalFrequency/HasTokenFreq`

`HasTokenFreq` (in `Theories/Phonology/LexicalFrequency/Defs.lean`) is
a *getter-only* class on fragment lexical entries — fragments are
immutable data, so there is no setter. `HasFactor Cell ℝ` is a *lens*
on paradigm cells, which the paradigm-level predicates below need to
quantify over swapping a frequency without touching other factors.

Wug cells that wrap a fragment lexical entry typically store the
manipulable factor as a separate field (e.g. `WugBKKCell.n2LogFreq`)
that **mirrors** the entry's `tokenLogFreq` for attested items and
ranges freely on novel items. This is the right architecture for an
experimental paradigm: the cell-level factor IS the experimentally
manipulated value, not the lexicon-derived one. The connection to
`HasTokenFreq` is by intent (downstream theories test whether the
cell-level factor predicts the rate observable, with the cell-level
factor *originating* in the lexicon channel for attested items), not
by an automatic instance.

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
-- §2. Lens class — the parametric factor schema
-- ============================================================================

/-! Studies' `Cell` types vary in what additional factors they cross
(item, paradigm slot, frequency stratum, IOR membership, …). The
shared minimum is that every wug cell carries some collection of
factors and a way to swap each one without touching others. The lens
laws (`get_set`, `set_get`, `set_set`) make `setFactor` a proper lens;
the paradigm-level predicates rely on them to express "swapping the
factor changes the rate" as a statement that quantifies over the rest
of the cell uniformly.

`HasFactor` takes the codomain `F` as a parameter so that one schema
covers `Attestation` (categorical), `ℝ` (frequency), `Bool` (binary
IOR membership), and any other factor a future study introduces.
Each `Cell` declares one `HasFactor` instance per factor it exposes;
typeclass synthesis routes by the requested `F`. -/

/-- A lens on `Cell` exposing a factor of type `F`. -/
class HasFactor (Cell : Type) (F : Type) where
  factorOf : Cell → F
  setFactor : F → Cell → Cell
  factorOf_setFactor :
      ∀ f c, factorOf (setFactor f c) = f
  setFactor_factorOf :
      ∀ c, setFactor (factorOf c) c = c
  setFactor_setFactor :
      ∀ f₁ f₂ c, setFactor f₁ (setFactor f₂ c) = setFactor f₁ c

/-- `Cell` has an attestation factor that can be swapped without
    touching other factors. The @cite{berko-1958} dimension. -/
abbrev HasAttestation (Cell : Type) := HasFactor Cell Attestation

/-- `Cell` exposes a real-valued frequency factor (e.g. log token
    frequency of the source lexeme; log corpus frequency of an
    analogous attested compound). Frequency is `ℝ`-valued because
    lexical-frequency theories (@cite{coetzee-pater-2008},
    @cite{coetzee-kawahara-2013}) operate on log frequencies as a
    continuous regressor. -/
abbrev HasFrequency (Cell : Type) := HasFactor Cell ℝ

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
They are written in terms of `setFactor` (the lens), so any `Cell`
type with the relevant `HasFactor` instances can claim them without
re-deriving the universal quantification per study. The predicates
are *abstract*; they express a shape ("novel forms show a factor
gradient") that empirical studies and theoretical models may or may
not satisfy. -/

variable {Cell : Type} {F : Type} {R : Type}

/-- A rate observable shows the *novel-form factor gradient* if,
    holding all other factors constant and fixing `attestation =
    novel`, varying the `F`-typed factor strictly varies the rate.
    This is the prediction of indexed-constraint
    (@cite{pater-2010}), scaled-weight
    (@cite{coetzee-pater-2008}), and representation-strength
    (@cite{moore-cantwell-2021}, @cite{smolensky-goldrick-2016})
    theories: novel forms inherit a frequency-conditioned grammar
    pressure from analogous lexical items and therefore show a
    factor gradient even though they are themselves unlisted. -/
def NovelShowsFactorGradient
    [HasAttestation Cell] [HasFactor Cell F] [LT F] [LT R]
    (rate : Rate Cell R) : Prop :=
  ∀ (c : Cell) (f₁ f₂ : F), f₁ < f₂ →
    rate (HasFactor.setFactor f₁ (HasFactor.setFactor Attestation.novel c)) <
    rate (HasFactor.setFactor f₂ (HasFactor.setFactor Attestation.novel c))

/-- A rate observable is *factor-invariant on novel forms* if, holding
    all other factors constant and fixing `attestation = novel`,
    varying the `F`-typed factor leaves the rate unchanged. This is
    the prediction of UseListed (@cite{zuraw-2000}): novel forms have
    no lexical entry, so no entry-keyed factor lookup can affect their
    grammar pressure. The two hypotheses thus make opposite predictions
    on the same paradigm cell. -/
def NovelInvariantInFactor
    [HasAttestation Cell] [HasFactor Cell F]
    (rate : Rate Cell R) : Prop :=
  ∀ (c : Cell) (f₁ f₂ : F),
    rate (HasFactor.setFactor f₁ (HasFactor.setFactor Attestation.novel c)) =
    rate (HasFactor.setFactor f₂ (HasFactor.setFactor Attestation.novel c))

/-- Frequency-specific spelling of `NovelShowsFactorGradient` at
    `F := ℝ`. Kept as an `abbrev` for readability at use sites where
    "frequency gradient" is the linguist-facing terminology. -/
abbrev NovelShowsFreqGradient
    [HasAttestation Cell] [HasFrequency Cell] [LT R]
    (rate : Rate Cell R) : Prop :=
  NovelShowsFactorGradient (F := ℝ) rate

/-- Frequency-specific spelling of `NovelInvariantInFactor` at
    `F := ℝ`. -/
abbrev NovelInvariantInFrequency
    [HasAttestation Cell] [HasFrequency Cell]
    (rate : Rate Cell R) : Prop :=
  NovelInvariantInFactor (F := ℝ) rate

-- ============================================================================
-- §5. Discriminator theorem
-- ============================================================================

/-- The two predictions are *structurally* incompatible: any rate
    observable that satisfies both `NovelShowsFactorGradient` and
    `NovelInvariantInFactor` at the same factor type `F` must have a
    vacuous factor space (no two `F`-distinct values). On any cell
    whose typeclasses permit `f₁ < f₂` for some `F`-typed factors,
    the predicates are mutually exclusive — exactly the discriminator
    a wug paradigm is supposed to provide.

    For binary factors (`F := Bool`), the precondition `f₁ < f₂` is
    discharged automatically by `Bool.false_lt_true`; for real-valued
    factors (`F := ℝ`) any concrete pair like `(0 : ℝ) < 1` works.

    This is the structural source of the empirical claim that wug
    paradigms can adjudicate between grammar-locus and listing-locus
    accounts of productivity: the bridge theorem is a single
    application of this lemma to a study's cell type. -/
theorem novelGradient_inconsistent_with_invariance
    [HasAttestation Cell] [HasFactor Cell F] [LT F] [Preorder R]
    (rate : Rate Cell R)
    (h_grad : NovelShowsFactorGradient (F := F) rate)
    (h_inv  : NovelInvariantInFactor (F := F) rate)
    (c : Cell) (f₁ f₂ : F) (h_lt : f₁ < f₂) : False := by
  exact absurd (h_inv c f₁ f₂) (ne_of_lt (h_grad c f₁ f₂ h_lt))

end Paradigms.WugTest
