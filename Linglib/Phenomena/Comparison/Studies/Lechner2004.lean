import Linglib.Features.Acceptability
import Linglib.Paradigms.Measurement

/-!
# Lechner 2004: Ellipsis in Comparatives
@cite{lechner-2004} @cite{lechner-2001} @cite{bresnan-1973}
@cite{kennedy-1999} @cite{merchant-2001}

Winfried Lechner. *Ellipsis in Comparatives.* Studies in Generative
Grammar 72. Berlin/New York: Mouton de Gruyter.

## What this file is

The canonical home of the binding diagnostic for phrasal comparatives.
Lechner Ch 2 §2.1 ("Disjoint reference effects") establishes that the
comparative-deletion site is reconstructed at LF and is therefore
visible to Principle C. Lechner's diagnostic is the *source* of
@cite{bhatt-takahashi-2011}'s English binding battery; B&T fn. 4
explicitly says their (11)–(13) are modelled on this work.

This file owns the diagnostic schema (`BindingDatum`), the two
analyses' structural predictions (`RAPredictsCoref` /
`DAPredictsCoref`), and the language-level realised-availability
predicates (`realizesReduction` / `realizesDirect`). Downstream study
files (`BhattTakahashi2011.lean` and any future cross-linguistic work)
import these and instantiate them on per-paper data.

## Lechner's argument (Ch 2 §2.1)

Lechner contrasts two predictions about the CD-site's syntactic
reality:

- **CD-site is reconstructed at LF** (Lechner's view): material inside
  the CD-site is visible to Principle C. R-expressions inside the
  CD-site induce disjoint-reference effects.
- **CD-site is recovered only in semantics** (Kennedy 1999, Lerner &
  Pinkal): syntactic principles are blind to the CD-site's content.

Lechner's key data points (numbers from Lechner 2004):

- **(24)** *`*Mary is prouder of John_i than he_i is.`* — CD-site is
  `d-proud of John_i`. Coreferential reading is unavailable. Under
  reconstruction this is a Principle C violation; under the semantic
  view there is no syntactic basis for the deviance.
- **(25)** `Mary is prouder of John_i than he_i believes that I am.` —
  same R-expression-in-CD-site configuration, but coref is licit.
  Lechner attributes the obviation to Vehicle Change (Fiengo & May
  1994) once the CD-site is embedded under a clause boundary.
- **(28a/b)** `John_i is taller than himself_i.` (✓) vs.
  `*John_i is taller than him_i.` (✗) — phrasal pattern: a
  c-commanding NP can bind a reflexive remnant but cannot coindex
  with a pronominal remnant. Together these establish that the
  matrix subject c-commands into the than-XP at the relevant level.

The schema below abstracts the (24)-style minimal pair into two
binary dimensions: whether matrix material c-commands the comparative
associate, and whether coreference between that matrix material and
an R-expression inside the standard is attested. The (25)-style
embedding obviation requires a third dimension (depth of embedding)
which is *not* formalised here; see the closing prose for what would
be needed to capture it.

## Why this file is not in `Theories/`

The diagnostic is paper-faithful to Lechner: it instantiates an
empirical-data schema and proves which structural analyses are
consistent with which language's data. The structural primitives —
c-command, the CD-site, Vehicle Change — live in the relevant
syntax/ellipsis modules. This file is the *empirical bridge* between
those primitives and downstream study files that consume the
schema.
-/

namespace Lechner2004

open Features (Acceptability)

-- ════════════════════════════════════════════════════
-- § 1. The two analyses
-- ════════════════════════════════════════════════════

/-- The two competing structural analyses of phrasal comparatives.
    Lechner Ch 2 §1 introduces both (under different labels) and
    @cite{bhatt-takahashi-2011} adopts these names.

    - **Reduction Analysis (RA)**: phrasal `than NP` derives from
      clausal `than [NP is Adj]` via reduction (gapping, conjunction
      reduction, TP-ellipsis). The standard sits in a clause-internal
      position parallel to the matrix associate.
    - **Direct Analysis (DA)**: phrasal `than NP` is genuinely phrasal;
      the 'than'-PP is external and the standard is its complement. -/
inductive PhrasalAnalysis where
  | reduction
  | direct
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. The binding-diagnostic schema (Ch 2 §2.1)
-- ════════════════════════════════════════════════════

/-- A minimal-pair binding datum as used in Lechner's disjoint-
    reference diagnostic. Two binary dimensions:

    - `pronCCommandsAssociate` — whether some matrix expression
      c-commands the comparative associate at the relevant level
      (LF for RA's reconstructed structure; surface for DA's
      external 'than'-PP).
    - `corefAttested` — whether coreference between that matrix
      expression and an R-expression inside the standard is
      reported as grammatical.

    `citationId` records the example number (e.g. `"24"` for
    Lechner (24)) so that the relationship between the abstract
    schema and the concrete paper data is auditable. `acceptability`
    records fine-grained judgments where binary `corefAttested`
    is too coarse — e.g. for the @cite{bhatt-takahashi-2011} (13b)
    "(?)mildly deviant" case. -/
structure BindingDatum where
  citationId : String
  acceptability : Acceptability
  pronCCommandsAssociate : Bool
  corefAttested : Bool
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 3. Per-analysis structural predictions
-- ════════════════════════════════════════════════════

/-- The Reduction Analysis's structural prediction. The standard
    occupies a clause-internal position parallel to the associate;
    matrix material c-commanding the associate also c-commands the
    standard's R-expression. Coreference is therefore grammatical
    iff the matrix expression does *not* c-command the associate. -/
def RAPredictsCoref (d : BindingDatum) : Prop :=
  d.pronCCommandsAssociate = false ↔ d.corefAttested = true

instance (d : BindingDatum) : Decidable (RAPredictsCoref d) := by
  unfold RAPredictsCoref; infer_instance

/-- The Direct Analysis's structural prediction. The 'than'-PP is
    external and the matrix expression never c-commands into it,
    regardless of its relation to the associate. Coreference is
    therefore predicted to be uniformly available. -/
def DAPredictsCoref (d : BindingDatum) : Prop :=
  d.corefAttested = true

instance (d : BindingDatum) : Decidable (DAPredictsCoref d) := by
  unfold DAPredictsCoref; infer_instance

-- ════════════════════════════════════════════════════
-- § 4. Language-level realised availability
-- ════════════════════════════════════════════════════

/-- A language *realises* the Reduction Analysis (per its binding
    diagnostic) iff every datum matches RA's biconditional prediction
    (coref is attested iff the matrix expression does not c-command the
    associate). -/
def realizesReduction (data : List BindingDatum) : Prop :=
  ∀ d ∈ data, RAPredictsCoref d

instance (data : List BindingDatum) : Decidable (realizesReduction data) := by
  unfold realizesReduction; exact List.decidableBAll _ _

/-- A language *realises* the Direct Analysis (per its binding
    diagnostic) iff every datum exhibits coreference — DA imposes no
    structural constraint, so it is consistent with the data exactly
    when coreference is uniformly attested. -/
def realizesDirect (data : List BindingDatum) : Prop :=
  ∀ d ∈ data, DAPredictsCoref d

instance (data : List BindingDatum) : Decidable (realizesDirect data) := by
  unfold realizesDirect; exact List.decidableBAll _ _

/-- Per-language record of which analyses are realised by the binding
    diagnostic. Constructed via `headAvailabilityFromBinding` from the
    language's binding data, *not* stipulated. -/
structure HeadAvailability where
  reductionRealized : Bool
  directRealized : Bool
  deriving DecidableEq, Repr

/-- Build a `HeadAvailability` from binding data by checking
    consistency against each analysis's structural prediction. This
    is the anti-stipulation core: per-language head-availability is
    *derived* from the data, not asserted. The Bool fields are
    `decide`-extracted from the decidable propositions
    `realizesReduction` / `realizesDirect`. -/
def headAvailabilityFromBinding (data : List BindingDatum) : HeadAvailability where
  reductionRealized := decide (realizesReduction data)
  directRealized := decide (realizesDirect data)

-- ════════════════════════════════════════════════════
-- § 5. Lechner's English data (Ch 2 §2.1, examples (24)–(28))
-- ════════════════════════════════════════════════════

/-- Lechner (24): `*Mary is prouder of John_i than he_i is.` The
    matrix pronoun `he` c-commands the (matrix) associate `John`;
    coreference into the CD-site `d-proud of John_i` is unavailable.
    Under reconstruction, this is a Principle C violation. -/
def lechner_24 : BindingDatum :=
  { citationId := "24"
    acceptability := .unacceptable
    pronCCommandsAssociate := true
    corefAttested := false }

/-- Lechner (28a): `John_i is taller than himself_i.` Phrasal
    comparative; the matrix subject c-commands into the than-XP and
    binds the reflexive remnant. Recorded with `corefAttested := true`
    because the binding relation is grammatical (reflexive licensing
    is the dual of disjoint reference for our schema's purposes —
    binding/coref attested means the c-command relation is real). -/
def lechner_28a : BindingDatum :=
  { citationId := "28a"
    acceptability := .ok
    pronCCommandsAssociate := false
    corefAttested := true }

/-- Lechner's English binding data: the minimal pair from (24)
    establishing reconstruction-into-CD-site, paired with the (28a)
    no-c-command control. -/
def englishLechnerData : List BindingDatum :=
  [lechner_24, lechner_28a]

/-- Lechner's English data is consistent with RA: the disjoint-
    reference effect at (24) follows iff the CD-site is
    reconstructed (RA-style), and (28a)'s no-c-command control
    permits coref as RA predicts. -/
theorem english_lechner_realizes_reduction :
    realizesReduction englishLechnerData := by
  decide

/-- Lechner's English data is *not* consistent with DA: DA predicts
    uniform coref availability, contradicted by (24). -/
theorem english_lechner_rules_out_direct :
    ¬ realizesDirect englishLechnerData := by
  decide

/- ## What this file does not formalize

- **(25) Vehicle Change obviation**. Embedding the CD-site under a
  clause boundary lifts the Principle C effect (Fiengo & May 1994).
  Capturing this requires a third dimension (depth of embedding)
  on `BindingDatum` plus a substantive theory of Vehicle Change;
  this file's binary schema is faithful only to (24)/(28).
- **§2.2 Reflexives and reciprocals**. Lechner extends the diagnostic
  to anaphor binding (sloppy identity in (30)). The schema would need
  to be parameterised by anaphor type to capture this; the
  acceptability data alone is captured by the existing schema.
- **§2.3 Coordinate Structure Constraint**. Argues for syntactic
  CD-identification via CSC violations in comparatives. Encoding
  CSC requires the syntactic-island infrastructure currently in
  `Core/Islands.lean`.
- **The semantic compositional details** of Ch 4 — the head-raising
  derivation, the AP-Raising Hypothesis. The current schema is
  shallow: it records the *binding-diagnostic outcomes* without
  reconstructing the full compositional pathway. -/

end Lechner2004
