import Linglib.Theories.Pragmatics.Efficiency
import Linglib.Theories.Pragmatics.AsymmetricCommunication

/-!
# Lexicalization: Efficient Encoding of Emerging Concepts
@cite{xu-etal-2024}

Substrate for the information-theoretic account of lexicalization in
@cite{xu-etal-2024}: novel concepts enter the lexicon either by *reuse*
(an existing word picks up a new sense — *mouse* → computer peripheral)
or by *compounding* (concatenation of existing words — *spreadsheet*).
Both strategies are shaped by the same tradeoff between speaker effort
(word length) and information loss (listener confusion).

## Diachronic framing

This is a model of **innovation spread under variation**, not a synchronic
optimization of a static lexicon. @cite{xu-etal-2024} §1–§2 ground in the
variation-theory tradition (@cite{weinreich-labov-herzog-1968},
@cite{milroy-milroy-1985}, @cite{labov-2011}): there is a spread interval
`[t₁, t₂]` during which only some members of the speech community have
acquired the new encoding `E*`. The speaker's production policy is
conditioned on the expanded lexicon `L'` (= `L ∪ E*`); the listener's
interpretation is conditioned on the existing lexicon `L`. This
asymmetry is the diachronic content — it lives at the type level via
`Pragmatics.Communication.AsymmetricCommModel` (its `produce` and
`comprehend` are independent functions that may disagree).

Cline-following diachronic processes (grammaticalization,
subjectification) and constructionalization are out of scope here; see
sibling files in `Theories/Diachronic/`. The contrast is
*type of diachronic process* (cline-following vs. punctuated lexical
innovation), not diachronic vs. synchronic.
-/

namespace Diachronic.Lexicalization

open Pragmatics.Efficiency Pragmatics.Communication

/-! ## Lexicalization strategies -/

/-- Strategy by which a novel concept enters the lexicon
    (@cite{xu-etal-2024} Table 1: reuse items R vs. compounds C).

    The paper notes that borrowing (e.g., *tofu*) and coinage (e.g.,
    *quark*) are additional lexicalization strategies excluded from
    its scope; this enum mirrors that scope restriction. -/
inductive Strategy where
  /-- Reuse an existing word for a new meaning.
      E.g., *mouse* (rodent → peripheral), *dish* (plate → antenna). -/
  | reuse
  /-- Concatenate existing words into a compound.
      E.g., *birthday card*, *spreadsheet*, *urban renewal*. -/
  | compound
  deriving DecidableEq, Repr

/-- Literality of the form–meaning relationship. Literal items tend to
    be more communicatively efficient (@cite{xu-etal-2024} §3.2).

    This binary distinction is a coarsening of the continuous taxonomic-
    distance measures the paper *also* tests (Wu-Palmer 1994;
    Leacock-Chodorow-Miller 1998), reported in paper §3.2 final
    paragraph + SI §S5.E as monotonically correlated with efficiency
    loss. The enum captures the headline literal/non-literal contrast;
    a continuous version would parameterize over a distance metric. -/
inductive Literality where
  /-- Form directly relates to the intended concept.
      - Reuse: intended sense is a hyponym of an existing sense.
      - Compound: endocentric (head = superordinate of intended concept). -/
  | literal
  /-- Metaphorical or metonymic relationship.
      - Reuse: e.g., *mouse* for computer peripheral.
      - Compound: exocentric, e.g., *boîte noire* = flight recorder. -/
  | nonliteral
  deriving DecidableEq, Repr

/-- A form–concept pair in an emerging encoding (one entry in `E*`).

    The `concept` field is a human-readable label. In @cite{xu-etal-2024}
    actual use, concepts are WordNet sense IDs embedded via Sentence-BERT
    (paper §5.3); two distinct senses can share a surface label, so
    serious instantiation needs disambiguating IDs. The string here is
    a presentation-layer convenience for example data. -/
structure FormConceptPair where
  form : String
  concept : String
  strategy : Strategy
  literality : Literality
  deriving Repr

/-- Orthographic form length, used as the speaker-effort proxy in
    @cite{xu-etal-2024} (paper eq. 2). -/
def FormConceptPair.formLength (p : FormConceptPair) : ℕ := p.form.length

/-! ## Communicative costs -/

/-- Per-pair surprisal cap used when `model.comprehend` returns a
    non-positive value. The paper's softmax model never produces zero
    listener probability, so this bound is for numeric robustness only.
    Default is 20 nats ≈ 28.8 bits, comfortably above attested typical
    information loss of ~10–15 bits (@cite{xu-etal-2024} Fig. 2 axes;
    paper uses log₂, this file uses natural log). -/
def surprisalCap : ℝ := 20

/-- Communicative costs of an encoding under an asymmetric communication
    model. Cost₂ uses `model.comprehend` (the listener-side channel
    conditioned on the existing lexicon `L`), reflecting the diachronic
    asymmetry @cite{xu-etal-2024} introduces. The speaker-side `produce`
    channel is not consumed in the deterministic-policy case (see below)
    but lives in the same `model` so future non-deterministic versions
    can read it.

    `cost₁` (paper eq. 2): expected word length under `needProb`.
    `cost₂` (paper eq. 3): expected surprisal under the listener
    distribution. The unweighted sum `cost₂ + β · cost₁` recovers
    `L_β` (paper eq. 4); the per-pair, proportional rearrangement is
    paper eq. 5. We use natural log throughout, so `cost₂` is in nats;
    multiply by `1 / Real.log 2` for the paper's bits convention.

    **Deterministic-policy assumption.** The signature takes
    `needProb : String → ℝ` (a concept-only marginal) rather than a
    joint `p(c, w | L')`. This silently assumes a deterministic
    production policy — one form per concept in `pairs`. Paper §5.2
    estimates `p(c, w | L') = p(w | L') · p(c | w, L')` separately for
    each language; under the assumption that each emerging form-sense
    pair appears with multiplicity 1 in `E*`, the joint reduces to
    `needProb p.concept` and these costs are exact. With non-deterministic
    encodings (multiple forms competing for one concept), use the joint
    instead and marginalize. -/
noncomputable def encodingCosts
    (pairs : List FormConceptPair)
    (needProb : String → ℝ)
    (model : AsymmetricCommModel String String) : CostPair where
  cost₁ := (pairs.map fun p => needProb p.concept * (p.formLength : ℝ)).sum
  cost₂ := (pairs.map fun p =>
    let score := model.comprehend p.concept p.form
    needProb p.concept * if score ≤ 0 then surprisalCap else -Real.log score).sum

/-- Combined cost (paper eq. 4): `L_β = info_loss + β · effort`.
    The named hook the Studies layer invokes to ask for a particular
    β-scalarization of an encoding's `CostPair`. Parameterizes the
    Pareto frontier in `Pragmatics.Efficiency`. -/
noncomputable def unifiedObjective
    (pairs : List FormConceptPair)
    (needProb : String → ℝ)
    (model : AsymmetricCommModel String String)
    (β : ℝ) : ℝ :=
  weightedCost (encodingCosts pairs needProb model) β

end Diachronic.Lexicalization
