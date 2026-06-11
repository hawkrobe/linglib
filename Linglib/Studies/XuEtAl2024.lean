import Linglib.Pragmatics.Efficiency
import Linglib.Pragmatics.AsymmetricCommunication

/-!
# Word Reuse and Combination Support Efficient Communication
[xu-etal-2024]

Xu, A., Kemp, C., Frermann, L., & Xu, Y. (2024). Word reuse and combination
support efficient communication of emerging concepts. *PNAS* 121(46),
e2406971121.

## Empirical contributions

Using WordNet data from English, French, and Finnish (1900–2000):

1. Both reuse items and compounds sit near the Pareto frontier of
   communicative efficiency (Fig. 2).
2. Attested encodings are more efficient than random and near-synonym
   baselines (Fig. 3).
3. Literal items (hyponymic reuse, endocentric compounds) tend to be
   more efficient than nonliteral counterparts (paper §3.2; significant
   for French and Finnish reuse, with English reuse supplemented by
   compound head words because WordNet does not directly classify
   English-reuse literality).
4. Reuse items tend shorter than compounds across all three languages;
   compounds tend more informative than reuse items in English and
   French only (paper §3.3 — Finnish does not show the informativeness
   asymmetry).

## Connection to polysemy

Word reuse is a polysemy-generating process: when *mouse* acquires the
sense "computer peripheral", the word becomes polysemous. This study
provides an information-theoretic account of why productive polysemy
exists — it is communicatively efficient under a tradeoff between
length and listener confusion. Bridges synchronic copredication judgments
([asher-2011], [gotham-2017]) to a diachronic functional account.
-/

namespace Phenomena.Polysemy

open Pragmatics.Communication (AsymmetricCommModel)
open Pragmatics.Efficiency (CostPair weightedCost)

/-! ## §0. Lexicalization substrate

The information-theoretic model of lexicalization: novel concepts enter
the lexicon either by *reuse* (an existing word picks up a new sense —
*mouse* → computer peripheral) or by *compounding* (concatenation of
existing words — *spreadsheet*). Both strategies are shaped by the same
tradeoff between speaker effort (word length) and information loss
(listener confusion).

This is a model of **innovation spread under variation**, not a
synchronic optimization of a static lexicon. [xu-etal-2024] §1–§2 ground
in the variation-theory tradition ([weinreich-labov-herzog-1968],
[milroy-milroy-1985], [labov-2011]): there is a spread interval
`[t₁, t₂]` during which only some members of the speech community have
acquired the new encoding `E*`. The speaker's production policy is
conditioned on the expanded lexicon `L'` (= `L ∪ E*`); the listener's
interpretation is conditioned on the existing lexicon `L`. This
asymmetry is the diachronic content — it lives at the type level via
`Pragmatics.Communication.AsymmetricCommModel` (its `produce` and
`comprehend` are independent functions that may disagree). -/

/-- Strategy by which a novel concept enters the lexicon
    ([xu-etal-2024] Table 1: reuse items R vs. compounds C).

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
    be more communicatively efficient ([xu-etal-2024] §3.2).

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

    The `concept` field is a human-readable label. In [xu-etal-2024]
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
    [xu-etal-2024] (paper eq. 2). -/
def FormConceptPair.formLength (p : FormConceptPair) : ℕ := p.form.length

/-- Per-pair surprisal cap used when `model.comprehend` returns a
    non-positive value. The paper's softmax model never produces zero
    listener probability, so this bound is for numeric robustness only.
    Default is 20 nats ≈ 28.8 bits, comfortably above attested typical
    information loss of ~10–15 bits ([xu-etal-2024] Fig. 2 axes;
    paper uses log₂, this file uses natural log). -/
def surprisalCap : ℝ := 20

/-- Communicative costs of an encoding under an asymmetric communication
    model. Cost₂ uses `model.comprehend` (the listener-side channel
    conditioned on the existing lexicon `L`), reflecting the diachronic
    asymmetry [xu-etal-2024] introduces. The speaker-side `produce`
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
    The β-scalarization of an encoding's `CostPair`; parameterizes the
    Pareto frontier in `Pragmatics.Efficiency`. -/
noncomputable def unifiedObjective
    (pairs : List FormConceptPair)
    (needProb : String → ℝ)
    (model : AsymmetricCommModel String String)
    (β : ℝ) : ℝ :=
  weightedCost (encodingCosts pairs needProb model) β

/-! ## §1. Example data (Table 1) -/

/-- English reuse items from paper Table 1. -/
def englishReuse : List FormConceptPair :=
  [ { form := "locker",  concept := "storage trunk",      strategy := .reuse, literality := .literal }
  , { form := "printer", concept := "data output device", strategy := .reuse, literality := .literal }
  , { form := "dish",    concept := "parabolic antenna",  strategy := .reuse, literality := .nonliteral } ]

/-- English compounds from paper Table 1. -/
def englishCompounds : List FormConceptPair :=
  [ { form := "birthday card", concept := "birthday greeting card", strategy := .compound, literality := .literal }
  , { form := "urban renewal", concept := "urban redevelopment",    strategy := .compound, literality := .literal }
  , { form := "spreadsheet",   concept := "financial software",     strategy := .compound, literality := .nonliteral } ]

/-- French reuse items. -/
def frenchReuse : List FormConceptPair :=
  [ { form := "antenne",   concept := "radio/TV antenna",   strategy := .reuse, literality := .literal }
  , { form := "publicité", concept := "commercial ad",      strategy := .reuse, literality := .literal }
  , { form := "émuler",    concept := "software emulation", strategy := .reuse, literality := .nonliteral } ]

/-- French compounds. -/
def frenchCompounds : List FormConceptPair :=
  [ { form := "turbine à gaz",   concept := "gas turbine",     strategy := .compound, literality := .literal }
  , { form := "galaxie spirale", concept := "spiral galaxy",   strategy := .compound, literality := .literal }
  , { form := "boîte noire",     concept := "flight recorder", strategy := .compound, literality := .nonliteral } ]

/-! ## §2. Strategy properties (verified on example data)

The full Pareto-efficiency claims (Figs. 2–3) depend on a fitted
sentence-encoder embedding for the listener's prototype distribution
(paper §5.3) and 100,000 random/near-synonym baseline encodings per
language–interval cell (paper §5.5); they are not reduced to
`decide`-checkable form here. The claims that ARE decide-checkable on
the Table-1 examples are about word length — the speaker-effort axis. -/

/-- Reuse items are shorter on average than compounds (paper §3.3:
    holds across all three languages and all time intervals). -/
theorem english_reuse_shorter :
    (englishReuse.map (·.formLength)).sum / englishReuse.length <
    (englishCompounds.map (·.formLength)).sum / englishCompounds.length := by
  decide

/-- French reuse items are also shorter on average than French compounds. -/
theorem french_reuse_shorter :
    (frenchReuse.map (·.formLength)).sum / frenchReuse.length <
    (frenchCompounds.map (·.formLength)).sum / frenchCompounds.length := by
  decide

/-- Both strategies include literal and nonliteral items in the
    paper's Table 1 sample. -/
theorem both_literalities :
    (englishReuse.any (·.literality == .literal)) ∧
    (englishReuse.any (·.literality == .nonliteral)) ∧
    (englishCompounds.any (·.literality == .literal)) ∧
    (englishCompounds.any (·.literality == .nonliteral)) := by
  decide

/-! ## §3. Substrate witnesses

Concrete instantiations of `encodingCosts` and `unifiedObjective`
demonstrate the Theory-layer substrate is operationally consumed.
The toy `needProb` and `model` below are not the paper's actual
fitted distributions; they are stipulated only to anchor the
type-checking. Real instantiation requires the WordNet+Sentence-BERT
pipeline of paper §5.3 + §5.4. -/

/-- A toy uniform-need distribution: `1/n` for each concept in a
    list-derived encoding, `0` elsewhere. Constant function for the
    witness; serious use would derive from corpus frequencies. -/
noncomputable def uniformNeed (n : ℕ) : String → ℝ :=
  fun _ => 1 / n

/-- A toy symmetric communication model with constant listener score `1/2`.
    Makes `encodingCosts.cost₂` a determinate value for the witness
    theorems below. -/
noncomputable def stipulatedModel : AsymmetricCommModel String String :=
  AsymmetricCommModel.symmetric (fun _ _ => 1 / 2)

/-- The English-reuse encoding's costs under the toy model. -/
noncomputable def englishReuseCosts : CostPair :=
  encodingCosts englishReuse (uniformNeed englishReuse.length) stipulatedModel

/-- The English-compound encoding's costs under the toy model. -/
noncomputable def englishCompoundsCosts : CostPair :=
  encodingCosts englishCompounds (uniformNeed englishCompounds.length) stipulatedModel

/-- `unifiedObjective` decomposes into `weightedCost (encodingCosts ...) β`.
    This `rfl` theorem witnesses that the named `unifiedObjective` hook
    is the `β`-scalarization of the cost pair the substrate computes —
    no extra arithmetic, no glue. -/
theorem unifiedObjective_eq_weightedCost
    (pairs : List FormConceptPair) (np : String → ℝ)
    (m : AsymmetricCommModel String String) (β : ℝ) :
    unifiedObjective pairs np m β =
    weightedCost (encodingCosts pairs np m) β := rfl

/-! ## §4. Reuse as polysemy generation -/

/-- Word reuse creates polysemy: the reused word acquires a new sense
    alongside its existing one. Connects the diachronic process of
    lexicalization to the synchronic phenomenon of polysemy.

    Copredication ([asher-2011], [gotham-2017]) is the synchronic
    *consequence* of reuse (multiple aspects coexist); this paper's
    account explains the diachronic *cause* (efficiency pressure).

    **Caveat on the copredication bridge.** Xu's reuse polysemy and
    *logical* polysemy are not the same phenomenon. Logical polysemy
    involves sortally-compatible aspects with a shared individuation
    ground (book = phys × info, both individuating one volume); Xu's
    *mouse* → peripheral generates two unrelated sortal categories
    with no shared ground. The honest bridge: Xu's *literal* reuse
    (hyponymic, e.g. *car* narrowed from *wheeled cart*) is compatible
    with logical polysemy (shared ground); Xu's *non-literal* reuse
    (metaphorical, e.g. *mouse*) is not. The `Literality` enum
    in the Theory file is the partition this distinction lives on. -/
def reuseIsPolysemyGeneration : List FormConceptPair → List String :=
  List.filterMap fun p =>
    if p.strategy == .reuse
    then some s!"'{p.form}' is polysemous: original sense + '{p.concept}'"
    else none

/-- All reuse items in the English data generate polysemy. -/
theorem all_english_reuse_creates_polysemy :
    (reuseIsPolysemyGeneration englishReuse).length = englishReuse.length := by
  decide

end Phenomena.Polysemy
