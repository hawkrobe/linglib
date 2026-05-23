import Linglib.Studies.Gotham2017
import Linglib.Diachronic.Lexicalization

/-!
# Word Reuse and Combination Support Efficient Communication
@cite{xu-etal-2024}

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
length and listener confusion. Bridges `Gotham2017`
(synchronic copredication judgments) to a diachronic functional account.
-/

namespace Phenomena.Polysemy

open Diachronic.Lexicalization
open Pragmatics.Communication (AsymmetricCommModel)
open Pragmatics.Efficiency (CostPair weightedCost)

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

    The copredication data in `Gotham2017`
    captures the synchronic *consequence* of reuse (multiple aspects
    coexist); this paper's account explains the diachronic *cause*
    (efficiency pressure).

    **Caveat on the Gotham bridge.** Xu's reuse polysemy and Gotham's
    *logical* polysemy are not the same phenomenon. Gotham's `DotType`
    requires sortally-compatible aspects with a shared individuation
    ground (book = phys × info, both individuating one volume); Xu's
    *mouse* → peripheral generates two unrelated sortal categories
    with no shared ground. The honest bridge: Xu's *literal* reuse
    (hyponymic, e.g. *car* narrowed from *wheeled cart*) is
    Gotham-compatible (shared ground); Xu's *non-literal* reuse
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
