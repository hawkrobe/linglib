import Linglib.Phenomena.Polysemy.Data
import Linglib.Theories.Diachronic.Lexicalization

/-!
# Word Reuse and Combination Support Efficient Communication
@cite{xu-etal-2024}

Xu, A., Kemp, C., Frermann, L., & Xu, Y. (2024). Word reuse and combination
support efficient communication of emerging concepts. *PNAS* 121(46),
e2406971121.

## Empirical Contributions

Using WordNet data from English, French, and Finnish (1900–2000):

1. Both reuse items and compounds sit near the Pareto frontier of
   communicative efficiency (Fig. 2)
2. Attested encodings are more efficient than random and near-synonym
   baselines (Fig. 3)
3. Literal items (hyponymic reuse, endocentric compounds) are more
   efficient than nonliteral counterparts (§Item-Level Variation)
4. Reuse items tend shorter; compounds tend more informative (§Strategy
   Comparison)

## Connection to Polysemy

Word reuse IS polysemy generation: when "mouse" acquires the sense
"computer peripheral", the word becomes polysemous. This study provides
an information-theoretic explanation for WHY productive polysemy exists —
it is communicatively efficient. This bridges `Phenomena.Polysemy.Data`
(synchronic copredication judgments) to a diachronic functional account.
-/

namespace Phenomena.Polysemy

open Diachronic.Lexicalization

-- ============================================================================
-- §1. Example Data (Table 1)
-- ============================================================================

/-- English reuse items from Table 1. -/
def englishReuse : List FormConceptPair :=
  [ { form := "locker",  concept := "storage trunk",     strategy := .reuse, literality := .literal }
  , { form := "printer", concept := "data output device", strategy := .reuse, literality := .literal }
  , { form := "dish",    concept := "parabolic antenna",  strategy := .reuse, literality := .nonliteral } ]

/-- English compounds from Table 1. -/
def englishCompounds : List FormConceptPair :=
  [ { form := "birthday card",  concept := "birthday greeting card", strategy := .combination, literality := .literal }
  , { form := "urban renewal",  concept := "urban redevelopment",    strategy := .combination, literality := .literal }
  , { form := "spreadsheet",    concept := "financial software",     strategy := .combination, literality := .nonliteral } ]

/-- French reuse items. -/
def frenchReuse : List FormConceptPair :=
  [ { form := "antenne",   concept := "radio/TV antenna",   strategy := .reuse, literality := .literal }
  , { form := "publicité", concept := "commercial ad",      strategy := .reuse, literality := .literal }
  , { form := "émuler",    concept := "software emulation", strategy := .reuse, literality := .nonliteral } ]

/-- French compounds. -/
def frenchCompounds : List FormConceptPair :=
  [ { form := "turbine à gaz",   concept := "gas turbine",    strategy := .combination, literality := .literal }
  , { form := "galaxie spirale", concept := "spiral galaxy",  strategy := .combination, literality := .literal }
  , { form := "boîte noire",     concept := "flight recorder", strategy := .combination, literality := .nonliteral } ]

-- ============================================================================
-- §2. Strategy Properties (Verified on Example Data)
-- ============================================================================

/-- Reuse items are shorter on average than compounds.
    @cite{xu-etal-2024} §Strategy Comparison: holds across all three
    languages and all time intervals. -/
theorem english_reuse_shorter :
    (englishReuse.map (·.formLength)).sum / englishReuse.length <
    (englishCompounds.map (·.formLength)).sum / englishCompounds.length := by
  native_decide

/-- Both strategies include literal and nonliteral items. -/
theorem both_literalities :
    (englishReuse.any (·.literality == .literal)) ∧
    (englishReuse.any (·.literality == .nonliteral)) ∧
    (englishCompounds.any (·.literality == .literal)) ∧
    (englishCompounds.any (·.literality == .nonliteral)) := by
  native_decide

-- ============================================================================
-- §3. Reuse as Polysemy Generation
-- ============================================================================

/-- Word reuse creates polysemy: the reused word acquires a new sense
    alongside its existing one. This connects the diachronic process
    of lexicalization to the synchronic phenomenon of polysemy.

    The copredication data in `Phenomena.Polysemy.Data` captures the
    synchronic *consequence* of reuse (multiple aspects coexist);
    this paper explains the diachronic *cause* (efficiency pressure). -/
def reuseIsPolysemyGeneration : List FormConceptPair → List String :=
  List.filterMap fun p =>
    if p.strategy == .reuse
    then some s!"'{p.form}' is polysemous: original sense + '{p.concept}'"
    else none

/-- All reuse items in the English data generate polysemy. -/
theorem all_english_reuse_creates_polysemy :
    (reuseIsPolysemyGeneration englishReuse).length = englishReuse.length := by
  native_decide

end Phenomena.Polysemy
