import Linglib.Syntax.Agreement.Profile
import Linglib.Fragments.Slavic.Russian.Agreement

/-!
# Corbett 1998: Morphology and Agreement
[corbett-1998]

The Handbook of Morphology chapter. §1 defines agreement via systematic
covariance and fixes the controller/target/domain/features vocabulary,
including anaphoric pronouns in the wider sense. §2: "There are three
indisputable agreement features, gender, number and person." §2.4 classifies
the remaining covariant dimensions by the asymmetry criterion: case "is
imposed on the noun phrase by government ... This is not agreement, if we
take seriously the question of asymmetry"; definiteness (Arabic) is likewise
"imposed on the noun phrase as a whole". The chapter's claim is thus a
partition of covariance facts, not a denial of them — adjective-noun case
covariance is conceded ("both do indeed stand in the same form").

We encode §2.4's classification (`imposedDims`) and derive §2's three
(`agreementFeatures`), then check the partition against the Russian
agreement profile instantiated by the chapter's examples (1)-(5). The
mechanism question remains open in the current literature; the rival reading
of the same facts is `Studies/AlexeyenkoZeijlstra2025.lean`, which carries
case through the nominal projection alongside φ.
-/

namespace Corbett1998

open Agreement

/-- §2.4's classification: dimensions whose value is imposed on the noun
    phrase from outside (by government, or as phrase-level marking) rather
    than determined by an asymmetric controller — case (5) and definiteness
    (Arabic). -/
def imposedDims : Finset Dimension := {.case, .definiteness}

private def allDims : Finset Dimension :=
  {.person, .number, .gender, .case, .definiteness}

/-- `allDims` enumerates every dimension (guards against enum growth). -/
theorem mem_allDims (d : Dimension) : d ∈ allDims := by cases d <;> decide

/-- The agreement features: covariant dimensions NOT imposed on the NP —
    derived from the §2.4 classification, not stipulated. -/
def agreementFeatures : Finset Dimension := allDims.filter (· ∉ imposedDims)

/-- §2: "There are three indisputable agreement features, gender, number and
    person" — as derived from §2.4's classification. -/
theorem indisputable_three :
    agreementFeatures = {.person, .number, .gender} := by decide

/-- Russian attributive adjectives covary in case ((5) *v nov-om
    avtomobil'-e* 'in a new car'), yet §2.4 classifies case as imposed: the
    covariance fact and the agreement classification come apart exactly
    here. -/
theorem russian_attr_case_covariant_but_imposed :
    .case ∈ Russian.Agreement.profile .attributive ∧
    .case ∈ imposedDims := by decide

/-- What Russian attributive adjectives AGREE in on the chapter's
    classification — the covariance profile restricted to agreement
    features: gender and number ((1)-(4)). -/
theorem russian_attr_agreement :
    Russian.Agreement.profile .attributive ∩ agreementFeatures =
      {.number, .gender} := by decide

/-- §1: pronouns are agreement targets in the wider sense — the Russian
    personal pronoun covaries (in gender and number) with its antecedent. -/
theorem pronoun_target_covaries :
    Russian.Agreement.profile .personalPronoun ≠ ∅ := by decide

end Corbett1998
