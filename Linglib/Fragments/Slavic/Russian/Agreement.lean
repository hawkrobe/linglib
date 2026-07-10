import Linglib.Syntax.Agreement.Covariance

/-!
# Russian Agreement Covariance
[wade-2020] [corbett-1998]

Per-target covariance facts for Russian ([wade-2020]; [corbett-1998]'s
running examples): attributive and long-form predicative adjectives covary
in number, gender, and case; relative *kotoryj* covaries in number and
gender, with case assigned clause-internally; personal pronouns covary with
their antecedent in number and gender; finite verbs covary in person/number
(nonpast) and gender/number (past), unioned here per the
`CovarianceProfile` convention.
-/

namespace Russian.Agreement

open _root_.Agreement

/-- Dimensions covarying on each target category ([wade-2020]). -/
def covariance : CovarianceProfile
  | .attributive     => {.number, .gender, .case}
  | .predicate       => {.number, .gender, .case}
  | .relativePronoun => {.number, .gender}
  | .personalPronoun => {.number, .gender}
  | .verb            => {.person, .number, .gender}

end Russian.Agreement
