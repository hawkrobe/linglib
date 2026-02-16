/-
# Hawkins et al. (2025): PRIOR-PQ

"Relevant answers to polar questions"
Phil. Trans. R. Soc. B 380: 20230505.

## PRIOR-PQ: Pragmatic Reasoning In Overinformative Responses to Polar Questions

This model explains why respondents sometimes provide more information than
strictly necessary when answering yes/no questions.

Example: "Do you have iced tea?" → "No, but we have iced coffee."

## Innovation

The question choice itself signals information about the questioner's goals.
The respondent uses Theory of Mind to infer the likely decision problem
and tailor their response accordingly.

## Grounding in Van Rooy (2003)

Van Rooy's decision-theoretic semantics assumes the respondent *knows* the
questioner's decision problem. PRIOR-PQ extends this by having the respondent
*infer* the decision problem via Theory of Mind from the question choice itself.

```
Van Rooy (2003):  Decision Problem → Question Meaning → Answer Selection
                        ↓ known
                   Respondent

Hawkins et al. (2025):  Decision Problem ← Inferred from Question
                             ↑ ToM          ↓
                        Respondent → Answer Selection
```
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Basic
import Linglib.Core.DecisionTheory

namespace RSA.PriorPQ

/-!
This file previously contained the full Hawkins et al. (2025) PRIOR-PQ RSA implementation.
All definitions and theorems depend on Phenomena types (ResponseType, cs1/cs2/cs3 data,
etc.) and have been moved to
`Linglib.Phenomena.Questions.Bridge_RSA_HawkinsEtAl2025`.
-/

end RSA.PriorPQ
