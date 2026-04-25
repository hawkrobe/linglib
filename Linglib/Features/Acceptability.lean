/-!
# Features.Acceptability — Linguistic Acceptability Diacritics

Standard acceptability diacritics used in linguistic papers, encoded as
a six-way taxonomy. These correspond to the conventional marks placed
before example sentences:

- (unmarked) = fully acceptable
- `?`        = degraded/marginal
- `??`       = quite degraded
- `*`        = clearly unacceptable
- `#`        = semantically/pragmatically anomalous (syntactically well-formed)
- `%`        = dialectally variable / speaker-dependent

The semantic-vs-syntactic split (`#` vs `*`) and dialect marker (`%`) are
linguistically substantive distinctions, not just gradient acceptability;
this is why the type is a labeled enum rather than a Likert-style ordinal.
For experimental Likert ratings, see paradigm-specific contracts under
`Paradigms/` (e.g., `AcceptabilityJudgment.lean`'s `DDResult`).
-/

namespace Features

/-- Standard acceptability diacritics used in linguistic papers. -/
inductive Acceptability where
  /-- (unmarked) fully acceptable -/
  | ok
  /-- `?` degraded but not out -/
  | marginal
  /-- `??` quite degraded -/
  | degraded
  /-- `*` clearly unacceptable -/
  | unacceptable
  /-- `#` semantically/pragmatically odd -/
  | anomalous
  /-- `%` dialectally variable -/
  | variable
  deriving Repr, DecidableEq

end Features
