/-!
# Mirativity
[delancey-1997] [aikhenvald-2004]

Mirativity is the grammatical category that marks whether the propositional
content is **expected** or **surprising** to the speaker. [delancey-1997]
introduced the term and argued — against earlier evidential-subsumption
analyses — that mirativity is typologically *independent* of evidentiality:
the two categories are often conveyed by overlapping morphology (e.g.,
Turkish *-mIş*), but they answer distinct questions ("what is the source of
the evidence?" vs "is the content surprising?").

This module is intentionally separate from `Semantics.Evidential` to reflect
that independence; bundling structures that combine source, authority, and
mirativity (e.g. `Semantics.Epistemicity.EpistemicProfile`) import both.

-/

namespace Features.Mirativity

/-- Mirativity value: whether the propositional content aligns with
    speaker expectations. -/
inductive MirativityValue where
  /-- Content is expected / non-newsworthy. -/
  | expected
  /-- Content is surprising / newsworthy. -/
  | unexpected
  /-- No mirative marking; expectation is unspecified. -/
  | neutral
  deriving DecidableEq, Repr, Inhabited

end Features.Mirativity
