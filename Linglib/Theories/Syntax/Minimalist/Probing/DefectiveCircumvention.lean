import Linglib.Theories.Syntax.Minimalist.Probing.DefectiveGoal

/-!
# Defective Circumvention
@cite{storment-2025} @cite{storment-2026} @cite{roberts-2010}

Storment's *defective circumvention* probing operation
(@cite{storment-2025}, ch. 2; cited as eq. 59 in @cite{storment-2026}):

> A probe P enters into an Agree relation with a higher defective goal α
> and then conditionally goes on to Agree past α with a lower, more
> featurally specified goal β.

Two outcomes per @cite{storment-2026}:

1. **No circumvention** → 3sg "default" agreement (the unvalued probe
   features that α couldn't supply are spelled out as default values).
2. **Successful circumvention** → agreement tracks β when β's features
   are compatible with what was already acquired from α.

Circumvention can fail when β's features conflict with α's
(@cite{storment-2026} §3.1.4): if α gave [Person:3] and β has
[Person:1], the second cycle produces "an irresolvable and
uninterpretable feature conflict on the T⁰ probe."

## Storment's empirical predictions
- **Setswana QI**: re-probe disallowed → defective theme → SM17 default
- **English QI** with 3rd-person plural agent: re-probe allowed,
  features compatible → tracks agent (`advise the dieticians`)
- **English QI** with 1st/2nd person agent: re-probe attempted but
  features clash → falls back to default → ungrammatical with agent
  agreement (`*ask we`)
-/

namespace Minimalist.Probing

open Minimalist

/-- The four outcomes of a probing operation that may or may not invoke
    defective circumvention. -/
inductive ProbingOutcome where
  /-- The higher goal α was not defective; α suffices, no re-probe needed. -/
  | trackHigher
  /-- α was defective; re-probe was disallowed; default features spell out. -/
  | defaultAgreement
  /-- α was defective; re-probe to β succeeded (β features compatible). -/
  | trackLower
  /-- α was defective; re-probe to β attempted but β's features
      conflict with what was acquired from α; derivation crashes. -/
  | featureClash
  deriving DecidableEq, Repr

/-- Defective circumvention probing. Given a probe and two candidate
    goals (α higher, β lower), parameterized by:
    - `allowReprobe` — language- or construction-specific flag governing
      whether the probe may search past a defective goal
    - `compatible` — feature-compatibility predicate on `(α, β)` deciding
      whether circumvention can complete without conflict. -/
def defectiveCircumvention
    (probe alpha beta : FeatureBundle)
    (allowReprobe : Bool)
    (compatible : FeatureBundle → FeatureBundle → Bool) :
    ProbingOutcome :=
  if DefectiveGoal probe alpha then
    if allowReprobe then
      (if compatible alpha beta then .trackLower else .featureClash)
    else .defaultAgreement
  else .trackHigher

/-- When the higher goal is not defective, circumvention is never invoked. -/
theorem defectiveCircumvention_trackHigher_of_nondefective
    (probe alpha beta : FeatureBundle) (allowReprobe : Bool)
    (compatible : FeatureBundle → FeatureBundle → Bool)
    (h : ¬ DefectiveGoal probe alpha) :
    defectiveCircumvention probe alpha beta allowReprobe compatible = .trackHigher := by
  unfold defectiveCircumvention; simp [h]

/-- When the higher goal is defective and re-probe is disallowed,
    the result is default agreement (Storment's Setswana case). -/
theorem defectiveCircumvention_default_when_no_reprobe
    (probe alpha beta : FeatureBundle)
    (compatible : FeatureBundle → FeatureBundle → Bool)
    (hd : DefectiveGoal probe alpha) :
    defectiveCircumvention probe alpha beta false compatible = .defaultAgreement := by
  unfold defectiveCircumvention; simp [hd]

/-- When the higher goal is defective, re-probe is allowed, and β's
    features are compatible: circumvention tracks β (Storment's English
    `advise the dieticians` case). -/
theorem defectiveCircumvention_tracks_lower
    (probe alpha beta : FeatureBundle)
    (compatible : FeatureBundle → FeatureBundle → Bool)
    (hd : DefectiveGoal probe alpha) (hc : compatible alpha beta = true) :
    defectiveCircumvention probe alpha beta true compatible = .trackLower := by
  unfold defectiveCircumvention; simp [hd, hc]

/-- When the higher goal is defective, re-probe is allowed, but β's
    features conflict with α's: derivation crashes (Storment's English
    `*ask we` case). -/
theorem defectiveCircumvention_clash_on_incompatible
    (probe alpha beta : FeatureBundle)
    (compatible : FeatureBundle → FeatureBundle → Bool)
    (hd : DefectiveGoal probe alpha) (hc : compatible alpha beta = false) :
    defectiveCircumvention probe alpha beta true compatible = .featureClash := by
  unfold defectiveCircumvention; simp [hd, hc]

end Minimalist.Probing
