import Linglib.Syntax.Minimalist.Probe.Basic
import Linglib.Syntax.Minimalist.Features
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic

/-!
# Satisfaction conditions: the Deal/Keine probe specification
[deal-2024] [keine-2019]

Standard Agree assumes a probe is satisfied only by finding a matching
valued feature. [deal-2024] argues for richer conditions — a probe can
*interact* (halt) with more than satisfies it:

- **Feature match**: the standard case.
- **Head encounter**: probe halts on encountering a head of a category
  (e.g. Mam's Infl probe stopped by transitive Voice), copying no
  features → Elsewhere/default exponent.
- **Disjunctive**: halt on ANY of several conditions.

A `SatisfactionCond` is a *probe specification* in the sense of
`Probe/Basic.lean`: it denotes a `Probe α` via `SatisfactionCond.toProbe`,
with visibility = halting ([deal-2024] interaction) and activity =
feature copying ([deal-2024] satisfaction). The interaction/satisfaction
split is exactly the `Probe.vis`/`Probe.act` split — this file is where
the substrate makes that identification (the previously study-local
bridge in `Studies/Scott2023.lean`).

## Main declarations

- `SatisfactionCond` — featureMatch / headEncounter / disjunctive.
- `SatisfactionCond.isSatisfied`, `.copiedFeatures` — halting and copying.
- `SatisfactionCond.toProbe` — the canonical specification-to-`Probe`
  map, generic over how a goal exposes its features and host category.
-/

namespace Minimalist

/-- How a probe's search can be terminated.

    Standard Agree assumes a probe is satisfied only by finding a matching
    valued feature (simple feature match). [deal-2024] argues for richer
    conditions to capture e.g. Mam's Infl probe, which is satisfied by
    EITHER matching φ-features OR encountering transitive Voice:

    **Mam example** ([scott-2023], via [deal-2024]):
    - Infl carries [uφ] with satisfaction [SAT: φ or Voice_TR]
    - Intransitive: probe passes through (no Voice_TR) → finds S → real φ-agreement
    - Transitive: probe encounters Voice_TR → satisfied without copying φ → default "∅"

    This turns the Mam bridge's prose account into a computable derivation:
    ```
    def mamInflSatisfaction : SatisfactionCond :=
.disjunctive [.featureMatch (.phi (.person.third)),.headEncounter.v]
    ```
-/
inductive SatisfactionCond where
  /-- Standard: probe is satisfied by finding a matching valued feature. -/
  | featureMatch : FeatureVal → SatisfactionCond
  /-- Disjunctive: probe is satisfied by ANY of these conditions.
      Models [deal-2024]'s interaction-based probes. -/
  | disjunctive : List SatisfactionCond → SatisfactionCond
  /-- Head encounter: probe is satisfied by encountering a head of this
      category, even without feature matching. The probe stops but copies
      no features — yielding the Elsewhere (default) exponent at PF. -/
  | headEncounter : Cat → SatisfactionCond
  deriving Repr

/-- Is an atomic (non-disjunctive) condition met? -/
private def atomicSatisfied (cond : SatisfactionCond) (fb : FeatureBundle)
    (ctx : Option Cat) : Bool :=
  match cond with
  | .featureMatch ft => hasValuedFeature fb ft
  | .headEncounter cat => ctx == some cat
  | .disjunctive _ => false  -- nested disjunctions handled at top level

/-- Check whether a satisfaction condition is met.

    `fb` is the feature bundle of the element the probe encounters.
    `ctx` is the syntactic category of that element (if it's a head).
    Returns `true` if the probe should stop searching. -/
def SatisfactionCond.isSatisfied (cond : SatisfactionCond) (fb : FeatureBundle)
    (ctx : Option Cat) : Bool :=
  match cond with
  | .featureMatch ft => hasValuedFeature fb ft
  | .disjunctive conds => conds.any (atomicSatisfied · fb ctx)
  | .headEncounter cat => ctx == some cat

/-- Did the probe copy features, or just stop?

    When satisfied by feature match, the probe copies features (→ real agreement).
    When satisfied by head encounter, no features are copied (→ default/Elsewhere).
    For disjunctive conditions, feature copying occurs iff the first satisfied
    condition is a feature match. -/
def SatisfactionCond.copiedFeatures (cond : SatisfactionCond) (fb : FeatureBundle)
    (ctx : Option Cat) : Bool :=
  match cond with
  | .featureMatch ft => hasValuedFeature fb ft
  | .disjunctive conds =>
    match conds.find? (atomicSatisfied · fb ctx) with
    | some (.featureMatch ft) => hasValuedFeature fb ft
    | _ => false  -- head encounter or nested → no features copied
  | .headEncounter _ => false

/-- The `Probe` a `SatisfactionCond` denotes, given how a goal exposes
    its features (`feats`) and host category (`cat`): visibility =
    halting (interaction), activity = feature copying (satisfaction). -/
def SatisfactionCond.toProbe {α : Type*} (cond : SatisfactionCond)
    (feats : α → FeatureBundle) (cat : α → Option Cat) : Probe α :=
  { vis := fun a => cond.isSatisfied (feats a) (cat a)
    act := fun a => cond.copiedFeatures (feats a) (cat a) }

/-- Mam's Infl probe satisfaction condition:
    satisfied by EITHER matching φ-features OR encountering transitive Voice. -/
def mamInflSatisfaction : SatisfactionCond :=
  .disjunctive [.featureMatch (.phi (.person .third)), .headEncounter .v]

/-- Intransitive environment: the probe encounters a DP with φ-features
    (no Voice_TR in the way). Feature match is satisfied → real agreement. -/
theorem mam_intransitive_satisfied :
    mamInflSatisfaction.isSatisfied
      (.ofGramFeatures [.valued (.phi (.person .first)), .valued (.phi (.number .singular))])
      none = true := by decide

/-- Transitive environment: the probe encounters Voice_TR (category.v).
    Head encounter is satisfied → probe stops without copying features. -/
theorem mam_transitive_satisfied :
    mamInflSatisfaction.isSatisfied ⊥ (some .v) = true := by decide

/-- In the transitive case, no features are copied — yielding default. -/
theorem mam_transitive_no_copy :
    mamInflSatisfaction.copiedFeatures ⊥ (some .v) = false := by decide

/-- In the intransitive case, features ARE copied — yielding real agreement. -/
theorem mam_intransitive_copies :
    mamInflSatisfaction.copiedFeatures
      (.ofGramFeatures [.valued (.phi (.person .first)), .valued (.phi (.number .singular))])
      none = true := by decide

/-- Infl's satisfaction condition, unfolded: φ-match or Voice_TR encounter. -/
theorem mamInflSatisfaction_isSatisfied (fb : FeatureBundle) (ctx : Option Cat) :
    mamInflSatisfaction.isSatisfied fb ctx
      = (hasValuedFeature fb (.phi (.person .third)) || ctx == some Cat.v) := by
  simp [mamInflSatisfaction, SatisfactionCond.isSatisfied, atomicSatisfied]

/-- Head-encounter satisfaction never copies: Infl copies features iff
    they are there to copy, whatever the context. -/
theorem mamInflSatisfaction_copiedFeatures (fb : FeatureBundle) (ctx : Option Cat) :
    mamInflSatisfaction.copiedFeatures fb ctx
      = hasValuedFeature fb (.phi (.person .third)) := by
  cases hv : hasValuedFeature fb (.phi (.person .third)) <;>
    cases hc : ctx == some Cat.v <;>
      simp [mamInflSatisfaction, SatisfactionCond.copiedFeatures, atomicSatisfied,
        List.find?, hv, hc]

end Minimalist
