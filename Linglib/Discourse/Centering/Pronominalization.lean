import Linglib.Discourse.Centering.Basic

/-!
# Centering Theory — The Pronominalization Constraint
[grosz-joshi-weinstein-1995] [gordon-grosz-gilliom-1993]
[poesio-stevenson-eugenio-hitzeman-2004]

Two variants of the constraint on realizing the backward-looking center:
`PronominalizationConstraint` ("Rule 1" of [grosz-joshi-weinstein-1995])
fires only when some pronoun is used; `CbPronominalized`
([gordon-grosz-gilliom-1993]'s unconditional strengthening, motivated by
the repeated-name penalty) is its consequent and so implies it.
-/

namespace Discourse.Centering

variable {E R U : Type*} [DecidableEq E] [CfRankerOf E R]
  [Realizes U E] [Pronominalizes U E]

/-- The backward-looking center of `cur` (after `prev`), if defined, is
    realized by a pronoun — [gordon-grosz-gilliom-1993]'s unconditional
    strengthening of "Rule 1", motivated by the repeated-name penalty. -/
def CbPronominalized (prev : Utterance E R) (cur : U) : Prop :=
  ∀ c ∈ cb prev cur, pronominalizes cur c

instance CbPronominalized.decidable (prev : Utterance E R) (cur : U) :
    Decidable (CbPronominalized prev cur) := by
  unfold CbPronominalized; infer_instance

/-- The pronominalization constraint — "Rule 1" of
    [grosz-joshi-weinstein-1995]: if any element of `Cf(prev)` is
    pronominalized in `cur`, then the backward-looking center is
    pronominalized too. Vacuously satisfied when no pronoun is used. -/
def PronominalizationConstraint (prev : Utterance E R) (cur : U) : Prop :=
  (∃ e ∈ prev.cf, pronominalizes cur e) → CbPronominalized prev cur

instance PronominalizationConstraint.decidable (prev : Utterance E R) (cur : U) :
    Decidable (PronominalizationConstraint prev cur) := by
  unfold PronominalizationConstraint; infer_instance

/-- The unconditional constraint implies the conditional one, by
    construction: `CbPronominalized` is `PronominalizationConstraint`'s
    consequent. -/
theorem CbPronominalized.constraint {prev : Utterance E R} {cur : U}
    (h : CbPronominalized prev cur) : PronominalizationConstraint prev cur :=
  fun _ => h

end Discourse.Centering
