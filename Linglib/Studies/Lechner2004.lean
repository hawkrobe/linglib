import Linglib.Features.Acceptability

/-!
# Lechner (2004): Ellipsis in Comparatives

This file formalizes the binding diagnostic for phrasal comparatives of [lechner-2004]: an
R-expression inside the comparative-deletion site induces a disjoint-reference effect with a
c-commanding matrix pronoun, expected if the deletion site is reconstructed at LF and visible
to Principle C, unexpected if the ellipsis is recovered only in the semantics
([kennedy-1999]). Two structural analyses of phrasal comparatives make opposite predictions
(`PhrasalAnalysis`). Under the reduction analysis the standard sits in a clause-internal
position parallel to the associate, so coreference is available exactly when no matrix
expression c-commands the associate (`RAPredictsCoref`); under the direct analysis the
*than*-phrase is external and coreference is always available (`DAPredictsCoref`). A body of
binding data realizes an analysis when every datum fits its prediction (`realizesReduction`,
`realizesDirect`), and the book's English data realize the reduction analysis alone
(`english_lechner_realizes_reduction`).

## Implementation notes

A datum records whether some matrix expression c-commands the associate and whether
coreference into the standard is attested (`BindingDatum`). The obviation of the effect under
clausal embedding, which the book attributes to vehicle change, would need a depth dimension
the schema lacks, as would the extension of the diagnostic to reflexives and reciprocals and
the coordinate-structure argument for syntactic identification of the deletion site.

## References

* [lechner-2004]
* [kennedy-1999]
-/

namespace Lechner2004

open Features (Acceptability)

/-- The two structural analyses of phrasal comparatives: under reduction, phrasal *than NP*
derives from clausal *than [NP is Adj]* and the standard sits in a clause-internal position
parallel to the associate; under the direct analysis the *than*-phrase is external and the
standard is its complement. -/
inductive PhrasalAnalysis where
  | reduction
  | direct
  deriving DecidableEq, Repr

/-- A binding datum of the disjoint-reference diagnostic: whether some matrix expression
c-commands the comparative associate, and whether coreference between that expression and an
R-expression inside the standard is attested; `citationId` names the source example and
`acceptability` keeps the graded judgment. -/
structure BindingDatum where
  citationId : String
  acceptability : Acceptability
  pronCCommandsAssociate : Bool
  corefAttested : Bool
  deriving DecidableEq, Repr

/-- The reduction analysis's prediction: matrix material c-commanding the associate also
c-commands the standard's R-expression, so coreference is available iff the matrix expression
does not c-command the associate. -/
def RAPredictsCoref (d : BindingDatum) : Prop :=
  d.pronCCommandsAssociate = false ↔ d.corefAttested = true

instance (d : BindingDatum) : Decidable (RAPredictsCoref d) := by
  unfold RAPredictsCoref; infer_instance

/-- The direct analysis's prediction: the *than*-phrase is external and never c-commanded
into, so coreference is always available. -/
def DAPredictsCoref (d : BindingDatum) : Prop :=
  d.corefAttested = true

instance (d : BindingDatum) : Decidable (DAPredictsCoref d) := by
  unfold DAPredictsCoref; infer_instance

/-- Binding data realize the reduction analysis iff every datum fits its prediction. -/
def realizesReduction (data : List BindingDatum) : Prop :=
  ∀ d ∈ data, RAPredictsCoref d

instance (data : List BindingDatum) : Decidable (realizesReduction data) := by
  unfold realizesReduction; exact List.decidableBAll _ _

/-- Binding data realize the direct analysis iff every datum attests coreference. -/
def realizesDirect (data : List BindingDatum) : Prop :=
  ∀ d ∈ data, DAPredictsCoref d

instance (data : List BindingDatum) : Decidable (realizesDirect data) := by
  unfold realizesDirect; exact List.decidableBAll _ _

/-- Which analyses a body of binding data realizes. -/
structure HeadAvailability where
  reductionRealized : Bool
  directRealized : Bool
  deriving DecidableEq, Repr

/-- The analyses realized by binding data, decided from the two predictions. -/
def headAvailabilityFromBinding (data : List BindingDatum) : HeadAvailability where
  reductionRealized := decide (realizesReduction data)
  directRealized := decide (realizesDirect data)

/-! ### The book's English data

The data are the second chapter's (24) and (28a). -/

/-- (24) *Mary is prouder of Johnᵢ than heᵢ is*: the matrix pronoun c-commands the
associate and coreference into the deletion site is unavailable. -/
def lechner_24 : BindingDatum :=
  { citationId := "24"
    acceptability := .unacceptable
    pronCCommandsAssociate := true
    corefAttested := false }

/-- (28a) *Johnᵢ is taller than himselfᵢ*: the matrix subject binds the reflexive remnant,
so the binding relation into the *than*-phrase is attested. -/
def lechner_28a : BindingDatum :=
  { citationId := "28a"
    acceptability := .ok
    pronCCommandsAssociate := false
    corefAttested := true }

/-- The book's English binding data. -/
def englishLechnerData : List BindingDatum :=
  [lechner_24, lechner_28a]

/-- The English data realize the reduction analysis: the disjoint-reference effect follows
from reconstruction of the deletion site. -/
theorem english_lechner_realizes_reduction :
    realizesReduction englishLechnerData := by
  decide

/-- The English data do not realize the direct analysis, which predicts coreference
throughout. -/
theorem english_lechner_rules_out_direct :
    ¬ realizesDirect englishLechnerData := by
  decide

end Lechner2004
