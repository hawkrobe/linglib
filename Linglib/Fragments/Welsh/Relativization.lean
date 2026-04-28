import Linglib.Core.Relativization.Basic
import Linglib.Typology.Relativization.Defs

/-!
# Welsh Relativization Fragment
@cite{keenan-comrie-1977}

Two relative clause markers (discussed §1.3.2):
- Particle *a* with gap in NP_rel (-case, covers SU/DO)
- Particle *y* with resumptive pronoun (+case, covers IO–OCOMP)

Data from @cite{keenan-comrie-1977} Table 1 and §1.3.2.
-/

namespace Fragments.Welsh

open Core

/-- Relative particle *a*. Introduces postnominal RCs with gap in NP_rel.
    Covers subject and direct object.
    E.g., "Y dyn [a adawodd _]" 'the man [PRT left _]'. -/
def relParticleA : RelClauseMarker :=
  { form := "a"
  , npRel := .gap
  , bearsCaseMarking := false
  , rcPosition := .postNominal
  , positions := [.subject, .directObject]
  , notes := "Relative particle; NP_rel deleted; §1.3.2" }

/-- Relative particle *y*. Introduces postnominal RCs with a resumptive
    personal pronoun in NP_rel.
    Covers IO–OCOMP.
    E.g., "Y dyn [y rhoddais i'r llyfr iddo]"
    'the man [PRT I-gave the book to-him]'. -/
def relParticleY : RelClauseMarker :=
  { form := "y"
  , npRel := .resumptive
  , bearsCaseMarking := true
  , rcPosition := .postNominal
  , positions := [.indirectObject, .oblique, .genitive, .objComparison]
  , notes := "Relative particle; resumptive pronoun in NP_rel; §1.3.2" }

/-- All Welsh relative clause markers. -/
def relMarkers : List RelClauseMarker := [relParticleA, relParticleY]

/-- Welsh relativization profile (typological summary). -/
def relativization : Typology.Relativization.RelativizationProfile :=
  { subjStrategy := .gap
  , oblStrategy := .pronounRetention
  , rcPosition := .postNominal
  , lowestRelativizable := .oblique
  , notes := "Gap on subject (particle a); resumptive on obliques; "
          ++ "VSO language with post-nominal RC" }

end Fragments.Welsh
