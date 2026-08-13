import Linglib.Syntax.Comparative

/-!
# Korean Comparative Construction [stassen-1985]

Korean uses a **separative** comparative construction: the standard NP is
marked with the postposition *-boda* ('from/than'), which has ablative
semantics. The adjective appears in its bare form with no comparative
morphology; the optional adverb *deo* ('more') may intensify.

Example: *Yenghi-ga Chelswu-boda (deo) khu-da*
         'Yenghi-NOM Chelswu-than (more) tall-DECL'
         = 'Yenghi is taller than Chelswu'

The marker *-boda* is sometimes analyzed as a particle rather than a case
marker, but its ablative/separative semantics ('from the point of view of')
places Korean firmly in the separative class in [stassen-1985]'s
typology.
-/

set_option autoImplicit false

namespace Korean.Comparison

open Comparative

/-- The *-boda* comparative: separative postposition-marked standard, no
    degree morphology. -/
def boda : Comparative :=
  { standardMarker := some "-boda"
  , caseAssignment := .fixed
  , fixedEncoding := some .adverbial
  , standardCase := some .abl }

/-- No overt degree marking; the adverb *deo* is an optional intensifier. -/
def degreeWord : DegreeWordType := .noDegreeMarking

/-- Superlative as comparative with universal standard. -/
def superlative : SuperlativeStrategy := .comparativeUniversal

end Korean.Comparison
