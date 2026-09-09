import Linglib.Features.Reflex
import Linglib.Syntax.Extraction

/-!
# Mam extraction marking

The extraction marking of Mam (Mayan, Western Highlands of Guatemala) as reflex cells: subject
(ergative) extraction switches the verb to an antipassive, the Mayan repair for the Ergative
Extraction Constraint ([aissen-2017]; the San Juan Atitán forms in [scott-2023]), oblique
extraction places the movement enclitic =(y)a' on the Voice or directional head of the verbal
complex ([england-1989], [elkins-torrence-brown-2026]), and absolutive extraction is unmarked. The
distribution of the enclitic across adjunct types, clause sizes and movement paths is the matter
of `Studies/ElkinsTorrenceBrown2026.lean`.

## References

* [elkins-torrence-brown-2026]
* [england-1989]
* [scott-2023]
* [aissen-2017]
-/

open Extraction

namespace Mam.Extraction

/-- Reflex hosts of Mam extraction marking: the verb, and the Voice or directional head hosting
=(y)a'. -/
inductive Site
  | verb
  | voiceHead
  deriving DecidableEq, Repr

/-- The two marked cells: subject extraction antipassivizes the verb, oblique extraction places
=(y)a' on a Voice or directional head; core-object extraction is unmarked. -/
def realize : ExtractionTarget → List (Features.Reflex Site)
  | .subject => [.morpheme .verb]
  | .oblique => [.morpheme .voiceHead]
  | _ => []

/-- WALS-style label: dedicated morphemes mark extraction. -/
def strategy : ExtractionMarkingStrategy := .dedicatedMorpheme

theorem marks_oblique : Marked realize .oblique := by decide

/-- =(y)a' tracks obliques, not subjects: no voice-head reflex under subject extraction. -/
theorem eqya_not_on_subject : Features.Reflex.morpheme Site.voiceHead ∉ realize .subject := by
  decide

end Mam.Extraction
