import Linglib.Core.Typology.LanguageProfile

/-!
# Bambara typological profile

Aggregate WALS-style typological profile for Bambara (ISO 639-3 `bam`).

This is the only Bambara fragment in linglib at present; the language
appears in the cross-linguistic relativization sample as the canonical
example of an internally-headed RC language.
-/

namespace Fragments.Bambara

open Core.Typology in
/-- Bambara: SOV, postpositional, Mande; internally-headed relative clauses
    via the non-reduction strategy (the head noun appears inside the RC). -/
def typology : LanguageProfile :=
  LanguageProfile.ofWALS "bam" "Bambara"
    |>.withRelativization
        { subjStrategy := .nonReduction
        , oblStrategy := .notRelativizable
        , rcPosition := .internallyHeaded
        , lowestRelativizable := .directObject
        , notes := "Internally-headed RC; non-reduction strategy; "
                ++ "limited to subject and direct object on AH" }

end Fragments.Bambara
