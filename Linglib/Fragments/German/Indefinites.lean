import Linglib.Features.IndefiniteType

/-!
# German Indefinite Pronouns
@cite{aloni-port-2015} @cite{bubnov-2026}

German *irgend-* is an epistemic indefinite (type iv): its semantics
requires variation across epistemic alternatives (var(∅,x)), allowing
it in both specific-unknown and non-specific contexts.

Diachronically, *irgend-* extended from non-specific to epistemic
(@cite{aloni-port-2015}), instantiating the semantic weakening path
var(v,x) → var(∅,x) (@cite{bubnov-2026} §6, Figure 3).

See also `Fragments.German.ModalIndefinites` for the modal indefinite
perspective on *irgendein* (domain widening per
@cite{kratzer-shimoyama-2002}).
-/

set_option autoImplicit false

namespace Fragments.German.Indefinites

open Features.IndefiniteType

/-- German *irgend-*: epistemic indefinite (type iv).
    D&A semantics: var(∅,x). Diachronically extended from non-specific
    to epistemic (@cite{aloni-port-2015}).
    @cite{bubnov-2026} §6, Table 3. -/
def irgend : IndefiniteEntry where
  language := "German"
  form := "irgend-"
  gloss := "some (epistemic)"
  specType := .epistemic
  allowsSK := false; allowsSU := true; allowsNS := true
  source := "Aloni & Port 2015, Bubnov 2026"

theorem irgend_consistent : irgend.distributionConsistent = true := rfl

end Fragments.German.Indefinites
