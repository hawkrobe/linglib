import Linglib.Typology.Indefinite

/-!
# German Indefinite Pronouns
@cite{aloni-port-2015} @cite{bubnov-2026} @cite{wals-2013}

German uses multiple morphological bases for indefinites: the dedicated
prefix *irgend-* (special), and the generic-noun-derived *jemand* 'someone'
and *etwas* 'something'. Per @cite{wals-2013} F46A, German is classified
`.mixed` on this basis.

*irgend-* is an epistemic indefinite (D&A type iv, `var(∅,x)`):
its semantics requires variation across epistemic alternatives, allowing
both specific-unknown and non-specific contexts. Diachronically, *irgend-*
extended from non-specific to epistemic (@cite{aloni-port-2015}),
instantiating the semantic weakening path `var(v,x) → var(∅,x)`
(@cite{bubnov-2026} §6, Figure 3).

See also `Fragments.German.ModalIndefinites` for the modal-indefinite
perspective on *irgendein* (domain widening per
@cite{kratzer-shimoyama-2002}).
-/

set_option autoImplicit false

namespace Fragments.German.Indefinites

open Typology.Indefinite

/-- German *irgend-*: dedicated indefinite prefix (special basis),
    epistemic indefinite (D&A type iv).
    @cite{aloni-port-2015}; @cite{bubnov-2026} §6, Table 3. -/
def irgendEntry : IndefiniteEntry where
  language := "German"
  form := "irgend-"
  gloss := "some (epistemic)"
  basis := .special
  functions := {.specificUnknown, .irrealis}

/-- German *jemand* 'someone' / *etwas* 'something': generic-noun-derived
    (etymologically *je-man[d]* 'ever-person'); used for SK + SU. -/
def jemandEntry : IndefiniteEntry where
  language := "German"
  form := "jemand/etwas"
  gloss := "someone/something"
  basis := .genericNoun
  functions := {.specificKnown, .specificUnknown}

/-- The German indefinite paradigm: special prefix + generic-noun forms,
    yielding WALS F46A `.mixed`. -/
def paradigm : IndefiniteParadigm where
  language := "German"
  isoCode := "deu"
  forms := [irgendEntry, jemandEntry]

/-- German's WALS F46A classification: paradigm uses two distinct bases
    (`.special` and `.genericNoun`) → derives `.mixed`. -/
theorem german_paradigm_is_mixed :
    paradigm.toWALS46A = some .mixed := rfl

end Fragments.German.Indefinites
