import Linglib.Features.ModalIndefinite

/-!
# Spanish Modal Indefinite Fragment

Lexical entries for Spanish modal indefinites *algún*
([alonso-ovalle-menendez-benito-2010]: epistemic, with an
anti-singleton domain constraint) and *uno cualquiera*
([alonso-ovalle-menendez-benito-2018]: random choice).
-/

namespace Spanish.ModalIndefinites

open Features.ModalIndefinite

/-- *algún*: not-at-issue, epistemic only, upper-bounded. The modal
    component is a conversational implicature derived from the
    anti-singleton constraint on the domain
    ([alonso-ovalle-menendez-benito-2010], §4). -/
def algúnEntry : ModalIndefiniteEntry where
  form := "algún"
  status := .notAtIssue
  flavors := [.epistemic]
  upperBounded := true
  hasUnremarkableReading := false
  canBePredicate := false

/-- *uno cualquiera*: at-issue, random choice only, upper-bounded. The
    random-choice interpretation requires a volitional predicate; with
    non-volitional predicates only the unremarkable reading is
    available ([alonso-ovalle-menendez-benito-2018], §1.1). -/
def unoCualquieraEntry : ModalIndefiniteEntry where
  form := "uno cualquiera"
  status := .atIssue
  flavors := [.circumstantial]
  upperBounded := true
  hasUnremarkableReading := true
  canBePredicate := true
  anchorConstraint := some .volitionalOnly

/-- The Spanish modal indefinite paradigm. -/
def paradigm : List ModalIndefiniteEntry := [algúnEntry, unoCualquieraEntry]

end Spanish.ModalIndefinites
