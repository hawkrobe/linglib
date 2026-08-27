import Linglib.Syntax.Category.Determiner.ModalIndefinite

/-!
# Spanish modal indefinites

Lexical entries for *algún* ([alonso-ovalle-menendez-benito-2010]: epistemic, an
implicature derived from an anti-singleton domain constraint) and *uno cualquiera*
([alonso-ovalle-menendez-benito-2018]: at-issue random choice, projected from the
decision of a volitional event).
-/

namespace Spanish.ModalIndefinites

/-- *algún*: epistemic only, upper-bounded; the modal component is a conversational
implicature ([alonso-ovalle-menendez-benito-2010], §4). -/
def algún : ModalIndefinite where
  form := "algún"
  status := .implicature
  flavors := {.epistemic}
  upperBounded := true

/-- *uno cualquiera*: at-issue random choice, upper-bounded, with an unremarkable reading in
predicative position; its anchor must be a volitional event
([alonso-ovalle-menendez-benito-2018], §1.1). -/
def unoCualquiera : ModalIndefinite where
  form := "uno cualquiera"
  status := .atIssue
  flavors := {.circumstantial}
  upperBounded := true
  hasUnremarkableReading := true
  canBePredicate := true
  anchorConstraint := some .volitionalOnly

/-- The Spanish modal indefinite paradigm. -/
def paradigm : List ModalIndefinite := [algún, unoCualquiera]

end Spanish.ModalIndefinites
