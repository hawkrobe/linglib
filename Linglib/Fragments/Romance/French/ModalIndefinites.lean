import Linglib.Syntax.Category.Determiner.ModalIndefinite

/-!
# French modal indefinites

Lexical entry for *n'importe quel* ([jayez-tovena-2006]).
-/

namespace French.ModalIndefinites

/-- *n'importe quel* ("no matter which"): at-issue random choice, not upper-bounded
([jayez-tovena-2006]). -/
def nimporteQuel : ModalIndefinite where
  form := "n'importe quel"
  status := .atIssue
  flavors := {.circumstantial}
  upperBounded := false
  anchorConstraint := some .unrestricted

/-- The French modal indefinite paradigm. -/
def paradigm : List ModalIndefinite := [nimporteQuel]

end French.ModalIndefinites
