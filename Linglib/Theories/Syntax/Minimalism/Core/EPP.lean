import Linglib.Theories.Syntax.Minimalism.Core.Basic

/-!
# Extended Projection Principle (EPP)

The EPP requires Spec,TP to be filled. Cross-linguistically, languages
differ in *how* this requirement is satisfied, yielding different basic
word orders from the same underlying vP-internal structure.

## Strategies

- **Subject raising** (English, French): DP subject raises from Spec,vP
  to Spec,TP → SVO
- **VP raising** (Toba Batak, Malagasy): VP/predicate phrase raises to
  Spec,TP → VOS
- **Expletive** (English *there*, French *il*): expletive inserted in
  Spec,TP, subject stays low → existential constructions
- **None** (one analysis of Irish/Arabic VSO): Spec,TP unfilled, T
  attracts the verb but not a phrasal specifier → VSO
-/

namespace Minimalism

/-- What satisfies the EPP (requirement to fill Spec,TP). -/
inductive EPPStrategy where
  /-- Subject DP raises to Spec,TP (English, French, etc.). -/
  | subjectRaising
  /-- VP/predicate phrase raises to Spec,TP (Toba Batak VOS, Malagasy VOS). -/
  | vpRaising
  /-- Expletive inserted in Spec,TP (English *there*, French *il*). -/
  | expletive
  /-- No EPP — verb-initial order persists (one analysis of Irish/Arabic VSO). -/
  | none
  deriving Repr, DecidableEq

/-- Word-order parameter: EPP strategy and predicted basic order. -/
structure WordOrderParameter where
  language : String
  eppStrategy : EPPStrategy
  predictedOrder : String

def english_wo : WordOrderParameter :=
  { language := "English", eppStrategy := .subjectRaising, predictedOrder := "SVO" }

def tobaBatak_wo : WordOrderParameter :=
  { language := "Toba Batak", eppStrategy := .vpRaising, predictedOrder := "VOS" }

def irish_wo : WordOrderParameter :=
  { language := "Irish", eppStrategy := .none, predictedOrder := "VSO" }

end Minimalism
