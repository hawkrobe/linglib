import Linglib.Morphology.Paradigm.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# Modern Greek nominal declensions

The eight nominal inflection classes of Modern Greek by their case–number endings, after
Ralli's description as simplified in [ackerman-malouf-2013] (stem alternations and stress set
aside), as a weighted paradigm system with uniform class weights.

## References

* [ackerman-malouf-2013]
-/

namespace Greek.StandardModern.Declension

open Morphology

/-- The nominal endings. -/
inductive Ending
  | os
  | u
  | on
  | e
  | i
  | us
  | s
  | zero
  | es
  | is
  | o
  | a
  deriving DecidableEq, Repr

/-- The cells: nominative, genitive, accusative, and vocative, singular then plural. -/
abbrev nomSg : Fin 8 := 0
abbrev genSg : Fin 8 := 1
abbrev accSg : Fin 8 := 2
abbrev vocSg : Fin 8 := 3
abbrev nomPl : Fin 8 := 4
abbrev genPl : Fin 8 := 5
abbrev accPl : Fin 8 := 6
abbrev vocPl : Fin 8 := 7

/-- The eight declensions, each with unit weight. -/
def nominal : ParadigmSystem 8 Ending where
  entries :=
    [(![.os, .u, .on, .e, .i, .on, .us, .i], 1),
      (![.s, .zero, .zero, .zero, .es, .on, .es, .es], 1),
      (![.zero, .s, .zero, .zero, .es, .on, .es, .es], 1),
      (![.zero, .s, .zero, .zero, .is, .on, .is, .is], 1),
      (![.o, .u, .o, .o, .a, .on, .a, .a], 1),
      (![.zero, .u, .zero, .zero, .a, .on, .a, .a], 1),
      (![.os, .us, .os, .os, .i, .on, .i, .i], 1),
      (![.zero, .os, .zero, .zero, .a, .on, .a, .a], 1)]

end Greek.StandardModern.Declension
