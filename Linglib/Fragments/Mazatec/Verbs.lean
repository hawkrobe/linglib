import Linglib.Morphology.Paradigm.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# Chiquihuitlán Mazatec verb inflection

Two of the three cross-cutting inflection-class systems of Chiquihuitlán Mazatec verbs over the
cells 1sg, 2sg, 3, 1incl, 1pl, 2pl, after Jamieson's description as tabulated in
[ackerman-malouf-2013]: the ten final-vowel classes and the six neutral-aspect tone patterns,
each with unit weight.

## References

* [ackerman-malouf-2013]
-/

namespace Mazatec.Verbs

open Morphology

/-- The cells. -/
abbrev firstSg : Fin 6 := 0
abbrev secondSg : Fin 6 := 1
abbrev third : Fin 6 := 2
abbrev firstIncl : Fin 6 := 3
abbrev firstPl : Fin 6 := 4
abbrev secondPl : Fin 6 := 5

/-- Final vowels, nasal ones suffixed `N`. -/
inductive Vowel
  | ae
  | i
  | e
  | u
  | o
  | a
  | eN
  | iN
  | uN
  | oN
  | aN
  deriving DecidableEq, Repr

/-- The ten final-vowel classes. -/
def finalVowels : ParadigmSystem 6 Vowel where
  entries :=
    [(![.ae, .i, .i, .eN, .iN, .uN], 1),
      (![.ae, .e, .e, .eN, .iN, .uN], 1),
      (![.ae, .e, .ae, .eN, .iN, .uN], 1),
      (![.u, .i, .u, .uN, .iN, .uN], 1),
      (![.o, .e, .o, .oN, .iN, .uN], 1),
      (![.a, .e, .a, .aN, .iN, .uN], 1),
      (![.eN, .iN, .iN, .eN, .iN, .uN], 1),
      (![.eN, .iN, .eN, .eN, .iN, .uN], 1),
      (![.uN, .iN, .uN, .uN, .iN, .uN], 1),
      (![.aN, .iN, .eN, .aN, .iN, .uN], 1)]

/-- Tone patterns, named by their tone numbers. -/
inductive Tone
  | t3_1
  | t3_31
  | t3_14
  | t1_1
  | t2_2
  | t2_24
  | t3_2
  | t1_43
  | t3_24
  | t14_42
  | t14_34
  | t14_3
  deriving DecidableEq, Repr

/-- The six neutral-aspect tone patterns. -/
def tones : ParadigmSystem 6 Tone where
  entries :=
    [(![.t3_1, .t3_1, .t3_1, .t3_31, .t3_14, .t3_1], 1),
      (![.t1_1, .t2_2, .t2_2, .t2_2, .t2_24, .t2_2], 1),
      (![.t3_1, .t2_2, .t3_2, .t2_2, .t2_24, .t2_2], 1),
      (![.t1_43, .t1_43, .t3_24, .t14_42, .t14_34, .t14_3], 1),
      (![.t1_1, .t3_2, .t3_2, .t3_2, .t3_24, .t3_2], 1),
      (![.t3_1, .t3_2, .t3_2, .t3_2, .t3_24, .t3_2], 1)]

end Mazatec.Verbs
