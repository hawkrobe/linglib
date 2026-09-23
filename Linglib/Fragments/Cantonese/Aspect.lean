module

public import Linglib.Semantics.Aspect.Defs

/-!
# Cantonese aspect markers

The postverbal aspect suffixes of Cantonese (ISO `yue`) with the viewpoint each marks, following
[matthews-yip-1994] and [cheung-2007]: the perfective *-zo*, the experiential *-gwo*, an
experiential perfect, and the two imperfectives, the progressive *-gan* of ongoing activity and
the continuous *-zyu* of a maintained state or posture. The association of these suffixes with
the outer and inner aspect projections is the analysis of [liu-yip-2026] and lives in
`Studies/LiuYip2026.lean`; the postverbal *again*-suffix *-faan* is a presupposition trigger and
is entered with the other *again*-elements in `Fragments/Cantonese/Particles.lean`.

## References

* [matthews-yip-1994]
* [cheung-1972]
* [cheung-2007]
-/

@[expose] public section

namespace Cantonese.Aspect

/-- A Cantonese postverbal aspect suffix: its jyutping, its character, its gloss and the
viewpoint it marks. -/
structure Marker where
  /-- The jyutping form with tone number. -/
  jyutping : String
  /-- The character. -/
  hanzi : String
  /-- The gloss. -/
  gloss : String
  /-- The viewpoint the suffix marks. -/
  viewpoint : Aspect.ViewpointType
  deriving Repr, DecidableEq

/-- The perfective *-zo* 咗. -/
def zo : Marker := { jyutping := "zo2", hanzi := "咗", gloss := "PFV", viewpoint := .perfective }

/-- The experiential *-gwo* 過, an experiential perfect. -/
def gwo : Marker := { jyutping := "gwo3", hanzi := "過", gloss := "EXP", viewpoint := .perfect }

/-- The progressive *-gan* 緊, an imperfective of ongoing activity. -/
def gan : Marker :=
  { jyutping := "gan2", hanzi := "緊", gloss := "PROG", viewpoint := .imperfective }

/-- The continuous *-zyu* 住, an imperfective of a maintained state or posture. -/
def zyu : Marker :=
  { jyutping := "zyu6", hanzi := "住", gloss := "CONT", viewpoint := .imperfective }

/-- The aspect suffixes. -/
def markers : List Marker := [zo, gwo, gan, zyu]

end Cantonese.Aspect
