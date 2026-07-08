import Linglib.Morphology.MorphRule
import Linglib.Syntax.Reciprocal

/-!
# Modern Greek Reciprocal Fragment
[nordlinger-2023] [siloni-2008]

Modern Greek marks reciprocity with nonactive voice morphology (verbal
affix strategy, monovalent). The same morphology is used for reflexives,
passives, and middles — WALS Ch 106 classifies Greek as "mixed."

CAN form discontinuous reciprocals with "me" ('with'):
"O Giannis filithike me ti Maria" ('John kissed with Maria')
[nordlinger-2023] ex. 27b, 36.

Greek allows discontinuous reciprocals ([nordlinger-2023] ex. 27b),
which per Siloni's analysis implies lexical formation (Dimitriadis 2004, 2008).
-/

namespace Greek.StandardModern.Reciprocals

open Morphology

/-- Greek nonactive voice suffix as a morphological rule.

    The nonactive suffix (various allomorphs: -ome, -omai, etc.)
    marks reciprocal, reflexive, passive, and middle voice. -/
def nonactiveVoiceSuffix : MorphRule Bool :=
  { category := .voice
  , value := "nonactive"
  , formRule := fun stem => stem ++ "ome"
  , featureRule := id
  , valenceRule := fun _ => some ComplementType.none
  , semEffect := id
  }

/-- The Greek nonactive suffix is a voice operation (not valence). -/
theorem nonactive_is_voice :
    nonactiveVoiceSuffix.category = .voice := rfl

open Reciprocal

/-- Nonactive voice morphology as a reciprocal marker (shared with
    reflexives/middles; [nordlinger-2023] ex. 27). -/
def nonactive : ReciprocalMarker :=
  { form := "nonactive voice", strategy := .verbalAffix
  , readings := [.reciprocal, .reflexive] }

/-- o enas ton allon — distinct periphrastic reciprocal, whose existence
    underlies the WALS "mixed" classification ([maslova-nedjalkov-2013]). -/
def oEnasTonAllon : ReciprocalMarker :=
  { form := "o enas ton allon", strategy := .bipartiteNP }

/-- Marker inventory, primary strategy first. -/
def markers : List ReciprocalMarker := [nonactive, oEnasTonAllon]

end Greek.StandardModern.Reciprocals
