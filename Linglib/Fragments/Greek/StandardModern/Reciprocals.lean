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

open Reciprocal

def nonactive : Marker :=
  { form := "-ome", strategy := .verbalAffix
  , readings := [.reciprocal, .reflexive] }

/-- o enas ton allon — distinct periphrastic reciprocal, whose existence
    underlies the WALS "mixed" classification ([maslova-nedjalkov-2013]). -/
def oEnasTonAllon : Marker :=
  { form := "o enas ton allon", strategy := .bipartiteNP }

/-- Marker inventory, primary strategy first. -/
def markers : List Marker := [nonactive, oEnasTonAllon]

end Greek.StandardModern.Reciprocals
