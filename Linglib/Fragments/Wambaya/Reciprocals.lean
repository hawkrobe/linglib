import Linglib.Data.UD.Basic
import Linglib.Syntax.Reciprocal
import Linglib.Morphology.Word.Basic

open Morphology (Word)

/-!
# Wambaya Reciprocal Fragment
[nordlinger-2023]

Wambaya (Australian, Mirndi) marks reciprocity with the bound
morpheme **-ngg-** (glossed RR = reciprocal/reflexive) in the object
slot of the auxiliary's pronominal complex, a bound reciprocal pronoun
([evans-2008]); the same morpheme serves both reciprocal and reflexive
functions. Nominal subjects keep ergative marking under
reciprocalization ([evans-et-al-2007]), so the clause stays bivalent.

In [nordlinger-2023] ex. 11 (citing [nordlinger-1998], p. 142):
"Alag-bulu wurlu-**ngg**-a nyurrunyurru" = 'The two children are
chasing each other.' Here "wurlu-ngg-a" = 3DU.SBJ-RR-NFUT
(auxiliary with RR marker) and "nyurrunyurru" = 'chase' (coverb).

WALS Ch 106 classifies Wambaya as "identical to reflexive."
-/

namespace Wambaya.Reciprocals


/-- -ngg- (RR) — reciprocal/reflexive bound morpheme in the auxiliary.
    The gloss value represents the morpheme; surface allomorphs vary
    by auxiliary paradigm. -/
def rrMorpheme : Word :=
  { form :="-ngg-", cat := .PART, features := {}}

open Reciprocal in
/-- The RR morpheme as a typological marker: a bound reciprocal pronoun
    serving both reciprocal and reflexive functions (form derived from
    `rrMorpheme`). -/
def rr : Marker :=
  { form := rrMorpheme.form, strategy := .boundPronoun
  , readings := {.reciprocal, .reflexive} }

open Reciprocal in
/-- Marker inventory. -/
def markers : List Marker := [rr]

end Wambaya.Reciprocals
