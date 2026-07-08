import Linglib.Data.UD.Basic
import Linglib.Morphology.Word

/-!
# Wambaya Reciprocal Fragment
[nordlinger-2023]

Wambaya (Australian, Mirndi) marks reciprocity with the bound
morpheme **-ngg-** (glossed RR = reciprocal/reflexive) in the
auxiliary verb complex. The same morpheme serves both reciprocal
and reflexive functions — a clitic strategy.

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

/-- The same morpheme serves both reciprocal and reflexive functions. -/
def isIdenticalToReflexive : Bool := true

end Wambaya.Reciprocals
