import Linglib.Core.Lexical.Word

/-!
# Wambaya Reciprocal Fragment
@cite{nordlinger-2023}

Wambaya (Australian, Mirndi) marks reciprocity with the bound
morpheme **-ngg-** (glossed RR = reciprocal/reflexive) in the
auxiliary verb complex. The same morpheme serves both reciprocal
and reflexive functions. This is a clitic strategy (bivalent):
the clause retains its transitive structure.

In @cite{nordlinger-2023} ex. 11 (citing Nordlinger 1998, p. 142):
"Alag-bulu wurlu-**ngg**-a nyurrunyurru" = 'The two children are
chasing each other.' Here "wurlu-ngg-a" = 3DU.SBJ-RR-NFUT
(auxiliary with RR marker) and "nyurrunyurru" = 'chase' (coverb).

WALS Ch 106 classifies Wambaya as "identical to reflexive."
-/

namespace Fragments.Wambaya.Reciprocals

/-- -ngg- (RR) — reciprocal/reflexive bound morpheme in the auxiliary.
    The gloss value represents the morpheme; surface allomorphs vary
    by auxiliary paradigm. -/
def rrMorpheme : Word :=
  ⟨"-ngg-", .PART, {}⟩

/-- The same morpheme serves both reciprocal and reflexive functions. -/
def isIdenticalToReflexive : Bool := true

end Fragments.Wambaya.Reciprocals
