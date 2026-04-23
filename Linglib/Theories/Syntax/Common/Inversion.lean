import Linglib.Core.Lexical.Word

/-!
# Subject–auxiliary inversion helpers

Word-list predicates for detecting subject–auxiliary inversion in a
linearised string, shared by HPSG (`Theories/Syntax/HPSG/Inversion.lean`)
and Minimalism (`Theories/Syntax/Minimalism/Inversion.lean`) accounts.

The helpers operate on raw `List Word`, using UD UPOS tags and the `wh`
feature. They make no commitment to either theory's representation of
the inversion alternation; both theories' bridge theorems quantify over
these predicates to license their own inversion derivations.
-/

namespace Inversion

/-- Does some word satisfying `p` precede some word satisfying `q`? -/
def precedes (p q : Word → Bool) (ws : List Word) : Bool :=
  match ws.findIdx? p, ws.findIdx? q with
  | some i, some j => i < j
  | _, _ => false

/-- Is this a nominal category that can be a subject? -/
def isSubjectCat (c : UD.UPOS) : Bool :=
  c == .PROPN || c == .NOUN || c == .PRON

/-- Is this word a non-wh subject? -/
def isSubject (w : Word) : Bool :=
  isSubjectCat w.cat && !w.features.wh

/-- Does the auxiliary precede the subject? -/
def auxPrecedesSubject (ws : List Word) : Bool :=
  precedes (·.cat == .AUX) isSubject ws

/-- Does the subject precede the auxiliary? -/
def subjectPrecedesAux (ws : List Word) : Bool :=
  precedes isSubject (·.cat == .AUX) ws

end Inversion
