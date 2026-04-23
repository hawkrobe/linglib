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

Two API layers:

* `Bool` helpers (`precedes`, `isSubjectCat`, `isSubjectWord`,
  `auxPrecedesSubject`, `subjectPrecedesAux`) — computational, used by
  existing theorem statements `... ws = true`.
* `Prop` wrappers (`IsSubjectWord`, `AuxPrecedesSubject`,
  `SubjectPrecedesAux`) with `Decidable` instances — for new propositional
  use sites per the project's Bool→Prop migration policy.

Note `isSubjectWord` is so named (rather than `isSubject`) to avoid a
naming collision with `UD.DepRel.isSubject`, which classifies dependency
labels rather than words.
-/

namespace Inversion

/-- Does the *earliest* `p`-word precede the *earliest* `q`-word in `ws`?

    Returns `false` if no `p`-word or no `q`-word exists. Note this is
    weaker than the existential reading "∃ i, j, p (ws[i]) ∧ q (ws[j]) ∧
    i < j" — only the first match of each predicate is considered. For
    inversion-style word-order questions this matches the linguist's
    intended reading (was the first auxiliary before the first subject?). -/
def precedes (p q : Word → Bool) (ws : List Word) : Bool :=
  match ws.findIdx? p, ws.findIdx? q with
  | some i, some j => i < j
  | _, _ => false

/-- Is this a nominal category that can be a subject? -/
def isSubjectCat (c : UD.UPOS) : Bool :=
  c == .PROPN || c == .NOUN || c == .PRON

/-- Is this word a non-wh subject?

    Named `isSubjectWord` rather than `isSubject` to avoid a name
    collision with `UD.DepRel.isSubject` (which classifies dependency
    labels). -/
def isSubjectWord (w : Word) : Bool :=
  isSubjectCat w.cat && !w.features.wh

/-- Does the auxiliary precede the subject? -/
def auxPrecedesSubject (ws : List Word) : Bool :=
  precedes (·.cat == .AUX) isSubjectWord ws

/-- Does the subject precede the auxiliary? -/
def subjectPrecedesAux (ws : List Word) : Bool :=
  precedes isSubjectWord (·.cat == .AUX) ws

-- Prop wrappers

/-- `Prop`-valued companion to `isSubjectWord`. -/
def IsSubjectWord (w : Word) : Prop := isSubjectWord w = true

/-- `Prop`-valued companion to `auxPrecedesSubject`. -/
def AuxPrecedesSubject (ws : List Word) : Prop := auxPrecedesSubject ws = true

/-- `Prop`-valued companion to `subjectPrecedesAux`. -/
def SubjectPrecedesAux (ws : List Word) : Prop := subjectPrecedesAux ws = true

instance (w : Word) : Decidable (IsSubjectWord w) := by
  unfold IsSubjectWord; infer_instance

instance (ws : List Word) : Decidable (AuxPrecedesSubject ws) := by
  unfold AuxPrecedesSubject; infer_instance

instance (ws : List Word) : Decidable (SubjectPrecedesAux ws) := by
  unfold SubjectPrecedesAux; infer_instance

end Inversion
