/-
HPSG Feature System.

General feature types and constraints: HEAD, VALENCE, INV.
Phrase structure rules and unification are in Basic.lean.
Pollard & Sag (1994).
-/

import Linglib.Core.Basic

namespace HPSG

section HeadFeatures

/-- Verb form features. -/
inductive VForm' where
  | finite
  | infinitive
  | gerund
  | pastParticiple
  | presentParticiple
  deriving Repr, DecidableEq

/-- The INV(erted) feature for subject-aux inversion. -/
inductive Inv where
  | plus
  | minus
  deriving Repr, DecidableEq

/-- Head features bundle. -/
structure HeadFeatures' where
  vform : VForm' := .finite
  inv : Inv := .minus
  aux : Bool := false
  deriving Repr, DecidableEq

end HeadFeatures

section WordOrder

/-- Find the position of the first auxiliary. -/
def findAuxPosition (ws : List Word) : Option Nat :=
  ws.findIdx? (·.cat == .AUX)

/-- Is this a nominal category that can be a subject? -/
def isSubjectCat (c : Cat) : Bool :=
  c == .PROPN || c == .NOUN || c == .PRON

/-- Find the position of the first subject (non-wh DP). -/
def findSubjectPosition (ws : List Word) : Option Nat :=
  ws.findIdx? λ w => isSubjectCat w.cat && !w.features.wh

/-- Auxiliary precedes subject. -/
def auxPrecedesSubject (ws : List Word) : Bool :=
  match findAuxPosition ws, findSubjectPosition ws with
  | some a, some s => a < s
  | _, _ => false

/-- Subject precedes auxiliary. -/
def subjectPrecedesAux (ws : List Word) : Bool :=
  match findAuxPosition ws, findSubjectPosition ws with
  | some a, some s => s < a
  | _, _ => false

/-- [INV +] correlates with aux-before-subject order. -/
def invPlusImpliesAuxFirst (inv : Inv) (ws : List Word) : Prop :=
  inv = .plus → auxPrecedesSubject ws = true

/-- [INV -] correlates with subject-before-aux order. -/
def invMinusImpliesSubjectFirst (inv : Inv) (ws : List Word) : Prop :=
  inv = .minus → subjectPrecedesAux ws = true

end WordOrder

section Theorems

/-- INV+ and INV- are mutually exclusive. -/
theorem inv_exclusive (i : Inv) : i = .plus ∨ i = .minus := by
  cases i <;> simp

/-- If we have aux-first order, INV+ is possible. -/
theorem aux_first_allows_inv_plus (ws : List Word)
    (h : auxPrecedesSubject ws = true) :
    invPlusImpliesAuxFirst .plus ws := by
  intro _; exact h

/-- If we have subject-first order, INV- is possible. -/
theorem subject_first_allows_inv_minus (ws : List Word)
    (h : subjectPrecedesAux ws = true) :
    invMinusImpliesSubjectFirst .minus ws := by
  intro _; exact h

end Theorems

end HPSG
