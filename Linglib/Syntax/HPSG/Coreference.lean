import Linglib.Syntax.HPSG.Basic
import Linglib.Syntax.Binding.Basic

/-!
# HPSG Coreference (Binding)

Binding via **ARG-ST outranking** (obliqueness order), following
@cite{sag-wasow-bender-2003} Ch. 7 and @cite{pollard-sag-1994}. The c-command
analogue in HPSG is *outranking* on the ARG-ST list: a less-oblique argument
(the subject, at position 0) outranks a more-oblique one (the object, at
position 1).

As with the other frameworks, the binding principles are *not* restated here:
this file supplies HPSG's command relation as a `Binding.CommandRelation`
instance, and the framework-neutral engine (`Syntax/Binding/Basic.lean`) derives
Principles A/B over it. (SWB2003's two-principle MODE system — Principle B
subsuming Principle C — is the model-theoretic RSRL formalization in
`Syntax/HPSG/Binding.lean`; this file is the ARG-ST command relation the shared
engine consumes.) The file is language-neutral — it imports no Fragment.

## Main definitions

- `toArgSt`, `subjectOutranksObject`, `sameArgSt` — the ARG-ST outranking
  relation and its locality restriction, over a `Binding.SimpleClause`.
- `instance : CommandRelation` — the HPSG instance of the abstract command
  relation (ARG-ST outranking); the engine supplies the binding principles.
-/

namespace HPSG.Coreference

open Binding (SimpleClause Pos CommandRelation)

/-! ### ARG-ST outranking -/

/-- Convert a word to a minimal HPSG Synsem for ARG-ST construction. -/
private def wordToSynsem (w : Word) : HPSG.Synsem := { cat := w.cat }

/-- Build the ARG-ST for a clause from its arguments: `[subject, object]`,
    ordered by obliqueness (@cite{sag-wasow-bender-2003}). -/
def toArgSt (clause : SimpleClause) : HPSG.ArgSt :=
  match clause.object with
  | none => { args := [wordToSynsem clause.subject] }
  | some obj => { args := [wordToSynsem clause.subject, wordToSynsem obj] }

/-- Subject outranks object on ARG-ST: subject at 0 outranks object at 1. -/
def subjectOutranksObject (clause : SimpleClause) : Bool :=
  (toArgSt clause).outranks 0 1

/-- Both positions are on the same ARG-ST list (the local binding domain). -/
def sameArgSt (clause : SimpleClause) : Bool :=
  match clause.object with
  | none => true
  | some _ => 1 < (toArgSt clause).args.length

/-! ### HPSG as a command relation -/

/-- The HPSG command relation: ARG-ST outranking. The subject (0) outranks the
    object (1); the object does not outrank the subject. -/
def commands (c : SimpleClause) : Pos → Pos → Prop
  | .subject, .object => subjectOutranksObject c = true
  | .object, .subject => (toArgSt c).outranks 1 0 = true
  | _, _ => False

instance (c : SimpleClause) (i j : Pos) : Decidable (commands c i j) := by
  unfold commands; split <;> infer_instance

/-- Locality: the arguments share one ARG-ST list. -/
def sameDomain (c : SimpleClause) (_ _ : Pos) : Prop := sameArgSt c = true

instance (c : SimpleClause) (i j : Pos) : Decidable (sameDomain c i j) :=
  inferInstanceAs (Decidable (sameArgSt c = true))

/-- The HPSG instance of the abstract command relation
    (@cite{barker-pullum-1990}): ARG-ST outranking. The engine supplies the
    binding principles; a study applies them with this instance and a language
    classifier. -/
instance : CommandRelation where
  commands := commands
  sameDomain := sameDomain
  commandsDec := fun c i j => inferInstance
  sameDomainDec := fun c i j => inferInstance

end HPSG.Coreference
