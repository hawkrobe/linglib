/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.HPSG.Description
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.DeriveFintype

/-!
# HPSG binding theory in RSRL

This file states Principles A and B of HPSG binding theory as RSRL descriptions and checks them
on small models of a transitive clause. One argument locally o-commands another when both are on
the same argument structure and the first is less oblique. It locally o-binds the other when, in
addition, the two share their index and agree in gender and number. Principle A requires a
locally o-commanded anaphor to be locally o-bound, and Principle B requires a personal pronoun
to be locally o-free.

## Main definitions

* `HPSG.RSRL.Binding.bindingSig`: the signature, with nominal-object sorts, indices, gender and
  number values, and the relation of local o-command.
* `HPSG.RSRL.Binding.principleA`: Principle A.
* `HPSG.RSRL.Binding.principleB`: Principle B.
* `HPSG.RSRL.Binding.clause`: the model of a transitive clause with a given object.

## Implementation notes

Coindexation and agreement are token identity of the `IDX`, `GEND` and `NUM` values, so a
coindexed anaphor that clashes with its antecedent in gender or number is not bound. The
argument structure of the verb is flattened into the attributes `SUBJ` and `OBJ`, and each model
interprets local o-command directly.

## References

* [pollard-sag-1994]
* [richter-2000]
* [muller-2024-binding]
-/

namespace HPSG.RSRL.Binding

/-! ### The signature -/

/-- The sorts are signs, the nominal objects with their three species, referential indices, and
the gender and number values. -/
inductive Srt
  | top | sign | synsem | ana | ppro | npro | idx
  | gender | masc | fem | number | sing | plur
  deriving DecidableEq, Fintype, Repr

/-- The attributes are the two arguments of a sign and the index, gender and number of a nominal
object. -/
inductive Attr | SUBJ | OBJ | IDX | GEND | NUM
  deriving DecidableEq, Fintype, Repr

/-- The one relation symbol is local o-command. -/
inductive Rel | locO
  deriving DecidableEq, Fintype, Repr

/-- The immediate supersort of each sort other than `top`. -/
def Srt.parent : Srt → Option Srt
  | .top => none
  | .sign | .synsem | .idx | .gender | .number => some .top
  | .ana | .ppro | .npro => some .synsem
  | .masc | .fem => some .gender
  | .sing | .plur => some .number

/-- The depth of a sort below `top`. -/
def Srt.rank : Srt → ℕ
  | .top => 0
  | .sign | .synsem | .idx | .gender | .number => 1
  | .ana | .ppro | .npro | .masc | .fem | .sing | .plur => 2

instance : PartialOrder Srt :=
  partialOrderOfCovers (fun σ τ : Srt ↦ σ.parent = some τ) Srt.rank (by decide)

instance : DecidableLE Srt :=
  decidableLEOfCovers (covers := fun σ τ : Srt ↦ σ.parent = some τ)
    [.top, .sign, .synsem, .ana, .ppro, .npro, .idx, .gender, .masc, .fem, .number, .sing, .plur]
    (by decide)

/-- A sign introduces the subject and the object, and a nominal object introduces the index, the
gender and the number. -/
def Attr.decl : Attr → List (Srt × Srt)
  | .SUBJ | .OBJ => [(.sign, .synsem)]
  | .IDX => [(.synsem, .idx)]
  | .GEND => [(.synsem, .gender)]
  | .NUM => [(.synsem, .number)]

/-- The signature of the binding fragment. -/
@[reducible] def sig : Signature Srt := .ofDecl Attr Rel (fun _ ↦ 2) Attr.decl (by decide)

/-- The three species of nominal object inherit the index that `synsem` introduces, and a sign
has none. -/
example : sig.approp .ana .IDX = some .idx ∧ sig.approp .sign .IDX = none := by decide

/-! ### Principles A and B -/

/-- The entities at the variables `x` and `y` are coindexed when they share their index. -/
def coindexed (x y : ℕ) : Desc sig :=
  .pathEq (.feat (.var x) .IDX) (.feat (.var y) .IDX)

/-- The entities at the variables `x` and `y` agree when they share their gender and their
number. -/
def agrees (x y : ℕ) : Desc sig :=
  .and (.pathEq (.feat (.var x) .GEND) (.feat (.var y) .GEND))
    (.pathEq (.feat (.var x) .NUM) (.feat (.var y) .NUM))

/-- The entity at `y` locally o-binds the entity at `x` when it locally o-commands it, is
coindexed with it, and agrees with it. -/
def locallyOBinds (y x : ℕ) : Desc sig :=
  .and (.rel .locO ![y, x]) (.and (coindexed x y) (agrees x y))

/-- Principle A says that a locally o-commanded anaphor is locally o-bound. -/
def principleA : Desc sig :=
  .all 0 (.imp (.and (.sortAssign (.var 0) .ana) (.ex 1 (.rel .locO ![1, 0])))
    (.ex 1 (locallyOBinds 1 0)))

/-- Principle B says that a personal pronoun is locally o-free. -/
def principleB : Desc sig :=
  .all 0 (.imp (.sortAssign (.var 0) .ppro) (.neg (.ex 1 (locallyOBinds 1 0))))

/-- The grammar of the binding fragment. -/
def grammar : Grammar sig := [principleA, principleB]

/-- The two principles are closed, whereas the binding condition they quantify over has both of
its variables free. -/
theorem freeVars_grammar : ∀ d ∈ grammar, d.freeVars = ∅ := by decide

example : (locallyOBinds 1 0).freeVars = {0, 1} := by decide

/-! ### Models of a transitive clause -/

/-- The entities of a transitive clause are the verb's sign, its subject and object, two
indices, and the gender and number values. -/
inductive Ent
  | s | subj | obj | iSubj | iObj | gMasc | gFem | nSing | nPlur
  deriving DecidableEq, Fintype, Repr

/-- The model of a transitive clause whose subject is a masculine singular nonpronoun indexed
`iSubj` that locally o-commands the object. The object has the given sort, index, gender and
number. -/
@[reducible] def clause (objSort : Srt) (objIdx objGend objNum : Ent) : Interpretation sig Ent where
  S
    | .s => .sign
    | .subj => .npro
    | .obj => objSort
    | .iSubj | .iObj => .idx
    | .gMasc => .masc
    | .gFem => .fem
    | .nSing => .sing
    | .nPlur => .plur
  A
    | .SUBJ, .s => some .subj
    | .OBJ, .s => some .obj
    | .IDX, .subj => some .iSubj
    | .IDX, .obj => some objIdx
    | .GEND, .subj => some .gMasc
    | .GEND, .obj => some objGend
    | .NUM, .subj => some .nSing
    | .NUM, .obj => some objNum
    | _, _ => none
  R _ xs := xs 0 = .subj ∧ xs 1 = .obj

instance (objSort : Srt) (objIdx objGend objNum : Ent) (ρ : sig.Rel) :
    DecidablePred ((clause objSort objIdx objGend objNum).R ρ) :=
  fun xs ↦ inferInstanceAs (Decidable (xs 0 = .subj ∧ xs 1 = .obj))

/-- In *John likes himself* the anaphor is coindexed with the subject and agrees with it, so it
is locally o-bound. -/
example : (clause .ana .iSubj .gMasc .nSing).Models grammar := by decide

/-- In *John likes herself* the coindexed anaphor clashes with the subject in gender, so it is
locally o-commanded without being locally o-bound. -/
example : ¬ (clause .ana .iSubj .gFem .nSing).Models [principleA] := by decide

/-- A coindexed anaphor that clashes with the subject in number violates Principle A in the
same way. -/
example : ¬ (clause .ana .iSubj .gMasc .nPlur).Models [principleA] := by decide

/-- An anaphor with an index of its own is locally o-commanded but not coindexed, so it
violates Principle A. -/
example : ¬ (clause .ana .iObj .gMasc .nSing).Models [principleA] := by decide

/-- In *John likes him* with coindexation the pronoun is locally o-bound, so it violates
Principle B. -/
example : ¬ (clause .ppro .iSubj .gMasc .nSing).Models [principleB] := by decide

/-- A clause whose object has a species as its sort is well-typed, and one whose object has the
underspecified sort `synsem` is not. -/
example : (clause .ana .iSubj .gMasc .nSing).WellTyped ∧
    ¬ (clause .synsem .iSubj .gMasc .nSing).WellTyped := by decide

/-- The object, its index and its gender are components of the clause, and nothing is a
component of an index but the index itself. -/
example : (clause .ana .iSubj .gMasc .nSing).IsComponentOf .s .gMasc ∧
    ¬ (clause .ana .iSubj .gMasc .nSing).IsComponentOf .iSubj .s := by decide

end HPSG.RSRL.Binding
