/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.HPSG.Description
import Mathlib.Tactic.DeriveFintype


/-!
# HPSG Binding Theory (Principles A & B) in RSRL, with φ-agreement
[pollard-sag-1994], [richter-2000], [muller-2024-binding]

The *relational, quantified* HPSG binding principles in the RSRL substrate, exercising the
`rel`/`ex`/`all` machinery of `Description.lean`. Following HPSG Binding Theory
([muller-2024-binding], Ch. 20): **local o-command** ("less oblique, same ARG-ST", the relation
`locO`), **o-bind** (coindexed ∧ o-commands ∧ **agrees in φ**), **Principle A** (a locally o-commanded
anaphor is locally o-bound), **Principle B** (a pronoun is locally o-free).

Coindexation is **token identity** of `INDEX` (`pathEq`). Binding additionally requires **φ-agreement**
(`GEND`/`NUM` token-identical between binder and bindee) — so a *coindexed but φ-clashing* anaphor (*John
likes herself*, gender; *they like himself*, number) is **not** bound and Principle A is violated. This
is the model-theoretic counterpart of the neutral binding engine's `Word.Agree` check
(`Syntax/Binding/Basic`), against which `Studies/SagWasowBender2003` cross-checks.

ARG-ST is modeled via `SUBJ`/`OBJ` attributes and `locO` interpreted per model.
-/

namespace HPSG.RSRL.Binding


/-! ### Signature: nom-obj hierarchy, INDEX, φ-features, and the o-command relation -/

/-- Sorts: a `sign`, `synsem` objects with the nom-obj species (`ana`/`ppro`/`npro`), an atomic `idx`
(referential index), and the φ-value hierarchies `gender > {masc, fem}` and `number > {sing, plur}`. -/
inductive BSort
  | top | sign | synsem | ana | ppro | npro | idx
  | gender | masc | fem | number | sing | plur
  deriving DecidableEq, Fintype, Repr

/-- Attributes: `SUBJ`/`OBJ` (a sign's arguments — a flattened ARG-ST), `IDX` (a synsem's referential
index), and the φ-features `GEND`/`NUM`. -/
inductive BAttr | SUBJ | OBJ | IDX | GEND | NUM deriving DecidableEq, Fintype, Repr

/-- One relation: local o-command, `locO` (arity 2). -/
inductive BRel | locO deriving DecidableEq, Fintype, Repr

/-- Direct subsumption ("covers"): the DAG edges. Nom-obj species cover `synsem`; gender/number values
cover their φ root; `sign`/`synsem`/`idx`/`gender`/`number` cover `top`. -/
def bCovers : BSort → BSort → Bool
  | .sign, .top => true
  | .synsem, .top => true
  | .idx, .top => true
  | .gender, .top => true
  | .number, .top => true
  | .ana, .synsem => true
  | .ppro, .synsem => true
  | .npro, .synsem => true
  | .masc, .gender => true
  | .fem, .gender => true
  | .sing, .number => true
  | .plur, .number => true
  | _, _ => false

/-- Specificity depth; every covers edge strictly increases it (giving antisymmetry). -/
def bRank : BSort → Nat
  | .top => 0
  | .sign => 1 | .synsem => 1 | .idx => 1 | .gender => 1 | .number => 1
  | .ana => 2 | .ppro => 2 | .npro => 2 | .masc => 2 | .fem => 2 | .sing => 2 | .plur => 2

instance : PartialOrder BSort :=
  partialOrderOfCovers (bCovers · · = true) bRank (by decide)

instance : DecidableLE BSort := fun a b =>
  decidableLEOfCovers (covers := (bCovers · · = true))
    [.top, .sign, .synsem, .ana, .ppro, .npro, .idx, .gender, .masc, .fem, .number, .sing, .plur]
    (by decide) a b

/-- Appropriateness: a sign has `SUBJ`/`OBJ` synsems; every synsem species has an `IDX`, a `GEND`, and
a `NUM`. -/
def bapprop : BSort → BAttr → Option BSort
  | .sign, .SUBJ => some .synsem
  | .sign, .OBJ => some .synsem
  | .synsem, .IDX => some .idx
  | .ana, .IDX => some .idx
  | .ppro, .IDX => some .idx
  | .npro, .IDX => some .idx
  | .synsem, .GEND => some .gender
  | .ana, .GEND => some .gender
  | .ppro, .GEND => some .gender
  | .npro, .GEND => some .gender
  | .synsem, .NUM => some .number
  | .ana, .NUM => some .number
  | .ppro, .NUM => some .number
  | .npro, .NUM => some .number
  | _, _ => none

private theorem bapprop_inh : ∀ (σ₁ σ₂ : BSort) (α : BAttr) (τ₁ : BSort),
    σ₂ ≤ σ₁ → bapprop σ₁ α = some τ₁ → ∃ τ₂, bapprop σ₂ α = some τ₂ ∧ τ₂ ≤ τ₁ := by decide

@[reducible] def bindingSig : Signature BSort where
  Attr := BAttr
  Rel := BRel
  arity := fun _ => 2
  approp := bapprop
  approp_inherits := fun {σ₁ σ₂ α τ₁} => bapprop_inh σ₁ σ₂ α τ₁

/-! ### Principles A and B as descriptions

Variable `0` is the bound synsem `x`; `1` is the candidate binder `y`. -/

/-- Coindexation of the entities at variables `x` and `y`: token identity of their `INDEX`. -/
def coindexed (x y : Nat) : Desc bindingSig :=
  .pathEq (.feat (.var x) .IDX) (.feat (.var y) .IDX)

/-- **φ-agreement** of `x` and `y`: token identity of their `GEND` and `NUM` (HPSG agreement as
re-entrancy). -/
def agrees (x y : Nat) : Desc bindingSig :=
  .and (.pathEq (.feat (.var x) .GEND) (.feat (.var y) .GEND))
       (.pathEq (.feat (.var x) .NUM) (.feat (.var y) .NUM))

/-- `y` locally o-binds `x`: `locO(y, x)`, coindexed, **and agreeing in φ**. -/
def locallyOBinds (y x : Nat) : Desc bindingSig :=
  .and (.rel .locO [.var y, .var x]) (.and (coindexed x y) (agrees x y))

/-- **Principle A**: a locally o-commanded anaphor must be locally o-bound. -/
def principleA : Desc bindingSig :=
  .all 0 (.imp
    (.and (.sortAssign (.var 0) .ana) (.ex 1 (.rel .locO [.var 1, .var 0])))
    (.ex 1 (locallyOBinds 1 0)))

/-- **Principle B**: a personal pronoun must be locally o-free — no component locally o-binds it. -/
def principleB : Desc bindingSig :=
  .all 0 (.imp (.sortAssign (.var 0) .ppro)
    (.neg (.ex 1 (locallyOBinds 1 0))))

/-- The binding fragment's grammar. -/
def bindingGrammar : Grammar bindingSig := [principleA, principleB]

/-! ### Worked models

One transitive-clause carrier and one builder `clause`; the binding configurations are instantiations
differing in the object's sort, index, and φ-features. The subject is a masculine-singular `npro`
indexed `iSubj`. -/

/-- Entities of a transitive clause: verb sign, subject, object, two indices, and the gender/number
value objects (`gMasc`/`gFem`, `nSing`/`nPlur`). -/
inductive BindEnt
  | s | subj | obj | iSubj | iObj | gMasc | gFem | nSing | nPlur
  deriving DecidableEq, Fintype, Repr

/-- A transitive clause "`subj` V `obj`": the subject is a masc-sing `npro` indexed `iSubj` and locally
o-commands the object; the object has sort `objSort`, index `objIdx`, gender `objGend`, number `objNum`.
Coindexation is `objIdx = iSubj`; agreement is `objGend = gMasc ∧ objNum = nSing`. -/
@[reducible] def clause (objSort : BSort) (objIdx objGend objNum : BindEnt) :
    Interpretation bindingSig where
  U := BindEnt
  S := fun
    | .s => .sign
    | .subj => .npro
    | .obj => objSort
    | .iSubj => .idx
    | .iObj => .idx
    | .gMasc => .masc
    | .gFem => .fem
    | .nSing => .sing
    | .nPlur => .plur
  A := fun a u => match a, u with
    | .SUBJ, .s => some .subj
    | .OBJ, .s => some .obj
    | .IDX, .subj => some .iSubj
    | .IDX, .obj => some objIdx
    | .GEND, .subj => some .gMasc
    | .GEND, .obj => some objGend
    | .NUM, .subj => some .nSing
    | .NUM, .obj => some objNum
    | _, _ => none
  R := fun _ args => args = [BindEnt.subj, BindEnt.obj]

instance (objSort : BSort) (objIdx objGend objNum : BindEnt) (ρ : bindingSig.Rel) :
    DecidablePred ((clause objSort objIdx objGend objNum).R ρ) :=
  fun args => inferInstanceAs (Decidable (args = [BindEnt.subj, BindEnt.obj]))

/-- *John likes himself*: a coindexed, φ-agreeing anaphor (masc-sing, like the subject) is locally
o-bound — Principle A satisfied (Principle B vacuous: no pronoun). -/
example : (clause .ana .iSubj .gMasc .nSing).Models bindingGrammar := by decide

/-- *John likes herself* (**gender clash**): a coindexed anaphor whose `GEND` is feminine disagrees with
the masculine subject, so it is locally o-commanded but not locally o-*bound* — Principle A violated. -/
example : ¬ (clause .ana .iSubj .gFem .nSing).Models [principleA] := by decide

/-- *They like himself* (**number clash**): a coindexed anaphor whose `NUM` is singular disagrees with
the (here plural-construed) subject's number — Principle A violated on agreement. -/
example : ¬ (clause .ana .iSubj .gMasc .nPlur).Models [principleA] := by decide

/-- *Himself likes John* (**structural**): a disjoint-indexed anaphor (`objIdx = iObj`) is locally
o-commanded but not coindexed, so not locally o-bound — Principle A violated. -/
example : ¬ (clause .ana .iObj .gMasc .nSing).Models [principleA] := by decide

/-- *John likes him_i* coindexed: a coindexed, agreeing pronoun is locally o-bound, so not locally
o-free — Principle B violated. -/
example : ¬ (clause .ppro .iSubj .gMasc .nSing).Models [principleB] := by decide

end HPSG.RSRL.Binding
