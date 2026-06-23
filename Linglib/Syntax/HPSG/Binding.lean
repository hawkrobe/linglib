import Linglib.Syntax.HPSG.Description
import Mathlib.Tactic.DeriveFintype

/-!
# HPSG Binding Theory (Principles A & B) in RSRL
[pollard-sag-1994], [richter-2000], [muller-2024-binding]

The first *relational, quantified* HPSG principles in the RSRL substrate, exercising the
`rel`/`ex`/`all` machinery of `Description.lean`. Following HPSG Binding Theory
([muller-2024-binding], Ch. 20): **local o-command** ("less oblique, same ARG-ST", the
relation `locO`), **o-bind** (coindexed ∧ o-commands), **Principle A** (a locally o-commanded
anaphor is locally o-bound), **Principle B** (a pronoun is locally o-free).

Coindexation is **token identity** of `INDEX` (`pathEq`), the RSRL-faithful reading. ARG-ST is
modeled via `SUBJ`/`OBJ` attributes and `locO` interpreted per model (deriving `locO` from a
`FIRST`/`REST` list is a refinement). A bridge to the computational binding
(`Coreference.lean`, coindexation as `index : Option Nat` value equality) is deferred — the same
value-vs-token gap as the HFP bridge.
-/

namespace HPSG.Binding

open HPSG.RSRL

/-! ### Signature: nom-obj hierarchy, INDEX, and the o-command relation -/

/-- Sorts: a `sign`, `synsem` objects with the nom-obj species (`ana`/`ppro`/`npro`), and an
atomic `idx` (referential index). -/
inductive BSort | top | sign | synsem | ana | ppro | npro | idx
  deriving DecidableEq, Fintype, Repr

/-- Attributes: `SUBJ`/`OBJ` (a sign's arguments — a flattened ARG-ST) and `IDX` (a synsem's
referential index). -/
inductive BAttr | SUBJ | OBJ | IDX deriving DecidableEq, Fintype, Repr

/-- One relation: local o-command, `locO` (arity 2). -/
inductive BRel | locO deriving DecidableEq, Fintype, Repr

/-- Direct subsumption ("covers"): the DAG edges. The nom-obj species (`ana`/`ppro`/`npro`) cover
`synsem`; `sign`/`synsem`/`idx` cover `top`. The order is `ReflTransGen bCovers`. -/
def bCovers : BSort → BSort → Bool
  | .sign, .top => true
  | .synsem, .top => true
  | .idx, .top => true
  | .ana, .synsem => true
  | .ppro, .synsem => true
  | .npro, .synsem => true
  | _, _ => false

/-- Specificity depth; every covers edge strictly increases it (giving antisymmetry). -/
def bRank : BSort → Nat
  | .top => 0
  | .sign => 1 | .synsem => 1 | .idx => 1
  | .ana => 2 | .ppro => 2 | .npro => 2

instance : PartialOrder BSort :=
  partialOrderOfCovers (bCovers · · = true) bRank (by decide)

instance : DecidableLE BSort := fun a b =>
  decidableLEOfCovers (covers := (bCovers · · = true))
    [.top, .sign, .synsem, .ana, .ppro, .npro, .idx]
    (by decide) a b

/-- Appropriateness: a sign has `SUBJ`/`OBJ` synsems; every synsem species has an `IDX`. -/
def bapprop : BSort → BAttr → Option BSort
  | .sign, .SUBJ => some .synsem
  | .sign, .OBJ => some .synsem
  | .synsem, .IDX => some .idx
  | .ana, .IDX => some .idx
  | .ppro, .IDX => some .idx
  | .npro, .IDX => some .idx
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

/-- `y` locally o-binds `x`: `locO(y, x)` and they are coindexed. -/
def locallyOBinds (y x : Nat) : Desc bindingSig :=
  .and (.rel .locO [.var y, .var x]) (coindexed x y)

/-- **Principle A**: a locally o-commanded anaphor must be locally o-bound. -/
def principleA : Desc bindingSig :=
  .all 0 (.imp
    (.and (.sortAssign (.var 0) .ana) (.ex 1 (.rel .locO [.var 1, .var 0])))
    (.ex 1 (locallyOBinds 1 0)))

/-- **Principle B**: a personal pronoun must be locally o-free — no component locally o-binds
it. -/
def principleB : Desc bindingSig :=
  .all 0 (.imp (.sortAssign (.var 0) .ppro)
    (.neg (.ex 1 (locallyOBinds 1 0))))

/-- The binding fragment's grammar. -/
def bindingGrammar : Grammar bindingSig := [principleA, principleB]

/-! ### Worked models

One transitive-clause carrier and one builder `clause`; the three binding configurations are
instantiations differing only in the object's sort and index. -/

/-- Entities of a transitive clause: the verb sign, subject, object, and two indices. -/
inductive BindEnt | s | subj | obj | i1 | i2 deriving DecidableEq, Fintype, Repr

/-- A transitive clause "`subj` V `obj`": the subject is an `npro` indexed `i1` and locally
o-commands the object; the object has sort `objSort` and index `objIdx`. Coindexation is
`objIdx = i1`. -/
@[reducible] def clause (objSort : BSort) (objIdx : BindEnt) : Interpretation bindingSig where
  U := BindEnt
  S := fun
    | .s => .sign
    | .subj => .npro
    | .obj => objSort
    | .i1 => .idx
    | .i2 => .idx
  A := fun a u => match a, u with
    | .SUBJ, .s => some .subj
    | .OBJ, .s => some .obj
    | .IDX, .subj => some .i1
    | .IDX, .obj => some objIdx
    | _, _ => none
  R := fun _ args => args = [BindEnt.subj, BindEnt.obj]

instance (objSort : BSort) (objIdx : BindEnt) (ρ : bindingSig.Rel) :
    DecidablePred ((clause objSort objIdx).R ρ) :=
  fun args => inferInstanceAs (Decidable (args = [BindEnt.subj, BindEnt.obj]))

/-- *Mary likes herself*: a coindexed anaphor object (`objIdx = i1`) is locally o-bound by the
subject — Principle A satisfied, and the whole grammar (Principle B vacuous: no pronoun). -/
example : (clause .ana .i1).Models bindingGrammar := by decide

/-- *Mary likes himself* (gender clash): the anaphor object has a *distinct* index (`i2`), so it
is locally o-commanded but not locally o-bound — Principle A violated (a genuine filter). -/
example : ¬ (clause .ana .i2).Models [principleA] := by decide

/-- *Mary likes her_i* coindexed: a coindexed pronoun object is locally o-bound, so not locally
o-free — Principle B violated. -/
example : ¬ (clause .ppro .i1).Models [principleB] := by decide

end HPSG.Binding
