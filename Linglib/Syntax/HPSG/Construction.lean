/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.HPSG.Description
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false

/-!
# The filler-head construction in RSRL
[sag-2010] [sag-2012] [richter-2000] [carpenter-1992]

The Sign-Based Construction Grammar filler-head construction, formalized properly on the RSRL
feature-structure substrate (`Syntax/HPSG/{Signature,Interpretation,Description}`), the same way
`Model.lean` formalizes the Head Feature Principle. A construction is a **constraint** (a `Desc`
implication on a `construct` feature structure), not a category lattice. The filler-head
construction's content — which an ad-hoc per-position category bundle cannot express — is:

* the filler daughter is `[CAT nonverbal]` and the head daughter is `[CAT verbal]` ([sag-2010] (25),
  (61)), as **subsumption** constraints over a category type hierarchy (so "NP or PP" is the type
  `nominal`, [sag-2010] (92), not a powerset disjunction);
* the filler–gap dependency is **token identity** (`pathEq`) between the filler daughter's category
  and the head daughter's `GAP` value — the structure sharing (the boxed tags) that *is* the
  construction, [sag-2010] (61).

Two worked constructs show the principle filters: a well-formed one (nonverbal filler, verbal head,
GAP token-shared with the filler) satisfies it; one with a mismatched GAP and one with a verbal
filler each violate it.

## Scope

`GAP` is modeled as a single category (single-gap), not the HPSG list; the full sign feature geometry
(SEM composition, WH/REL/IC/INV/VFORM), n-ary `DTRS`, and the cross-classifying construction type
hierarchy (`interrogative-cl` etc.) are deferred. This is the filler-head supertype only.
-/

namespace HPSG.Construction

open HPSG.RSRL

/-! ### Sorts: a category type hierarchy plus signs and constructs

`nonverbal` resolves to `nominal`/`adj`/`adv`; `nominal` to `noun`/`prep` (so "NP or PP" is the type
`nominal`, [sag-2010] (92)); `verbal` to `verb`/`comp`. -/

/-- Sorts of the fragment: the category hierarchy, plus `sign`, `construct`, and the
`fillerHeadCxt` construction type. -/
inductive FHSort
  | top
  | cat | verbal | nonverbal | nominal | verb | comp | noun | prep | adj | adv
  | sign | construct | fillerHeadCxt
  deriving DecidableEq, Fintype, Repr

/-- Subsumption (`fhLe a b` = "`a` at least as specific as `b`"), transitively closed. -/
def fhLe : FHSort → FHSort → Bool
  | _, .top => true
  | .verbal, .cat => true
  | .nonverbal, .cat => true
  | .verb, .verbal => true | .verb, .cat => true
  | .comp, .verbal => true | .comp, .cat => true
  | .nominal, .nonverbal => true | .nominal, .cat => true
  | .adj, .nonverbal => true | .adj, .cat => true
  | .adv, .nonverbal => true | .adv, .cat => true
  | .noun, .nominal => true | .noun, .nonverbal => true | .noun, .cat => true
  | .prep, .nominal => true | .prep, .nonverbal => true | .prep, .cat => true
  | .fillerHeadCxt, .construct => true
  | a, b => decide (a = b)

instance : PartialOrder FHSort :=
  partialOrderOfBool fhLe (by decide) (by decide) (by decide)

instance : DecidableLE FHSort := fun a b => inferInstanceAs (Decidable (fhLe a b = true))

/-! ### Attributes and the signature -/

/-- Attributes: a construct's daughters (`MTR`, `HDDTR`, `FILLERDTR`); a sign's `CAT` and (single)
`GAP` category. -/
inductive FHAttr
  | MTR | HDDTR | FILLERDTR | CAT | GAP
  deriving DecidableEq, Fintype, Repr

/-- Appropriateness: constructs have the three daughter attributes (value `sign`); signs have `CAT`
and `GAP` (value `cat`); categories are attributeless. -/
def fhApprop : FHSort → FHAttr → Option FHSort
  | .construct, .MTR => some .sign
  | .construct, .HDDTR => some .sign
  | .construct, .FILLERDTR => some .sign
  | .fillerHeadCxt, .MTR => some .sign
  | .fillerHeadCxt, .HDDTR => some .sign
  | .fillerHeadCxt, .FILLERDTR => some .sign
  | .sign, .CAT => some .cat
  | .sign, .GAP => some .cat
  | _, _ => none

private theorem fhApprop_inh : ∀ (σ₁ σ₂ : FHSort) (α : FHAttr) (τ₁ : FHSort),
    σ₂ ≤ σ₁ → fhApprop σ₁ α = some τ₁ → ∃ τ₂, fhApprop σ₂ α = some τ₂ ∧ τ₂ ≤ τ₁ := by decide

/-- The filler-head fragment's signature (no relations). -/
@[reducible] def fhSig : Signature FHSort where
  Attr := FHAttr
  Rel := Empty
  arity := fun e => e.elim
  approp := fhApprop
  approp_inherits := fun {σ₁ σ₂ α τ₁} => fhApprop_inh σ₁ σ₂ α τ₁

instance (I : Interpretation fhSig) : ∀ ρ, DecidablePred (I.R ρ) := fun ρ => nomatch ρ

/-! ### The filler-head construction as a principle

`fillerHeadCxt ⇒ FILLERDTR is [CAT nonverbal] ∧ HDDTR is [CAT verbal] ∧ FILLERDTR's CAT is
token-identical to HDDTR's GAP`. The last conjunct (`pathEq`) is the filler–gap dependency — the
structure sharing that distinguishes a filler-head construct from an arbitrary binary phrase. -/
def fillerHead : Desc fhSig :=
  .imp (.sortAssign .colon .fillerHeadCxt)
    (.and (.sortAssign (.path [.FILLERDTR, .CAT]) .nonverbal)
      (.and (.sortAssign (.path [.HDDTR, .CAT]) .verbal)
        (.pathEq (.path [.FILLERDTR, .CAT]) (.path [.HDDTR, .GAP]))))

/-- The one-principle grammar. -/
def fhGrammar : Grammar fhSig := [fillerHead]

/-! ### Worked constructs (entities: the construct, its two daughters, two category objects) -/

/-- Entities of a worked filler-head construct. -/
inductive Ent
  | cxt | head | filler | npCat | vpCat
  deriving DecidableEq, Fintype, Repr

/-- A well-formed filler-head construct: a nonverbal (`noun`) filler, a verbal (`verb`) head, and the
head's `GAP` pointing at the *same* category object as the filler's `CAT` — token identity. -/
def goodModel : Interpretation fhSig where
  U := Ent
  S := fun
    | .cxt => .fillerHeadCxt
    | .head => .sign
    | .filler => .sign
    | .npCat => .noun
    | .vpCat => .verb
  A := fun a u => match a, u with
    | .HDDTR, .cxt => some .head
    | .FILLERDTR, .cxt => some .filler
    | .CAT, .filler => some .npCat
    | .CAT, .head => some .vpCat
    | .GAP, .head => some .npCat   -- token-identical to the filler's CAT
    | _, _ => none
  R := fun e => e.elim

instance : Fintype goodModel.U := inferInstanceAs (Fintype Ent)
instance : DecidableEq goodModel.U := inferInstanceAs (DecidableEq Ent)

/-- The well-formed construct satisfies the filler-head construction. -/
example : goodModel.Models fhGrammar := by decide

/-- An ill-formed construct: the head's `GAP` is a *different* object (`vpCat`) from the filler's
`CAT`, so the token-identity (filler–gap) conjunct fails — the gap is not filled by the filler. -/
def gapMismatchModel : Interpretation fhSig where
  U := Ent
  S := fun
    | .cxt => .fillerHeadCxt
    | .head => .sign
    | .filler => .sign
    | .npCat => .noun
    | .vpCat => .verb
  A := fun a u => match a, u with
    | .HDDTR, .cxt => some .head
    | .FILLERDTR, .cxt => some .filler
    | .CAT, .filler => some .npCat
    | .CAT, .head => some .vpCat
    | .GAP, .head => some .vpCat    -- ≠ the filler's CAT: the filler–gap link is broken
    | _, _ => none
  R := fun e => e.elim

instance : Fintype gapMismatchModel.U := inferInstanceAs (Fintype Ent)
instance : DecidableEq gapMismatchModel.U := inferInstanceAs (DecidableEq Ent)

/-- The gap-mismatch construct violates the filler-head construction — `pathEq` genuinely filters. -/
example : ¬ gapMismatchModel.Models fhGrammar := by decide

/-- An ill-formed construct: the filler daughter is `verb` (verbal), not nonverbal, so the
`[CAT nonverbal]` conjunct fails. -/
def verbalFillerModel : Interpretation fhSig where
  U := Ent
  S := fun
    | .cxt => .fillerHeadCxt
    | .head => .sign
    | .filler => .sign
    | .npCat => .verb       -- the filler's category is verbal — a category violation
    | .vpCat => .verb
  A := fun a u => match a, u with
    | .HDDTR, .cxt => some .head
    | .FILLERDTR, .cxt => some .filler
    | .CAT, .filler => some .npCat
    | .CAT, .head => some .vpCat
    | .GAP, .head => some .npCat
    | _, _ => none
  R := fun e => e.elim

instance : Fintype verbalFillerModel.U := inferInstanceAs (Fintype Ent)
instance : DecidableEq verbalFillerModel.U := inferInstanceAs (DecidableEq Ent)

/-- The verbal-filler construct violates the filler-head construction — `[CAT nonverbal]` filters. -/
example : ¬ verbalFillerModel.Models fhGrammar := by decide

end HPSG.Construction
