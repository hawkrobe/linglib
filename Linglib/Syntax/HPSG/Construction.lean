/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.HPSG.Description
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false

/-!
# The SBCG construct type hierarchy in RSRL
[sag-2010] [sag-etal-2020] [sag-2012] [richter-2000] [richter-2024]

The Sign-Based Construction Grammar **construct type hierarchy with monotonic multiple inheritance**,
formalized on the RSRL feature-structure substrate (`Syntax/HPSG/{Signature,Interpretation,
Description}`). A construction is a constraint `τ ⇒ D` ([sag-2012] (44)) on a `construct = [MTR, DTRS]`
([sag-2012] (46)); inheritance is the **sort order plus the implication semantics** — a construct
whose sort sits below several supersorts satisfies *all* their principles, with no per-construction
restatement. This is exactly the monotonic (no-overriding) inheritance SBCG commits to ([sag-2012]
fn. 17; [sag-etal-2020]'s "category restriction operation").

The hierarchy is the authoritative two-dimensional one of [sag-etal-2020] (Figs. 6–7):

* **construct backbone** (Fig. 6): `construct > {phrasal-cxt, lexical-cxt}`;
  `phrasal-cxt > {headed-cxt, clause}`;
  `headed-cxt > {head-filler-cxt, subject-head-cxt, aux-initial-cxt, …}`;
* **clausal dimension** (Fig. 7): `clause > {core-cl, relative-cl}`;
  `core-cl > {declarative-cl, interrogative-cl, exclamative-cl}`.

The **cross-classification** (Fig. 5) is a lower bound across the two dimensions: [sag-2010]'s
nonsubject wh-interrogative `ns-wh-int-cl` is a subtype of *both* `head-filler-cxt` (headed dim.) and
`interrogative-cl` (clausal dim.), so it inherits the filler-head constraints (head verbal, filler
nonverbal, filler↔gap token identity) **and** the interrogative semantics (`MTR` `SEM` a question) from
one sort assignment — the keystone theorem below.

## Scope

This file establishes the hierarchy and the `ns-wh-int-cl` cross-classification keystone. The full five
filler-gap constructions ([sag-2010]) and the inversion construction (`aux-initial-cxt`, [sag-etal-2020]
(39)) are paper-anchored consumers built on this substrate; n-ary `DTRS`, GAP amalgamation, islands,
and compositional `SEM` are deferred. Decidability stays inside `Models` over fixed finite
interpretations (Kepser 2004: full RSRL model-checking is undecidable).
-/

namespace HPSG.Construction

open HPSG.RSRL

/-! ### Sorts: categories, semantic types, signs, and the construct/clausal hierarchy -/

/-- Sorts of the fragment: a category hierarchy, a semantic-type hierarchy, `sign`, and the
[sag-etal-2020] construct (Fig. 6) and clausal (Fig. 7) type hierarchies, with `ns-wh-int-cl` as the
worked cross-classified subtype (Fig. 5). -/
inductive FHSort
  | top
  -- category hierarchy (head-filler-cxt keys on verbal/nonverbal)
  | cat | verbal | nonverbal | verb | noun
  -- semantic-type hierarchy (clause types key on the MTR's SEM type)
  | semType | austinean | question | fact | proposition
  -- signs
  | sign
  -- construct backbone (Fig. 6)
  | construct | phrasalCxt | lexicalCxt | headedCxt | clause | headFillerCxt
  -- clausal hierarchy (Fig. 7)
  | coreCl | relativeCl | declarativeCl | interrogativeCl | exclamativeCl
  -- the cross-classified construct (Fig. 5): < head-filler-cxt AND < interrogative-cl
  | nsWhIntCl
  deriving DecidableEq, Fintype, Repr

/-- Subsumption (`fhLe a b` = "`a` at least as specific as `b`"), transitively closed. The two arms
for `nsWhIntCl` — below both `headFillerCxt` and `interrogativeCl` — are the multiple inheritance. -/
def fhLe : FHSort → FHSort → Bool
  | _, .top => true
  -- categories
  | .verbal, .cat => true
  | .nonverbal, .cat => true
  | .verb, .verbal => true | .verb, .cat => true
  | .noun, .nonverbal => true | .noun, .cat => true
  -- semantic types
  | .austinean, .semType => true
  | .question, .semType => true
  | .fact, .semType => true
  | .proposition, .semType => true
  -- construct backbone
  | .phrasalCxt, .construct => true
  | .lexicalCxt, .construct => true
  | .headedCxt, .phrasalCxt => true | .headedCxt, .construct => true
  | .clause, .phrasalCxt => true | .clause, .construct => true
  | .headFillerCxt, .headedCxt => true | .headFillerCxt, .phrasalCxt => true
  | .headFillerCxt, .construct => true
  -- clausal
  | .coreCl, .clause => true | .coreCl, .phrasalCxt => true | .coreCl, .construct => true
  | .relativeCl, .clause => true | .relativeCl, .phrasalCxt => true | .relativeCl, .construct => true
  | .declarativeCl, .coreCl => true | .declarativeCl, .clause => true
  | .declarativeCl, .phrasalCxt => true | .declarativeCl, .construct => true
  | .interrogativeCl, .coreCl => true | .interrogativeCl, .clause => true
  | .interrogativeCl, .phrasalCxt => true | .interrogativeCl, .construct => true
  | .exclamativeCl, .coreCl => true | .exclamativeCl, .clause => true
  | .exclamativeCl, .phrasalCxt => true | .exclamativeCl, .construct => true
  -- cross-classified: ns-wh-int-cl < head-filler-cxt (headed dim.) AND < interrogative-cl (clausal)
  | .nsWhIntCl, .headFillerCxt => true | .nsWhIntCl, .headedCxt => true
  | .nsWhIntCl, .interrogativeCl => true | .nsWhIntCl, .coreCl => true
  | .nsWhIntCl, .clause => true | .nsWhIntCl, .phrasalCxt => true | .nsWhIntCl, .construct => true
  | a, b => decide (a = b)

instance : PartialOrder FHSort :=
  partialOrderOfBool fhLe (by decide) (by decide) (by decide)

instance : DecidableLE FHSort := fun a b => inferInstanceAs (Decidable (fhLe a b = true))

/-! ### Attributes and the signature -/

/-- Attributes: a construct's mother (`MTR`) and head/filler daughters (`HDDTR`/`FILLERDTR`); a sign's
`CAT`, (single) `GAP` category, and `SEM` type. -/
inductive FHAttr
  | MTR | HDDTR | FILLERDTR | CAT | GAP | SEM
  deriving DecidableEq, Fintype, Repr

/-- Appropriateness: every construct has a `MTR` (a sign); `headed-cxt` and its subtypes additionally
have `HDDTR`/`FILLERDTR`; a `sign` has `CAT`/`GAP` (categories) and `SEM` (a semantic type). Respects
feature inheritance ([richter-2024]): an attribute appropriate to a sort is appropriate to its
subsorts (so `ns-wh-int-cl`, below `headed-cxt`, has daughters, and below `interrogative-cl`, a
mother). -/
def fhApprop : FHSort → FHAttr → Option FHSort
  | .construct, .MTR => some .sign
  | .phrasalCxt, .MTR => some .sign
  | .lexicalCxt, .MTR => some .sign
  | .headedCxt, .MTR => some .sign
  | .clause, .MTR => some .sign
  | .headFillerCxt, .MTR => some .sign
  | .coreCl, .MTR => some .sign
  | .relativeCl, .MTR => some .sign
  | .declarativeCl, .MTR => some .sign
  | .interrogativeCl, .MTR => some .sign
  | .exclamativeCl, .MTR => some .sign
  | .nsWhIntCl, .MTR => some .sign
  | .headedCxt, .HDDTR => some .sign
  | .headedCxt, .FILLERDTR => some .sign
  | .headFillerCxt, .HDDTR => some .sign
  | .headFillerCxt, .FILLERDTR => some .sign
  | .nsWhIntCl, .HDDTR => some .sign
  | .nsWhIntCl, .FILLERDTR => some .sign
  | .sign, .CAT => some .cat
  | .sign, .GAP => some .cat
  | .sign, .SEM => some .semType
  | _, _ => none

private theorem fhApprop_inh : ∀ (σ₁ σ₂ : FHSort) (α : FHAttr) (τ₁ : FHSort),
    σ₂ ≤ σ₁ → fhApprop σ₁ α = some τ₁ → ∃ τ₂, fhApprop σ₂ α = some τ₂ ∧ τ₂ ≤ τ₁ := by decide

/-- The fragment's signature (no relations). -/
@[reducible] def fhSig : Signature FHSort where
  Attr := FHAttr
  Rel := Empty
  arity := fun e => e.elim
  approp := fhApprop
  approp_inherits := fun {σ₁ σ₂ α τ₁} => fhApprop_inh σ₁ σ₂ α τ₁

instance (I : Interpretation fhSig) : ∀ ρ, DecidablePred (I.R ρ) := fun ρ => nomatch ρ

/-! ### Principles (constructions as `τ ⇒ D`)

Each principle constrains every feature structure whose sort is `≤` its antecedent — so a construct
inherits a principle exactly when its sort sits below the principle's type. -/

/-- The **filler-head construction** ([sag-2010] (61), [sag-etal-2020] Fig. 6): the filler daughter is
`[CAT nonverbal]`, the head daughter is `[CAT verbal]`, and the filler's category is **token-identical**
(`pathEq`) to the head daughter's `GAP` value — the filler-gap structure sharing. -/
def headFillerPrinciple : Desc fhSig :=
  .imp (.sortAssign .colon .headFillerCxt)
    (.and (.sortAssign (.path [.FILLERDTR, .CAT]) .nonverbal)
      (.and (.sortAssign (.path [.HDDTR, .CAT]) .verbal)
        (.pathEq (.path [.FILLERDTR, .CAT]) (.path [.HDDTR, .GAP]))))

/-- Clausal semantics ([sag-etal-2020] Fig. 7, following G&S 2000): the mother's `SEM` type is fixed
by the clausal type — `declarative-cl` ⇒ austinean, `interrogative-cl` ⇒ question,
`exclamative-cl` ⇒ fact, `relative-cl` ⇒ proposition. -/
def declarativePrinciple : Desc fhSig :=
  .imp (.sortAssign .colon .declarativeCl) (.sortAssign (.path [.MTR, .SEM]) .austinean)
def interrogativePrinciple : Desc fhSig :=
  .imp (.sortAssign .colon .interrogativeCl) (.sortAssign (.path [.MTR, .SEM]) .question)
def exclamativePrinciple : Desc fhSig :=
  .imp (.sortAssign .colon .exclamativeCl) (.sortAssign (.path [.MTR, .SEM]) .fact)
def relativePrinciple : Desc fhSig :=
  .imp (.sortAssign .colon .relativeCl) (.sortAssign (.path [.MTR, .SEM]) .proposition)

/-- The grammar: the filler-head construction and the four clausal-type principles. -/
def fhGrammar : Grammar fhSig :=
  [headFillerPrinciple, declarativePrinciple, interrogativePrinciple, exclamativePrinciple,
    relativePrinciple]

/-! ### Multiple inheritance: `ns-wh-int-cl` is a lower bound across the two dimensions -/

/-- `ns-wh-int-cl` sits below **both** `head-filler-cxt` (the headed dimension) and `interrogative-cl`
(the clausal dimension) — the cross-classification of [sag-2010] (80) / [sag-etal-2020] Fig. 5. -/
theorem nsWhIntCl_inherits :
    (FHSort.nsWhIntCl ≤ .headFillerCxt) ∧ (FHSort.nsWhIntCl ≤ .interrogativeCl) := by decide

/-! ### Worked constructs -/

/-- Entities shared by the worked constructs: the construct, its mother and two daughters, two
category objects, and one semantic object. -/
inductive Ent
  | cxt | mtr | hd | fl | npCat | vpCat | sem
  deriving DecidableEq, Fintype, Repr

/-- A well-formed filler-head construct (sort `head-filler-cxt`): nonverbal filler, verbal head, and
the head's `GAP` token-identical to the filler's `CAT`. -/
def goodFillerHead : Interpretation fhSig where
  U := Ent
  S := fun
    | .cxt => .headFillerCxt
    | .hd => .sign
    | .fl => .sign
    | .npCat => .noun
    | .vpCat => .verb
    | .mtr => .sign
    | .sem => .semType
  A := fun a u => match a, u with
    | .HDDTR, .cxt => some .hd
    | .FILLERDTR, .cxt => some .fl
    | .CAT, .fl => some .npCat
    | .CAT, .hd => some .vpCat
    | .GAP, .hd => some .npCat
    | _, _ => none
  R := fun e => e.elim

instance : Fintype goodFillerHead.U := inferInstanceAs (Fintype Ent)
instance : DecidableEq goodFillerHead.U := inferInstanceAs (DecidableEq Ent)

/-- The well-formed filler-head construct satisfies the grammar (the clausal principles are vacuous —
`head-filler-cxt` is not below any clausal type). -/
example : goodFillerHead.Models fhGrammar := by decide

/-- Breaking the filler↔gap token identity (head `GAP` ≠ filler `CAT`) violates the filler-head
principle. -/
def gapMismatch : Interpretation fhSig where
  U := Ent
  S := goodFillerHead.S
  A := fun a u => match a, u with
    | .HDDTR, .cxt => some .hd
    | .FILLERDTR, .cxt => some .fl
    | .CAT, .fl => some .npCat
    | .CAT, .hd => some .vpCat
    | .GAP, .hd => some .vpCat    -- ≠ filler's CAT
    | _, _ => none
  R := fun e => e.elim

instance : Fintype gapMismatch.U := inferInstanceAs (Fintype Ent)
instance : DecidableEq gapMismatch.U := inferInstanceAs (DecidableEq Ent)

example : ¬ gapMismatch.Models fhGrammar := by decide

/-! ### The keystone: cross-classification by inheritance

A single `ns-wh-int-cl` construct satisfies the filler-head principle **and** the interrogative
principle — both inherited via `nsWhIntCl_inherits`, neither stipulated on `ns-wh-int-cl`. -/

/-- A well-formed nonsubject wh-interrogative construct (sort `ns-wh-int-cl`): nonverbal filler,
verbal head, filler↔gap token identity (from `head-filler-cxt`), and the mother's `SEM` a question
(from `interrogative-cl`). -/
def goodNsWhInt : Interpretation fhSig where
  U := Ent
  S := fun
    | .cxt => .nsWhIntCl
    | .mtr => .sign
    | .hd => .sign
    | .fl => .sign
    | .npCat => .noun
    | .vpCat => .verb
    | .sem => .question
  A := fun a u => match a, u with
    | .MTR, .cxt => some .mtr
    | .HDDTR, .cxt => some .hd
    | .FILLERDTR, .cxt => some .fl
    | .SEM, .mtr => some .sem
    | .CAT, .fl => some .npCat
    | .CAT, .hd => some .vpCat
    | .GAP, .hd => some .npCat
    | _, _ => none
  R := fun e => e.elim

instance : Fintype goodNsWhInt.U := inferInstanceAs (Fintype Ent)
instance : DecidableEq goodNsWhInt.U := inferInstanceAs (DecidableEq Ent)

/-- **Keystone.** The `ns-wh-int-cl` construct satisfies the whole grammar — in particular both the
inherited filler-head constraints and the inherited interrogative semantics, from its single sort
assignment (`nsWhIntCl_inherits`). No filler-head or interrogative constraint is restated on
`ns-wh-int-cl`; both fire because its sort lies below both supersorts. -/
example : goodNsWhInt.Models fhGrammar := by decide

/-- The inherited interrogative constraint genuinely binds: an `ns-wh-int-cl` construct whose mother's
`SEM` is austinean (not a question) violates the **inherited** interrogative principle — even though
nothing about interrogativity is stated on `ns-wh-int-cl` directly. -/
def nsWhIntWrongSem : Interpretation fhSig where
  U := Ent
  S := fun
    | .cxt => .nsWhIntCl
    | .mtr => .sign
    | .hd => .sign
    | .fl => .sign
    | .npCat => .noun
    | .vpCat => .verb
    | .sem => .austinean    -- not a question
  A := goodNsWhInt.A
  R := fun e => e.elim

instance : Fintype nsWhIntWrongSem.U := inferInstanceAs (Fintype Ent)
instance : DecidableEq nsWhIntWrongSem.U := inferInstanceAs (DecidableEq Ent)

example : ¬ nsWhIntWrongSem.Models fhGrammar := by decide

end HPSG.Construction
