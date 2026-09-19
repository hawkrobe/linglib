/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.HPSG.Description
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.DeriveFintype

/-!
# The construct hierarchy of Sign-Based Construction Grammar in RSRL

This file defines an RSRL signature and grammar for a fragment of Sign-Based Construction
Grammar. A construct is a feature structure with a mother sign and daughter signs, and a
construction is a constraint on the constructs of one sort. Constructs are classified along two
dimensions, by how they are headed and by what kind of clause they form, and a construct sort
may lie below a sort of each dimension. It then inherits the constraints on both, because a
constraint on a sort holds of every entity below that sort.

The grammar contains the filler-head construction of Sag, which identifies the filler daughter
with the first element of the head daughter's `GAP` list and passes the rest of the list to the
mother, as Bouma, Malouf and Sag amalgamate gaps. It also contains the constraints that fix the
semantic type of each clause type after Ginzburg and Sag, the constraints particular to
topicalized, wh-exclamative and wh-relative clauses, and the head-modifier construction. A
`GAP` element is a `loc` object with a category and an index, as in Borsley and Crysmann's
presentation, so that a filler shares the index of its gap.

## Main definitions

* `HPSG.Construction.Srt`: the sorts, with the hierarchies of categories, semantic types,
  lists, constructs and clauses.
* `HPSG.Construction.sig`: the signature.
* `HPSG.Construction.fillerHeadPrinciple`: the filler-head construction.
* `HPSG.Construction.grammar`: the grammar.
* `HPSG.Construction.singleConstruct`: the model of a filler-head construct with one gap.
* `HPSG.Construction.twoGapConstruct`: the model of a filler-head construct whose head daughter
  has two gaps.
* `HPSG.Construction.memberDef`: the principle that defines list membership.

## Main results

* `HPSG.Construction.nsWhIntCl_inherits_principles`: in every model of the grammar, a nonsubject
  wh-interrogative construct satisfies the constraints on filler-head constructs and on
  interrogative clauses.
* `HPSG.Construction.freeVars_grammar`: the principles of the grammar are closed.

## Implementation notes

HPSG is a model-theoretic framework in the sense of Pullum and Scholz: a structure is
grammatical when it satisfies every principle, and no derivation is involved. The theorems
about particular constructs are therefore decided on finite interpretations.

A construct has at most two daughters, each under an attribute of its own. The filler-head
construction discharges the first element of `GAP`, whereas the `SLASH` value of the HPSG
literature is a set. The relation `member` recovers the set reading, and `memberDef` and the
example after it show what the list encoding rejects. The `WH`, `REL`, `IC` and `VFORM`
features and compositional semantics are not in the signature.

The aux-initial sorts and the `INV` attribute are constrained in `Studies/SagEtAl2020`, the
coordinate construct in `Studies/SagWasowBender2003`, and the island status of the five
filler-gap clauses is derived in `Studies/Sag2010`.

## References

* [sag-2010]
* [sag-etal-2020]
* [sag-2012]
* [ginzburg-sag-2000]
* [bouma-malouf-sag-2001]
* [borsley-crysmann-2024]
* [sag-wasow-bender-2003]
* [pollard-sag-1994]
* [pullum-scholz-2001]
* [richter-2000]
* [richter-2024]
-/

namespace HPSG.Construction

open HPSG.RSRL

/-! ### Sorts -/

/-- The sorts of the fragment. -/
inductive Srt
  | top
  -- categories
  | cat | verbal | nonverbal | verb | comp | nominal | noun | prep | adj | adv
  -- semantic types
  | semType | austinean | question | fact | proposition
  -- inversion values
  | invVal | invPlus | invMinus
  -- lists and their elements
  | list | elist | nelist | loc | idx
  | sign
  -- constructs
  | construct | phrasalCxt | lexicalCxt | headedCxt | clause | coordCxt
  | fillerHeadCxt | auxInitialCxt | headModifierCxt
  -- clause types
  | coreCl | relativeCl | declarativeCl | interrogativeCl | exclamativeCl
  -- clauses that are both headed constructs and clause types
  | topCl | whExclCl | nsWhIntCl | whRelCl | theCl | polarIntCl | auxInitialExclCl
  deriving DecidableEq, Fintype, Repr

/-- The immediate supersorts of a sort. Each filler-gap clause and each aux-initial clause has
two, a headed construct and a clause type. -/
def Srt.parents : Srt → List Srt
  | .top => []
  | .cat | .semType | .invVal | .list | .sign | .construct | .loc | .idx => [.top]
  | .verbal | .nonverbal => [.cat]
  | .verb | .comp => [.verbal]
  | .nominal | .adj | .adv => [.nonverbal]
  | .noun | .prep => [.nominal]
  | .austinean | .question | .fact | .proposition => [.semType]
  | .invPlus | .invMinus => [.invVal]
  | .elist | .nelist => [.list]
  | .phrasalCxt | .lexicalCxt => [.construct]
  | .headedCxt | .clause | .coordCxt => [.phrasalCxt]
  | .fillerHeadCxt | .auxInitialCxt | .headModifierCxt => [.headedCxt]
  | .coreCl | .relativeCl => [.clause]
  | .declarativeCl | .interrogativeCl | .exclamativeCl => [.coreCl]
  | .topCl | .theCl => [.fillerHeadCxt, .declarativeCl]
  | .whExclCl => [.fillerHeadCxt, .exclamativeCl]
  | .nsWhIntCl => [.fillerHeadCxt, .interrogativeCl]
  | .whRelCl => [.fillerHeadCxt, .relativeCl]
  | .polarIntCl => [.auxInitialCxt, .interrogativeCl]
  | .auxInitialExclCl => [.auxInitialCxt, .exclamativeCl]

/-- The length of the longest chain from a sort up to `top`. -/
def Srt.rank : Srt → ℕ
  | .top => 0
  | .cat | .semType | .invVal | .list | .sign | .construct | .loc | .idx => 1
  | .verbal | .nonverbal | .austinean | .question | .fact | .proposition | .invPlus | .invMinus
  | .elist | .nelist | .phrasalCxt | .lexicalCxt => 2
  | .verb | .comp | .nominal | .adj | .adv | .headedCxt | .clause | .coordCxt => 3
  | .noun | .prep | .fillerHeadCxt | .auxInitialCxt | .headModifierCxt | .coreCl
  | .relativeCl => 4
  | .declarativeCl | .interrogativeCl | .exclamativeCl => 5
  | .topCl | .whExclCl | .nsWhIntCl | .whRelCl | .theCl | .polarIntCl | .auxInitialExclCl => 6

instance : PartialOrder Srt :=
  partialOrderOfCovers (fun σ τ : Srt ↦ τ ∈ σ.parents) Srt.rank (by decide)

instance : DecidableLE Srt :=
  decidableLEOfCovers (covers := fun σ τ : Srt ↦ τ ∈ σ.parents)
    [.top, .cat, .verbal, .nonverbal, .nominal, .semType, .invVal, .list, .construct,
      .phrasalCxt, .headedCxt, .clause, .fillerHeadCxt, .auxInitialCxt, .coreCl, .relativeCl,
      .declarativeCl, .interrogativeCl, .exclamativeCl]
    (by decide)

/-! ### Attributes and the signature -/

/-- The attributes. A construct has a mother and daughters, a sign has a category, a `GAP` list,
a semantic type, an inversion value, a modified category and an index, and a nonempty list has
a first element and a rest. -/
inductive Feat
  | MTR | HDDTR | FILLERDTR | MODDTR | CONJ1 | CONJ2 | CAT | GAP | SEM | INV | MOD | FIRST | REST
  | INDEX
  deriving DecidableEq, Fintype, Repr

/-- The sorts that introduce each attribute, with its value sort there. -/
def Feat.decl : Feat → List (Srt × Srt)
  | .MTR => [(.construct, .sign)]
  | .HDDTR => [(.headedCxt, .sign)]
  | .FILLERDTR => [(.fillerHeadCxt, .sign)]
  | .MODDTR => [(.headModifierCxt, .sign)]
  | .CONJ1 | .CONJ2 => [(.coordCxt, .sign)]
  | .CAT => [(.sign, .cat), (.loc, .cat)]
  | .GAP => [(.sign, .list)]
  | .SEM => [(.sign, .semType)]
  | .INV => [(.sign, .invVal)]
  | .MOD => [(.sign, .cat)]
  | .FIRST => [(.nelist, .loc)]
  | .REST => [(.nelist, .list)]
  | .INDEX => [(.sign, .idx), (.loc, .idx)]

/-- The one relation symbol is list membership. -/
inductive CRel | member
  deriving DecidableEq, Fintype, Repr

/-- The signature of the fragment. -/
@[reducible] def sig : Signature Srt := .ofDecl Feat CRel (fun _ ↦ 2) Feat.decl (by decide)

/-- A nonsubject wh-interrogative construct inherits its mother from `construct` and its filler
daughter from `filler-head-cxt`, and a coordinate construct has no filler daughter. -/
example : sig.approp .nsWhIntCl .MTR = some .sign ∧ sig.approp .nsWhIntCl .FILLERDTR = some .sign ∧
    sig.approp .coordCxt .FILLERDTR = none := by decide

/-- The interpretation of `member` that holds of nothing, for models whose principles do not
mention the relation. -/
def noRel {U : Type*} (ρ : sig.Rel) : Set (Fin (sig.arity ρ) → U) := fun _ ↦ False

instance {U : Type*} (ρ : sig.Rel) : DecidablePred (@noRel U ρ) := fun _ ↦ instDecidableFalse

/-! ### Principles -/

/-- The filler-head construction. The filler daughter is nonverbal and the head daughter verbal.
The filler shares its category and its index with the first element of the head daughter's
`GAP` list, and the mother's `GAP` list is the rest of the head daughter's. -/
def fillerHeadPrinciple : Desc sig :=
  .imp (.sortAssign .colon .fillerHeadCxt)
    (.and (.sortAssign (.path [.FILLERDTR, .CAT]) .nonverbal)
      (.and (.sortAssign (.path [.HDDTR, .CAT]) .verbal)
        (.and (.pathEq (.path [.FILLERDTR, .CAT]) (.path [.HDDTR, .GAP, .FIRST, .CAT]))
          (.and (.pathEq (.path [.FILLERDTR, .INDEX]) (.path [.HDDTR, .GAP, .FIRST, .INDEX]))
            (.pathEq (.path [.MTR, .GAP]) (.path [.HDDTR, .GAP, .REST]))))))

/-- The mother of a declarative clause has an austinean semantic type. -/
def declarativePrinciple : Desc sig :=
  .imp (.sortAssign .colon .declarativeCl) (.sortAssign (.path [.MTR, .SEM]) .austinean)

/-- The mother of an interrogative clause denotes a question. -/
def interrogativePrinciple : Desc sig :=
  .imp (.sortAssign .colon .interrogativeCl) (.sortAssign (.path [.MTR, .SEM]) .question)

/-- The mother of an exclamative clause denotes a fact. -/
def exclamativePrinciple : Desc sig :=
  .imp (.sortAssign .colon .exclamativeCl) (.sortAssign (.path [.MTR, .SEM]) .fact)

/-- The mother of a relative clause denotes a proposition. -/
def relativePrinciple : Desc sig :=
  .imp (.sortAssign .colon .relativeCl) (.sortAssign (.path [.MTR, .SEM]) .proposition)

/-- The filler of a wh-relative clause is nominal, a noun phrase or a prepositional phrase. -/
def whRelPrinciple : Desc sig :=
  .imp (.sortAssign .colon .whRelCl) (.sortAssign (.path [.FILLERDTR, .CAT]) .nominal)

/-- The head daughter of a topicalized clause is a projection of a verb, which excludes the
complementizer-headed clause that a the-clause allows. -/
def topPrinciple : Desc sig :=
  .imp (.sortAssign .colon .topCl) (.sortAssign (.path [.HDDTR, .CAT]) .verb)

/-- The mother of a topicalized clause has an empty `GAP` list, which makes the clause an
island. -/
def topIslandPrinciple : Desc sig :=
  .imp (.sortAssign .colon .topCl) (.sortAssign (.path [.MTR, .GAP]) .elist)

/-- The mother of a wh-exclamative clause has an empty `GAP` list. -/
def whExclIslandPrinciple : Desc sig :=
  .imp (.sortAssign .colon .whExclCl) (.sortAssign (.path [.MTR, .GAP]) .elist)

/-- The head-modifier construction. The modifier daughter selects the category of the head
daughter through `MOD`, and the mother has the category of the head daughter. -/
def headModifierPrinciple : Desc sig :=
  .imp (.sortAssign .colon .headModifierCxt)
    (.and (.pathEq (.path [.MODDTR, .MOD]) (.path [.HDDTR, .CAT]))
      (.pathEq (.path [.MTR, .CAT]) (.path [.HDDTR, .CAT])))

/-- The grammar of the fragment. -/
def grammar : Grammar sig :=
  [fillerHeadPrinciple, declarativePrinciple, interrogativePrinciple, exclamativePrinciple,
    relativePrinciple, whRelPrinciple, topPrinciple, topIslandPrinciple, whExclIslandPrinciple,
    headModifierPrinciple]

/-- Every principle of the grammar is closed, so its satisfaction does not depend on the
variable assignment. -/
theorem freeVars_grammar : ∀ d ∈ grammar, d.freeVars = ∅ := by decide

/-! ### Inheritance from two supersorts -/

/-- The nonsubject wh-interrogative clause is both a filler-head construct and an interrogative
clause. -/
theorem nsWhIntCl_inherits :
    Srt.nsWhIntCl ≤ .fillerHeadCxt ∧ Srt.nsWhIntCl ≤ .interrogativeCl := by decide

/-- Each of the five filler-gap clauses is a filler-head construct and a clause of the type
that fixes its semantics. -/
theorem fg_cross_classify :
    (Srt.topCl ≤ .fillerHeadCxt ∧ Srt.topCl ≤ .declarativeCl) ∧
      (Srt.whExclCl ≤ .fillerHeadCxt ∧ Srt.whExclCl ≤ .exclamativeCl) ∧
      (Srt.nsWhIntCl ≤ .fillerHeadCxt ∧ Srt.nsWhIntCl ≤ .interrogativeCl) ∧
      (Srt.whRelCl ≤ .fillerHeadCxt ∧ Srt.whRelCl ≤ .relativeCl) ∧
      (Srt.theCl ≤ .fillerHeadCxt ∧ Srt.theCl ≤ .declarativeCl) := by decide

/-- In every model of the grammar, a nonsubject wh-interrogative construct inherits from both of
its supersorts. Its head daughter is verbal, as in every filler-head construct, and its mother
denotes a question, as in every interrogative clause. Neither constraint is stated on the sort
itself. -/
theorem nsWhIntCl_inherits_principles {U : Type*} {I : Interpretation sig U}
    (hI : I.Models grammar) {u : U} (hu : I.S u ≤ .nsWhIntCl) :
    I.Satisfies (fun _ ↦ u) u (.sortAssign (.path [.HDDTR, .CAT]) .verbal) ∧
      I.Satisfies (fun _ ↦ u) u (.sortAssign (.path [.MTR, .SEM]) .question) := by
  have hfh : fillerHeadPrinciple ∈ grammar := List.mem_cons_self
  have hint : interrogativePrinciple ∈ grammar := by simp [grammar]
  exact ⟨(Interpretation.satisfies_and.1 (Interpretation.satisfies_and.1
      (hI.satisfies_of_le hfh (hu.trans nsWhIntCl_inherits.1))).2).1,
    hI.satisfies_of_le hint (hu.trans nsWhIntCl_inherits.2)⟩

/-! ### Models of filler-head constructs -/

/-- The entities of the worked constructs are the construct, its mother, head daughter and
filler daughter, four categories, two list cells and the empty list, the category of a second
gap, a semantic object, and two `loc` objects with their indices. -/
inductive Ent
  | cxt | mtr | hd | fl | npCat | vpCat | adjCat | compCat | g1 | g2 | nil | c2 | sem
  | lcl1 | lcl2 | ix1 | ix2
  deriving DecidableEq, Fintype, Repr

/-- The default sort of each entity. A model overrides the sort of the construct and, where its
clause type requires, of the semantic object and of the second gap's category. -/
def baseS : Ent → Srt
  | .cxt => .fillerHeadCxt
  | .mtr | .hd | .fl => .sign
  | .npCat | .c2 => .noun
  | .vpCat => .verb
  | .adjCat => .adj
  | .compCat => .comp
  | .g1 | .g2 => .nelist
  | .nil => .elist
  | .sem => .austinean
  | .lcl1 | .lcl2 => .loc
  | .ix1 | .ix2 => .idx

/-- The attribute values of a construct with one gap. The head daughter is verbal with the
`GAP` list `⟨lcl1⟩`, the filler is a noun phrase that shares its category and index with
`lcl1`, and the mother's `GAP` list is empty. -/
def singleGapA : Feat → Ent → Option Ent
  | .MTR, .cxt => some .mtr
  | .HDDTR, .cxt => some .hd
  | .FILLERDTR, .cxt => some .fl
  | .CAT, .fl | .CAT, .lcl1 => some .npCat
  | .INDEX, .fl | .INDEX, .lcl1 => some .ix1
  | .CAT, .hd => some .vpCat
  | .GAP, .hd => some .g1
  | .FIRST, .g1 => some .lcl1
  | .REST, .g1 | .GAP, .mtr => some .nil
  | .SEM, .mtr => some .sem
  | _, _ => none

/-- The attribute values of a construct whose head daughter has the `GAP` list `⟨lcl1, lcl2⟩`.
The filler discharges `lcl1`, and the mother's `GAP` list is the rest, `⟨lcl2⟩`. -/
def twoGapA : Feat → Ent → Option Ent
  | .MTR, .cxt => some .mtr
  | .HDDTR, .cxt => some .hd
  | .FILLERDTR, .cxt => some .fl
  | .CAT, .fl | .CAT, .lcl1 => some .npCat
  | .INDEX, .fl | .INDEX, .lcl1 => some .ix1
  | .CAT, .hd => some .vpCat
  | .GAP, .hd => some .g1
  | .FIRST, .g1 => some .lcl1
  | .REST, .g1 | .GAP, .mtr => some .g2
  | .FIRST, .g2 => some .lcl2
  | .CAT, .lcl2 => some .c2
  | .INDEX, .lcl2 => some .ix2
  | .REST, .g2 => some .nil
  | .SEM, .mtr => some .sem
  | _, _ => none

/-- The model of a construct of sort `cxtSort` whose mother has semantic type `semSort`, with
the attribute values `a`. -/
@[reducible] def singleConstruct (cxtSort semSort : Srt) (a : Feat → Ent → Option Ent) :
    Interpretation sig Ent where
  S
    | .cxt => cxtSort
    | .sem => semSort
    | u => baseS u
  A := a
  R := noRel

/-- The model of a two-gap construct of sort `cxtSort` whose mother has semantic type `semSort`
and whose second gap has category `c2Sort`. -/
@[reducible] def twoGapConstruct (cxtSort semSort c2Sort : Srt) : Interpretation sig Ent where
  S
    | .cxt => cxtSort
    | .sem => semSort
    | .c2 => c2Sort
    | u => baseS u
  A := twoGapA
  R := noRel

/-- A well-formed filler-head construct with one gap. -/
abbrev goodFillerHead : Interpretation sig Ent :=
  singleConstruct .fillerHeadCxt .austinean singleGapA

example : goodFillerHead.Models grammar := by decide

/-- A filler-head construct whose filler is an adjective phrase although the gap is a noun
phrase. The filler is still nonverbal, so only the identity of filler and gap fails. -/
abbrev gapMismatch : Interpretation sig Ent :=
  singleConstruct .fillerHeadCxt .austinean fun
    | .CAT, .fl => some .adjCat
    | a, u => singleGapA a u

example : ¬ gapMismatch.Models [fillerHeadPrinciple] := by decide

/-- A filler-head construct whose filler and gap agree in category but differ in index. -/
abbrev indexMismatch : Interpretation sig Ent :=
  singleConstruct .fillerHeadCxt .austinean fun
    | .INDEX, .fl => some .ix2
    | a, u => singleGapA a u

example : ¬ indexMismatch.Models [fillerHeadPrinciple] := by decide

/-- A filler-head construct whose head daughter has two gaps. The second gap passes to the
mother. -/
abbrev goodTwoGap : Interpretation sig Ent :=
  twoGapConstruct .fillerHeadCxt .austinean .noun

example : goodTwoGap.Models grammar := by decide

/-- A well-formed nonsubject wh-interrogative construct, which witnesses the hypotheses of
`nsWhIntCl_inherits_principles`. -/
abbrev goodNsWhInt : Interpretation sig Ent :=
  singleConstruct .nsWhIntCl .question singleGapA

example : goodNsWhInt.Models grammar := by decide

/-- A nonsubject wh-interrogative construct whose mother has an austinean semantic type. It
violates the constraint that it inherits from the interrogative clause. -/
abbrev nsWhIntWrongSem : Interpretation sig Ent :=
  singleConstruct .nsWhIntCl .austinean singleGapA

example : nsWhIntWrongSem.Models [fillerHeadPrinciple] ∧
    ¬ nsWhIntWrongSem.Models [interrogativePrinciple] := by decide

/-- A wh-relative construct whose filler is an adjective phrase that matches the gap. It
satisfies the filler-head construction but not the requirement of a nominal filler. -/
abbrev whRelAdjFiller : Interpretation sig Ent :=
  singleConstruct .whRelCl .proposition fun
    | .CAT, .fl | .CAT, .lcl1 => some .adjCat
    | a, u => singleGapA a u

example : whRelAdjFiller.Models [fillerHeadPrinciple] ∧
    ¬ whRelAdjFiller.Models [whRelPrinciple] := by decide

/-- A the-clause whose head daughter is headed by a complementizer. -/
abbrev goodTheCl : Interpretation sig Ent :=
  singleConstruct .theCl .austinean fun
    | .CAT, .hd => some .compCat
    | a, u => singleGapA a u

example : goodTheCl.Models grammar := by decide

/-- A topicalized clause whose head daughter is headed by a complementizer. The head is verbal,
as the filler-head construction requires, but it is not a projection of a verb. -/
abbrev topClCompHead : Interpretation sig Ent :=
  singleConstruct .topCl .austinean fun
    | .CAT, .hd => some .compCat
    | a, u => singleGapA a u

example : topClCompHead.Models [fillerHeadPrinciple] ∧ ¬ topClCompHead.Models [topPrinciple] := by
  decide

/-- A head with the `GAP` list `⟨lcl1, lcl2⟩` whose two elements both carry the filler's index,
as in across-the-board extraction. -/
abbrev atbConstruct : Interpretation sig Ent where
  S := baseS
  A
    | .INDEX, .lcl2 => some .ix1
    | .CAT, .lcl2 => some .npCat
    | a, u => twoGapA a u
  R := noRel

/-- One filler shares its index with two gaps, which a `GAP` list of bare categories could not
express. -/
theorem atb_one_filler_two_coindexed_gaps :
    atbConstruct.Satisfies (fun _ ↦ .cxt) .cxt
      (.and (.pathEq (.path [.FILLERDTR, .INDEX]) (.path [.HDDTR, .GAP, .FIRST, .INDEX]))
        (.pathEq (.path [.FILLERDTR, .INDEX]) (.path [.HDDTR, .GAP, .REST, .FIRST, .INDEX]))) := by
  decide

/-! ### Models of head-modifier constructs -/

/-- The model of a noun modified by an adjunct whose `MOD` value is the entity `modTarget`. -/
@[reducible] def headModConstruct (modTarget : Ent) : Interpretation sig Ent where
  S
    | .cxt => .headModifierCxt
    | u => baseS u
  A
    | .MTR, .cxt => some .mtr
    | .HDDTR, .cxt => some .hd
    | .MODDTR, .cxt => some .fl
    | .CAT, .hd | .CAT, .mtr => some .npCat
    | .MOD, .fl => some modTarget
    | _, _ => none
  R := noRel

/-- A modifier that selects the noun's category is licensed, and one that selects a verb's
category is not. -/
example : (headModConstruct .npCat).Models grammar ∧
    ¬ (headModConstruct .vpCat).Models grammar := by decide

/-! ### The `GAP` list as a set

The filler-head construction discharges the first element of the `GAP` list. The relation
`member`, defined by `memberDef`, lets a principle speak of any element instead. -/

/-- The entities of a filler-head construct whose head has the `GAP` list `⟨gNP, gPP⟩` and whose
filler matches the second element. -/
inductive GapEnt
  | cxt | mtr | hd | fl | gVerb | gNP | gPP | gAdj | l1 | l2 | lnil
  deriving DecidableEq, Fintype, Repr

/-- The attribute values of the construct. -/
def gapSetA : Feat → GapEnt → Option GapEnt
  | .MTR, .cxt => some .mtr
  | .HDDTR, .cxt => some .hd
  | .FILLERDTR, .cxt => some .fl
  | .CAT, .hd => some .gVerb
  | .CAT, .fl => some .gPP
  | .CAT, .mtr => some .gAdj
  | .GAP, .hd => some .l1
  | .GAP, .mtr => some .l2
  | .FIRST, .l1 => some .gNP
  | .REST, .l1 => some .l2
  | .FIRST, .l2 => some .gPP
  | .REST, .l2 => some .lnil
  | _, _ => none

/-- The elements of the list rooted at `l`, collected along at most `n` cells. -/
def gapElems (a : Feat → GapEnt → Option GapEnt) : ℕ → GapEnt → List GapEnt
  | 0, _ => []
  | n + 1, l => match a .FIRST l with
    | some f => f :: (match a .REST l with | some r => gapElems a n r | none => [])
    | none => []

/-- The entity `e` is an element of the list rooted at `l`. -/
def memberOf (e l : GapEnt) : Prop := e ∈ gapElems gapSetA 11 l

instance (e l : GapEnt) : Decidable (memberOf e l) :=
  inferInstanceAs (Decidable (e ∈ gapElems gapSetA 11 l))

/-- The model, which interprets `member` as list membership. -/
@[reducible] def gapSetModel : Interpretation sig GapEnt where
  S
    | .cxt => .fillerHeadCxt
    | .mtr | .hd | .fl => .sign
    | .gVerb => .verb
    | .gNP => .noun
    | .gPP => .prep
    | .gAdj => .adj
    | .l1 | .l2 => .nelist
    | .lnil => .elist
  A := gapSetA
  R _ xs := memberOf (xs 0) (xs 1)

instance (ρ : sig.Rel) : DecidablePred (gapSetModel.R ρ) := fun xs ↦
  inferInstanceAs (Decidable (memberOf (xs 0) (xs 1)))

/-- The principle that defines `member`. The entity `x` is a member of `L` exactly when `L` is a
nonempty list and `x` is its first element or a member of its rest. The rest reaches the
relation through the bound variable `2`, since a relation symbol applies to variables. -/
def memberDef : Desc sig :=
  .all 0 (.all 1 (.iff (.rel .member ![0, 1])
    (.and (.sortAssign (.var 1) .nelist)
      (.or (.pathEq (.var 0) (.feat (.var 1) .FIRST))
        (.ex 2 (.and (.pathEq (.var 2) (.feat (.var 1) .REST)) (.rel .member ![0, 2])))))))

example : gapSetModel.Models [memberDef] := by decide

/-- The filler's category is a member of the head daughter's `GAP` list. -/
example : gapSetModel.Satisfies (fun _ ↦ .cxt) .cxt
    (.ex 0 (.ex 1 (.and (.pathEq (.var 0) (.path [.FILLERDTR, .CAT]))
      (.and (.pathEq (.var 1) (.path [.HDDTR, .GAP])) (.rel .member ![0, 1]))))) := by decide

/-- The same construct violates the filler-head construction, which looks only at the first
element of the list. -/
example : ¬ gapSetModel.Models [fillerHeadPrinciple] := by decide

end HPSG.Construction
