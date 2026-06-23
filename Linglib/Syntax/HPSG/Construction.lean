/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.HPSG.Description
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false

/-!
# The canonical SBCG construct hierarchy with list-valued GAP in RSRL
[sag-2010] [sag-etal-2020] [sag-2012] [bouma-malouf-sag-2001] [richter-2000] [richter-2024]

The **single canonical RSRL signature** for the Sign-Based Construction Grammar fragment, formalized on
the RSRL feature-structure substrate (`Syntax/HPSG/{Signature,Interpretation,Description}`). One
`Signature` (`sig`) carries, in one feature-structure language:

* the **construct type hierarchy with monotonic multiple inheritance** ([sag-etal-2020] Figs. 6–7);
* a **list-valued `GAP` (SLASH) feature** with gap **amalgamation** ([sag-2010] §4, after
  [bouma-malouf-sag-2001]); and
* **islands** as `[GAP ⟨⟩]` constraints on the construction types themselves ([sag-2010] §5.1).

A construction is a constraint `τ ⇒ D` ([sag-2012] (44)) on a `construct = [MTR, DTRS]` ([sag-2012]
(46)); inheritance is the **sort order plus the implication semantics** — a construct whose sort sits
below several supersorts satisfies *all* their principles, with no per-construction restatement. This
is the monotonic (no-overriding) inheritance SBCG commits to ([sag-2012] fn. 17; the "category
restriction operation" of [sag-etal-2020]).

The hierarchy is the authoritative two-dimensional one of [sag-etal-2020] (Figs. 6–7):

* **construct backbone** (Fig. 6): `construct > {phrasal-cxt, lexical-cxt}`;
  `phrasal-cxt > {headed-cxt, clause}`;
  `headed-cxt > {subject-head-cxt, pred-head-comp-cxt, aux-initial-cxt, …}` — with `filler-head-cxt`
  the further `headed-cxt` subtype of [sag-2010] Fig. A2 (elided behind Fig. 6's "…");
* **clausal dimension** (Fig. 7): `clause > {core-cl, relative-cl}`;
  `core-cl > {declarative-cl, interrogative-cl, exclamative-cl}`.

The **cross-classification** is a lower bound across the two dimensions — the mechanism [sag-etal-2020]
Fig. 5 illustrates for `subj-pred-cl` (`declarative-cl ⊓ subject-head-cxt`). Here [sag-2010]'s
nonsubject wh-interrogative `ns-wh-int-cl` ((80), Fig. 8) is a subtype of *both* `filler-head-cxt`
(headed dim.) and `interrogative-cl` (clausal dim.), so it inherits the filler-head constraints (head
verbal, filler nonverbal, filler↔gap token identity, gap amalgamation) **and** the interrogative
semantics (`MTR` `SEM` a question) from one sort assignment — the keystone theorem below.

## The list-valued GAP and islands

A sign's `GAP` value is a genuine HPSG list — `elist` (empty) or `nelist` with `FIRST`/`REST`
([sag-2010]'s `⟨…⟩` notation). The **filler-head construction** binds the head daughter's *first* gap
(token identity between the filler's category and `GAP|FIRST`) and **amalgamates the rest** onto the
mother (`MTR|GAP = HD-DTR|GAP|REST`), so a clause with two undischarged gaps passes the second up
([sag-2010] (53), (59)). **Islands fall out** of this: an island construction (topicalization (67),
wh-exclamative (74)) additionally constrains its mother to `[GAP ⟨⟩]` (`elist`); a would-be *second*
gap then makes the amalgamated mother `GAP` non-empty, contradicting `[GAP ⟨⟩]`, so the construct is
rejected — the model-theoretic content of "topicalization is an absolute extraction island", a theorem
about `Models`, not a universal Subjacency. Weak islands (`weak-island-cxt`) are *selectively* permeable
(NP passes, PP blocked), the NP/PP asymmetry of [sag-wasow-bender-2003] Ch. 15.

## Scope

This file is the **substrate**: the type hierarchy, the cross-classification keystone, all five
filler-gap constructions ([sag-2010] §5: topicalization, wh-exclamative, nonsubject wh-interrogative,
wh-relative, the-clause), and the gap/island mechanism. The hierarchy also carries the
`aux-initial-cxt`/`interrogative-SAI` sort nodes and the `INV` feature ([sag-etal-2020] Fig. 6); the
**inversion construction**'s own principle and worked constructs are paper-anchored in
`Studies/SagEtAl2020.lean`, and the island/extraction taxonomy theorems in `Studies/SagWasowBender2003`
and `Studies/Sag2010`, which consume this substrate.

The minimal HFP-bridge signature `hpsgSig` (`Model.lean`, value-equality↔token-identity bridge to the
computational core) and the relational binding signature `bindingSig` (`Binding.lean`, the only signature
with a non-empty `Rel`) stay **separate example signatures** over the same RSRL framework — mathlib keeps
many example structures over one framework, and folding them in would force a non-empty `Rel` (losing the
empty-relation decidability shortcut) for marginal gain.

`GAP` elements are bare categories (not full local objects); n-ary `DTRS`, the `WH`/`REL`/`IC`/`VFORM`
finer variation, and compositional `SEM` are deferred. Decidability stays inside `Models` over fixed
finite interpretations (Kepser 2004: full RSRL model-checking is undecidable).
-/

namespace HPSG.Construction

open HPSG.RSRL

/-! ### Sorts: categories, semantic types, GAP lists, signs, and the construct/clausal hierarchy -/

/-- Sorts of the fragment: a category hierarchy, a semantic-type hierarchy, the `GAP`-list sorts
(`list > {elist, nelist}`), `sign`, and the [sag-etal-2020] construct (Fig. 6) and clausal (Fig. 7)
type hierarchies, with `ns-wh-int-cl` as the worked cross-classified subtype ([sag-2010] (80), Fig. 8)
and the generic `island-cxt`/`weak-island-cxt` demonstration subtypes of `filler-head-cxt`. -/
inductive Srt
  | top
  -- category hierarchy (filler-head-cxt keys on verbal/nonverbal; wh-rel on nominal; the-cl on comp;
  -- the noun/prep split is the NP/PP distinction weak islands are sensitive to)
  | cat | verbal | nonverbal | verb | comp | nominal | noun | prep | adj
  -- semantic-type hierarchy (clause types key on the MTR's SEM type)
  | semType | austinean | question | fact | proposition
  -- inversion-value hierarchy (aux-initial-cxt keys on the head's INV value, [sag-etal-2020] (39))
  | invVal | invPlus | invMinus
  -- GAP-list sorts ([sag-2010]'s ⟨…⟩): a list is empty (elist) or has a FIRST and a REST (nelist)
  | list | elist | nelist
  -- signs
  | sign
  -- construct backbone (Fig. 6; filler-head-cxt per [sag-2010] Fig. A2): filler-head-cxt and
  -- aux-initial-cxt are sibling headed-cxt subtypes
  | construct | phrasalCxt | lexicalCxt | headedCxt | clause | fillerHeadCxt | auxInitialCxt
  -- head-modifier-cxt (Fig. 6): a relative clause or other adjunct modifies a head ([sag-2010] §6)
  | headModifierCxt
  -- lexical constructs (Fig. 6): inflectional-cxt = a category-preserving lexical rule (e.g. passive)
  | inflectionalCxt
  -- generic island demonstrations (Ross domains, not Sag construction types) under filler-head-cxt
  | islandCxt | weakIslandCxt
  -- clausal hierarchy (Fig. 7)
  | coreCl | relativeCl | declarativeCl | interrogativeCl | exclamativeCl
  -- the filler-gap constructions ([sag-2010] §5) and the interrogative SAI ([sag-etal-2020]), each
  -- cross-classifying a clausal type
  | topCl | whExclCl | nsWhIntCl | whRelCl | theCl | interrogativeSAI
  deriving DecidableEq, Fintype, Repr

/-- Direct subsumption ("covers"): the **DAG edges** (a is *directly* more specific than b), not the
transitive closure. The order is `ReflTransGen covers`, so transitivity is structural and there is no
hand-maintained closure or `|Srt|³` `decide`. Each filler-gap construction covers **two** parents —
its `headed-cxt` subtype and its clausal type — the multiple inheritance. -/
def covers : Srt → Srt → Bool
  -- categories (nonverbal > {nominal, adj}; nominal > {noun, prep})
  | .verbal, .cat => true | .nonverbal, .cat => true
  | .verb, .verbal => true | .comp, .verbal => true
  | .nominal, .nonverbal => true | .adj, .nonverbal => true
  | .noun, .nominal => true | .prep, .nominal => true
  -- semantic types
  | .austinean, .semType => true | .question, .semType => true
  | .fact, .semType => true | .proposition, .semType => true
  -- inversion values
  | .invPlus, .invVal => true | .invMinus, .invVal => true
  -- GAP lists
  | .elist, .list => true | .nelist, .list => true
  -- the maximal sorts, directly below top
  | .cat, .top => true | .semType, .top => true | .invVal, .top => true | .list, .top => true
  | .sign, .top => true | .construct, .top => true
  -- construct backbone
  | .phrasalCxt, .construct => true | .lexicalCxt, .construct => true
  | .inflectionalCxt, .lexicalCxt => true
  | .headedCxt, .phrasalCxt => true | .clause, .phrasalCxt => true
  | .fillerHeadCxt, .headedCxt => true | .auxInitialCxt, .headedCxt => true
  | .headModifierCxt, .headedCxt => true
  | .islandCxt, .fillerHeadCxt => true | .weakIslandCxt, .fillerHeadCxt => true
  | .coreCl, .clause => true | .relativeCl, .clause => true
  | .declarativeCl, .coreCl => true | .interrogativeCl, .coreCl => true
  | .exclamativeCl, .coreCl => true
  -- filler-gap constructions and the interrogative SAI: each covers its headed parent AND its clausal
  -- type ([sag-2010] §5; whRelCl's clausal parent is relative-cl, directly under clause, Fig. 7)
  | .topCl, .fillerHeadCxt => true | .topCl, .declarativeCl => true
  | .whExclCl, .fillerHeadCxt => true | .whExclCl, .exclamativeCl => true
  | .nsWhIntCl, .fillerHeadCxt => true | .nsWhIntCl, .interrogativeCl => true
  | .whRelCl, .fillerHeadCxt => true | .whRelCl, .relativeCl => true
  | .theCl, .fillerHeadCxt => true | .theCl, .declarativeCl => true
  | .interrogativeSAI, .auxInitialCxt => true | .interrogativeSAI, .interrogativeCl => true
  | _, _ => false

/-- Specificity depth; every covers edge strictly increases it, giving antisymmetry. The filler-gap
constructions sit at depth 6, above *both* their depth-4 headed parent and their depth-5 clausal type. -/
def rank : Srt → Nat
  | .top => 0
  | .cat => 1 | .semType => 1 | .invVal => 1 | .list => 1 | .sign => 1 | .construct => 1
  | .verbal => 2 | .nonverbal => 2 | .austinean => 2 | .question => 2 | .fact => 2 | .proposition => 2
  | .invPlus => 2 | .invMinus => 2 | .elist => 2 | .nelist => 2 | .phrasalCxt => 2 | .lexicalCxt => 2
  | .verb => 3 | .comp => 3 | .nominal => 3 | .adj => 3 | .headedCxt => 3 | .clause => 3
  | .inflectionalCxt => 3
  | .noun => 4 | .prep => 4 | .fillerHeadCxt => 4 | .auxInitialCxt => 4 | .headModifierCxt => 4
  | .coreCl => 4 | .relativeCl => 4
  | .islandCxt => 5 | .weakIslandCxt => 5
  | .declarativeCl => 5 | .interrogativeCl => 5 | .exclamativeCl => 5
  | .topCl => 6 | .whExclCl => 6 | .nsWhIntCl => 6 | .whRelCl => 6 | .theCl => 6 | .interrogativeSAI => 6

instance : PartialOrder Srt :=
  partialOrderOfCovers (covers · · = true) rank (by decide)

instance : DecidableLE Srt := fun a b =>
  decidableLEOfCovers (covers := (covers · · = true))
    [.top, .cat, .verbal, .nonverbal, .verb, .comp, .nominal, .noun, .prep, .adj,
     .semType, .austinean, .question, .fact, .proposition, .invVal, .invPlus, .invMinus,
     .list, .elist, .nelist, .sign,
     .construct, .phrasalCxt, .lexicalCxt, .headedCxt, .clause, .fillerHeadCxt, .auxInitialCxt,
     .headModifierCxt, .inflectionalCxt, .islandCxt, .weakIslandCxt,
     .coreCl, .relativeCl, .declarativeCl, .interrogativeCl, .exclamativeCl,
     .topCl, .whExclCl, .nsWhIntCl, .whRelCl, .theCl, .interrogativeSAI]
    (by decide) a b

/-! ### Attributes and the signature -/

/-- Attributes: a construct's mother (`MTR`) and head/filler daughters (`HDDTR`/`FILLERDTR`); a sign's
`CAT`, (list-valued) `GAP`, `SEM` type, and `INV` value; a nonempty list's `FIRST` (a category) and
`REST` (a list). -/
inductive Feat
  | MTR | HDDTR | FILLERDTR | MODDTR | BASE | CAT | GAP | SEM | INV | MOD | FIRST | REST
  deriving DecidableEq, Fintype, Repr

/-- Appropriateness: every construct has a `MTR` (a sign); `headed-cxt` and its subtypes additionally
have `HDDTR` (and `filler-head-cxt` a `FILLERDTR`); a `sign` has `CAT`/`SEM`/`INV` and a list-valued
`GAP`; a `nelist` has `FIRST` (a category) and `REST` (a list). Respects feature inheritance
([richter-2024]): an attribute appropriate to a sort is appropriate to its subsorts. -/
def approp : Srt → Feat → Option Srt
  | .construct, .MTR => some .sign
  | .phrasalCxt, .MTR => some .sign
  | .lexicalCxt, .MTR => some .sign
  | .inflectionalCxt, .MTR => some .sign
  | .headedCxt, .MTR => some .sign
  | .clause, .MTR => some .sign
  | .fillerHeadCxt, .MTR => some .sign
  | .islandCxt, .MTR => some .sign
  | .weakIslandCxt, .MTR => some .sign
  | .coreCl, .MTR => some .sign
  | .relativeCl, .MTR => some .sign
  | .declarativeCl, .MTR => some .sign
  | .interrogativeCl, .MTR => some .sign
  | .exclamativeCl, .MTR => some .sign
  | .nsWhIntCl, .MTR => some .sign
  | .topCl, .MTR => some .sign
  | .whExclCl, .MTR => some .sign
  | .whRelCl, .MTR => some .sign
  | .theCl, .MTR => some .sign
  | .auxInitialCxt, .MTR => some .sign
  | .interrogativeSAI, .MTR => some .sign
  | .headModifierCxt, .MTR => some .sign
  -- HDDTR is common to all headed constructs; FILLERDTR is specific to filler-head-cxt (an
  -- aux-initial construct has head + valent daughters, no filler); MODDTR (the modifier) to
  -- head-modifier-cxt
  | .headedCxt, .HDDTR => some .sign
  | .auxInitialCxt, .HDDTR => some .sign
  | .interrogativeSAI, .HDDTR => some .sign
  | .fillerHeadCxt, .HDDTR => some .sign
  | .fillerHeadCxt, .FILLERDTR => some .sign
  | .islandCxt, .HDDTR => some .sign
  | .islandCxt, .FILLERDTR => some .sign
  | .weakIslandCxt, .HDDTR => some .sign
  | .weakIslandCxt, .FILLERDTR => some .sign
  | .nsWhIntCl, .HDDTR => some .sign
  | .nsWhIntCl, .FILLERDTR => some .sign
  | .topCl, .HDDTR => some .sign
  | .topCl, .FILLERDTR => some .sign
  | .whExclCl, .HDDTR => some .sign
  | .whExclCl, .FILLERDTR => some .sign
  | .whRelCl, .HDDTR => some .sign
  | .whRelCl, .FILLERDTR => some .sign
  | .theCl, .HDDTR => some .sign
  | .theCl, .FILLERDTR => some .sign
  | .headModifierCxt, .HDDTR => some .sign
  | .headModifierCxt, .MODDTR => some .sign
  -- a lexical rule's input base (inflectional-cxt: a category-preserving rule like passive)
  | .inflectionalCxt, .BASE => some .sign
  | .sign, .CAT => some .cat
  | .sign, .GAP => some .list
  | .sign, .SEM => some .semType
  | .sign, .INV => some .invVal
  | .sign, .MOD => some .cat
  | .nelist, .FIRST => some .cat
  | .nelist, .REST => some .list
  | _, _ => none

-- Appropriateness values never refine down this hierarchy (a sort and its subsorts carry the *same*
-- value for an attribute); proving this propagation over just `(σ₁, σ₂, α)` — without the `τ₁`
-- quantifier or `∃`-search — keeps the `decide` within budget, and `approp_inh_of_propagates` derives
-- the `Signature.approp_inherits` obligation from it.
private theorem approp_propagates : ∀ (σ₁ σ₂ : Srt) (α : Feat),
    σ₂ ≤ σ₁ → (approp σ₁ α).isSome = true → approp σ₂ α = approp σ₁ α := by decide

/-- The fragment's signature (no relations). -/
@[reducible] def sig : Signature Srt where
  Attr := Feat
  Rel := Empty
  arity := fun e => e.elim
  approp := approp
  approp_inherits := fun hle happ => approp_inh_of_propagates approp_propagates hle happ

/-! ### Principles (constructions as `τ ⇒ D`)

Each principle constrains every feature structure whose sort is `≤` its antecedent — so a construct
inherits a principle exactly when its sort sits below the principle's type. -/

/-- The **filler-head construction** ([sag-2010] (58); placed under `headed-cxt` in [sag-2010] Fig. A2;
amalgamation after [bouma-malouf-sag-2001]): the head daughter is `[CAT verbal]`, the filler is
`[CAT nonverbal]`, the filler's category is **token-identical** (`pathEq`) to the head daughter's
*first* gap (`GAP|FIRST` — the bound dependency), and the mother's `GAP` is the head daughter's
`GAP|REST` (the remaining gaps amalgamate up). The `[CAT nonverbal]` filler is, in the paper, a
per-subtype generalization (each F-G construction's (25)-style parameter, refined to `nominal` for
wh-relative, (25b)) rather than a constraint of (58) itself; it is stated here once on the supertype
because every subtype satisfies it. -/
def fillerHeadPrinciple : Desc sig :=
  .imp (.sortAssign .colon .fillerHeadCxt)
    (.and (.sortAssign (.path [.FILLERDTR, .CAT]) .nonverbal)
      (.and (.sortAssign (.path [.HDDTR, .CAT]) .verbal)
        (.and (.pathEq (.path [.FILLERDTR, .CAT]) (.path [.HDDTR, .GAP, .FIRST]))
          (.pathEq (.path [.MTR, .GAP]) (.path [.HDDTR, .GAP, .REST])))))

/-- Clausal semantics ([sag-etal-2020] Fig. 7, following G&S 2000): the mother's `SEM` type is fixed
by the clausal type — `declarative-cl` ⇒ austinean, `interrogative-cl` ⇒ question,
`exclamative-cl` ⇒ fact, `relative-cl` ⇒ proposition. -/
def declarativePrinciple : Desc sig :=
  .imp (.sortAssign .colon .declarativeCl) (.sortAssign (.path [.MTR, .SEM]) .austinean)
def interrogativePrinciple : Desc sig :=
  .imp (.sortAssign .colon .interrogativeCl) (.sortAssign (.path [.MTR, .SEM]) .question)
def exclamativePrinciple : Desc sig :=
  .imp (.sortAssign .colon .exclamativeCl) (.sortAssign (.path [.MTR, .SEM]) .fact)
def relativePrinciple : Desc sig :=
  .imp (.sortAssign .colon .relativeCl) (.sortAssign (.path [.MTR, .SEM]) .proposition)

/-- The **wh-relative construction**'s distinguishing constraint ([sag-2010] (92), (25b)): unlike the
other filler-gap constructions (nonverbal filler), the relative filler is `[CAT nominal]` — an NP or PP
(`nominal` resolves to `noun`/`prep`), excluding AP/AdvP. -/
def whRelPrinciple : Desc sig :=
  .imp (.sortAssign .colon .whRelCl) (.sortAssign (.path [.FILLERDTR, .CAT]) .nominal)

/-- The **topicalization construction**'s distinguishing constraint ([sag-2010] (61), (27a)): its head
daughter is a `[CAT verb]` projection (an S), excluding the complementizer-headed CP that the
otherwise-similar (also austinean) the-clause allows ((27b): the-clause head is S or CP). -/
def topPrinciple : Desc sig :=
  .imp (.sortAssign .colon .topCl) (.sortAssign (.path [.HDDTR, .CAT]) .verb)

/-- **Absolute island** ([sag-2010] (67)): a generic island construct's mother is `[GAP ⟨⟩]` — no
dependency penetrates beyond the one its filler binds. This generic `island-cxt` demonstrates the
mechanism for Ross's island *domains* (`Studies/SagWasowBender2003`); the F-G constructions that are
absolute islands carry their own `[GAP ⟨⟩]` principle below. -/
def islandPrinciple : Desc sig :=
  .imp (.sortAssign .colon .islandCxt) (.sortAssign (.path [.MTR, .GAP]) .elist)

/-- **Weak-island constraint**: a weak island is *selectively* permeable — an NP dependency passes
through, a PP (more generally, non-nominal) dependency does not ([sag-wasow-bender-2003] Ch. 15). Stated
on the *passing* gap: if a weak-island construct's mother `GAP|FIRST` is a `prep` (PP), the mother must
be `[GAP ⟨⟩]` — so a PP cannot penetrate, while a `noun` (NP) mother gap is unconstrained and passes. -/
def weakIslandPrinciple : Desc sig :=
  .imp (.and (.sortAssign .colon .weakIslandCxt)
             (.sortAssign (.path [.MTR, .GAP, .FIRST]) .prep))
    (.sortAssign (.path [.MTR, .GAP]) .elist)

/-- **Topicalization is an absolute island** ([sag-2010] (67)): a topicalization construct's mother is
`[GAP ⟨⟩]`. Stated directly on `top-cl` (as [sag-2010] does, not via a generic island supertype the
paper lacks), so a topicalized clause with a second, undischarged gap is rejected. -/
def topIslandPrinciple : Desc sig :=
  .imp (.sortAssign .colon .topCl) (.sortAssign (.path [.MTR, .GAP]) .elist)

/-- **Wh-exclamatives are absolute islands** ([sag-2010] (74)): a wh-exclamative construct's mother is
`[GAP ⟨⟩]`. -/
def whExclIslandPrinciple : Desc sig :=
  .imp (.sortAssign .colon .whExclCl) (.sortAssign (.path [.MTR, .GAP]) .elist)

/-- The **head-modifier construction** ([sag-2010] §6; [pollard-sag-1994] Head-Adjunct Schema): an
adjunct (e.g. a relative clause) modifies a head daughter. The modifier daughter's `MOD` value is
**token-identical** to the head daughter's `CAT` (the modifier selects exactly that category), and the
mother's `CAT` is the head daughter's `CAT` (the Head Feature Principle: modification preserves the
head's category). So a relative clause modifying a noun yields a noun. -/
def headModifierPrinciple : Desc sig :=
  .imp (.sortAssign .colon .headModifierCxt)
    (.and (.pathEq (.path [.MODDTR, .MOD]) (.path [.HDDTR, .CAT]))
      (.pathEq (.path [.MTR, .CAT]) (.path [.HDDTR, .CAT])))

/-- The **inflectional lexical rule** ([sag-2012] (48) `inflectional-cxt`; [pollard-sag-1994] lexical
rules): a category-preserving lexical rule (e.g. passive: V ⤳ V) relates a mother to its input base,
with the mother's `CAT` **token-identical** to the base's `CAT` — the Head Feature Principle for the
lexicon. Two outputs of the same rule from same-category bases share a category, which is why (e.g.)
passivized verbs coordinate. Category-*changing* derivation (nominalization) is a separate
`derivational-cxt`, deferred. -/
def inflectionalPrinciple : Desc sig :=
  .imp (.sortAssign .colon .inflectionalCxt) (.pathEq (.path [.MTR, .CAT]) (.path [.BASE, .CAT]))

/-- The grammar: the filler-head construction (with gap amalgamation), the four clausal-type
principles, the filler-gap construction-specific restrictions (topicalization's verb head, wh-relative's
nominal filler), the generic absolute/weak island constraints, the absolute-island status of
topicalization and wh-exclamatives, the head-modifier construction, and the inflectional lexical rule.
The aux-initial / inversion construction is paper-anchored in `Studies/SagEtAl2020.lean`, which extends
this grammar. -/
def grammar : Grammar sig :=
  [fillerHeadPrinciple, declarativePrinciple, interrogativePrinciple, exclamativePrinciple,
    relativePrinciple, whRelPrinciple, topPrinciple,
    islandPrinciple, weakIslandPrinciple, topIslandPrinciple, whExclIslandPrinciple,
    headModifierPrinciple, inflectionalPrinciple]

/-! ### Multiple inheritance: `ns-wh-int-cl` is a lower bound across the two dimensions -/

/-- `ns-wh-int-cl` sits below **both** `filler-head-cxt` (the headed dimension) and `interrogative-cl`
(the clausal dimension) — the cross-classification of [sag-2010] (80), Fig. 8 (the cross-classification
mechanism being the one [sag-etal-2020] Fig. 5 illustrates for `subj-pred-cl`). -/
theorem nsWhIntCl_inherits :
    (Srt.nsWhIntCl ≤ .fillerHeadCxt) ∧ (Srt.nsWhIntCl ≤ .interrogativeCl) := by decide

/-- All four filler-gap constructions cross-classify: each is below `filler-head-cxt` (so inherits the
filler-head constraints) **and** below the clausal type fixing its semantics ([sag-2010] §5) —
topicalization/declarative, wh-exclamative/exclamative, nonsubject-wh-interrogative/interrogative,
wh-relative/relative. -/
theorem fg_cross_classify :
    ((Srt.topCl ≤ .fillerHeadCxt) ∧ (Srt.topCl ≤ .declarativeCl)) ∧
      ((Srt.whExclCl ≤ .fillerHeadCxt) ∧ (Srt.whExclCl ≤ .exclamativeCl)) ∧
      ((Srt.nsWhIntCl ≤ .fillerHeadCxt) ∧ (Srt.nsWhIntCl ≤ .interrogativeCl)) ∧
      ((Srt.whRelCl ≤ .fillerHeadCxt) ∧ (Srt.whRelCl ≤ .relativeCl)) ∧
      ((Srt.theCl ≤ .fillerHeadCxt) ∧ (Srt.theCl ≤ .declarativeCl)) := by decide

/-! ### Worked constructs

Entities shared by the worked constructs: the construct (`cxt`), its mother (`mtr`) and two daughters
(`hd`, `fl`); the category objects (`npCat`/`vpCat`/`adjCat`/`compCat`, of species `noun`/`verb`/`adj`/
`comp`); the `GAP`-list cells (`g1` the head's gap list, `g2` its tail cell, `nil` the empty list); the
passing second-gap category `c2`; and the semantic object `sem`. A `GAP` list `⟨c⟩` is
`g1[FIRST c, REST nil]`; `⟨c₁, c₂⟩` is `g1[FIRST c₁, REST g2]`, `g2[FIRST c₂, REST nil]`. -/

/-- Entities of the worked constructs. -/
inductive Ent
  | cxt | mtr | hd | fl | npCat | vpCat | adjCat | compCat | g1 | g2 | nil | c2 | sem
  deriving DecidableEq, Fintype, Repr

/-- Common species assignment: the cells are `nelist`, `nil` is `elist`, `c2` defaults to `noun` (NP),
`sem` defaults to `austinean`, `cxt` defaults to `filler-head-cxt`; each model overrides `cxt` (its
construction type) and, where the clausal type demands, `sem`/`c2`. -/
def baseS : Ent → Srt
  | .cxt => .fillerHeadCxt
  | .mtr => .sign | .hd => .sign | .fl => .sign
  | .npCat => .noun | .vpCat => .verb | .adjCat => .adj | .compCat => .comp
  | .g1 => .nelist | .g2 => .nelist | .nil => .elist
  | .c2 => .noun
  | .sem => .austinean

/-- Single-gap filler-head geometry: head `GAP ⟨c⟩` (`g1`), filler binds `c` (token-identical to the
head's first gap `npCat`), mother `GAP ⟨⟩`; verbal head, nonverbal (NP) filler, mother `SEM` `sem`. -/
def singleGapA : Feat → Ent → Option Ent := fun a u => match a, u with
  | .MTR, .cxt => some .mtr
  | .HDDTR, .cxt => some .hd
  | .FILLERDTR, .cxt => some .fl
  | .CAT, .fl => some .npCat
  | .CAT, .hd => some .vpCat
  | .GAP, .hd => some .g1
  | .FIRST, .g1 => some .npCat     -- bound gap = filler category (token identity)
  | .REST, .g1 => some .nil        -- head GAP = ⟨npCat⟩
  | .GAP, .mtr => some .nil         -- mother GAP = head GAP REST = ⟨⟩
  | .SEM, .mtr => some .sem
  | _, _ => none

/-- Two-gap amalgamation geometry: head `GAP ⟨npCat, c2⟩`, the filler binds the first gap, and the
second gap `c2` passes up — mother `GAP ⟨c2⟩` (`g2`). -/
def twoGapA : Feat → Ent → Option Ent := fun a u => match a, u with
  | .MTR, .cxt => some .mtr
  | .HDDTR, .cxt => some .hd
  | .FILLERDTR, .cxt => some .fl
  | .CAT, .fl => some .npCat
  | .CAT, .hd => some .vpCat
  | .GAP, .hd => some .g1
  | .FIRST, .g1 => some .npCat
  | .REST, .g1 => some .g2          -- head GAP = ⟨npCat, c2⟩
  | .FIRST, .g2 => some .c2
  | .REST, .g2 => some .nil
  | .GAP, .mtr => some .g2           -- mother GAP = ⟨c2⟩ (the amalgamated second dependency)
  | .SEM, .mtr => some .sem
  | _, _ => none

/-! ### Construct families (parameterized worked-model builders)

Two parameterized families cover every worked construct: each fixes the carrier `Ent` and the
attribute geometry, exposing the construction sort, the mother's `SEM` type (and, for two gaps, the
passing-gap category) as parameters. The two `Fintype`/`DecidableEq` instances per family are written
once and serve every instantiation, so the named models below are one-line `abbrev`s with **no
per-model boilerplate**. (A universal builder over an arbitrary carrier is blocked by `DecidableEq`
metavariable unification, so the carrier is fixed per family — the `Binding.clause` pattern.) -/

/-- Single-gap construct family: construction sort `cxtSort`, mother `SEM` `semSort`, attribute map `a`
(`singleGapA` for the standard filler-head geometry; a custom `a` for the head/filler variants). -/
def singleConstruct (cxtSort semSort : Srt) (a : Feat → Ent → Option Ent) : Interpretation sig where
  U := Ent
  S := fun u => match u with | .cxt => cxtSort | .sem => semSort | u => baseS u
  A := a
  R := fun e => e.elim

instance (cxtSort semSort : Srt) (a : Feat → Ent → Option Ent) :
    Fintype (singleConstruct cxtSort semSort a).U := inferInstanceAs (Fintype Ent)
instance (cxtSort semSort : Srt) (a : Feat → Ent → Option Ent) :
    DecidableEq (singleConstruct cxtSort semSort a).U := inferInstanceAs (DecidableEq Ent)

/-- Two-gap construct family (amalgamation geometry `twoGapA`): construction sort `cxtSort`, mother
`SEM` `semSort`, passing second-gap category `c2Sort`. -/
def twoGapConstruct (cxtSort semSort c2Sort : Srt) : Interpretation sig where
  U := Ent
  S := fun u => match u with | .cxt => cxtSort | .sem => semSort | .c2 => c2Sort | u => baseS u
  A := twoGapA
  R := fun e => e.elim

instance (cxtSort semSort c2Sort : Srt) :
    Fintype (twoGapConstruct cxtSort semSort c2Sort).U := inferInstanceAs (Fintype Ent)
instance (cxtSort semSort c2Sort : Srt) :
    DecidableEq (twoGapConstruct cxtSort semSort c2Sort).U := inferInstanceAs (DecidableEq Ent)

/-- A well-formed filler-head construct (sort `filler-head-cxt`): nonverbal filler, verbal head, the
head's first `GAP` token-identical to the filler's `CAT`, the (empty) rest amalgamated to the mother. -/
abbrev goodFillerHead : Interpretation sig :=
  singleConstruct .fillerHeadCxt .austinean singleGapA

/-- The well-formed filler-head construct satisfies the grammar (the clausal/island principles are
vacuous — `filler-head-cxt` is below no clausal type or island type). -/
example : goodFillerHead.Models grammar := by decide

/-- Breaking the filler↔gap token identity (filler `CAT` ≠ head `GAP|FIRST`) violates the filler-head
principle. The filler is an AP (nonverbal, so the nonverbal constraint still holds) while the head's
bound gap is an NP — isolating the token-identity failure. -/
abbrev gapMismatch : Interpretation sig :=
  singleConstruct .fillerHeadCxt .austinean
    (fun a u => match a, u with
      | .CAT, .fl => some .adjCat       -- filler AP ≠ head's NP gap
      | _, _ => singleGapA a u)

example : ¬ gapMismatch.Models grammar := by decide

/-! ### The keystone: cross-classification by inheritance

A single `ns-wh-int-cl` construct satisfies the filler-head principle **and** the interrogative
principle — both inherited via `nsWhIntCl_inherits`, neither stipulated on `ns-wh-int-cl`. -/

/-- A well-formed nonsubject wh-interrogative construct (sort `ns-wh-int-cl`): nonverbal filler, verbal
head, filler↔gap token identity (from `filler-head-cxt`), and the mother's `SEM` a question (from
`interrogative-cl`). -/
abbrev goodNsWhInt : Interpretation sig :=
  singleConstruct .nsWhIntCl .question singleGapA

/-- **Keystone.** The `ns-wh-int-cl` construct satisfies the whole grammar — in particular both the
inherited filler-head constraints and the inherited interrogative semantics, from its single sort
assignment (`nsWhIntCl_inherits`). No filler-head or interrogative constraint is restated on
`ns-wh-int-cl`; both fire because its sort lies below both supersorts. -/
example : goodNsWhInt.Models grammar := by decide

/-- The inherited interrogative constraint genuinely binds: an `ns-wh-int-cl` construct whose mother's
`SEM` is austinean (not a question) violates the **inherited** interrogative principle — even though
nothing about interrogativity is stated on `ns-wh-int-cl` directly. -/
abbrev nsWhIntWrongSem : Interpretation sig :=
  singleConstruct .nsWhIntCl .austinean singleGapA    -- austinean ≠ question

example : ¬ nsWhIntWrongSem.Models grammar := by decide

/-! ### The five filler-gap constructions ([sag-2010] §5)

A worked single-gap construct of each sort. By `fg_cross_classify`, each satisfies the inherited
filler-head constraints and its clausal semantics; wh-relative additionally satisfies its nominal-filler
restriction and topicalization its verb-head restriction. Single-gap topicalization and wh-exclamative
also satisfy their absolute-island principle (the one bound gap leaves the mother `[GAP ⟨⟩]`); the
two-gap island theorems below show the constraint genuinely binds. -/

/-- Topicalization ([sag-2010] (61)): a declarative (austinean) filler-head construct, verb head. -/
abbrev goodTopCl : Interpretation sig :=
  singleConstruct .topCl .austinean singleGapA

example : goodTopCl.Models grammar := by decide

/-- Wh-exclamative ([sag-2010] (70)): an exclamative (fact) filler-head construct. -/
abbrev goodWhExcl : Interpretation sig :=
  singleConstruct .whExclCl .fact singleGapA

example : goodWhExcl.Models grammar := by decide

/-- Wh-relative ([sag-2010] (92)): a relative (proposition) filler-head construct whose filler is
nominal (NP/PP). -/
abbrev goodWhRel : Interpretation sig :=
  singleConstruct .whRelCl .proposition singleGapA

example : goodWhRel.Models grammar := by decide

/-- The wh-relative filler restriction genuinely binds: an AP filler (`adj` — nonverbal but not
nominal), token-identical to the head's gap so the filler-head constraint holds, violates the
relative-specific `[CAT nominal]` restriction, so the construct is rejected. -/
abbrev whRelAdjFiller : Interpretation sig :=
  singleConstruct .whRelCl .proposition
    (fun a u => match a, u with
      | .CAT, .fl => some .adjCat       -- AP filler: nonverbal but not nominal
      | .FIRST, .g1 => some .adjCat     -- head's bound gap token-identical to the filler
      | _, _ => singleGapA a u)

example : ¬ whRelAdjFiller.Models grammar := by decide

/-- The-clause ([sag-2010] (108)): an austinean filler-head construct whose head may be a
complementizer-headed CP (`comp`) — distinguishing it from topicalization, whose head must be a verb
projection ((27a) vs (27b)). -/
abbrev goodTheCl : Interpretation sig :=
  singleConstruct .theCl .austinean
    (fun a u => match a, u with
      | .CAT, .hd => some .compCat      -- a CP head, licensed for the-clauses
      | _, _ => singleGapA a u)

example : goodTheCl.Models grammar := by decide

/-- The topicalization head restriction binds: a CP (`comp`) head is verbal (so the inherited
filler-head constraint holds) but violates topicalization's `[CAT verb]` restriction — the very
constraint separating topicalization from the otherwise-identical (austinean) the-clause. -/
abbrev topClCompHead : Interpretation sig :=
  singleConstruct .topCl .austinean
    (fun a u => match a, u with
      | .CAT, .hd => some .compCat
      | _, _ => singleGapA a u)

example : ¬ topClCompHead.Models grammar := by decide

/-! ### Gap amalgamation and islands ([sag-2010] §4–§5.1, after [bouma-malouf-sag-2001])

The two-gap models exercise amalgamation: the filler binds the first gap and the second passes up to the
mother. Whether the second gap survives is what distinguishes a free filler-head construct, an absolute
island, and a (selectively permeable) weak island. These named models ground the island taxonomy
theorems of `Studies/SagWasowBender2003` and `Studies/Sag2010`. -/

/-- **Amalgamation of overlapping dependencies** ([sag-2010] (53), (59)): a generic filler-head head
with two gaps `⟨c₁, c₂⟩`; the filler binds `c₁` and the second gap `c₂` passes up — the mother's `GAP`
is `⟨c₂⟩`. -/
abbrev goodTwoGap : Interpretation sig :=
  twoGapConstruct .fillerHeadCxt .austinean .noun

example : goodTwoGap.Models grammar := by decide

/-- **The absolute-island theorem** ([sag-2010] (67)–(68)). A *second* gap cannot penetrate a generic
absolute island (`island-cxt`): a two-gap head amalgamates a non-empty mother `GAP ⟨c₂⟩`, contradicting
the island's `[GAP ⟨⟩]` — so the construct is rejected. Topicalization is an absolute extraction island
(`topClSecondGap` below), derived from the `[GAP ⟨⟩]` constraint plus amalgamation, not from Subjacency. -/
abbrev islandTwoGap : Interpretation sig :=
  twoGapConstruct .islandCxt .austinean .noun

example : ¬ islandTwoGap.Models grammar := by decide

/-- **NP extraction through a weak island is licensed.** A weak-island construct whose passing (second)
gap is an NP (`noun`) amalgamates a non-empty mother `GAP ⟨NP⟩`; the weak-island antecedent (a `prep`
mother gap) is false, so the constraint is vacuous and the structure is well-formed. -/
abbrev weakIslandNPGap : Interpretation sig :=
  twoGapConstruct .weakIslandCxt .austinean .noun

example : weakIslandNPGap.Models grammar := by decide

/-- **PP extraction through a weak island is blocked.** The same geometry with a `prep` (PP) passing gap
makes the mother `GAP ⟨PP⟩`; the weak-island constraint then forces `[GAP ⟨⟩]`, contradicting the
non-empty mother gap — so the construct is rejected. The NP/PP asymmetry, derived from the constraint,
not stipulated. -/
abbrev weakIslandPPGap : Interpretation sig :=
  twoGapConstruct .weakIslandCxt .austinean .prep

example : ¬ weakIslandPPGap.Models grammar := by decide

/-! ### Islands as a property of the construction type ([sag-2010] §5.1)

The five F-G constructions carry their island status *as constructions*: topicalization and
wh-exclamative are absolute islands (their two-gap variants are rejected), while the nonsubject
wh-interrogative, wh-relative, and the-clause are not (their two-gap variants pass). These ground
`Studies/Sag2010`'s `IsIsland` verdicts as `Models` facts about the construction sorts. -/

/-- **Topicalization blocks a second gap** ([sag-2010] (67)): a `top-cl` construct with two gaps
amalgamates a non-empty mother `GAP`, contradicting `topIslandPrinciple`'s `[GAP ⟨⟩]` — rejected. -/
abbrev topClSecondGap : Interpretation sig :=
  twoGapConstruct .topCl .austinean .noun

example : ¬ topClSecondGap.Models grammar := by decide

/-- **Wh-exclamatives block a second gap** ([sag-2010] (74)): same as topicalization, via
`whExclIslandPrinciple`. -/
abbrev whExclSecondGap : Interpretation sig :=
  twoGapConstruct .whExclCl .fact .noun

example : ¬ whExclSecondGap.Models grammar := by decide

/-- **Nonsubject wh-interrogatives are not islands** ([sag-2010] §5.3): a `ns-wh-int-cl` construct with
a second gap passes — no `[GAP ⟨⟩]` constraint applies, so the second dependency amalgamates freely. -/
abbrev nsWhIntSecondGap : Interpretation sig :=
  twoGapConstruct .nsWhIntCl .question .noun

example : nsWhIntSecondGap.Models grammar := by decide

/-- **Wh-relatives are not constructional islands** ([sag-2010], pace the Complex-NP Constraint): a
`wh-rel-cl` construct with a second gap passes; the residual degradation is processing, not grammar
([hofmeister-sag-2010]). -/
abbrev whRelSecondGap : Interpretation sig :=
  twoGapConstruct .whRelCl .proposition .noun

example : whRelSecondGap.Models grammar := by decide

/-- **The-clauses are not islands**: a `the-cl` construct with a second gap passes. -/
abbrev theClSecondGap : Interpretation sig :=
  twoGapConstruct .theCl .austinean .noun

example : theClSecondGap.Models grammar := by decide

/-! ### Head-modifier constructs ([sag-2010] §6)

A head (e.g. a noun) modified by an adjunct (e.g. a relative clause). The modifier's `MOD` value
selects the head's category and the mother inherits it. These ground `Studies/SagWasowBender2003`'s
relative-clause licensing as `Models` facts: a relative clause modifies a noun and the result is a noun;
a modifier selecting the wrong category is rejected. The relative clause's *internal* gap is the
filler-gap `wh-rel-cl` construct above. -/

/-- Head-modifier construct family: a head daughter of category `noun`, an adjunct (modifier) daughter
whose `MOD` value is the entity `modTarget`, and a mother of the head's category. When `modTarget` is the
head's category (`npCat`) the modifier correctly selects the head. -/
def headModConstruct (modTarget : Ent) : Interpretation sig where
  U := Ent
  S := fun u => match u with | .cxt => .headModifierCxt | u => baseS u
  A := fun a u => match a, u with
    | .MTR, .cxt => some .mtr
    | .HDDTR, .cxt => some .hd
    | .MODDTR, .cxt => some .fl        -- the modifier (e.g. a relative clause)
    | .CAT, .hd => some .npCat          -- head is a noun
    | .CAT, .mtr => some .npCat          -- mother category = head's (preserved)
    | .MOD, .fl => some modTarget        -- the modifier selects `modTarget`
    | _, _ => none
  R := fun e => e.elim

instance (modTarget : Ent) : Fintype (headModConstruct modTarget).U := inferInstanceAs (Fintype Ent)
instance (modTarget : Ent) : DecidableEq (headModConstruct modTarget).U :=
  inferInstanceAs (DecidableEq Ent)

/-- A relative clause modifying a noun: the modifier's `MOD` is the noun head's category, and the mother
is a noun — modification preserves the head's category. -/
abbrev goodHeadMod : Interpretation sig := headModConstruct .npCat

example : goodHeadMod.Models grammar := by decide

/-- The head-modifier constraint binds: a modifier selecting a *verb* category does not modify the noun
head, so the construct is rejected. -/
abbrev headModWrongCat : Interpretation sig := headModConstruct .vpCat

example : ¬ headModWrongCat.Models grammar := by decide

/-! ### Inflectional lexical-rule constructs ([sag-2012] (48))

A category-preserving lexical rule (e.g. passive) relating an output mother to its input base; the
mother's `CAT` is the base's `CAT`. These ground `Studies/Mueller2013`'s claim that HPSG lexical rules
preserve category (so e.g. passivized verbs coordinate). -/

/-- An inflectional lexical-rule construct family: mother and base of category `baseCat`. When the
mother's category equals the base's (the entity is shared), the rule is category-preserving. -/
def inflectionalConstruct (mtrCat : Ent) : Interpretation sig where
  U := Ent
  S := fun u => match u with | .cxt => .inflectionalCxt | u => baseS u
  A := fun a u => match a, u with
    | .MTR, .cxt => some .mtr
    | .BASE, .cxt => some .hd          -- the input base (e.g. the active verb)
    | .CAT, .hd => some .vpCat          -- base is a verb
    | .CAT, .mtr => some mtrCat          -- mother category
    | _, _ => none
  R := fun e => e.elim

instance (mtrCat : Ent) : Fintype (inflectionalConstruct mtrCat).U := inferInstanceAs (Fintype Ent)
instance (mtrCat : Ent) : DecidableEq (inflectionalConstruct mtrCat).U :=
  inferInstanceAs (DecidableEq Ent)

/-- A passive-like inflectional rule: the output verb has the base verb's category (V ⤳ V) — category
preserved, so the output coordinates with other same-category outputs. -/
abbrev goodInflectional : Interpretation sig := inflectionalConstruct .vpCat

example : goodInflectional.Models grammar := by decide

/-- The category-preservation constraint binds: a lexical rule whose output category differs from the
base's (here a noun output from a verb base) violates `inflectionalPrinciple`. -/
abbrev inflectionalWrongCat : Interpretation sig := inflectionalConstruct .npCat

example : ¬ inflectionalWrongCat.Models grammar := by decide

/-- Entities of a two-step lexical-rule chain (e.g. double passivization, [mueller-2013] §11): two
inflectional constructs where the first's output (`mid`) is the second's input base. -/
inductive ChainEnt
  | cxt1 | cxt2 | base0 | mid | out | vCat
  deriving DecidableEq, Fintype, Repr

/-- **Lexical rules iterate freely, preserving category** ([mueller-2013] §11): a chain of two
inflectional rules — the first maps `base0 ⤳ mid`, the second `mid ⤳ out` — keeps the category
throughout (`out`'s `CAT` = `base0`'s, via two `inflectionalPrinciple` steps), so double passivization
works with no phrasal machinery. -/
def iterationChain : Interpretation sig where
  U := ChainEnt
  S := fun u => match u with
    | .cxt1 => .inflectionalCxt | .cxt2 => .inflectionalCxt
    | .base0 => .sign | .mid => .sign | .out => .sign | .vCat => .verb
  A := fun a u => match a, u with
    | .MTR, .cxt1 => some .mid  | .BASE, .cxt1 => some .base0
    | .MTR, .cxt2 => some .out  | .BASE, .cxt2 => some .mid
    | .CAT, .base0 => some .vCat | .CAT, .mid => some .vCat | .CAT, .out => some .vCat
    | _, _ => none
  R := fun e => e.elim

instance : Fintype iterationChain.U := inferInstanceAs (Fintype ChainEnt)
instance : DecidableEq iterationChain.U := inferInstanceAs (DecidableEq ChainEnt)

example : iterationChain.Models grammar := by decide

end HPSG.Construction
