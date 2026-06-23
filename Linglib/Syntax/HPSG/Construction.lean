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
fn. 17; the "category restriction operation" of [sag-etal-2020]).

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
verbal, filler nonverbal, filler↔gap token identity) **and** the interrogative semantics (`MTR` `SEM` a
question) from one sort assignment — the keystone theorem below.

## Scope

This file is the **substrate**: the type hierarchy, the cross-classification keystone, and **all five
filler-gap constructions** ([sag-2010] §5: topicalization, wh-exclamative, nonsubject wh-interrogative,
wh-relative, the-clause), distinguished by their clausal semantics, wh-relative's nominal filler, and
the topicalization/the-clause head contrast (verb vs CP). The hierarchy also carries the
`aux-initial-cxt`/`interrogative-SAI` sort nodes and the `INV` feature ([sag-etal-2020] Fig. 6); the
**inversion construction**'s own principle and worked constructs are paper-anchored in
`Studies/SagEtAl2020.lean`, which consumes this substrate as a second study — the two-consumer
justification for the theory-layer home.

n-ary `DTRS`, GAP amalgamation, islands, the `WH`/`REL`/`IC`/`VFORM` finer variation, and compositional
`SEM` are deferred. Decidability stays inside `Models` over fixed finite interpretations (Kepser 2004:
full RSRL model-checking is undecidable).
-/

namespace HPSG.Construction

open HPSG.RSRL

/-! ### Sorts: categories, semantic types, signs, and the construct/clausal hierarchy -/

/-- Sorts of the fragment: a category hierarchy, a semantic-type hierarchy, `sign`, and the
[sag-etal-2020] construct (Fig. 6) and clausal (Fig. 7) type hierarchies, with `ns-wh-int-cl` as the
worked cross-classified subtype ([sag-2010] (80), Fig. 8). -/
inductive FHSort
  | top
  -- category hierarchy (filler-head-cxt keys on verbal/nonverbal; wh-rel on nominal; the-cl on comp)
  | cat | verbal | nonverbal | verb | comp | nominal | noun | prep | adj
  -- semantic-type hierarchy (clause types key on the MTR's SEM type)
  | semType | austinean | question | fact | proposition
  -- inversion-value hierarchy (aux-initial-cxt keys on the head's INV value, [sag-etal-2020] (39))
  | invVal | invPlus | invMinus
  -- signs
  | sign
  -- construct backbone (Fig. 6; filler-head-cxt per [sag-2010] Fig. A2): filler-head-cxt and
  -- aux-initial-cxt are sibling headed-cxt subtypes
  | construct | phrasalCxt | lexicalCxt | headedCxt | clause | fillerHeadCxt | auxInitialCxt
  -- clausal hierarchy (Fig. 7)
  | coreCl | relativeCl | declarativeCl | interrogativeCl | exclamativeCl
  -- the filler-gap constructions ([sag-2010] §5) and the interrogative SAI ([sag-etal-2020]), each
  -- cross-classifying a clausal type
  | topCl | whExclCl | nsWhIntCl | whRelCl | theCl | interrogativeSAI
  deriving DecidableEq, Fintype, Repr

/-- Subsumption (`fhLe a b` = "`a` at least as specific as `b`"). **Must be written transitively
closed by hand** — every transitive consequence is listed explicitly (e.g. `noun ≤ nominal` *and*
`noun ≤ nonverbal` *and* `noun ≤ cat`), and the `PartialOrder` instance's `le_trans`/`le_antisymm`
`decide`s verify the closure is correct and acyclic. When adding a sort or edge, add all its downstream
transitive arms or `le_trans` fails. The two arms for `nsWhIntCl` — below both `fillerHeadCxt` and
`interrogativeCl` — are the multiple inheritance. -/
def fhLe : FHSort → FHSort → Bool
  | _, .top => true
  -- categories (nonverbal > {nominal, adj}; nominal > {noun, prep})
  | .verbal, .cat => true
  | .nonverbal, .cat => true
  | .verb, .verbal => true | .verb, .cat => true
  | .comp, .verbal => true | .comp, .cat => true
  | .nominal, .nonverbal => true | .nominal, .cat => true
  | .noun, .nominal => true | .noun, .nonverbal => true | .noun, .cat => true
  | .prep, .nominal => true | .prep, .nonverbal => true | .prep, .cat => true
  | .adj, .nonverbal => true | .adj, .cat => true
  -- semantic types
  | .austinean, .semType => true
  | .question, .semType => true
  | .fact, .semType => true
  | .proposition, .semType => true
  -- inversion values
  | .invPlus, .invVal => true
  | .invMinus, .invVal => true
  -- construct backbone
  | .phrasalCxt, .construct => true
  | .lexicalCxt, .construct => true
  | .headedCxt, .phrasalCxt => true | .headedCxt, .construct => true
  | .clause, .phrasalCxt => true | .clause, .construct => true
  | .fillerHeadCxt, .headedCxt => true | .fillerHeadCxt, .phrasalCxt => true
  | .fillerHeadCxt, .construct => true
  | .auxInitialCxt, .headedCxt => true | .auxInitialCxt, .phrasalCxt => true
  | .auxInitialCxt, .construct => true
  -- clausal
  | .coreCl, .clause => true | .coreCl, .phrasalCxt => true | .coreCl, .construct => true
  | .relativeCl, .clause => true | .relativeCl, .phrasalCxt => true | .relativeCl, .construct => true
  | .declarativeCl, .coreCl => true | .declarativeCl, .clause => true
  | .declarativeCl, .phrasalCxt => true | .declarativeCl, .construct => true
  | .interrogativeCl, .coreCl => true | .interrogativeCl, .clause => true
  | .interrogativeCl, .phrasalCxt => true | .interrogativeCl, .construct => true
  | .exclamativeCl, .coreCl => true | .exclamativeCl, .clause => true
  | .exclamativeCl, .phrasalCxt => true | .exclamativeCl, .construct => true
  -- filler-gap constructions: each < filler-head-cxt (+ headed-cxt) AND its clausal type ([sag-2010]
  -- §5). Note relative-cl is directly under clause (Fig. 7), so whRelCl does not pass through core-cl.
  | .topCl, .fillerHeadCxt => true | .topCl, .headedCxt => true
  | .topCl, .declarativeCl => true | .topCl, .coreCl => true
  | .topCl, .clause => true | .topCl, .phrasalCxt => true | .topCl, .construct => true
  | .whExclCl, .fillerHeadCxt => true | .whExclCl, .headedCxt => true
  | .whExclCl, .exclamativeCl => true | .whExclCl, .coreCl => true
  | .whExclCl, .clause => true | .whExclCl, .phrasalCxt => true | .whExclCl, .construct => true
  | .nsWhIntCl, .fillerHeadCxt => true | .nsWhIntCl, .headedCxt => true
  | .nsWhIntCl, .interrogativeCl => true | .nsWhIntCl, .coreCl => true
  | .nsWhIntCl, .clause => true | .nsWhIntCl, .phrasalCxt => true | .nsWhIntCl, .construct => true
  | .whRelCl, .fillerHeadCxt => true | .whRelCl, .headedCxt => true
  | .whRelCl, .relativeCl => true
  | .whRelCl, .clause => true | .whRelCl, .phrasalCxt => true | .whRelCl, .construct => true
  | .theCl, .fillerHeadCxt => true | .theCl, .headedCxt => true
  | .theCl, .declarativeCl => true | .theCl, .coreCl => true
  | .theCl, .clause => true | .theCl, .phrasalCxt => true | .theCl, .construct => true
  -- the interrogative SAI: < aux-initial-cxt (headed dim.) AND < interrogative-cl (clausal)
  | .interrogativeSAI, .auxInitialCxt => true | .interrogativeSAI, .headedCxt => true
  | .interrogativeSAI, .interrogativeCl => true | .interrogativeSAI, .coreCl => true
  | .interrogativeSAI, .clause => true | .interrogativeSAI, .phrasalCxt => true
  | .interrogativeSAI, .construct => true
  | a, b => decide (a = b)

-- The transitivity check is `decide` over `FHSort³`; the proof term's nesting depth is intrinsic to
-- the hierarchy *size* (the fold over `|FHSort|³` triples), so it exceeds the default elaborator
-- recursion depth of 512 (a stack limit, not a compute budget — distinct from `maxHeartbeats`).
-- Empirically the default fails and ~1000 suffices; this scales with `|FHSort|`, so adding sorts may
-- require a bump. (An edge-list/closure encoding of `fhLe` would not help — the depth is the `decide`
-- fold, not `fhLe`'s match.)
set_option maxRecDepth 1000 in
instance : PartialOrder FHSort :=
  partialOrderOfBool fhLe (by decide) (by decide) (by decide)

instance : DecidableLE FHSort := fun a b => inferInstanceAs (Decidable (fhLe a b = true))

/-! ### Attributes and the signature -/

/-- Attributes: a construct's mother (`MTR`) and head/filler daughters (`HDDTR`/`FILLERDTR`); a sign's
`CAT`, (single) `GAP` category, and `SEM` type. -/
inductive FHAttr
  | MTR | HDDTR | FILLERDTR | CAT | GAP | SEM | INV
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
  | .fillerHeadCxt, .MTR => some .sign
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
  -- HDDTR is common to all headed constructs; FILLERDTR is specific to filler-head-cxt (an
  -- aux-initial construct has head + valent daughters, no filler)
  | .headedCxt, .HDDTR => some .sign
  | .auxInitialCxt, .HDDTR => some .sign
  | .interrogativeSAI, .HDDTR => some .sign
  | .fillerHeadCxt, .HDDTR => some .sign
  | .fillerHeadCxt, .FILLERDTR => some .sign
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
  | .sign, .CAT => some .cat
  | .sign, .GAP => some .cat
  | .sign, .SEM => some .semType
  | .sign, .INV => some .invVal
  | _, _ => none

-- Appropriateness values never refine down this hierarchy (a sort and its subsorts carry the *same*
-- value for an attribute), so the inherited value is `τ₁` itself. Proving this propagation over just
-- `(σ₁, σ₂, α)` — without the `τ₁` quantifier or the `∃`-search — keeps the `decide` within budget.
private theorem fhApprop_propagates : ∀ (σ₁ σ₂ : FHSort) (α : FHAttr),
    σ₂ ≤ σ₁ → (fhApprop σ₁ α).isSome = true → fhApprop σ₂ α = fhApprop σ₁ α := by decide

private theorem fhApprop_inh : ∀ (σ₁ σ₂ : FHSort) (α : FHAttr) (τ₁ : FHSort),
    σ₂ ≤ σ₁ → fhApprop σ₁ α = some τ₁ → ∃ τ₂, fhApprop σ₂ α = some τ₂ ∧ τ₂ ≤ τ₁ := by
  intro σ₁ σ₂ α τ₁ hle happ
  have hsome : (fhApprop σ₁ α).isSome = true := by rw [happ]; rfl
  exact ⟨τ₁, (fhApprop_propagates σ₁ σ₂ α hle hsome).trans happ, le_refl τ₁⟩

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

/-- The **filler-head construction** ([sag-2010] (58); placed under `headed-cxt` in [sag-2010] Fig. A2):
the head daughter is `[CAT verbal]`, and the filler's category is **token-identical** (`pathEq`) to the
head daughter's `GAP` value — the filler-gap structure sharing. The `[CAT nonverbal]` filler is, in the
paper, a per-subtype generalization (each F-G construction's (25)-style parameter, refined to `nominal`
for wh-relative, (25b)) rather than a constraint of (58) itself; it is stated here once on the supertype
because every subtype satisfies it. -/
def fillerHeadPrinciple : Desc fhSig :=
  .imp (.sortAssign .colon .fillerHeadCxt)
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

/-- The **wh-relative construction**'s distinguishing constraint ([sag-2010] (92), (25b)): unlike the
other filler-gap constructions (nonverbal filler), the relative filler is `[CAT nominal]` — an NP or PP
(`nominal` resolves to `noun`/`prep`), excluding AP/AdvP. -/
def whRelPrinciple : Desc fhSig :=
  .imp (.sortAssign .colon .whRelCl) (.sortAssign (.path [.FILLERDTR, .CAT]) .nominal)

/-- The **topicalization construction**'s distinguishing constraint ([sag-2010] (61), (27a)): its head
daughter is a `[CAT verb]` projection (an S), excluding the complementizer-headed CP that the
otherwise-similar (also austinean) the-clause allows ((27b): the-clause head is S or CP). -/
def topPrinciple : Desc fhSig :=
  .imp (.sortAssign .colon .topCl) (.sortAssign (.path [.HDDTR, .CAT]) .verb)

/-- The grammar: the filler-head construction, the four clausal-type principles, and the
filler-gap construction-specific restrictions (topicalization's verb head, wh-relative's nominal
filler). The aux-initial / inversion construction is paper-anchored in `Studies/SagEtAl2020.lean`,
which extends this grammar. -/
def fhGrammar : Grammar fhSig :=
  [fillerHeadPrinciple, declarativePrinciple, interrogativePrinciple, exclamativePrinciple,
    relativePrinciple, whRelPrinciple, topPrinciple]

/-! ### Multiple inheritance: `ns-wh-int-cl` is a lower bound across the two dimensions -/

/-- `ns-wh-int-cl` sits below **both** `filler-head-cxt` (the headed dimension) and `interrogative-cl`
(the clausal dimension) — the cross-classification of [sag-2010] (80), Fig. 8 (the cross-classification
mechanism being the one [sag-etal-2020] Fig. 5 illustrates for `subj-pred-cl`). -/
theorem nsWhIntCl_inherits :
    (FHSort.nsWhIntCl ≤ .fillerHeadCxt) ∧ (FHSort.nsWhIntCl ≤ .interrogativeCl) := by decide

/-- All four filler-gap constructions cross-classify: each is below `filler-head-cxt` (so inherits the
filler-head constraints) **and** below the clausal type fixing its semantics ([sag-2010] §5) —
topicalization/declarative, wh-exclamative/exclamative, nonsubject-wh-interrogative/interrogative,
wh-relative/relative. -/
theorem fg_cross_classify :
    ((FHSort.topCl ≤ .fillerHeadCxt) ∧ (FHSort.topCl ≤ .declarativeCl)) ∧
      ((FHSort.whExclCl ≤ .fillerHeadCxt) ∧ (FHSort.whExclCl ≤ .exclamativeCl)) ∧
      ((FHSort.nsWhIntCl ≤ .fillerHeadCxt) ∧ (FHSort.nsWhIntCl ≤ .interrogativeCl)) ∧
      ((FHSort.whRelCl ≤ .fillerHeadCxt) ∧ (FHSort.whRelCl ≤ .relativeCl)) ∧
      ((FHSort.theCl ≤ .fillerHeadCxt) ∧ (FHSort.theCl ≤ .declarativeCl)) := by decide

/-! ### Worked constructs -/

/-- Entities shared by the worked constructs: the construct, its mother and two daughters, two
category objects, and one semantic object. -/
inductive Ent
  | cxt | mtr | hd | fl | npCat | vpCat | adjCat | compCat | sem
  deriving DecidableEq, Fintype, Repr

/-- A well-formed filler-head construct (sort `filler-head-cxt`): nonverbal filler, verbal head, and
the head's `GAP` token-identical to the filler's `CAT`. -/
def goodFillerHead : Interpretation fhSig where
  U := Ent
  S := fun
    | .cxt => .fillerHeadCxt
    | .hd => .sign
    | .fl => .sign
    | .npCat => .noun
    | .vpCat => .verb
    | .adjCat => .adj
    | .compCat => .comp
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
`filler-head-cxt` is not below any clausal type). -/
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
verbal head, filler↔gap token identity (from `filler-head-cxt`), and the mother's `SEM` a question
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
    | .adjCat => .adj
    | .compCat => .comp
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
    | .adjCat => .adj
    | .compCat => .comp
    | .sem => .austinean    -- not a question
  A := goodNsWhInt.A
  R := fun e => e.elim

instance : Fintype nsWhIntWrongSem.U := inferInstanceAs (Fintype Ent)
instance : DecidableEq nsWhIntWrongSem.U := inferInstanceAs (DecidableEq Ent)

example : ¬ nsWhIntWrongSem.Models fhGrammar := by decide

/-! ### The five filler-gap constructions ([sag-2010] §5)

A worked construct of each sort. By `fg_cross_classify`, each satisfies the inherited filler-head
constraints and its clausal semantics; wh-relative additionally satisfies its nominal-filler
restriction and topicalization its verb-head restriction. The constructions are distinguished here by
their clausal `SEM` (austinean / fact / question / proposition), wh-relative's nominal filler, and the
topicalization-vs-the-clause head contrast (verb vs CP); the finer parametric variation (`WH`/`REL`,
head `IC`/`INV`/`VFORM`) is deferred. -/

/-- Topicalization ([sag-2010] (61)): a declarative (austinean) filler-head construct. -/
def goodTopCl : Interpretation fhSig where
  U := Ent
  S := fun
    | .cxt => .topCl
    | .mtr => .sign | .hd => .sign | .fl => .sign
    | .npCat => .noun | .vpCat => .verb | .adjCat => .adj | .compCat => .comp
    | .sem => .austinean
  A := goodNsWhInt.A
  R := fun e => e.elim

instance : Fintype goodTopCl.U := inferInstanceAs (Fintype Ent)
instance : DecidableEq goodTopCl.U := inferInstanceAs (DecidableEq Ent)

example : goodTopCl.Models fhGrammar := by decide

/-- Wh-exclamative ([sag-2010] (70)): an exclamative (fact) filler-head construct. -/
def goodWhExcl : Interpretation fhSig where
  U := Ent
  S := fun
    | .cxt => .whExclCl
    | .mtr => .sign | .hd => .sign | .fl => .sign
    | .npCat => .noun | .vpCat => .verb | .adjCat => .adj | .compCat => .comp
    | .sem => .fact
  A := goodNsWhInt.A
  R := fun e => e.elim

instance : Fintype goodWhExcl.U := inferInstanceAs (Fintype Ent)
instance : DecidableEq goodWhExcl.U := inferInstanceAs (DecidableEq Ent)

example : goodWhExcl.Models fhGrammar := by decide

/-- Wh-relative ([sag-2010] (92)): a relative (proposition) filler-head construct whose filler is
nominal (NP/PP). -/
def goodWhRel : Interpretation fhSig where
  U := Ent
  S := fun
    | .cxt => .whRelCl
    | .mtr => .sign | .hd => .sign | .fl => .sign
    | .npCat => .noun | .vpCat => .verb | .adjCat => .adj | .compCat => .comp
    | .sem => .proposition
  A := goodNsWhInt.A
  R := fun e => e.elim

instance : Fintype goodWhRel.U := inferInstanceAs (Fintype Ent)
instance : DecidableEq goodWhRel.U := inferInstanceAs (DecidableEq Ent)

example : goodWhRel.Models fhGrammar := by decide

/-- The wh-relative filler restriction genuinely binds: an AP filler (`adj` — nonverbal but not
nominal) satisfies the inherited filler-head constraint (and its token identity) yet violates the
relative-specific `[CAT nominal]` restriction, so the construct is rejected. -/
def whRelAdjFiller : Interpretation fhSig where
  U := Ent
  S := goodWhRel.S
  A := fun a u => match a, u with
    | .MTR, .cxt => some .mtr
    | .HDDTR, .cxt => some .hd
    | .FILLERDTR, .cxt => some .fl
    | .SEM, .mtr => some .sem
    | .CAT, .fl => some .adjCat    -- AP filler: nonverbal but not nominal
    | .CAT, .hd => some .vpCat
    | .GAP, .hd => some .adjCat     -- token-identical to the filler, so only the nominal restriction fails
    | _, _ => none
  R := fun e => e.elim

instance : Fintype whRelAdjFiller.U := inferInstanceAs (Fintype Ent)
instance : DecidableEq whRelAdjFiller.U := inferInstanceAs (DecidableEq Ent)

example : ¬ whRelAdjFiller.Models fhGrammar := by decide

/-- The-clause ([sag-2010] (108)): an austinean filler-head construct whose head may be a
complementizer-headed CP (`comp`) — distinguishing it from topicalization, whose head must be a verb
projection ((27a) vs (27b)). -/
def goodTheCl : Interpretation fhSig where
  U := Ent
  S := fun
    | .cxt => .theCl
    | .mtr => .sign | .hd => .sign | .fl => .sign
    | .npCat => .noun | .vpCat => .verb | .adjCat => .adj | .compCat => .comp
    | .sem => .austinean
  A := fun a u => match a, u with
    | .MTR, .cxt => some .mtr
    | .HDDTR, .cxt => some .hd
    | .FILLERDTR, .cxt => some .fl
    | .SEM, .mtr => some .sem
    | .CAT, .fl => some .npCat
    | .CAT, .hd => some .compCat    -- a CP head, licensed for the-clauses
    | .GAP, .hd => some .npCat
    | _, _ => none
  R := fun e => e.elim

instance : Fintype goodTheCl.U := inferInstanceAs (Fintype Ent)
instance : DecidableEq goodTheCl.U := inferInstanceAs (DecidableEq Ent)

example : goodTheCl.Models fhGrammar := by decide

/-- The topicalization head restriction binds: a CP (`comp`) head is verbal (so the inherited
filler-head constraint holds) but violates topicalization's `[CAT verb]` restriction — the very
constraint separating topicalization from the otherwise-identical (austinean) the-clause. -/
def topClCompHead : Interpretation fhSig where
  U := Ent
  S := fun
    | .cxt => .topCl
    | .mtr => .sign | .hd => .sign | .fl => .sign
    | .npCat => .noun | .vpCat => .verb | .adjCat => .adj | .compCat => .comp
    | .sem => .austinean
  A := goodTheCl.A
  R := fun e => e.elim

instance : Fintype topClCompHead.U := inferInstanceAs (Fintype Ent)
instance : DecidableEq topClCompHead.U := inferInstanceAs (DecidableEq Ent)

example : ¬ topClCompHead.Models fhGrammar := by decide

end HPSG.Construction
