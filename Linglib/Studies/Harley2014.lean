/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.DM.VocabularyInsertion
import Linglib.Morphology.DM.Allosemy
import Linglib.Morphology.Root.Certificates

/-!
# Harley (2014): roots as abstract indices
[harley-2014] [marantz-1997] [halle-marantz-1993] [bobaljik-2008]

[harley-2014] "On the identity of roots" argues that a root terminal
(DM's List 1) is neither phonologically nor semantically individuated: it
is an **abstract index**, a syntactic atom identified only by its position
in the vocabulary, with its form supplied by List 2 (Vocabulary Insertion)
and its meaning by List 3 (the Encyclopedia). The argument is negative on
both flanks:

* **Phonological identification fails** (§2.1–2.2). Hiaki has suppletive
  roots — one root, two phonologically unrelated forms competing under the
  Elsewhere Condition. If a root were identified by its phonology (√kæt),
  root suppletion would be incoherent.
* **Semantic identification fails** (§2.3–2.4). Cran-morphs (*cahoot*) have
  a meaning only inside one licensing frame and none elsewhere, so a root
  cannot be a Fodorian atomic concept either.

What survives is the **index**: `RootIndex := ℕ` here, a `√322`-style
meaningless tag. Distinctness of roots is then true by typing — distinct
indices are distinct roots — which is exactly what lets `√tenne` block
`√vuite` at *its* index without blocking a different intransitive root
(§2.1, Marantz's thought experiment).

## This file

* `vocabulary` — the Hiaki suppletive List-2 entries ([harley-2014] (3),
  (26), (27)), keyed by `RootIndex`, resolved by the shared DM engine
  `Morphology.DM.VI.vocabularyInsert`.
* Selection theorems — the engine picks the attested form per context.
* `suppletion_ignores_ergative` — the §3.3 ergative-absolutive
  generalization: suppletion tracks the **internal (absolutive)**
  argument's number and is blind to the external (ergative) argument.
* `run_index_two_forms` — one index, two exponents: phonological
  individuation would split the root (§2.1–2.2).
* `cahoot_no_elsewhere` — the cran-morph has an interpretation only in its
  licensing context and none elsewhere (§2.3), stated on the LF side with
  the allosemy exponence engine (`selectBy`, `no Elsewhere` = `none`).

## The `vuite`/`tenne` Elsewhere direction (fn. 16)

The paper's first pass (7) writes the plural `tenne` as the *conditioned*
form (`/ [DP-pl]`) and `vuite` as Elsewhere. Footnote 16 corrects this: in
the Hiaki impersonal passive the sole argument is syntactically absent and
so number-unspecified, and the root then surfaces as `tenne`, **not** as
singular `vuite`. So `tenne` is the true Elsewhere form and `vuite` is
conditioned by a singular internal argument. We encode the considered (fn.
16) analysis: `vuite / [absolutive-sg]`, `tenne` elsewhere (plural *and*
number-unspecified).
-/

namespace Harley2014

open Morphology.DM.VI
open Morphology.DM.Allosemy (SyntacticContext AllosemicEntry AllosemicHead)
open Morphology.Exponence (selectBy realize)

/-! ### List 1: roots as abstract indices -/

/-- A List-1 root index: a meaningless `√`-style tag ([harley-2014] §2.4).
Individuation is by index alone — distinct indices, distinct roots — so
the phonological form (List 2) and the interpretation (List 3) are free to
vary without identifying the root. -/
abbrev RootIndex := ℕ

/-- `√322`: the Hiaki root realized `vuite`/`tenne` 'run' ([harley-2014] (14)). -/
def runRoot : RootIndex := 322
/-- `√401`: the root realized `weye`/`kaate` 'walk' ([harley-2014] (26)). -/
def walkRoot : RootIndex := 401
/-- `√402`: the root realized `mea`/`sua` 'kill' ([harley-2014] (27)). -/
def killRoot : RootIndex := 402
/-- `√500`: a non-suppletive intransitive root ('sing', *bwiika*), used to
show the suppletive rules do not block insertion at other indices. -/
def singRoot : RootIndex := 500

/-! ### The conditioning context

Suppletion is conditioned by number, but — crucially for §3.3 — by the
number of the **absolutive** (internal) argument: the sole argument of an
intransitive, the object of a transitive. The ergative (external) argument
never conditions it. -/

/-- Grammatical number of an argument. `unspecified` is the number-neutral
case of [harley-2014] fn. 16 (the impersonal passive), which surfaces as
the Elsewhere form. -/
inductive Number where
  | sg
  | pl
  | unspecified
  deriving DecidableEq, Repr

/-- The morphosyntactic context a suppletive root is spelled out in: the
number of its absolutive (internal) argument, plus — for a transitive —
the number of its ergative (external) argument, which is never consulted. -/
structure Ctx where
  /-- Number of the absolutive (internal) argument — the conditioning one. -/
  absNumber : Number
  /-- Number of the ergative (external) argument, `none` if intransitive.
      Never conditions suppletion (§3.3). -/
  ergNumber : Option Number := none
  deriving DecidableEq, Repr

/-! ### List 2: the suppletive Vocabulary Items

Each root index has a singular-conditioned entry (specificity 1) and an
Elsewhere entry (specificity 0); the DM engine's Elsewhere resolution
(`vocabularyInsert`) selects the more specific matching rule. -/

/-- A singular-conditioned suppletive entry for `idx`. -/
private def sgEntry (form : String) (idx : RootIndex) : VocabItem Ctx RootIndex where
  exponent := form
  contextMatch := fun c => decide (c.absNumber = Number.sg)
  rootMatch := some (· == idx)
  specificity := 1

/-- An Elsewhere suppletive entry for `idx` (matches any context). -/
private def elseEntry (form : String) (idx : RootIndex) : VocabItem Ctx RootIndex where
  exponent := form
  contextMatch := fun _ => true
  rootMatch := some (· == idx)
  specificity := 0

/-- The Hiaki suppletive vocabulary ([harley-2014] (3), (26), (27)): three
suppletive roots, each an sg-conditioned form competing with an Elsewhere
form, all keyed by `RootIndex`. -/
def vocabulary : List (VocabItem Ctx RootIndex) :=
  [ sgEntry "vuite" runRoot,  elseEntry "tenne" runRoot,
    sgEntry "weye"  walkRoot, elseEntry "kaate" walkRoot,
    sgEntry "mea"   killRoot, elseEntry "sua"   killRoot ]

instance : Morphology.Exponence.DecidableApplies (VocabItem Ctx RootIndex) (Ctx × RootIndex) :=
  fun c vi => inferInstanceAs (Decidable (vi.matches c.1 c.2 = true))

/-- Spell out root `idx` in context `ctx` by Elsewhere competition over
`vocabulary`, resolved by the shared exponence engine (`Exponence.realize`
on the `VocabItem` specificity score) — the same selection engine as the
allosemy LF side below. -/
def insert (ctx : Ctx) (idx : RootIndex) : Option String :=
  realize VocabItem.specificity vocabulary (ctx, idx)

/-! ### Selection: the engine picks the attested form -/

/-- Singular subject → `vuite` ([harley-2014] (1a)). -/
theorem run_sg : insert ⟨.sg, none⟩ runRoot = some "vuite" := by decide

/-- Plural subject → `tenne` ([harley-2014] (1b)). -/
theorem run_pl : insert ⟨.pl, none⟩ runRoot = some "tenne" := by decide

/-- Number-unspecified (impersonal passive) → `tenne`, the true Elsewhere
form ([harley-2014] fn. 16): the diagnostic that `tenne`, not `vuite`, is
Elsewhere. -/
theorem run_impersonal : insert ⟨.unspecified, none⟩ runRoot = some "tenne" := by decide

/-- Singular subject → `weye` ([harley-2014] (26a)). -/
theorem walk_sg : insert ⟨.sg, none⟩ walkRoot = some "weye" := by decide

/-- Plural subject → `kaate` ([harley-2014] (26b)). -/
theorem walk_pl : insert ⟨.pl, none⟩ walkRoot = some "kaate" := by decide

/-- Singular object → `mea`, regardless of the (plural) subject
([harley-2014] (27a)). -/
theorem kill_sgObj : insert ⟨.sg, some .pl⟩ killRoot = some "mea" := by decide

/-- Plural object → `sua`, regardless of the (singular) subject
([harley-2014] (27b)). -/
theorem kill_plObj : insert ⟨.pl, some .sg⟩ killRoot = some "sua" := by decide

/-! ### §3.3 The ergative-absolutive conditioning generalization -/

/-- **Suppletion tracks the absolutive argument** ([harley-2014] §3.3): the
selected form depends only on the internal (absolutive) argument's number;
the external (ergative) argument's number is never consulted. This is the
ergative-absolutive distribution of suppletive agreement — the challenge to
[bobaljik-2008]'s marked-case generalization the paper raises. -/
theorem suppletion_ignores_ergative (n : Number) (e e' : Option Number) (i : RootIndex) :
    insert ⟨n, e⟩ i = insert ⟨n, e'⟩ i := rfl

/-! ### §2.1 Individuation is not phonological -/

/-- **One index, two forms.** The single root `√322` is realized by two
phonologically unrelated exponents (`vuite` vs `tenne`). Any identification
of the root by its phonological form would split it in two, making
suppletion incoherent ([harley-2014] §2.2, contra Borer 2009). -/
theorem run_index_two_forms :
    insert ⟨.sg, none⟩ runRoot ≠ insert ⟨.pl, none⟩ runRoot := by decide

/-- **The suppletive rule is index-local** ([harley-2014] §2.1, Marantz's
thought experiment): `tenne` competes only at `√322`, so it does not block
insertion at a different intransitive root — a non-suppletive `√500`
(*bwiika* 'sing') gets no exponent from this vocabulary. This is why List-1
roots must be individuated (as indices) before spell-out. -/
theorem suppletive_rule_index_local (n : Number) :
    insert ⟨n, none⟩ singRoot = none := by
  cases n <;> decide

/-! ### §2.3 Individuation is not semantic: the cran-morph on the LF side

The mirror argument on List 3. A cran-morph (*cahoot*) has an interpretation
only inside its licensing frame (`in [ [ √ n ] -PL ]`) and — unlike an
ordinary root — **no Elsewhere interpretation** ([harley-2014] (16)). We
state this with the allosemy exponence engine (`AllosemicEntry` as an
`Morphology.Exponence.Rule` instance): `selectBy` returns a meaning in the
licensed context and `none` outside it. -/

/-- `√548` *cahoot*: a single LF entry, licensed only under `n` (the idiom
frame), with no Elsewhere alloseme ([harley-2014] (16)). -/
def cahootLF : List (AllosemicEntry String) :=
  [ { label := "cahoot", denotation := "a conspiracy", context := { belowCat := some .n } } ]

/-- In its licensing context the cran-morph is interpreted. -/
theorem cahoot_licensed :
    (selectBy AllosemicEntry.score cahootLF { belowCat := some .n }).isSome = true := by decide

/-- **No Elsewhere interpretation** ([harley-2014] (16)): outside the
licensing frame the cran-morph receives no meaning at all — the LF engine
returns `none`, the semantic analogue of a phonological gap. A Fodorian
atomic concept could not behave this way, so the root is not semantically
individuated. -/
theorem cahoot_no_elsewhere :
    (selectBy AllosemicEntry.score cahootLF { }).isNone = true := by decide

/-! ### The surviving individuation: the index -/

/-- Individuation by index is true by typing: distinct suppletive roots are
distinct `RootIndex` values ([harley-2014] §2.4). Neither the shared
Elsewhere-form shape nor the shared interpretation-frame identifies them. -/
example : runRoot ≠ walkRoot ∧ walkRoot ≠ killRoot ∧ runRoot ≠ killRoot := by decide

/-! ### Both individuation-failure arguments on the shared `Realization` carrier

The two negative flanks (§2.1–2.2 phonological, §2.3 semantic) are the
constancy pair of `Morphology.Realization` at one index: form varies across
contexts (`IsProperlySuppletive`), meaning does not vary but *gaps* (an
empty `interp` fiber outside the cran-morph's frame, via
`AllosemicHead.toInterpreted`). The vocabulary of §2.1 is the List-2 map,
`cahootLF` the List-3 map.

The form side wraps this file's `insert` — the shared Exponence engine
(`Exponence.realize`, argmax) — as a `Realization`. `VI.toRealization`
wraps the equivalent DM `vocabularyInsert`, whose `List.mergeSort` is
well-founded-recursive and so kernel-opaque; `insert` computes, so the
fibers reduce and the same theorem lands on the same data. -/

/-- The Hiaki suppletive vocabulary as a `Realization`: index `→` its
Elsewhere-selected exponent (`insert`) as a singleton fiber, `∅` at an
unlicensed index — the univalent stratum ([marantz-1997]'s List 2). -/
def realization : Morphology.Realization RootIndex Ctx String :=
  ⟨fun r c => match insert c r with | some f => {f} | none => ∅⟩

/-- **Phonological individuation fails, on the carrier** ([harley-2014]
§2.1–2.2): the Hiaki √322 realizes two nonempty, distinct fibers
(`vuite` / `tenne`) across two licensed contexts — `IsProperlySuppletive`,
the exact √GO case the predicate names. A root identified by its form would
split here. -/
theorem run_isProperlySuppletive : realization.IsProperlySuppletive runRoot := by
  have hsg : realization.realize runRoot ⟨.sg, none⟩ = {"vuite"} := by
    show (match insert ⟨.sg, none⟩ runRoot with
      | some f => ({f} : Finset String) | none => ∅) = _
    rw [run_sg]
  have hpl : realization.realize runRoot ⟨.pl, none⟩ = {"tenne"} := by
    show (match insert ⟨.pl, none⟩ runRoot with
      | some f => ({f} : Finset String) | none => ∅) = _
    rw [run_pl]
  refine ⟨⟨.sg, none⟩, ⟨.pl, none⟩, hsg ▸ Finset.singleton_nonempty _,
    hpl ▸ Finset.singleton_nonempty _, ?_⟩
  rw [hsg, hpl, ne_eq, Finset.singleton_inj]; decide

/-- **√322 is a suppletive-core root, not merely affixally inflected**
([harley-2014] §2.1): under the monomorphemic-form core extraction (a whole
exponent is its own core), `vuite`/`tenne` alternate at the core itself — the
`go`/`went` case of `Morphology.Root.HasSuppletiveCore`, the certificate axis
that distinguishes true suppletion from `cat`/`cats` inflection. -/
theorem run_hasSuppletiveCore :
    Morphology.Root.HasSuppletiveCore realization (fun s => {s}) runRoot :=
  (Morphology.Root.hasSuppletiveCore_singleton realization runRoot).mpr
    (realization.isSuppletive_iff.mpr (Or.inr run_isProperlySuppletive))

/-- √548 *cahoot* as a List-3 `Realization.Interpreted` view: one head, the
cran-morph's single alloseme. -/
def cahootHead : AllosemicHead String := { morpheme := .n, entries := cahootLF }

/-- **Semantic individuation fails, on the carrier** ([harley-2014] §2.3):
the cran-morph is interpreted (`a conspiracy`) inside its licensing frame
but has an empty `interp` fiber elsewhere — the meaning-side analogue of an
empty realization fiber, a *gap* rather than contextual variation. So this
is a licensing failure, not an `IsAllosemous` witness: unlike an ordinary
root (whose meaning would merely vary), a Fodorian atom could not gap. -/
theorem cahoot_interp_gap :
    cahootHead.toInterpreted.interp () { belowCat := some .n } = {"a conspiracy"} ∧
    cahootHead.toInterpreted.interp () { } = ∅ := by
  refine ⟨?_, ?_⟩ <;> decide

end Harley2014
