/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
import Linglib.Morphology.DistributedMorphology.Allosemy
import Linglib.Morphology.Root.Certificates
import Linglib.Features.Number.Basic
import Linglib.Semantics.ArgumentStructure.Valency
import Linglib.Studies.Marantz1991

/-!
# On the identity of roots

[harley-2014] argues that a root terminal of List 1 is individuated neither by
its form nor by its meaning but by an index. Hiaki root suppletion (√322:
*vuite*~*tenne* 'run') shows that roots must already be distinct when their
Vocabulary Items compete, and that phonologically individuated roots would
turn suppletion into rewriting; caboodle items (*cahoot*) show that List-3
interpretation can be bound to one frame with no Elsewhere, so a root is not
a concept either. What remains is the index, on which List 2 and List 3 are
both keyed.

## Main definitions

* `Clause`, `siteFeatures`: the number at each core-argument position
  (`ArgumentStructure.ArgPosition`), and a suppletive root's insertion site —
  its index and the number of the internal argument, the local conditioning
  environment of §3.3.
* `vocabulary`: the Hiaki items of (3a), (3f), (3g): a singular-conditioned
  form and an Elsewhere form per root ((14), fn. 16).
* `cahootLF`: the List-3 entry of (16), one frame and no Elsewhere.
* `realization`: List 2 as a `Morphology.Realization`.

## Main results

* `run_isProperlySuppletive`, `run_hasSuppletiveCore`: one index, two
  unrelated forms — individuation is not phonological (§2.2).
* `cahoot_interp_gap`: interpreted in its frame, uninterpreted elsewhere —
  individuation is not semantic (§2.3).
* `suppletion_not_agreement`: conditioning by the internal argument is an
  ergative–absolutive pattern in a nominative–accusative language, which
  [bobaljik-2008]'s generalization rules out for agreement, so it is local
  Vocabulary-Item competition rather than agreement (§3.3).
* `index_local`: a suppletive item blocks nothing at another index — the
  thought experiment of §2.1.
* `intransitive_isRootValency`: the conditioning argument of an intransitive
  occupies the root's valency — the paper's prediction that the intransitive
  suppletive verbs are unaccusative.

## Implementation notes

Footnote 16 settles the Elsewhere direction: the impersonal passive, whose
argument is syntactically absent, surfaces as *tenne*, so *tenne* is the
Elsewhere form and *vuite* is conditioned by a singular internal argument;
(7) is the paper's first pass with the roles reversed. The paper indexes only
√322 and √548; the other indices here are arbitrary distinct ones. The
caboodle frame of (16), `[in [[√ n]nP -PL]DP]PP`, is recorded by its
categorizing head.
-/

namespace Harley2014

open DistributedMorphology ArgumentStructure
open DistributedMorphology.Allosemy (SyntacticContext AllosemicEntry toInterpreted)
open Morphology.Exponence (selectBy)

/-! ### List 1: roots as indices -/

/-- √322, realized *vuite*~*tenne* 'run' ((3a), (14)). -/
def run : Root := ⟨322⟩

/-- The root realized *weye*~*kaate* 'walk' ((3f), (26)). -/
def walk : Root := ⟨401⟩

/-- The root realized *mea*~*sua* 'kill' ((3g), (27)). -/
def kill : Root := ⟨402⟩

/-- A non-suppletive intransitive root, *bwiika* 'sing', at whose index the
suppletive items must not compete (§2.1). -/
def sing : Root := ⟨500⟩

/-! ### The insertion site -/

/-- The number borne at each core-argument position of a clause, `none` where
the position is unfilled. -/
abbrev Clause := ArgPosition → Option Number

/-- An intransitive clause whose sole argument, of number `n`, is internal. -/
def intransitive (n : Number) : Clause
  | .internal => some n
  | .external => none

/-- A transitive clause with an internal argument of number `obj` and an
external one of number `subj`. -/
def transitive (obj subj : Number) : Clause
  | .internal => some obj
  | .external => some subj

/-- The impersonal passive: no number-bearing argument (fn. 16). -/
def impersonal : Clause := fun _ => none

/-- The positions a clause fills. -/
def Clause.valency (c : Clause) : Valency := Finset.univ.filter fun p => (c p).isSome

/-- Features at a suppletive root's insertion site: its index and the number
of the internal argument. -/
inductive SiteFeature where
  | root (r : Root)
  | internal (n : Number)
  deriving DecidableEq, Repr

/-- The insertion bundle for root `r` in clause `c`: the external argument
is not in the local environment (§3.3). -/
def siteFeatures (c : Clause) (r : Root) : List SiteFeature :=
  .root r :: ((c .internal).map .internal).toList

/-! ### List 2: the suppletive Vocabulary Items -/

/-- A suppletive root's two items: the form conditioned by a singular
internal argument and the Elsewhere form ((14), fn. 16). -/
def suppletive (r : Root) (sgForm elseForm : String) : List (VocabularyItem SiteFeature String) :=
  [⟨[.root r, .internal .singular], sgForm⟩, ⟨[.root r], elseForm⟩]

/-- The Hiaki suppletive vocabulary of (3a), (3f), (3g). -/
def vocabulary : List (VocabularyItem SiteFeature String) :=
  suppletive run "vuite" "tenne" ++ suppletive walk "weye" "kaate" ++ suppletive kill "mea" "sua"

/-- Spell out root `r` in clause `c` by the Subset Principle over
`vocabulary`. -/
def spellout (c : Clause) (r : Root) : Option String :=
  subsetPrinciple vocabulary (siteFeatures c r)

/-- Singular subject → *vuite* ((6a)). -/
theorem run_sg : spellout (intransitive .singular) run = some "vuite" := by decide

/-- Plural subject → *tenne* ((6b)). -/
theorem run_pl : spellout (intransitive .plural) run = some "tenne" := by decide

/-- No number-bearing argument (the impersonal passive) → *tenne*, the
Elsewhere form (fn. 16). -/
theorem run_impersonal : spellout impersonal run = some "tenne" := by decide

/-- *weye*/*kaate* with a singular/plural subject ((26)). -/
theorem walk_sg_pl :
    spellout (intransitive .singular) walk = some "weye" ∧
      spellout (intransitive .plural) walk = some "kaate" := by
  decide

/-- *mea*/*sua* with a singular/plural object, whatever the subject ((27)). -/
theorem kill_sgObj_plObj :
    spellout (transitive .singular .plural) kill = some "mea" ∧
      spellout (transitive .plural .singular) kill = some "sua" := by
  decide

/-! ### §2.1–2.2 Individuation is not phonological -/

/-- One index, two phonologically unrelated forms: a root identified by its
form would split √322 in two (§2.2). -/
theorem run_two_forms :
    spellout (intransitive .singular) run ≠ spellout (intransitive .plural) run := by
  decide

/-- The suppletive items compete only at their own index: a non-suppletive
intransitive root receives no exponent from `vocabulary` — why List-1 roots
must be distinct before spell-out (§2.1). -/
theorem index_local (c : Clause) : spellout c sing = none := by
  unfold spellout siteFeatures
  rcases h : c .internal with _ | n
  · rfl
  · cases n <;> rfl

/-! ### §3.3 Conditioning by the internal argument -/

/-- The external argument's number never conditions the form. -/
theorem suppletion_ignores_external (obj subj subj' : Number) (r : Root) :
    spellout (transitive obj subj) r = spellout (transitive obj subj') r := rfl

/-- The conditioning argument of an intransitive occupies the root's valency
([coon-2019]'s division of labor): the intransitive suppletive verbs are
unaccusative, the paper's prediction from locality. -/
theorem intransitive_isRootValency (n : Number) : (intransitive n).valency.IsRootValency := by
  revert n; decide

/-- Which arguments condition Hiaki suppletion, read off `spellout`: the sole
argument of an intransitive and the object of a transitive, not the
transitive subject. -/
def conditioningPattern : Minimalist.AgreementPattern where
  sAgrees := spellout (intransitive .singular) run != spellout (intransitive .plural) run
  aAgrees := spellout (transitive .singular .singular) kill !=
    spellout (transitive .singular .plural) kill
  pAgrees := spellout (transitive .singular .singular) kill !=
    spellout (transitive .plural .singular) kill

/-- Suppletion follows an ergative–absolutive distribution. -/
theorem conditioningPattern_isErgAbs : conditioningPattern.isErgAbs = true := by decide

/-- **Suppletion is not agreement**: Hiaki case is nominative–accusative
((29)), and no agreement threshold over nominative–accusative case yields
an ergative–absolutive pattern (`Minimalist.nomAcc_no_ergAbs_agreement`,
[bobaljik-2008]'s generalization) — so the pattern is local Vocabulary-Item
competition, conditioned by the internal argument. -/
theorem suppletion_not_agreement (t : Minimalist.CaseAccessibility) :
    Minimalist.agreementFromThreshold Minimalist.nomAcc t ≠ conditioningPattern := by
  intro h
  have := Minimalist.nomAcc_no_ergAbs_agreement t
  rw [h, conditioningPattern_isErgAbs] at this
  exact Bool.noConfusion this

/-! ### §2.3 Individuation is not semantic: the caboodle item -/

/-- √548 *cahoot* ((16)). -/
def cahoot : Root := ⟨548⟩

/-- The List-3 entry of √548: "a conspiracy" in the frame of (16), recorded by
its categorizing head, and no Elsewhere. -/
def cahootLF : List (AllosemicEntry String) :=
  [{ denotation := "a conspiracy", context := { aboveCat := some .n } }]

/-- Outside its frame the caboodle item has no interpretation. The paper adds
that no List-3 entry could be a true Elsewhere, since an interpretation must
compose with its sister's type; caboodle items make the absence visible. -/
theorem cahoot_no_elsewhere : selectBy AllosemicEntry.score cahootLF {} = none := by decide

/-! ### Both flanks on the `Realization` carrier

Form varies across contexts (`IsProperlySuppletive`), meaning does not vary
but gaps (an empty `interp` fiber outside the frame, via
`Allosemy.toInterpreted`): `vocabulary` is the List-2 map, `cahootLF` the
List-3 map. -/

/-- List 2 as a `Realization`: a root's Elsewhere-selected exponent as a
singleton fiber, `∅` at an index with no item. -/
def realization : Morphology.Realization Root Clause String :=
  ⟨fun r c => (spellout c r).elim ∅ ({·})⟩

/-- √322 realizes two nonempty, distinct fibers across two licensed clauses —
the *go*/*went* case the predicate names (§2.2). -/
theorem run_isProperlySuppletive : realization.IsProperlySuppletive run := by
  have hsg : realization.realize run (intransitive .singular) = {"vuite"} := by
    show (spellout (intransitive .singular) run).elim ∅ ({·}) = _
    simp [run_sg]
  have hpl : realization.realize run (intransitive .plural) = {"tenne"} := by
    show (spellout (intransitive .plural) run).elim ∅ ({·}) = _
    simp [run_pl]
  refine ⟨intransitive .singular, intransitive .plural, hsg ▸ Finset.singleton_nonempty _,
    hpl ▸ Finset.singleton_nonempty _, ?_⟩
  rw [hsg, hpl, ne_eq, Finset.singleton_inj]; decide

/-- Under the identity core-extraction, *vuite*/*tenne* alternate at the core
itself — `Morphology.Root.HasSuppletiveCore`, suppletion proper rather than
affixal inflection. -/
theorem run_hasSuppletiveCore : Morphology.Root.HasSuppletiveCore realization (fun s => {s}) run :=
  (Morphology.Root.hasSuppletiveCore_singleton realization run).mpr
    (realization.isSuppletive_iff.mpr (Or.inr run_isProperlySuppletive))

/-- √548 as a List-3 `Realization.Interpreted` view. -/
def cahootHead : Morphology.Realization.Interpreted Unit SyntacticContext Unit String :=
  toInterpreted cahootLF

/-- The caboodle item is interpreted inside its frame and has an empty
`interp` fiber elsewhere — a gap, the meaning-side analogue of an empty
realization fiber, so a licensing failure rather than allosemy (§2.3). -/
theorem cahoot_interp_gap :
    cahootHead.interp () { aboveCat := some .n } = {"a conspiracy"} ∧
      cahootHead.interp () {} = ∅ := by
  refine ⟨?_, ?_⟩ <;> decide

end Harley2014
