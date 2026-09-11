/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
import Linglib.Morphology.DistributedMorphology.Allosemy
import Linglib.Morphology.Root.Certificates
import Linglib.Features.Number.Basic
import Linglib.Syntax.Clause.Arguments
import Linglib.Studies.Marantz1991

/-!
# Harley (2014): On the identity of roots

This file formalizes [harley-2014]'s argument that a root of List 1 is individuated neither by
its form nor by its meaning but by an index, on which the Vocabulary Items of List 2 and the
interpretations of List 3 are both keyed. Hiaki root suppletion (√322, *vuite* ~ *tenne* 'run')
shows that roots must already be distinct when their items compete, since an item conditioned
by number would otherwise block every less specified root, and that phonologically individuated
roots would turn suppletion into rewriting; the caboodle item *cahoot* shows an interpretation
bound to one frame with no Elsewhere, so a root is not a concept either. `spellout` realizes a
root at its insertion site, the index with the number of the internal argument below, by the
Subset Principle over the Hiaki vocabulary; `run_isProperlySuppletive` and `cahoot_interp_gap`
are the two flanks. `suppletion_not_agreement` is §3.3's argument that conditioning by the
internal argument, an ergative–absolutive pattern in a nominative–accusative language, is
Vocabulary-Item competition rather than agreement, and `unergative_elsewhere` its prediction
that the suppletive intransitives are unaccusative.

## Implementation notes

Footnote 16 settles the Elsewhere direction: the impersonal passive, whose argument is
syntactically absent, surfaces as *tenne*, so *tenne* is the Elsewhere form and *vuite* is
conditioned by a singular internal argument, as in the paper's (14); its (7) is a first pass with
the roles reversed. The paper indexes only √322 and √548, the other indices here are arbitrary
distinct ones, and the caboodle frame of (16) is recorded by its categorizing head. Example
numbers follow the revised manuscript (LingBuzz 001527); the paper's Hiaki examples are the rows
of `Data/Examples/Harley2014.json`.

## References

* [harley-2014]
* [bobaljik-2008]
-/

namespace Harley2014

open DistributedMorphology
open DistributedMorphology.Allosemy (toInterpreted embedding)
open Morphology.Exponence (selectBy)
open Clause (Arguments)
open Clause.Arguments (unaccusative unergative transitive empty)

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

/-- What a root's Vocabulary Items may mention: its index, and the number
of the internal argument on the terminal below. -/
inductive SiteFeature where
  | root (r : Root)
  | internal (n : Number)
  deriving DecidableEq, Repr

/-- The neighborhood of root `r` in a clause bearing the numbers `c`: the
internal argument is the terminal below; the external argument is not in the
local environment (§3.3). -/
def site (c : Arguments Number) (r : Root) : Neighborhood (List SiteFeature) :=
  ⟨[.root r], ((c .internal).map λ n => ([.internal n] : List SiteFeature)).toList, []⟩

/-! ### List 2: the suppletive Vocabulary Items -/

/-- A suppletive root's two items ((14), fn. 16): the form conditioned by a
singular internal argument below, and the Elsewhere form. -/
def suppletive (r : Root) (sgForm elseForm : String) : List (VocabularyItem SiteFeature String) :=
  [⟨⟨[.root r], [[.internal .singular]], []⟩, sgForm⟩, [.root r] ⟷ elseForm]

/-- The Hiaki suppletive vocabulary of (3a), (3f), (3g). -/
def vocabulary : List (VocabularyItem SiteFeature String) :=
  suppletive run "vuite" "tenne" ++ suppletive walk "weye" "kaate" ++ suppletive kill "mea" "sua"

/-- Spell out root `r` in clause `c` by the Subset Principle over
`vocabulary`. -/
def spellout (c : Arguments Number) (r : Root) : Option String :=
  subsetPrinciple vocabulary (site c r)

/-- Singular subject → *vuite* ((6a)). -/
theorem run_sg : spellout (unaccusative .singular) run = some "vuite" := by decide

/-- Plural subject → *tenne* ((6b)). -/
theorem run_pl : spellout (unaccusative .plural) run = some "tenne" := by decide

/-- No number-bearing argument (the impersonal passive) → *tenne*, the
Elsewhere form (fn. 16). -/
theorem run_impersonal : spellout empty run = some "tenne" := by decide

/-- *weye*/*kaate* with a singular/plural subject ((26)). -/
theorem walk_sg_pl :
    spellout (unaccusative .singular) walk = some "weye" ∧
      spellout (unaccusative .plural) walk = some "kaate" := by
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
    spellout (unaccusative .singular) run ≠ spellout (unaccusative .plural) run := by
  decide

/-- The suppletive items compete only at their own index: a non-suppletive
intransitive root receives no exponent from `vocabulary` — why List-1 roots
must be distinct before spell-out (§2.1). -/
theorem index_local (c : Arguments Number) : spellout c sing = none := by
  unfold spellout site
  rcases h : c .internal with _ | n
  · rfl
  · cases n <;> rfl

/-! ### §3.3 Conditioning by the internal argument -/

/-- The external argument's number never conditions the form. -/
theorem suppletion_ignores_external (obj subj subj' : Number) (r : Root) :
    spellout (transitive obj subj) r = spellout (transitive obj subj') r := rfl

/-- Only an internal argument conditions the form: an intransitive whose sole
argument is external gets the Elsewhere form whatever its number, so the
suppletive intransitives must be unaccusative — the paper's prediction from
locality. -/
theorem unergative_elsewhere (n : Number) : spellout (unergative n) run = some "tenne" := rfl

/-- Which arguments condition Hiaki suppletion, read off `spellout`: the sole
argument of an intransitive and the object of a transitive, not the
transitive subject. -/
def conditioningPattern : Minimalist.AgreementPattern where
  sAgrees := spellout (unaccusative .singular) run != spellout (unaccusative .plural) run
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
def cahootLF : List (VocabularyItem Allosemy.Feature String) :=
  [⟨embedding [.cat .n], "a conspiracy"⟩]

/-- Outside its frame the caboodle item has no interpretation. The paper adds
that no List-3 entry could be a true Elsewhere, since an interpretation must
compose with its sister's type; caboodle items make the absence visible. -/
theorem cahoot_no_elsewhere : winner? cahootLF ∅ = none := by decide

/-! ### Both flanks on the `Realization` carrier

Form varies across contexts (`IsProperlySuppletive`), meaning does not vary
but gaps (an empty `interp` fiber outside the frame, via
`Allosemy.toInterpreted`): `vocabulary` is the List-2 map, `cahootLF` the
List-3 map. -/

/-- List 2 as a `Realization`: a root's Elsewhere-selected exponent as a
singleton fiber, `∅` at an index with no item. -/
def realization : Morphology.Realization Root (Arguments Number) String :=
  ⟨λ r c => (spellout c r).elim ∅ ({·})⟩

/-- √322 realizes two nonempty, distinct fibers across two licensed clauses —
the *go*/*went* case the predicate names (§2.2). -/
theorem run_isProperlySuppletive : realization.IsProperlySuppletive run := by
  have hsg : realization.realize run (unaccusative .singular) = {"vuite"} := by
    show (spellout (unaccusative .singular) run).elim ∅ ({·}) = _
    simp [run_sg]
  have hpl : realization.realize run (unaccusative .plural) = {"tenne"} := by
    show (spellout (unaccusative .plural) run).elim ∅ ({·}) = _
    simp [run_pl]
  refine ⟨unaccusative .singular, unaccusative .plural, hsg ▸ Finset.singleton_nonempty _,
    hpl ▸ Finset.singleton_nonempty _, ?_⟩
  rw [hsg, hpl, ne_eq, Finset.singleton_inj]; decide

/-- Under the identity core-extraction, *vuite*/*tenne* alternate at the core
itself — `Morphology.Root.HasSuppletiveCore`, suppletion proper rather than
affixal inflection. -/
theorem run_hasSuppletiveCore : Morphology.Root.HasSuppletiveCore realization (λ s => {s}) run :=
  (Morphology.Root.hasSuppletiveCore_singleton realization run).mpr
    (realization.isSuppletive_iff.mpr (Or.inr run_isProperlySuppletive))

/-- √548 as a List-3 `Realization.Interpreted` view. -/
def cahootHead :
    Morphology.Realization.Interpreted Unit (Neighborhood (List Allosemy.Feature)) Unit String :=
  toInterpreted cahootLF

/-- The caboodle item is interpreted inside its frame and has an empty
`interp` fiber elsewhere — a gap, the meaning-side analogue of an empty
realization fiber, so a licensing failure rather than allosemy (§2.3). -/
theorem cahoot_interp_gap :
    cahootHead.interp () (embedding [.cat .n]) = {"a conspiracy"} ∧
      cahootHead.interp () ∅ = ∅ := by
  refine ⟨?_, ?_⟩ <;> decide

end Harley2014
