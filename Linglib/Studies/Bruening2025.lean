import Linglib.Studies.BrueningAlKhalaf2020

/-!
# Bruening 2025: selectional violations in coordination

Coordination lets a conjunct appear where its category is otherwise banned, but only in two
configurations: a clause coordinated with a noun phrase in a position that admits noun phrases
only, and one of the non-*ly* adverbs coordinated with an adjective phrase in prenominal position.
This file formalizes the reply to the objection that these are not selectional violations at all.
Three acceptability surveys reported in the paper bear the objection out in neither case: the
prenominal adverb is degraded next to its adjectival counterpart yet better than an ungrammatical
control, the same adverb fails the one-replacement test that the adjective passes, and a clause in
a noun-phrase position is rated far higher coordinated than alone. Those are effect directions on
rating scales, so they are recorded here in prose rather than as theorems.

What is formalized is the structural side of the reply. The two permitted violations are
directional — a clause goes where a noun phrase is selected, never the reverse — and every other
category mismatch is out, which is what rules out the accounts on which any category may appear
as a non-initial conjunct. Behind that lies the assumption the reply defends at length: categorial
selection cannot be reduced to semantic selection. Five predicates take a semantic predicate as
their complement and differ arbitrarily in the categories they admit, so no function from a
complement's semantics to its category can reproduce their distribution.

## Main definitions

* `ComplementProfile`, `becomeType` — the categories each *become*-type predicate admits

## Main results

* `cSelection_not_reducible` — no assignment of categories to a semantic class fits the five
  predicates, since they agree semantically and differ categorially
* `violations_are_directional` — a clause may join a noun phrase where clauses are banned, and no
  noun phrase may join a clause where noun phrases are banned
* `no_other_violations` — the remaining mismatches the literature has proposed are not permitted

## References

* [bruening-2025]
* [bruening-alkhalaf-2020]
* [pollard-sag-1987]
-/

namespace Bruening2025

open BrueningAlKhalaf2020
open Syntax (Cat)
open Syntax.Cat (NP AdvP AdjP)

/-! ### Categorial selection is not semantic selection -/

/-- The complement categories a predicate admits. Every complement at issue is semantically a
predicate, so the profiles differ on categories alone. -/
structure ComplementProfile where
  /-- Noun phrases: *she ended up a cynic*. -/
  np : Bool
  /-- Adjective phrases: *she grew tired*. -/
  ap : Bool
  /-- Prepositional phrases: *she got into trouble*. -/
  pp : Bool
  /-- Gerundive complements: *they ended up liking it*. -/
  gerund : Bool
  /-- *To*-infinitives: *they turned out to like it*. -/
  toInfinitive : Bool
  deriving DecidableEq, Repr

/-- The five *become*-type predicates and the categories each admits. -/
inductive BecomeType where
  | become | grow | get | endUp | turnOut
  deriving DecidableEq, Repr

/-- *Become* admits noun and adjective phrases, *grow* only adjective phrases, *get* adjective and
prepositional phrases, and *end up* and *turn out* both noun and adjective phrases while splitting
the nonfinite complements between them. -/
def BecomeType.profile : BecomeType → ComplementProfile
  | .become => ⟨true, true, false, false, false⟩
  | .grow => ⟨false, true, false, false, false⟩
  | .get => ⟨false, true, true, false, false⟩
  | .endUp => ⟨true, true, false, true, false⟩
  | .turnOut => ⟨true, true, false, false, true⟩

/-- No assignment of a complement profile to the semantic class the five predicates share can
reproduce their distribution: they are alike semantically and differ categorially, so categorial
selection is a further fact about a predicate. -/
theorem cSelection_not_reducible {α : Type*} (semantics : BecomeType → α)
    (halike : ∀ v w, semantics v = semantics w) (fromSemantics : α → ComplementProfile) :
    ¬ ∀ v : BecomeType, fromSemantics (semantics v) = v.profile := by
  intro h
  have := (h .become).symm.trans ((halike .become .grow) ▸ h .grow)
  exact absurd this (by decide)

/-- Even the two predicates that admit the same phrasal categories differ on nonfinite
complements: *they ended up liking it* against *they turned out to like it*. -/
theorem endUp_turnOut_differ :
    BecomeType.endUp.profile.np = BecomeType.turnOut.profile.np ∧
      BecomeType.endUp.profile.ap = BecomeType.turnOut.profile.ap ∧
      BecomeType.endUp.profile.gerund ≠ BecomeType.turnOut.profile.gerund ∧
      BecomeType.endUp.profile.toInfinitive ≠ BecomeType.turnOut.profile.toInfinitive := by
  decide

/-! ### The two permitted violations -/

/-- The violations run one way. A clause coordinated with a noun phrase is admitted where a noun
phrase is selected — *you can depend on my assistant and that he will be on time* — while a noun
phrase coordinated with a clause is not admitted where a clause is selected: *she thinks that the
world is flat and another discredited thing*. The same asymmetry holds of the adverb and the
adjective in prenominal position. -/
theorem violations_are_directional :
    NP ∈ coordExtension .CP ∧ Cat.CP ∉ coordExtension NP ∧
      AdjP ∈ coordExtension AdvP ∧ AdvP ∉ coordExtension AdjP := by
  refine ⟨cp_extends_np, ?_, advp_extends_adjp, ?_⟩ <;> decide

/-- No other mismatch is permitted: a prepositional phrase may not join a noun phrase where the
selecting head admits noun phrases only — *the invaders destroyed the castle and of the surrounding
town* — and likewise for the other categories the literature has appealed to. -/
theorem no_other_violations (c : Cat) (h : c ≠ .CP) (h' : c ≠ AdvP) :
    coordExtension c = ∅ := by
  by_contra hc
  rcases coordExtension_exhaustive c hc with rfl | rfl
  exacts [h rfl, h' rfl]

/-- The two violations the surveys tested are the two the earlier paper derives: a clause where a
noun phrase is selected, and a non-*ly* adverb where an adjective is selected. -/
theorem surveyed_violations :
    SelectionViolationType.cpAsNp.cats = (.CP, NP) ∧
      SelectionViolationType.advAsAdj.cats = (AdvP, AdjP) := ⟨rfl, rfl⟩

end Bruening2025
