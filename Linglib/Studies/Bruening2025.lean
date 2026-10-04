module

public import Linglib.Studies.BrueningAlKhalaf2020

/-!
# Bruening 2025: selectional violations in coordination

Bruening replies to the objection that the two selectional violations Bruening and Al Khalaf find
in coordination, a clause beside a noun phrase where only noun phrases are selected and a non-*ly*
adverb beside an adjective before a noun, are not violations at all. Three acceptability surveys
bear the objection out in neither case, and since their results are effect directions on rating
scales they are recorded in prose. The reply accepts the critics' evidence that coordinated
arguments need not match in category ((8)–(12)) and revises the 2020 analysis, keeping its
selector's requirements and dropping the requirement that conjuncts share a category (§§5.2–5.3).
It rests on categorial selection being irreducible to semantic selection, which five
*become*-type predicates show.

## Main definitions

* `ComplementProfile`, `BecomeType.profile`: the categories each *become*-type predicate admits.

## Main results

* `cSelection_not_reducible`: no assignment of categories to a semantic class fits the five
  predicates.
* `unlike_arguments`: coordinated arguments of different categories, each selected, are admitted
  by the revision and excluded by the 2020 grammar.
* `violations_are_directional`: a clause may join a noun phrase where clauses are banned, after it
  but not before it, and no noun phrase may join a clause where noun phrases are banned.
* `no_other_violations`: a prepositional phrase may not join a noun phrase where noun phrases
  alone are selected.

## Implementation notes

* The revision is the 2020 study's `Satisfies` without its `Coordinable` clause, so the 2020
  theorems about `Satisfies`, `mem_cats_or_of_admits` and `mem_cats_of_mem_leftToRight`, hold of
  it. The reply's own analysis of the adverbial violation (§5.8) is not formalized.

## References

* [bruening-2025]
* [bruening-alkhalaf-2020]
* [pollard-sag-1987]
-/

@[expose] public section

namespace Bruening2025

open BrueningAlKhalaf2020
open Syntax (Cat)
open Syntax.Cat (NP PP)

/-! ### Categorial selection is not semantic selection -/

/-- The complement categories a predicate admits. Every complement at issue is semantically a
predicate, so the profiles differ on categories alone. -/
structure ComplementProfile where
  /-- Whether noun phrases are admitted, as in *she ended up a cynic*. -/
  np : Bool
  /-- Whether adjective phrases are admitted, as in *she grew tired*. -/
  ap : Bool
  /-- Whether prepositional phrases are admitted, as in *she got into trouble*. -/
  pp : Bool
  /-- Whether gerundive complements are admitted, as in *they ended up liking it*. -/
  gerund : Bool
  /-- Whether *to*-infinitives are admitted, as in *they turned out to like it*. -/
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
reproduce their distribution, since they are alike semantically and differ categorially, so
categorial selection is a further fact about a predicate. -/
theorem cSelection_not_reducible {α : Type*} (semantics : BecomeType → α)
    (halike : ∀ v w, semantics v = semantics w) (fromSemantics : α → ComplementProfile) :
    ¬ ∀ v : BecomeType, fromSemantics (semantics v) = v.profile := by
  intro h
  have := (h .become).symm.trans ((halike .become .grow) ▸ h .grow)
  exact absurd this (by decide)

/-- Even the two predicates that admit the same phrasal categories differ on nonfinite
complements, as *they ended up liking it* against *they turned out to like it* shows. -/
theorem endUp_turnOut_differ :
    BecomeType.endUp.profile.np = BecomeType.turnOut.profile.np ∧
      BecomeType.endUp.profile.ap = BecomeType.turnOut.profile.ap ∧
      BecomeType.endUp.profile.gerund ≠ BecomeType.turnOut.profile.gerund ∧
      BecomeType.endUp.profile.toInfinitive ≠ BecomeType.turnOut.profile.toInfinitive := by
  decide

/-! ### The revised grammar -/

/-- Coordinated arguments of different categories, each selected, are admitted once conjuncts need
not share a category, as a clause and a prepositional phrase are after *believe* (9) and a clause
before a noun phrase after *show* (10). The 2020 grammar excludes both, the second because the
clause must then be a noun phrase under the null N, which bears no S-features for the verb to
check, as in its (69). -/
theorem unlike_arguments :
    (Admits (Satisfies (leftToRight .headInitial) {.CP, PP}) [.CP, PP] ∧
      ¬ Admits (Licensed (leftToRight .headInitial) {.CP, PP}) [.CP, PP]) ∧
    (Admits (Satisfies (leftToRight .headInitial) {NP, .CP}) [.CP, NP] ∧
      ¬ Admits (Licensed (leftToRight .headInitial) {NP, .CP}) [.CP, NP]) := by
  decide

/-- The violations run one way, and away from the selector. A clause coordinated with a noun
phrase is admitted where a noun phrase is selected, after the noun phrase but not before it — *you
can depend on my assistant and that he will be on time* against (3b) — while a noun phrase
coordinated with a clause is not admitted where a clause is selected, as in *she thinks that the
world is flat and another discredited thing* (49). -/
theorem violations_are_directional :
    Admits (Satisfies (leftToRight .headInitial) {NP}) [NP, .CP] ∧
      ¬ Admits (Satisfies (leftToRight .headInitial) {NP}) [.CP, NP] ∧
      ¬ Admits (Satisfies (leftToRight .headInitial) {.CP}) [.CP, NP] := by
  decide

/-- A prepositional phrase may not join a noun phrase where the selecting head admits noun phrases
only, so *the invaders destroyed the castle and of the surrounding town* is out (44). In general a
phrase the selector does not c-select can only be a clause where a noun phrase is selected
(`mem_cats_or_of_admits`). -/
theorem no_other_violations : ¬ Admits (Satisfies (leftToRight .headInitial) {NP}) [NP, PP] := by
  decide

end Bruening2025
