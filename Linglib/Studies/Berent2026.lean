import Linglib.Phonology.Segmental.Basic
import Linglib.Studies.BerentEtAl2016

/-!
# Berent (2026): Three arguments for abstraction in phonology

This file formalizes Berent's three experimental arguments that phonological grammar is
substance-free. Phonology is *abstract* (§3.1): the preference for onsets with large
sonority rises, in data from Berent, Steriade, Lennertz and Vaknin, survives print
presentation and articulatory suppression. It is *algebraic* (§3.2): identity restrictions
generalize to feature values unattested in the speaker's language, Hebrew /θ/ and novel
ASL handshapes. It is *amodal* (§3.3): English speakers project the doubling restrictions
of their spoken language onto novel ASL signs, banning identity in phonological contexts
and preferring reduplication in morphological ones.

Each property is carried by a type rather than restated. Abstractness is the invariance of
onset markedness under anything but the `Sonority` order. Algebraicity is the parametric
polymorphism of `Constraints.mkOCP`, which cannot inspect what it compares. Amodality is
the statement of the doubling reversal of `Studies/BerentEtAl2016.lean` over an arbitrary
type of prosodic constituents, spoken or signed.

## Main definitions

* `onsetProfile`, `onsetMarkedness`: the rise, plateau or fall of a two-consonant onset, and
  its markedness by sonority distance, on the abstract `Sonority` type.

## Main results

* `sonority_cline`: the four-point cline blif ≺ bnif ≺ bdif ≺ lbif of Figure 1 follows from
  rank distance, where the three-way profile cannot separate blif from bnif.
* `onsetMarkedness_rank_invariant`, `markedness_vs_profile`: markedness sees only the
  sonority ordering, and refines the three-way profile.
* `amodal_doubling_reversal`: the doubling reversal holds for any type of constituents and
  either ranking of the OCP and DEP.

## References

* [berent-2026]
* [berent-steriade-lennertz-vaknin-2007]
* [berent-bat-el-brentari-dupuis-vaknin-nusbaum-2016]
* [mccarthy-1986]
-/

open Phonology (Sonority)

namespace Berent2026

open Constraints OptimalityTheory BerentEtAl2016

/-! ### Onset markedness: the sonority cline -/

/-- The sonority profile of a two-consonant onset is the relation between the sonority of
    its first and second consonant, on the abstract `Sonority` order. -/
inductive OnsetProfile where
  | rise
  | plateau
  | fall
  deriving DecidableEq, Repr

/-- The sonority profile of a two-consonant onset. -/
def onsetProfile (c1 c2 : Sonority) : OnsetProfile :=
  if c1.rank < c2.rank then .rise
  else if c1.rank == c2.rank then .plateau
  else .fall

/-- Onset markedness falls with the sonority rise, so large rises beat small rises, which
    beat plateaus, which beat falls. The pad `5`, the top rank, keeps the subtraction in
    `ℕ` total, and only the ordering of the values matters. -/
def onsetMarkedness : Constraint (Sonority × Sonority) :=
  fun (c1, c2) ↦ 5 + c1.rank - c2.rank

/-- The four-point behavioral cline blif ≺ bnif ≺ bdif ≺ lbif of Figure 1, that is
    stop–liquid ≺ stop–nasal ≺ stop–stop ≺ liquid–stop, follows from rank distance on the
    abstract type. -/
theorem sonority_cline :
    onsetMarkedness (.stop, .liquid) < onsetMarkedness (.stop, .nasal) ∧
      onsetMarkedness (.stop, .nasal) < onsetMarkedness (.stop, .stop) ∧
        onsetMarkedness (.stop, .stop) < onsetMarkedness (.liquid, .stop) := by
  decide

/-- Markedness depends only on the sonority ranks, so onsets whose segments match in rank
    are treated identically, whatever their articulatory realization. -/
theorem onsetMarkedness_rank_invariant (c1 c2 d1 d2 : Sonority)
    (h1 : c1.rank = d1.rank) (h2 : c2.rank = d2.rank) :
    onsetMarkedness (c1, c2) = onsetMarkedness (d1, d2) := by
  simp [onsetMarkedness, h1, h2]

/-- The distance markedness refines the three-way profile, with values below `5` a rise,
    `5` a plateau, and values above `5` a fall. -/
theorem markedness_vs_profile (c1 c2 : Sonority) :
    (onsetMarkedness (c1, c2) < 5 ↔ onsetProfile c1 c2 = .rise) ∧
      (onsetMarkedness (c1, c2) = 5 ↔ onsetProfile c1 c2 = .plateau) ∧
        (5 < onsetMarkedness (c1, c2) ↔ onsetProfile c1 c2 = .fall) := by
  cases c1 <;> cases c2 <;> decide

/-! ### Algebraic OCP (Argument 2)

`mkOCP` and `adjacentIdentical` (`Phonology/Constraints/Basic.lean`) are parametrically
polymorphic over the feature type: the constraint cannot inspect what kind of features it
compares, only whether they are identical. That parametricity is Argument 2's
algebraicity — the OCP extends to Hebrew /θ/ and to unattested ASL handshapes by
construction (§3.2). The recursion lemmas `adjacentIdentical_cons_self` and
`adjacentIdentical_cons_of_ne` live with the definition. -/

/-! ### The doubling reversal (Argument 3) -/

/-- In the phonology–morphology reversal the same identity ban yields opposite surface
    preferences depending on whether the morphological context licenses reduplication.
    It is amodal in that the constituents `x` and `y` range over any type, syllables of
    speech or of sign alike; the dependence on the spoken language is
    `BerentEtAl2016.exists_optimal_surface_iff`. -/
theorem amodal_doubling_reversal {α : Type*} [DecidableEq α] {x y : α} (h : x ≠ y)
    (r : Ranking 2) :
    (tableau x y .phonology r).optimal = {.simplex [x, y]} ∧
      (tableau x y .morphology r).optimal = {.reduplicated [x]} :=
  ⟨optimal_phonology h r, optimal_morphology h r⟩

end Berent2026
