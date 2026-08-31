import Linglib.Phonology.Segmental.Basic
import Linglib.Phonology.Constraints.Basic
import Linglib.Phonology.OptimalityTheory.Tableau
import Linglib.Phonology.OptimalityTheory.Doubling
import Linglib.Phonology.OptimalityTheory.TableauSystem

/-!
# Three arguments for abstraction in phonology

Formalization of [berent-2026] (Glossa 12). Three experimental arguments that phonological
grammar is substance-free: it is *abstract* — the sonority-cline preference on onsets
(Figure 1, data from [berent-steriade-lennertz-vaknin-2007]) survives print presentation
and articulatory suppression, engaging Broca's area rather than motor cortex (§3.1);
*algebraic* — identity restrictions generalize to feature values unattested in the
speaker's language, Hebrew /θ/ and novel ASL handshapes (§3.2); and *amodal* — English
speakers project their spoken-language doubling constraints onto novel ASL signs, banning
identity in phonological contexts and preferring reduplication in morphological ones
(§3.3).

The three properties are carried by the substrate's types rather than restated:
abstractness is rank-invariance of the markedness function over the featureless `Sonority`
order; algebraicity is the parametric polymorphism of `mkOCP` (the constraint cannot
inspect what it compares); amodality is the same polymorphic constraint applying to any
feature type by construction, with the phonology–morphology reversal in
`OptimalityTheory.Doubling` and its experimental 2×2 in `Studies/BerentEtAl2016.lean`.

## Main definitions

* `onsetProfile`, `onsetMarkedness` — the rise/plateau/fall classification and the
  sonority-distance markedness of a two-consonant onset, on the abstract `Sonority` type.

## Main results

* `sonority_cline` — blif ≺ bnif ≺ bdif ≺ lbif: the four-point behavioral cline of
  Figure 1A derived from rank distance; a three-way profile alone cannot separate blif
  from bnif.
* `onsetMarkedness_rank_invariant`, `markedness_vs_profile` — markedness sees only the
  sonority ordering (substance-freeness), and refines the three-way profile.
* `amodal_doubling_reversal`, `phonSystem_predict_nonidentical`,
  `morphSystem_predict_reduplication` — Argument 3's reversal, from the substrate, lifted
  to probability-1 `ConstraintSystem` predictions.

## References

* [berent-2026] — the paper.
* [berent-steriade-lennertz-vaknin-2007] — the onset-cline data (Figure 1A).
* [berent-bat-el-brentari-dupuis-vaknin-nusbaum-2016] — the doubling 2×2, formalized in
  `Studies/BerentEtAl2016.lean`.
* [mccarthy-1986] — the OCP.
-/

open Phonology (Sonority)
open OptimalityTheory
open OptimalityTheory.Doubling

namespace Berent2026

open Core.Optimization Constraints OptimalityTheory

/-! ### Onset markedness: the sonority cline -/

/-- Onset sonority profile: the relation between C1 and C2 sonority in a two-consonant
    onset, on the abstract `Sonority` order. -/
inductive OnsetProfile where
  | rise
  | plateau
  | fall
  deriving DecidableEq, Repr

/-- Classify a two-consonant onset by its sonority profile. -/
def onsetProfile (c1 c2 : Sonority) : OnsetProfile :=
  if c1.rank < c2.rank then .rise
  else if c1.rank == c2.rank then .plateau
  else .fall

/-- Onset markedness from sonority distance: the smaller the rise, the worse (§3.1 —
    large rises over small rises over plateaus over falls). The pad `5` (the top rank)
    keeps ℕ-subtraction total; only the ordering of the values matters. -/
def onsetMarkedness : Constraint (Sonority × Sonority) :=
  fun (c1, c2) => 5 + c1.rank - c2.rank

/-- The four-point behavioral cline ([berent-2026] Figure 1A, data from
    [berent-steriade-lennertz-vaknin-2007]): blif ≺ bnif ≺ bdif ≺ lbif — stop+liquid ≺
    stop+nasal ≺ stop+stop ≺ liquid+stop — derived from rank distance on the abstract
    type. -/
theorem sonority_cline :
    onsetMarkedness (.stop, .liquid) < onsetMarkedness (.stop, .nasal) ∧
      onsetMarkedness (.stop, .nasal) < onsetMarkedness (.stop, .stop) ∧
        onsetMarkedness (.stop, .stop) < onsetMarkedness (.liquid, .stop) := by
  decide

/-- Substance-freeness as invariance: markedness depends only on the sonority ranks —
    onsets whose segments match in rank are treated identically, whatever their
    articulatory realization. -/
theorem onsetMarkedness_rank_invariant (c1 c2 d1 d2 : Sonority)
    (h1 : c1.rank = d1.rank) (h2 : c2.rank = d2.rank) :
    onsetMarkedness (c1, c2) = onsetMarkedness (d1, d2) := by
  simp [onsetMarkedness, h1, h2]

/-- The distance markedness refines the three-way profile: below `5` is a rise, `5` a
    plateau, above `5` a fall. -/
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

/-- The phonology–morphology reversal: the same identity ban yields opposite surface
    preferences depending on whether the morphological context licenses reduplication —
    amodal (it transfers from speech to sign) and L1-dependent. The proof is
    `OptimalityTheory.Doubling.doubling_reversal`; the experimental 2×2 is
    [berent-bat-el-brentari-dupuis-vaknin-nusbaum-2016]. -/
theorem amodal_doubling_reversal :
    (Tableau.ofRanking phonCandidates phonRanking).optimal
      = {DoublingParse.nonidentical} ∧
    (Tableau.ofRanking morphCandidates morphRanking).optimal
      = {DoublingParse.reduplication} :=
  doubling_reversal

/-! ### Probability-1 predictions

Both doubling tableaux lift to generic `ConstraintSystem`s via `tableauSystem`: the same
identity ban assigns probability 1 to `.nonidentical` in phonological contexts and to
`.reduplication` in morphological ones. -/

section PredictAPI
open Core.Optimization Constraints

/-- Phonological-context tableau as a generic `ConstraintSystem`. -/
noncomputable def phonSystem : ConstraintSystem DoublingParse (LexProfile Nat 2) :=
  tableauSystem (Tableau.ofRanking phonCandidates phonRanking)

/-- In phonological contexts, `.nonidentical` has probability 1. -/
theorem phonSystem_predict_nonidentical :
    phonSystem.predict DoublingParse.nonidentical = 1 :=
  tableauSystem_predict_unique_winner _ _ phon_prefers_XY

/-- Morphological-context tableau as a generic `ConstraintSystem`. -/
noncomputable def morphSystem : ConstraintSystem DoublingParse (LexProfile Nat 3) :=
  tableauSystem (Tableau.ofRanking morphCandidates morphRanking)

/-- In morphological contexts where reduplication is available, `.reduplication` has
    probability 1. -/
theorem morphSystem_predict_reduplication :
    morphSystem.predict DoublingParse.reduplication = 1 :=
  tableauSystem_predict_unique_winner _ _ morph_prefers_reduplication

end PredictAPI

end Berent2026
