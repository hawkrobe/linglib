import Linglib.Core.Optimization.Evaluation
import Linglib.Pragmatics.Superoptimal
import Linglib.Pragmatics.Bidirectional
import Linglib.Semantics.Presupposition.Accommodation

/-!
# Presupposition projection in bidirectional OT

Formalization of §4 of [blutner-2000] (Journal of Semantics 17), which reconstructs the
[van-der-sandt-1992] and [geurts-1995] projection mechanism in bidirectional OT: the
I-principle selects the preferred projection site under the ranking AvoidA ≫ BeStrong
(the paper's C1/C2 and R), and the Q-principle blocks accommodation whenever a simpler
expression alternative exists — Zeevat's generalization ((23)): a trigger does not
accommodate iff it has a simple non-triggering expression alternative. The §2–3
apparatus (strong vs. weak bidirection ((6)/(11)), total and partial blocking, Horn's
division of pragmatic labour) lives in `Pragmatics/Superoptimal.lean` and
`Pragmatics/Bidirectional.lean`; this file consumes it for the §4 case studies.

## Main definitions

* `ProjectionSite` — local, intermediate, global; mapped onto the standard
  accommodation levels by `ProjectionSite.toAccommodationLevel`.
* `dogProfile`, `catProfile` — the [AvoidA, BeStrong] profiles of tableaux (17) and
  (18) for the conditionals (15) and (16).

## Main results

* `dog_global_accommodation` — (15)/(17): every site accommodates, so BeStrong decides
  and global accommodation wins.
* `cat_intermediate_binding` — (16)/(18): only the intermediate site binds, so AvoidA
  decides.
* `accommodation_blocked`, `accommodation_blocked_is_Q` — (22): "??The car hit him" is
  blocked by the alternative "A car hit him" — the Q-principle.

## References

* [blutner-2000] — the paper.
* [van-der-sandt-1992], [geurts-1995] — the projection mechanism and its preferences
  (binding over accommodation; higher sites, ceteris paribus).
* [asher-lascarides-1998] — the car-accident blocking datum of (22).
-/

namespace Blutner2000

open Core.Optimization.Evaluation
open Pragmatics.Bidirectional

/-! ### Projection sites -/

/-- Presupposition projection sites, following [van-der-sandt-1992]. -/
inductive ProjectionSite where
  | local
  | intermediate
  | global
  deriving DecidableEq, Repr

/-- The single presuppositional sentence of each §4 interpretation competition: the
    form is held fixed and the projection sites race. -/
inductive SentenceForm where
  | sentence
  deriving DecidableEq, Repr

/-! ### (15)/(17): "If Peter has a dog, then his cat is gray"

The presupposition (Peter has a cat) finds no binder, so every site accommodates its
marker and AvoidA is tied; BeStrong decides. The strength grades follow tableau (17):
the global projection r ∧ (p ⇒ q) entails both others, and the local p ⇒ (q ∧ r)
entails the intermediate (r ∧ p) ⇒ q — the tableau's u > v and w > v — so the
intermediate projection is weakest. -/

def dogGen : Finset (SentenceForm × ProjectionSite) :=
  { (.sentence, .local), (.sentence, .intermediate), (.sentence, .global) }

/-- Tableau (17) profile, [AvoidA, BeStrong]; lower BeStrong = stronger. -/
def dogProfile : SentenceForm × ProjectionSite → List Nat
  | (.sentence, .global)       => [1, 0]  -- r ∧ (p ⇒ q): strongest
  | (.sentence, .local)        => [1, 1]  -- p ⇒ (q ∧ r)
  | (.sentence, .intermediate) => [1, 2]  -- (r ∧ p) ⇒ q: weakest

/-- (15): AvoidA is tied, so BeStrong decides — global accommodation wins. -/
theorem dog_global_accommodation :
    superoptimal dogGen dogProfile
      = { (SentenceForm.sentence, ProjectionSite.global) } := by
  decide

/-! ### (16)/(18): "If Peter has a cat, then his cat is gray"

The antecedent supplies a binder at the intermediate site, which factors rather than
accommodates; AvoidA ≫ BeStrong makes it the winner. The strength grades follow
tableau (18): global p ∧ (p ⇒ q) is strongest, and — ignoring reference markers — the
local and intermediate projections coincide (the tableau's w = v; fn. 13). -/

def catGen : Finset (SentenceForm × ProjectionSite) :=
  { (.sentence, .local), (.sentence, .intermediate), (.sentence, .global) }

/-- Tableau (18) profile: only the intermediate site binds (AvoidA 0). -/
def catProfile : SentenceForm × ProjectionSite → List Nat
  | (.sentence, .global)       => [1, 0]  -- p ∧ (p ⇒ q): strongest
  | (.sentence, .intermediate) => [0, 1]  -- bound (factored)
  | (.sentence, .local)        => [1, 1]  -- ≡ intermediate in strength (fn. 13)

/-- (16): AvoidA decides — the bound intermediate projection wins. -/
theorem cat_intermediate_binding :
    superoptimal catGen catProfile
      = { (SentenceForm.sentence, ProjectionSite.intermediate) } := by
  decide

/-! ### (22): accommodation blocked by the Q-principle

"He had an accident. ??The car hit him." vs. "He had an accident. A car hit him."
([asher-lascarides-1998]'s datum, the paper's (22)). From a car-neutral context both
continuations effect the same context change, but the definite requires accommodation;
the indefinite alternative blocks it. Zeevat's (23) generalizes: a presupposition
trigger does not accommodate iff it has a simple non-triggering expression
alternative. -/

/-- The presuppositional definite and its non-triggering indefinite alternative. -/
inductive DefForm where
  | definite
  | indefinite
  deriving DecidableEq, Repr

/-- The shared context-change result. -/
inductive AccidentMeaning where
  | carHitHim
  deriving DecidableEq, Repr

def genAccident : Finset (DefForm × AccidentMeaning) :=
  { (.definite, .carHitHim), (.indefinite, .carHitHim) }

/-- Profile, [markedness, accommodation cost]: the definite accommodates, the
    indefinite does not. -/
def profileAccident : DefForm × AccidentMeaning → List Nat
  | (.definite,   .carHitHim) => [1, 0]
  | (.indefinite, .carHitHim) => [0, 0]

/-- The indefinite blocks the definite: same meaning, fewer violations — the definite
    is pragmatically anomalous in car-neutral contexts. -/
theorem accommodation_blocked :
    superoptimal genAccident profileAccident
      = { (DefForm.indefinite, AccidentMeaning.carHitHim) } := by
  decide

/-- List form of `genAccident` for the `satisfiesQ`/`satisfiesI` API. -/
def genAccidentList : List (DefForm × AccidentMeaning) :=
  [(.definite, .carHitHim), (.indefinite, .carHitHim)]

/-- The blocking is a Q-principle effect: a competing form with the same meaning is
    better. -/
theorem accommodation_blocked_is_Q :
    Pragmatics.Bidirectional.satisfiesQ
      genAccidentList profileAccident (.definite, .carHitHim) = false := by
  decide

/-- The indefinite satisfies both principles. -/
theorem indefinite_satisfies_both :
    Pragmatics.Bidirectional.satisfiesQ
      genAccidentList profileAccident (.indefinite, .carHitHim) = true ∧
    Pragmatics.Bidirectional.satisfiesI
      genAccidentList profileAccident (.indefinite, .carHitHim) = true :=
  ⟨by decide, by decide⟩

/-! ### Bridge to the accommodation levels

The projection sites are the accommodation levels of the Heim/Lewis/van der Sandt
tradition (`Presupposition.Accommodation`). -/

open Presupposition.Accommodation

/-- Map projection sites to the standard accommodation levels. -/
def ProjectionSite.toAccommodationLevel : ProjectionSite → AccommodationLevel
  | .local        => .local
  | .intermediate => .intermediate 0
  | .global       => .global

theorem global_is_global_accommodation :
    ProjectionSite.global.toAccommodationLevel = AccommodationLevel.global := rfl

theorem local_is_local_accommodation :
    ProjectionSite.local.toAccommodationLevel = AccommodationLevel.local := rfl

end Blutner2000
