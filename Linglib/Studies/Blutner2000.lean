module

public import Linglib.Pragmatics.Bidirectional
public import Linglib.Semantics.Presupposition.Accommodation
public import Mathlib.Data.Fintype.Pi

/-!
# Blutner (2000): Some aspects of optimality in natural language interpretation

[blutner-2000] evaluates form-meaning pairs bidirectionally (`Pragmatics/Bidirectional.lean`)
and argues from blocking that the two directions must constrain each other. The paper's
schematic tableaux set the strong and weak versions against each other: an unmarked and a
marked form, a stereotypical and a marked situation, with the constraints F (against marked
forms) and C (against marked situations). Under strong bidirection the marked form is blocked
in every interpretation, total blocking; restricting the generator does not help; only the
weak version yields [horn-1984]'s division of pragmatic labour, with the marked form taking
the marked situation. The presupposition section reconstructs the [van-der-sandt-1992] and
[geurts-1995] projection mechanism: the I-principle selects the projection site under
AvoidA ≫ BeStrong, and the Q-principle blocks accommodation whenever a simpler expression
alternative exists, Zeevat's generalization.

## Main definitions

* `Form`, `Situation`, `formMarkedness`, `situationMarkedness`, `tableau` — the schematic
  tableaux and their two constraints F and C.
* `ProjectionSite` — local, intermediate, global; mapped onto the standard accommodation
  levels by `ProjectionSite.toAccommodationLevel`.
* `ProjectionSite.projection`, `beStrong` — the projections as propositions over worlds and
  the strength grade derived from entailment among them; `dogAvoidA`, `catAvoidA`,
  `accidentAvoidA` the paper's binding data.

## Main results

* `strong_total_blocking`, `strong_restricted_gen` — the strong version blocks the marked
  form entirely, on the full generator and on the generator without the unmarked form's
  marked reading.
* `weak_division_of_labour` — the weak version pairs marked with marked; the strong version's
  optimal pairs are a proper subset (`strong_ssubset_weak`).
* `dog_global_accommodation` — every site accommodates, so BeStrong decides and global
  accommodation wins.
* `cat_intermediate_binding` — only the intermediate site binds, so AvoidA decides.
* `accommodation_blocked`, `accommodation_blocked_is_Q` — "??The car hit him" is blocked by
  the alternative "A car hit him" through the Q-principle.

## TODO

* The paper's dog tableau grades the intermediate projection above the local one, while its
  own discussion of the car case, and entailment, put the local projection (r ∧ p) ⇒ q
  below p ⇒ (q ∧ r); `beStrong` follows entailment. The winner is the same either way.

## References

* [blutner-2000] — the paper.
* [horn-1984] — the division of pragmatic labour.
* [van-der-sandt-1992], [geurts-1995] — the projection mechanism and its preferences.
* [asher-lascarides-1998] — the car-accident blocking datum.
-/

@[expose] public section

namespace Blutner2000

open BidirectionalOT

/-! ### Total blocking and the division of pragmatic labour

The paper's schematic tableau: forms `A₁` (unmarked) and `A₂` (marked, e.g. *cause to die*
beside *kill*), situations `τ₁` (stereotypical) and `τ₂` (marked), the constraint F violated
by the marked form and C by the marked situation. -/

/-- The unmarked and the marked form. -/
inductive Form where
  | unmarked
  | marked
  deriving DecidableEq, Repr

/-- The stereotypical and the marked situation. -/
inductive Situation where
  | stereotypical
  | marked
  deriving DecidableEq, Repr

/-- The constraint F: the marked form violates it. -/
def formMarkedness : Form × Situation → ℕ
  | (.marked, _) => 1
  | (.unmarked, _) => 0

/-- The constraint C: the marked situation violates it. -/
def situationMarkedness : Form × Situation → ℕ
  | (_, .marked) => 1
  | (_, .stereotypical) => 0

/-- The tableau's ranking, F over C. -/
def tableau : Form × Situation → List ℕ := profile [formMarkedness, situationMarkedness]

/-- The full generator: both forms express both situations. -/
def fullGen : Finset (Form × Situation) :=
  {(.unmarked, .stereotypical), (.unmarked, .marked), (.marked, .stereotypical),
    (.marked, .marked)}

/-- The generator with the unmarked form restricted to the stereotypical situation, the
paper's first attempt to avoid total blocking. -/
def restrictedGen : Finset (Form × Situation) :=
  {(.unmarked, .stereotypical), (.marked, .stereotypical), (.marked, .marked)}

/-- Total blocking: under strong bidirection only the unmarked form survives, in its
stereotypical reading, and the marked form is blocked in every interpretation. -/
theorem strong_total_blocking :
    strongOptimal fullGen tableau = {(.unmarked, .stereotypical)} := by decide

/-- Restricting the generator does not help the strong version: the marked form's marked
reading is still I-blocked by its stereotypical reading, so the marked form stays blocked. -/
theorem strong_restricted_gen :
    strongOptimal restrictedGen tableau = {(.unmarked, .stereotypical)} := by decide

/-- The division of pragmatic labour: under weak bidirection the unmarked form takes the
stereotypical situation and the marked form the marked one. -/
theorem weak_division_of_labour :
    superoptimal fullGen tableau = {(.unmarked, .stereotypical), (.marked, .marked)} := by decide

/-- The weak version admits strictly more pairs than the strong one on the full generator. -/
theorem strong_ssubset_weak : strongOptimal fullGen tableau ⊂ superoptimal fullGen tableau := by
  decide

/-- The paper introduces no ranking between F and C, and none is needed: every blocking
comparison differs in exactly one constraint, so the reverse ranking gives the same result. -/
theorem weak_division_of_labour_ranking_free :
    superoptimal fullGen (profile [situationMarkedness, formMarkedness]) =
      superoptimal fullGen tableau := by
  decide

/-! ### Projection sites

The presupposition section reconstructs [van-der-sandt-1992]'s projection mechanism for a
conditional "if p then q" whose consequent presupposes r. Each site yields a projection, a
proposition over the worlds fixing p, q and r, and BeStrong is derived from entailment among
the three projections rather than read off the paper's tableau (`## TODO`). The competitions
hold the form fixed, so they are I-principle competitions; `SentenceForm` has one constructor
and `superoptimal` reduces to the I-optimal site. -/

/-- Presupposition projection sites, following [van-der-sandt-1992]. -/
inductive ProjectionSite where
  | local
  | intermediate
  | global
  deriving DecidableEq, Fintype, Repr

/-- The atomic propositions: the antecedent `p`, the consequent `q` and the presupposition
`r`. -/
inductive Atom where
  | p
  | q
  | r
  deriving DecidableEq, Fintype

/-- A world fixes the truth of the three atoms. -/
abbrev World := Atom → Bool

/-- The projection of "if p then q", q presupposing r, with r accommodated at the site. -/
def ProjectionSite.projection : ProjectionSite → World → Prop
  | .global => fun w ↦ w .r ∧ (w .p → w .q)
  | .intermediate => fun w ↦ w .r ∧ w .p → w .q
  | .local => fun w ↦ w .p → w .q ∧ w .r

instance (s : ProjectionSite) (w : World) : Decidable (s.projection w) := by
  cases s <;> dsimp only [ProjectionSite.projection] <;> infer_instance

/-- BeStrong: the number of sites whose projection a site's projection fails to entail, so the
strongest projection scores `0`. `worlds` restricts the worlds, letting the antecedent bind
the presupposition. -/
def beStrong (worlds : Finset World) (s : ProjectionSite) : ℕ :=
  (Finset.univ.filter fun t : ProjectionSite ↦
    ¬ ∀ w ∈ worlds, s.projection w → t.projection w).card

/-- The single presuppositional sentence of each interpretation competition: the form is
held fixed and the projection sites race. -/
inductive SentenceForm where
  | sentence
  deriving DecidableEq, Repr

/-- The generator of the interpretation competitions: the sentence with each site. -/
def sites : Finset (SentenceForm × ProjectionSite) :=
  {(.sentence, .local), (.sentence, .intermediate), (.sentence, .global)}

/-! ### "If Peter has a dog, then his cat is gray"

The presupposition (Peter has a cat) finds no binder, so every site accommodates its marker
and AvoidA is tied; BeStrong decides. The global projection r ∧ (p ⇒ q) entails both others
and the local p ⇒ (q ∧ r) entails the intermediate (r ∧ p) ⇒ q, so global wins. -/

/-- AvoidA for the dog conditional: every site accommodates. -/
def dogAvoidA : SentenceForm × ProjectionSite → ℕ := fun _ ↦ 1

/-- BeStrong for the dog conditional: p, q and r vary independently. -/
def dogBeStrong (p : SentenceForm × ProjectionSite) : ℕ := beStrong Finset.univ p.2

/-- The derived grades: global strongest, then local, then intermediate. -/
theorem dogBeStrong_eq :
    dogBeStrong (.sentence, .global) = 0 ∧ dogBeStrong (.sentence, .local) = 1 ∧
      dogBeStrong (.sentence, .intermediate) = 2 := by
  decide

/-- AvoidA is tied, so BeStrong decides: global accommodation wins. -/
theorem dog_global_accommodation :
    superoptimal sites (profile [dogAvoidA, dogBeStrong]) = {(.sentence, .global)} := by decide

/-! ### "If Peter has a cat, then his cat is gray"

The antecedent is the presupposition, so the intermediate site binds rather than accommodates
and AvoidA ≫ BeStrong makes it the winner. With p = r the global projection p ∧ (p ⇒ q) is
strongest and the local and intermediate projections coincide, as the paper's footnote
notes. -/

/-- AvoidA for the cat conditional: only the intermediate site binds. -/
def catAvoidA : SentenceForm × ProjectionSite → ℕ
  | (.sentence, .intermediate) => 0
  | _ => 1

/-- The worlds of the cat conditional: the antecedent is the presupposition. -/
def catWorlds : Finset World := Finset.univ.filter fun w ↦ w .p = w .r

/-- BeStrong for the cat conditional. -/
def catBeStrong (p : SentenceForm × ProjectionSite) : ℕ := beStrong catWorlds p.2

/-- The derived grades: global strongest, local and intermediate tied. -/
theorem catBeStrong_eq :
    catBeStrong (.sentence, .global) = 0 ∧ catBeStrong (.sentence, .local) = 1 ∧
      catBeStrong (.sentence, .intermediate) = 1 := by
  decide

/-- AvoidA decides: the bound intermediate projection wins. -/
theorem cat_intermediate_binding :
    superoptimal sites (profile [catAvoidA, catBeStrong]) = {(.sentence, .intermediate)} := by
  decide

/-! ### Accommodation blocked by the Q-principle

"He had an accident. ??The car hit him." vs. "He had an accident. A car hit him." (the
paper's datum, attributed there to [asher-lascarides-1998]). From a car-neutral context both
continuations effect the same context change, but the definite requires accommodation; the
indefinite alternative blocks it. Zeevat's generalization: a presupposition trigger does not
accommodate iff any occurrence of it has a simple non-triggering expression alternative. -/

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
  {(.definite, .carHitHim), (.indefinite, .carHitHim)}

/-- AvoidA: the definite accommodates the car, the indefinite introduces it. -/
def accidentAvoidA : DefForm × AccidentMeaning → ℕ
  | (.definite, _) => 1
  | (.indefinite, _) => 0

/-- The indefinite blocks the definite: same meaning, no accommodation, so the definite is
pragmatically anomalous in car-neutral contexts. -/
theorem accommodation_blocked :
    superoptimal genAccident (profile [accidentAvoidA]) = {(.indefinite, .carHitHim)} := by
  decide

/-- The blocking is a Q-principle effect: a competing form with the same meaning is better. -/
theorem accommodation_blocked_is_Q :
    QBlocks (profile [accidentAvoidA]) ↑genAccident (.definite, .carHitHim) := by decide

/-- The indefinite satisfies both principles against the whole generator. -/
theorem indefinite_unblocked :
    ¬ Blocks (profile [accidentAvoidA]) ↑genAccident (.indefinite, .carHitHim) := by decide

/-! ### Bridge to the accommodation levels

The projection sites are the accommodation levels of the Heim/Lewis/van der Sandt tradition
(`Presupposition.Accommodation`). -/

open Presupposition.Accommodation

/-- Map projection sites to the standard accommodation levels; a conditional has one
intermediate site, indexed `0`. -/
def ProjectionSite.toAccommodationLevel : ProjectionSite → AccommodationLevel
  | .local => .local
  | .intermediate => .intermediate 0
  | .global => .global

theorem global_is_global_accommodation :
    ProjectionSite.global.toAccommodationLevel = AccommodationLevel.global := rfl

theorem local_is_local_accommodation :
    ProjectionSite.local.toAccommodationLevel = AccommodationLevel.local := rfl

end Blutner2000
