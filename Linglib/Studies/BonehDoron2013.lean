import Linglib.Semantics.Quantification.Counting
import Linglib.Semantics.Genericity.Basic
import Linglib.Semantics.Aspect.Basic
import Linglib.Semantics.Mereology
import Linglib.Semantics.Modality.Kratzer.Ordering

/-!
# Boneh and Doron 2013: Hab and Gen in the expression of habituality

[boneh-doron-2013] (in the OUP *Genericity* volume) argue that habituality
involves two distinct covert operators. Gen (21) is the familiar modalized
universal; Hab (13) is a modalized existential over sums of events — an
iteration (14) in every world of a gnomic modal base, with only a
disposition-indicating INIT event (15) required in the actual world. The
auxiliaries mark neither: *would* marks mood (a special case of Gen, (22)),
and *used to* is the imperfective under a retrospective aspect (18)–(19),
locating the reference interval wholly before the perspective interval. The
operators are built here on the library's own objects: iteration on the
[link-1983] closure, the modal base of [kratzer-1981], Klein's imperfective,
and [pancheva-2003]'s final-subinterval perfect.

## Main definitions

* `iter`, `hab` — the chapter's (14) and (13)/(15), on `Mereology.AlgClosure`
  and `Modality.Kratzer.ModalBase`.
* `retro`, `usedToOp`, `perfectOp` — (19b), (18), and the (34a) perfect over
  `IntervalPred`, with (19a) as the substrate's `IMPF`.
* `HabitualForm`, `admitsViewpoint`, `admitsPerspective` — Table (41).

## Main results

* `iter_impossible_of_unrepeatable`, `same_object_infelicity`,
  `gen_admits_fresh_objects` — the (4)–(8) contrast derived: an indefinite
  scoping over Hab forces an unrepeatable event, while Gen's universal lets
  it vary.
* `hab_without_actual_iteration` — (13)–(17): Hab holds with a single actual
  initiating event, iteration living only in the accessible worlds.
* `retro_perfect_forces_point`, `usedTo_of_persisting_state` — (30)–(35): the
  retrospective and the perfect exclude each other except at a degenerate
  perspective, and nothing bounds the state itself — retrospectivity of the
  state is a cancellable implicature.
* `restrictor_contrast`, `sameObjectParallel`, `actualization_contrast`,
  `individual_level_contrast`, `would_vs_usedTo_puzzle` — the chapter's
  judgment pairs ((2), (4), (6)–(7), (42), (47)–(48)).
* `gen_skeleton` — Gen's reduction to the relativized restricted universal.

## References

* [boneh-doron-2013] — the chapter.
* [link-1983], [kratzer-1981], [klein-1994], [pancheva-2003] — the sum
  closure, modal base, imperfective, and final-subinterval substrate.
* [del-prete-2013] — the same volume's Italian Same-Object Effect.
-/

namespace BonehDoron2013

open Quantification
open Genericity (Situation traditionalGEN)
open Aspect (Perfectivity IntervalPred IMPF)
open Modality.Kratzer (ModalBase accessibleWorlds)

/-! ### Hab against Gen ((4)–(8), (13)–(15))

Gen needs an explicit restrictor; without one only Hab applies, and an
indefinite can only scope over it, as in (8) `∃x [cigarette(x) ∧ Hab e
smoke(e, Mary, x)]`. The contrast between (4a) and (4b) is then a theorem:
smoking is unrepeatable per cigarette, so the wide-scope form is
contradictory while Gen's (5a) is satisfiable with a fresh cigarette per
event. -/

/-- (14): iteration — a sum of P-events with at least two distinct proper
P-parts, on the [link-1983] closure. -/
def iter {E : Type*} [SemilatticeSup E] (P : E → Prop) (e : E) : Prop :=
  Mereology.AlgClosure P e ∧ ∃ e₁ < e, ∃ e₂ < e, P e₁ ∧ P e₂ ∧ e₁ ≠ e₂

/-- An unrepeatable predicate cannot iterate: no event carries two distinct
proper parts of a once-only happening. -/
theorem iter_impossible_of_unrepeatable {E : Type*} [SemilatticeSup E] {P : E → Prop}
    (h : ∀ e₁ e₂, P e₁ → P e₂ → e₁ = e₂) (e : E) : ¬ iter P e :=
  fun ⟨_, _, _, _, _, h₁, h₂, hne⟩ => hne (h _ _ h₁ h₂)

/-- (4b)/(8): with the indefinite scoping over Hab, the same object recurs
through the iteration; when the predicate is unrepeatable per object — one
smoking per cigarette — the reading is contradictory. [del-prete-2013]'s
Italian Same-Object Effect is the same configuration. -/
theorem same_object_infelicity {E C : Type*} [SemilatticeSup E]
    {smoke : E → C → Prop} {cig : C → Prop}
    (hOnce : ∀ c e₁ e₂, smoke e₁ c → smoke e₂ c → e₁ = e₂) :
    ¬ ∃ c, cig c ∧ ∃ e, iter (smoke · c) e :=
  fun ⟨c, _, e, hIter⟩ => iter_impossible_of_unrepeatable (hOnce c) e hIter

/-- (4a)/(5a): Gen's universal lets the indefinite scope below, so the same
unrepeatability premise is satisfiable — a fresh cigarette per event. -/
theorem gen_admits_fresh_objects :
    ∃ smoke : Bool → Bool → Prop,
      (∀ c e₁ e₂, smoke e₁ c → smoke e₂ c → e₁ = e₂) ∧
        everyOn (Finset.univ : Finset Bool) (fun _ => True) (fun e => ∃ c, smoke e c) :=
  ⟨(· = ·), fun _ _ _ h₁ h₂ => h₁.trans h₂.symm, fun e _ _ => ⟨e, rfl⟩⟩

/-- (13) with (15): Hab requires the disposition-indicating INIT event in the
actual world and an iteration in every accessible world of the gnomic modal
base ([kratzer-1981]). The paper leaves "indicating a disposition"
unanalyzed, so it is a parameter; the temporal anchoring `τ(s) ⊆ τ(e)` is
suppressed with the event times. -/
def hab {W E : Type*} [SemilatticeSup E] (P : E → W → Prop) (mb : ModalBase W)
    (indicatesDisposition : W → Prop) (w : W) : Prop :=
  indicatesDisposition w ∧ ∀ w' ∈ accessibleWorlds mb w, ∃ e, iter (P · w') e

/-- (16)–(17), (42a–b): Hab is dispositional — it holds on the strength of a
single actual initiating event, with the iteration living only in the
accessible worlds. Nothing beyond INIT is actualized. -/
theorem hab_without_actual_iteration :
    ∃ (P : Finset ℕ → Bool → Prop) (mb : ModalBase Bool),
      hab P mb (· = false) false ∧ ¬ ∃ e, iter (P · false) e := by
  refine ⟨fun e w' => match w' with | true => e.Nonempty ∧ e ⊆ {0, 1} | false => e = {0},
    fun _ => [(· = true)], ⟨rfl, ?_⟩, ?_⟩
  · intro w' hw'
    have hw : w' = true := by
      simpa [accessibleWorlds, Intensional.Premise.propIntersection] using hw'
    subst hw
    exact ⟨{0} ⊔ {1}, .sum (.base (by decide)) (.base (by decide)),
      {0}, by decide, {1}, by decide, by decide, by decide, by decide⟩
  · rintro ⟨e, -, e₁, -, e₂, -, h₁, h₂, hne⟩
    exact hne (h₁.trans h₂.symm)

/-- Gen's denotation is the canonical relativized restricted universal, with
the restrictor conjoined from a normalcy predicate and an overt restrictor.
Hab admits no such reduction: its force is the existential of (13). -/
theorem gen_skeleton
    (sits : List Situation) (normal restrictor scope : Situation → Bool) :
    traditionalGEN sits normal restrictor scope =
      everyOn sits.toFinset (fun s => (normal s && restrictor s) = true)
        (fun s => scope s = true) := rfl

/-! ### used to: the imperfective under a retrospective ((18)–(19), (30)–(35))

The auxiliary decomposes as retrospective over imperfective. (19a) is
Klein's imperfective — the substrate's `IMPF` — and (19b) locates the
reference interval before the perspective interval, [kamp-reyle-1993]'s P.
Imperfectivity and retrospectivity of *used to* in Table (41) thus hold by
construction. -/

/-- (19b): the retrospective — some reference interval satisfying the
description lies wholly before the perspective interval. -/
def retro {W Time : Type*} [LinearOrder Time] (A : IntervalPred W Time) :
    IntervalPred W Time :=
  fun w p => ∃ i, A w i ∧ i.isBefore p

/-- (18): *used to* — the retrospective over the imperfective. -/
def usedToOp {W Time : Type*} [LinearOrder Time] (P : W → Event Time → Prop) :
    IntervalPred W Time :=
  retro (IMPF P)

/-- (34a): the perfect — the perspective is a final subinterval of the
reference interval ([pancheva-2003]'s PTS, from the substrate). -/
def perfectOp {W Time : Type*} [LinearOrder Time] (A : IntervalPred W Time) :
    IntervalPred W Time :=
  fun w p => ∃ i, A w i ∧ p.finalSubinterval i

/-- (32)–(34): one reference interval serves the retrospective and the
perfect at once only for a degenerate instantaneous perspective. The two
form the Horn scale behind the retrospectivity implicature (31)–(33). -/
theorem retro_perfect_forces_point {Time : Type*} [LinearOrder Time]
    {i p : NonemptyInterval Time} (hb : i.isBefore p) (hf : p.finalSubinterval i) :
    p.IsPoint :=
  le_antisymm p.fst_le_snd (hf.2.trans_le hb)

/-- (30): retrospectivity of the *state* is cancellable ("… used to go to.
Still do."): (19a) bounds only the reference interval, so a state whose
runtime strictly contains a pre-perspective reference interval satisfies
*used to* however far the state runs — through the perspective included. -/
theorem usedTo_of_persisting_state {W Time : Type*} [LinearOrder Time]
    {P : W → Event Time → Prop} {w : W} {e : Event Time} (hP : P w e)
    {i p : NonemptyInterval Time} (hie : i < e.τ) (hip : i.isBefore p) :
    usedToOp P w p :=
  ⟨i, ⟨e, hie, hP⟩, hip⟩

/-! ### The three forms and Table (41) -/

/-- The English past-habituality forms of (1). -/
inductive HabitualForm where
  | simpleForm
  | usedTo
  | would
  deriving DecidableEq, Repr

/-- Internal vs. retrospective perspective, Table (41)'s second dimension. -/
inductive PerspectiveType where
  | internal
  | retrospective
  deriving DecidableEq, Repr

/-- Table (41), viewpoint column: the simple form takes either viewpoint
((26)–(27)); the periphrastic forms are imperfective only. -/
def admitsViewpoint : HabitualForm → Perfectivity → Prop
  | .simpleForm, _ => True
  | _, .imperfective => True
  | _, .perfective => False

/-- Table (41), perspective column: *used to* is retrospective, *would*
internal, the simple form either ((35)–(40)). -/
def admitsPerspective : HabitualForm → PerspectiveType → Prop
  | .simpleForm, _ => True
  | .usedTo, .retrospective => True
  | .usedTo, .internal => False
  | .would, .internal => True
  | .would, .retrospective => False

/-! ### The chapter's judgments -/

/-- An English judgment from the chapter. -/
structure EnglishDatum where
  sentence : String
  form : HabitualForm
  felicitous : Bool
  exNumber : String
  deriving Repr

/-- (4a): felicitous — *after dinner* supplies Gen's restrictor, and the
indefinite scopes below it, as in (5a). -/
def maryCigaretteAfterDinner : EnglishDatum :=
  { sentence := "Mary smokes a cigarette after dinner"
    form := .simpleForm, felicitous := true, exNumber := "(4a)" }

/-- (4b): no explicit restrictor, so only Hab applies; the indefinite scopes
over it, (8), and `same_object_infelicity` bites. -/
def maryCigarette : EnglishDatum :=
  { sentence := "#Mary smokes a cigarette"
    form := .simpleForm, felicitous := false, exNumber := "(4b)" }

/-- (6b): the same-object reading — one flower growing out repeatedly — is
plausible, so the sentence survives on it. -/
def flowerGrows : EnglishDatum :=
  { sentence := "A flower grows out behind the old shed"
    form := .simpleForm, felicitous := true, exNumber := "(6b)" }

/-- (7b): the indefinite scopes over the adverbial's quantifier — the same
rabbit killed repeatedly — which is absurd. -/
def maxKilledRabbit : EnglishDatum :=
  { sentence := "#Max killed a rabbit repeatedly"
    form := .simpleForm, felicitous := false, exNumber := "(7b)" }

/-- (2c): *would* requires the restricting episodes to be explicit or
already presupposed; the opera scene supplies no such restriction, so Gen
goes unrestricted. -/
def wouldDressNoContext : EnglishDatum :=
  { sentence := "#In the good old days, people would dress elegantly"
    form := .would, felicitous := false, exNumber := "(2c)" }

/-- (2d): the purpose clause supplies the restriction. -/
def wouldDressWithContext : EnglishDatum :=
  { sentence := "In the good old days, people would dress elegantly to go to the opera"
    form := .would, felicitous := true, exNumber := "(2d)" }

/-- (42a): true on a single actual episode — episodic, or Hab via
`hab_without_actual_iteration`. -/
def sheWentByBus : EnglishDatum :=
  { sentence := "She went to work by bus"
    form := .simpleForm, felicitous := true, exNumber := "(42a)" }

/-- (42b): *would* is Gen — about the accessible worlds, not actual
iteration — so a single episode suffices. -/
def sheWouldGoByBus : EnglishDatum :=
  { sentence := "She would go to work by bus"
    form := .would, felicitous := true, exNumber := "(42b)" }

/-- (42c): false on a single episode. The chapter derives the actualization
requirement from the aspect: the retrospective's extended reference interval
characterizes a period, and only actualized episodes can characterize one. -/
def sheUsedToGoByBus : EnglishDatum :=
  { sentence := "She used to go to work by bus"
    form := .usedTo, felicitous := false, exNumber := "(42c)" }

/-- (48a): *used to* is an aspectual operator selecting states, individual-
level states included, so no habituality is needed here at all. -/
def usedToStand : EnglishDatum :=
  { sentence := "The London Bridge used to stand on the Thames, now it stands in Arizona"
    form := .usedTo, felicitous := true, exNumber := "(48a)" }

/-- (48b): habitual *would* is Gen, and an individual-level predicate is
incompatible with an episodic restrictor; a definite subject supplies no
nominal one. -/
def wouldStand : EnglishDatum :=
  { sentence := "*The London Bridge would stand on the Thames, now it stands in Arizona"
    form := .would, felicitous := false, exNumber := "(48b)" }

/-- (3a)/(47a): the indefinite singular provides Gen's restrictor — a
restrictor of objects, not events — so *would* tolerates the individual-level
predicate. -/
def wouldKnowLatin : EnglishDatum :=
  { sentence := "a French teacher would know Latin"
    form := .would, felicitous := true, exNumber := "(3a)/(47a)" }

/-- (3b)/(47b): *used to* is aspectual, not quantificational, so the
indefinite singular finds no operator below Gen; Gen must scope over the
whole clause, (50b), predicating a past-cut-off habit of teachers in
general — the wrong truth conditions. A bare plural instead denotes the kind
and combines directly, (50a). -/
def usedToKnowLatin : EnglishDatum :=
  { sentence := "*a French teacher used to know Latin"
    form := .usedTo, felicitous := false, exNumber := "(3b)/(47b)" }

/-- (4): Gen with a restrictor is fine; Hab with a wide-scope indefinite is
not — the derived halves are `gen_admits_fresh_objects` and
`same_object_infelicity`. -/
theorem restrictor_contrast :
    maryCigaretteAfterDinner.felicitous = true ∧ maryCigarette.felicitous = false :=
  ⟨rfl, rfl⟩

/-- (6b)/(7b): the same-object reading decides felicity — plausible for the
flower, absurd for the rabbit. [del-prete-2013]'s Italian SOEs parallel
these judgments. -/
theorem sameObjectParallel :
    flowerGrows.felicitous = true ∧ maxKilledRabbit.felicitous = false :=
  ⟨rfl, rfl⟩

/-- (42): one actual episode verifies the simple form and *would* but not
*used to*. -/
theorem actualization_contrast :
    sheWentByBus.felicitous = true ∧ sheWouldGoByBus.felicitous = true ∧
      sheUsedToGoByBus.felicitous = false :=
  ⟨rfl, rfl, rfl⟩

/-- (48): *used to* selects individual-level states; habitual *would* cannot
restrict Gen with them. -/
theorem individual_level_contrast :
    usedToStand.felicitous = true ∧ wouldStand.felicitous = false :=
  ⟨rfl, rfl⟩

/-- (3)/(47): the indefinite singular restricts Gen under *would* but has no
host under aspectual *used to*. -/
theorem would_vs_usedTo_puzzle :
    wouldKnowLatin.felicitous = true ∧ usedToKnowLatin.felicitous = false :=
  ⟨rfl, rfl⟩

end BonehDoron2013
