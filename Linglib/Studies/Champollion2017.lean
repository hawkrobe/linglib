import Linglib.Semantics.Aspect.Stratified
import Linglib.Semantics.Events.CEM
import Linglib.Semantics.Plurality.Algebra
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Features.Aktionsart

/-!
# [champollion-2017]: Distributivity as a bridge between aspect and measurement

Paper-anchored study for *Parts of a Whole*. The book unifies four
ostensibly disjoint phenomena — predicative distributivity (Ch 4),
atelicity (Ch 5–6), and pseudopartitive measurement (Ch 7) — under one
higher-order property, *stratified reference* (`SR`, Ch 4 §4.6). A
distributive construction with Share `S`, Map `M`, granularity `g`
describing entity `x` is acceptable iff `SR_{M,g}(S)(x)` (Distributivity
Constraint, Ch 4 §4.6).

Substrate types `SR`, `SDR`, `SSR`, `SMR` and the construction
abbreviations live in `Semantics/Events/Aspect/Stratified.lean`.
This file consumes them against English Fragment verbs and stages the
empirical data the book argues over.

## Main definitions

* `DistProfile` — per-verb agent/theme distributivity tag bundle;
  Fragment-level metadata indexed against the substrate
  `VerbDistributivity` postulate class.
* `DistDatum` — empirical collective/distributive judgment record.
* `predictsSSR` — typological convenience function predicting `SSR`
  from a Vendler class. *Not* Champollion's own diagnostic — see
  Caveats.

## Caveats

* **Vendler classes are not Champollion primitives.** Champollion Ch 6
  explicitly disclaims Vendler classes ("Vendler classes do not appear
  as primitives in this book"). `predictsSSR` is a convenience bridge
  from linglib's Fragment Vendler tags to expected `SSR` behaviour;
  the underlying Champollion prediction is the cover/granularity-
  theoretic SR test.
* **Lexical cumulativity is assumed throughout.** Per [champollion-2017]
  §2.7.2, every verb's denotation is cumulative (`*[[V]] = [[V]]`).
  This is why `SSR_univ → CUM` does not hold and the Krifka-CUM contrast
  cannot be recast as an SR-vs-CUM contrast — see
  `Aspect/Stratified.lean` module docstring "Relation to Krifka's CUM/QUA".

## TODO

* **Push carts contrast (Ch 6 §6.4)** — the book's headline empirical
  case where SR predicts acceptable and Krifka 1998 predicts
  presupposition failure: *John pushed carts all the way to the store
  for fifty minutes* (Champollion's BACK-AND-FORTH scenario, Ch 6
  §6.4.1). Sketch ~80 LOC: scenario record, acceptability data,
  `SSR`-derived prediction, Krifka-divisive-reference-derived prediction
  (requires a `divisiveReference` substrate stub in or referenceable
  from `Studies/Krifka1998.lean`), divergence theorem.

* **Spatial SR / `SR_σ` (Ch 6)** — Champollion treats `SR_σ` (dimension
  = location trace) symmetrically with `SR_τ`; *for fifty meters* uses
  `SR_σ`. Substrate currently exposes only `SSR` (temporal). Add
  `SR_σ` in `Aspect/Stratified.lean` (~30 LOC), then exercise here on
  *the road meanders for a mile* / *the road ends in a mile* (~30 LOC).

* **SMR consumers (Ch 7 §7.4)** — substrate `SMR_univ` has no consumer.
  Stage Champollion's Ch 7 measurement-substance contrasts:
  predicted-acceptable *thirty liters of water*, *five feet of snow*,
  *two degrees Celsius of global warming*, *cool for five degrees*; and
  predicted-failures *thirty degrees Celsius of water*, *five pounds
  of book*. ~60 LOC. The *book* rejection is via at-issue-meaning +
  count-noun quantization, *not* SR — make the distinction explicit.

* **Distributivity Constraint as unification (Ch 4 §4.6)** — headline
  theorem: `eachConstr`, `forConstr`, `pseudopartConstr` all reduce to
  `DistConstr`. Substrate already supports this; state the three
  reductions (~5 LOC `rfl` per construction) plus a packaging corollary.
  ~25 LOC.

* **Lexical cumulativity assumption (§2.7.2)** — express as a
  `class LexicallyCumulativeFragment` carrying
  `verbIsCumulative : ∀ V ∈ verbs, AlgClosure V = V`, with English
  Fragment supplying the instance. Required for soundness of any
  theorem that imports the book's *for*-adverbial entry. ~20 LOC.

* **Granularity rescue of *waltz* (Ch 5 §5.4)** — concrete meaning
  postulate showing *waltz* has SR_{τ, λt[seconds(t)≤3]}, the only
  place in the book Champollion uses a numerical threshold. Couple
  with linglib `Time.seconds` measure. ~20 LOC.

* **Cover / SR equivalence (Ch 5 §5.4)** — substrate-bridge theorem
  `*λy[C(y)] x ↔ ∃C' ⊆ C [Cov(C', x)]`. Connects Champollion's SR to
  [schwarzschild-1996] cover semantics. Lives in
  `Aspect/Stratified.lean` as a property of `AlgClosure`; consumed
  here only if needed for Ch 6 push-carts proof. Substrate ~40 LOC.

* **`regular` predicate in *for*-adverbial entry (Ch 4)** — Champollion's
  lexical entry includes `... ∧ regular(M(e))` — a condition currently
  invisible in linglib's `forAdverbialMeaning`. Either define
  `regular : Interval Time → Prop` (~10 LOC substrate) or document
  why linglib drops it.

* **Theorem subjects via substrate predicates** — per CLAUDE.md
  theory-hub denotation discipline: replace `seeProfile.agentSDR = true`
  (Bool tag) with statements about `SDR_univ agentOf seePred` where
  `seePred : Event Time → Prop` is derived from Fragment `see.semantics`.
  Requires Fragment verbs to expose an `Event Time → Prop` denotation.

* **Convert `Bool` fields to `Prop` + `[Decidable]`** per CLAUDE.md
  "no `Bool` for predicate-shape data" — affects `DistProfile`,
  `DistDatum`, `predictsSSR`. ~15 LOC mechanical.

## What this file is NOT

* Not a re-statement of substrate primitives. `SR`, `SDR`, `SSR`, `SMR`
  live in `Aspect/Stratified.lean`; this file only consumes them.
* Not a Krifka 1998 vs SR proof harness. The empirical contrast lives
  in `Studies/Krifka1998.lean` (sister); the push-carts §6 will live
  there or be split across both.
* Not a Vendler-class theory anchor. Ch 6 explicitly disclaims Vendler
  classes; `predictsSSR` is a Fragment-tagging convenience.

## References

* [champollion-2017] (primary; SR machinery + Ch 4–7 empirical
  cases + §2.7.2 lexical cumulativity stance + Ch 6 vs-Krifka argument)
* [krifka-1998] (the divisive-reference target Champollion argues
  against in Ch 6; sister: `Studies/Krifka1998.lean`)
* [schwarzschild-2006] (the monotonic-measure-function predicate
  Champollion's `SMR` translates and weakens, Ch 7 §7.3)
* [link-1983] (the algebraic-closure `*` operator SR builds on)
* [dowty-1979] (the subinterval property SR generalizes, Ch 5)
-/

namespace Champollion2017

open English.Predicates.Verbal
open Semantics.Lexical
open Features
open Features (forXPrediction inXPrediction)
open _root_.Mereology
open Semantics.Plurality.Algebra (Materialization)

/-! ### Champollion §2.5/§2.7.2 algebraic substrate

Champollion's framework rests on two algebraic-substrate assumptions:

* **§2.5 — thematic roles and `τ` are sum homomorphisms.** Thematic
  roles (`agent`, `theme`, …) and the temporal trace
  `τ : Event → Interval` distribute over join:
  `θ(e₁ ⊔ e₂) = θ(e₁) ⊔ θ(e₂)`. This is exactly the `IsSumHom h`
  clause inside `Plurality.Algebra.Materialization`.

* **§2.7.2 — lexical cumulativity.** Every verb's denotation is closed
  under sum: `*[[V]] = [[V]]`. Equivalently, `AlgClosure ⟦V⟧ = ⟦V⟧`
  (`Algebra.star` is a fixed point on `⟦V⟧`), which is what Krifka's
  `CUM` predicate captures. This assumption underwrites his
  *for*-adverbial entry and the Distributivity Constraint. -/

section ThematicRolesAndCumulativity

variable {E I : Type*} [SemilatticeSup E] [SemilatticeSup I]

/-- Champollion §2.5: any sum-homomorphism `f : Event → α` (thematic
    role or `τ` runtime) packages into a `Materialization` (=
    `SupHom E I`). Bridges the unbundled `IsSumHom` typeclass and the
    bundled SupHom struct via `IsSumHom.toSupHom`. -/
def materializationOfSumHom (f : E → I) [hf : IsSumHom f] :
    Materialization E I :=
  hf.toSupHom

@[simp] theorem materializationOfSumHom_apply (f : E → I) [IsSumHom f] (x : E) :
    materializationOfSumHom f x = f x := rfl

/-- Champollion §2.7.2: lexical cumulativity for a single predicate is
    the assumption that `AlgClosure P = P` extensionally —
    equivalently, that `P` is a fixed point of `Algebra.star`. -/
def LexicallyCumulative {α : Type*} [SemilatticeSup α] (P : α → Prop) : Prop :=
  ∀ x, AlgClosure P x ↔ P x

/-- Lexical cumulativity entails `CUM` (Krifka 1989 D12): a verb
    denotation closed under `*` is closed under binary join. -/
theorem lexicallyCumulative_imp_cum {α : Type*} [SemilatticeSup α]
    {P : α → Prop} (h : LexicallyCumulative P) : CUM P := by
  intro x y hPx hPy
  exact (h _).mp (AlgClosure.sum (AlgClosure.base hPx) (AlgClosure.base hPy))

end ThematicRolesAndCumulativity

/-! ### Distributivity Profiles -/

/-- Per-verb distributivity profile: whether the verb distributes
    over atomic agents and/or themes. Mirrors the postulates in
    `VerbDistributivity` from `Events/Aspect/Stratified.lean`. -/
structure DistProfile where
  verb : String
  agentSDR : Bool   -- distributes over atomic agents?
  themeSDR : Bool   -- distributes over atomic themes?
  deriving Repr, DecidableEq

/-- "see" distributes on both agent and theme.
    "The boys saw the movies" → each boy saw each movie. -/
def seeProfile : DistProfile :=
  { verb := "see", agentSDR := true, themeSDR := true }

/-- "kill" distributes on theme only.
    "The boys killed the chicken" → the chicken was killed (by the group). -/
def killProfile : DistProfile :=
  { verb := "kill", agentSDR := false, themeSDR := true }

/-- "meet" does NOT distribute on agent (inherently collective).
    "The boys met" does NOT entail each boy met. -/
def meetProfile : DistProfile :=
  { verb := "meet", agentSDR := false, themeSDR := false }

/-- "eat" distributes on agent (each ate something).
    "The boys ate the pizza" → each boy ate (some) the pizza. -/
def eatProfile : DistProfile :=
  { verb := "eat", agentSDR := true, themeSDR := true }

def distProfiles : List DistProfile :=
  [seeProfile, killProfile, meetProfile, eatProfile]

/-! ### Distributivity Data -/

/-- Empirical collective/distributive ambiguity judgments. -/
structure DistDatum where
  sentence : String
  distributiveOK : Bool
  collectiveOK : Bool
  deriving Repr, DecidableEq

def seeDistDatum : DistDatum :=
  { sentence := "The boys saw the movie",
    distributiveOK := true, collectiveOK := true }

def killDistDatum : DistDatum :=
  { sentence := "The boys killed the chicken",
    distributiveOK := false, collectiveOK := true }

def meetDistDatum : DistDatum :=
  { sentence := "The boys met",
    distributiveOK := false, collectiveOK := true }

def eatDistDatum : DistDatum :=
  { sentence := "The boys ate the pizza",
    distributiveOK := true, collectiveOK := true }

def distData : List DistDatum :=
  [seeDistDatum, killDistDatum, meetDistDatum, eatDistDatum]

/-! ### Profile → Data Alignment -/

/-! Verify that the distributivity profiles predict the empirical data:
    agentSDR = true ↔ distributive reading available. -/

/-- Agent SDR predicts distributive reading availability. -/
theorem profiles_predict_data :
    (seeProfile.agentSDR = seeDistDatum.distributiveOK) ∧
    (killProfile.agentSDR = killDistDatum.distributiveOK) ∧
    (meetProfile.agentSDR = meetDistDatum.distributiveOK) ∧
    (eatProfile.agentSDR = eatDistDatum.distributiveOK) := ⟨rfl, rfl, rfl, rfl⟩

/-- All data consistently shows collective reading is available. -/
theorem all_collective_ok :
    distData.all (λ d => d.collectiveOK) = true := by decide

/-! ### VerbDistributivity Postulate Alignment -/

/-! The `VerbDistributivity` class from `Events/Aspect/Stratified.lean`
    axiomatizes `SDR_univ` for specific verbs.
    Verify our profiles match:
    - `see_agent_sdr`, `see_theme_sdr` ↔ seeProfile = (true, true)
    - `kill_theme_sdr`, `kill_agent_not_sdr` ↔ killProfile = (false, true)
    - `meet_agent_not_sdr` ↔ meetProfile.agentSDR = false -/

/-- See profile matches VerbDistributivity postulates. -/
theorem see_matches_postulates :
    seeProfile.agentSDR = true ∧ seeProfile.themeSDR = true := ⟨rfl, rfl⟩

/-- Kill profile matches VerbDistributivity postulates. -/
theorem kill_matches_postulates :
    killProfile.agentSDR = false ∧ killProfile.themeSDR = true := ⟨rfl, rfl⟩

/-- Meet profile matches VerbDistributivity postulates. -/
theorem meet_matches_postulates :
    meetProfile.agentSDR = false := rfl

/-- Fragment verb entries have the right Vendler class for SDR alignment. -/
theorem verb_vendler_for_sdr :
    see.toVerb.vendlerClass = some .state ∧
    kill.toVerb.vendlerClass = some .accomplishment ∧
    meet.toVerb.vendlerClass = some .achievement ∧
    eat.toVerb.vendlerClass = some .accomplishment :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### `SSR_univ` ↔ Vendler Bridge -/

/-! `SSR_univ` connects to Vendlerian atelicity via
    `qua_incompatible_with_ssr` and `forAdverbial_requires_ssr`:
    QUA(P) + `SSR_univ` P → ⊥ at any P-event, so telic predicates
    can't have `SSR_univ`. The atelic Vendler classes (states/activities)
    are expected to have `SSR_univ` and to accept *for X*; the telic
    classes (achievements/accomplishments) are not and accept *in X*.

    We verify this through the Vendler classification of fragment verbs.
    The Bool-valued `predictsSSR` below is the per-class typology
    prediction; bridging to the substrate-side `SSR_univ` predicate on
    a verb's denotation requires a verb-side `Event Time → Prop` denotation
    (theory-hub denotation discipline; follow-up work). -/

/-- Per-verb prediction of `SSR_univ` based on Vendler class:
    state / activity → atelic; achievement / accomplishment /
    semelfactive → not atelic. -/
def predictsSSR : Option VendlerClass → Bool
  | some .state => true
  | some .activity => true
  | some .achievement => false
  | some .accomplishment => false
  | some .semelfactive => false  -- punctual, no subinterval property
  | none => false

/-- States and activities are atelic → predict SSR → accept "for X". -/
theorem atelic_classes_accept_forX :
    forXPrediction .state = .accept ∧
    forXPrediction .activity = .accept := ⟨rfl, rfl⟩

/-- Achievements and accomplishments are telic → no SSR → accept "in X". -/
theorem telic_classes_accept_inX :
    inXPrediction .achievement = .accept ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl⟩

/-- "sleep" (state) → SSR expected. -/
theorem sleep_ssr : predictsSSR sleep.toVerb.vendlerClass = true := rfl

/-- "run" (activity) → SSR expected. -/
theorem run_ssr : predictsSSR run.toVerb.vendlerClass = true := rfl

/-- "arrive" (achievement) → no SSR. -/
theorem arrive_no_ssr : predictsSSR arrive.toVerb.vendlerClass = false := rfl

/-- "eat" (accomplishment) → no SSR. -/
theorem eat_no_ssr : predictsSSR eat.toVerb.vendlerClass = false := rfl

/-- "see" (state) → SSR expected. -/
theorem see_ssr : predictsSSR see.toVerb.vendlerClass = true := rfl

end Champollion2017
