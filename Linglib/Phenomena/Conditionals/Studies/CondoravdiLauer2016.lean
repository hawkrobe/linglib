import Linglib.Theories.Semantics.Attitudes.CondoravdiLauer
import Linglib.Theories.Semantics.Conditionals.Restrictor
import Linglib.Data.Examples.Schema
import Mathlib.Tactic.FinCases

/-!
# @cite{condoravdi-lauer-2016} — Anankastic conditionals are just conditionals

C&L's central claim: anankastics (eq. 1, the Harlem sentence) need no
special compositional treatment, provided (i) `want` is given the
effective-preference reading from § 5 (substrate at
`Theories/Semantics/Attitudes/CondoravdiLauer.lean`) and (ii) the
conditional has the double-modal `NEC[ψ][MODAL[φ]]` LF from § 6. The
Hoboken problem (§ 2.3, § 7.1.1) is then solved by *consistency-driven
vacuous truth*: a hypothetical effective preference for Harlem is
incompatible with the actual effective preference for Hoboken, so the
NEC's modal-base restriction by the antecedent is empty — and the
universal NEC is vacuously satisfied.

## Scope

In:
* `harlemLF` — the § 7.1 eq. (87b)/(88) Harlem LF as a composition of
  existing substrate primitives.
* `doubleModalLF` — the § 6.1 eq. (77) double-modal schema (inline; not
  promoted to substrate per the ≥ 2-consumer graduation rule).
* `HobokenScenario` — minimal 2-world model + the § 7.1.1 headline
  theorem `harlem_true_in_hoboken_scenario`.

Out: § 3 review (see `Phenomena/Conditionals/Studies/vonFintelIatridou2005.lean`);
§ 4 full near-anankastic taxonomy; § 6.2 Sobel sequences; § 7.1.4
informational asymmetry; § 7.2.3 weak antecedents/consequents.
Strong-vs-weak modal distinction is set aside per paper fn. 12.

## TODO

A `PreferenceStructure → Kratzer.OrderingSource` bridge would let the
inner MUST be evaluated non-trivially in scenarios where the antecedent
restriction does *not* collapse to vacuous truth. The Hoboken theorem
doesn't need it (vacuous truth wins), but a richer-information scenario
or the § 7.2 near-anankastic family would. Substrate work, not
paper-specific; tracked in
`Core/Order/PreferenceStructure/MaxInducedOrdering.lean:12-15`.

## Cross-references

* `Theories/Semantics/Attitudes/CondoravdiLauer.lean` — `wantEP` and
  `wantEP_jointly_belief_consistent` (the load-bearing lemma).
* `Phenomena/Conditionals/Studies/vonFintelIatridou2005.lean` — vF&I's
  primary-secondary ordering source analysis that C&L 2016 critiques
  (paper § 3.2.2).
* `Phenomena/Modality/Studies/PhillipsBrown2025.lean` § 11 — sibling
  no-go theorem `condoravdiLauer_blocks_simultaneous_pq_and_negpq`,
  same consistency-of-EP delegation pattern.
-/

namespace Phenomena.Conditionals.Studies.CondoravdiLauer2016

open Semantics.Attitudes.CondoravdiLauer
open Semantics.Modality.Kratzer
open Semantics.Conditionals.Restrictor
open Core.Order

universe u

/-! ### § 6.1 Double-modal compositional schema (eq. 77) -/

/-- @cite{condoravdi-lauer-2016} eq. (77): `If ψ, MODAL[φ]` parses as
`NEC[ψ][MODAL[φ]]` when the consequent contains an overt modal claim.
Composed from `conditionalNecessity` (the outer NEC restriction by
antecedent, from `Theories/Semantics/Conditionals/Restrictor.lean`) and
an arbitrary world-indexed inner-modal proposition.

This is the schema instantiated by `harlemLF`. Kept inline rather than
promoted to `Theories/Semantics/Conditionals/DoubleModal.lean` because
no second paper-anchored study currently consumes it (≥ 2-consumer
graduation rule). Kaufmann & Schwager 2009 on conditional imperatives
would be the natural second consumer. -/
def doubleModalLF {W : Type u} (fOuter : ModalBase W) (gOuter : OrderingSource W)
    (ψ : W → Prop) (innerModal : W → Prop) (w : W) : Prop :=
  conditionalNecessity fOuter gOuter ψ innerModal w

/-! ### § 7.1 The Harlem LF (eq. 87b / 88) -/

/-- @cite{condoravdi-lauer-2016} eq. (88) at the operator level: the
Harlem-sentence LF parameterised over its four contextual backgrounds.
`NEC_{fBelS, gNorm}[wantEP(Ad, Harlem)] [MUST_{fHist, gInner}[ATrain]]`.

The four contextual parameters:
* `fBelS` — modal base of NEC, "speaker's true beliefs" (paper p. 41).
* `gNorm` — ordering source of NEC, "stereotypical" (paper § 6.1).
* `fHist` — modal base of MUST, "historical alternatives at time t"
  (paper p. 42; `historicalNecessity` substrate exists at
  `Theories/Semantics/Modality/Temporal.lean:119`, but the v1 LF here
  takes an arbitrary modal base because the Hoboken theorem doesn't
  constrain it).
* `gInner` — ordering source of MUST. Paper eq. (88) uses `g_epA`
  (= `maxOrderingSource EP Ad`), but the bridge from `Set (Set W)` to
  the `List`-valued `OrderingSource` is deferred (see TODO in the
  module docstring); v1 takes `gInner` as a parameter. -/
def harlemLF {Agent W : Type u}
    (fBelS : ModalBase W) (gNorm : OrderingSource W)
    {B : Agent → W → Set W} (EP : EffectivePreferentialBackground Agent W B)
    (fHist : ModalBase W) (gInner : OrderingSource W)
    (Ad : Agent) (Harlem ATrain : Set W) (w : W) : Prop :=
  doubleModalLF fBelS gNorm
    (fun w' => wantEP EP Ad Harlem w')
    (fun w' => necessity fHist gInner (· ∈ ATrain) w')
    w

/-- The Harlem LF instantiates the eq. (77) double-modal schema by
construction. Documentation theorem (the equality is `rfl`). -/
theorem harlemLF_eq_doubleModalLF {Agent W : Type u}
    (fBelS : ModalBase W) (gNorm : OrderingSource W)
    {B : Agent → W → Set W} (EP : EffectivePreferentialBackground Agent W B)
    (fHist : ModalBase W) (gInner : OrderingSource W)
    (Ad : Agent) (Harlem ATrain : Set W) (w : W) :
    harlemLF fBelS gNorm EP fHist gInner Ad Harlem ATrain w =
      doubleModalLF fBelS gNorm
        (fun w' => wantEP EP Ad Harlem w')
        (fun w' => necessity fHist gInner (· ∈ ATrain) w')
        w :=
  rfl

/-! ### § 7.1.1 Hoboken scenario — the headline theorem

A minimal two-world model: `w₀` (actual, Ad effectively prefers
Hoboken) and `w₁` (hypothetical, Ad effectively prefers Harlem). The
two destination propositions are disjoint, and Ad knows this (`B = univ`
contains both worlds and `Harlem ∩ Hoboken = ∅`).

The headline (§ 7.1.1, p. 44): the Harlem sentence comes out **true**
at `w₀` despite Ad's actual preference for Hoboken — solving the
conflicting-goals problem § 2.3 raised against Sæbø's analysis. -/

namespace HobokenScenario

/-- Two-world model: `w₀` (Hoboken-world) and `w₁` (Harlem-world). -/
abbrev World : Type := Fin 2

/-- The actual world (Hoboken scenario). -/
abbrev wActual : World := 0

/-- The destination propositions. Disjoint by construction
(`Harlem ∩ Hoboken = ∅`) — Ad cannot go to both places in the same
time frame, per paper p. 7 / eq. (90). -/
def Harlem : Set World := {1}
def Hoboken : Set World := {0}

/-- Ad's belief state: full epistemic uncertainty (both worlds are
belief-possible). `B Ad w = Set.univ` for both Ad ∈ Unit and w ∈ World. -/
def belAd : Unit → World → Set World := fun _ _ => Set.univ

/-- The propositions are disjoint at the world level (eq. 90). -/
theorem harlem_inter_hoboken_eq_empty : Harlem ∩ Hoboken = ∅ := by
  ext w
  fin_cases w <;> simp [Harlem, Hoboken]

/-- Building block: a singleton preference structure whose unique
preference is `φ`. With an empty `prec` relation, `φ ∈ maxElts`
trivially. -/
private def singletonPS (φ : Set World) : PreferenceStructure World where
  prefs := {φ}
  prec := fun _ _ => False
  isStrictOrder := { irrefl := fun _ h => h, trans := fun _ _ _ h _ => h }

private theorem singletonPS_mem_maxElts (φ : Set World) :
    φ ∈ (singletonPS φ).maxElts :=
  ⟨⟨φ, rfl⟩, fun _ h => h, rfl⟩

/-- Consistency of a singleton preference structure: the unique
preference must be belief-compatible. Pure algebra; the consistency
hypothesis reduces to ruling out two cases on `X ⊆ {φ}`. -/
private theorem singletonPS_consistent_of_nonempty
    (φ : Set World) (B : Set World) (hNE : (φ ∩ B).Nonempty) :
    (singletonPS φ).consistent B := by
  intro X hXsub hEmpty
  exfalso
  rcases Set.subset_singleton_iff_eq.mp hXsub with hX | hX
  · -- X = ∅; ⋂ p ∈ ∅, p = univ; B ∩ univ = B; hEmpty forces B = ∅
    rw [hX] at hEmpty
    simp only [Set.mem_empty_iff_false, Set.iInter_of_empty, Set.iInter_univ,
               Set.inter_univ] at hEmpty
    exact hNE.ne_empty (by rw [hEmpty]; simp)
  · -- X = {φ}; B ∩ φ = ∅, contradicting hNE
    rw [hX, Set.biInter_singleton] at hEmpty
    exact hNE.ne_empty (by rw [Set.inter_comm]; exact hEmpty)

/-- Effective preference at `w₀`: Ad effectively prefers Hoboken. -/
noncomputable def epAtW0 : EffectivePreference World Set.univ :=
  EffectivePreference.ofConsistent (singletonPS Hoboken)
    (singletonPS_consistent_of_nonempty Hoboken Set.univ
      ⟨0, by simp [Hoboken]⟩)

/-- Effective preference at `w₁`: Ad effectively prefers Harlem. -/
noncomputable def epAtW1 : EffectivePreference World Set.univ :=
  EffectivePreference.ofConsistent (singletonPS Harlem)
    (singletonPS_consistent_of_nonempty Harlem Set.univ
      ⟨1, by simp [Harlem]⟩)

/-- The effective preferential background: at `w₀` Hoboken-preferring,
at `w₁` Harlem-preferring. Uses `if`-on-decidable equality to keep the
reduction simple at the use sites. -/
noncomputable def EP : EffectivePreferentialBackground Unit World belAd :=
  fun _ w => if w = (0 : World) then epAtW0 else epAtW1

/-- At `wActual = w₀`: Ad effectively prefers Hoboken. -/
theorem wantEP_hoboken_at_wActual : wantEP EP () Hoboken wActual := by
  show Hoboken ∈ (EP () wActual).toPreferenceStructure.maxElts
  simp only [EP, wActual]
  exact singletonPS_mem_maxElts Hoboken

/-- The crux: at `wActual`, Ad does NOT effectively prefer Harlem.
By `wantEP_jointly_belief_consistent`, if Ad effectively preferred both
Hoboken and Harlem, then `(Hoboken ∩ Harlem) ∩ B Ad wActual ≠ ∅`. But
Hoboken ∩ Harlem = ∅, contradiction. -/
theorem not_wantEP_harlem_at_wActual :
    ¬ wantEP EP () Harlem wActual := by
  intro hHarlem
  have hHoboken := wantEP_hoboken_at_wActual
  have h := wantEP_jointly_belief_consistent EP hHoboken hHarlem
  apply h
  rw [show Hoboken ∩ Harlem = ∅ by
    rw [Set.inter_comm]; exact harlem_inter_hoboken_eq_empty]
  simp

/-- Speaker's modal base: knows the actual world. `fBelS(w) = {w}` is
the simplest realization of "speaker's true beliefs" — the standard
omniscient case where vacuous truth wins. -/
def fBelS : ModalBase World := fun w => [(· = w)]

/-- Empty (stereotypical) ordering source — minimal choice; the
Hoboken theorem doesn't depend on its content. -/
def gNorm : OrderingSource World := emptyBackground

/-- Inner modal base (paper `f^t_hist`) — paper-local placeholder. -/
def fHist : ModalBase World := emptyBackground

/-- Inner ordering source (paper `g_epA`) — paper-local placeholder.
The Hoboken theorem's vacuous-truth doesn't constrain `gInner`; this is
just a typed stub. See module docstring TODO on the bridge. -/
def gInner : OrderingSource World := emptyBackground

/-- The A-train proposition (arbitrary; the Hoboken theorem doesn't
constrain it). -/
def ATrain : Set World := Set.univ

/-- **Paper § 7.1.1 headline theorem (eq. 88 evaluated at the Hoboken
scenario).** The Harlem sentence is *true* at `wActual` — solving the
conflicting-goals problem § 2.3 raised against Sæbø 2001.

Mechanism: the NEC's modal base is `fBelS = [(· = wActual)]`, so
`accessibleWorlds fBelS wActual = {wActual}`. Restricting by the
antecedent `wantEP EP Ad Harlem` removes `wActual` from the accessible
set (by `not_wantEP_harlem_at_wActual`, derived from the consistency of
EP and `Harlem ∩ Hoboken = ∅`), leaving the empty set. The NEC
quantifies over `bestWorlds` of that empty set, which is empty, so the
NEC is vacuously true.

The inner MUST is never evaluated — consistency of EP alone suffices.
This is the formal core of C&L's claim that anankastics need no
special compositional treatment. -/
theorem harlem_true_in_hoboken_scenario :
    harlemLF fBelS gNorm EP fHist gInner () Harlem ATrain wActual := by
  unfold harlemLF doubleModalLF conditionalNecessity
  rw [necessity_iff_all]
  intro w' hw'
  exfalso
  have hAcc : w' ∈ accessibleWorlds (restrictedBase fBelS
      (fun w'' => wantEP EP () Harlem w'')) wActual := hw'.1
  rw [restricted_accessible_eq] at hAcc
  obtain ⟨hAccBase, hAntec⟩ := hAcc
  have hEq : w' = wActual := by
    unfold accessibleWorlds Core.Logic.Intensional.Premise.propIntersection fBelS at hAccBase
    simpa using hAccBase
  rw [hEq] at hAntec
  exact not_wantEP_harlem_at_wActual hAntec

end HobokenScenario

-- BEGIN GENERATED EXAMPLES
-- (Generated from Linglib/Data/Examples/CondoravdiLauer2016.json by scripts/gen_examples.py.
-- Do not edit between markers; re-run the generator after editing the JSON.)

namespace Examples
open Data.Examples

def cl2016_2_intend : LinguisticExample :=
  { id := "cl2016_2_intend"
    source := ⟨"condoravdi-lauer-2016", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you intend to go to Harlem, you should / have to take the A train."
    discourseSegments := []
    glossedTokens := []
    translation := "If you intend to go to Harlem, you should / have to take the A train."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "harlemBase"), ("desirePredicate", "intend")]
    comment := "Intend-variant of (1); supports the paper's argument that the antecedent need not be want — any intention-related predicate works."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_3_plan : LinguisticExample :=
  { id := "cl2016_3_plan"
    source := ⟨"condoravdi-lauer-2016", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you are planning to go to Harlem, you should / have to take the A train."
    discourseSegments := []
    glossedTokens := []
    translation := "If you are planning to go to Harlem, you should / have to take the A train."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "harlemBase"), ("desirePredicate", "plan")]
    comment := "Plan-variant of (1)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_4_goal : LinguisticExample :=
  { id := "cl2016_4_goal"
    source := ⟨"condoravdi-lauer-2016", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If your goal is to go to Harlem, you should / have to take the A train."
    discourseSegments := []
    glossedTokens := []
    translation := "If your goal is to go to Harlem, you should / have to take the A train."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "harlemBase"), ("desirePredicate", "goal")]
    comment := "Goal-variant of (1). Together with (2)-(3), shows the antecedent desire-predicate is not lexically privileged."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_5_chocolate : LinguisticExample :=
  { id := "cl2016_5_chocolate"
    source := ⟨"condoravdi-lauer-2016", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to eat chocolate, you should try thinking about something else."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to eat chocolate, you should try thinking about something else."
    context := "Advice to avoid eating chocolate."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "nonAnankasticAntecedent"), ("reading", "mere-desire")]
    comment := "Non-anankastic if-want conditional. Same surface form as (1) but conveys NOT 'thinking-about-something-else is necessary for chocolate' — it's advice to avoid. Shows surface form does not determine anankasticity; want gets a mere-desire construal here (paper § 7.2.1, formalized as cl2016_5_chocolate in the chocolate-LF contrast)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_19_chess : LinguisticExample :=
  { id := "cl2016_19_chess"
    source := ⟨"condoravdi-lauer-2016", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(In view of what he wants,) John should resign the game. / (In view of what he wants,) John should not resign the game."
    discourseSegments := ["(In view of what he wants,) John should resign the game.", "(In view of what he wants,) John should not resign the game."]
    glossedTokens := []
    translation := "Both readings of 'in view of what he wants, John should/should not resign' are simultaneously felicitous."
    context := "John is far superior chess player, but Bill is good enough to draw out the game; John hates resigning to inferior players but it is 3am and he needs to sleep. The only way to end quickly is to resign; the only way to win is to keep playing."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "interactingPreferences"), ("modalForce", "unconditionalNec")]
    comment := "Interacting-preferences scenario: unconditional necessity statements (a)/(b) are jointly inconsistent, but the corresponding conditionals (20) can be jointly true. Shows preferences must be resolved differently in conditional vs unconditional cases."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_20_chess_conditional : LinguisticExample :=
  { id := "cl2016_20_chess_conditional"
    source := ⟨"condoravdi-lauer-2016", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John wants to go to bed, he should resign. / If John wants to win the game, he should not resign."
    discourseSegments := ["If John wants to go to bed, he should resign.", "If John wants to win the game, he should not resign."]
    glossedTokens := []
    translation := "Both conditionals true simultaneously."
    context := "Same chess scenario as (19)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "interactingPreferences"), ("modalForce", "conditionalNec")]
    comment := "Conditionalized version of (19); both conditionals can be true even though their unconditional counterparts cannot. Tests interacting-preferences resolution."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_28_invite : LinguisticExample :=
  { id := "cl2016_28_invite"
    source := ⟨"condoravdi-lauer-2016", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to invite everyone to the dinner, your table has to seat at least 20 people."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to invite everyone to the dinner, your table has to seat at least 20 people."
    context := "There are at least 20 people to be invited."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "nearAnankastic"), ("relationType", "precondition")]
    comment := "Near-anankastic: conveys precondition (seating 20+ is necessary FOR being able to seat everyone) rather than means-of. Used to argue the analysis must generalize beyond means-of."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_29a_vaccine_safe : LinguisticExample :=
  { id := "cl2016_29a_vaccine_safe"
    source := ⟨"condoravdi-lauer-2016", "(29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to travel to that place, you should / must get a vaccine to be safe."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to travel to that place, you should / must get a vaccine to be safe."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "nearAnankastic"), ("relationType", "strengthened-goal")]
    comment := "Near-anankastic with overt purpose clause 'to be safe'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_29b_vaccine : LinguisticExample :=
  { id := "cl2016_29b_vaccine"
    source := ⟨"condoravdi-lauer-2016", "(29b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to travel to that place, you should / must get a vaccine."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to travel to that place, you should / must get a vaccire."
    context := "Getting a vaccine is a precondition for safe travel, not for travel per se."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "nearAnankastic"), ("relationType", "implicit-strengthened-goal")]
    comment := "Near-anankastic without overt purpose clause; the strengthened goal (safe travel) must be supplied by context. Paper argues Huitink's strong-antecedent analysis predicts this false on its strongest reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_31_disneyworld : LinguisticExample :=
  { id := "cl2016_31_disneyworld"
    source := ⟨"condoravdi-lauer-2016", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to go to Disneyworld, you must / should spend at least five days there."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to go to Disneyworld, you must / should spend at least five days there."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "nearAnankastic"), ("relationType", "teleological-consequence")]
    comment := "Near-anankastic about teleological CONSEQUENCES: spending five days is a consequence of (optimally) going to Disneyworld, not a precondition. Raises the same compositionality problem as canonical anankastics."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_38_exemption : LinguisticExample :=
  { id := "cl2016_38_exemption"
    source := ⟨"condoravdi-lauer-2016", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to use the exemption now, you must / will have to pay more taxes next year."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to use the exemption now, you must / will have to pay more taxes next year."
    context := "Tax law: using the exemption now triggers higher liability later."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "nearAnankastic"), ("modalType", "deontic")]
    comment := "Near-anankastic with DEONTIC inner modal (rather than teleological). Conveys: actually taking the exemption forces higher taxes — not that wanting it does. The vacuity-of-want is contingent on the actualization assumption (paper § 7.2.2)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_39a_disaster : LinguisticExample :=
  { id := "cl2016_39a_disaster"
    source := ⟨"condoravdi-lauer-2016", "(39a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to go to the disaster area, you should go there quickly."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to go to the disaster area, you should go there quickly."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "nearAnankastic"), ("relationType", "what-kind-of")]
    comment := "'What-kind-of' near-anankastic: the prejacent ENTAILS the antecedent goal (going-quickly entails going). Tests against purpose-clause analyses that can't paraphrase such conditionals."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_40a_dress : LinguisticExample :=
  { id := "cl2016_40a_dress"
    source := ⟨"condoravdi-lauer-2016", "(40a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you want to buy a fancy dress, you should buy a well-made one."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to buy a fancy dress, you should buy a well-made one."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "nearAnankastic"), ("relationType", "what-kind-of")]
    comment := "'What-kind-of' near-anankastic."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_46_neg_letter_grade : LinguisticExample :=
  { id := "cl2016_46_neg_letter_grade"
    source := ⟨"condoravdi-lauer-2016", "(46) (Penka p.c.)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you don't want to get a letter grade for the course, you don't have to take the exam."
    discourseSegments := []
    glossedTokens := []
    translation := "If you don't want to get a letter grade for the course, you don't have to take the exam."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "nearAnankastic"), ("scope", "negation-over-want")]
    comment := "Negation in the antecedent: scopes over want (= 'absence of preference'), not over the complement. Tests that want interacts with embedding operators normally. Defeats 'vacuous want' analyses."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_52_picnic_hiking : LinguisticExample :=
  { id := "cl2016_52_picnic_hiking"
    source := ⟨"condoravdi-lauer-2016", "(52)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I want it to rain tomorrow so the picnic gets canceled, but I (also) want it to be sunny tomorrow so I can go hiking."
    discourseSegments := []
    glossedTokens := []
    translation := "I want it to rain tomorrow so the picnic gets canceled, but I (also) want it to be sunny tomorrow so I can go hiking."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "conjunctionIntroduction"), ("reading", "mere-desire")]
    comment := "Levinson-style example: two incompatible wants coherently asserted. Argues mere-desire reading of want (not effective-preference) does not validate Conjunction Introduction."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_55_chess_incompat : LinguisticExample :=
  { id := "cl2016_55_chess_incompat"
    source := ⟨"condoravdi-lauer-2016", "(55)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John intends to move in with his girlfriend, but he also intends to keep living alone."
    discourseSegments := []
    glossedTokens := []
    translation := "John intends to move in with his girlfriend, but he also intends to keep living alone."
    context := ""
    judgment := .questionable
    alternatives := [("John would like to move in with his girlfriend, but he would also like to keep living alone. He can't make up his mind.", .acceptable)]
    readings := []
    paperFeatures := [("puzzle", "conjunctionIntroduction"), ("reading", "effective-preference")]
    comment := "Intend-variant of (53). The intend-version sounds contradictory / attributes irrationality; the would-like-to variant (alternative) is coherent. Argues intend = effective preference is subject to a consistency constraint that mere desires lack."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_61_concorde : LinguisticExample :=
  { id := "cl2016_61_concorde"
    source := ⟨"asher-1987", "p. 225"⟩
    reportedIn := some ⟨"condoravdi-lauer-2016", "(62) / via Levinson 2003"⟩
    language := "stan1293"
    primaryText := "Nicholas wants to take a free trip on the Concorde. / Nicholas wants to take a trip on the Concorde."
    discourseSegments := ["Nicholas wants to take a free trip on the Concorde.", "Nicholas wants to take a trip on the Concorde."]
    glossedTokens := []
    translation := "First sentence true (free trip would be great), second false (paying would be financial ruin)."
    context := "Paying for a Concorde trip would mean financial ruin for Nicholas; a free trip would be very welcome."
    judgment := .acceptable
    alternatives := []
    readings := [("upward-entailment-fails", .acceptable)]
    paperFeatures := [("puzzle", "upwardEntailment"), ("reading", "effective-preference")]
    comment := "Tests Upward Entailment for want. Asher/Levinson claim (a) true but (b) false despite the entailment; C&L argue (b) can be true on a sub-property reading (Condoravdi et al. 2001, Zimmermann 2006 — quantification over sub-concepts)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_63_poodle_dog : LinguisticExample :=
  { id := "cl2016_63_poodle_dog"
    source := ⟨"condoravdi-lauer-2016", "(63)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wants to get a poodle, so he wants to get a dog."
    discourseSegments := []
    glossedTokens := []
    translation := "John wants to get a poodle, so he wants to get a dog."
    context := ""
    judgment := .acceptable
    alternatives := [("John wants to get a dog. So he would be happy to get a poodle.", .questionable)]
    readings := []
    paperFeatures := [("puzzle", "upwardEntailment")]
    comment := "Upward Entailment for want: poodle-getting entails dog-getting; the inference goes through. Pair with the alternative (which goes the wrong direction) to show want is UE not DE."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_82a_dog_tax : LinguisticExample :=
  { id := "cl2016_82a_dog_tax"
    source := ⟨"condoravdi-lauer-2016", "(82a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John gets a dog, he will have to pay more taxes."
    discourseSegments := []
    glossedTokens := []
    translation := "If John gets a dog, he will have to pay more taxes."
    context := "Dog owners pay a special tax; service dogs for the blind are exempt; John's eyesight is currently perfect and he has no dog."
    judgment := .acceptable
    alternatives := [("But if John loses his eyesight and gets a dog, he will not have to pay more taxes.", .acceptable)]
    readings := []
    paperFeatures := [("puzzle", "defeasibleObligation"), ("modalType", "deontic")]
    comment := "Defeasible obligation pair. Both true on the double-modal analysis (outer NEC restricts to typical worlds where John keeps his eyesight; inner MUST quantifies over best worlds in those). Argues for stereotypical outer ordering source on overt deontic modals."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_92_vladivostok : LinguisticExample :=
  { id := "cl2016_92_vladivostok"
    source := ⟨"vonstechow-krasikova-penka-2006", "p. 168"⟩
    reportedIn := some ⟨"condoravdi-lauer-2016", "(92)"⟩
    language := "stan1293"
    primaryText := "If you want to go to Vladivostok, you have to take the Chinese train."
    discourseSegments := []
    glossedTokens := []
    translation := "If you want to go to Vladivostok, you have to take the Chinese train."
    context := "Two trains go to Vladivostok, one Russian and one Chinese; the Chinese is much more comfortable. Addressee has a salient preference for comfort."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "compatibleSecondaryPreference")]
    comment := "Conditional anankastic with a COMPATIBLE secondary preference (comfort) that influences the prediction. Truth depends on whether comfort is taken to be an effective preference; vF&I 2005 report judgment variability — C&L attribute to contextual variability of effective-preference set, not grammatical variability."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_91a_virus_no : LinguisticExample :=
  { id := "cl2016_91a_virus_no"
    source := ⟨"condoravdi-lauer-2016", "(91a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I know John wants to go to Hoboken today, not to Harlem. #But if he wants to go to Harlem today, he has to take the A train."
    discourseSegments := ["I know John wants to go to Hoboken today, not to Harlem.", "But if he wants to go to Harlem today, he has to take the A train."]
    glossedTokens := []
    translation := "Continuation infelicitous when speaker known incompatible preference."
    context := ""
    judgment := .unacceptable
    alternatives := [("But if he wanted to go to Harlem today, he would have to take the A train.", .acceptable)]
    readings := []
    paperFeatures := [("puzzle", "informationalAsymmetry"), ("mood", "indicative-vs-subjunctive")]
    comment := "Indicative anankastic infelicitous when speaker knows the hypothetical EP is incompatible with actual; subjunctive variant is fine. The paper's evidence that the indicative imposes 'antecedent is epistemically possible' — same constraint as ordinary indicative conditionals."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cl2016_112a_inclined_harlem : LinguisticExample :=
  { id := "cl2016_112a_inclined_harlem"
    source := ⟨"vonfintel-iatridou-2005", "(via Weatherson)"⟩
    reportedIn := some ⟨"condoravdi-lauer-2016", "(112c)"⟩
    language := "stan1293"
    primaryText := "If you're inclined to go to Harlem, you have to take the A train."
    discourseSegments := []
    glossedTokens := []
    translation := "If you're inclined to go to Harlem, you have to take the A train."
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "weakAntecedent")]
    comment := "Weak antecedent (inclined, would-like-to, etc.). Generally not ananakastic — predicates that can only express mere desires can't target effective preferences. Becomes anankastic only in contexts where the mere desire would be acted on. Originally due to Weatherson (p.c.) via vF&I 2006 slides; here cited from the vF&I 2005 ms-companion."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [cl2016_2_intend, cl2016_3_plan, cl2016_4_goal, cl2016_5_chocolate, cl2016_19_chess, cl2016_20_chess_conditional, cl2016_28_invite, cl2016_29a_vaccine_safe, cl2016_29b_vaccine, cl2016_31_disneyworld, cl2016_38_exemption, cl2016_39a_disaster, cl2016_40a_dress, cl2016_46_neg_letter_grade, cl2016_52_picnic_hiking, cl2016_55_chess_incompat, cl2016_61_concorde, cl2016_63_poodle_dog, cl2016_82a_dog_tax, cl2016_92_vladivostok, cl2016_91a_virus_no, cl2016_112a_inclined_harlem]

end Examples
-- END GENERATED EXAMPLES

end Phenomena.Conditionals.Studies.CondoravdiLauer2016
