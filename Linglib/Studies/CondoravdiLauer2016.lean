import Linglib.Semantics.Attitudes.Desire
import Linglib.Semantics.Conditionals.Restrictor
import Linglib.Data.Examples.Schema
import Mathlib.Tactic.FinCases
import Linglib.Data.Examples.CondoravdiLauer2016

/-!
# [condoravdi-lauer-2016] — Anankastic conditionals are just conditionals

C&L's central claim: anankastics (eq. 1, the Harlem sentence) need no
special compositional treatment, provided (i) `want` is given the
effective-preference reading from § 5 (substrate at
`Semantics/Attitudes/Desire.lean`, `WantExactMatch`) and (ii) the
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

Out: § 3 review (see `Studies/vonFintelIatridou2005.lean`);
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
`Semantics/Attitudes/Preference.lean` (`maxInducedLe`).

## Cross-references

* `Semantics/Attitudes/Desire.lean` — `WantExactMatch`;
  `Semantics/Attitudes/Preference.lean` —
  `maxElts_pair_belief_compatible` (the load-bearing lemma).
* `Studies/vonFintelIatridou2005.lean` — vF&I's
  primary-secondary ordering source analysis that C&L 2016 critiques
  (paper § 3.2.2).
* `Studies/PhillipsBrown2025.lean` § 11 — sibling
  no-go theorem `condoravdiLauer_blocks_simultaneous_pq_and_negpq`,
  same consistency-delegation pattern.
-/

namespace CondoravdiLauer2016

open Desire
open Modality.Kratzer
open Semantics.Conditionals.Restrictor

universe u

/-! ### § 6.1 Double-modal compositional schema (eq. 77) -/

/-- [condoravdi-lauer-2016] eq. (77): `If ψ, MODAL[φ]` parses as
`NEC[ψ][MODAL[φ]]` when the consequent contains an overt modal claim.
Composed from `conditionalNecessity` (the outer NEC restriction by
antecedent, from `Semantics/Conditionals/Restrictor.lean`) and
an arbitrary world-indexed inner-modal proposition.

This is the schema instantiated by `harlemLF`. Kept inline rather than
promoted to `Semantics/Conditionals/DoubleModal.lean` because
no second paper-anchored study currently consumes it (≥ 2-consumer
graduation rule). Kaufmann & Schwager 2009 on conditional imperatives
would be the natural second consumer. -/
def doubleModalLF {W : Type u} (fOuter : ModalBase W) (gOuter : OrderingSource W)
    (ψ : W → Prop) (innerModal : W → Prop) (w : W) : Prop :=
  conditionalNecessity fOuter gOuter ψ innerModal w

/-! ### § 7.1 The Harlem LF (eq. 87b / 88) -/

/-- [condoravdi-lauer-2016] eq. (88) at the operator level: the
Harlem-sentence LF parameterised over its four contextual backgrounds.
`NEC_{fBelS, gNorm}[WantExactMatch(Ad, Harlem)] [MUST_{fHist, gInner}[ATrain]]`.

The four contextual parameters:
* `fBelS` — modal base of NEC, "speaker's true beliefs" (paper p. 41).
* `gNorm` — ordering source of NEC, "stereotypical" (paper § 6.1).
* `fHist` — modal base of MUST, "historical alternatives at time t"
  (paper p. 42; the historical-alternatives substrate lives in
  `Semantics/Modality/HistoricalAlternatives.lean`, but the v1 LF here
  takes an arbitrary modal base because the Hoboken theorem doesn't
  constrain it).
* `gInner` — ordering source of MUST. Paper eq. (88) uses `g_epA`
  (= `fun w => (P Ad w).maxElts`), but the bridge from `Set (Set W)` to
  the `List`-valued `OrderingSource` is deferred (see TODO in the
  module docstring); v1 takes `gInner` as a parameter. -/
def harlemLF {Agent W : Type u}
    (fBelS : ModalBase W) (gNorm : OrderingSource W)
    (P : Agent → W → PreferenceStructure W)
    (fHist : ModalBase W) (gInner : OrderingSource W)
    (Ad : Agent) (Harlem ATrain : Set W) (w : W) : Prop :=
  doubleModalLF fBelS gNorm
    (fun w' => WantExactMatch P Ad Harlem w')
    (fun w' => necessity fHist gInner (· ∈ ATrain) w')
    w

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
  ⟨rfl, fun _ _ h => h⟩

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

/-- The preferential background: Hoboken-preferring at `w₀`,
Harlem-preferring at `w₁`. Uses `if`-on-decidable equality to keep the
reduction simple at the use sites. -/
def prefBg : Unit → World → PreferenceStructure World :=
  fun _ w => if w = (0 : World) then singletonPS Hoboken else singletonPS Harlem

/-- `prefBg` is Ad's *effective* preference function (C&L (68)):
pointwise consistent with the belief state. -/
theorem prefBg_consistent (u : Unit) (w : World) :
    (prefBg u w).consistent (belAd u w) := by
  unfold prefBg belAd
  split
  · exact singletonPS_consistent_of_nonempty Hoboken Set.univ ⟨0, by simp [Hoboken]⟩
  · exact singletonPS_consistent_of_nonempty Harlem Set.univ ⟨1, by simp [Harlem]⟩

/-- At `wActual = w₀`: Ad effectively prefers Hoboken. -/
theorem hoboken_wanted_at_wActual :
    WantExactMatch prefBg () Hoboken wActual := by
  show Hoboken ∈ (prefBg () wActual).maxElts
  simp only [prefBg, wActual, if_pos]
  exact singletonPS_mem_maxElts Hoboken

/-- The crux: at `wActual`, Ad does NOT effectively prefer Harlem. Two
maximal preferences of a consistent structure must meet inside the
belief state (`maxElts_pair_belief_compatible`), but
Hoboken ∩ Harlem = ∅. -/
theorem harlem_not_wanted_at_wActual :
    ¬ WantExactMatch prefBg () Harlem wActual := by
  intro hHarlem
  have h := (prefBg () wActual).maxElts_pair_belief_compatible
    (prefBg_consistent () wActual) hoboken_wanted_at_wActual hHarlem
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
antecedent `WantExactMatch prefBg Ad Harlem` removes `wActual` from the
accessible set (by `harlem_not_wanted_at_wActual`, derived from the
consistency of the background and `Harlem ∩ Hoboken = ∅`), leaving the
empty set. The NEC quantifies over `bestWorlds` of that empty set,
which is empty, so the NEC is vacuously true.

The inner MUST is never evaluated — consistency alone suffices. This is
the formal core of C&L's claim that anankastics need no special
compositional treatment. -/
theorem harlem_true_in_hoboken_scenario :
    harlemLF fBelS gNorm prefBg fHist gInner () Harlem ATrain wActual := by
  unfold harlemLF doubleModalLF conditionalNecessity
  rw [necessity_iff_all]
  intro w' hw'
  exfalso
  have hAcc : w' ∈ accessibleWorlds (restrictedBase fBelS
      (fun w'' => WantExactMatch prefBg () Harlem w'')) wActual := hw'.1
  rw [restricted_accessible_eq] at hAcc
  obtain ⟨hAccBase, hAntec⟩ := hAcc
  have hEq : w' = wActual := by
    unfold accessibleWorlds Intensional.Premise.propIntersection fBelS at hAccBase
    simpa using hAccBase
  rw [hEq] at hAntec
  exact harlem_not_wanted_at_wActual hAntec

end HobokenScenario

end CondoravdiLauer2016
