import Linglib.Semantics.Entailment.StrawsonEntailment
import Linglib.Semantics.Focus.Control
import Linglib.Data.Examples.VonFintel1999
import Linglib.Studies.KadmonLandman1993
import Linglib.Studies.Lahiri1998
import Linglib.Studies.Hoeksema1983

/-!
# Strawson entailment and NPI licensing (von Fintel 1999)

This file indexes [von-fintel-1999]'s defense of the Fauconnier-Ladusaw
analysis of NPI licensing: four contexts that license NPIs without being
classically downward entailing — *only*, adversative attitudes,
superlatives, and conditional antecedents — are all Strawson-DE (his
Definition 14). Each theorem is named after the paper's example number
and discharged by specializing the corresponding substrate theorem from
`Semantics/Entailment/StrawsonEntailment.lean`. The NPI stimuli are typed
rows in `Data/Examples/VonFintel1999.json` (`Examples.ex10`, …).

## Main results

* `ex11_only_not_DE`, `ex18_only_strawsonDE` — the §2 separation: *only*
  is Strawson-DE but not classically DE.
* `ex22_since_strawsonDE` — §2.2: *since* (Iatridou's exs. 20-22).
* `ex30_sorry_not_DE`, `ex28b_sorry_strawsonDE` — the §3 adversative
  separation.
* `ex45_want_isUE`, `ex50_gladKL_isUE`, `ex52_gladVF_isUE` — §§3.2-3.3:
  *want* and *glad* are upward entailing, so NPIs are not licensed.
* `ex72_conditional_antecedent_DE`,
  `conditional_antecedent_strawsonDE_under_restrictor` — §4.1, the
  restrictor analysis.
* `ex77_superlative_strawsonDE` — §4.2 superlatives.
* `onlyIndiv_eq_onlyVia` — (15)'s individual-identity exclusion equals
  [rooth-1992]'s `onlyVia` over injective individual-generated families.
* `bridge_lahiri_glad_settle_overgeneration`,
  `bridge_hoeksema_gtOverSet_strawsonDE` — cross-framework bridges.

Discussed without formalization: §2.3 pseudo-anti-additivity
(exs. 23-27), ex. 31, and the §3.4 shifting-context material
(exs. 60-68).

## References

* [von-fintel-1999], [kadmon-landman-1993], [lahiri-1998],
  [hoeksema-1983], [rooth-1992], [atlas-1996].
-/

namespace VonFintel1999

open Entailment

/-! ### *only* is Strawson-DE but not DE (§2)

The licensing datum is `Examples.ex10`; the separation fails classically
because the conclusion's existence presupposition is not guaranteed by
the premise. -/

/-- *Only John*, with the focus individual modeled as `· = World.w0`. -/
def onlyJohn : Set World → Set World := onlyFull (· = World.w0)

/-- *Only John*'s existence presupposition. -/
def onlyJohnDefined (scope : Set World) (_w : World) : Prop :=
  ∃ w', w' = World.w0 ∧ scope w'

/-- Ex. 11 (p. 101): *only* is not classically downward entailing. -/
theorem ex11_only_not_DE : ¬ IsDownwardEntailing onlyJohn :=
  onlyFull_not_de

/-- Ex. 18 (p. 104): *only* is Strawson-DE relative to its existence presupposition. -/
theorem ex18_only_strawsonDE : IsStrawsonDE onlyJohn onlyJohnDefined :=
  onlyFull_isStrawsonDE _

/-! ### *since* (§2.2)

Iatridou's examples; the licensing datum is `Examples.ex21`. -/

/-- Ex. 22 (p. 107): *since* is Strawson-DE in its complement, relative
to the past-event presupposition. -/
theorem ex22_since_strawsonDE (pastEvent sinceWindow : World → Set World) :
    IsStrawsonDE (sinceFull pastEvent sinceWindow)
      (fun p w => ∃ w' ∈ pastEvent w, p w') :=
  sinceFull_isStrawsonDE pastEvent sinceWindow

/-! ### Pseudo-anti-additivity (§2.3)

[atlas-1996]'s pseudo-anti-additivity is "useless for the analysis of
NPI licensing" (p. 110): licensers and non-licensers share it alike
(exs. 25-27). -/

/-! ### Adversative attitudes (§3)

Factivity blocks classical DE in the complement (exs. 29-30);
Strawson-DE restores the inference. The licensing data are
`Examples.ex28a` and `Examples.ex28b`; [kadmon-landman-1993]'s
coherence challenge (ex. 31) is reanalyzed in §3.1 as a modal-base
shift. -/

section Adversatives

variable (dox bestOf : World → Set World)

/-- The substrate's DE-counterexample frame for `sorryFull`. -/
def sorryFrame : Set World → Set World :=
  sorryFull (fun w => ({w} : Set World)) (fun _ => ({World.w1} : Set World))

/-- Ex. 30 (p. 111): *sorry* is not classically DE in its complement. -/
theorem ex30_sorry_not_DE : ¬ IsDownwardEntailing sorryFrame :=
  sorryFull_not_de

/-- Ex. 28b (p. 111): *sorry* is Strawson-DE relative to doxastic factivity. -/
theorem ex28b_sorry_strawsonDE :
    IsStrawsonDE (sorryFull dox bestOf) (fun p w => ∀ w' ∈ dox w, p w') :=
  sorryFull_isStrawsonDE dox bestOf

/-! ### *want* and *glad* are upward entailing (§§3.2-3.3)

The Asher/Heim apparent non-monotonicity of *want* is a modal-base
shift; the *sorry*/*glad* monotonicity asymmetry tracks the
NPI-licensing asymmetry (`Examples.glad_any`), in English and in Hindi
([lahiri-1998] §4.5). -/

/-- Eq. 45 (§3.2): *want* is upward entailing in its complement. -/
theorem ex45_want_isUE : Monotone (wantFull bestOf) :=
  wantFull_isUE bestOf

/-- Ex. 50 (p. 122): *glad* on the K&L semantics is upward entailing. -/
theorem ex50_gladKL_isUE : Monotone (gladFull dox bestOf) :=
  gladFull_isUE dox bestOf

/-- Ex. 52 (p. 124): *glad* on vF's replacement semantics is likewise upward entailing. -/
theorem ex52_gladVF_isUE (dox relevant : World → Set World)
    (lt : World → World → World → Prop) :
    Monotone (gladFullVF dox relevant lt) :=
  gladFullVF_isUE dox relevant lt

end Adversatives

/-! ### Shifting contexts (§3.4)

The coherent *glad…but sorry* sequences (exs. 60-61) rest on modal-base
shifts and need dynamic-context machinery not in the substrate;
footnote 8's Weakened DE is the substrate's `IsWDE`; focus-*only* over
a non-name (exs. 66-68) is subsumed by `onlyFull`. -/

/-! ### Conditional antecedents (§4.1)

The restrictor analysis ([kratzer-1986]) makes the antecedent position
classically DE; on Stalnaker-Lewis ([stalnaker-1968], [lewis-1973]) it
is not, and vF §4.3 reduces those failures to context shifts via
[von-fintel-2000], an operator not in the substrate. The licensing
datum is `Examples.ex70a`. -/

/-- Ex. 72 (p. 137): with an idle ordering source, `condNecessity` is
classically DE in its antecedent. -/
theorem ex72_conditional_antecedent_DE
    (domain : World → Set World) (β : Set World) :
    IsDownwardEntailing (fun α => condNecessity domain α β) :=
  conditional_antecedent_antitone domain β

/-- Restrictor-style conditional antecedents are a fortiori Strawson-DE. -/
theorem conditional_antecedent_strawsonDE_under_restrictor
    (domain : World → Set World) (β : Set World)
    (defined : Set World → World → Prop) :
    IsStrawsonDE (fun α => condNecessity domain α β) defined :=
  conditional_antecedent_strawsonDE domain β defined

/-! ### Superlatives (§4.2)

Adding a restriction can reorder the comparison class (ex. 76), so the
position is not classically DE; predicative use only (`Examples.ex75`),
the definite-description use (ex. 80) lacking local Strawson-DE. -/

/-- Ex. 77 (p. 139): the superlative is Strawson-DE in its restriction position. -/
theorem ex77_superlative_strawsonDE (α : World) :
    IsStrawsonDE (superlativeAssert α) (superlativePresup α) :=
  superlative_isStrawsonDE α

/-! ### Cross-framework bridges

The four recalcitrants land at exactly Strawson-DE while *glad* sits
outside the hierarchy (UE). K&L and vF derive the *sorry*/*glad*
asymmetry from the same substrate theorems under different prose; the
`example`s check the statement identity by discharging this file's
statements with K&L's proof terms. -/

example (dox bestOf : World → Set World) :
    IsStrawsonDE (sorryFull dox bestOf) (fun p w => ∀ w' ∈ dox w, p w') :=
  KadmonLandman1993.sorry_licenses_any dox bestOf

example (dox bestOf : World → Set World) :
    Monotone (gladFull dox bestOf) :=
  KadmonLandman1993.glad_does_not_license dox bestOf

/-- The settle-for-less data ([lahiri-1998] §4.5,
[kadmon-landman-1993]): *glad* + NPI is grammatical on a rescued
reading that `gladFull_isUE` cannot capture. -/
theorem bridge_lahiri_glad_settle_overgeneration :
    Lahiri1998.npi_glad_settle.grammatical = true ∧
    KadmonLandman1993.settleGladAnybody.grammatical = true ∧
    KadmonLandman1993.settleGladTickets.grammatical = true :=
  ⟨rfl, rfl, rfl⟩

/-- [hoeksema-1983]'s S-comparative is anti-additive, hence Strawson-DE
with classical AA to spare (it licenses strong NPIs). -/
theorem bridge_hoeksema_gtOverSet_strawsonDE
    {Entity D : Type*} [Preorder D] (μ : Entity → D)
    (defined : Set D → Entity → Prop) :
    IsStrawsonDE (Core.Order.Comparison.gt.overSet μ) defined :=
  antitone_implies_strawsonDE _
    (Degree.gtOverSet_isAntiAdditive μ).antitone defined

/-! ### Individual-identity *only* and Rooth's strong theory

(15) (p. 104) excludes by individual identity, `onlyVia` by proposition
identity; they coincide over an injective individual-generated family.
World-constant propositions (the extensional `onlyFull`) fail
injectivity wholesale, so the bridge is stated intensionally. -/

section OnlyViaBridge

open Focus (onlyVia mem_onlyVia)

variable {W ι : Type*}

/-- (15)'s assertion, intensionalized: no individual other than `x` satisfies P. -/
def onlyIndiv (P : ι → Set W) (x : ι) : Set W :=
  {w | ∀ y, y ≠ x → w ∉ P y}

/-- (15) coincides with `onlyVia` over an injective individual-generated alternative family. -/
theorem onlyIndiv_eq_onlyVia (P : ι → Set W) (x : ι)
    (hP : Function.Injective P) :
    onlyIndiv P x = onlyVia (Set.range P) (P x) := by
  ext w
  simp only [onlyIndiv, Set.mem_setOf_eq, mem_onlyVia]
  constructor
  · rintro h q ⟨y, rfl⟩ hw
    by_cases hyx : y = x
    · exact hyx ▸ rfl
    · exact absurd hw (h y hyx)
  · intro h y hyx hw
    exact hyx (hP (h (P y) ⟨y, rfl⟩ hw))

/-- `onlyVia` cannot distinguish cotrue alternatives that (15) separates. -/
theorem onlyIndiv_ne_onlyVia_of_collapse :
    onlyIndiv (fun _ : Bool => (Set.univ : Set Bool)) true ≠
      onlyVia (Set.range fun _ : Bool => (Set.univ : Set Bool)) Set.univ := by
  intro h
  have h0 : true ∈ onlyIndiv (fun _ : Bool => (Set.univ : Set Bool)) true := by
    rw [h]
    exact fun q hq _ => by obtain ⟨y, rfl⟩ := hq; rfl
  exact h0 false (by decide) (Set.mem_univ true)

end OnlyViaBridge

end VonFintel1999
