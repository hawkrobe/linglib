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

/-! ### *only* is Strawson-DE but not DE (§2) -/

/-- The §2 operator: *only John*, with the focus individual modeled as
the world-predicate `· = World.w0`. -/
def onlyJohn : Set World → Set World := onlyFull (· = World.w0)

/-- *Only John*'s existence presupposition: some `John`-world satisfies
the scope. -/
def onlyJohnDefined (scope : Set World) (_w : World) : Prop :=
  ∃ w', w' = World.w0 ∧ scope w'

/-- Ex. 11 (p. 101): *only* is not classically downward entailing —
narrowing the scope is not truth-preserving because the conclusion's
existence presupposition is not guaranteed by the premise. With
`ex18_only_strawsonDE`, the paper's headline separation
(`Examples.ex10` is the licensing datum). -/
theorem ex11_only_not_DE : ¬ IsDownwardEntailing onlyJohn :=
  onlyFull_not_de

/-- Ex. 18 (p. 104): *only* is Strawson-DE relative to its existence
presupposition. -/
theorem ex18_only_strawsonDE : IsStrawsonDE onlyJohn onlyJohnDefined :=
  onlyFull_isStrawsonDE _

/-! ### *since* (§2.2) -/

/-- Ex. 22 (p. 107): *since* is Strawson-DE in its complement, relative
to the temporal presupposition that a past `p`-event existed —
Iatridou's exs. 20-21 (`Examples.ex21`) show licensing without
classical DE. -/
theorem ex22_since_strawsonDE (pastEvent sinceWindow : World → Set World) :
    IsStrawsonDE (sinceFull pastEvent sinceWindow)
      (fun p w => ∃ w' ∈ pastEvent w, p w') :=
  sinceFull_isStrawsonDE pastEvent sinceWindow

/-! ### Pseudo-anti-additivity (§2.3)

[atlas-1996]'s pseudo-anti-additivity for *only John* (ex. 25) is
"useless for the analysis of NPI licensing" (p. 110): licensers and
non-licensers share it alike (exs. 26-27). Strawson-DE, not pseudo-AA,
is the operative notion; the negative argument is a survey of
counterexamples, not a theorem. -/

/-! ### Adversative attitudes (§3)

Factivity blocks classical DE in the complement of *sorry/regret/
surprised* (exs. 29-30); Strawson-DE restores the inference by adding
factivity at the evaluation world. [kadmon-landman-1993]'s coherence
challenge (ex. 31) is reanalyzed in §3.1 as a modal-base shift; the
results below hold on a constant perspective. -/

section Adversatives

variable (dox bestOf : World → Set World)

/-- The concrete `sorryFull` frame of the substrate's DE counterexample:
identity doxastic state, preference fixed on `w1`. -/
def sorryFrame : Set World → Set World :=
  sorryFull (fun w => ({w} : Set World)) (fun _ => ({World.w1} : Set World))

/-- Ex. 30 (p. 111): *sorry* is not classically DE in its complement —
factivity of the narrower complement may fail at the evaluation world
even when the wider one's holds. -/
theorem ex30_sorry_not_DE : ¬ IsDownwardEntailing sorryFrame :=
  sorryFull_not_de

/-- Ex. 28b (p. 111): *sorry* is Strawson-DE relative to doxastic
factivity (`dox w ⊆ p`) — the explanatory result behind
`Examples.ex28b`, and the §3 counterpart of the §2 separation. -/
theorem ex28b_sorry_strawsonDE :
    IsStrawsonDE (sorryFull dox bestOf) (fun p w => ∀ w' ∈ dox w, p w') :=
  sorryFull_isStrawsonDE dox bestOf

/-! ### *want* and *glad* are upward entailing (§§3.2-3.3) -/

/-- vF §3.2 headline (eq. 45): *want* is upward entailing in its
complement under a doxastic modal base; the Asher/Heim apparent
non-monotonicity is a modal-base shift, parallel to §3.4. -/
theorem ex45_want_isUE : Monotone (wantFull bestOf) :=
  wantFull_isUE bestOf

/-- Ex. 50 / K&L (p. 122): *glad* under the K&L semantics is upward
entailing, so NPIs are not licensed in its complement
(`Examples.glad_any`) — the monotonicity asymmetry with *sorry* tracks
the licensing asymmetry, and recurs in Hindi ([lahiri-1998] §4.5:
*aaScarya* 'surprised' licenses, *khuS* 'glad' does not). -/
theorem ex50_gladKL_isUE : Monotone (gladFull dox bestOf) :=
  gladFull_isUE dox bestOf

/-- Ex. 52 (p. 124), vF's preferred replacement: *glad* is upward
entailing on the vF semantics too — same NPI prediction, different
content. -/
theorem ex52_gladVF_isUE (dox relevant : World → Set World)
    (lt : World → World → World → Prop) :
    Monotone (gladFullVF dox relevant lt) :=
  gladFullVF_isUE dox relevant lt

end Adversatives

/-! ### Shifting contexts (§3.4)

The coherent *glad…but sorry* sequences (exs. 60-61) rest on a shift of
the modal-base parameter between conjuncts; monotone validity is
checked against a constant context, and a formal treatment needs
dynamic-context machinery not in the substrate. Footnote 8's Weakened
DE ([asher-1987]) is the substrate's `IsWDE`; focus-*only* over a
non-name (exs. 66-68) is subsumed by `onlyFull`'s option-(a)
assertion clause. -/

/-! ### Conditional antecedents (§4.1) -/

/-- Ex. 72 (p. 137), restrictor analysis ([kratzer-1986]) with idle
ordering source: `condNecessity` is classically DE in its antecedent —
domain restriction is antitone. The Stalnaker-Lewis analysis
([stalnaker-1968], [lewis-1973]; ex. 73) makes the position non-DE;
vF §4.3 reduces its failures to context shifts via [von-fintel-2000],
an operator not in the substrate. -/
theorem ex72_conditional_antecedent_DE
    (domain : World → Set World) (β : Set World) :
    IsDownwardEntailing (fun α => condNecessity domain α β) :=
  conditional_antecedent_antitone domain β

/-- Restrictor-style conditional antecedents are a fortiori Strawson-DE
(`de_implies_strawsonDE`). -/
theorem conditional_antecedent_strawsonDE_under_restrictor
    (domain : World → Set World) (β : Set World)
    (defined : Set World → World → Prop) :
    IsStrawsonDE (fun α => condNecessity domain α β) defined :=
  conditional_antecedent_strawsonDE domain β defined

/-! ### Superlatives (§4.2) -/

/-- Ex. 77 (p. 139): the superlative is Strawson-DE in its restriction,
relative to the presupposition that the subject satisfies the
restriction — adding a restriction can reorder the comparison class
(ex. 76), so the position is not classically DE. Predicative use only
(`Examples.ex75`); the definite-description use (ex. 80) lacks local
Strawson-DE. -/
theorem ex77_superlative_strawsonDE (α : World) :
    IsStrawsonDE (superlativeAssert α) (superlativePresup α) :=
  superlative_isStrawsonDE α

/-! ### Cross-framework bridges

The four recalcitrants land at exactly Strawson-DE
(`ex18_only_strawsonDE`, `ex28b_sorry_strawsonDE`,
`conditional_antecedent_strawsonDE_under_restrictor`,
`ex77_superlative_strawsonDE`; hierarchy AM → AA → DE → Strawson-DE via
`de_implies_strawsonDE`), while *glad* sits outside the hierarchy (UE).
K&L and vF derive the *sorry*/*glad* asymmetry from the same substrate
theorems under different prose; the `example`s below check the
statement identity by discharging this file's statements with K&L's
proof terms. -/

example (dox bestOf : World → Set World) :
    IsStrawsonDE (sorryFull dox bestOf) (fun p w => ∀ w' ∈ dox w, p w') :=
  KadmonLandman1993.sorry_licenses_any dox bestOf

example (dox bestOf : World → Set World) :
    Monotone (gladFull dox bestOf) :=
  KadmonLandman1993.glad_does_not_license dox bestOf

/-- `gladFull_isUE` undergenerates against the settle-for-less data:
Hindi *khuS* 'glad' + NPI is grammatical on a "settle for less" reading
([lahiri-1998] §4.5), as is the English analogue
([kadmon-landman-1993]) — the rescued reading needs a
perspective-shifted `bestOf` or a Strawson-DE treatment the substrate
lacks. -/
theorem bridge_lahiri_glad_settle_overgeneration :
    Lahiri1998.npi_glad_settle.grammatical = true ∧
    KadmonLandman1993.settleGladAnybody.grammatical = true ∧
    KadmonLandman1993.settleGladTickets.grammatical = true :=
  ⟨rfl, rfl, rfl⟩

/-- [hoeksema-1983]'s S-comparative is anti-additive
(`Degree.gtOverSet_isAntiAdditive`), hence Strawson-DE — in vF's
recalcitrant class with classical AA to spare, so it licenses strong
NPIs where *only* licenses only weak ones. -/
theorem bridge_hoeksema_gtOverSet_strawsonDE
    {Entity D : Type*} [Preorder D] (μ : Entity → D)
    (defined : Set D → Entity → Prop) :
    IsStrawsonDE (Core.Order.Comparison.gt.overSet μ) defined :=
  antitone_implies_strawsonDE _
    (Degree.gtOverSet_isAntiAdditive μ).antitone defined

/-! ### Individual-identity *only* and Rooth's strong theory

(15) (p. 104) excludes by individual identity — "¬∃y ≠ x: P(y) = True"
— while [rooth-1992]'s `onlyVia` excludes by proposition identity over
a resolved alternative set; they coincide over the individual-generated
family exactly when it is injective. World-constant propositions (the
extensional `onlyFull`) fail injectivity wholesale, which is why the
bridge is stated intensionally. -/

section OnlyViaBridge

open Semantics.Focus (onlyVia mem_onlyVia)

variable {W ι : Type*}

/-- (15)'s assertion, intensionalized: no individual distinct from the
focus `x` has a true P-proposition. -/
def onlyIndiv (P : ι → Set W) (x : ι) : Set W :=
  {w | ∀ y, y ≠ x → w ∉ P y}

/-- **(15) = strong-theory *only*** over an injective
individual-generated alternative family: individual-identity exclusion
coincides with `onlyVia`'s proposition-identity exclusion over
`Set.range P`. -/
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

/-- Injectivity is essential: when two distinct individuals share one
true proposition, (15) still excludes but `onlyVia` cannot see the
distinction. -/
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
