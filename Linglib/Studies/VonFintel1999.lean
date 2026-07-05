import Linglib.Semantics.Entailment.StrawsonEntailment
import Linglib.Semantics.Focus.Control
import Linglib.Data.Examples.VonFintel1999
import Linglib.Studies.KadmonLandman1993
import Linglib.Studies.Lahiri1998
import Linglib.Studies.Hoeksema1983

/-!
# [von-fintel-1999] — Strawson entailment as a rescue for Fauconnier-Ladusaw

von Fintel, K. (1999). NPI Licensing, Strawson Entailment, and Context
Dependency. Journal of Semantics 16(2), 97–148.

The paper defends the Fauconnier-Ladusaw analysis of NPI licensing — NPIs
are licensed in DE positions — against four arenas where NPIs are licensed
although the host context is not classically DE: *only*, the adversative
attitude predicates, superlatives, and conditional antecedents. The key
move weakens classical DE to **Strawson-DE** (his Definition 14): the
inference `f(q) ⊨ f(p)` need only hold assuming the conclusion's
presupposition. All four contexts come out Strawson-DE.

The Strawson-DE substrate lives in
`Semantics/Entailment/StrawsonEntailment.lean`; this file is the
paper-citation index — each theorem is named after the paper's example
number(s) and discharged by specializing the corresponding substrate
theorem. The NPI stimuli themselves are typed rows in
`Data/Examples/VonFintel1999.json` (`Examples.ex10`, …); the inference
schemata quoted in section docstrings are what the theorems formalize.

## Coverage

- §2 *only*: exs. 10, 11, 18 — formalized; (15)'s individual-identity
  exclusion reconciled with [rooth-1992]'s `onlyVia` over injective
  individual-generated families (`onlyIndiv_eq_onlyVia`).
- §2.2 *since* (Iatridou): exs. 20-22 — formalized via `sinceFull`.
- §2.3 pseudo-anti-additivity (against Atlas): exs. 23-27 — discussed.
- §3 *sorry/surprised/regret*: exs. 28-30 — formalized via `sorryFull`;
  ex. 31 (Kadmon-Landman's coherence challenge) discussed.
- §3.2 *want* (Asher/Heim): eq. 45 — formalized via `wantFull`.
- §3.3 *glad* asymmetry: exs. 50, 52 — formalized.
- §3.4 shifting contexts (exs. 60-65) and focus-*only* (exs. 66-68) —
  discussed.
- §4.1 conditional antecedents: exs. 70-73 — restrictor side formalized.
- §4.2 superlatives: exs. 75-77 — formalized via `superlativeAssert`.
-/

namespace VonFintel1999

open Entailment

/-! ## §2 — *only*

The Fauconnier-Ladusaw puzzle: *only John* licenses NPIs in its scope
(`Examples.ex10`) yet the canonical DE inference fails (ex. 11) —
narrowing the scope (kale ⊆ vegetables) is not classically
truth-preserving because the conclusion carries a presupposition
(someone ate kale) the premise does not guarantee. Strawson-DE plugs the
gap (ex. 18), and Strawson-DE suffices for NPI licensing.

> (11) Only John ate vegetables for breakfast. ⇏ Only John ate kale for
>      breakfast. (p. 101)
> (18) Kale is a vegetable. John ate kale for breakfast. Only John ate
>      vegetables for breakfast. ∴ Only John ate kale for breakfast. (p. 104)
-/

/-- The §2 operator: *only John*, with the focus individual modeled as
the world-predicate `· = World.w0`. -/
def onlyJohn : Set World → Set World := onlyFull (· = World.w0)

/-- *Only John*'s existence presupposition: some `John`-world satisfies
the scope. -/
def onlyJohnDefined (scope : Set World) (_w : World) : Prop :=
  ∃ w', w' = World.w0 ∧ scope w'

/-- Ex. 11 (p. 101): *only* is not classically downward entailing —
together with `ex18_only_strawsonDE`, the paper's headline separation
for §2. -/
theorem ex11_only_not_DE : ¬ IsDownwardEntailing onlyJohn :=
  onlyFull_not_de

/-- Ex. 18 (p. 104): *only* is Strawson-DE relative to its existence
presupposition. -/
theorem ex18_only_strawsonDE : IsStrawsonDE onlyJohn onlyJohnDefined :=
  onlyFull_isStrawsonDE _

/-! ### §2.2 *since* (Iatridou, p.c.)

*Since* licenses NPIs in its complement (`Examples.ex21`) but is not
classically DE (ex. 20); adding the temporal presupposition (a past
`p`-event existed) restores the inference (ex. 22):

> (20) It's been five years since I saw a bird of prey in this area. ⇏
>      It's been five years since I saw an eagle in this area. (p. 107)
> (22) …with the additional premise "Five years ago I saw an eagle",
>      the inference of (20) is restored.
-/

/-- Ex. 22 (p. 107): *since* is Strawson-DE in its complement, relative
to the temporal presupposition. -/
theorem ex22_since_strawsonDE (pastEvent sinceWindow : World → Set World) :
    IsStrawsonDE (sinceFull pastEvent sinceWindow)
      (fun p w => ∃ w' ∈ pastEvent w, p w') :=
  sinceFull_isStrawsonDE pastEvent sinceWindow

/-! ### §2.3 — pseudo-anti-additivity is useless for NPI licensing

[atlas-1996] suggests *only John* is "pseudo-anti-additive" (ex. 25,
p. 109): it satisfies the `f(x) ∧ f(y) → f(x ∨ y)` half of
anti-additivity. Von Fintel shows this is "useless for the analysis of
NPI licensing" (p. 110): the property is shared by licensers (*no
student*) and non-licensers (*some/every/at least three students*)
alike (exs. 26-27). The negative argument is a survey of
counterexamples, not a single theorem; its upshot is the substrate as
it stands — Strawson-DE, not pseudo-AA, is the operative notion. -/

/-! ## §3 — adversative attitude predicates

Adversative factives (*sorry*, *regret*, *surprised*, *amazed*) license
NPIs in their complements (`Examples.ex28a`, `Examples.ex28b`) although
the complement position is not classically DE: factivity blocks the
narrowing inference (exs. 29-30), and Strawson-DE restores it by adding
factivity at the evaluation world.

> (29) Robin ate kale ⇒ Robin ate a green vegetable; but Sandy is amazed
>      that Robin ate a green vegetable ⇏ Sandy is amazed that Robin ate
>      kale. (p. 111)
> (30) Robin bought a Honda Civic ⇒ Robin bought a car; but Sandy is
>      sorry that Robin bought a car ⇏ Sandy is sorry that Robin bought
>      a Honda Civic. (p. 111)

Ex. 31 (p. 112) — "Sandy regrets that Robin bought a car, but Sandy does
not regret that Robin bought a Honda Civic" — is [kadmon-landman-1993]'s
prima-facie coherence challenge: if *regret* were uniformly DE, (31)
should be incoherent. Von Fintel's §3.1 reanalysis treats the coherence
as a shift of the modal-base parameter; the Strawson-DE results below
hold on a constant perspective.
-/

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
`Examples.ex28b`, and the §3 counterpart of the §2 separation
(`ex30_sorry_not_DE`). -/
theorem ex28b_sorry_strawsonDE :
    IsStrawsonDE (sorryFull dox bestOf) (fun p w => ∀ w' ∈ dox w, p w') :=
  sorryFull_isStrawsonDE dox bestOf

/-! ### §3.2 — `want` and the Asher/Heim non-monotonicity puzzle

vF §3.2 (pp. 115-121) defends *want* as upward entailing under a
doxastic modal base, against the Asher 1987 Concorde example (eq. 46)
and the Heim 1992 couch example (eq. 48): the apparent non-monotonicity
is a context shift in the modal base, parallel to §3.4. -/

/-- vF §3.2 headline (eq. 45): *want* is upward entailing in its
complement. -/
theorem ex45_want_isUE : Monotone (wantFull bestOf) :=
  wantFull_isUE bestOf

/-! ### §3 footnote 8 — Asher's WDE as a sibling notion

vF p. 112 (footnote 8) cites [asher-1987]'s Weakened Downward
Entailment: a *doxastic* side condition in the *upward* direction, in
contrast to Strawson-DE's presuppositional side condition downward. The
substrate's `IsWDE` captures it; classical UE implies WDE
(`monotone_implies_WDE`). -/

/-! ### §3.3 — *glad* is upward entailing, hence does not license NPIs

The *sorry*/*glad* asymmetry (`Examples.glad_any` vs `Examples.ex28b`):
*sorry* is Strawson-DE in its complement, *glad* is UE, and the
monotonicity asymmetry tracks the NPI-licensing asymmetry — for both
the K&L (ex. 50) and vF (ex. 52) semantics of *glad*.

The same adversative/non-adversative asymmetry shows up in Hindi
([lahiri-1998] §4.5): *aaScarya* 'surprised' licenses *koii bhii* / *ek
bhii*; *khuS* 'glad' does not (`Studies/Lahiri1998.lean`,
`npi_adversative_surprise_ek`, `npi_glad_bad`). Lahiri posits a covert
anti-additive operator; von Fintel derives the asymmetry from lexical
monotonicity — same predictions on the basic English/Hindi data.
-/

/-- Ex. 50 / K&L (p. 122): *glad* under the K&L semantics is upward
entailing — NPIs are not licensed in its complement. -/
theorem ex50_gladKL_isUE : Monotone (gladFull dox bestOf) :=
  gladFull_isUE dox bestOf

/-- Ex. 52 (p. 124), vF's preferred replacement: *glad* is upward
entailing on the vF semantics too — same NPI prediction, different
content (his Honda Civic example, pp. 124-125). -/
theorem ex52_gladVF_isUE (dox relevant : World → Set World)
    (lt : World → World → World → Prop) :
    Monotone (gladFullVF dox relevant lt) :=
  gladFullVF_isUE dox relevant lt

end Adversatives

/-! ### §3.4 — shifting contexts

The coherent sequences (60)/(61) (p. 129) — "Sandy is glad that Robin
bought a car, but sorry that Robin bought a Honda" and its mirror — do
not threaten monotonicity: their coherence rests on a *shift* of the
modal-base parameter between conjuncts, and monotone validity is
checked against a constant context. A formal treatment needs
dynamic-context machinery not yet in `StrawsonEntailment.lean`.

Curveball #2 (exs. 66-68, pp. 133-134): focus-sensitive *only* over a
non-name associate is also Strawson-DE in its prejacent, provided the
option-(a) propositional semantics (closure under entailment of the
prejacent) rather than [von-fintel-1997]'s option (b). The substrate's
`onlyFull` captures option (a) via its assertion clause. -/

/-! ## §4 — conditional antecedents and superlatives

### §4.1 — conditional antecedents

Conditional antecedents license NPIs (`Examples.ex70a`). Whether they
are DE depends on the analysis:

- *Restrictor analysis* ([kratzer-1986]; eq. 72, p. 137): the if-clause
  restricts the modal base. With an idle ordering source, antecedent
  strengthening only shrinks the domain, so the position is classically
  DE — `condNecessity` formalizes exactly this subcase; the full
  Kratzer conditional with a non-trivial ordering source is not
  monotone, which is the §4 puzzle.
- *Stalnaker-Lewis* ([stalnaker-1968], [lewis-1973]; ex. 73, p. 138):
  Strengthening the Antecedent fails. Von Fintel §4.3 (p. 141) defends
  a dynamic monotonic semantics in [von-fintel-2000] under which the
  failures reduce to context shifts, parallel to §3.4. That operator is
  not yet in the substrate.
-/

/-- Ex. 72 (p. 137), restrictor analysis with idle ordering source:
`condNecessity` is classically DE in its antecedent — domain
restriction is antitone. -/
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

/-! ### §4.2 — superlatives

Superlatives license NPIs in their restriction (`Examples.ex75`); adding
a restriction can change the ranking, so the position is not classically
DE (ex. 76), but with the presupposition that the subject satisfies the
new restriction the inference is Strawson-valid (ex. 77):

> (76) Emma is the tallest girl in her class. ⇏ Emma is the tallest girl
>      in her class to have learned the alphabet. (p. 139)
> (77) Emma has learned the alphabet. Emma is the tallest girl in her
>      class. ∴ Emma is the tallest girl in her class to have learned
>      the alphabet. (p. 139)

`superlativeAssert` encodes the predicative use (exs. 75/77); the
definite-description use (ex. 80, p. 140) lacks local Strawson-DE — see
the substrate's superlative section.
-/

/-- Ex. 77 (p. 139): the superlative is Strawson-DE in its restriction,
relative to the presupposition that the subject satisfies the
restriction. -/
theorem ex77_superlative_strawsonDE (α : World) :
    IsStrawsonDE (superlativeAssert α) (superlativePresup α) :=
  superlative_isStrawsonDE α

/-! ## Hierarchy connection

The paper's §1 sets up the AM → AA → DE hierarchy; §2 extends it
downward with Strawson-DE (`de_implies_strawsonDE` in the substrate).
The four recalcitrant operators — `onlyJohn` (`ex18_only_strawsonDE`),
`sorryFull` (`ex28b_sorry_strawsonDE`), `condNecessity`
(`conditional_antecedent_strawsonDE_under_restrictor`), and
`superlativeAssert` (`ex77_superlative_strawsonDE`) — land at exactly
Strawson-DE, while `gladFull` sits outside the hierarchy entirely (UE).
-/

/-! ## Cross-framework bridges

Chronology rule: this file may reference [kadmon-landman-1993],
[lahiri-1998], and [hoeksema-1983] (all earlier), not the reverse.

**K&L ≡ vF on the adversative asymmetry.** Both derive the
*sorry*/*glad* asymmetry from the same substrate theorems
(`sorryFull_isStrawsonDE`, `gladFull_isUE`) — K&L glossing them as
"lexical entailment to *want ¬A*", vF as Strawson-DE/UE of the
attitude. The `example`s below check the statement identity: K&L's
proof terms discharge this file's statements verbatim. The prose
explanations differ; distinguishing them empirically requires the
settle-for-less data below. -/

example (dox bestOf : World → Set World) :
    IsStrawsonDE (sorryFull dox bestOf) (fun p w => ∀ w' ∈ dox w, p w') :=
  KadmonLandman1993.sorry_licenses_any dox bestOf

example (dox bestOf : World → Set World) :
    Monotone (gladFull dox bestOf) :=
  KadmonLandman1993.glad_does_not_license dox bestOf

/-- **`gladFull_isUE` undergenerates against the settle-for-less data.**
[lahiri-1998] §4.5 records Hindi *khuS* 'glad' + NPI as grammatical on
a "settle for less" reading (`npi_glad_settle`); [kadmon-landman-1993]
flag the same in English (`settleGladAnybody`, `settleGladTickets`).
`gladFull_isUE` predicts uniformly no licensing, so the rescued reading
needs machinery the substrate lacks — a perspective-shifted `bestOf` or
a Strawson-DE treatment of the shifted reading. This records the
data-side of that gap. -/
theorem bridge_lahiri_glad_settle_overgeneration :
    Lahiri1998.npi_glad_settle.grammatical = true ∧
    KadmonLandman1993.settleGladAnybody.grammatical = true ∧
    KadmonLandman1993.settleGladTickets.grammatical = true :=
  ⟨rfl, rfl, rfl⟩

/-- **Hoeksema's S-comparative is anti-additive, hence Strawson-DE.**
[hoeksema-1983] proves the S-comparative anti-additive
(`Degree.gtOverSet_isAntiAdditive`); AA → DE → Strawson-DE makes the
bridge automatic. This places the S-comparative in the Strawson-DE
class of vF's recalcitrants with classical AA to spare — S-comparatives
license *strong* NPIs where vF's *only* licenses only weak ones. -/
theorem bridge_hoeksema_gtOverSet_strawsonDE
    {Entity D : Type*} [Preorder D] (μ : Entity → D)
    (defined : Set D → Entity → Prop) :
    IsStrawsonDE (Core.Order.Comparison.gt.overSet μ) defined :=
  antitone_implies_strawsonDE _
    (Degree.gtOverSet_isAntiAdditive μ).antitone defined

/-! ### (15) and Rooth's strong theory

Von Fintel's (15) (p. 104) excludes by *individual* identity — "if
defined, ⟦only⟧(x)(P) = True iff ¬∃y ≠ x: P(y) = True" — while
[rooth-1992]'s strong theory (`onlyVia`) excludes by *proposition*
identity over a resolved alternative set. The two coincide over the
individual-generated family exactly when the family is injective:
individuals with coinciding P-propositions are distinguished by (15)
but invisible to `onlyVia`. World-constant propositions (the
extensional `onlyFull`) are the degenerate case where injectivity fails
wholesale, which is why the bridge is stated intensionally. -/

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
