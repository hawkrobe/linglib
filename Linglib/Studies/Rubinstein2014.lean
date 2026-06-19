import Linglib.Studies.Narrog2010
import Linglib.Semantics.Modality.Kratzer.Flavor
import Linglib.Semantics.Modality.Directive
import Linglib.Fragments.English.Auxiliaries
import Linglib.Data.Examples.Rubinstein2014
import Mathlib.Data.Fin.Basic

/-!
# On Necessity and Comparison
[rubinstein-2014]

Supports [sloman-1970]'s proposal that a comparative semantics is the defining
property of weak necessity. Weak necessity modals (*ought*, *should*) and
evaluative comparative predicates (*good*, *better*, *preferable*, *worthwhile*)
form a semantic natural class: both are relativized to **negotiable** ideals —
priorities not endorsed by all discourse participants.

Rubinstein splits [kratzer-1981]/[kratzer-1991] ordering-source material into two
kinds. Non-negotiable priorities are promoted to modal-base status, restricting
the **favored worlds** via [frank-1996]'s compatibility-restricted union; the
remaining negotiable priorities stay as an ordering source. Strong necessity
quantifies over *all* favored worlds (no ordering, [frank-1996]'s non-comparative
analysis); weak necessity over the *best* favored worlds, ranked by the negotiable
ideals — the comparative component. The reduction `weakNecessityR ≅ necessity` ties
this back to [von-fintel-iatridou-2008]-style Kratzer semantics.

## Main definitions

* `PriorityTypology` — modal base split into circumstances, non-negotiable
  priorities, and a negotiable ordering source.
* `favoredWorlds`, `strongNecessityR`, `weakNecessityR` — the favored-worlds set
  and the strong/weak necessity operators over it.
* `WeakNecessityStrategy` — the three crosslinguistic routes to weak necessity.

## Main results

* `strong_entails_weak_R`, `weak_not_entails_strong_R` — the strong/weak asymmetry.
* `strongR_eq_simpleNecessity`, `weakR_eq_necessity` — reductions to Kratzer
  semantics when no priorities are promoted.
* `should_to_haveto_shift` — the tax-report promotion (§3.3): the same prejacent
  shifts from weak-only to strong necessity when a negotiable ideal is endorsed.
* `negRaising_iff_fragment_weak`, `evaluatives_neg_raise` — neg-raising tracks
  the English fragment's weak-necessity marking ([horn-1978] diagnostics).
* `hebrew_strategy_evaluative`, `weak_rarity` — Hebrew expresses weak necessity
  only through evaluative comparison; only 62/200 languages grammaticalize it
  ([narrog-2012]).

Empirical stimuli (Hebrew, Spanish, English diagnostics) live as typed
`LinguisticExample` rows in `Data.Examples.Rubinstein2014`; theorems quantify over
their `judgment`/`readings`/`paperFeatures`.
-/

namespace Rubinstein2014

abbrev World := Fin 4

open Semantics.Modality.Kratzer
open Semantics.Modality.Directive
open Semantics.Modality (ModalForce)
open Data.Examples

/-! ### Priority reconceptualization (§3.2)

Rubinstein argues that norms, ideals, and preferences — traditionally all
ordering-source material in [kratzer-1981]'s framework — come in two kinds:

- **Non-negotiable**: promoted to modal-base status. These restrict which
  worlds are "live possibilities" (the favored worlds).
- **Negotiable**: remain as ordering-source material. These rank the favored
  worlds but do not eliminate any from consideration.

Strong necessity modals quantify over all favored worlds (no ordering); weak
necessity modals quantify over the BEST favored worlds (with ordering). -/

/-- Whether a priority is negotiable among discourse participants.
    A priority is negotiable iff at least one discourse participant is not
    committed to it (§3.3, definition 49). -/
inductive Negotiability where
  | negotiable      -- not all participants committed; ordering source material
  | nonNegotiable   -- all participants committed; promoted to modal base
  deriving DecidableEq, Repr

/-- Rubinstein's reconceptualized modal backgrounds (§3.2).

    In standard [kratzer-1981], there is one modal base f and one ordering
    source g. Rubinstein splits priorities into two components based on
    negotiability, promoting the non-negotiable part to modal-base status. -/
structure PriorityTypology where
  /-- Factual circumstances: standard Kratzer modal base f(e). -/
  circumstances : ModalBase World
  /-- Non-negotiable priorities h(e): promoted to modal-base status.
      These are norms/ideals that all discourse participants endorse. -/
  nonNegotiable : ModalBase World
  /-- Negotiable priorities g(e): remain as ordering source.
      These are ideals promoted by an opinionated assessor but not
      universally endorsed. -/
  negotiable : OrderingSource World

/-! ### Favored worlds (§3.2, definitions 39–40)

The favored worlds are determined by combining factual circumstances with
non-negotiable priorities. When priorities are consistent with circumstances,
this is simply the intersection of both.

Full definition: `Fav(f, h, e) = ∪{∩M : M ∈ f(e) + h(e)}` where `f(e) + h(e)`
is [frank-1996]'s compatibility-restricted union (def 39). When h(w) is
consistent with f(w), this reduces to `∩(f(w) ∪ h(w))`. We implement the
consistent case, which covers the paper's examples. -/

/-- **Favored worlds** (definition 40, consistent case):
    worlds satisfying both the factual circumstances f(w) and the
    non-negotiable priorities h(w). -/
def favoredWorlds (pt : PriorityTypology) (w : World) : Set World :=
  propIntersection (pt.circumstances w ++ pt.nonNegotiable w)

/-- Favored worlds with no non-negotiable priorities reduce to
    standard Kratzer accessible worlds. -/
theorem favored_no_promoted (f : ModalBase World) (g : OrderingSource World) (w : World) :
    favoredWorlds ⟨f, emptyBackground, g⟩ w = accessibleWorlds f w := by
  unfold favoredWorlds accessibleWorlds emptyBackground propIntersection
  ext w'
  simp only [List.append_nil]

-- `bestAmong`, `bestAmong_empty`, and `bestAmong_sub` are imported from
-- `Kratzer.lean`, where they were promoted as general-purpose operations.

/-! ### Strong and weak necessity (§3.2, definitions 41–42)

Strong necessity quantifies over ALL favored worlds (no ordering). Weak
necessity quantifies over the BEST favored worlds (ordered by negotiable
priorities). This is where the comparative semantics enters: weak necessity
uses world ranking, strong necessity does not. -/

/-- **Strong necessity** (definition 41):
    `⟦must⟧ = λpλe∀w'(w' ∈ Fav(f, h, e) → w' ∈ p)`

    Universal quantification over favored worlds. No ordering source
    is consulted — strong necessity is non-comparative. -/
def strongNecessityR (pt : PriorityTypology) (p : World → Prop) (w : World) : Prop :=
  ∀ w' ∈ favoredWorlds pt w, p w'

/-- **Weak necessity** (definition 42):
    `⟦ought⟧ = λpλe∀w'(w' ∈ BEST(Fav(f, h, e), g(e)) → w' ∈ p)`

    Universal quantification over the best favored worlds, where "best"
    is determined by the negotiable ordering source g(e). -/
def weakNecessityR (pt : PriorityTypology) (p : World → Prop) (w : World) : Prop :=
  ∀ w' ∈ bestAmong (favoredWorlds pt w) (pt.negotiable w), p w'

/-! ### Strong necessity entails weak necessity (§1, the paper's key asymmetry)

Since `BEST(Fav, g) ⊆ Fav` (the best worlds are a subset of all favored
worlds), if p holds at all favored worlds, it a fortiori holds at all best
favored worlds. -/

/-- **Strong necessity entails weak necessity** in Rubinstein's framework.
    Parallel to `Directive.strong_entails_weak`, but derived from the
    subset relation `BEST(Fav, g) ⊆ Fav`. -/
theorem strong_entails_weak_R (pt : PriorityTypology) (p : World → Prop)
    (w : World) (h : strongNecessityR pt p w) :
    weakNecessityR pt p w := by
  intro w' hw'
  exact h w' (bestAmong_sub _ _ hw')

/-- Counterexample components for the converse. -/
private def ce_pt : PriorityTypology where
  circumstances := emptyBackground
  nonNegotiable := emptyBackground
  negotiable := λ _ => [λ w => w = (1 : World)]

private def ce_p : World → Prop := λ w => w = (1 : World)

instance : DecidablePred ce_p := fun w => decEq w (1 : World)

/-- The converse fails: weak necessity does NOT entail strong necessity.
    If p holds at all BEST favored worlds but not at all favored worlds,
    weak necessity holds but strong necessity does not.

    Concretely: with `circumstances = nonNegotiable = ∅` and
    `negotiable = [λw => w = (1 : World)]`, we have
    `favoredWorlds ce_pt (0 : World) = Set.univ` and
    `bestAmong univ [λw => w = (1 : World)] = {(1 : World)}`. Thus `ce_p` (which says
    `w = (1 : World)`) holds at all best worlds but not at all favored worlds. -/
theorem weak_not_entails_strong_R :
    ¬(∀ (pt : PriorityTypology) (p : World → Prop) [DecidablePred p] (w : World),
      weakNecessityR pt p w → strongNecessityR pt p w) := by
  intro h
  -- Compute favoredWorlds ce_pt (0 : World) = univ
  have hFav : favoredWorlds ce_pt (0 : World) = Set.univ := by
    unfold favoredWorlds ce_pt emptyBackground propIntersection
    ext w; simp
  -- Show weakNecessityR ce_pt ce_p (0 : World) holds:
  -- Every world in `bestAmong univ [λw => w = (1 : World)]` satisfies ce_p.
  have hWeak : weakNecessityR ce_pt ce_p (0 : World) := by
    intro w' hw'
    -- hw' : w' ∈ bestAmong (favoredWorlds ce_pt (0 : World)) (ce_pt.negotiable (0 : World))
    obtain ⟨_hMem, hBest⟩ := hw'
    -- Apply hBest with the test world (1 : World), which is in favoredWorlds.
    have hW1Fav : (1 : World) ∈ favoredWorlds ce_pt (0 : World) := by rw [hFav]; exact Set.mem_univ _
    -- The single ordering proposition is (λ w => w = (1 : World)).
    have hProp : (λ w : World => w = (1 : World)) ∈ ce_pt.negotiable (0 : World) := by
      simp only [ce_pt, List.mem_singleton]
    have := hBest (1 : World) hW1Fav (λ w : World => w = (1 : World)) hProp rfl
    exact this
  -- Show strongNecessityR ce_pt ce_p (0 : World) fails: ce_p (0 : World) = ((0 : World) = (1 : World)) is false.
  have hNotStrong : ¬ strongNecessityR ce_pt ce_p (0 : World) := by
    intro hS
    have hW0Fav : (0 : World) ∈ favoredWorlds ce_pt (0 : World) := by rw [hFav]; exact Set.mem_univ _
    have : ce_p (0 : World) := hS (0 : World) hW0Fav
    -- ce_p (0 : World) unfolds to `(0 : World) = (1 : World)`, which is false
    exact absurd this (by intro h; cases h)
  exact hNotStrong (h ce_pt ce_p (0 : World) hWeak)

/-! ### Reduction to standard Kratzer semantics (bridge to `Directive.lean`)

When no priorities are promoted to modal-base status (h = ∅), Rubinstein's
strong necessity reduces to simple Kratzer necessity (no ordering), and her
weak necessity reduces to standard Kratzer necessity with the negotiable
ordering source. -/

/-- With no promoted priorities, Rubinstein's strong necessity equals
    simple Kratzer necessity (no ordering). -/
theorem strongR_eq_simpleNecessity (f : ModalBase World) (p : World → Prop)
    (w : World) :
    strongNecessityR ⟨f, emptyBackground, emptyBackground⟩ p w ↔
    simpleNecessity f p w := by
  rw [simpleNecessity_iff_all]
  unfold strongNecessityR
  rw [favored_no_promoted f emptyBackground w]

/-- With no promoted priorities, Rubinstein's weak necessity equals
    standard Kratzer necessity under the negotiable ordering.

    This is **not** the same as `Directive.weakNecessity` — Rubinstein's
    "weak" with h=∅ equals Directive's "strong" (with g). The analyses
    differ structurally: Directive treats all priorities as ordering-source
    material; Rubinstein promotes some to modal-base status. -/
theorem weakR_eq_necessity (f : ModalBase World) (g : OrderingSource World)
    (p : World → Prop) (w : World) :
    weakNecessityR ⟨f, emptyBackground, g⟩ p w ↔
    necessity f g p w := by
  rw [necessity_iff_all]
  unfold weakNecessityR
  rw [favored_no_promoted f g w]
  -- bestAmong (accessibleWorlds f w) (g w) = bestWorlds f g w by definition
  rfl

/-- When no priorities are promoted AND no negotiable ordering exists,
    strong and weak necessity coincide (both = simple necessity). -/
theorem strongR_eq_weakR_trivial (f : ModalBase World) (p : World → Prop)
    (w : World) :
    strongNecessityR ⟨f, emptyBackground, emptyBackground⟩ p w ↔
    weakNecessityR ⟨f, emptyBackground, emptyBackground⟩ p w := by
  unfold strongNecessityR weakNecessityR
  rw [favored_no_promoted f emptyBackground w]
  -- After rewriting, the favored set is `accessibleWorlds f w`.
  -- The negotiable ordering is `emptyBackground .. = []`, so
  -- `bestAmong (accessibleWorlds f w) [] = accessibleWorlds f w` by `bestAmong_empty`.
  show (∀ w' ∈ accessibleWorlds f w, p w') ↔
       ∀ w' ∈ bestAmong (accessibleWorlds f w) [], p w'
  rw [bestAmong_empty]

/-! ### The tax report scenario (§3.3, examples 45–47, 51)

The paper's central worked example (§3.3): An accountant says "We should
report all our revenue" — promoting a negotiable ideal about international
revenue. The law about domestic revenue is non-negotiable. Later, if the
manager endorses the ideal, the international-revenue clause is promoted to
non-negotiable status, making "We have to report all our revenue" appropriate.

We model this with two propositions:
- reportDomestic: a non-negotiable legal obligation (in h)
- reportInternational: a negotiable ideal promoted by the speaker (in g)
- reportAll: the conjunction (the prejacent of should/have-to) -/

private def reportDomestic : World → Prop := λ w => w = (0 : World) ∨ w = (1 : World)
private def reportInternational : World → Prop := λ w => w = (0 : World) ∨ w = (2 : World)
private def reportAll : World → Prop := λ w => reportDomestic w ∧ reportInternational w

instance : DecidablePred reportDomestic := by unfold reportDomestic; infer_instance
instance : DecidablePred reportInternational := by unfold reportInternational; infer_instance
instance : DecidablePred reportAll := by
  unfold reportAll reportDomestic reportInternational; infer_instance

/-- **Scenario A** (ex. 45/51a): "We should report all our revenue."
    Domestic reporting is non-negotiable; international is negotiable. -/
private def taxScenarioA : PriorityTypology where
  circumstances := emptyBackground
  nonNegotiable := λ _ => [reportDomestic]
  negotiable := λ _ => [reportInternational]

/-- **Scenario B** (ex. 46/51b): "We have to report all our revenue."
    Both domestic and international reporting are now non-negotiable
    (the manager endorsed the international ideal). -/
private def taxScenarioB : PriorityTypology where
  circumstances := emptyBackground
  nonNegotiable := λ _ => [reportDomestic, reportInternational]
  negotiable := emptyBackground

/-- In scenario A, the favored worlds are exactly those satisfying
    `reportDomestic`, namely `{(0 : World), (1 : World)}`. -/
private theorem favored_taxScenarioA :
    favoredWorlds taxScenarioA (0 : World) = {w | reportDomestic w} := by
  unfold favoredWorlds taxScenarioA emptyBackground propIntersection
  ext w
  simp

/-- In scenario A, weak necessity holds: all BEST favored worlds
    satisfy reportAll (the ordering picks out worlds where international
    revenue is also reported).

    The single negotiable ideal `reportInternational` holds at (0 : World) (which is
    in favored worlds and satisfies all of `reportInternational`), so any
    "best" favored world must also satisfy it. The only favored world
    satisfying both is (0 : World), so `reportAll` holds at all best favored worlds. -/
theorem tax_should_holds :
    weakNecessityR taxScenarioA reportAll (0 : World) := by
  intro w' hw'
  obtain ⟨hFav, hBest⟩ := hw'
  -- w' ∈ favoredWorlds taxScenarioA (0 : World), so reportDomestic w'
  have hDom : reportDomestic w' := by
    rw [favored_taxScenarioA] at hFav; exact hFav
  -- (0 : World) is favored (it's in {(0 : World), (1 : World)})
  have hW0Fav : ((0 : World) : World) ∈ favoredWorlds taxScenarioA (0 : World) := by
    rw [favored_taxScenarioA]; show reportDomestic (0 : World)
    unfold reportDomestic; left; rfl
  -- (0 : World) satisfies reportInternational
  have hW0Int : reportInternational (0 : World) := by
    unfold reportInternational; left; rfl
  -- The ordering proposition `reportInternational` is in negotiable (0 : World)
  have hPropMem : reportInternational ∈ taxScenarioA.negotiable (0 : World) := by
    simp only [taxScenarioA, List.mem_singleton]
  -- So w' must satisfy reportInternational (it's at-least-as-good as (0 : World))
  have hInt : reportInternational w' := hBest (0 : World) hW0Fav reportInternational hPropMem hW0Int
  exact ⟨hDom, hInt⟩

/-- In scenario A, strong necessity FAILS: not all favored worlds
    satisfy reportAll (worlds reporting only domestic revenue survive).

    (1 : World) is favored (satisfies reportDomestic) but does not satisfy
    reportInternational, so reportAll fails at (1 : World). -/
theorem tax_must_fails :
    ¬ strongNecessityR taxScenarioA reportAll (0 : World) := by
  intro h
  -- (1 : World) ∈ favoredWorlds (satisfies reportDomestic via the second disjunct)
  have hW1Fav : ((1 : World) : World) ∈ favoredWorlds taxScenarioA (0 : World) := by
    rw [favored_taxScenarioA]; show reportDomestic (1 : World)
    unfold reportDomestic; right; rfl
  have hAll : reportAll (1 : World) := h (1 : World) hW1Fav
  -- reportAll (1 : World) implies reportInternational (1 : World), but
  -- reportInternational (1 : World) = ((1 : World) = (0 : World) ∨ (1 : World) = (2 : World)), both false
  obtain ⟨_, hInt⟩ := hAll
  rcases hInt with h | h <;> cases h

/-- In scenario B (after promotion), strong necessity holds: all
    favored worlds now satisfy reportAll.

    With both `reportDomestic` and `reportInternational` non-negotiable,
    favored worlds must satisfy both, so `reportAll` holds trivially. -/
theorem tax_must_holds_after_promotion :
    strongNecessityR taxScenarioB reportAll (0 : World) := by
  intro w' hw'
  -- hw' : w' ∈ favoredWorlds taxScenarioB (0 : World) = propIntersection ([] ++ [reportDomestic, reportInternational])
  -- So w' satisfies both reportDomestic and reportInternational.
  unfold favoredWorlds taxScenarioB emptyBackground propIntersection at hw'
  simp at hw'
  exact ⟨hw'.1, hw'.2⟩

/-- The should→have-to shift: the SAME proposition goes from weak-only
    to strong necessity when the negotiable ideal is promoted. -/
theorem should_to_haveto_shift :
    ¬ strongNecessityR taxScenarioA reportAll (0 : World) ∧
    strongNecessityR taxScenarioB reportAll (0 : World) :=
  ⟨tax_must_fails, tax_must_holds_after_promotion⟩

/-! ### The evaluative comparative natural class (§2.1, §2.1.3)

The central empirical thesis: *ought*, *should*, *good*, *better*,
*preferable*, and *worthwhile* share a semantic core — quantification over
BEST worlds ranked by negotiable ordering sources. Class membership is
diagnosed by two felicity tests (Test 1: "x E q, but doesn't have to q";
Test 2 with an exclusive: "y has to q, x only E q"). The stimuli are typed
`LinguisticExample` rows in `Data.Examples.Rubinstein2014`; we read their
felicity off `judgment`. -/

/-- Weak-necessity *ought* passes Test 1 (§2.1, ex 8a): "I ought to do the
    dishes but I don't have to" is felicitous because weak necessity is
    strictly weaker than have-to. -/
theorem ought_passes_test1 :
    Examples.ought_lexical.judgment = .acceptable := by decide

/-- The Hebrew evaluative comparatives all pass Test 1 in the bribe scenario
    (§2.1.3, ex 21): *yoter tov*, *'adif*, and *kday* are felicitous
    translations of priority-type *ought*. -/
theorem evaluatives_pass_test1 :
    [Examples.heb_yoter_tov, Examples.heb_adif, Examples.heb_kday].all
      (·.judgment == .acceptable) = true := by decide

/-- *carix* 'need' fails both strength tests (§2.1.2, ex 16a, 19):
    substituting it for *ought* is infelicitous, aligning it with strong
    necessity (*xayav* 'must') rather than the comparative class. -/
theorem carix_fails_strength_tests :
    Examples.test1_carix.judgment ≠ .acceptable ∧
    Examples.test2_carix.judgment ≠ .acceptable := ⟨by decide, by decide⟩

/-- The morphological comparative *better* supports an explicit than-clause
    (§2.1.3, ex 24), making the comparative backbone overt. Modal *ought*
    (positive/superlative) only selects the overall best — see [rubinstein-2014]. -/
theorem better_supports_than_clause :
    Examples.comp_better.judgment = .acceptable ∧
    Examples.comp_better.paperFeatures.lookup "pairwise" = some "true" :=
  ⟨by decide, by decide⟩

/-! ### Neg-raising and negotiability (§2.2, §3.4)

Rubinstein connects the evaluative comparative class to neg-raising (§3.4):
predicates relativized to negotiable ordering sources have an "opinionated"
alternative `□.¬p` available, enabling the excluded-middle inference that
underlies neg-raising. Strong necessity modals, which quantify over favored
worlds WITHOUT ordering, lack this alternative. Horn's ([horn-1978]) cyclicity
diagnostic ("I don't think you should leave" ≅ "I think you should stay")
splits the modals; the stimuli carry the lower-negation reading on `readings`.

The weak/strong split for English modal *verbs* is **derived** from the
English fragment (`Auxiliaries.lean`) rather than re-stipulated: a verb
neg-raises iff the fragment marks it weak necessity. -/

/-- Stimuli testing neg-raising under higher negation. -/
def negRaisingRows : List LinguisticExample :=
  Examples.all.filter (·.paperFeatures.lookup "diagnostic" == some "negRaising")

/-- Force assigned to an English modal *verb* by the English fragment — the
    single source of truth for modal force. (Evaluative comparatives are
    adjectives, outside the auxiliary fragment.) -/
private def fragmentMarksWeak : String → Bool
  | "should"  => English.Auxiliaries.should.modalMeaning.any (·.force == .weakNecessity)
  | "ought"   => English.Auxiliaries.ought.modalMeaning.any (·.force == .weakNecessity)
  | "must"    => English.Auxiliaries.must.modalMeaning.any (·.force == .weakNecessity)
  | "have to" => English.Auxiliaries.haveTo.modalMeaning.any (·.force == .weakNecessity)
  | "need"    => English.Auxiliaries.need.modalMeaning.any (·.force == .weakNecessity)
  | _         => false

/-- **The neg-raising split, derived from the fragment.** For every English
    modal-*verb* stimulus, the lower-negation (neg-raising) reading is
    available iff the English fragment marks the verb as weak necessity.
    Flipping either the fragment's force assignment or the recorded reading
    breaks this — the classification is derived, not stipulated. -/
theorem negRaising_iff_fragment_weak :
    (negRaisingRows.filter (·.paperFeatures.lookup "category" == some "modalVerb")).all
      (fun e =>
        (e.readings.lookup "lowerNeg" == some Features.Judgment.acceptable) ==
        fragmentMarksWeak ((e.paperFeatures.lookup "modal").getD "")) = true := by decide

/-- Every evaluative-comparative stimulus shows the neg-raising reading
    (*good*, *better*, *'adif*), the empirical core of the natural-class
    claim (§2.2, ex 30, 31a, 33). -/
theorem evaluatives_neg_raise :
    (negRaisingRows.filter (·.paperFeatures.lookup "category" == some "evaluativeComparative")).all
      (·.readings.lookup "lowerNeg" == some Features.Judgment.acceptable) = true := by decide

/-- Strong necessity modal verbs (*must*, *have to*) lack the neg-raising
    reading (§2.2, ex 31b). -/
theorem strong_verbs_no_neg_raising :
    (negRaisingRows.filter (fun e =>
       e.paperFeatures.lookup "category" == some "modalVerb" &&
       !fragmentMarksWeak ((e.paperFeatures.lookup "modal").getD ""))).all
      (·.readings.lookup "lowerNeg" == some Features.Judgment.unacceptable) = true := by decide

/-! ### Cross-linguistic typology of weak necessity (§2.1; Table 1, [narrog-2012])

There are three crosslinguistic routes to weak necessity: a dedicated lexical
item (English *should*/*ought*), compositional weakening of a strong modal
(Spanish *debería* = *deber*+COND), or evaluative-comparative language
(Hebrew *yoter tov*). Hebrew lacks the first two; this supports the claim that
weak necessity is comparative — where the comparative route is the only route,
it surfaces overtly. Data imported from `Studies/Narrog2010.lean`. -/

/-- Rubinstein's three routes to expressing weak necessity (§2.1). -/
inductive WeakNecessityStrategy where
  | lexical               -- dedicated item (English should/ought)
  | compositional         -- strong + weakening morphology (Spanish debería)
  | evaluativeComparative -- comparative/evaluative language (Hebrew yoter tov)
  deriving DecidableEq, Repr

/-- English has a lexical weak-necessity strategy (§2.1, ex 8a). -/
theorem english_lexical :
    Examples.all.any (fun e =>
      e.language == "stan1293" &&
      e.paperFeatures.lookup "strategy" == some "lexical") = true := by decide

/-- Spanish has a compositional strategy: *deber* + conditional (§2.1, ex 8b). -/
theorem spanish_compositional :
    Examples.all.any (fun e =>
      e.language == "stan1288" &&
      e.paperFeatures.lookup "strategy" == some "compositional") = true := by decide

/-- Hebrew has neither lexical nor compositional weak necessity (§2.1.1–2.1.2):
    no Hebrew stimulus uses those strategies. -/
theorem hebrew_lacks_lexical_and_compositional :
    Examples.all.all (fun e =>
      !(e.language == "hebr1245") ||
        (!(e.paperFeatures.lookup "strategy" == some "lexical") &&
         !(e.paperFeatures.lookup "strategy" == some "compositional"))) = true := by decide

/-- The Hebrew route to weak necessity is exclusively evaluative-comparative
    (§2.1.3, ex 21): every Hebrew strategy-bearing stimulus uses it. -/
theorem hebrew_strategy_evaluative :
    (Examples.all.filter (fun e =>
       e.language == "hebr1245" && e.paperFeatures.any (·.1 == "strategy"))).all
      (·.paperFeatures.lookup "strategy" == some "evaluativeComparative") = true := by decide

open Narrog2010 in
/-- Only 62 of the 200 surveyed languages grammaticalize weak deontic
    necessity (Table 1), supporting Rubinstein's claim that weak necessity is
    not a universal grammatical category. The Table-1 row totals exceed the
    131 languages with deontic necessity because some have modals of multiple
    types. -/
theorem weak_rarity : countOf .weak = 62 := by decide

/-! ### Bridge to the English fragment (`Auxiliaries.lean`)

The English fragment classifies modals by force; we verify these match
Rubinstein's force assignments: *should*/*ought* are weak necessity
(comparative class), *must*/*need* are strong necessity (non-comparative). -/

/-- The English fragment classifies *should* as weak necessity. -/
theorem fragment_should_weak :
    English.Auxiliaries.should.modalMeaning.any
      (·.force == .weakNecessity) = true := by decide

/-- The English fragment classifies *ought* as weak necessity. -/
theorem fragment_ought_weak :
    English.Auxiliaries.ought.modalMeaning.any
      (·.force == .weakNecessity) = true := by decide

/-- The English fragment classifies *must* as strong necessity. -/
theorem fragment_must_strong :
    English.Auxiliaries.must.modalMeaning.any
      (·.force == .necessity) = true := by decide

/-- *must* is NOT classified as weak necessity — confirming it is
    outside the evaluative comparative natural class. -/
theorem fragment_must_not_weak :
    English.Auxiliaries.must.modalMeaning.any
      (·.force == .weakNecessity) = false := by decide

/-- *should* is NOT classified as strong necessity — confirming the
    asymmetry: comparative class members have strictly weaker force. -/
theorem fragment_should_not_strong :
    English.Auxiliaries.should.modalMeaning.any
      (·.force == .necessity) = false := by decide

/-- *need* is classified as strong necessity — matching its exclusion
    from the evaluative comparative class (§2.1.2, note 14). -/
theorem fragment_need_strong :
    English.Auxiliaries.need.modalMeaning.any
      (·.force == .necessity) = true := by decide

/-- *need* is NOT classified as weak necessity — confirming it fails
    the scalar tests (examples 16, 18–19). -/
theorem fragment_need_not_weak :
    English.Auxiliaries.need.modalMeaning.any
      (·.force == .weakNecessity) = false := by decide

end Rubinstein2014
