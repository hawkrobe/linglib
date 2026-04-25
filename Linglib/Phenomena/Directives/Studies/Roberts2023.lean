import Linglib.Core.WorldTimeIndex
import Linglib.Core.Modality.HistoricalAlternatives
import Linglib.Core.Mood.IllocutionaryMood
import Linglib.Core.Mood.POSW
import Linglib.Core.Mood.POSWTarget
import Linglib.Core.Discourse.Scoreboard
import Linglib.Theories.Semantics.Modality.Kratzer.Flavor
import Linglib.Theories.Semantics.Modality.Directive
import Linglib.Theories.Semantics.Modality.Assert
import Linglib.Phenomena.Directives.Studies.RuytenbeekEtAl2017
import Mathlib.Data.Fin.Basic

/-!
# Roberts (2023): Imperatives in Dynamic Pragmatics
@cite{roberts-2023}

Imperatives in dynamic pragmatics. *Semantics & Pragmatics* 16, Article 7: 1–55.

## Core Contribution

A semantics and dynamic pragmatics for imperative mood that combines the
best features of @cite{kaufmann-2012} and @cite{portner-2004}:

1. **Semantic type**: Imperatives denote *de se* properties indexed to the
   addressee — following @cite{portner-2004}.
2. **Modal in semantic content**: The content includes a futurate
   circumstantial modal with Kratzerian modal base *f* and goal-based
   ordering source *g* — following @cite{kaufmann-2012}. But the modal
   is **not deontic**.
3. **Pragmatic deontic flavor**: The perceived deontic force arises
   entirely from the pragmatics of accepting a direction — updating the
   addressee's preference structure (the goals component G of the
   discourse scoreboard) — not from the LF.

## Substrate hookup

This file is a **configuration of existing infrastructure**, not a
standalone formalization of an imperative mood ontology:

- The futurate modal base reuses
  `Core.Modality.HistoricalAlternatives.futureHistoryBase`.
- The goal-based ordering and circumstantial modal base are
  `Kratzer.OrderingSource` / `ModalBase`, packaged as
  `TeleologicalFlavor` (no parallel types).
- The architectural commitment "imperative force targets the
  preferential POSW component, not the informational" is
  `Core.Mood.POSWTarget`'s `HasPOSWTarget IllocutionaryMood`
  instance — Roberts agrees with @cite{portner-2018} on the
  POSW component, disagrees with @cite{kaufmann-2012} only on
  the prejacent's modal flavor.
- The scoreboard updates are `Core.Discourse.Scoreboard`'s
  assertion/interrogation/direction; the *derivation* that
  `directionUpdate` factors as `POSW.star` lives in Scoreboard.lean
  (`toPOSW_direction_eq_star`).

## Equation citations

All equation numbers verified against the published PDF:
(45) circumstance, (47) SameHistory, (48) FUT, (49) goal-based
ordering source, (50) timely future, (51) futurate circumstantial
modal base, (53) APPLIC, (54)/(67) imperative character ¡,
(57) assertion, (58) interrogation, (59) direction, (65)
conservativity. Example "Have a cookie" is (60) in §2.2 (not §3).
-/

namespace Roberts2023

open Core (WorldTimeIndex)
open Core.Discourse (forceLinkingPrinciple defaultSemanticType sincerityCondition Scoreboard)
open Core.Mood (POSW POSWQ POSWTarget IllocutionaryMood HasPOSWTarget)
open Core.Modality.HistoricalAlternatives
open Semantics.Modality.Kratzer

abbrev World := Fin 4

/-! ## §2.1.2 Basic Ontology

Roberts's "circumstance" ⟨w, t⟩ (eq. 45), SameHistory (47), and FUT
(48) all instantiate the canonical world-time substrate in
`Core.WorldTimeIndex` and `Core.Modality.HistoricalAlternatives`:

  Roberts                        Linglib substrate
  ────────────────────────────   ────────────────────────────
  ⟨w, t⟩ circumstance            `WorldTimeIndex W T`
  SameHistory(w', w, t)          `WorldHistory W T` predicate
  FUT(⟨w, t⟩)                    `futureHistoryBase history s`

No new types are introduced for these. -/

/-! ## §2.1.2 The Imperative Character

Roberts's `¡` (eq. 54/67) bundles the addressee, the prejacent, and
the modal parameters. The modal flavor is **teleological** — facts
plus goals — represented directly by `Kratzer.TeleologicalFlavor`.
The "futurate" property of the modal base is enforced separately as
the predicate `IsFuturate` below, which uses `futureHistoryBase`. -/

/-- Roberts's imperative character `¡` (@cite{roberts-2023} (54)/(67)).
    Bundles the addressee, the prejacent property, and the
    teleological-flavor parameters. -/
structure ImperativeCharacter (W : Type*) where
  /-- The addressee (target of the directive). -/
  addressee : Nat
  /-- The prejacent: VP denotation. -/
  prejacent : W → Prop
  /-- Modal parameters: futurate circumstantial modal base + goal-based
      ordering source, packaged as a `TeleologicalFlavor`. -/
  flavor : TeleologicalFlavor W

/-- Necessity reading of the imperative character: the prejacent holds
    at every applicable circumstance (= every best world under the
    teleological flavor). Eq. (54)/(67) flattened to a world index. -/
def ImperativeCharacter.realize {W : Type*}
    (ic : ImperativeCharacter W) (w : W) : Prop :=
  ic.flavor.toKratzerParams.necessity ic.prejacent w

/-! ## §4 Conservativity Presupposition

Eq. (65), after @cite{kaufmann-2012}: an imperative subject NP must
live on the addressee set. Stated as a property of the bundle. -/

/-- Conservativity presupposition: the subject's quantificational
    domain is a subset of the addressee set. -/
def ImperativeCharacter.conservativeOn {W : Type*}
    (_ic : ImperativeCharacter W) (domain addressees : List Nat) : Prop :=
  ∀ e ∈ domain, e ∈ addressees

/-! ## §3 Architectural commitments

Roberts's central architectural claim is that the deontic flavor of
imperatives is **pragmatic** — it lives in the preferential POSW
component (the addressee's goals/plans), not in the LF as a deontic
modal. This is precisely the @cite{portner-2018} `POSWTarget`
assignment for `IllocutionaryMood.imperative`, derived (not
restipulated) here. -/

/-- **Roberts's architectural commitment**, derived from
    @cite{portner-2018}'s `HasPOSWTarget IllocutionaryMood`
    instance: the imperative targets the preferential POSW
    component (= the addressee's preference structure), not the
    informational component (= CG).

    This is the type-level shadow of "deontic force is pragmatic,
    not LF": deontic-style content lives where the preference
    component does, and the imperative refines that component
    (via `POSW.star` / `Scoreboard.directionUpdate`) rather than
    the informational one. -/
theorem imperative_targets_preferential :
    HasPOSWTarget.target IllocutionaryMood.imperative = .preferential := rfl

/-- **Pragmatic-deontic routing** (@cite{roberts-2023} §3, headline claim).

    Directing `p` to addressee `t` routes the deontic content through
    the **preferential** component of the projected POSW: every
    prejacent-violator `w` (`¬ p w`) is demoted relative to every
    prejacent-satisfier `v` (`p v`) in the preference order
    (`¬ (· ).toPOSW.le w v`).

    The dual negative claim — that the **informational** component
    (CG) is untouched — is `Scoreboard.direction_preserves_cg` (a
    `@[simp]` lemma). The two together discharge Roberts's claim
    that deontic content arises pragmatically via the preference
    structure rather than via assertion to common ground.

    The hypothesis `hin : t < K.goals.length` is the substrate
    counterpart of Roberts's conservativity presupposition (eq. (65)):
    the addressee must be a real participant for the directive to
    have its preferential effect. Composes
    `Scoreboard.direction_demotes_violators` (the substrate theorem
    that does the work) with the POSWTarget assignment
    `imperative_targets_preferential` (the architectural commitment
    that this preference-side change *is* the deontic content). -/
theorem pragmatic_deontic_routing
    {W : Type*} (K : Scoreboard W) (p : W → Prop) (s t pr : Nat)
    (hin : t < K.goals.length) {w v : W} (hpv : p v) (hpw : ¬ p w) :
    ¬ (K.directionUpdate p s t pr).toPOSW.le w v :=
  Scoreboard.direction_demotes_violators K p s t pr hin w v hpv hpw

/-! ## §1 Desideratum (h): Futurate Flavor

Restated against `futureHistoryBase` (the canonical Condoravdi/CIR
substrate in `Core.Modality.HistoricalAlternatives`) rather than a
local `FUT` enumeration. -/

/-- **(h) Futurate flavor** (@cite{roberts-2023} Table 1, §1, exx.
    33–35). Every circumstance in the future-history base of
    ⟨w, t⟩ has a strictly later time than t. Direct consequence of
    `futureHistoryBase`'s definition. -/
theorem futurate {W T : Type*} [LT T]
    (history : WorldHistory W T)
    (s s' : WorldTimeIndex W T) (h : s' ∈ futureHistoryBase history s) :
    s.time < s'.time := h.2

/-! ## §2.2 Force Linking — integration tests

These are smoke tests that the `IllocutionaryMood` infrastructure
agrees with Roberts's IFLP and her sincerity-condition triad.
Each `rfl` is a structural check that the `Scoreboard` enum
assignment matches the paper. -/

/-- The IFLP round-trips for all three core moods. -/
theorem iflp_roundtrip :
    forceLinkingPrinciple (defaultSemanticType .declarative) = .declarative ∧
    forceLinkingPrinciple (defaultSemanticType .interrogative) = .interrogative ∧
    forceLinkingPrinciple (defaultSemanticType .imperative) = .imperative :=
  ⟨rfl, rfl, rfl⟩

/-- Sincerity conditions: assertion expresses belief; interrogation
    and direction both express desire. -/
theorem sincerity_triad :
    sincerityCondition .declarative = .belief ∧
    sincerityCondition .interrogative = .desire ∧
    sincerityCondition .imperative = .desire := ⟨rfl, rfl, rfl⟩

/-- Direction-of-fit triad: assertion is mind-to-world, interrogation
    and direction are world-to-mind. -/
theorem direction_of_fit_triad :
    (sincerityCondition .declarative).directionOfFit = .mindToWorld ∧
    (sincerityCondition .interrogative).directionOfFit = .worldToMind ∧
    (sincerityCondition .imperative).directionOfFit = .worldToMind :=
  ⟨rfl, rfl, rfl⟩

/-! ## §5 Comparison with @cite{kaufmann-2012} / @cite{ruytenbeek-etal-2017}

Roberts's central disagreement with @cite{kaufmann-2012}: the
imperative's **prejacent-internal** modal flavor is teleological
(circumstantial + goals), not deontic. @cite{ruytenbeek-etal-2017}
adopt Kaufmann's position: their `SentType.imperative.modalFlavor =
some .deontic` (`RuytenbeekEtAl2017.lean` line 102) and their
`directiveCompatible` test fires only on `.deontic` flavor. This
is a *substantive* disagreement, not a naming dispute: the two
accounts make opposite predictions about whether circumstantial
declaratives ("Il est possible de VP" with goal-relevance) should
pattern with imperatives in directive force. -/

/-- The flavor Roberts assigns to the imperative's prejacent-internal
    modal: teleological/circumstantial. -/
def robertsImperativeFlavor : Core.Modality.ModalFlavor :=
  TeleologicalFlavor.flavorTag

/-- **Cross-paper disagreement** — @cite{ruytenbeek-etal-2017} Study 2
    encodes the @cite{kaufmann-2012} position by stipulating
    `SentType.imperative.modalFlavor = some .deontic`. Roberts's
    account predicts `.circumstantial`. The two prejacent-internal
    flavors are distinct. -/
theorem disagrees_with_ruytenbeek_imperative_flavor :
    some robertsImperativeFlavor ≠
    RuytenbeekEtAl2017.SentType.imperative.modalFlavor := by decide

/-- **Cross-paper disagreement** — Roberts's flavor for the imperative
    prejacent fails @cite{ruytenbeek-etal-2017}'s mechanism-1
    `directiveCompatible` test (which checks deontic flavor only).
    Under Roberts, an imperative is directive *despite* not having
    deontic flavor in its prejacent — the directive force comes from
    the `POSW.star` update on the addressee's preference structure
    (see `pragmatic_deontic_routing`), not from the prejacent's
    flavor matching the imperative's. -/
theorem roberts_fails_ruytenbeek_mechanism_one :
    ¬ RuytenbeekEtAl2017.directiveCompatible robertsImperativeFlavor := by decide

/-- @cite{kaufmann-2012}'s position is exposed in
    `Theories/Semantics/Modality/Assert.lean` as
    `primaryFlavor .imperative = .deontic`. Roberts disagrees. -/
theorem disagrees_with_assert :
    robertsImperativeFlavor ≠
    Semantics.Modality.Assert.primaryFlavor .imperative := by decide

/-- **Empirical wedge** — `possibleDecl` ("Il est possible de VP") is
    the construction where Roberts and Ruytenbeek/Kaufmann's mechanism 1
    make opposite predictions. `RuytenbeekEtAl2017.lean` encodes its
    flavor as `.circumstantial`; under Roberts the imperative prejacent
    is *also* `.circumstantial`, so Roberts groups them together by
    prejacent flavor while Ruytenbeek's mechanism 1 (`directiveCompatible
    flavor ↔ flavor = .deontic`) does not.

    `canDeclarative` was originally part of this wedge but was removed
    after the 2026-04-24 audit ground-truthed Ruytenbeek p.58 Discussion:
    *Vous pouvez VP*'s most salient reading is permission (deontic
    possibility), not ability (circumstantial). With that fix the two
    accounts now agree that `canDeclarative` is mechanism-1-licensed
    (Ruytenbeek) / not-flavor-shared-with-imperative (Roberts), so the
    wedge collapses for that construction.

    The `canYouInterrog` and `possibleInterrog` findings (Study 1) do
    not discriminate the accounts either: Ruytenbeek's mechanism 2
    (preparatory-condition questioning) handles them, and Roberts would
    derive the same pattern from pragmatic-deontic routing on the
    addressee's preference structure. Only `possibleDecl` — a
    declarative with no preparatory-condition queried and no
    flavor-share-with-imperative under Ruytenbeek — remains as a
    discriminating case. -/
theorem empirical_wedge_possible_declarative :
    RuytenbeekEtAl2017.SentType.possibleDecl.modalFlavor =
      some robertsImperativeFlavor ∧
    ¬ RuytenbeekEtAl2017.SentType.possibleDecl.directiveCompatibleMech1 ∧
    ¬ RuytenbeekEtAl2017.SentType.possibleDecl.directiveCompatibleMech2 :=
  ⟨rfl, by decide, by decide⟩

/-! ## Worked Examples

These instantiate `ImperativeCharacter` with the local 4-world toy
type `World := Fin 4` defined above. -/

/-- Example: "Move!" (@cite{roberts-2023} (55), worked derivation).
    Trivial case — empty modal base and ordering, prejacent always
    holds. -/
def moveExample : ImperativeCharacter World where
  addressee := 0
  prejacent := λ _ => True
  flavor := ⟨emptyBackground, emptyBackground⟩

theorem move_trivial : ∀ w, moveExample.realize w := by
  intro w
  show necessity _ _ _ _
  rw [necessity_iff_all]
  intro _ _; trivial

/-- Example: "Nobody move!" (@cite{roberts-2023} (42), attributed to
    @cite{veltman-2018}). Negation is **internal** (predicate-term
    negation `¬MOVE`), not external (`¬□`) — propositional negation
    cannot scope over a property. -/
def nobodyMoveExample : ImperativeCharacter World where
  addressee := 0
  prejacent := λ _ => False
  flavor := ⟨emptyBackground, emptyBackground⟩

private theorem empty_best (w : World) :
    w ∈ bestWorlds (W := World) emptyBackground emptyBackground w := by
  have hAcc : w ∈ accessibleWorlds (emptyBackground (W := World)) w := by
    rw [empty_base_universal_access]; exact Set.mem_univ _
  exact ⟨hAcc, fun _ _ q hq _ => by simp [emptyBackground] at hq⟩

theorem nobody_move_total_prohibition :
    ∀ w, ¬ nobodyMoveExample.realize w := by
  intro w h
  have h' : necessity (W := World) emptyBackground emptyBackground (λ _ => False) w := h
  rw [necessity_iff_all] at h'
  exact h' w (empty_best w)

/-! ## §1 (38) Weak imperatives — suggestions and advice

Suggestions like "Hire an attorney" carry weaker modal force than
commands. The mood and semantic type are unchanged; the force
difference lives in the **ordering source**, where the prejacent
itself serves as a secondary ordering criterion (yielding weak
necessity in the sense of @cite{von-fintel-iatridou-2008}, which
linglib formalizes in `Theories/Semantics/Modality/Directive.lean`). -/

open Semantics.Modality.Directive in
/-- Weak (suggestion/advice) reading of an imperative character: weak
    necessity under the primary teleological ordering plus a
    secondary ordering favoring the prejacent. -/
def ImperativeCharacter.weakRealize {W : Type*}
    (ic : ImperativeCharacter W) (secondaryGoals : OrderingSource W)
    (w : W) : Prop :=
  weakNecessity ic.flavor.circumstances ic.flavor.goals secondaryGoals
    ic.prejacent w

open Semantics.Modality.Directive in
/-- Commands entail suggestions: strong necessity entails weak
    necessity (`Directive.strong_entails_weak`), so a command-strength
    imperative a fortiori realizes the suggestion. -/
theorem strong_imperative_entails_suggestion {W : Type*}
    (ic : ImperativeCharacter W) (secondaryGoals : OrderingSource W) (w : W)
    (h : ic.realize w) :
    ic.weakRealize secondaryGoals w :=
  strong_entails_weak ic.flavor.circumstances ic.flavor.goals secondaryGoals
    ic.prejacent w h

/-- Example: "Have a cookie." (@cite{roberts-2023} §2.2, (60)).
    Invitation, not command — the hostess proposes the goal of
    eating a cookie; the guest may decline. Modeled as weak
    necessity over an empty primary ordering, with a secondary
    ordering favoring cookie-eating worlds. -/
def haveCookieExample : ImperativeCharacter World where
  addressee := 0
  prejacent := λ w => w = (0 : World)
  flavor := ⟨emptyBackground, emptyBackground⟩

theorem cookie_not_command :
    ¬ haveCookieExample.realize (1 : World) := by
  intro h
  have h' : necessity (W := World) emptyBackground emptyBackground
      (λ w => w = (0 : World)) (1 : World) := h
  rw [necessity_iff_all] at h'
  exact absurd (h' (1 : World) (empty_best (1 : World))) (by decide)

open Semantics.Modality.Directive in
theorem cookie_is_suggestion :
    haveCookieExample.weakRealize
      (λ _ => [λ w => w = (0 : World)]) (0 : World) := by
  show necessity _ _ _ _
  rw [necessity_iff_all]
  intro w hw
  by_contra hne
  rcases hw with ⟨_, hBest⟩
  have hw0Acc : (0 : World) ∈ accessibleWorlds (emptyBackground (W := World)) (0 : World) := by
    rw [empty_base_universal_access]; exact Set.mem_univ _
  have hgoal : (λ w' : World => w' = (0 : World)) (0 : World) := rfl
  have hweq : w = (0 : World) := hBest (0 : World) hw0Acc (λ w' : World => w' = (0 : World))
    (by simp [combineOrdering]) hgoal
  exact hne hweq

end Roberts2023
