import Linglib.Semantics.Aspect.Defs
import Linglib.Semantics.Aspect.Viewpoint

/-!
# Smith (1997): The Parameter of Aspect

This file formalizes the two-component theory of [smith-1997]: aspectual meaning factors into a
situation type (`VendlerClass`) and a viewpoint (`ViewpointType`), independent and freely
combined. The visibility properties of chapter 4 are not stipulated per viewpoint: whether a
viewpoint asserts the initial point or the final point of the situation, presents it as closed,
or focuses an interval inside it are predicates over the substrate's relation between topic
time and situation time, and the chapter's table of what each viewpoint makes visible is
recovered as four theorems (`showsInitialPoint_iff`, `showsFinalPoint_iff`,
`presentsClosed_iff`, `focusesPreliminaryStages_iff`). The perfective makes both endpoints
visible and is closed, the imperfective makes neither visible and is open, and the neutral
viewpoint of section 4.2.3 sits between them, including the initial point and at least one
stage but never the preliminary stages that separate it from the imperfective
(`perfective_closed`, `imperfective_open`, `neutral_intermediate`,
`neutral_no_preliminary_stages`). Section 4.2 records the viewpoint inventories of the four
languages of Part II and the three relations between the perfective and statives
(`Language.system`); the perfective conveys completion for telic and termination for atelic
situation types (`perfectiveEffect`, `completion_iff_telic`); and the imperfective paradox of
section 4.3.2 is the invisibility of a telic situation's final point under a viewpoint that
does not show it (`CompletionInvisible`).

## Implementation notes

* The visibility predicates quantify over every linearly ordered time domain; the negative
  cases are witnessed on the integers.
* The per-language systems are the chapter's claims about which viewpoints a language
  grammaticizes, which viewpoint is dominant in an asymmetric system, and how its perfective
  treats statives. The compositional rules of section 3.3 are not formalized.

## References

* [smith-1997]
* [klein-1994]
-/

open Aspect

namespace Smith1997

/-! ### Visibility, section 4.1 -/

/-- The viewpoint asserts the initial point of the situation. -/
def ShowsInitialPoint (v : ViewpointType) : Prop :=
  ∀ {T : Type} [LinearOrder T] {tt tsit : NonemptyInterval T},
    v.ttTSitRelation tt tsit → tsit.fst ∈ tt

/-- The viewpoint asserts the final point of the situation. -/
def ShowsFinalPoint (v : ViewpointType) : Prop :=
  ∀ {T : Type} [LinearOrder T] {tt tsit : NonemptyInterval T},
    v.ttTSitRelation tt tsit → tsit.snd ∈ tt

/-- The viewpoint presents the situation as closed: the topic time reaches its final point. -/
def PresentsClosed (v : ViewpointType) : Prop :=
  ∀ {T : Type} [LinearOrder T] {tt tsit : NonemptyInterval T},
    v.ttTSitRelation tt tsit → tsit.snd ≤ tt.snd

/-- The viewpoint focuses a topic time strictly inside the situation. -/
def FocusesPreliminaryStages (v : ViewpointType) : Prop :=
  ∀ {T : Type} [LinearOrder T] {tt tsit : NonemptyInterval T},
    v.ttTSitRelation tt tsit → tt < tsit

private theorem rel_imperfective :
    ViewpointType.imperfective.ttTSitRelation (⟨⟨1, 2⟩, by omega⟩ : NonemptyInterval ℤ)
      ⟨⟨0, 3⟩, by omega⟩ := by
  decide

private theorem rel_perfect :
    ViewpointType.perfect.ttTSitRelation (⟨⟨3, 4⟩, by omega⟩ : NonemptyInterval ℤ)
      ⟨⟨0, 2⟩, by omega⟩ := by
  decide

private theorem rel_prospective :
    ViewpointType.prospective.ttTSitRelation (⟨⟨0, 1⟩, by omega⟩ : NonemptyInterval ℤ)
      ⟨⟨2, 3⟩, by omega⟩ := by
  decide

private theorem rel_neutral_short :
    ViewpointType.neutral.ttTSitRelation (⟨⟨0, 1⟩, by omega⟩ : NonemptyInterval ℤ)
      ⟨⟨0, 5⟩, by omega⟩ := by
  decide

private theorem rel_neutral_wide :
    ViewpointType.neutral.ttTSitRelation (⟨⟨0, 10⟩, by omega⟩ : NonemptyInterval ℤ)
      ⟨⟨0, 5⟩, by omega⟩ := by
  decide

private theorem rel_perfective_refl :
    ViewpointType.perfective.ttTSitRelation (⟨⟨0, 1⟩, by omega⟩ : NonemptyInterval ℤ)
      ⟨⟨0, 1⟩, by omega⟩ := by
  decide

/-- The initial point: the perfective and the neutral viewpoint assert it. -/
theorem showsInitialPoint_iff (v : ViewpointType) :
    ShowsInitialPoint v ↔ v = .perfective ∨ v = .neutral := by
  refine ⟨?_, ?_⟩
  · intro h
    cases v with
    | perfective => exact Or.inl rfl
    | neutral => exact Or.inr rfl
    | imperfective =>
        exfalso
        have hC := @h ℤ _ _ _ rel_imperfective
        have : (1 : ℤ) ≤ 0 := hC.1
        omega
    | perfect =>
        exfalso
        have hC := @h ℤ _ _ _ rel_perfect
        have : (3 : ℤ) ≤ 0 := hC.1
        omega
    | prospective =>
        exfalso
        have hC := @h ℤ _ _ _ rel_prospective
        have : (2 : ℤ) ≤ 1 := hC.2
        omega
  · rintro (rfl | rfl)
    · intro _ _ tt tsit h
      exact ⟨h.1, le_trans tsit.fst_le_snd h.2⟩
    · intro _ _ _ _ h
      exact h.2

/-- The final point: only the perfective asserts it. -/
theorem showsFinalPoint_iff (v : ViewpointType) : ShowsFinalPoint v ↔ v = .perfective := by
  refine ⟨?_, ?_⟩
  · intro h
    cases v with
    | perfective => rfl
    | imperfective =>
        exfalso
        have hC := @h ℤ _ _ _ rel_imperfective
        have : (3 : ℤ) ≤ 2 := hC.2
        omega
    | perfect =>
        exfalso
        have hC := @h ℤ _ _ _ rel_perfect
        have : (3 : ℤ) ≤ 2 := hC.1
        omega
    | prospective =>
        exfalso
        have hC := @h ℤ _ _ _ rel_prospective
        have : (3 : ℤ) ≤ 1 := hC.2
        omega
    | neutral =>
        exfalso
        have hC := @h ℤ _ _ _ rel_neutral_short
        have : (5 : ℤ) ≤ 1 := hC.2
        omega
  · rintro rfl
    intro _ _ tt tsit h
    exact ⟨le_trans h.1 tsit.fst_le_snd, h.2⟩

/-- Closure: the perfective and the perfect present the situation as closed. -/
theorem presentsClosed_iff (v : ViewpointType) :
    PresentsClosed v ↔ v = .perfective ∨ v = .perfect := by
  refine ⟨?_, ?_⟩
  · intro h
    cases v with
    | perfective => exact Or.inl rfl
    | perfect => exact Or.inr rfl
    | imperfective =>
        exfalso
        have : (3 : ℤ) ≤ 2 := @h ℤ _ _ _ rel_imperfective
        omega
    | prospective =>
        exfalso
        have : (3 : ℤ) ≤ 1 := @h ℤ _ _ _ rel_prospective
        omega
    | neutral =>
        exfalso
        have : (5 : ℤ) ≤ 1 := @h ℤ _ _ _ rel_neutral_short
        omega
  · rintro (rfl | rfl)
    · intro _ _ _ _ h
      exact h.2
    · intro _ _ tt _ h
      exact le_trans h tt.fst_le_snd

/-- Preliminary stages: only the imperfective places the topic time strictly inside the
situation. -/
theorem focusesPreliminaryStages_iff (v : ViewpointType) :
    FocusesPreliminaryStages v ↔ v = .imperfective := by
  refine ⟨?_, ?_⟩
  · intro h
    cases v with
    | imperfective => rfl
    | perfective =>
        exfalso
        exact lt_irrefl _ (@h ℤ _ _ _ rel_perfective_refl)
    | perfect =>
        exfalso
        have hC := @h ℤ _ _ _ rel_perfect
        have : (4 : ℤ) ≤ 2 := hC.1.2
        omega
    | prospective =>
        exfalso
        have hC := @h ℤ _ _ _ rel_prospective
        have : (2 : ℤ) ≤ 0 := hC.1.1
        omega
    | neutral =>
        exfalso
        have hC := @h ℤ _ _ _ rel_neutral_wide
        have : (10 : ℤ) ≤ 5 := hC.1.2
        omega
  · rintro rfl
    intro _ _ _ _ h
    exact h

/-- The perfective makes both endpoints visible and presents the situation as closed,
section 4.2.1. -/
theorem perfective_closed :
    ShowsInitialPoint .perfective ∧ ShowsFinalPoint .perfective ∧ PresentsClosed .perfective :=
  ⟨(showsInitialPoint_iff _).mpr (Or.inl rfl), (showsFinalPoint_iff _).mpr rfl,
    (presentsClosed_iff _).mpr (Or.inl rfl)⟩

/-- The imperfective makes neither endpoint visible and is open, section 4.2.2. -/
theorem imperfective_open :
    ¬ ShowsInitialPoint .imperfective ∧ ¬ ShowsFinalPoint .imperfective ∧
      ¬ PresentsClosed .imperfective := by
  rw [showsInitialPoint_iff, showsFinalPoint_iff, presentsClosed_iff]
  decide

/-- The neutral viewpoint is intermediate, section 4.2.3: the initial point visible as under the
perfective, the final point unasserted as under the imperfective, and open. -/
theorem neutral_intermediate :
    ShowsInitialPoint .neutral ∧ ¬ ShowsFinalPoint .neutral ∧ ¬ PresentsClosed .neutral := by
  refine ⟨(showsInitialPoint_iff _).mpr (Or.inr rfl), ?_, ?_⟩
  · rw [showsFinalPoint_iff]; decide
  · rw [presentsClosed_iff]; decide

/-- Only the imperfective focuses preliminary stages, the discriminator between the neutral
viewpoint and the imperfective, section 4.2.3, (41). -/
theorem neutral_no_preliminary_stages :
    ¬ FocusesPreliminaryStages .neutral ∧ FocusesPreliminaryStages .imperfective := by
  refine ⟨?_, (focusesPreliminaryStages_iff _).mpr rfl⟩
  rw [focusesPreliminaryStages_iff]; decide

/-- The neutral viewpoint sides with the perfective on the initial point and with the
imperfective on the final point. -/
theorem neutral_between_perf_imperf :
    (ShowsInitialPoint .neutral ↔ ShowsInitialPoint .perfective) ∧
      (ShowsFinalPoint .neutral ↔ ShowsFinalPoint .imperfective) :=
  ⟨iff_of_true neutral_intermediate.1 perfective_closed.1,
    iff_of_false neutral_intermediate.2.1 imperfective_open.2.1⟩

/-! ### The independence of the components, section 4.3 -/

/-- An aspectual interpretation: a situation type and a viewpoint, chosen independently. -/
structure AspectualInterpretation where
  situationType : VendlerClass
  viewpoint : ViewpointType
  deriving DecidableEq

/-- The imperfective paradox, section 4.3.2: the situation type is visible whatever the
viewpoint, so a telic situation's natural endpoint is known though not asserted under a
viewpoint that does not show the final point. -/
def CompletionInvisible (ai : AspectualInterpretation) : Prop :=
  ai.situationType.telicity = .telic ∧ ¬ ShowsFinalPoint ai.viewpoint

/-- Completion is invisible exactly for telic situation types under a non-perfective
viewpoint. -/
theorem completionInvisible_iff (ai : AspectualInterpretation) :
    CompletionInvisible ai ↔ ai.situationType.telicity = .telic ∧ ai.viewpoint ≠ .perfective := by
  rw [CompletionInvisible, showsFinalPoint_iff]

/-- *We were walking to school*, (47): an accomplishment under the imperfective. -/
theorem walking_to_school : CompletionInvisible ⟨.accomplishment, .imperfective⟩ :=
  (completionInvisible_iff _).mpr ⟨rfl, by decide⟩

/-! ### The perfective's final point, section 4.2.1

The perfective presents its situation as closed, and the closed situation is completed or
terminated according to its situation type, (10) and (11). -/

/-- What the perfective conveys of the final point: completion for a telic situation type,
termination for an atelic one, and nothing under another viewpoint. -/
inductive PerfectiveEffect
  | completion | termination | noEffect
  deriving DecidableEq

/-- The perfective effect of an aspectual interpretation. -/
def perfectiveEffect (ai : AspectualInterpretation) : PerfectiveEffect :=
  match ai.viewpoint with
  | .perfective => if ai.situationType.telicity = .telic then .completion else .termination
  | _ => .noEffect

/-- Under the perfective, completion is conveyed exactly by the telic situation types. -/
theorem completion_iff_telic (c : VendlerClass) :
    perfectiveEffect ⟨c, .perfective⟩ = .completion ↔ c.telicity = .telic := by
  cases c <;> decide

/-- The imperfective conveys neither completion nor termination. -/
theorem imperfective_noEffect (c : VendlerClass) :
    perfectiveEffect ⟨c, .imperfective⟩ = .noEffect := rfl

/-! ### The aspectual systems of Part II, section 4.2 -/

/-- The relation between the perfective and statives, section 4.2.1: the perfective includes
the changes into and out of a state and closes it (French); it presents states open or closed
(English); or it does not apply to statives (Russian, Chinese, Navajo). -/
inductive PerfectiveStative
  | closed | openOrClosed | excluded
  deriving DecidableEq

/-- The interaction of viewpoint and situation type, section 4.2: an asymmetric system in
which one viewpoint is limited and the dominant one is available to every situation type, a
system in which every viewpoint is available to every situation type, or one in which
statives lie outside the viewpoint system. -/
inductive Interaction
  | asymmetric (dominant : ViewpointType) | symmetric | nonStativeOnly
  deriving DecidableEq

/-- A language's aspectual system: its viewpoints, their interaction with situation type, and
the treatment of statives by the perfective. -/
structure AspectualSystem where
  viewpoints : List ViewpointType
  interaction : Interaction
  perfectiveStative : PerfectiveStative
  deriving DecidableEq

/-- The four languages of Part II. -/
inductive Language
  | english | french | mandarin | navajo
  deriving DecidableEq

/-- The systems of section 4.2: English has the perfective and the progressive, the perfective
dominant, and presents states open or closed; French has the perfective, the imperfective and
the neutral viewpoint of its Futur, every viewpoint available to every situation type, and
its perfective closes states; Mandarin has perfectives, imperfectives and the neutral
viewpoint of a sentence without a viewpoint morpheme, and Navajo the perfective, the
imperfective and the neutral viewpoint of its Usitative and Iterative, both keeping statives
outside the viewpoint system. -/
def Language.system : Language → AspectualSystem
  | .english => ⟨[.perfective, .imperfective], .asymmetric .perfective, .openOrClosed⟩
  | .french => ⟨[.perfective, .imperfective, .neutral], .symmetric, .closed⟩
  | .mandarin => ⟨[.perfective, .imperfective, .neutral], .nonStativeOnly, .excluded⟩
  | .navajo => ⟨[.perfective, .imperfective, .neutral], .nonStativeOnly, .excluded⟩

/-- A language whose perfective does not apply to statives keeps them outside its viewpoint
system, and conversely. -/
theorem excluded_iff_nonStativeOnly (l : Language) :
    l.system.perfectiveStative = .excluded ↔ l.system.interaction = .nonStativeOnly := by
  cases l <;> decide

end Smith1997
