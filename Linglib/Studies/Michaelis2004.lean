/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.ConstructionGrammar.Composition
import Linglib.Features.Aktionsart

/-!
# [michaelis-2004]: Type Shifting in Construction Grammar

Aspectual coercion without interpolated coercion operators: constructions
denote semantic types, and the override principle — "if a lexical item is
semantically incompatible with its morphosyntactic context, the meaning
of the lexical item conforms to the meaning of the structure in which it
is embedded" ((20)) — resolves mismatches in favor of the construction.
Concord constructions denote the type they select ((27)); shift
constructions denote a different one ((28)); both perform implicit
type-shifting via the override, and only shift constructions shift
explicitly (Table 3).

## Main declarations

- `Michaelis2004.inchoativeAddition`, `onsetSelection`,
  `conformToActivity`: the reconciliation operators
- `Michaelis2004.frameAdverbial` (concord, Figure 5) and
  `Michaelis2004.progressive` (shift, Figure 6), meaning poles their
  composition rules
- `Michaelis2004.frame_adverbial_activity_ambiguity`: the two readings of
  ex. (41), derived from the two operators
- `Michaelis2004.progressive_stativizes`: progressive predications denote
  states whatever the complement's Aktionsart
-/

namespace Michaelis2004

open ConstructionGrammar
open Features

/-! ### Reconciliation operators

The override principle repairs a type mismatch by one of the paper's
reconciliation operations on the input's aspectual representation. -/

/-- The addition operator under inchoative construal (§5.1.2): a change
is added to the causal representation, so a state yields the achievement
of its onset — "They were bored in a minute" denotes the onset of
boredom — and an activity a bounded accomplishment. Other types are left
as they are. -/
def inchoativeAddition (p : AspectualProfile) : AspectualProfile :=
  if p.dynamicity = .stative then achievementProfile
  else if p = activityProfile then accomplishmentProfile
  else p

/-- The selection operator (§5.1.2): the onset phase of a durative
situation is selected, an achievement — ex. (41)'s reading on which the
frame measures the delay before the program began to air. -/
def onsetSelection (p : AspectualProfile) : AspectualProfile :=
  if p.duration = .durative then achievementProfile else p

/-- The reconciliation operators available to the frame adverbial. -/
def reconciliation : List (AspectualProfile → AspectualProfile) :=
  [inchoativeAddition, onsetSelection]

/-- The progressive's complement is inherently processual (§5.2.1): the
override conforms any input to the activity type — states via the
addition of `hold` and an effector to their causal representation, telic
events via their processual construal. -/
def conformToActivity : AspectualProfile → AspectualProfile :=
  fun _ => activityProfile

/-! ### The frame adverbial construction (Figure 5, concord) -/

/-- The frame adverbial's composition rule: the `within` frame demands a
telic event and the construct denotes that same type. -/
def frameAdverbialRule : CompositionRule AspectualProfile
  | [p] => if p.telicity = .telic then some p else none
  | _ => none

/-- The frame adverbial construction (Figure 5): an *in*-headed adjunct
added to the verbal valence. -/
def frameAdverbial : Construction (CompositionRule AspectualProfile) :=
  { name := "Frame adverbial"
  , form :=
      [ { filler := .open_ .VERB, isHead := true }
      , { filler := .fixed "in" }
      , { filler := .open_ .NOUN } ]
  , meaning := frameAdverbialRule }

/-! ### The progressive construction (Figure 6, shift) -/

/-- The progressive's composition rule: an activity complement yields the
state holding during the activity's interval, by selection of an
intermediate rest in its temporal representation. -/
def progressiveRule : CompositionRule AspectualProfile
  | [p] => if p = activityProfile then some stateProfile else none
  | _ => none

/-- The progressive construction (Figure 6): auxiliary *be* with a
participial complement whose subject unifies with the auxiliary's — an
instance of [kay-fillmore-1999]'s coinstantiation construction. -/
def progressive : Construction (CompositionRule AspectualProfile) :=
  { name := "Progressive"
  , form :=
      [ { filler := .open_ .NOUN, gf := some .subj, refIdx := some 1 }
      , { filler := .headed "be" .AUX, isHead := true }
      , { filler := .open_ .VERB, gf := some .comp, refIdx := some 1 } ]
  , meaning := progressiveRule }

/-- Figure 6's raising property: the subject of *be* and the complement's
subject form one coreference group, the coinstantiation pattern. -/
theorem progressive_coinstantiation : refGroupCount progressive.form = 1 := by
  decide

/-! ### Concord vs. shift ((27), (28)) -/

/-- A unary rule preserves type when its output type is its input's —
(27)'s concord constructions; (28)'s shift constructions fail it. -/
def PreservesType (r : CompositionRule AspectualProfile) : Prop :=
  ∀ p q, r [p] = some q → q = p

/-- The frame adverbial is a concord construction: it denotes the telic
event type it selects. -/
theorem frameAdverbial_concord : PreservesType frameAdverbialRule := by
  intro p q h
  simp only [frameAdverbialRule] at h
  split at h
  · exact (Option.some_inj.mp h).symm
  · exact absurd h (by simp)

/-- The progressive is a shift construction: it selects activities but
denotes states. -/
theorem progressive_shift : ¬ PreservesType progressiveRule := fun h =>
  absurd (h activityProfile stateProfile (by decide)) (by decide)

/-! ### Frame-adverbial predictions (§5.1.2) -/

/-- "She solved the problem in ten minutes" (Figure 5's instantiation): a
telic complement composes directly, with no coercion ambiguity. -/
theorem frame_adverbial_instantiation :
    frameAdverbialRule.override reconciliation [accomplishmentProfile]
      = [accomplishmentProfile] :=
  CompositionRule.override_eq_of_eq_some _ (by decide)

/-- Ex. (30), "They were bored in a minute": the stative input conforms
by inchoative construal — the onset of boredom, an achievement. -/
theorem frame_adverbial_coerces_state :
    frameAdverbialRule.override reconciliation [stateProfile]
      = [achievementProfile] := by decide

/-- Ex. (41), "My radio program ran in less than four minutes": an
activity input is genuinely ambiguous — inchoative addition yields the
accomplishment reading (the frame measures the running time), onset
selection the achievement reading (the frame measures the delay before
airing) — [de-swart-1998]'s observation, derived from the operator
inventory. -/
theorem frame_adverbial_activity_ambiguity :
    frameAdverbialRule.override reconciliation [activityProfile]
      = [accomplishmentProfile, achievementProfile] := by decide

/-! ### Progressive predictions (§5.2.1) -/

/-- "We were playing cards" (Figure 6's explicit shift): an activity
complement yields a state directly. -/
theorem progressive_explicit :
    progressiveRule [activityProfile] = some stateProfile := by decide

/-- Exx. (31), (42)–(44), "We were living in Boulder": a stative
complement conforms to the activity type and the predication is again a
state — the "temporary state" reading. -/
theorem progressive_coerces_state :
    progressiveRule.override [conformToActivity] [stateProfile]
      = [stateProfile] := by decide

/-- "They were baking a cake": a telic complement is construed as its
process, so the culmination is not entailed. -/
theorem progressive_coerces_telic :
    progressiveRule.override [conformToActivity] [accomplishmentProfile]
      = [stateProfile] := by decide

/-- Progressive predications denote states whatever the Aktionsart of the
complement (§5.2.1): the apparent paradox of a stativizing construction
accepting stative input dissolves under the override. -/
theorem progressive_stativizes (p : AspectualProfile) :
    progressiveRule.override [conformToActivity] [p] = [stateProfile] := by
  obtain ⟨t, d, dyn⟩ := p
  cases t <;> cases d <;> cases dyn <;> decide

end Michaelis2004
