module

public import Linglib.Syntax.CCG.Derivation
public import Linglib.Phonology.Prosody.Intonation
public import Linglib.Core.Order.PartialUnify
public import Mathlib.Tactic.DeriveFintype

/-!
# CCG intonation and information structure

Steedman aligns prosodic structure with CCG derivations through an INFORMATION feature, theme or
rheme, that pitch accents mark on words and that combination unifies up the derivation. CCG's
spurious ambiguity is the engine: alternative derivations of one string are alternative
information structures, disambiguated by intonation, so "Anna married Manny" derives both
[Anna][married Manny] and, by composition, [Anna married][Manny], and the theme tune on
"ANNA married" selects the latter. Because a `ProsodicPhrase` carries a `Derivation`, only CCG
constituents can be prosodic phrases, which is Selkirk's Sense Unit Condition by construction.

## Main definitions

* `CCG.Intonation.InfoFeature`: the INFORMATION feature, with `InfoFeature.unify` its partial
  join, a `PartialUnify` instance.
* `CCG.Intonation.accentInfo`: the marking an accent slot contributes.
* `CCG.Derivation.infoFeature`: the feature a derivation projects under an accent assignment,
  `none` on a theme/rheme clash.
* `CCG.Intonation.Tune`, `CCG.Intonation.themeTune`, `CCG.Intonation.rhemeTune`: pitch accent
  plus terminal contour.
* `CCG.Intonation.ProsodicPhrase`, `CCG.Intonation.extractInfoStructure`: tune-marked
  constituents and the theme/rheme partition of an utterance.

## Implementation notes

The prosodic vocabulary comes from `Prosody`'s autosegmental-metrical types. Relating these
phrases to the phonology-side prosodic hierarchy (`Phonology/Prosody/Phrase`) is left to
study-level work.

## References

* [steedman-2000]
* [selkirk-1984]
* [pierrehumbert-hirschberg-1990]
* [carpenter-1992]
* [kuroda-1972]
-/

@[expose] public section

namespace CCG.Intonation

open CCG
open Prosody

/-! ### The INFORMATION feature -/

/-- The INFORMATION feature of [steedman-2000]. -/
inductive InfoFeature where
  /-- Theme. -/
  | θ
  /-- Rheme. -/
  | ρ
  /-- Unspecified, unifying with either theme or rheme. -/
  | unmarked
  /-- Phrasal, after a boundary has applied. -/
  | φ
  deriving Repr, DecidableEq, Inhabited, Fintype

/-- The unification of two info features, their partial join in the subsumption order below
(`PartialUnify`). -/
def InfoFeature.unify : InfoFeature → InfoFeature → WithTop InfoFeature
  | .unmarked, f => f
  | f, .unmarked => f
  | .θ, .θ => (.θ : InfoFeature)
  | .ρ, .ρ => (.ρ : InfoFeature)
  | .φ, .φ => (.φ : InfoFeature)
  | _, _ => ⊤

/-! ### The information feature as a subsumption order

`unmarked` is Steedman's underspecified feature — the category that "can unify with
either" theme or rheme — so it is `⊥`; `θ`, `ρ`, `φ` are pairwise-incomparable atoms
above it. This is the flat order of feature unification ([carpenter-1992]) carried on
the information feature: `InfoFeature.unify` is its partial join (`PartialUnify`) and
the total meet is generalization (anti-unification). -/

instance : LE InfoFeature where
  le a b := a = .unmarked ∨ a = b

theorem InfoFeature.le_def {a b : InfoFeature} :
    a ≤ b ↔ a = .unmarked ∨ a = b := Iff.rfl

instance (a b : InfoFeature) : Decidable (a ≤ b) :=
  decidable_of_iff _ InfoFeature.le_def.symm

instance : PartialOrder InfoFeature where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : OrderBot InfoFeature where
  bot := .unmarked
  bot_le := by decide

instance : Min InfoFeature where
  min a b := if a = b then a else .unmarked

instance : SemilatticeInf InfoFeature :=
  { (inferInstance : PartialOrder InfoFeature), (inferInstance : Min InfoFeature) with
    inf := min
    inf_le_left := by decide
    inf_le_right := by decide
    le_inf := by decide }

/-- The two `PartialUnify` axioms in decidable form. A successful unification is the least
upper bound, and unification succeeds on bounded-above pairs. -/
private theorem InfoFeature.unify_spec (a b : InfoFeature) :
    (∀ c : InfoFeature, InfoFeature.unify a b = ↑c →
        (a ≤ c ∧ b ≤ c) ∧ ∀ u, a ≤ u → b ≤ u → c ≤ u) ∧
      ((∃ u, a ≤ u ∧ b ≤ u) → InfoFeature.unify a b ≠ ⊤) := by
  revert a b; decide

instance : PartialUnify InfoFeature where
  unify := InfoFeature.unify
  isLUB_of_unify_eq_coe {a b c} h := by
    obtain ⟨⟨hac, hbc⟩, hmin⟩ := (InfoFeature.unify_spec a b).1 c h
    refine ⟨mem_upperBounds_pair.mpr ⟨hac, hbc⟩, fun u hu ↦ ?_⟩
    obtain ⟨hau, hbu⟩ := mem_upperBounds_pair.mp hu
    exact hmin u hau hbu
  unify_ne_top_of_bddAbove {a b} h := by
    obtain ⟨u, hu⟩ := h
    obtain ⟨hau, hbu⟩ := mem_upperBounds_pair.mp hu
    exact (InfoFeature.unify_spec a b).2 ⟨u, hau, hbu⟩

/-! ### Projecting information structure through a derivation -/

/-- The information marking an accent slot contributes. In [steedman-2000] L+H* marks the
theme, unaccented material is unmarked, and H* and the remaining accents mark the rheme. -/
def accentInfo : Option PitchAccent → InfoFeature
  | some (.leading .L .H) => .θ
  | none => .unmarked
  | some _ => .ρ

/-- An assignment of pitch accents to the tokens of a derivation, `none` for an unaccented
token. -/
def AccentAssignment (T : Type*) := T → Option PitchAccent

/-- The INFORMATION feature a derivation projects under an accent assignment. Leaves contribute
the `accentInfo` of their accent and combination unifies the daughters' features, with `none` on
a theme/rheme clash, the prosodic analogue of `Derivation.interp`'s reading of the same tree. -/
def _root_.CCG.Derivation.infoFeature {T α : Type*} {R : RuleSystem α}
    (acc : AccentAssignment T) : {c : Cat α} → Derivation T R c → Option InfoFeature
  | _, .lex f _ => some (accentInfo (acc f))
  | _, .node _ d₁ d₂ => do (← d₁.infoFeature acc).unify (← d₂.infoFeature acc)

/-! ### Tunes and prosodic phrases -/

/-- An intonational tune is a pitch accent plus a terminal contour. Of the two main tunes of
English in [steedman-2000], L+H* LH% marks the theme and H* LL% the rheme. -/
structure Tune where
  /-- The pitch accent. -/
  accent : PitchAccent
  /-- The phrase accent and boundary tone. -/
  terminal : TerminalContour
  deriving Repr, DecidableEq

/-- The theme tune, L+H* with the rise LH%. -/
def themeTune : Tune := ⟨.leading .L .H, ⟨.L, .H⟩⟩

/-- The rheme tune, H* with the fall LL%. -/
def rhemeTune : Tune := ⟨.mono .H, ⟨.L, .L⟩⟩

/-- A prosodic phrase is a tune-marked CCG constituent. Because `deriv` is a derivation, only
constituents can be phrases, the Sense Unit Condition of [selkirk-1984] by construction. -/
structure ProsodicPhrase (T : Type*) {α : Type*} (R : RuleSystem α) where
  /-- The category of the constituent. -/
  cat : Cat α
  /-- The constituent's derivation. -/
  deriv : Derivation T R cat
  /-- The tune the phrase carries. -/
  tune : Tune

/-- An information-structure analysis is a theme/rheme partition, following [steedman-2000].
The theme is what the utterance is about (the λ-abstract presupposing a QUD, marked in English by
the L+H* LH% tune per [pierrehumbert-hirschberg-1990]) and the rheme is what is asserted about it
(marked H* LL%). `theme := none` encodes an all-rheme structure, thetic in [kuroda-1972]'s sense,
with no theme constituent. -/
structure InfoStructure (P : Type*) where
  /-- The theme (λ-abstract, presupposed QUD); `none` for all-rheme
  (thetic) structures. -/
  theme : Option P
  /-- The rheme (comment, answer, assertion). -/
  rheme : P
  /-- Focused elements (evoking alternatives). -/
  foci : List P := []
  /-- Background elements (given). -/
  background : List P := []

/-- The information structure of a sequence of prosodic phrases takes the phrase with the theme
tune as theme and the phrase with the rheme tune as rheme, and a theme-less utterance is
all-rheme. It is `none` when the phrases yield no coherent partition. -/
def extractInfoStructure {T α : Type*} {R : RuleSystem α} (phrases : List (ProsodicPhrase T R)) :
    Option (InfoStructure (ProsodicPhrase T R)) :=
  let themes := phrases.filter (·.tune == themeTune)
  let rhemes := phrases.filter (·.tune == rhemeTune)
  match themes, rhemes with
  | [t], [r] => some { theme := some t, rheme := r }
  | [], [r] => some { theme := none, rheme := r }
  | _, _ => none

end CCG.Intonation
