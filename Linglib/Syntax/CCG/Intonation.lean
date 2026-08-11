import Linglib.Syntax.CCG.Derivation
import Linglib.Features.Prosody
import Linglib.Core.Order.PartialUnify
import Mathlib.Tactic.DeriveFintype

/-!
# CCG Intonation and Information Structure

This file defines [steedman-2000]'s alignment of prosodic structure with CCG
derivations: the INFORMATION feature (theme/rheme) as a unification lattice, the
projection of that feature through a derivation from its leaves' pitch accents, and
prosodic phrases as tune-marked constituents.

CCG's "spurious ambiguity" is the engine: alternative derivations of one string are
alternative information structures, disambiguated by intonation — "Anna married
Manny" derives both [Anna][married Manny] and, via composition, [Anna married]
[Manny], and the theme tune on "ANNA married" selects the latter. Because a
`ProsodicPhrase` carries an intrinsically typed `Derivation`, only CCG constituents
can be prosodic phrases — [selkirk-1984]'s Sense Unit Condition holds by
construction ([steedman-2000] ch. 2).

## Main definitions

* `InfoFeature`: the INFORMATION feature — theme `θ`, rheme `ρ`, `unmarked` (the `⊥`
  of a flat subsumption order), and phrasal `φ`; `InfoFeature.unify` is its partial
  join, a `PartialUnify` instance.
* `accentInfo`: the marking a pitch accent contributes (L+H* ⇒ `θ`, null ⇒
  `unmarked`, other accents ⇒ `ρ`).
* `Derivation.infoFeature`: the feature a derivation projects under an accent
  assignment for its leaf forms — combination unifies, type-raising preserves;
  `none` on a theme/rheme clash.
* `Tune`, `themeTune`, `rhemeTune`: pitch accent plus terminal contour.
* `ProsodicPhrase`, `extractInfoStructure`: tune-marked constituents and the
  theme/rheme partition of an utterance ([pierrehumbert-hirschberg-1990]).

## Implementation notes

The prosodic vocabulary comes from `Features.Prosody`'s autosegmental-metrical types.
Relating these phrases to the phonology-side prosodic hierarchy
(`Phonology/Prosody/Phrase`) is left to future study-level work.
-/

namespace CCG.Intonation

open CCG
open Features.Prosody

/-! ### The INFORMATION feature -/

inductive InfoFeature where
  | θ         -- Theme
  | ρ         -- Rheme
  | unmarked  -- Unspecified
  | φ         -- Phrasal (boundary applied)
  deriving Repr, DecidableEq, Inhabited, Fintype

/-- Unify two info features: the partial join in the subsumption order below
(`PartialUnify`). -/
def InfoFeature.unify : InfoFeature → InfoFeature → Option InfoFeature
  | .unmarked, f => some f
  | f, .unmarked => some f
  | .θ, .θ => some .θ
  | .ρ, .ρ => some .ρ
  | .φ, .φ => some .φ
  | _, _ => none

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

/-- The two `PartialUnify` axioms in decidable form: a successful unification is the
least upper bound, and unification succeeds on bounded-above pairs. -/
private theorem InfoFeature.unify_spec (a b : InfoFeature) :
    (∀ c, InfoFeature.unify a b = some c →
        (a ≤ c ∧ b ≤ c) ∧ ∀ u, a ≤ u → b ≤ u → c ≤ u) ∧
      ((∃ u, a ≤ u ∧ b ≤ u) → (InfoFeature.unify a b).isSome) := by
  revert a b; decide

instance : PartialUnify InfoFeature where
  unify := InfoFeature.unify
  isLUB_of_unify_eq_some {a b c} h := by
    obtain ⟨⟨hac, hbc⟩, hmin⟩ := (InfoFeature.unify_spec a b).1 c h
    refine ⟨PartialUnify.mem_upperBounds_pair.mpr ⟨hac, hbc⟩, fun u hu => ?_⟩
    obtain ⟨hau, hbu⟩ := PartialUnify.mem_upperBounds_pair.mp hu
    exact hmin u hau hbu
  isSome_unify_of_bddAbove {a b} h := by
    obtain ⟨u, hu⟩ := h
    obtain ⟨hau, hbu⟩ := PartialUnify.mem_upperBounds_pair.mp hu
    exact (InfoFeature.unify_spec a b).2 ⟨u, hau, hbu⟩

/-! ### Projecting information structure through a derivation -/

/-- The information marking a pitch accent contributes ([steedman-2000]: L+H* marks
the theme, unaccented material is unmarked, and H* with the remaining accents mark
the rheme). -/
def accentInfo : PitchAccent → InfoFeature
  | .L_plus_H_star => .θ
  | .null => .unmarked
  | _ => .ρ

/-- An assignment of pitch accents to the leaf forms of a derivation. -/
def AccentAssignment := String → PitchAccent

/-- The INFORMATION feature a derivation projects under an accent assignment: leaves
contribute `accentInfo` of their accent, combination unifies the daughters' features,
and type-raising preserves. `none` on a theme/rheme clash — the prosodic analogue of
`Derivation.interp`'s reading of the same tree. -/
def _root_.CCG.Derivation.infoFeature (acc : AccentAssignment) :
    {c : Cat Atom} → Derivation Atom c → Option InfoFeature
  | _, .lex f _ => some (accentInfo (acc f))
  | _, .node _ d₁ d₂ => do (← d₁.infoFeature acc).unify (← d₂.infoFeature acc)

/-! ### Tunes and prosodic phrases -/

/-- An intonational tune: pitch accent plus terminal contour. The two main tunes of
English ([steedman-2000]): L+H* LH% marks the theme, H* LL% the rheme. -/
structure Tune where
  accent : PitchAccent
  terminal : TerminalContour
  deriving Repr, DecidableEq

/-- The theme tune: L+H* with continuation rise (LH%). -/
def themeTune : Tune := ⟨.L_plus_H_star, .continuation⟩

/-- The rheme tune: H* with declarative fall (LL%). -/
def rhemeTune : Tune := ⟨.H_star, .declarative⟩

/-- A prosodic phrase: a tune-marked CCG constituent. Because `deriv` is an
intrinsically typed derivation, only constituents can be phrases — the Sense Unit
Condition ([selkirk-1984]) by construction. -/
structure ProsodicPhrase where
  cat : Cat Atom
  deriv : Derivation Atom cat
  tune : Tune

/-- An information-structure analysis as a theme/rheme partition,
following [steedman-2000]: the theme is what the utterance is about
(the λ-abstract presupposing a QUD, marked by the L+H* LH% theme tune
in English per [pierrehumbert-hirschberg-1990]); the rheme is what is
asserted about it (marked H* LL%). `theme := none` encodes an
all-rheme (thetic, in [kuroda-1972]'s sense) structure with no theme
constituent. -/
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

/-- Extract the information structure of a sequence of prosodic phrases: the phrase
with the theme tune becomes the theme, the phrase with the rheme tune the rheme, and
a theme-less utterance is all-rheme. `none` when the phrase list yields no coherent
partition. -/
def extractInfoStructure (phrases : List ProsodicPhrase) :
    Option (InfoStructure ProsodicPhrase) :=
  let themes := phrases.filter (·.tune == themeTune)
  let rhemes := phrases.filter (·.tune == rhemeTune)
  match themes, rhemes with
  | [t], [r] => some { theme := some t, rheme := r }
  | [], [r] => some { theme := none, rheme := r }
  | _, _ => none

end CCG.Intonation
