/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.Construction.Schema
import Linglib.Core.Order.Flat

/-!
# Audring (2019): Mothers or sisters? The encoding of morphological knowledge

This file formalizes [audring-2019]'s division of labour between mother schemas and sister links
in a full-entry lexicon. A generalization over stored words can be encoded by a mother schema
dominating them or by sister links, coindices between the words themselves. A sister link is a
subscripting through which the pair of words factors, so it captures relations of sameness:
*boyish* and *childish* are sisters at the affix (`ish_affix_sisters`) but cannot be coindexed
at the base, where their fillers differ (`not_base_sisters`). The mother `[N -ish]A` of (8)
relates every member of the family through one variable (`ishSchema_relates`), which is what
states that different bases serve the same function. The mother also carries productivity: it
generates *Trumpish* over an empty lexicon (`ishSchema_generates_trumpish`), whereas a fully
specified word generates nothing but itself (`word_generates_iff`).

The second-order schema `[N -ful]A ≈ [N -less]A` of (14) is a sister link between mother
schemas, one description over a shared base variable read through two subscriptings. The
coindexed base pairs *careful* with *careless* and not with *hopeless*
(`careful_careless_pairs`, `not_careful_hopeless_pairs`). A mother of the two schemas would be
the meet of their descriptions, which over these slots is empty (`fulLess_mother_eq_bot`) and
so is instantiated by every word (`fulLess_mother_instantiates`): it states nothing the sisters
do not, and cannot state the pairing they do.

## Implementation notes

* Words are descriptions over a base slot and an affix slot on a flat carrier, one tier of the
  paper's three; the same subscripting mechanism coindexes across tiers. The paper's remaining
  cases for a mother, an antonymic scale and the feature matrix of an inflectional paradigm,
  are not formalized.

## References

* [audring-2019]
* [booij-2019]
-/

namespace Audring2019

open Morphology.Construction

/-- The bases and affixes of the words cited: the *-ish* family of (8) with the novel base
*Trump*, and the *-ful* and *-less* words of (14). -/
inductive Atom
  | boy
  | fool
  | child
  | trump
  | care
  | hope
  | ish
  | ful
  | less
  deriving DecidableEq

/-- The slots of a suffixed word. -/
inductive Slot
  | base
  | affix
  deriving DecidableEq

/-- The fully specified word with base `b` and affix `a`. -/
def word (b a : Atom) : Slot → Flat Atom
  | .base => ↑b
  | .affix => ↑a

/-! ### The *-ish* family: sister links and their mother -/

/-- The mother schema `[N -ish]A` of (8): the affix pinned, the base an open variable. -/
def ishSchema : Schema Slot (Flat Atom) := ⟨λ | .base => ⊥ | .affix => ↑Atom.ish, {.base}⟩

/-- The stored family of (8). -/
def ishFamily : Set (Slot → Flat Atom) := {word .boy .ish, word .fool .ish, word .child .ish}

theorem ishSchema_instantiates (b : Atom) : ishSchema.Instantiates (word b .ish)
  | .base => bot_le
  | .affix => le_rfl

/-- The variables of a sister link coindexing the affixes of two words. -/
inductive AffixLink
  | base₁
  | base₂
  | affix
  deriving DecidableEq

/-- The sister link at the affix: the two affix slots share a variable, the bases do not. -/
def affixLink : Slot ⊕ Slot → AffixLink
  | .inl .base => .base₁
  | .inr .base => .base₂
  | _ => .affix

/-- The variables of a sister link coindexing the bases of two words. -/
inductive BaseLink
  | base
  | affix₁
  | affix₂
  deriving DecidableEq

/-- The sister link at the base: the two base slots share a variable, the affixes do not. -/
def baseLink : Slot ⊕ Slot → BaseLink
  | .inl .affix => .affix₁
  | .inr .affix => .affix₂
  | _ => .base

/-- Two *-ish* words are sisters at the affix: the pair factors through the link. -/
theorem ish_affix_sisters (b b' : Atom) :
    (Sum.elim (word b .ish) (word b' .ish)).FactorsThrough affixLink := by
  rintro (p | p) (q | q) h <;> cases p <;> cases q <;> first | rfl | simp [affixLink] at h

/-- Two *-ish* words with different bases cannot be coindexed at the base: the relation between
*boy* and *child* is equivalence of function, not sameness, and no sister link states it. -/
theorem not_base_sisters {b b' : Atom} (h : b ≠ b') :
    ¬ (Sum.elim (word b .ish) (word b' .ish)).FactorsThrough baseLink :=
  λ hf => h (Flat.coe_injective (@hf (.inl .base) (.inr .base) rfl))

/-- The mother relates every member of the family through its one variable. -/
theorem ishSchema_relates {w : Slot → Flat Atom} (hw : w ∈ ishFamily) :
    ishSchema.Relates ishFamily w := by
  refine ⟨hw, ?_⟩
  simp only [ishFamily, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl <;> exact ishSchema_instantiates _

/-- The mother is productive: its one variable is open. -/
theorem ishSchema_isProductive : ishSchema.IsProductive := by
  rintro (_ | _) h
  exacts [Set.mem_singleton _, absurd h (by decide)]

/-- The mother generates the novel *Trumpish* with nothing stored. -/
theorem ishSchema_generates_trumpish : ishSchema.Generates ∅ (word .trump .ish) :=
  ishSchema_isProductive.generates_iff.2 (ishSchema_instantiates _)

/-- A fully specified word, taken as a schema, generates nothing but itself: a sister link
between stored words licenses no novel word, and productivity needs a mother's variable. -/
theorem word_generates_iff (b a : Atom) {Λ : Set (Slot → Flat Atom)} {w : Slot → Flat Atom} :
    (⟨word b a, ∅⟩ : Schema Slot (Flat Atom)).Generates Λ w ↔ w = word b a := by
  have hmax : ∀ v, IsMax (word b a v) := λ v => by cases v <;> exact Flat.isMax_coe _
  refine ⟨λ h => (Schema.instantiates_iff_eq_of_forall_isMax hmax).1 h.instantiates, ?_⟩
  rintro rfl
  exact ⟨le_rfl, λ v hv _ => by cases v <;> exact absurd hv Flat.coe_ne_bot⟩

/-! ### The second-order schema `[N -ful]A ≈ [N -less]A` -/

/-- The variables of (14): the base shared by the two schemas and the two affixes. -/
inductive FulLessVar
  | base
  | ful
  | less
  deriving DecidableEq

/-- (14): the two schemas with their coindexed base as one description. -/
def fulLess : Schema FulLessVar (Flat Atom) :=
  ⟨λ | .base => ⊥ | .ful => ↑Atom.ful | .less => ↑Atom.less, {.base}⟩

/-- The subscripting of the slots of `[N -ful]A` by the variables of (14). -/
def fulSub : Slot → FulLessVar
  | .base => .base
  | .affix => .ful

/-- The subscripting of the slots of `[N -less]A` by the variables of (14). -/
def lessSub : Slot → FulLessVar
  | .base => .base
  | .affix => .less

/-- `[N -ful]A`: the description of (14) read at its own slots. -/
def fulSchema : Schema Slot (Flat Atom) := fulLess.comap fulSub

/-- `[N -less]A`: the description of (14) read at its own slots. -/
def lessSchema : Schema Slot (Flat Atom) := fulLess.comap lessSub

/-- The variables of (14) filled by base `b`. -/
def fulLessWord (b : Atom) : FulLessVar → Flat Atom
  | .base => ↑b
  | .ful => ↑Atom.ful
  | .less => ↑Atom.less

/-- *careful* and *careless* are a paired instantiation of (14): same base, sister affixes. -/
theorem careful_careless_pairs :
    fulLess.InstantiatesAt (Sum.elim fulSub lessSub)
      (Sum.elim (word .care .ful) (word .care .less)) :=
  ⟨fulLessWord .care, λ v => by cases v <;> first | exact bot_le | exact le_rfl,
    funext λ p => by rcases p with p | p <;> cases p <;> rfl⟩

/-- *careful* and *hopeless* are not: the coindexed base is filled differently. -/
theorem not_careful_hopeless_pairs :
    ¬ fulLess.InstantiatesAt (Sum.elim fulSub lessSub)
      (Sum.elim (word .care .ful) (word .hope .less)) :=
  λ h => by
    simpa [word] using (Schema.instantiatesAt_elim_iff.1 h).2.2.2.2 .base .base rfl

/-- A mother of the two schemas would be the meet of their descriptions, which over these slots
is empty: nothing but the categories, which the slots do not record. -/
theorem fulLess_mother_eq_bot : fulSchema.body ⊓ lessSchema.body = ⊥ := by
  funext v
  cases v <;> decide

/-- The mother is instantiated by every word: it states nothing the sisters do not. -/
theorem fulLess_mother_instantiates (w : Slot → Flat Atom) :
    (⟨fulSchema.body ⊓ lessSchema.body, ∅⟩ : Schema Slot (Flat Atom)).Instantiates w := by
  show fulSchema.body ⊓ lessSchema.body ≤ w
  rw [fulLess_mother_eq_bot]
  exact bot_le

end Audring2019
