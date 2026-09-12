/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Data.Forms.Audring2019
import Linglib.Morphology.ConstructionMorphology.Schema
import Linglib.Core.Relation.FactorsThroughOn
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

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
coindexed base pairs *careful* with *careless* and not with *clueless*
(`careful_careless_pairs`, `not_careful_clueless_pairs`). A mother of the two schemas would be
the meet of their descriptions, which over these slots is empty (`fulLess_mother_eq_bot`) and
so is instantiated by every word (`fulLess_mother_instantiates`): it states nothing the sisters
do not, and cannot state the pairing they do.

## Implementation notes

* The words are the CLDF forms of `Data/Forms/Audring2019.json`, read as slot-indexed segments
  by `Data.Forms.Form.slots`: a base slot and an affix slot on the flat carrier, one tier of the
  paper's three; the same subscripting mechanism coindexes across tiers. The paper's remaining
  cases for a mother, an antonymic scale and the feature matrix of an inflectional paradigm,
  are not formalized.

## References

* [audring-2019]
* [booij-2019]
-/

namespace Audring2019

open ConstructionMorphology

/-- A word with base `b` and affix `a` over the two slots base and affix. -/
def word (b a : String) : Fin 2 → Flat String := ![↑b, ↑a]

/-! ### The *-ish* family: sister links and their mother -/

/-- The mother schema `[N -ish]A` of (8): the affix pinned, the base an open variable. -/
def ishSchema : Schema (Fin 2) (Flat String) := Schema.productive ![⊥, ↑"ish"]

/-- The stored family of (8). -/
def ishFamily : Set (Fin 2 → Flat String) :=
  {Forms.boyish.slots, Forms.foolish.slots, Forms.childish.slots}

/-- Any word whose affix is *-ish* instantiates the mother. -/
theorem ishSchema_instantiates {w : Fin 2 → Flat String} (h : w 1 = ↑"ish") :
    ishSchema.Instantiates w := by
  intro i
  fin_cases i
  · exact bot_le
  · exact h.ge

/-- The variables of a sister link coindexing the affixes of two words. -/
inductive AffixLink
  | base₁
  | base₂
  | affix
  deriving DecidableEq

/-- The sister link at the affix: the two affix slots share a variable, the bases do not. -/
def affixLink : Fin 2 ⊕ Fin 2 → AffixLink := Sum.elim ![.base₁, .affix] ![.base₂, .affix]

/-- The variables of a sister link coindexing the bases of two words. -/
inductive BaseLink
  | base
  | affix₁
  | affix₂
  deriving DecidableEq

/-- The sister link at the base: the two base slots share a variable, the affixes do not. -/
def baseLink : Fin 2 ⊕ Fin 2 → BaseLink := Sum.elim ![.base, .affix₁] ![.base, .affix₂]

/-- *boyish* and *childish* are sisters at the affix: the pair factors through the link. -/
theorem ish_affix_sisters :
    (Sum.elim Forms.boyish.slots Forms.childish.slots).FactorsThrough affixLink := by
  decide

/-- *boyish* and *childish* cannot be coindexed at the base: the relation between *boy* and
*child* is equivalence of function, not sameness, and no sister link states it. -/
theorem not_base_sisters :
    ¬ (Sum.elim Forms.boyish.slots Forms.childish.slots).FactorsThrough baseLink := by
  decide

/-- The mother relates every member of the family through its one variable. -/
theorem ishSchema_relates {w : Fin 2 → Flat String} (hw : w ∈ ishFamily) :
    ishSchema.Relates ishFamily w := by
  refine ⟨hw, ?_⟩
  simp only [ishFamily, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl <;> exact ishSchema_instantiates (by decide)

/-- The mother is productive: its one variable is open. -/
theorem ishSchema_isProductive : ishSchema.IsProductive := Schema.isProductive_productive _

/-- The mother generates the novel *Trumpish* with nothing stored. -/
theorem ishSchema_generates_trumpish : ishSchema.Generates ∅ Forms.trumpish.slots :=
  ishSchema_isProductive.generates_iff.2 (ishSchema_instantiates (by decide))

/-- A fully specified word, taken as a schema, generates nothing but itself: a sister link
between stored words licenses no novel word, and productivity needs a mother's variable. -/
theorem word_generates_iff (b a : String) {Λ : Set (Fin 2 → Flat String)}
    {w : Fin 2 → Flat String} :
    (⟨word b a, ∅⟩ : Schema (Fin 2) (Flat String)).Generates Λ w ↔ w = word b a := by
  have hmax : ∀ v, IsMax (word b a v) := λ v => by fin_cases v <;> exact Flat.isMax_coe _
  refine ⟨λ h => (Schema.instantiates_iff_eq_of_forall_isMax hmax).1 h.instantiates, ?_⟩
  rintro rfl
  exact ⟨le_rfl, λ v hv _ => by fin_cases v <;> exact absurd hv Flat.coe_ne_bot⟩

/-! ### The second-order schema `[N -ful]A ≈ [N -less]A` -/

/-- The variables of (14): the base shared by the two schemas and the two affixes. -/
inductive FulLessVar
  | base
  | ful
  | less
  deriving DecidableEq

/-- (14): the two schemas with their coindexed base as one description. -/
def fulLess : Schema FulLessVar (Flat String) :=
  ⟨λ | .base => ⊥ | .ful => ↑"ful" | .less => ↑"less", {.base}⟩

/-- The subscripting of the slots of `[N -ful]A` by the variables of (14). -/
def fulSub : Fin 2 → FulLessVar := ![.base, .ful]

/-- The subscripting of the slots of `[N -less]A` by the variables of (14). -/
def lessSub : Fin 2 → FulLessVar := ![.base, .less]

/-- `[N -ful]A`: the description of (14) read at its own slots. -/
def fulSchema : Schema (Fin 2) (Flat String) := fulLess.comap fulSub

/-- `[N -less]A`: the description of (14) read at its own slots. -/
def lessSchema : Schema (Fin 2) (Flat String) := fulLess.comap lessSub

/-- The variables of (14) filled by base `b`. -/
def fulLessWord (b : String) : FulLessVar → Flat String
  | .base => ↑b
  | .ful => ↑"ful"
  | .less => ↑"less"

/-- *careful* and *careless* are a paired instantiation of (14): same base, sister affixes. -/
theorem careful_careless_pairs :
    fulLess.InstantiatesAt (Sum.elim fulSub lessSub)
      (Sum.elim Forms.careful.slots Forms.careless.slots) :=
  ⟨fulLessWord "care", λ v => by cases v <;> first | exact bot_le | exact le_rfl,
    funext λ p => by rcases p with p | p <;> fin_cases p <;> decide⟩

/-- *careful* and *clueless* are not: the coindexed base is filled differently. -/
theorem not_careful_clueless_pairs :
    ¬ fulLess.InstantiatesAt (Sum.elim fulSub lessSub)
      (Sum.elim Forms.careful.slots Forms.clueless.slots) :=
  λ h => absurd ((Schema.instantiatesAt_elim_iff.1 h).2.2.2.2 0 0 rfl) (by decide)

/-- A mother of the two schemas would be the meet of their descriptions, which over these slots
is empty: nothing but the categories, which the slots do not record. -/
theorem fulLess_mother_eq_bot : fulSchema.body ⊓ lessSchema.body = ⊥ := by
  funext v
  fin_cases v <;> decide

/-- The mother is instantiated by every word: it states nothing the sisters do not. -/
theorem fulLess_mother_instantiates (w : Fin 2 → Flat String) :
    (⟨fulSchema.body ⊓ lessSchema.body, ∅⟩ : Schema (Fin 2) (Flat String)).Instantiates
      w := by
  show fulSchema.body ⊓ lessSchema.body ≤ w
  rw [fulLess_mother_eq_bot]
  exact bot_le

end Audring2019
