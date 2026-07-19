/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.Morph
import Mathlib.Data.List.Infix

/-!
# Roots

The formal definition of roothood over `Morph`, relative to a fragment's word
and free-form inventories ([bloomfield-1933], the base definition of
[qin-2025]): a morph is a root iff it occurs in a *primary word* — one with no
free form as a proper part. The definition is deliberately inclusive
(meaning-free cores like *-fer* qualify; so do free function words);
`Studies/Qin2025.lean` grades instances by canonicity, and
[haspelmath-2025-root]'s contentfulness-gated alternative is
`Studies/Haspelmath2025Root.lean`. Consonantal skeletons are
`ConsonantalRoot`; DM's acategorial root is `Morphology/DM/Root.lean`.

## Main declarations

* `IsPrimaryWord` — no proper contiguous part is a free form.
* `Morph.IsCoreIn` — the root property: occurrence in a primary word.
* `Morph.IsTypicalAffixIn` — occurrence in secondary words only.
-/

namespace Morphology

/-- A word is **primary** ([bloomfield-1933]): no proper contiguous part of
it is a free form. *cat* and *refer* are primary; *cats* and *blackbirds* are
secondary. -/
def IsPrimaryWord (freeForms : List (List Morph)) (w : List Morph) : Prop :=
  ∀ f ∈ freeForms, f.length < w.length → ¬ f <:+: w

instance (freeForms : List (List Morph)) (w : List Morph) :
    Decidable (IsPrimaryWord freeForms w) :=
  inferInstanceAs (Decidable (∀ f ∈ freeForms, _ → _))

/-- A **morphological core** — [qin-2025]'s base definition of a root: a
morph occurring in some primary word. -/
def Morph.IsCoreIn (m : Morph) (words freeForms : List (List Morph)) : Prop :=
  ∃ w ∈ words, IsPrimaryWord freeForms w ∧ m ∈ w

instance (m : Morph) (words freeForms : List (List Morph)) :
    Decidable (m.IsCoreIn words freeForms) :=
  inferInstanceAs (Decidable (∃ w ∈ words, _))

/-- A **typical affix** occurs only in secondary words ([bloomfield-1933]):
*-s* and *-ness* attach to free forms. -/
def Morph.IsTypicalAffixIn (m : Morph)
    (words freeForms : List (List Morph)) : Prop :=
  ∀ w ∈ words, m ∈ w → ¬ IsPrimaryWord freeForms w

/-- A singleton word is primary when the free-form inventory has no empty
form. -/
theorem isPrimaryWord_singleton {freeForms : List (List Morph)}
    (h : [] ∉ freeForms) (m : Morph) : IsPrimaryWord freeForms [m] := by
  intro f hf hlen _
  exact h (List.length_eq_zero_iff.mp (Nat.lt_one_iff.mp hlen) ▸ hf)

/-- A free morpheme standing as a word is a morphological core. -/
theorem Morph.isCoreIn_of_free_word {words freeForms : List (List Morph)}
    {m : Morph} (hw : [m] ∈ words) (h : [] ∉ freeForms) :
    m.IsCoreIn words freeForms :=
  ⟨[m], hw, isPrimaryWord_singleton h m, List.mem_singleton_self m⟩

end Morphology
