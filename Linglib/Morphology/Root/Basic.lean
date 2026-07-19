/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Data.UD.Basic
import Linglib.Morphology.Morph
import Mathlib.Data.List.Infix

/-!
# Roots

Two definitions of roothood over `Morph`, relative to a fragment's word and
free-form inventories. The formal one ([bloomfield-1933], the base definition
of [qin-2025]): a morph is a core iff it occurs in a *primary word* — one with
no free form as a proper part. The semantic one ([haspelmath-2025-root]'s
definition (1)): a *contentful* morph — denoting an action, an object or a
property — occurring in a free form with no other contentful morph. The two
come apart at meaning-free cores like *-fer* (`Studies/Qin2025.lean`).
Consonantal skeletons are `ConsonantalRoot`; DM's acategorial root is
`Morphology/DM/Root.lean`.

## Main declarations

* `IsPrimaryWord`, `Morph.IsCoreIn`, `Morph.IsTypicalAffixIn` — the formal
  layer: primary words, cores, and affixes.
* `RootClass`, `RootClass.upos` — action, object, and property roots and
  their word classes.
* `Morph.IsRootIn` — the semantic layer, relative to a contentfulness
  classification `cls`.
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

/-- The three semantic root classes: roots denoting actions, objects, and
properties. Their prototypical combinations with discourse functions —
predication, reference, modification — need no function indicators, which
is what makes these the crucial classes for word-class typology. -/
inductive RootClass where
  /-- A root denoting an action (*sing*, *open*). -/
  | action
  /-- A root denoting an object (*tree*, *bird*). -/
  | object
  /-- A root denoting a property (*good*, *small*). -/
  | property
  deriving DecidableEq, Repr

/-- Word classes as comparative concepts: a verb is an action-denoting root,
a noun an object-denoting root, an adjective a property-denoting root. -/
def RootClass.upos : RootClass → UD.UPOS
  | .action => .VERB
  | .object => .NOUN
  | .property => .ADJ

/-- `m.IsRootIn freeForms cls` is [haspelmath-2025-root]'s definition (1)
relative to a fragment: the classification `cls` assigns `m` a root class
(it is contentful), and `m` occurs in some free form in which every other
morph is non-contentful. Contentful affixes and neoclassical combining
forms satisfy the first conjunct but not the second. -/
def Morph.IsRootIn (m : Morph) (freeForms : List (List Morph))
    (cls : Morph → Option RootClass) : Prop :=
  (cls m).isSome ∧ ∃ w ∈ freeForms, m ∈ w ∧ ∀ m' ∈ w, m' ≠ m → cls m' = none

instance (m : Morph) (freeForms : List (List Morph))
    (cls : Morph → Option RootClass) [DecidableEq Morph] :
    Decidable (m.IsRootIn freeForms cls) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Morphology
