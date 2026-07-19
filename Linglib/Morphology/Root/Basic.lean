/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Data.UD.Basic
import Linglib.Morphology.Morph

/-!
# Roots

[haspelmath-2025-root]'s definition (1): a **root** is a contentful morph —
a morph denoting an action, an object or a property — that can occur as part
of a free form without another contentful morph. A root is thus a kind of
`Morph`, a concrete contiguous form: Semitic consonantal skeletons do not
fall under the definition (they are `Morphology.ConsonantalRoot`), and the
abstract acategorial Root of Distributed Morphology is a different object
again (`Morphology/DM/Root.lean`). The qualifying clause excludes contentful
affixes (the Japanese causative *-ase*) and neoclassical combining forms
(*geo-*, *socio-*), which are contentful but never the sole contentful morph
of a free form.

Formally identical roots with related meanings (*hammer* the instrument,
*hammer* the action) are heterosemous *sister roots*, not one precategorial
root — the classification `cls` below assigns each its own class.

## Main declarations

* `RootClass` — action, object, and property roots.
* `RootClass.upos` — word classes as comparative concepts: a verb is an
  action-denoting root, a noun an object-denoting root, an adjective a
  property-denoting root.
* `Morph.IsRootIn` — the definition, relative to a fragment's free forms
  and contentfulness classification.
-/

namespace Morphology

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

/-- Word classes as comparative concepts: a verb is an action-denoting
root, a noun an object-denoting root, an adjective a property-denoting
root. -/
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
