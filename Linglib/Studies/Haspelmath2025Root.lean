import Linglib.Morphology.Root.Basic
import Linglib.Data.UD.Basic

/-!
# Haspelmath 2025: the contentfulness-gated root
[haspelmath-2025-root]

Definition (1): a **root** is a contentful morph — a morph denoting an action,
an object or a property — that can occur as part of a free form without
another contentful morph. Against the formal base definition of
`Morphology/Root/Basic.lean`, contentfulness is a *gate*: the qualifying
clause excludes contentful affixes (the Japanese causative *-ase*) and
neoclassical combining forms (*geo-*, *socio-*), which are contentful but
never the sole contentful morph of a free form
(`geo_not_root`). Formally identical roots with related meanings (*hammer*
the instrument, *hammer* the action) are heterosemous *sister roots*, not one
precategorial root — the classification `cls` assigns each its own class; the
paper's §6 divergence from precategorial root families is deferred content.

## Main declarations

* `RootClass` — action, object, and property roots; `RootClass.upos` — word
  classes as comparative concepts.
* `Morph.IsRootIn` — definition (1), relative to a fragment's free forms and
  contentfulness classification.
* `geo_not_root` — a combining form is contentful yet fails the definition.
-/

namespace Haspelmath2025Root

open Morphology

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

/-- `m.IsRootIn freeForms cls` is definition (1) relative to a fragment: the
classification `cls` assigns `m` a root class (it is contentful), and `m`
occurs in some free form in which every other morph is non-contentful. -/
def _root_.Morphology.Morph.IsRootIn (m : Morph)
    (freeForms : List (List Morph))
    (cls : Morph → Option RootClass) : Prop :=
  (cls m).isSome ∧ ∃ w ∈ freeForms, m ∈ w ∧ ∀ m' ∈ w, m' ≠ m → cls m' = none

instance (m : Morph) (freeForms : List (List Morph))
    (cls : Morph → Option RootClass) :
    Decidable (m.IsRootIn freeForms cls) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### The combining-form exclusion -/

/-- The neoclassical combining form *geo-*. -/
def geo : Morph := .root "geo"
/-- The neoclassical combining form *-logy*. -/
def logy : Morph := .root "logy"

/-- The classification: both pieces of *geology* are contentful. -/
def geoCls : Morph → Option RootClass
  | m => if m = geo ∨ m = logy then some .object else none

/-- *geo-* is contentful yet not a root: in *geology* it never occurs as the
sole contentful morph of a free form — the definition's qualifying clause in
action. Under the formal base definition it is a morphological core. -/
theorem geo_not_root :
    ¬ geo.IsRootIn [[geo, logy]] geoCls ∧
      geo.IsCoreIn [[geo, logy]] [[geo, logy]] := by
  refine ⟨by decide, by decide⟩

end Haspelmath2025Root
