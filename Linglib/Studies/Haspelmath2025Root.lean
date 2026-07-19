import Linglib.Morphology.Root.Basic
import Linglib.Morphology.Root.System
import Linglib.Data.UD.Basic
import Mathlib.Tactic.DeriveFintype

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

/-! ### Sister roots vs one root, as hom-existence

The paper's heterosemy claim — *hammer* the instrument and *hammer* the
action are two sister roots, not one precategorial root — rendered on
`Morphology.Root.System`: the sister carving (two frame-restricted indices)
and the single-√ carving (one index, allosemous across frames) are
**hom-incomparable** on the strict tier, so neither analysis reduces to the
other; and accidental homophones (*bank₁*/*bank₂*) spellout-merge but never
interp-merge into any target — the strict tier separates identity from
homophony. -/

section Individuation

open Morphology.Root

/-- The two categorial frames. -/
inductive Frame | nominal | verbal
  deriving DecidableEq, Fintype, Repr

/-- The two *bank* homophones. -/
inductive BankLex | river | money
  deriving DecidableEq, Fintype, Repr

/-- Their senses. -/
inductive BankSense | riverside | institution
  deriving DecidableEq, Fintype, Repr

/-- The homophone system: identical spellout everywhere, distinct senses. -/
def bankSisters : Interpreted BankLex Frame String BankSense where
  spellout := fun _ _ => {"bank"}
  interp := fun r _ =>
    match r with | .river => {.riverside} | .money => {.institution}

/-- The merged one-index target for the spellout level. -/
def bankMerged : System Unit Frame String where
  spellout := fun _ _ => {"bank"}

/-- At the spellout level the homophones merge: a transport hom exists. -/
theorem bank_spellout_merger :
    Nonempty (System.Hom bankSisters.toSystem bankMerged) :=
  ⟨⟨fun _ => (), fun _ c => c, fun r _ => by cases r <;> rfl⟩⟩

/-- **No strict hom into any target merges the homophones**: identification
would force their senses to coincide contextwise
(`Interpreted.Hom.interp_eq_of_onRoot_eq`). Homophony is not identity. -/
theorem bank_no_identity {R₂ C₂ : Type*}
    {T : Interpreted R₂ C₂ String BankSense}
    (φ : Interpreted.Hom bankSisters T) :
    φ.onRoot .river ≠ φ.onRoot .money := by
  intro h
  have := φ.interp_eq_of_onRoot_eq h .nominal
  simp [bankSisters] at this

/-- The heterosemous senses of *hammer*. -/
inductive HammerSense | instrument | action
  deriving DecidableEq, Fintype, Repr

/-- The paper's carving: two sister roots. -/
inductive Sisters | hammerN | hammerV
  deriving DecidableEq, Fintype, Repr

/-- The rival carving: one acategorial root. -/
inductive Sqrt | hammer
  deriving DecidableEq, Fintype, Repr

/-- The sister carving: each root licensed only in its own frame, with its
own sense. -/
def sisterCarving : Interpreted Sisters Frame String HammerSense where
  spellout := fun r c =>
    match r, c with
    | .hammerN, .nominal => {"hammer"}
    | .hammerV, .verbal => {"hammer"}
    | _, _ => ∅
  interp := fun r c =>
    match r, c with
    | .hammerN, .nominal => {.instrument}
    | .hammerV, .verbal => {.action}
    | _, _ => ∅

/-- The single-√ carving: one root licensed in both frames, allosemous. -/
def sqrtCarving : Interpreted Sqrt Frame String HammerSense where
  spellout := fun _ _ => {"hammer"}
  interp := fun _ c =>
    match c with | .nominal => {.instrument} | .verbal => {.action}

/-- No strict hom from the sister carving to the single-√ carving: the
sisters' licensing gaps (*hammer-the-noun* has no verbal cell) cannot be
reproduced by the total √. -/
theorem sisters_to_sqrt_none (φ : Interpreted.Hom sisterCarving sqrtCarving) :
    False := by
  have h := φ.spellout_eq .hammerN .verbal
  cases hr : φ.onRoot .hammerN
  cases hc : φ.onCtx .verbal <;> rw [hr, hc] at h <;>
    exact absurd h (by decide)

/-- No strict hom from the single-√ carving to the sister carving either:
the total √ must land on one frame-restricted sister, whose single licensed
cell cannot carry both allosemes. The two carvings are hom-incomparable —
the rivalry is between genuinely distinct systems. -/
theorem sqrt_to_sisters_none (φ : Interpreted.Hom sqrtCarving sisterCarving) :
    False := by
  have hs₁ := φ.spellout_eq .hammer .nominal
  have hs₂ := φ.spellout_eq .hammer .verbal
  have hi₁ := φ.interp_eq .hammer .nominal
  have hi₂ := φ.interp_eq .hammer .verbal
  cases hr : φ.onRoot .hammer <;> cases hc₁ : φ.onCtx .nominal <;>
    cases hc₂ : φ.onCtx .verbal <;> rw [hr, hc₁] at hs₁ hi₁ <;>
    rw [hr, hc₂] at hs₂ hi₂ <;>
    first
    | exact absurd hs₁ (by decide)
    | exact absurd hs₂ (by decide)
    | exact absurd (hi₁.trans hi₂.symm) (by decide)

end Individuation

end Haspelmath2025Root
