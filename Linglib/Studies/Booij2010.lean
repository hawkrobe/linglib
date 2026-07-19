/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.Construction.Schema
import Linglib.Morphology.Construction.Inheritance
import Linglib.Core.Order.Flat

/-!
# Construction Morphology: the constructional-schema engine [booij-2010-compass]

[booij-2010-compass] analyzes complex words as constructions — pairings of form
and meaning — licensed by constructional schemas in a hierarchical lexicon. This
file instantiates the `Morphology/Construction/` substrate as that CxM engine
over small `Flat` carriers: the deadjectival `-ness` schema and its
unification-instantiation (`carless` unified with the schema is `carlessness`),
generation of a novel `-ness` noun, the compound hierarchy with right-headed
subschemas, the default-inheritance override (`werkbaar`), and schema
unification (`on-` prefixation composed with `V-baar`).

## Main results

* `carlessness_unifies` — instantiation is unification of an adjective with the
  `-ness` schema ([booij-2010-compass]'s worked example)
* `awareness_generates` — the `-ness` schema licenses a novel deadjectival noun
* `compound_inheritance` — subschemas inherit right-headedness (no Right-hand
  Head Rule) yet override locally (NN allows a recursive modifier, AN does not)
* `werkbaar_overrides` — the CxM default-inheritance demand site: `werkbaar`
  overrides the `-baar` schema's transitivity default
* `onbaar_unifies` — two word-formation schemas unify into `on-V-baar`, no listed
  intermediate required
-/

namespace Booij2010

open Morphology.Construction

/-! ### The deadjectival `-ness` schema

The schema `[[x]A ness]N` of [booij-2010-compass]: a two-slot construction whose
affix slot is lexically fixed as `-ness` and whose base slot is an open
(deadjectival) variable. A concrete adjective unified into the base slot yields a
`-ness` noun. -/

/-- The morphs and (deadjectival) bases the `-ness` schema handles. -/
inductive Atom | ness | aware | carless | bald
  deriving DecidableEq, Fintype

/-- The two slots of the `-ness` construction. -/
inductive NessSlot | base | affix
  deriving DecidableEq, Fintype

/-- The `-ness` schema: the affix slot pinned to `-ness`, the base slot an open
deadjectival variable (`⊥`). -/
def nessSchema : Schema NessSlot (Flat Atom) where
  body
    | .base => ⊥
    | .affix => ↑Atom.ness
  opens := {.base}

/-- `carlessness`: the adjective `carless` unified into the base slot. -/
def carlessness : NessSlot → Flat Atom
  | .base => ↑Atom.carless
  | .affix => ↑Atom.ness

/-- `baldness`: a stored `-ness` noun, the attested filler at the affix slot. -/
def baldness : NessSlot → Flat Atom
  | .base => ↑Atom.bald
  | .affix => ↑Atom.ness

/-- `awareness`: a novel `-ness` noun the schema generates. -/
def awareness : NessSlot → Flat Atom
  | .base => ↑Atom.aware
  | .affix => ↑Atom.ness

/-- Any filling whose affix slot is `-ness` instantiates the schema: the base slot
is open, the affix slot's constraint is met. -/
theorem ness_instantiates {w : NessSlot → Flat Atom} (h : w .affix = ↑Atom.ness) :
    nessSchema.Instantiates w := by
  intro i; cases i
  · exact bot_le
  · rw [h]; exact le_rfl

/-- `carlessness` instantiates the `-ness` schema. -/
theorem carlessness_instantiates : nessSchema.Instantiates carlessness :=
  ness_instantiates rfl

/-- Instantiation as unification: unifying the schema description with
`carlessness` returns `carlessness` — [booij-2010-compass]'s worked example. -/
theorem carlessness_unifies :
    PartialUnify.unify nessSchema.body carlessness = some carlessness :=
  nessSchema.instantiates_iff_unify.mp carlessness_instantiates

/-- The stored lexicon of `-ness` nouns feeding the generative role. -/
def nessLexicon : Set (NessSlot → Flat Atom) := {baldness}

/-- The `-ness` schema generates the novel noun `awareness`: the open base slot is
free, and the pinned affix slot takes only its attested filler `-ness`. The
affix slot is not open, so this is `Generates`, not full productivity. -/
theorem awareness_generates : nessSchema.Generates nessLexicon awareness := by
  refine ⟨ness_instantiates rfl, ?_⟩
  intro v hv
  cases v with
  | base => exact absurd rfl hv
  | affix => exact ⟨baldness, rfl, ness_instantiates rfl, rfl⟩

/-! ### The compound hierarchy

The compound schema `(6)` dominates the NN/VN/AN/PN subcases `(7)`. Headedness is
read off the general schema — right-headed — so no Right-hand Head Rule is
needed; subschemas inherit it. Subschemas still legislate locally: an NN
modifier may itself be a compound, an AN modifier may not `(8)`. -/

/-- The compound schema and its four subcases. -/
inductive CompoundNode | compound | nn | vn | an | pn
  deriving DecidableEq, Fintype

/-- The subschema-of relation: each subcase's parent is the general compound
schema. -/
def compoundParent : CompoundNode → Option CompoundNode
  | .compound => none
  | .nn => some .compound
  | .vn => some .compound
  | .an => some .compound
  | .pn => some .compound

private def compoundDepth : CompoundNode → Nat
  | .compound => 0
  | _ => 1

private theorem compoundParent_wf :
    WellFounded (fun a b : CompoundNode => compoundParent b = some a) := by
  have hq : WellFounded (fun a b : CompoundNode => compoundDepth a < compoundDepth b) :=
    InvImage.wf compoundDepth Nat.lt_wfRel.wf
  refine Subrelation.wf (fun {a b} hab => ?_) hq
  revert hab; cases a <;> cases b <;> decide

/-- The hierarchical constructicon of English compounds. -/
def compoundHierarchy : Hierarchy CompoundNode where
  parent := compoundParent
  wf := compoundParent_wf

/-- Headedness, specified once at the general schema. -/
inductive Headed | right | left
  deriving DecidableEq

/-- Right-headedness is a property of the general compound schema alone. -/
def headedness : CompoundNode → Option Headed
  | .compound => some .right
  | _ => none

/-- Whether the modifier may itself be a compound: allowed by default, overridden
at the AN subschema `(8)`. -/
def recursiveModifier : CompoundNode → Option Bool
  | .compound => some true
  | .an => some false
  | _ => none

/-- Subschemas inherit right-headedness from the general schema (no Right-hand
Head Rule), while the AN subschema overrides the default recursive-modifier
option: an NN modifier may be a compound, an AN modifier may not. -/
theorem compound_inheritance :
    compoundHierarchy.value headedness .nn = some .right ∧
    compoundHierarchy.value recursiveModifier .nn = some true ∧
    compoundHierarchy.value recursiveModifier .an = some false := by decide

/-! ### Default inheritance and override: `werkbaar`

[booij-2010-compass]'s own demand site for default inheritance: `-baar` attaches
to transitive verbs, but `werkbaar` (from intransitive `werk`) overrides the
inherited transitivity specification. "By default, complex words inherit the
information specified in a schema, but a particular piece of information may be
overruled by an individual lexical item." A minimal two-level hierarchy: the
schema node and the `werkbaar` leaf. -/

/-- The `-baar` schema node and the `werkbaar` lexical item. -/
inductive BaarNode | baarSchema | werkbaar
  deriving DecidableEq, Fintype

def baarParent : BaarNode → Option BaarNode
  | .baarSchema => none
  | .werkbaar => some .baarSchema

private def baarDepth : BaarNode → Nat
  | .baarSchema => 0
  | .werkbaar => 1

private theorem baarParent_wf :
    WellFounded (fun a b : BaarNode => baarParent b = some a) := by
  have hq : WellFounded (fun a b : BaarNode => baarDepth a < baarDepth b) :=
    InvImage.wf baarDepth Nat.lt_wfRel.wf
  refine Subrelation.wf (fun {a b} hab => ?_) hq
  revert hab; cases a <;> cases b <;> decide

def baarHierarchy : Hierarchy BaarNode where
  parent := baarParent
  wf := baarParent_wf

/-- Transitivity of the base verb. -/
inductive Transitivity | trans | intrans
  deriving DecidableEq

/-- The `-baar` schema requires a transitive base by default; `werkbaar`
overrides to intransitive. -/
def baseTransitivity : BaarNode → Option Transitivity
  | .baarSchema => some .trans
  | .werkbaar => some .intrans

/-- The default-override flagship: `werkbaar` overrides the inherited transitivity
specification, while the schema keeps its default. -/
theorem werkbaar_overrides :
    baarHierarchy.value baseTransitivity .werkbaar = some .intrans ∧
    baarHierarchy.value baseTransitivity .baarSchema = some .trans := by decide

/-! ### Schema unification: `on-` composed with `V-baar`

The two productive schemas — negative `on-` prefixation and deverbal `-baar`
suffixation — unify into a single complex schema `[on [V baar]A]A` `(16)`, so
`onbedwingbaar` is coined directly from the verb without the intermediate
`bedwingbaar` needing to be listed. The join is taken on the schema bodies over a
shared slot space; the intermediate positive adjective is not required to exist,
which is exactly the content the join without a listed intermediate expresses. -/

/-- The affixal morphs of the `on-V-baar` complex. -/
inductive BaarAtom | on | baar
  deriving DecidableEq, Fintype

/-- The three slots of the `on-V-baar` complex schema. -/
inductive OnbaarSlot | pre | base | suf
  deriving DecidableEq, Fintype

/-- The `on-A` schema body: prefix pinned to `on-`, base open. -/
def onBody : OnbaarSlot → Flat BaarAtom
  | .pre => ↑BaarAtom.on
  | .base => ⊥
  | .suf => ⊥

/-- The `V-baar` schema body: suffix pinned to `-baar`, base open. -/
def baarBody : OnbaarSlot → Flat BaarAtom
  | .pre => ⊥
  | .base => ⊥
  | .suf => ↑BaarAtom.baar

/-- The unified `on-V-baar` schema body: both affixes pinned, base open. -/
def onbaarBody : OnbaarSlot → Flat BaarAtom
  | .pre => ↑BaarAtom.on
  | .base => ⊥
  | .suf => ↑BaarAtom.baar

/-- The `on-` and `V-baar` schema bodies unify into the `on-V-baar` body — the
schema unification `(16)`, with no intermediate `V-baar` word required. -/
theorem onbaar_unifies : PartialUnify.unify onBody baarBody = some onbaarBody := by decide

/-! ### Further constructional phenomena (prose)

[booij-2010-compass] extends the constructional analysis in three directions this
file records but does not formalize. **Holistic VN exocentrics**: Romance `VN`
compounds (`lava-piatti` 'dishwasher') carry an agent/instrument meaning that is
a property of the construction as a whole, with no head constituent and no
zero-affix to bear it. **Constructional inflection**: the Russian declension
paradigm treats each cell's morpho-syntactic value as a holistic property of the
word form, with thematic material that is morphomic ([aronoff-1994]). **Periphrasis**:
`have` plus past participle is a constructional idiom whose perfect meaning is
holistic — the natural home for a dedicated periphrasis carrier. -/

end Booij2010
