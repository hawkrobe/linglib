/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Data.Forms.Booij2010
import Linglib.Morphology.ConstructionMorphology.Schema
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Linglib.Morphology.ConstructionMorphology.Inheritance
import Linglib.Core.Order.Flat

/-!
# Construction Morphology: the constructional-schema engine [booij-2010-compass]

[booij-2010-compass] analyzes complex words as constructions — pairings of form
and meaning — licensed by constructional schemas in a hierarchical lexicon. This
file instantiates the `Morphology/ConstructionMorphology/` substrate as that CxM engine
over small `Flat` carriers: the deadjectival `-ness` schema and its
unification-instantiation (`carless` unified with the schema is `carlessness`),
generation of a novel `-ness` noun, the compound hierarchy with right-headed
subschemas, the default-inheritance override (`werkbaar`), and schema
unification (`on-` prefixation composed with `V-baar`).

## Main results

* `carlessness_unifies` — instantiation is unification of an adjective with the
  `-ness` schema ([booij-2010-compass]'s worked example)
* `carlessness_generates`, `awareness_related` — the schema's two roles on one
  lexicon: coining the paper's novel noun, relating its stored one
* `compound_inheritance` — subschemas inherit right-headedness (no Right-hand
  Head Rule) yet override locally (NN allows a recursive modifier, AN does not)
* `werkbaar_overrides` — the CxM default-inheritance demand site: `werkbaar`
  overrides the `-baar` schema's transitivity default
* `onbaar_unifies`, `onbaarSchema_instantiates_iff` — two word-formation schemas
  unify into `on-V-baar`, whose instances are exactly their common instances, no
  listed intermediate required
-/

namespace Booij2010

open ConstructionMorphology

/-! ### The deadjectival `-ness` schema

The schema `[[x]A ness]N` of [booij-2010-compass]: a two-slot construction whose
affix slot is lexically fixed as `-ness` and whose base slot is an open
(deadjectival) variable. A concrete adjective unified into the base slot yields a
`-ness` noun. -/

/-- The `-ness` schema over the two slots of a `-ness` noun, base and affix: the affix slot
pinned to `-ness`, the base slot an open deadjectival variable (`⊥`). -/
def nessSchema : Schema (Fin 2) (Flat String) := ⟨![⊥, ↑"ness"], {0}⟩

/-- Any filling whose affix slot is `-ness` instantiates the schema: the base slot
is open, the affix slot's constraint is met. -/
theorem ness_instantiates {w : Fin 2 → Flat String} (h : w 1 = ↑"ness") :
    nessSchema.Instantiates w := by
  intro i
  fin_cases i
  · exact bot_le
  · exact h.ge

/-- `carlessness`, the paper's novel coin (Time, October 5, 2009), instantiates the
`-ness` schema. -/
theorem carlessness_instantiates : nessSchema.Instantiates Forms.carlessness.slots :=
  ness_instantiates (by decide)

/-- Instantiation as unification: unifying the schema description with
`carlessness` returns `carlessness` — [booij-2010-compass]'s worked example. -/
theorem carlessness_unifies :
    PartialUnify.unify nessSchema.body Forms.carlessness.slots =
      some Forms.carlessness.slots :=
  nessSchema.instantiates_iff_unify.mp carlessness_instantiates

/-- The stored `-ness` nouns of the paper's opening word set, feeding the schema's two
roles. -/
def nessLexicon : Set (Fin 2 → Flat String) :=
  {Forms.baldness.slots, Forms.awareness.slots}

/-- The `-ness` schema is productive: its one variable, the base slot, is open. -/
theorem nessSchema_isProductive : nessSchema.IsProductive := by
  intro i h
  fin_cases i
  · exact Set.mem_singleton_iff.2 rfl
  · exact absurd h (by decide)

/-- The schema licenses the novel coin `carlessness` over the stored nouns: the
open base slot takes the unlisted adjective, and the affix slot is a constant.
Being productive, the schema generates every instance whatever is stored. -/
theorem carlessness_generates :
    nessSchema.Generates nessLexicon Forms.carlessness.slots :=
  nessSchema_isProductive.generates_iff.2 carlessness_instantiates

/-- The relational role over the same schema: `awareness` is listed and
instantiates it — the paper's two functions of a schema, expressing the
predictable properties of existing words and coining new ones, on one
schema and one lexicon. -/
theorem awareness_related : nessSchema.Relates nessLexicon Forms.awareness.slots :=
  ⟨Set.mem_insert_of_mem _ rfl, ness_instantiates (by decide)⟩

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

/-- The hierarchical constructicon of English compounds. -/
def compoundHierarchy : Hierarchy CompoundNode :=
  .ofDepth compoundParent (fun n => match n with | .compound => 0 | _ => 1) (by decide)

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

def baarHierarchy : Hierarchy BaarNode :=
  .ofDepth baarParent (fun n => match n with | .baarSchema => 0 | .werkbaar => 1) (by decide)

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

/-- The `on-A` schema: prefix pinned to `on-`, base open. -/
def onSchema : Schema OnbaarSlot (Flat BaarAtom) where
  body
    | .pre => ↑BaarAtom.on
    | .base => ⊥
    | .suf => ⊥
  opens := {.base}

/-- The `V-baar` schema: suffix pinned to `-baar`, base open. -/
def baarSchema : Schema OnbaarSlot (Flat BaarAtom) where
  body
    | .pre => ⊥
    | .base => ⊥
    | .suf => ↑BaarAtom.baar
  opens := {.base}

/-- The unified `on-V-baar` schema: both affixes pinned, base open. -/
def onbaarSchema : Schema OnbaarSlot (Flat BaarAtom) where
  body
    | .pre => ↑BaarAtom.on
    | .base => ⊥
    | .suf => ↑BaarAtom.baar
  opens := {.base}

/-- The `on-` and `V-baar` descriptions unify into the `on-V-baar` description — the
schema unification `(16)`, with no intermediate `V-baar` word required. -/
theorem onbaar_unifies :
    PartialUnify.unify onSchema.body baarSchema.body = some onbaarSchema.body := by decide

/-- The unified schema's instances are exactly the words that are at once `on-`
prefixed and `-baar` suffixed: the content of coining `onbedwingbaar` directly. -/
theorem onbaarSchema_instantiates_iff {w : OnbaarSlot → Flat BaarAtom} :
    onbaarSchema.Instantiates w ↔ onSchema.Instantiates w ∧ baarSchema.Instantiates w :=
  Schema.instantiates_iff_of_unify_eq_some onbaar_unifies

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
