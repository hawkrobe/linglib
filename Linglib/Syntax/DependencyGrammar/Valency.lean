/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.DependencyGrammar.Basic
import Linglib.Syntax.Category.Verb.Frame

/-!
# Valency: argument-structure frames over dependency graphs

The DG valency layer: slot data types, standard frame schemas for the basic
valences, the map from a verb's lexical `ComplementType` into them, and
satisfaction of a frame by a position's dependents. [hudson-2010],
[osborne-2019].

Frames are a *side table* (`Frames n`), not part of the graph carrier: the
frame is framework apparatus (like HPSG's ARG-ST), supplied alongside the
graph by the consumers that reason about valency and populated from the
lexical carrier (a verb's `complementType.valency`).

## Main declarations

* `Valency`, `Valency.Slot` — a word's valency ([tesniere-1959]'s term) as a
  list of slots: relation, side of the head, optionality.
* `Frames n`, `Frames.ofList` — the per-position valency table.
* `Valency.intransitive/transitive/ditransitive/passiveTransitive`,
  `ComplementType.valency` — standard schemas and the lexical map into them.
* `SatisfiesValency`, `Graph.SatisfiesFrames` — valency satisfaction: every
  filler on its slot's side of the head, required slots filled, no
  unlicensed core arguments.
-/

namespace DependencyGrammar

/-! ### Slot data -/

/-- Direction of a dependent relative to its head. -/
inductive Dir where
  /-- The dependent precedes the head. -/
  | left
  /-- The dependent follows the head. -/
  | right
  deriving Repr, DecidableEq

/-- A dependent at position `dep` sits on side `dir` of the head at
    position `head`. -/
def Dir.Admits {n : ℕ} : Dir → Fin n → Fin n → Prop
  | .left, head, dep => dep < head
  | .right, head, dep => head < dep

instance {n : ℕ} (dir : Dir) (head dep : Fin n) :
    Decidable (dir.Admits head dep) := by
  cases dir <;> exact inferInstanceAs (Decidable (_ < _))

/-- A single valency slot: which relation fills it, on which side of the
    head, and whether it must be filled. -/
structure Valency.Slot where
  /-- The UD relation of the filler. -/
  depType : UD.DepRel
  /-- Which side of the head the filler sits. -/
  dir : Dir
  /-- Whether the slot must be filled. -/
  required : Bool := true
  deriving Repr, DecidableEq

/-- The valency of a word: the dependent slots it requires or allows. -/
abbrev Valency := List Valency.Slot

/-- The per-position frame table supplied alongside a `Graph n`. -/
abbrev Frames (n : ℕ) := Fin n → Option Valency

/-- A sparse frame table: positions not listed carry no frame. -/
def Frames.ofList {n : ℕ} (l : List (Fin n × Valency)) : Frames n :=
  λ i => (l.find? (·.1 == i)).map (·.2)

/-! ### Standard schemas -/

/-- Intransitive verb: subject to the left. -/
def Valency.intransitive : Valency := [⟨.nsubj, .left, true⟩]

/-- Transitive verb: subject left, object right. -/
def Valency.transitive : Valency := [⟨.nsubj, .left, true⟩, ⟨.obj, .right, true⟩]

/-- Ditransitive verb: subject left, indirect object right, object right. -/
def Valency.ditransitive : Valency :=
  [⟨.nsubj, .left, true⟩, ⟨.iobj, .right, true⟩, ⟨.obj, .right, true⟩]

/-- Passive transitive: subject left (was patient), optional by-phrase right. -/
def Valency.passiveTransitive : Valency := [⟨.nsubj, .left, true⟩, ⟨.obl, .right, false⟩]

/-- A verb's lexical complement type as a standard valency. Returns `none`
    for frames without a standard schema: clause-embedding types take
    xcomp/ccomp, not obj, and `.np_pp` has no fixture here. -/
def _root_.ComplementType.valency : ComplementType → Option Valency
  | .none => some .intransitive
  | .np => some .transitive
  | .np_np => some .ditransitive
  | _ => none

/-! ### Frame satisfaction -/

section Satisfaction

variable {n : ℕ}

/-- The dependents of `v` linked by relation `rel`. -/
def Graph.fillersOf (g : Graph n) (v : Fin n) (rel : UD.DepRel) : List (Fin n) :=
  (g.children v).filter (g.label v · == some rel)

/-- The graph satisfies a valency at head `v`: every filler of every slot
    sits on the slot's side of the head, and required slots are filled. -/
def SatisfiesValency (g : Graph n) (v : Fin n) (val : Valency) : Prop :=
  ∀ slot ∈ val, (∀ w ∈ g.fillersOf v slot.depType, slot.dir.Admits v w) ∧
    (slot.required → g.fillersOf v slot.depType ≠ [])

instance (g : Graph n) (v : Fin n) (val : Valency) :
    Decidable (SatisfiesValency g v val) :=
  List.decidableBAll _ val

/-- Core argument relations governed by lexical frames. Deliberately the
    nominal core only — UD's clausal core relations (csubj, ccomp, xcomp)
    are licensed by clause-embedding frames, which `ComplementType.valency`
    does not schematize. -/
private def coreArgRels : List UD.DepRel := [.nsubj, .obj, .iobj]

/-- Every core-argument dependent of `v` is licensed by a slot of `val` —
    the closed-world half of valency checking (`SatisfiesValency` only
    checks that required slots are filled). -/
private def CoreArgsLicensed (g : Graph n) (v : Fin n) (val : Valency) : Prop :=
  ∀ w ∈ g.children v, ∀ r ∈ g.label v w,
    r ∈ coreArgRels → ∃ slot ∈ val, slot.depType = r

private instance (g : Graph n) (v : Fin n) (val : Valency) :
    Decidable (CoreArgsLicensed g v val) :=
  List.decidableBAll _ _

/-- Each verb's dependents satisfy its frame: required slots filled in the
    right direction (`SatisfiesValency`) and no unlicensed core arguments
    (`CoreArgsLicensed`). Verbs without a frame are unconstrained. -/
def Graph.SatisfiesFrames (g : Graph n) (frames : Frames n) : Prop :=
  ∀ v, (g.words v).cat = .VERB → ∀ val ∈ frames v,
    SatisfiesValency g v val ∧ CoreArgsLicensed g v val

instance (g : Graph n) (frames : Frames n) :
    Decidable (g.SatisfiesFrames frames) :=
  inferInstanceAs (Decidable (∀ _, _))

end Satisfaction

end DependencyGrammar
