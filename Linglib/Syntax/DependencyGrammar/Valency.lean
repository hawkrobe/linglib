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
lexical carrier (`complementToArgStr` applied to a verb's `complementType`).

## Main declarations

* `Dir`, `ArgSlot`, `ArgStr` — the slot data: relation, side of the head,
  optionality.
* `Frames n`, `Frames.ofList` — the per-position frame table.
* `argStrV0/VN/VNN/VPassive`, `complementToArgStr` — standard schemas and
  the lexical map into them.
* `satisfiesArgStr`, `checkVerbSubcat` — frame satisfaction: every filler on
  its slot's side of the head, required slots filled, no unlicensed core
  arguments.
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

/-- Whether a dependent at position `dep` sits on side `dir` of the head at
    position `head`. -/
def Dir.admits {n : ℕ} : Dir → Fin n → Fin n → Bool
  | .left, head, dep => dep < head
  | .right, head, dep => head < dep

/-- A single argument slot in an argument structure: which relation fills it,
    on which side of the head, and whether it must be filled. -/
structure ArgSlot where
  /-- The UD relation of the filler. -/
  depType : UD.DepRel
  /-- Which side of the head the filler sits. -/
  dir : Dir
  /-- Whether the slot must be filled. -/
  required : Bool := true
  deriving Repr, DecidableEq

/-- Argument structure: the dependent slots a word requires or allows. -/
abbrev ArgStr := List ArgSlot

/-- The per-position frame table supplied alongside a `Graph n`. -/
abbrev Frames (n : ℕ) := Fin n → Option ArgStr

/-- A sparse frame table: positions not listed carry no frame. -/
def Frames.ofList {n : ℕ} (l : List (Fin n × ArgStr)) : Frames n :=
  λ i => (l.find? (·.1 == i)).map (·.2)

/-! ### Standard schemas -/

/-- Intransitive verb: subject to the left. -/
def argStrV0 : ArgStr := [⟨.nsubj, .left, true⟩]

/-- Transitive verb: subject left, object right. -/
def argStrVN : ArgStr := [⟨.nsubj, .left, true⟩, ⟨.obj, .right, true⟩]

/-- Ditransitive verb: subject left, indirect object right, object right. -/
def argStrVNN : ArgStr :=
  [⟨.nsubj, .left, true⟩, ⟨.iobj, .right, true⟩, ⟨.obj, .right, true⟩]

/-- Passive transitive: subject left (was patient), optional by-phrase right. -/
def argStrVPassive : ArgStr := [⟨.nsubj, .left, true⟩, ⟨.obl, .right, false⟩]

/-- Map a complement type to the corresponding standard DG argument structure.
    Returns `none` for frames without a standard schema: clause-embedding
    types take xcomp/ccomp, not obj, and `.np_pp` has no fixture here. -/
def complementToArgStr : ComplementType → Option ArgStr
  | .none => some argStrV0
  | .np => some argStrVN
  | .np_np => some argStrVNN
  | _ => none

/-! ### Frame satisfaction -/

section Satisfaction

variable {n : ℕ}

/-- The dependents of `v` linked by relation `rel`. -/
def Graph.fillersOf (g : Graph n) (v : Fin n) (rel : UD.DepRel) : List (Fin n) :=
  (g.children v).filter (g.label v · == some rel)

/-- The graph satisfies an argument structure at head `v`: every filler of
    every slot sits on the slot's side of the head, and required slots are
    filled. -/
def satisfiesArgStr (g : Graph n) (v : Fin n) (argStr : ArgStr) : Bool :=
  argStr.all λ slot =>
    (g.fillersOf v slot.depType).all (slot.dir.admits v ·) &&
    (!slot.required || !(g.fillersOf v slot.depType).isEmpty)

/-- Core argument relations governed by lexical frames. Deliberately the
    nominal core only — UD's clausal core relations (csubj, ccomp, xcomp)
    are licensed by clause-embedding frames, which `complementToArgStr`
    does not schematize. -/
private def coreArgRels : List UD.DepRel := [.nsubj, .obj, .iobj]

/-- Every core-argument dependent of `v` is licensed by a slot of `argStr` —
    the closed-world half of frame checking (`satisfiesArgStr` only checks
    that required slots are filled). -/
private def coreArgsLicensed (g : Graph n) (v : Fin n) (argStr : ArgStr) : Bool :=
  (g.children v).all λ w =>
    match g.label v w with
    | some r => !coreArgRels.contains r || argStr.any (·.depType == r)
    | none => true

/-- Check each verb's dependents against its frame: required slots filled in
    the right direction (`satisfiesArgStr`) and no unlicensed core arguments
    (`coreArgsLicensed`). Verbs without a frame are skipped. -/
def checkVerbSubcat (g : Graph n) (frames : Frames n) : Bool :=
  (List.finRange n).all λ v =>
    if (g.words v).cat == .VERB then
      match frames v with
      | some a => satisfiesArgStr g v a && coreArgsLicensed g v a
      | none => true
    else true

end Satisfaction

end DependencyGrammar
