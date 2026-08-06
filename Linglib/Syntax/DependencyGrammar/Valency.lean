import Linglib.Syntax.DependencyGrammar.Basic
import Linglib.Syntax.Category.Verb.Frame

/-!
# Valency: argument-structure frames over dependency trees

The DG valency layer: standard frame schemas for the basic valences, the
map from a verb's lexical `ComplementType` into them, and satisfaction of
a frame by a tree's dependents. [hudson-2010], [osborne-2019].

The slot data types (`Dir`, `ArgSlot`, `ArgStr`) live in `Basic` because
`Tree.frames` carries them; this file owns everything that *does* something
with a frame, and with it the only import of the verb lexicon.

## Main declarations

* `argStrV0/VN/VNN/VPassive` — frame schemas for the standard intransitive /
  transitive / ditransitive / passive valences.
* `complementToArgStr` — a verb's lexical complement type as a frame.
* `satisfiesArgStr`, `checkVerbSubcat` — frame satisfaction: every filler on
  its slot's side of the head, required slots filled, no unlicensed core
  arguments.
-/

namespace DependencyGrammar

section StandardArgStr

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

end StandardArgStr

section ArgStrSatisfaction

/-- The dependency `d` fills `slot` at head position `headIdx` (relation and
    head match; direction is checked separately by `Dir.admits`). -/
def slotMatches (headIdx : Nat) (slot : ArgSlot) (d : Dependency) : Bool :=
  d.headIdx == headIdx && d.depType == slot.depType

/-- The tree satisfies an argument structure at `headIdx`: every filler of
    every slot sits on the slot's side of the head, and required slots are
    filled. -/
def satisfiesArgStr (t : Tree) (headIdx : Nat) (argStr : ArgStr) : Bool :=
  argStr.all λ slot =>
    (t.deps.filter (slotMatches headIdx slot)).all
      (λ d => slot.dir.admits headIdx d.depIdx) &&
    (!slot.required || t.deps.any (slotMatches headIdx slot))

/-- Core argument relations governed by lexical frames. Deliberately the
    nominal core only — UD's clausal core relations (csubj, ccomp, xcomp)
    are licensed by clause-embedding frames, which `complementToArgStr`
    does not schematize. -/
private def coreArgRels : List UD.DepRel := [.nsubj, .obj, .iobj]

/-- Every core-argument dependent of `headIdx` is licensed by a slot of
    `argStr` — the closed-world half of frame checking (`satisfiesArgStr`
    only checks that required slots are filled). -/
private def coreArgsLicensed (t : Tree) (headIdx : Nat) (argStr : ArgStr) : Bool :=
  t.deps.all λ d =>
    if d.headIdx == headIdx && coreArgRels.contains d.depType then
      argStr.any (·.depType == d.depType)
    else true

/-- Check each verb's dependents against its lexical frame: required slots
    filled in the right direction (`satisfiesArgStr`) and no unlicensed core
    arguments (`coreArgsLicensed`). Verbs without a frame are skipped. -/
def checkVerbSubcat (t : Tree) : Bool :=
  t.words.zipIdx.all λ (w, i) =>
    if w.cat == .VERB then
      match t.frame i with
      | some a => satisfiesArgStr t i a && coreArgsLicensed t i a
      | none => true
    else true

end ArgStrSatisfaction

end DependencyGrammar
