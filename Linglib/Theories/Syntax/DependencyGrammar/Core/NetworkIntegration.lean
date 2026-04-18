import Linglib.Core.Inheritance
import Linglib.Core.Grammar
import Linglib.Theories.Syntax.DependencyGrammar.Core.Basic

/-!
# WG Network Integration

Connects `Core.Inheritance` (Hudson's isA/prop network model) to the
dependency grammar module so that word classes and their argument structures
live in a single WG network. @cite{hudson-1984} @cite{hudson-2010}

Argument structures are inherited via default inheritance: a transitive verb
inherits from verb, but a passive can override locally (the most specific
value wins — what @cite{hudson-2010} later calls the "Best Fit Principle").

Subject-auxiliary inversion is modeled as subtype inheritance: the
interrogative auxiliary is a subtype of auxiliary that locally overrides the
subject's direction from left to right. This faithfully follows
@cite{hudson-1984} pp. 117-118, where the inverted auxiliary is treated as a
special subtype of "auxiliary" with its own word-order requirements:

> model (interrogative): auxiliary and tensed
> subject (interrogative): s, interrogative < s
-/

set_option autoImplicit false

namespace DepGrammar.WG

open Core.Inheritance

-- ============================================================================
-- Node and Relation Types
-- ============================================================================

/-- Nodes in a WG network: word classes, dependency relations, or directions. -/
inductive WGNode where
  | wordClass (name : String)
  | depRel (rel : UD.DepRel)
  | dir (d : Dir)
  deriving Repr, DecidableEq

/-- Relation labels for property links in a WG network.
In @cite{hudson-1984}'s terms, these are the named relations that connect
word-class nodes to their syntactic properties. -/
inductive WGRel where
  | argSlot (idx : Nat)     -- the idx-th argument slot (target = depRel)
  | slotDir (idx : Nat)     -- direction for slot idx (target = Dir)
  deriving Repr, DecidableEq

-- ============================================================================
-- Building Networks
-- ============================================================================

/-- Abbreviation for a WG inheritance network. -/
abbrev WGNetwork := Network WGNode WGRel

/-- Create an isA link between word classes. -/
def isALink (child parent : String) : Link WGNode WGRel :=
  { kind := .isA, source := .wordClass child, target := .wordClass parent }

/-- Create a property link for an argument slot's dependency relation. -/
def argSlotLink (wc : String) (idx : Nat) (rel : UD.DepRel) : Link WGNode WGRel :=
  { kind := .prop, source := .wordClass wc, target := .depRel rel,
    label := some (.argSlot idx) }

/-- Create a property link for an argument slot's direction. -/
def slotDirLink (wc : String) (idx : Nat) (d : Dir) : Link WGNode WGRel :=
  { kind := .prop, source := .wordClass wc, target := .dir d,
    label := some (.slotDir idx) }

-- ============================================================================
-- Resolving Argument Structure from the Network
-- ============================================================================

/-- Look up one argument slot from the network for a word class, using
default inheritance. Returns `none` if the slot is not defined. -/
def resolveSlot (net : WGNetwork) (wc : String) (idx : Nat)
    : Option ArgSlot :=
  let node := WGNode.wordClass wc
  let rels := inherited net node (.argSlot idx)
  let dirs := inherited net node (.slotDir idx)
  match rels, dirs with
  | [.depRel rel], [.dir d] => some { depType := rel, dir := d }
  | _, _ => none

/-- Resolve the full argument structure for a word class by collecting
slots 0, 1, 2, ... until one is not found. Uses default inheritance,
so locally specified slots override inherited ones. -/
def resolveArgStr (net : WGNetwork) (wc : String)
    (maxSlots : Nat := 10) : ArgStr :=
  let rec go (idx : Nat) (fuel : Nat) (acc : List ArgSlot) : List ArgSlot :=
    match fuel with
    | 0 => acc.reverse
    | fuel' + 1 =>
      match resolveSlot net wc idx with
      | some slot => go (idx + 1) fuel' (slot :: acc)
      | none => acc.reverse
  { slots := go 0 maxSlots [] }

-- ============================================================================
-- Example: English Auxiliary Network
-- ============================================================================

/-- A WG network encoding the English auxiliary word-class hierarchy,
following @cite{hudson-1984} Ch. 3:

- `verb` has slot 0 = nsubj/left (subject precedes verb by default)
- `transitive` isA `verb`, adds slot 1 = obj/right
- `passive` isA `transitive`, overrides slot 1 to obl/right (by-phrase)
- `auxiliary` isA `verb`, adds slot 1 = aux/right (main verb)
- `interrogative_auxiliary` isA `auxiliary`, overrides slot 0 direction
  to right — the subject follows the auxiliary in questions

The last point is the key to subject-auxiliary inversion: the interrogative
auxiliary is a *subtype* of auxiliary that locally overrides the subject's
position. Default inheritance does the rest — the interrogative auxiliary
inherits nsubj from `verb` (via `auxiliary`) but gets direction = right
from its own local specification. (@cite{hudson-1984} pp. 117-118)
-/
def englishAuxNet : WGNetwork := {
  links := [
    -- Taxonomy
    isALink "transitive" "verb",
    isALink "auxiliary" "verb",
    isALink "passive" "transitive",
    isALink "interrogative_auxiliary" "auxiliary",

    -- verb: slot 0 = nsubj/left (subject precedes by default)
    argSlotLink "verb" 0 .nsubj,
    slotDirLink "verb" 0 .left,

    -- transitive: slot 1 = obj/right
    argSlotLink "transitive" 1 .obj,
    slotDirLink "transitive" 1 .right,

    -- passive: override slot 1 = obl/right (by-phrase replaces direct obj)
    argSlotLink "passive" 1 .obl,
    slotDirLink "passive" 1 .right,

    -- auxiliary: slot 1 = aux/right (main verb follows)
    argSlotLink "auxiliary" 1 .aux,
    slotDirLink "auxiliary" 1 .right,

    -- interrogative_auxiliary: override slot 0 direction to right
    -- (subject follows auxiliary in questions)
    slotDirLink "interrogative_auxiliary" 0 .right
  ]
}

-- ============================================================================
-- Theorems: Default Inheritance
-- ============================================================================

/-- A transitive verb inherits nsubj/left from `verb` and adds obj/right
locally — the network-derived argStr matches the manual `argStr_VN`
(modulo optional fields that default). -/
theorem network_transitive_slot0 :
    resolveSlot englishAuxNet "transitive" 0 =
      some { depType := .nsubj, dir := .left } := by native_decide

theorem network_transitive_slot1 :
    resolveSlot englishAuxNet "transitive" 1 =
      some { depType := .obj, dir := .right } := by native_decide

/-- A passive verb's locally specified slot 1 (obl/right) overrides the
inherited transitive slot 1 (obj/right) — default inheritance in action. -/
theorem bestFit_passive_overrides :
    resolveSlot englishAuxNet "passive" 1 =
      some { depType := .obl, dir := .right } := by native_decide

/-- The non-inverted auxiliary inherits nsubj/left from `verb` for slot 0. -/
theorem network_aux_slot0 :
    resolveSlot englishAuxNet "auxiliary" 0 =
      some { depType := .nsubj, dir := .left } := by native_decide

/-- The network-derived arg structure for a transitive verb has the same
slots as the manually defined `argStr_VN`. -/
theorem network_argStr_matches_manual :
    (resolveArgStr englishAuxNet "transitive").slots =
      [{ depType := .nsubj, dir := .left },
       { depType := .obj, dir := .right }] := by native_decide

-- ============================================================================
-- Theorems: Subject-Auxiliary Inversion via Subtype Inheritance
-- ============================================================================

/-- The interrogative auxiliary inherits nsubj from `verb` (via `auxiliary`)
but its locally specified direction (right) overrides the inherited
direction (left). This is Hudson's subtype analysis of inversion:
the interrogative auxiliary is not a separate lexical rule — it's a
word-class subtype. -/
theorem inversion_by_subtype :
    -- Non-inverted: auxiliary gets nsubj/left (inherited from verb)
    resolveSlot englishAuxNet "auxiliary" 0 =
      some { depType := .nsubj, dir := .left } ∧
    -- Inverted: interrogative_auxiliary overrides direction to right
    resolveSlot englishAuxNet "interrogative_auxiliary" 0 =
      some { depType := .nsubj, dir := .right } := by
  constructor <;> native_decide

/-- The interrogative auxiliary inherits its main-verb slot (aux/right)
from `auxiliary` without overriding it — only the subject direction
changes. -/
theorem interrogative_aux_inherits_main_verb_slot :
    resolveSlot englishAuxNet "interrogative_auxiliary" 1 =
      some { depType := .aux, dir := .right } := by native_decide

/-- The full argument structure for the non-inverted auxiliary:
nsubj/left (inherited from verb) + aux/right (local). -/
theorem network_aux_argStr :
    (resolveArgStr englishAuxNet "auxiliary").slots =
      [{ depType := .nsubj, dir := .left },
       { depType := .aux, dir := .right }] := by native_decide

/-- The full argument structure for the interrogative (inverted) auxiliary:
nsubj/right (local override) + aux/right (inherited from auxiliary). -/
theorem network_interrogative_aux_argStr :
    (resolveArgStr englishAuxNet "interrogative_auxiliary").slots =
      [{ depType := .nsubj, dir := .right },
       { depType := .aux, dir := .right }] := by native_decide

-- ============================================================================
-- Clause-Type → Word-Class Mapping and Network Licensing
-- ============================================================================

/-- Map clause type to the word class that licenses the auxiliary in that
context. Matrix questions require an interrogative auxiliary (subject follows);
all other clause types use the default auxiliary (subject precedes). -/
def wordClassForClauseType : ClauseForm → String
  | .matrixQuestion => "interrogative_auxiliary"
  | _ => "auxiliary"

/-- License a dependency tree via the WG network: look up the word class
for the clause type, resolve its argument structure from the network, and
check the tree satisfies it. This is the end-to-end chain:
`ClauseForm → wordClass → network → argStr → satisfiesArgStr`. -/
def wgLicenses (net : WGNetwork) (t : DepTree) (auxIdx : Nat)
    (ct : ClauseForm) : Bool :=
  satisfiesArgStr t auxIdx (resolveArgStr net (wordClassForClauseType ct))

end DepGrammar.WG
