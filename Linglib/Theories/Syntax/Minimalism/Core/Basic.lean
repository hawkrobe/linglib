/-
# Syntactic Objects and Containment
@cite{chomsky-2013}

Foundation module for the Minimalist Program formalization.

## Syntactic Objects

- `SimpleLI`, `LexicalItem`, `LIToken`, `SyntacticObject`
- `merge`, `externalMerge`, `internalMerge`

## Containment Relations

- **Immediate Containment**: X immediately contains Y iff Y is a member of X
- **Containment (Dominance)**: Transitive closure of immediate containment
- **C-command**: Standard asymmetric relation for binding and locality

-/

import Mathlib.Data.Set.Basic
import Linglib.Core.Lexical.UD

namespace Minimalism

/-- Categorial features (Definition 10) -/
inductive Cat where
  | V     -- verb
  | N     -- noun
  | A     -- adjective
  | P     -- preposition
  | D     -- determiner
  | T     -- tense
  | C     -- complementizer
  | v     -- light verb
  | n     -- nominal categorizer / gender (little-n, @cite{marantz-2001}; Distributed Morphology)
  | a     -- adjectival categorizer (little-a, @cite{panagiotidis-2015}; DegP complement)
  | Place -- locational head (@cite{dendikken-2010}; PlaceP, F1 in adpositional EP)
  | Path  -- directional head (@cite{dendikken-2010} @cite{svenonius-2010}; PathP, F2 in adpositional EP)
  | Num   -- number (@cite{ritter-1991}; NumP between nP and QP/DP)
  | Q     -- quantity / classifier (@cite{borer-2005}; QP between NumP and DP)
  | Voice -- Voice head (@cite{kratzer-1996}; @cite{schaefer-2008})
  | Appl  -- Applicative head (@cite{pylkknen-2008}; @cite{cuervo-2003})
  | Foc   -- focus (@cite{rizzi-1997} split-CP; hosts [FoC] feature, triggers A-bar movement)
  | Top   -- topic (@cite{rizzi-1997} split-CP; hosts [G]/givenness, topic fronting)
  | Fin   -- finiteness (@cite{rizzi-1997} split-CP; allocutive probe in Magahi/Galician)
  | SA    -- speech act head (@cite{speas-tenny-2003}; hosts speaker/addressee)
  | Force -- force (@cite{rizzi-1997} split-CP; clause-typing [decl]/[interrog])
  | Neg   -- negation (@cite{pollock-1989}; @cite{zanuttini-1997}; hosts [±neg])
  | Mod   -- modality (@cite{cinque-1999}; modal auxiliaries)
  | Rel   -- relative (cartographic left periphery, @cite{rizzi-1997})
  | Pol   -- polarity (@cite{laka-1990}; ΣP for affirmation/negation)
  | Asp   -- aspect (@cite{cinque-1999}; inner inflectional, between Voice and T)
  | Evid  -- evidential (@cite{cinque-1999}; outer inflectional, above T below Fin)
  | Nmlz  -- nominalizer (@cite{keine-2020}; Hindi -naa/-ne nominalized clause; clause type distinct from CP)
  | K     -- inherent case shell (@cite{newman-2024}; KP wraps DP for oblique/inherent case; explains no-IO-passive languages)
  deriving Repr, DecidableEq, Inhabited

/-- Selectional stack consumed left-to-right -/
abbrev SelStack := List Cat

/-- A simple LI is a ⟨CAT, SEL⟩ pair (Definition 10), optionally with
    a phonological form for linearization. -/
structure SimpleLI where
  cat : Cat
  sel : SelStack
  phonForm : String := ""
  deriving Repr, DecidableEq

/-- Lexical item (simple or complex from head movement, Definition 88) -/
structure LexicalItem where
  features : List SimpleLI
  nonempty : features ≠ []
  deriving Repr

instance : DecidableEq LexicalItem := λ a b =>
  if h : a.features = b.features then
    isTrue (by cases a; cases b; simp at h; simp [h])
  else
    isFalse (by intro heq; cases heq; exact h rfl)

/-- Create a simple (non-complex) LI -/
def LexicalItem.simple (cat : Cat) (sel : SelStack) (phonForm : String := "") : LexicalItem :=
  ⟨[⟨cat, sel, phonForm⟩], by simp⟩

/-- Get the outer (projecting) category of an LI -/
def LexicalItem.outerCat (li : LexicalItem) : Cat :=
  match li.features with
  | [] => .V  -- unreachable by nonempty constraint
  | s :: _ => s.cat

/-- Get the outer selectional requirements -/
def LexicalItem.outerSel (li : LexicalItem) : SelStack :=
  match li.features with
  | [] => []  -- unreachable
  | s :: _ => s.sel

/-- Is this LI complex (result of head-to-head movement)? -/
def LexicalItem.isComplex (li : LexicalItem) : Bool :=
  li.features.length > 1

/-- Combine two LIs for head-to-head movement (target reprojects) -/
def LexicalItem.combine (target mover : LexicalItem) : LexicalItem :=
  ⟨target.features ++ mover.features, by
    cases htf : target.features with
    | nil => exact absurd htf target.nonempty
    | cons hd tl => simp⟩

/-- LI token: specific instance of an LI in a derivation -/
structure LIToken where
  item : LexicalItem
  id : Nat
  deriving Repr

instance : DecidableEq LIToken := λ a b =>
  if hid : a.id = b.id then
    if hitem : a.item = b.item then
      isTrue (by cases a; cases b; simp at hid hitem; simp [hid, hitem])
    else
      isFalse (by intro heq; cases heq; exact hitem rfl)
  else
    isFalse (by intro heq; cases heq; exact hid rfl)

/-- Syntactic object: LI token or set of two SOs (Definition 11) -/
inductive SyntacticObject where
  | leaf : LIToken → SyntacticObject
  | node : SyntacticObject → SyntacticObject → SyntacticObject
  deriving Repr, DecidableEq

namespace SyntacticObject

def isLeaf : SyntacticObject → Prop
  | .leaf _ => True
  | .node _ _ => False

instance : DecidablePred isLeaf := fun so => by
  cases so <;> unfold isLeaf <;> infer_instance

def isNode : SyntacticObject → Prop
  | .leaf _ => False
  | .node _ _ => True

instance : DecidablePred isNode := fun so => by
  cases so <;> unfold isNode <;> infer_instance

def getLIToken : SyntacticObject → Option LIToken
  | .leaf tok => some tok
  | .node _ _ => none

def getConstituents : SyntacticObject → Option (SyntacticObject × SyntacticObject)
  | .leaf _ => none
  | .node a b => some (a, b)

end SyntacticObject

/-- Merge: the fundamental structure-building operation (Definition 12) -/
def merge (x y : SyntacticObject) : SyntacticObject :=
  .node x y

def validMerge (x y : SyntacticObject) : Prop :=
  x ≠ y

def externalMerge (x y : SyntacticObject) (_h : x ≠ y) : SyntacticObject :=
  merge x y

def internalMerge (target mover : SyntacticObject) (_h : target ≠ mover) : SyntacticObject :=
  merge mover target

/-- Create a leaf SO from category and selection -/
def mkLeaf (cat : Cat) (sel : SelStack) (id : Nat) : SyntacticObject :=
  .leaf ⟨.simple cat sel, id⟩

/-- Create a leaf SO with a phonological form -/
def mkLeafPhon (cat : Cat) (sel : SelStack) (phon : String) (id : Nat) : SyntacticObject :=
  .leaf ⟨.simple cat sel (phonForm := phon), id⟩

/-- Map UD UPOS tags to Minimalist categories.

    This bridges the theory-neutral UD POS tags used in Core/Basic.lean
    and Fragments/ to the Minimalist Cat system. -/
def uposToCat : UD.UPOS → Cat
  | .VERB  => .V
  | .AUX   => .T
  | .NOUN  => .N
  | .PROPN => .N  -- proper nouns are N (but project to DP)
  | .ADJ   => .A
  | .ADP   => .P
  | .DET   => .D
  | .SCONJ => .C
  | .CCONJ => .C
  | _      => .N  -- default

/-- Get the phonological yield of an SO (collect phonForms from leaves) -/
def SyntacticObject.phonYield : SyntacticObject → List String
  | .leaf tok =>
    let phon := tok.item.features.head?.map (·.phonForm) |>.getD ""
    if phon.isEmpty then [] else [phon]
  | .node a b => a.phonYield ++ b.phonYield

/-- Linearize a `SyntacticObject` by collecting leaf `LIToken`s in
    left-to-right traversal order. -/
def linearize : SyntacticObject → List LIToken
  | .leaf tok => [tok]
  | .node l r => linearize l ++ linearize r

/-- Extract the phonological form from an LIToken. -/
def LIToken.phonForm (tok : LIToken) : String :=
  tok.item.features.head?.map (·.phonForm) |>.getD ""

/-- phonYield and linearize agree: phonYield extracts the non-empty
    phonological forms from the linearization. -/
theorem phonYield_eq_linearize (so : SyntacticObject) :
    so.phonYield = (linearize so).filterMap
      (λ tok => let p := tok.phonForm; if p.isEmpty then none else some p) := by
  induction so with
  | leaf tok =>
    simp only [SyntacticObject.phonYield, linearize, LIToken.phonForm]
    simp only [List.filterMap_cons, List.filterMap_nil]
    split <;> simp_all
  | node a b iha ihb =>
    simp only [SyntacticObject.phonYield, linearize, List.filterMap_append, iha, ihb]

/-- Create a trace SO. Traces are leaves with a distinguished sentinel:
    cat = N, sel = [], phonForm = "", and id = index + 10000.
    This encoding is detectable via `isTrace`. -/
def mkTrace (index : Nat) : SyntacticObject :=
  .leaf ⟨.simple .N [] (phonForm := ""), index + 10000⟩

/-- Detect if an SO is a trace (created via mkTrace).
    Returns the trace index if so. -/
def isTrace : SyntacticObject → Option Nat
  | .leaf tok => if tok.id ≥ 10000 then some (tok.id - 10000) else none
  | .node _ _ => none

def exampleVerb : SyntacticObject := mkLeaf .V [.D] 1

def exampleNoun : SyntacticObject := mkLeaf .N [] 2

def exampleDet : SyntacticObject := mkLeaf .D [.N] 3

/-- Count nodes (Merge operations) in an SO -/
def SyntacticObject.nodeCount : SyntacticObject → Nat
  | .leaf _ => 0
  | .node a b => 1 + a.nodeCount + b.nodeCount

def SyntacticObject.leafCount : SyntacticObject → Nat
  | .leaf _ => 1
  | .node a b => a.leafCount + b.leafCount
theorem leaf_node_relation (so : SyntacticObject) :
    so.leafCount = so.nodeCount + 1 := by
  induction so with
  | leaf _ => simp [SyntacticObject.leafCount, SyntacticObject.nodeCount]
  | node a b iha ihb =>
    simp [SyntacticObject.leafCount, SyntacticObject.nodeCount]
    omega

-- ============================================================================
-- Subterm Enumeration
-- ============================================================================

/-- All nodes in a `SyntacticObject`, including the root itself. -/
def SyntacticObject.subtrees : SyntacticObject → List SyntacticObject
  | so@(.leaf _) => [so]
  | so@(.node l r) => so :: (l.subtrees ++ r.subtrees)

/-- The terminal (leaf) nodes of a `SyntacticObject`. -/
def terminalNodes : SyntacticObject → List SyntacticObject
  | so@(.leaf _) => [so]
  | .node l r => terminalNodes l ++ terminalNodes r

/-- Every terminal node is a leaf. -/
theorem terminalNodes_are_leaves {so t : SyntacticObject}
    (h : t ∈ terminalNodes so) : t.isLeaf := by
  induction so with
  | leaf _ =>
    simp only [terminalNodes] at h
    exact List.mem_singleton.mp h ▸ trivial
  | node l r ihl ihr =>
    simp only [terminalNodes, List.mem_append] at h
    exact h.elim ihl ihr

/-- Every terminal is a subtree. -/
theorem terminalNodes_sub_subtrees {so t : SyntacticObject}
    (h : t ∈ terminalNodes so) : t ∈ so.subtrees := by
  induction so with
  | leaf _ =>
    simp only [terminalNodes] at h
    simp only [SyntacticObject.subtrees]
    exact h
  | node l r ihl ihr =>
    simp only [terminalNodes, List.mem_append] at h
    simp only [SyntacticObject.subtrees, List.mem_cons, List.mem_append]
    exact h.elim (fun h => Or.inr (Or.inl (ihl h)))
                 (fun h => Or.inr (Or.inr (ihr h)))

/-- The root is always in its own subtrees. -/
theorem self_mem_subtrees (so : SyntacticObject) : so ∈ so.subtrees := by
  cases so with
  | leaf _ => exact List.mem_cons.mpr (Or.inl rfl)
  | node _ _ => exact List.mem_cons.mpr (Or.inl rfl)

-- ============================================================================
-- Containment Relations
-- ============================================================================

-- Part 1: Immediate Containment (Definition 13)

/-- X immediately contains Y iff Y is a member of X

    "X immediately contains Y iff X = {Y, Z} for some SO Z"

    Since our SOs are binary sets, this means Y is one of the
    two immediate daughters of X. -/
def immediatelyContains (x y : SyntacticObject) : Prop :=
  match x with
  | .leaf _ => False
  | .node a b => y = a ∨ y = b

/-- Decidable immediate containment -/
instance decImmediatelyContains (x y : SyntacticObject) :
    Decidable (immediatelyContains x y) := by
  unfold immediatelyContains
  cases x with
  | leaf _ => exact isFalse (λ h => h)
  | node a b =>
    cases h1 : decide (y = a) with
    | true =>
      simp at h1
      exact isTrue (Or.inl h1)
    | false =>
      simp at h1
      cases h2 : decide (y = b) with
      | true =>
        simp at h2
        exact isTrue (Or.inr h2)
      | false =>
        simp at h2
        exact isFalse (λ h => h.elim h1 h2)

-- Part 2: Containment / Dominance (Definition 14)

/-- Containment is the transitive closure of immediate containment

    "X contains Y iff X immediately contains Y or
    X immediately contains some SO Z such that Z contains Y"

    This is standard syntactic dominance. -/
inductive contains : SyntacticObject → SyntacticObject → Prop where
  | imm : ∀ x y, immediatelyContains x y → contains x y
  | trans : ∀ x y z, immediatelyContains x z → contains z y → contains x y

-- Part 3: Properties of Containment

/-- Immediate containment implies containment -/
theorem imm_implies_contains {x y : SyntacticObject}
    (h : immediatelyContains x y) : contains x y :=
  contains.imm x y h

/-- Containment is transitive -/
theorem contains_trans {x y z : SyntacticObject}
    (hxy : contains x y) (hyz : contains y z) : contains x z := by
  induction hxy with
  | imm x y himm =>
    exact contains.trans x z y himm hyz
  | trans x y w himm _ ih =>
    exact contains.trans x z w himm (ih hyz)

/-- Leaves contain nothing -/
theorem leaf_contains_nothing (tok : LIToken) (y : SyntacticObject) :
    ¬(contains (SyntacticObject.leaf tok) y) := by
  intro h
  cases h with
  | imm _ _ himm =>
    simp [immediatelyContains] at himm
  | trans _ _ z himm _ =>
    simp [immediatelyContains] at himm

-- Part 3b: Well-Foundedness via nodeCount

/-- Immediate containment strictly decreases nodeCount -/
theorem immediatelyContains_lt_nodeCount {x y : SyntacticObject}
    (h : immediatelyContains x y) : y.nodeCount < x.nodeCount := by
  cases x with
  | leaf _ => simp [immediatelyContains] at h
  | node a b =>
    simp only [immediatelyContains] at h
    simp only [SyntacticObject.nodeCount]
    rcases h with rfl | rfl
    · omega
    · omega

/-- Containment strictly decreases nodeCount -/
theorem contains_lt_nodeCount {x y : SyntacticObject}
    (h : contains x y) : y.nodeCount < x.nodeCount := by
  induction h with
  | imm x y himm =>
    exact immediatelyContains_lt_nodeCount himm
  | trans x y z himm _ ih =>
    have h1 := immediatelyContains_lt_nodeCount himm
    omega

/-- No element contains itself (containment is irreflexive) -/
theorem contains_irrefl (x : SyntacticObject) : ¬contains x x := by
  intro h
  have hlt := contains_lt_nodeCount h
  exact Nat.lt_irrefl _ hlt

-- Part 3c: Boolean Containment (for decidability)

/-- Boolean containment check: does `x` (strictly) contain `y`? -/
def containsB : SyntacticObject → SyntacticObject → Bool
  | .leaf _, _ => false
  | .node a b, y => a == y || b == y || containsB a y || containsB b y

/-- `containsB` implies `contains`. -/
theorem containsB_implies_contains {x y : SyntacticObject}
    (h : containsB x y = true) : contains x y := by
  induction x with
  | leaf _ => simp [containsB] at h
  | node a b iha ihb =>
    simp only [containsB, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with ((rfl | rfl) | ha) | hb
    · exact contains.imm _ _ (Or.inl rfl)
    · exact contains.imm _ _ (Or.inr rfl)
    · exact contains.trans _ _ a (Or.inl rfl) (iha ha)
    · exact contains.trans _ _ b (Or.inr rfl) (ihb hb)

/-- `contains` implies `containsB`. -/
theorem contains_implies_containsB {x y : SyntacticObject}
    (h : contains x y) : containsB x y = true := by
  induction h with
  | imm x y himm =>
    cases x with
    | leaf _ => exact absurd himm id
    | node a b =>
      simp only [containsB, Bool.or_eq_true, beq_iff_eq]
      rcases himm with rfl | rfl
      · exact Or.inl (Or.inl (Or.inl rfl))
      · exact Or.inl (Or.inl (Or.inr rfl))
  | trans x _ z himm _ ih =>
    cases x with
    | leaf _ => exact absurd himm id
    | node a b =>
      simp only [containsB, Bool.or_eq_true, beq_iff_eq]
      rcases himm with rfl | rfl
      · exact Or.inl (Or.inr ih)
      · exact Or.inr ih

/-- Boolean and propositional containment are equivalent. -/
theorem containsB_iff {x y : SyntacticObject} :
    containsB x y = true ↔ contains x y :=
  ⟨containsB_implies_contains, contains_implies_containsB⟩

/-- Containment is decidable (derived from the Boolean predicate). -/
instance decContains (x y : SyntacticObject) : Decidable (contains x y) :=
  decidable_of_iff (containsB x y = true) containsB_iff

-- Part 4: Membership in Derivation

/-- X is a term of Y iff X = Y or Y contains X

    "X is a term of SO Y iff X = Y or Y contains X"

    This is useful for stating when an element is "somewhere in" a structure -/
def isTermOf (x y : SyntacticObject) : Prop :=
  x = y ∨ contains y x

/-- Every SO is a term of itself -/
theorem self_is_term (x : SyntacticObject) : isTermOf x x :=
  Or.inl rfl

/-- If Y contains X, then X is a term of Y -/
theorem contained_is_term {x y : SyntacticObject} (h : contains y x) : isTermOf x y :=
  Or.inr h

-- Part 5: Root and Reflexive Containment

/-- Reflexive containment (useful for stating constraints) -/
def containsOrEq (x y : SyntacticObject) : Prop :=
  x = y ∨ contains x y

/-- Every SO reflexively contains itself -/
theorem refl_containsOrEq (x : SyntacticObject) : containsOrEq x x :=
  Or.inl rfl

/-- Reflexive containment is transitive -/
theorem containsOrEq_trans {x y z : SyntacticObject}
    (hxy : containsOrEq x y) (hyz : containsOrEq y z) : containsOrEq x z := by
  rcases hxy with rfl | hxy
  · exact hyz
  · rcases hyz with rfl | hyz
    · exact Or.inr hxy
    · exact Or.inr (contains_trans hxy hyz)

-- Part 6: Tree-Relative Relations
--
-- The tree-free `areSisters` / `cCommands` definitions that were here
-- previously are unsound: sisterhood holds for ANY pair of distinct SOs
-- (witness: `node x y`), making asymmetric c-command trivially false.
-- The tree-relative versions below restrict witnesses to subtrees of a
-- given root, correctly capturing structural asymmetries.

/-- X and Y are sisters IN tree `root`: they are distinct co-daughters of
    some node that is a subtree of `root`. -/
def areSistersIn (root x y : SyntacticObject) : Prop :=
  ∃ z, z ∈ root.subtrees ∧ immediatelyContains z x ∧ immediatelyContains z y ∧ x ≠ y

/-- X c-commands Y IN tree `root`: X has a sister (in `root`) that
    contains-or-equals Y. -/
def cCommandsIn (root x y : SyntacticObject) : Prop :=
  ∃ z, areSistersIn root x z ∧ containsOrEq z y

/-- X asymmetrically c-commands Y in tree `root`. -/
def asymCCommandsIn (root x y : SyntacticObject) : Prop :=
  cCommandsIn root x y ∧ ¬cCommandsIn root y x

-- Part 5d: Boolean C-command (for decidability)

/-- Boolean c-command check: does `x` c-command `y` in tree `root`?

    Searches all subtrees of `root` for a parent node whose children
    include `x` and some sibling `z` where `z` equals or contains `y`.
    Mirrors `cCommandsIn` but is decidable by computation. -/
def cCommandsInB (root x y : SyntacticObject) : Bool :=
  root.subtrees.any λ parent =>
    match parent with
    | .node a b =>
      (a == x && x != y && (b == y || containsB b y)) ||
      (b == x && x != y && (a == y || containsB a y))
    | .leaf _ => false

/-! ## Tree Shape — abstract geometry ignoring terminal labels -/

/-- Abstract tree geometry: the shape of a `SyntacticObject` with all
    terminal labels erased. Two SOs are structurally isomorphic iff
    they have the same `TreeShape`. -/
inductive TreeShape where
  | leaf : TreeShape
  | node : TreeShape → TreeShape → TreeShape
  deriving Repr, DecidableEq

/-- Strip labels from a syntactic object, yielding its abstract shape. -/
def SyntacticObject.shape : SyntacticObject → TreeShape
  | .leaf _ => .leaf
  | .node l r => .node l.shape r.shape

/-- Two syntactic objects are structurally isomorphic iff they have
    the same tree shape (ignoring all terminal labels). -/
def structurallyIsomorphic (x y : SyntacticObject) : Bool :=
  x.shape == y.shape

end Minimalism
