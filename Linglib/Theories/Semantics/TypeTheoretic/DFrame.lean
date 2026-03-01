/-!
# D-Frames: Functional Attribute Structures @cite{loebner-2021}
@cite{osswald-kallmeyer-2018} @cite{petersen-2007}

Löbner (2021) "Frames at the Interface of Language and Cognition"
(Annual Review of Linguistics 7: 261–284) defines **D-frames**
(Düsseldorf frames): typed attributed structures where every attribute
is a *function* — each possessor has exactly one value per attribute.

Three core mechanisms:

1. **Functional attributes** (§1.4.1): attributes are functions, not relations.
   "The price of the book" = PRICE applied to the book node.

2. **Perspective shift** (§3.1.1): different words can share the same underlying
   frame but designate different nodes as *central* (the referential argument).
   *price*, *cheap*, *cost* all access one PRICE frame.

3. **Composition by unification** (§4.1): two partial frames combine by
   merging compatible attribute assignments. Unlike Montague's FA (one
   daughter is a function over the other's type), unification is symmetric.

## Connections

- `Frame2` (FrameBridge.lean) is a two-attribute D-frame
- `ThematicFrame` (Events/ThematicRoles.lean) is a D-frame whose
  attributes are thematic role names — the neo-Davidsonian insight
  that theta roles are *functional* (each event has at most one agent)
  is exactly Löbner's functional-attribute constraint
- HPSG `Sign` (Syntax/HPSG/Core/Basic.lean) is a D-frame with
  attributes CAT, HEAD, VAL
- See `Comparisons/FrameComposition.lean` for formal comparisons

-/

namespace Semantics.TypeTheoretic

-- ════════════════════════════════════════════════════
-- § 1. D-Frame Type
-- ════════════════════════════════════════════════════

/-- A D-frame: a partial function from attributes to values with a
    designated central node (Löbner 2014; 2021 §1.4).

    Attributes are *functional* — each maps to at most one value.
    `central` designates the *referential argument*: the node that
    the lexical item "refers to" or "is about."

    Use a sum type for `Val` when attributes have heterogeneous types. -/
structure DFrame (Attr Val : Type) where
  /-- The referential argument (central node) -/
  central : Val
  /-- Functional attribute access -/
  get : Attr → Option Val

-- ════════════════════════════════════════════════════
-- § 2. Perspective Shift (§3)
-- ════════════════════════════════════════════════════

/-- Perspective shift: re-designate the central node, preserving all
    attributes. *price* vs *cheap* vs *cost* are the same frame with
    different central nodes. Metonymy is a special case (§3.2.1):
    *opera* can refer to the dramatic work, a score, or a performance —
    same underlying frame, different central node (Figure 5a). -/
def DFrame.reanchor {Attr Val : Type} (f : DFrame Attr Val) (v : Val) :
    DFrame Attr Val :=
  { f with central := v }

/-- Reanchoring preserves all attributes. -/
theorem DFrame.reanchor_preserves {Attr Val : Type}
    (f : DFrame Attr Val) (v : Val) (a : Attr) :
    (f.reanchor v).get a = f.get a := rfl

-- ════════════════════════════════════════════════════
-- § 3. Frame Unification (§3.2.2, §4.1)
-- ════════════════════════════════════════════════════

/-- Merge two frames by combining attribute assignments (left-biased).
    The left frame's central node is preserved (it is the "head").

    Löbner's unification is symmetric and fails on conflict (§4.1.1);
    this simplified variant is left-biased (left frame wins on conflict).
    For compatible frames the two are equivalent. -/
def DFrame.unify {Attr Val : Type} (f g : DFrame Attr Val) :
    DFrame Attr Val where
  central := f.central
  get := fun a => f.get a <|> g.get a

/-- Unification with an attributeless frame is identity. -/
theorem DFrame.unify_empty_right {Attr Val : Type}
    (f : DFrame Attr Val) (c : Val) :
    ∀ (a : Attr), (f.unify ⟨c, fun _ => none⟩).get a = f.get a := by
  intro a; show (f.get a <|> none) = f.get a
  cases f.get a <;> rfl

/-- Unification preserves all left-frame attributes. -/
theorem DFrame.unify_left_defined {Attr Val : Type}
    (f g : DFrame Attr Val) (a : Attr) (v : Val)
    (h : f.get a = some v) :
    (f.unify g).get a = some v := by
  show (f.get a <|> g.get a) = some v; rw [h]; rfl

/-- Two frames are compatible on a given attribute set iff they agree
    on all jointly-defined attributes. -/
def DFrame.compatibleOn {Attr Val : Type} [BEq Val]
    (f g : DFrame Attr Val) (attrs : List Attr) : Bool :=
  attrs.all fun a =>
    match f.get a, g.get a with
    | some v₁, some v₂ => v₁ == v₂
    | _, _ => true

-- ════════════════════════════════════════════════════
-- § 4. Lexical Family: price / cheap / cost (§3)
-- ════════════════════════════════════════════════════

/-! Löbner (2021) §3.1.1, Figure 3: *price*, *cheap*, and *cost* share
    a single underlying PRICE frame with one attribute PRICE mapping a
    commodity (x) to its monetary value (p). They differ in perspective:

    - *price* (noun): referential argument = p (the price value) — Figure 3a
    - *cheap* (adj): perspective shifts to x (the commodity) — Figure 3b
    - *cost* (verb): PRICE becomes two-place with time argument — Figure 3c

    This explains why "The book has a low price," "The book is cheap,"
    and "The book costs little" all access the same conceptual structure. -/

/-- The PRICE concept frame (Figure 3) has a single functional attribute
    PRICE mapping a commodity to its monetary value. This is the simplest
    possible frame: one attribute, two nodes. -/
inductive PriceAttr where
  | price
  deriving DecidableEq, Repr, BEq

/-- Nodes in the PRICE frame: the commodity (x) and its price value (p). -/
inductive PriceNode where
  | commodity   -- x: the object being priced
  | priceVal    -- p: the monetary value
  deriving DecidableEq, Repr, BEq

/-- The shared PRICE frame. PRICE maps the commodity to its value. -/
def priceFrameBase : DFrame PriceAttr PriceNode where
  central := .priceVal
  get | .price => some .priceVal

/-- *price* (noun, Figure 3a): referential argument = the price value (p).
    The noun denotes the monetary value; the commodity is relational. -/
def priceNoun : DFrame PriceAttr PriceNode := priceFrameBase.reanchor .priceVal

/-- *cheap* (adjective, Figure 3b): perspective shifts to the commodity (x).
    "cheap" = "of low price" — same PRICE attribute, different perspective. -/
def cheapAdj : DFrame PriceAttr PriceNode := priceFrameBase.reanchor .commodity

/-- *price* and *cheap* share all attributes (same underlying concept). -/
theorem price_cheap_same_attrs (a : PriceAttr) :
    priceNoun.get a = cheapAdj.get a := by cases a <;> rfl

/-- But they differ in what they denote (different central node). -/
theorem price_cheap_different_central :
    priceNoun.central ≠ cheapAdj.central := by decide

-- ════════════════════════════════════════════════════
-- § 5. Compound Composition via Unification (§3.2.2)
-- ════════════════════════════════════════════════════

/-! Löbner (2021) §3.2.2: N-N compounds compose by frame unification.

    *Value compounds* fill an attribute slot of the head noun:
    "plastic bag" = the 'plastic' main node fills MATERIAL in the 'bag' frame.

    *Argument compounds* fill a relational argument node:
    "book chapter" = the 'book' main node fills the relational argument
    in the 'chapter' frame.

    Both are the same operation — `DFrame.unify`. Neither constituent
    is "the function" (contrast with Montague FA). -/

/-- Attributes for an artifact frame. -/
inductive ArtifactAttr where
  | material | shape | use
  deriving DecidableEq, Repr, BEq

/-- Values for artifact attributes. -/
inductive ArtifactVal where
  | plastic | leather | paper
  | rectangular | round
  | carrying | storage
  deriving DecidableEq, Repr, BEq

/-- Base *bag* frame: shape and use specified, material open. -/
def bagFrame : DFrame ArtifactAttr ArtifactVal where
  central := .rectangular
  get
    | .shape    => some .rectangular
    | .material => none
    | .use      => some .carrying

/-- *plastic* modifier frame: specifies only material. -/
def plasticMod : DFrame ArtifactAttr ArtifactVal where
  central := .plastic
  get
    | .material => some .plastic
    | _         => none

/-- "plastic bag" = head noun frame unified with modifier frame. -/
def plasticBag : DFrame ArtifactAttr ArtifactVal := bagFrame.unify plasticMod

/-- Unification fills the MATERIAL slot. -/
theorem plasticBag_material :
    plasticBag.get .material = some .plastic := rfl

/-- Head noun's central node and existing attributes are preserved. -/
theorem plasticBag_preserves_head :
    plasticBag.central = bagFrame.central ∧
    plasticBag.get .shape = bagFrame.get .shape ∧
    plasticBag.get .use = bagFrame.get .use := ⟨rfl, rfl, rfl⟩

/-- The frames are compatible: no conflicting attribute values. -/
theorem bag_plastic_compatible :
    DFrame.compatibleOn bagFrame plasticMod
      [.material, .shape, .use] = true := rfl

-- ════════════════════════════════════════════════════
-- § 6. Nondeterministic Composition (§4.1.2)
-- ════════════════════════════════════════════════════

/-! Löbner (2021) §4.1.2: composition by unification is not always
    deterministic. The color adjective *red* unifies with any node
    of type VISIBLE OBJECT in the pencil frame (Figure 2). Since
    three nodes satisfy this type constraint — the coating of the
    casing, the casing itself, and the pigment of the core — *red
    pencil* has three equally legitimate readings (p. 273).

    Montague FA is deterministic: one function applied to one argument
    yields exactly one result. Frame unification can yield multiple
    results because it is guided by type constraints, not syntactic
    function-argument structure. -/

/-- Parts of a pencil frame (simplified from Figure 2). -/
inductive PencilPart where
  | coating   -- coating of the casing
  | casing    -- the wooden casing
  | pigment   -- pigment of the core
  | core      -- the graphite core
  | pencil    -- the pencil (main node)
  deriving DecidableEq, Repr, BEq

/-- A pencil part is a valid COLOR unification target iff it is a
    visible object (type constraint from §4.1.2). -/
def PencilPart.isVisibleObject : PencilPart → Bool
  | .coating => true
  | .casing  => true
  | .pigment => true
  | _        => false

/-- *red pencil* admits exactly three readings: the pencil frame has
    three nodes satisfying the type constraint VISIBLE OBJECT (§4.1.2,
    p. 273). FA would yield exactly one reading. -/
theorem red_pencil_three_readings :
    ([PencilPart.coating, .casing, .pigment, .core, .pencil].filter
      (·.isVisibleObject)).length = 3 := rfl

end Semantics.TypeTheoretic
