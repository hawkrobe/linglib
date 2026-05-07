import Mathlib.Data.Set.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.Free
import Linglib.Core.UD
import Linglib.Core.Combinatorics.RootedTree.Decorated

/-!
# Syntactic Objects and Containment
@cite{chomsky-2013} @cite{marcolli-chomsky-berwick-2025}

Foundation module for the Minimalist Program formalization.

## Syntactic Objects

`SyntacticObject` is `FreeMagma LIToken`: bare phrase structure as the
free magma over lexical-item tokens, following @cite{marcolli-chomsky-berwick-2025}.
The two constructors are `FreeMagma.of` (lexical leaves) and
`FreeMagma.mul` (binary Merge). The shims `SyntacticObject.leaf` /
`SyntacticObject.node` rename them at the linguistic interface.

The Y-model branches by *map*, not by *type*: PF lives natively on
`SyntacticObject` via `linearize`/`phonYield`; the LF lift to
`Tree Unit String` lives in `SpellOut.lean` (`SyntacticObject.toLFTree`),
which handles trace detection and phonForm extraction.

- `SimpleLI`, `LexicalItem`, `LIToken`, `SyntacticObject`
- `merge`, `externalMerge`, `internalMerge`

## Containment Relations

- **Immediate Containment**: X immediately contains Y iff Y is a member of X
- **Containment (Dominance)**: Transitive closure of immediate containment
- **C-command**: Standard asymmetric relation for binding and locality

-/

namespace Minimalist

/-- Categorial features (Definition 10).

    Enumerates the head categories of the Minimalist Program clausal
    spine and nominal extended projection: cartographic left periphery,
    inflectional spine, v/Voice/Appl event-structure layer, nominal
    categorizer-and-quantity sequence, and adpositional Place/Path
    articulation. -/
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
  | Appl  -- Applicative head (@cite{pylkkanen-2008}; @cite{cuervo-2003})
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

/-- Syntactic object: nonplanar binary tree over `LIToken ⊕ Nat`,
    realized as `FreeCommMagma (LIToken ⊕ Nat)`.

Per @cite{marcolli-chomsky-berwick-2025} Definition 1.1.1 (book p. 22),
SO is the **free, non-associative, commutative** magma `Magma_{na,c}(SO_0, M)`
with `M(α,β) = {α,β}` (unordered). Linguistically, this is the position that
Merge produces unordered sets, with linearization (PF / LCA / head-directionality)
as a separate Externalization step.

The three "constructors" at the SO interface are:

- `.leaf tok` — a lexical leaf, encoded as `FreeCommMagma.of (.inl tok)`
- `.trace n` — a trace marker, encoded as `FreeCommMagma.of (.inr n)`
- binary Merge, written `l * r` (commutative: `l * r = r * l` as a strict
  equality inside the quotient)

### Trace handling: linglib commits to MCB's ^ρ-projection (with indexing)

MCB's SO_0 (book p. 22, Def 1.1.1) consists of *lexical items and syntactic
features only* — not trace markers. After Internal Merge extracts an accessible
term, MCB enumerates **three** forms of remainder (Defs 1.2.5–1.2.8, p. 31–35):

- `T/^c F_v` (contraction) — extracted term becomes a "deeper copy", visible
  to semantics but cancelled at PF
- `T/^d F_v` (deletion) — edge contraction collapses the position, no marker
- `T/^ρ F_v` (admissible cut) — an unlabeled structural vertex remains as the
  trace, used by the combined process

Linglib's `SyntacticObject := FreeCommMagma (LIToken ⊕ Nat)` is a substrate-
level commitment to **the ^ρ-projection with explicit indexing**: `Sum.inr n`
is a trace vertex tagged with which mover produced it. MCB's ^ρ vertex is
unlabeled; linglib enriches it with a `Nat` index for cross-reference.

This is faithful to MCB's framework — it instantiates one of the three
quotients MCB explicitly enumerates, not a deviation. Documented as a Phase 2+
upgrade target: a future revision could expose all three projections as
separate views of a workspace-level IM operation, with the SO type itself
being `FreeCommMagma LIToken` (trace-free); current trace-marker operations
would become projection-side rather than substrate. See the project memory
note `project_so_carrier_rho_projection.md`.

The migration from the prior planar `TraceTree LIToken Nat` carrier landed
at version 0.230.857 (Phase 0.5 substrate) + 0.230.858 (mathlib-canonical
`DecidableEq` via `CommEqv`, no `LinearOrder` needed). See
`docs/nonplanar-migration-plan.md` and `Linglib/Scratch/PreLiePlanarCheck.lean`
(counterexample showing the §1.7 pre-Lie identity is FALSE on planar trees,
the headline reason for nonplanarity).

For LF composition, see `SyntacticObject.toLFTree`. -/
abbrev SyntacticObject : Type := FreeCommMagma (LIToken ⊕ Nat)

namespace SyntacticObject

/-- Leaf shim: `SyntacticObject.leaf tok ≡ FreeCommMagma.of (.inl tok)`. -/
abbrev leaf (tok : LIToken) : SyntacticObject :=
  FreeCommMagma.of (.inl tok)

/-- Trace shim: `SyntacticObject.trace n ≡ FreeCommMagma.of (.inr n)`. -/
abbrev trace (n : Nat) : SyntacticObject :=
  FreeCommMagma.of (.inr n)

/-- Binary-Merge shim: `SyntacticObject.mul l r ≡ l * r`. The construction
    side of binary Merge; `*` is commutative on `SyntacticObject`. -/
abbrev mul (l r : SyntacticObject) : SyntacticObject := l * r

/-- Construction-only alias `.node l r ≡ mul l r ≡ l * r`. Pattern
    matching against `.node` does NOT work (the carrier is `Quot _`,
    so Lean cannot invert through it); use `induction so with | mul l r ihl ihr`
    instead. Retained as a construction shim to keep call sites readable
    during the `TraceTree → FreeCommMagma` migration. -/
abbrev node (l r : SyntacticObject) : SyntacticObject := mul l r

/-- The induction principle for `SyntacticObject` with linguistic case names.
    For `Prop` motives, `Quot.ind` propagates through the equivalence
    automatically — no swap-respect obligation needed. The `mul` case must
    cover both orderings (since `l * r = r * l`), which `Quot.ind` handles
    transparently for propositional motives. -/
@[elab_as_elim, induction_eliminator]
protected theorem ind {motive : SyntacticObject → Prop}
    (leaf : ∀ tok, motive (.leaf tok))
    (trace : ∀ n, motive (.trace n))
    (mul : ∀ l r, motive l → motive r → motive (l * r))
    : ∀ so, motive so := by
  intro so
  induction so using FreeCommMagma.ind with
  | _ fm =>
    induction fm with
    | ih1 x =>
      cases x with
      | inl tok => exact leaf tok
      | inr n => exact trace n
    | ih2 l r ihl ihr => exact mul (Quot.mk _ l) (Quot.mk _ r) ihl ihr

/-- Two-argument version of `ind`. Useful for theorems about pairs of SOs. -/
@[elab_as_elim]
protected theorem ind₂ {motive : SyntacticObject → SyntacticObject → Prop}
    (h : ∀ a b : FreeMagma (LIToken ⊕ Nat),
        motive (Quot.mk _ a) (Quot.mk _ b))
    (s t : SyntacticObject) : motive s t :=
  FreeCommMagma.inductionOn₂ s t h

/-! ### Predicates

Each predicate is defined via `FreeCommMagma.lift` from a swap-respecting
helper on the underlying `FreeMagma`. The `_leaf` / `_trace` / `_mul` simp
lemmas unfold cleanly. -/

private def isLeafAux : FreeMagma (LIToken ⊕ Nat) → Prop
  | .of _ => True
  | .mul _ _ => False

private theorem isLeafAux_respects (a b : FreeMagma (LIToken ⊕ Nat))
    (h : FreeMagma.CommRel a b) : isLeafAux a = isLeafAux b := by
  induction h <;> rfl

def isLeaf : SyntacticObject → Prop :=
  FreeCommMagma.lift isLeafAux isLeafAux_respects

@[simp] theorem isLeaf_leaf (tok : LIToken) : isLeaf (.leaf tok) ↔ True := by
  unfold isLeaf leaf; rfl

@[simp] theorem isLeaf_trace (n : Nat) : isLeaf (.trace n) ↔ True := by
  unfold isLeaf trace; rfl

@[simp] theorem isLeaf_mul (l r : SyntacticObject) : ¬ isLeaf (l * r) := by
  induction l using FreeCommMagma.ind with | _ a =>
    induction r using FreeCommMagma.ind with | _ b => exact id

instance : DecidablePred isLeaf := fun so =>
  Quot.recOnSubsingleton (motive := fun so => Decidable (isLeaf so))
    so fun fm => match fm with
      | .of _ => isTrue trivial
      | .mul _ _ => isFalse id

private def isNodeAux : FreeMagma (LIToken ⊕ Nat) → Prop
  | .of _ => False
  | .mul _ _ => True

private theorem isNodeAux_respects (a b : FreeMagma (LIToken ⊕ Nat))
    (h : FreeMagma.CommRel a b) : isNodeAux a = isNodeAux b := by
  induction h <;> rfl

def isNode : SyntacticObject → Prop :=
  FreeCommMagma.lift isNodeAux isNodeAux_respects

@[simp] theorem isNode_leaf (tok : LIToken) : ¬ isNode (.leaf tok) := id
@[simp] theorem isNode_trace (n : Nat) : ¬ isNode (.trace n) := id
@[simp] theorem isNode_mul (l r : SyntacticObject) : isNode (l * r) := by
  induction l using FreeCommMagma.ind with | _ a =>
    induction r using FreeCommMagma.ind with | _ b => trivial

instance : DecidablePred isNode := fun so =>
  Quot.recOnSubsingleton (motive := fun so => Decidable (isNode so))
    so fun fm => match fm with
      | .of _ => isFalse id
      | .mul _ _ => isTrue trivial

/-- Get the lexical token if this SO is a leaf (not a trace nor a node). -/
private def getLITokenAux : FreeMagma (LIToken ⊕ Nat) → Option LIToken
  | .of (.inl tok) => some tok
  | .of (.inr _) => none
  | .mul _ _ => none

private theorem getLITokenAux_respects (a b : FreeMagma (LIToken ⊕ Nat))
    (h : FreeMagma.CommRel a b) : getLITokenAux a = getLITokenAux b := by
  induction h <;> rfl

def getLIToken : SyntacticObject → Option LIToken :=
  FreeCommMagma.lift getLITokenAux getLITokenAux_respects

@[simp] theorem getLIToken_leaf (tok : LIToken) :
    getLIToken (.leaf tok) = some tok := rfl
@[simp] theorem getLIToken_trace (n : Nat) :
    getLIToken (.trace n) = none := rfl
@[simp] theorem getLIToken_mul (l r : SyntacticObject) :
    getLIToken (l * r) = none := by
  induction l using FreeCommMagma.ind with | _ a =>
    induction r using FreeCommMagma.ind with | _ b => rfl

end SyntacticObject

/-- Merge: the fundamental structure-building operation. Equal to
    `FreeCommMagma.mul` and to `(· * ·)`. Commutative: `merge x y = merge y x`
    as a strict equality on the quotient. -/
def merge (x y : SyntacticObject) : SyntacticObject :=
  x * y

def validMerge (x y : SyntacticObject) : Prop :=
  x ≠ y

def externalMerge (x y : SyntacticObject) (_h : x ≠ y) : SyntacticObject :=
  merge x y

def internalMerge (target mover : SyntacticObject) (_h : target ≠ mover) : SyntacticObject :=
  merge mover target

/-- Create a leaf SO from category and selection -/
def mkLeaf (cat : Cat) (sel : SelStack) (id : Nat) : SyntacticObject :=
  SyntacticObject.leaf ⟨.simple cat sel, id⟩

/-- Create a leaf SO with a phonological form -/
def mkLeafPhon (cat : Cat) (sel : SelStack) (phon : String) (id : Nat) : SyntacticObject :=
  SyntacticObject.leaf ⟨.simple cat sel (phonForm := phon), id⟩

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

/-! ### Linearization-dependent operations (Phase 1.0 placeholder)

`phonYield`, `linearize`, `leftmostLeaf`, `outerCat` traverse the SO in
**planar order**, which is a representative-choice over the unordered
quotient. Per @cite{marcolli-chomsky-berwick-2025} Remark 1.1.2 (book p. 23),
linearization belongs to *Externalization*, not to Merge proper.

Phase 1.0 placeholder: pick an arbitrary representative via `Quot.out` and
traverse it on the underlying `FreeMagma`. **Noncomputable** because
`Quot.out` uses `Classical.choose`. Phase 2 of the migration replaces this
with a head-marking + head-directionality parameter (LCA), making
linearization a parameterized choice rather than an arbitrary one. -/

/-- Trace marker token: synthesized when traversal needs an LIToken at a
    `.trace n` position. Encodes the trace index in the id field
    (sentinel ≥ 10000), preserving backward-compat for code that inspects
    `tok.id`. -/
def mkTraceToken (index : Nat) : LIToken :=
  ⟨.simple .N [] (phonForm := ""), index + 10000⟩

/-- Underlying phonological yield on a planar `FreeMagma` representative. -/
private def phonYieldPlanar : FreeMagma (LIToken ⊕ Nat) → List String
  | .of (.inl tok) =>
    let phon := tok.item.features.head?.map (·.phonForm) |>.getD ""
    if phon.isEmpty then [] else [phon]
  | .of (.inr _) => []
  | .mul a b => phonYieldPlanar a ++ phonYieldPlanar b

/-- Phonological yield of an SO. Order depends on the chosen planar
    representative (Phase 1.0 placeholder via `Quot.out`); Phase 2
    replaces this with LCA-derived linearization. -/
noncomputable def SyntacticObject.phonYield (so : SyntacticObject) : List String :=
  phonYieldPlanar so.out

/-- Underlying linearization on a planar `FreeMagma` representative. -/
private def linearizePlanar : FreeMagma (LIToken ⊕ Nat) → List LIToken
  | .of (.inl tok) => [tok]
  | .of (.inr _) => []
  | .mul l r => linearizePlanar l ++ linearizePlanar r

/-- Linearize an SO by collecting leaf tokens in the chosen planar order.
    Phase 1.0 placeholder via `Quot.out`; Phase 2 replaces with LCA. -/
noncomputable def linearize (so : SyntacticObject) : List LIToken :=
  linearizePlanar so.out

/-- Underlying leftmost-leaf on a planar `FreeMagma` representative. -/
private def leftmostLeafPlanar : FreeMagma (LIToken ⊕ Nat) → LIToken
  | .of (.inl tok) => tok
  | .of (.inr n) => mkTraceToken n
  | .mul l _ => leftmostLeafPlanar l

/-- The leftmost leaf of a `SyntacticObject` under the chosen planar
    representative. Phase 1.0 placeholder via `Quot.out`; Phase 2 replaces
    with head-marking-aware projection.

    **M-C-B alignment** (@cite{marcolli-chomsky-berwick-2025} §1.13.3,
    §1.15): in NEW Minimalism, head functions are *external* and *partial*
    — defined only on `Dom(h) ⊂ SO`. This accessor is the partial extension
    to all values via the leftmost-leaf heuristic, valid only when the
    chosen planar representative happens to put the head on the left. For
    derivation-based code, prefer `Derivation.outerCat?` (in
    `Selection.lean`), which is **total** on leaf-initial derivations
    because head info is tracked through the derivation history rather than
    recovered from the tree. The full formalism (head function + Labeling
    Algorithm) lives in `Theories/Syntax/Minimalism/HeadFunction.lean`. -/
noncomputable def SyntacticObject.leftmostLeaf (so : SyntacticObject) : LIToken :=
  leftmostLeafPlanar so.out

/-- For a leaf SO, the leftmost-leaf is the leaf itself — the
    equivalence class is a singleton, so `Quot.out` cannot pick a
    different representative. Lifts the singleton structure through
    `mk_eq_iff_commEqv`. -/
@[simp] theorem SyntacticObject.leftmostLeaf_leaf (tok : LIToken) :
    (SyntacticObject.leaf tok).leftmostLeaf = tok := by
  show leftmostLeafPlanar (SyntacticObject.leaf tok).out = tok
  have hmk :
      (Quot.mk FreeMagma.CommRel (SyntacticObject.leaf tok).out : SyntacticObject)
        = FreeCommMagma.mk (FreeMagma.of (Sum.inl tok)) := Quot.out_eq _
  rw [FreeCommMagma.mk_eq_iff_commEqv] at hmk
  match h : (SyntacticObject.leaf tok).out with
  | .of x =>
    rw [h] at hmk
    -- hmk : FreeMagma.CommEqv (.of x) (.of (.inl tok)), which unfolds to x = .inl tok
    show leftmostLeafPlanar (.of x) = tok
    cases x with
    | inl t =>
      simp only [leftmostLeafPlanar]
      exact (Sum.inl.inj (hmk : Sum.inl t = Sum.inl tok))
    | inr n => exact absurd (hmk : Sum.inr n = Sum.inl tok) (by intro; contradiction)
  | .mul _ _ =>
    rw [h] at hmk
    exact absurd hmk (by simp [FreeMagma.CommEqv])

/-- For a trace SO, the leftmost-leaf is the synthetic trace token. -/
@[simp] theorem SyntacticObject.leftmostLeaf_trace (n : Nat) :
    (SyntacticObject.trace n).leftmostLeaf = mkTraceToken n := by
  show leftmostLeafPlanar (SyntacticObject.trace n).out = mkTraceToken n
  have hmk :
      (Quot.mk FreeMagma.CommRel (SyntacticObject.trace n).out : SyntacticObject)
        = FreeCommMagma.mk (FreeMagma.of (Sum.inr n)) := Quot.out_eq _
  rw [FreeCommMagma.mk_eq_iff_commEqv] at hmk
  match h : (SyntacticObject.trace n).out with
  | .of x =>
    rw [h] at hmk
    show leftmostLeafPlanar (.of x) = mkTraceToken n
    cases x with
    | inl t => exact absurd (hmk : Sum.inl t = Sum.inr n) (by intro; contradiction)
    | inr m =>
      simp only [leftmostLeafPlanar]
      exact congrArg mkTraceToken (Sum.inr.inj (hmk : Sum.inr m = Sum.inr n))
  | .mul _ _ =>
    rw [h] at hmk
    exact absurd hmk (by simp [FreeMagma.CommEqv])

/-- The outer (projecting) categorial feature of an SO, recovered from the
    leftmost leaf along the left spine of a chosen planar representative. -/
noncomputable def SyntacticObject.outerCat (so : SyntacticObject) : Cat :=
  so.leftmostLeaf.item.outerCat

/-- For a leaf SO, `outerCat` is the leaf's outer category. -/
@[simp] theorem SyntacticObject.outerCat_leaf (tok : LIToken) :
    (SyntacticObject.leaf tok).outerCat = tok.item.outerCat := by
  show (SyntacticObject.leaf tok).leftmostLeaf.item.outerCat = tok.item.outerCat
  rw [leftmostLeaf_leaf]

/-- Extract the phonological form from an LIToken. -/
def LIToken.phonForm (tok : LIToken) : String :=
  tok.item.features.head?.map (·.phonForm) |>.getD ""

/-- Underlying agreement on a planar representative: `phonYield` is the
    non-empty-phonForm filter of `linearize`. -/
private theorem phonYield_eq_linearize_planar (fm : FreeMagma (LIToken ⊕ Nat)) :
    phonYieldPlanar fm = (linearizePlanar fm).filterMap
      (λ tok => let p := tok.phonForm; if p.isEmpty then none else some p) := by
  induction fm with
  | ih1 x =>
    cases x with
    | inl tok =>
      simp only [phonYieldPlanar, linearizePlanar, LIToken.phonForm]
      simp only [List.filterMap_cons, List.filterMap_nil]
      split <;> simp_all
    | inr _ =>
      simp only [phonYieldPlanar, linearizePlanar, List.filterMap_nil]
  | ih2 a b iha ihb =>
    simp only [phonYieldPlanar, linearizePlanar, List.filterMap_append, iha, ihb]

/-- `phonYield` and `linearize` agree: `phonYield` extracts the non-empty
    phonological forms from the linearization. Lifts via the planar
    representative theorem. -/
theorem phonYield_eq_linearize (so : SyntacticObject) :
    so.phonYield = (linearize so).filterMap
      (λ tok => let p := tok.phonForm; if p.isEmpty then none else some p) :=
  phonYield_eq_linearize_planar so.out

/-- Create a trace SO with binding index `index`. Detectable via `isTrace`. -/
def mkTrace (index : Nat) : SyntacticObject :=
  SyntacticObject.trace index

/-- Detect if an SO is a trace. Returns the trace index if so. -/
private def isTraceAux : FreeMagma (LIToken ⊕ Nat) → Option Nat
  | .of (.inr n) => some n
  | .of (.inl _) => none
  | .mul _ _ => none

private theorem isTraceAux_respects (a b : FreeMagma (LIToken ⊕ Nat))
    (h : FreeMagma.CommRel a b) : isTraceAux a = isTraceAux b := by
  induction h <;> rfl

def isTrace : SyntacticObject → Option Nat :=
  FreeCommMagma.lift isTraceAux isTraceAux_respects

@[simp] theorem isTrace_leaf (tok : LIToken) :
    isTrace (.leaf tok) = none := rfl
@[simp] theorem isTrace_trace (n : Nat) :
    isTrace (.trace n) = some n := rfl
@[simp] theorem isTrace_mul (l r : SyntacticObject) :
    isTrace (l * r) = none := by
  induction l using FreeCommMagma.ind with | _ a =>
    induction r using FreeCommMagma.ind with | _ b => rfl

def exampleVerb : SyntacticObject := mkLeaf .V [.D] 1

def exampleNoun : SyntacticObject := mkLeaf .N [] 2

def exampleDet : SyntacticObject := mkLeaf .D [.N] 3

/-- Count Merge nodes in an SO. Traces are leaf-position (count 0 nodes). -/
private def nodeCountAux : FreeMagma (LIToken ⊕ Nat) → Nat
  | .of _ => 0
  | .mul a b => 1 + nodeCountAux a + nodeCountAux b

private theorem nodeCountAux_respects (a b : FreeMagma (LIToken ⊕ Nat))
    (h : FreeMagma.CommRel a b) : nodeCountAux a = nodeCountAux b := by
  induction h with
  | swap _ _ => simp only [nodeCountAux]; omega
  | mul_left _ _ ih => simp only [nodeCountAux]; omega
  | mul_right _ _ ih => simp only [nodeCountAux]; omega

def SyntacticObject.nodeCount : SyntacticObject → Nat :=
  FreeCommMagma.lift nodeCountAux nodeCountAux_respects

@[simp] theorem SyntacticObject.nodeCount_leaf (tok : LIToken) :
    nodeCount (.leaf tok) = 0 := rfl
@[simp] theorem SyntacticObject.nodeCount_trace (n : Nat) :
    nodeCount (.trace n) = 0 := rfl
@[simp] theorem SyntacticObject.nodeCount_mul (l r : SyntacticObject) :
    nodeCount (l * r) = 1 + nodeCount l + nodeCount r := by
  induction l using FreeCommMagma.ind with | _ a =>
    induction r using FreeCommMagma.ind with | _ b => rfl

/-- Count leaves and trace markers. -/
private def leafCountAux : FreeMagma (LIToken ⊕ Nat) → Nat
  | .of _ => 1
  | .mul a b => leafCountAux a + leafCountAux b

private theorem leafCountAux_respects (a b : FreeMagma (LIToken ⊕ Nat))
    (h : FreeMagma.CommRel a b) : leafCountAux a = leafCountAux b := by
  induction h with
  | swap _ _ => simp only [leafCountAux]; omega
  | mul_left _ _ ih => simp only [leafCountAux]; omega
  | mul_right _ _ ih => simp only [leafCountAux]; omega

def SyntacticObject.leafCount : SyntacticObject → Nat :=
  FreeCommMagma.lift leafCountAux leafCountAux_respects

@[simp] theorem SyntacticObject.leafCount_leaf (tok : LIToken) :
    leafCount (.leaf tok) = 1 := rfl
@[simp] theorem SyntacticObject.leafCount_trace (n : Nat) :
    leafCount (.trace n) = 1 := rfl
@[simp] theorem SyntacticObject.leafCount_mul (l r : SyntacticObject) :
    leafCount (l * r) = leafCount l + leafCount r := by
  induction l using FreeCommMagma.ind with | _ a =>
    induction r using FreeCommMagma.ind with | _ b => rfl

theorem leaf_node_relation (so : SyntacticObject) :
    so.leafCount = so.nodeCount + 1 := by
  induction so with
  | leaf _ => rfl
  | trace _ => rfl
  | mul a b iha ihb =>
    simp only [SyntacticObject.leafCount_mul, SyntacticObject.nodeCount_mul, iha, ihb]
    omega

-- ============================================================================
-- Subterm Enumeration
-- ============================================================================

/-! ### Subtree enumeration — `Multiset` (MCB-faithful)

`subtrees` returns a `Multiset` because MCB's accessible-term operator
`Acc(T)` (Def 1.2.2, book p. 28) is multiplicity-preserving — eq (1.2.5)
`#V(F) = b_0(F) + #Acc(F)` requires multiplicities to match. The "set"
notation in MCB is loose; the formal object is indexed by `V_int(T)`,
which is a multiset of vertices (one per non-root vertex, with possibly
repeated subtree values when leaves repeat).

For linglib's typical use (LIToken-indexed leaves with distinct ids),
each subtree is a distinct value, so Multiset and Finset coincide
extensionally. Multiset is preferred for substrate faithfulness.

Multiset addition (`+`) preserves multiplicity (additive union); cons
(`::ₘ`) adds an element regardless of presence. Both are needed. -/

private def subtreesAux : FreeMagma (LIToken ⊕ Nat) → Multiset SyntacticObject
  | a@(.of _) => {FreeCommMagma.mk a}
  | a@(.mul l r) =>
    (FreeCommMagma.mk a) ::ₘ (subtreesAux l + subtreesAux r)

private theorem subtreesAux_respects (a b : FreeMagma (LIToken ⊕ Nat))
    (h : FreeMagma.CommRel a b) : subtreesAux a = subtreesAux b := by
  induction h with
  | swap a b =>
    show (FreeCommMagma.mk (a * b)) ::ₘ (subtreesAux a + subtreesAux b)
       = (FreeCommMagma.mk (b * a)) ::ₘ (subtreesAux b + subtreesAux a)
    rw [FreeCommMagma.swap a b, add_comm]
  | @mul_left a b h_inner c ih =>
    show (FreeCommMagma.mk (a * c)) ::ₘ (subtreesAux a + subtreesAux c)
       = (FreeCommMagma.mk (b * c)) ::ₘ (subtreesAux b + subtreesAux c)
    rw [FreeCommMagma.sound (.mul_left h_inner _), ih]
  | @mul_right a b c h_inner ih =>
    show (FreeCommMagma.mk (a * b)) ::ₘ (subtreesAux a + subtreesAux b)
       = (FreeCommMagma.mk (a * c)) ::ₘ (subtreesAux a + subtreesAux c)
    rw [FreeCommMagma.sound (.mul_right _ h_inner), ih]

/-- All subtrees of a `SyntacticObject`, including the root itself.
    Returns a `Multiset` (multiplicity-preserving), matching MCB Def 1.2.2
    (book p. 28) and supporting eq (1.2.5)'s vertex-counting identity.
    Computable via `FreeCommMagma.lift` from a swap-respecting helper. -/
def SyntacticObject.subtrees : SyntacticObject → Multiset SyntacticObject :=
  FreeCommMagma.lift subtreesAux subtreesAux_respects

@[simp] theorem SyntacticObject.subtrees_leaf (tok : LIToken) :
    (SyntacticObject.leaf tok).subtrees = {SyntacticObject.leaf tok} := rfl

@[simp] theorem SyntacticObject.subtrees_trace (n : Nat) :
    (SyntacticObject.trace n).subtrees = {SyntacticObject.trace n} := rfl

@[simp] theorem SyntacticObject.subtrees_mul (l r : SyntacticObject) :
    (l * r).subtrees = (l * r) ::ₘ (l.subtrees + r.subtrees) := by
  induction l, r using FreeCommMagma.inductionOn₂ with | _ a b => rfl

/-! ### Terminal nodes — planar `List` (order matters for LCA)

`terminalNodes` returns a `List` because the leftmost-to-rightmost
order is the input to LCA-derived linearization. Phase 1.0 placeholder
via `Quot.out` (planar representative); Phase 2 will replace with
LCA + head-directionality. -/

private def terminalNodesPlanar : FreeMagma (LIToken ⊕ Nat) →
    List (FreeMagma (LIToken ⊕ Nat))
  | a@(.of _) => [a]
  | .mul l r => terminalNodesPlanar l ++ terminalNodesPlanar r

/-- The terminal (leaf-position) SOs of a `SyntacticObject`. Order
    depends on the chosen planar representative. -/
noncomputable def terminalNodes (so : SyntacticObject) : List SyntacticObject :=
  (terminalNodesPlanar so.out).map (Quot.mk _)

private theorem terminalNodesPlanar_are_leaves
    {fm t : FreeMagma (LIToken ⊕ Nat)} (h : t ∈ terminalNodesPlanar fm) :
    SyntacticObject.isLeaf (Quot.mk _ t) := by
  induction fm with
  | ih1 _ =>
    simp only [terminalNodesPlanar, List.mem_singleton] at h
    subst h; trivial
  | ih2 l r ihl ihr =>
    simp only [terminalNodesPlanar, List.mem_append] at h
    exact h.elim ihl ihr

/-- Every terminal node is leaf-position. -/
theorem terminalNodes_are_leaves {so t : SyntacticObject}
    (h : t ∈ terminalNodes so) : t.isLeaf := by
  simp only [terminalNodes, List.mem_map] at h
  obtain ⟨a, ha_mem, ha_eq⟩ := h
  rw [← ha_eq]
  exact terminalNodesPlanar_are_leaves ha_mem

/-- For a leaf SO, `terminalNodes` is the singleton list `[.leaf tok]`.
    Same singleton-class argument as `leftmostLeaf_leaf`. -/
@[simp] theorem terminalNodes_leaf (tok : LIToken) :
    terminalNodes (SyntacticObject.leaf tok) = [SyntacticObject.leaf tok] := by
  show (terminalNodesPlanar (SyntacticObject.leaf tok).out).map _ = _
  have hmk :
      (Quot.mk FreeMagma.CommRel (SyntacticObject.leaf tok).out : SyntacticObject)
        = FreeCommMagma.mk (FreeMagma.of (Sum.inl tok)) := Quot.out_eq _
  rw [FreeCommMagma.mk_eq_iff_commEqv] at hmk
  match h : (SyntacticObject.leaf tok).out with
  | .of x =>
    rw [h] at hmk
    show (terminalNodesPlanar (.of x)).map _ = _
    cases x with
    | inl t =>
      simp only [terminalNodesPlanar, List.map_cons, List.map_nil]
      exact congrArg (fun y => [SyntacticObject.leaf y])
        (Sum.inl.inj (hmk : Sum.inl t = Sum.inl tok))
    | inr n => exact absurd (hmk : Sum.inr n = Sum.inl tok) (by intro; contradiction)
  | .mul _ _ =>
    rw [h] at hmk
    exact absurd hmk (by simp [FreeMagma.CommEqv])

private theorem terminalNodesPlanar_mem_subtreesAux
    {fm t : FreeMagma (LIToken ⊕ Nat)} (h : t ∈ terminalNodesPlanar fm) :
    (FreeCommMagma.mk t : SyntacticObject) ∈ subtreesAux fm := by
  induction fm with
  | ih1 _ =>
    simp only [terminalNodesPlanar, List.mem_singleton] at h
    subst h; simp [subtreesAux]
  | ih2 l r ihl ihr =>
    simp only [terminalNodesPlanar, List.mem_append] at h
    simp only [subtreesAux, Multiset.mem_cons, Multiset.mem_add]
    exact h.elim (fun hl => Or.inr (Or.inl (ihl hl)))
                 (fun hr => Or.inr (Or.inr (ihr hr)))

/-- Every terminal is a subtree. -/
theorem terminalNodes_sub_subtrees {so t : SyntacticObject}
    (h : t ∈ terminalNodes so) : t ∈ so.subtrees := by
  simp only [terminalNodes, List.mem_map] at h
  obtain ⟨a, ha_mem, ha_eq⟩ := h
  rw [← ha_eq]
  show (FreeCommMagma.mk a : SyntacticObject) ∈
    FreeCommMagma.lift subtreesAux subtreesAux_respects so
  rw [show so = FreeCommMagma.mk so.out from (Quot.out_eq so).symm]
  simp only [FreeCommMagma.lift_mk]
  exact terminalNodesPlanar_mem_subtreesAux ha_mem

/-- The root is always in its own subtrees. -/
theorem self_mem_subtrees (so : SyntacticObject) : so ∈ so.subtrees := by
  induction so with
  | leaf _ => simp
  | trace _ => simp
  | mul l r _ _ => simp [SyntacticObject.subtrees_mul]

/-- `subtrees` is downward-monotone along the subtree relation: if `t`
    is a subtree of `s` (at any multiplicity), then every subtree of
    `t` is also a subtree of `s` (`Multiset.Subset` ignores
    multiplicity, only membership). -/
theorem subtrees_subset_of_mem {t s : SyntacticObject}
    (h : t ∈ s.subtrees) : t.subtrees ⊆ s.subtrees := by
  induction s with
  | leaf tok =>
    simp only [SyntacticObject.subtrees_leaf, Multiset.mem_singleton] at h
    rw [h]; exact Multiset.Subset.refl _
  | trace n =>
    simp only [SyntacticObject.subtrees_trace, Multiset.mem_singleton] at h
    rw [h]; exact Multiset.Subset.refl _
  | mul l r ihl ihr =>
    simp only [SyntacticObject.subtrees_mul, Multiset.mem_cons,
               Multiset.mem_add] at h
    rcases h with rfl | hl | hr
    · intro _ h; exact h
    · intro x hx
      have := ihl hl hx
      simp only [SyntacticObject.subtrees_mul, Multiset.mem_cons,
                 Multiset.mem_add]
      exact Or.inr (Or.inl this)
    · intro x hx
      have := ihr hr hx
      simp only [SyntacticObject.subtrees_mul, Multiset.mem_cons,
                 Multiset.mem_add]
      exact Or.inr (Or.inr this)

-- ============================================================================
-- Containment Relations
-- ============================================================================

-- Part 1: Immediate Containment (Definition 13)

/-- X immediately contains Y iff Y is a member of X.

    "X immediately contains Y iff X = {Y, Z} for some SO Z" — since SOs
    are unordered binary sets (`l * r = r * l`), this means Y is one of
    the two immediate daughters of X.

    Defined via lift over a swap-respecting helper on `FreeMagma`. -/
private def immediatelyContainsAux (y : SyntacticObject) :
    FreeMagma (LIToken ⊕ Nat) → Prop
  | .of _ => False
  | .mul a b => y = (Quot.mk _ a : SyntacticObject) ∨ y = (Quot.mk _ b : SyntacticObject)

private theorem immediatelyContainsAux_respects (y : SyntacticObject)
    (a b : FreeMagma (LIToken ⊕ Nat)) (h : FreeMagma.CommRel a b) :
    immediatelyContainsAux y a = immediatelyContainsAux y b := by
  induction h with
  | swap a b => simp only [immediatelyContainsAux]; exact propext (Or.comm)
  | mul_left h_inner _ ih =>
    simp only [immediatelyContainsAux]
    have : (Quot.mk _ _ : SyntacticObject) = Quot.mk _ _ := Quot.sound h_inner
    rw [this]
  | mul_right _ h_inner ih =>
    simp only [immediatelyContainsAux]
    have : (Quot.mk _ _ : SyntacticObject) = Quot.mk _ _ := Quot.sound h_inner
    rw [this]

def immediatelyContains (x y : SyntacticObject) : Prop :=
  FreeCommMagma.lift (immediatelyContainsAux y)
    (immediatelyContainsAux_respects y) x

@[simp] theorem immediatelyContains_leaf (tok : LIToken) (y : SyntacticObject) :
    ¬ immediatelyContains (.leaf tok) y := id

@[simp] theorem immediatelyContains_trace (n : Nat) (y : SyntacticObject) :
    ¬ immediatelyContains (.trace n) y := id

@[simp] theorem immediatelyContains_mul (l r y : SyntacticObject) :
    immediatelyContains (l * r) y ↔ y = l ∨ y = r := by
  induction l using FreeCommMagma.ind with | _ a =>
    induction r using FreeCommMagma.ind with | _ b => rfl

/-- Decidable immediate containment. Recurses via `Quot.recOnSubsingleton`
    on the underlying `FreeMagma` representative. -/
instance decImmediatelyContains (x y : SyntacticObject) :
    Decidable (immediatelyContains x y) :=
  Quot.recOnSubsingleton (motive := fun x => Decidable (immediatelyContains x y))
    x fun fm =>
      match fm with
      | .of _ => isFalse id
      | .mul _ _ => inferInstanceAs (Decidable (_ ∨ _))

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
  | imm _ _ himm => exact immediatelyContains_leaf _ _ himm
  | trans _ _ z himm _ => exact immediatelyContains_leaf _ _ himm

/-- Trace markers contain nothing. -/
theorem trace_contains_nothing (n : Nat) (y : SyntacticObject) :
    ¬(contains (SyntacticObject.trace n) y) := by
  intro h
  cases h with
  | imm _ _ himm => exact immediatelyContains_trace _ _ himm
  | trans _ _ z himm _ => exact immediatelyContains_trace _ _ himm

-- Part 3b: Well-Foundedness via nodeCount

/-- Immediate containment strictly decreases nodeCount -/
theorem immediatelyContains_lt_nodeCount {x y : SyntacticObject}
    (h : immediatelyContains x y) : y.nodeCount < x.nodeCount := by
  induction x with
  | leaf _ => exact (immediatelyContains_leaf _ _ h).elim
  | trace _ => exact (immediatelyContains_trace _ _ h).elim
  | mul a b iha ihb =>
    rw [immediatelyContains_mul] at h
    simp only [SyntacticObject.nodeCount_mul]
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

-- Part 3c: Decidability of containment

/-- `Quot.mk` distributes over the underlying `FreeMagma` multiplication
    (definitionally, since `FreeCommMagma.mul` is `Quot.lift₂` over
    `FreeMagma.mul`). -/
private theorem mk_mul (a b : FreeMagma (LIToken ⊕ Nat)) :
    (Quot.mk _ (a * b) : SyntacticObject)
      = FreeCommMagma.mul (Quot.mk _ a) (Quot.mk _ b) := rfl

/-- Helper: decide `contains (Quot.mk _ fm) y` by structural recursion on
    the underlying `FreeMagma` representative. -/
private def decContainsAux (y : SyntacticObject) :
    (fm : FreeMagma (LIToken ⊕ Nat)) → Decidable (contains (Quot.mk _ fm) y)
  | .of (.inl tok) => isFalse (leaf_contains_nothing tok y)
  | .of (.inr n) => isFalse (trace_contains_nothing n y)
  | .mul a b =>
    let qa : SyntacticObject := Quot.mk _ a
    let qb : SyntacticObject := Quot.mk _ b
    have ha' : Decidable (contains qa y) := decContainsAux y a
    have hb' : Decidable (contains qb y) := decContainsAux y b
    have hd : Decidable (contains (qa * qb) y) :=
      decidable_of_iff
        (qa = y ∨ qb = y ∨ contains qa y ∨ contains qb y) <| by
        constructor
        · rintro (rfl | rfl | hca | hcb)
          · exact contains.imm _ _ ((immediatelyContains_mul _ _ _).mpr (Or.inl rfl))
          · exact contains.imm _ _ ((immediatelyContains_mul _ _ _).mpr (Or.inr rfl))
          · exact contains.trans _ _ _
              ((immediatelyContains_mul _ _ _).mpr (Or.inl rfl)) hca
          · exact contains.trans _ _ _
              ((immediatelyContains_mul _ _ _).mpr (Or.inr rfl)) hcb
        · intro h
          cases h with
          | imm _ _ himm =>
              rw [immediatelyContains_mul] at himm
              rcases himm with rfl | rfl
              · exact Or.inl rfl
              · exact Or.inr (Or.inl rfl)
          | trans _ _ z himm hcz =>
              rw [immediatelyContains_mul] at himm
              rcases himm with rfl | rfl
              · exact Or.inr (Or.inr (Or.inl hcz))
              · exact Or.inr (Or.inr (Or.inr hcz))
    -- Quot.mk _ (a * b) and qa * qb are defeq
    hd

/-- Containment is decidable by structural recursion on the containing SO's
    underlying `FreeMagma` representative (via `Quot.recOnSubsingleton` —
    `Decidable p` is a subsingleton up to propositional equality). -/
instance decContains (x y : SyntacticObject) : Decidable (contains x y) :=
  Quot.recOnSubsingleton (motive := fun x => Decidable (contains x y))
    x (fun a => decContainsAux y a)

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

instance decIsTermOf (x y : SyntacticObject) : Decidable (isTermOf x y) := by
  unfold isTermOf; infer_instance

-- Part 5: Root and Reflexive Containment

/-- Reflexive containment (useful for stating constraints) -/
def containsOrEq (x y : SyntacticObject) : Prop :=
  x = y ∨ contains x y

instance decContainsOrEq (x y : SyntacticObject) : Decidable (containsOrEq x y) := by
  unfold containsOrEq; infer_instance

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

/-! ### Subtree-Finset ↔ containment bridge

These theorems relate `subtrees : SO → Finset SO` to the propositional
`contains`/`containsOrEq` relations. With `subtrees` Finset-typed
(order-blind, computable), the bridges are provable by induction —
no `Quot.out` oracle dependence. -/

/-- Children of any subtree of `root` are themselves subtrees of `root`. -/
theorem mem_subtrees_of_imm_contains {root w z : SyntacticObject}
    (hw : w ∈ root.subtrees) (hwz : immediatelyContains w z) :
    z ∈ root.subtrees := by
  induction root with
  | leaf tok =>
    simp only [SyntacticObject.subtrees_leaf, Multiset.mem_singleton] at hw
    rw [hw] at hwz
    exact (immediatelyContains_leaf _ _ hwz).elim
  | trace n =>
    simp only [SyntacticObject.subtrees_trace, Multiset.mem_singleton] at hw
    rw [hw] at hwz
    exact (immediatelyContains_trace _ _ hwz).elim
  | mul l r ihl ihr =>
    simp only [SyntacticObject.subtrees_mul, Multiset.mem_cons,
               Multiset.mem_add] at hw
    rcases hw with rfl | hl | hr
    · -- w = l * r; immediatelyContains (l*r) z means z = l ∨ z = r
      rw [immediatelyContains_mul] at hwz
      simp only [SyntacticObject.subtrees_mul, Multiset.mem_cons,
                 Multiset.mem_add]
      rcases hwz with rfl | rfl
      · exact Or.inr (Or.inl (self_mem_subtrees _))
      · exact Or.inr (Or.inr (self_mem_subtrees _))
    · simp only [SyntacticObject.subtrees_mul, Multiset.mem_cons,
                 Multiset.mem_add]
      exact Or.inr (Or.inl (ihl hl))
    · simp only [SyntacticObject.subtrees_mul, Multiset.mem_cons,
                 Multiset.mem_add]
      exact Or.inr (Or.inr (ihr hr))

/-- Containment implies subtree-Finset membership. -/
theorem mem_subtrees_of_contains {y z : SyntacticObject}
    (h : contains y z) : z ∈ y.subtrees := by
  induction h with
  | imm x y himm =>
    exact mem_subtrees_of_imm_contains (self_mem_subtrees _) himm
  | trans x y w himm hcwy ih =>
    -- ih : y ∈ w.subtrees; himm : immediatelyContains x w
    -- so w ∈ x.subtrees by mem_subtrees_of_imm_contains
    -- then w.subtrees ⊆ x.subtrees by subtrees_subset_of_mem
    -- so y ∈ x.subtrees
    exact subtrees_subset_of_mem
      (mem_subtrees_of_imm_contains (self_mem_subtrees _) himm) ih

/-- Subtree-Multiset membership implies term-of relation. -/
theorem isTermOf_of_mem_subtrees {y z : SyntacticObject}
    (h : z ∈ y.subtrees) : isTermOf z y := by
  induction y with
  | leaf tok =>
    simp only [SyntacticObject.subtrees_leaf, Multiset.mem_singleton] at h
    exact Or.inl h
  | trace n =>
    simp only [SyntacticObject.subtrees_trace, Multiset.mem_singleton] at h
    exact Or.inl h
  | mul l r ihl ihr =>
    simp only [SyntacticObject.subtrees_mul, Multiset.mem_cons,
               Multiset.mem_add] at h
    rcases h with rfl | hl | hr
    · exact Or.inl rfl
    · -- z ∈ l.subtrees → isTermOf z l → contains (l*r) z (via l)
      rcases ihl hl with rfl | hcontains
      · exact Or.inr (contains.imm _ _
          ((immediatelyContains_mul _ _ _).mpr (Or.inl rfl)))
      · exact Or.inr (contains.trans _ _ _
          ((immediatelyContains_mul _ _ _).mpr (Or.inl rfl)) hcontains)
    · -- symmetric on right
      rcases ihr hr with rfl | hcontains
      · exact Or.inr (contains.imm _ _
          ((immediatelyContains_mul _ _ _).mpr (Or.inr rfl)))
      · exact Or.inr (contains.trans _ _ _
          ((immediatelyContains_mul _ _ _).mpr (Or.inr rfl)) hcontains)

/-- `isTermOf z y` iff `z` is in `y.subtrees`. The bridge between the
    propositional term-of relation and the Finset-typed enumeration. -/
theorem isTermOf_iff_mem_subtrees (y z : SyntacticObject) :
    isTermOf z y ↔ z ∈ y.subtrees := by
  refine ⟨fun h => ?_, isTermOf_of_mem_subtrees⟩
  rcases h with rfl | hcontains
  · exact self_mem_subtrees _
  · exact mem_subtrees_of_contains hcontains

/-- X and Y are sisters IN tree `root`: they are distinct co-daughters of
    some node that is a subtree of `root`. -/
def areSistersIn (root x y : SyntacticObject) : Prop :=
  ∃ z ∈ root.subtrees, immediatelyContains z x ∧ immediatelyContains z y ∧ x ≠ y

instance decAreSistersIn (root x y : SyntacticObject) :
    Decidable (areSistersIn root x y) :=
  Multiset.decidableExistsMultiset

/-- X c-commands Y IN tree `root`: X has a sister (in `root`) that
    contains-or-equals Y. -/
def cCommandsIn (root x y : SyntacticObject) : Prop :=
  ∃ z ∈ root.subtrees, areSistersIn root x z ∧ containsOrEq z y

/-- `cCommandsIn` is decidable: bounded existential over `root.subtrees`
    (Multiset). Computable since `subtrees` is. -/
instance decCCommandsIn (root x y : SyntacticObject) :
    Decidable (cCommandsIn root x y) :=
  Multiset.decidableExistsMultiset

/-- X asymmetrically c-commands Y in tree `root`. -/
def asymCCommandsIn (root x y : SyntacticObject) : Prop :=
  cCommandsIn root x y ∧ ¬cCommandsIn root y x

instance decAsymCCommandsIn (root x y : SyntacticObject) :
    Decidable (asymCCommandsIn root x y) := by
  unfold asymCCommandsIn; infer_instance

/-! ## Note on Barker-Pullum command relations

An earlier draft of this file recast `cCommandsIn` as B&P K-command
(`Core.Order.commandRelation` over `FreeMagma.toTree`'s tree-order),
aiming to inherit B&P's antitonicity / intersection theorems "for
free" in the same lattice as HPSG `o-command` and DG `d-command`.

That recast does not work: B&P's `commandRelation` is universal
("every branching ancestor of α also dominates β") and admits pairs
that sister-form c-command excludes — e.g., on tree `(a, (b, c))`,
the leaf `a` B&P-commands itself and the root, since the only
branching strict ancestor is the root, which trivially dominates
everything. Reinhart c-command is sister-form (∃ sister of α
containing β); the two relations are not biconditionally equivalent
on `FreeMagma`.

The mathlib-style resolution: keep `cCommandsIn` value-side and
sister-form (it's what binding consumers need, and it reads directly
off bare phrase structure per @cite{marcolli-chomsky-berwick-2025}).
Cross-tradition unification via B&P's parametric command lives in
`Core/Order/Command.lean` and is exercised by HPSG / DG, where its
universal shape matches the native primitive. Minimalism's c-command
does not reduce to it, so no bridge belongs here. -/

/-! ## Multiset shape — abstract geometry over the nonplanar quotient

The unlabeled SO shape: replace every leaf token / trace marker with
`()`. The result lives in `FreeCommMagma Unit` — the canonical
*nonplanar* analog of the prior planar `TreeShape` (which was deleted
because `.node L R = .node R L` failed to hold under MCB §1.1.3,
book p. 23). Two SOs are *structurally isomorphic* iff their shapes
are equal as elements of `FreeCommMagma Unit`. -/

/-- The unlabeled multiset-shape of an SO: forget every leaf token
    and trace marker, keeping only the binary-tree structure modulo
    nonplanar quotient. Functorial via `FreeCommMagma.map`. -/
def SyntacticObject.shape : SyntacticObject → FreeCommMagma Unit :=
  FreeCommMagma.map (Function.const _ ())

@[simp] theorem SyntacticObject.shape_leaf (tok : LIToken) :
    (SyntacticObject.leaf tok).shape = FreeCommMagma.of () := rfl

@[simp] theorem SyntacticObject.shape_trace (n : Nat) :
    (SyntacticObject.trace n).shape = FreeCommMagma.of () := rfl

@[simp] theorem SyntacticObject.shape_mul (l r : SyntacticObject) :
    (l * r).shape = l.shape * r.shape :=
  MulHom.map_mul (FreeCommMagma.map _) l r

/-- Two SOs are structurally isomorphic iff they have the same
    nonplanar shape (ignoring all leaf labels). Replaces the prior
    `Bool`-valued `structurallyIsomorphic` from the planar substrate;
    `Prop`-valued + `DecidableEq` is more mathlib-aligned. -/
def structurallyIsomorphic (x y : SyntacticObject) : Prop :=
  x.shape = y.shape

instance (x y : SyntacticObject) :
    Decidable (structurallyIsomorphic x y) := by
  unfold structurallyIsomorphic; infer_instance

/-! ## Y-model branch to LF

The LF lift `SyntacticObject.toLFTree : SyntacticObject → Tree Unit String`
lives in `Theories/Syntax/Minimalism/SpellOut.lean`, where trace
detection and phonForm extraction are handled. PF (linearize /
phonYield) operates natively on `SyntacticObject` and does not require
a lift. -/

end Minimalist
