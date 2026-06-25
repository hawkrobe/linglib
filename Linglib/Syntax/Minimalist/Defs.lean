import Mathlib.Data.Set.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.Free
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Linglib.Data.UD.Basic
import Linglib.Core.Algebra.Free
import Linglib.Core.Order.Branching
import Linglib.Core.Order.Command

/-!
# Syntactic Objects: core types and carrier
[chomsky-2013] [marcolli-chomsky-berwick-2025]

Definitions module for the Minimalist Program formalization: lexical items,
the `SyntacticObject` carrier, Merge, planar linearization, and node counts.
The containment/subterm theory built on these lives in `Basic.lean`.

## Syntactic Objects

`SyntacticObject` is `FreeMagma LIToken`: bare phrase structure as the
free magma over lexical-item tokens, following [marcolli-chomsky-berwick-2025].
The two constructors are `FreeMagma.of` (lexical leaves) and
`FreeMagma.mul` (binary Merge). The shims `SyntacticObject.leaf` /
`SyntacticObject.node` rename them at the linguistic interface.

The Y-model branches by *map*, not by *type*: PF lives natively on
`SyntacticObject` via `linearize`/`phonYield`; the LF lift to
`Tree Unit String` lives in `SpellOut.lean` (`SyntacticObject.toLFTree`),
which handles trace detection and phonForm extraction.

- `SimpleLI`, `LexicalItem`, `LIToken`, `SyntacticObject`
- `merge`, `externalMerge`, `internalMerge`

## Two programs on this carrier

This file is the shared foundation of two layers that build on
`SyntacticObject`:

- the **practical Minimalist syntax** (Voice, Agree, Phase, Probe, …), which
  operates on this `FreeCommMagma` carrier directly; and
- the **MCB algebraic Merge** (`Merge/`), the Connes–Kreimer bialgebra on
  `Nonplanar` forests, joined to this carrier only by the
  `SyntacticObject.toNonplanar` projection (`Merge/Defs.lean`), which orients
  each node via the selection-induced embedding `selLinearize` (`Selection.lean`).

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
  | n     -- nominal categorizer / gender (little-n, [marantz-2001]; Distributed Morphology)
  | a     -- adjectival categorizer (little-a, [panagiotidis-2015]; DegP complement)
  | Place -- locational head ([dendikken-2010]; PlaceP, F1 in adpositional EP)
  | Path  -- directional head ([dendikken-2010] [svenonius-2010]; PathP, F2 in adpositional EP)
  | Num   -- number ([ritter-1991]; NumP between nP and QP/DP)
  | Q     -- quantity / classifier ([borer-2005]; QP between NumP and DP)
  | Voice -- Voice head ([kratzer-1996]; [schaefer-2008])
  | Appl  -- Applicative head ([pylkkanen-2008]; [cuervo-2003])
  | Foc   -- focus ([rizzi-1997] split-CP; hosts [FoC] feature, triggers A-bar movement)
  | Top   -- topic ([rizzi-1997] split-CP; hosts [G]/givenness, topic fronting)
  | Fin   -- finiteness ([rizzi-1997] split-CP; allocutive probe in Magahi/Galician)
  | SA    -- speech act head ([speas-tenny-2003]; hosts speaker/addressee)
  | Say   -- say/assertion layer ([major-2021]; [krifka-2023]; [moulton-2009]); embeds the content of a verbal/representational sign. Distinct from `SA` (root illocutionary layer): `Say` is clause-internal, in the embedded left periphery with Say > Foc > T, and does NOT require a CP ([kiss-2023], [egressy-2026])
  | Force -- force ([rizzi-1997] split-CP; clause-typing [decl]/[interrog])
  | Neg   -- negation ([pollock-1989]; [zanuttini-1997]; hosts [±neg])
  | Mod   -- modality ([cinque-1999]; modal auxiliaries)
  | Rel   -- relative (cartographic left periphery, [rizzi-1997])
  | Pol   -- polarity ([laka-1990]; ΣP for affirmation/negation)
  | Asp   -- aspect ([cinque-1999]; inner inflectional, between Voice and T)
  | Evid  -- evidential ([cinque-1999]; outer inflectional, above T below Fin)
  | Nmlz  -- nominalizer ([keine-2020]; Hindi -naa/-ne nominalized clause; clause type distinct from CP)
  | K     -- inherent case shell ([newman-2024]; KP wraps DP for oblique/inherent case; explains no-IO-passive languages)
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

/-! ### Head-side convention (MCB Lemma 1.13.5) -/

/-- The harmonic head-side convention ([marcolli-chomsky-berwick-2025]
    Lemma 1.13.5, book p. 127): head functions on a tree are in bijection with
    its planar embeddings, under one of two conventions:

    - `.initial` (harmonic head-initial): the head daughter is to the LEFT of
      each binary node (English-like).
    - `.final` (harmonic head-final): the head daughter is to the RIGHT
      (Japanese/Korean/Turkish).

    A carrier-free parameter (it names a directionality, not a tree shape), so it
    lives in the alphabet layer alongside `Cat`. Consumed by the selection-induced
    externalization (`SyntacticObject/Externalization.lean`) and the legacy
    section-based `HeadFunction`. Mixed-direction languages (German head-final VP +
    head-initial CP) need a `headSide : Cat → ConventionDir` refinement, out of
    scope for §1.13-§1.16. -/
inductive ConventionDir where
  | initial
  | final
  deriving Repr, DecidableEq, Inhabited

/-- Syntactic object: nonplanar binary tree over `LIToken ⊕ Nat`,
    realized as `FreeCommMagma (LIToken ⊕ Nat)`.

Per [marcolli-chomsky-berwick-2025] Definition 1.1.1 (book p. 22),
SO is the **free, non-associative, commutative** magma `Magma_{na,c}(SO_0, M)`
with `M(α,β) = {α,β}` (unordered). Linguistically, this is the position that
Merge produces unordered sets, with linearization (PF / LCA / head-directionality)
as a separate Externalization step.

The three "constructors" at the SO interface are:

- `.leaf tok` — a lexical leaf, encoded as `FreeCommMagma.of (.inl tok)`
- `.trace n` — a trace marker, encoded as `FreeCommMagma.of (.inr n)`
- binary Merge, written `l * r` (commutative: `l * r = r * l` as a strict
  equality inside the quotient)

### Trace handling: linglib's `LIToken ⊕ Nat` is a deliberate divergence from MCB

MCB's SO_0 (book p. 22, Def 1.1.1) consists of *lexical items and syntactic
features only* — not trace markers. Internal Merge in MCB is a workspace-level
cut-and-extract operation: an accessible term is extracted, leaving one of
three possible remainder forms (Defs 1.2.5–1.2.8, book p. 31–35):

- `T/^c F_v` (contraction) — extracted term becomes a "deeper copy" labelling
  the leaf left by edge-contraction; visible to semantics, cancelled at PF
- `T/^d F_v` (deletion) — edge-contracted, no trace marker carried
- `T/^ρ F_v` (admissible cut) — an *unlabeled* structural vertex remains as
  the trace; used by the combined process

These are **three forms of the *remainder* tree after extraction**, not three
carrier choices for the SO type itself. In all three, the SO type's base
alphabet is `SO_0` = lexical items + syntactic features only.

**Linglib makes a different choice.** `SyntacticObject := FreeCommMagma
(LIToken ⊕ Nat)` adds *labeled, indexed* trace markers to the **base alphabet**.
This is structurally distinct from MCB's ^ρ form (where the trace is an
unlabeled structural vertex in the *remainder* tree only). Linglib's encoding
admits trace-bearing SOs at any stage of derivation, not just as remainders.

Why this divergence is here: chain-tracking ergonomics. The `Nat` index lets
downstream code identify which mover produced a given trace, which is
load-bearing for binding theory and reconstruction effects. MCB handles
chain-identification at the *workspace level* (a workspace forest may have
multiple connected components that are isomorphic to the same tree, and
those isomorphism classes are the chain). Linglib's chain-tracking-via-index
is expressively sufficient but inexpressively redundant w.r.t. MCB.

**Phase 2+ migration target**: replace `LIToken ⊕ Nat` with `LIToken` and
move chain-identification to the workspace layer. All current `.trace` /
`.isTrace` / `mkTrace` / `Step.im` operations become projection-side rather
than substrate. See project memory note `project_so_carrier_rho_projection.md`.

The migration from the prior planar `TraceTree LIToken Nat` carrier landed
at version 0.230.857 (Phase 0.5 substrate) + 0.230.858 (mathlib-canonical
`DecidableEq` via `CommEqv`, no `LinearOrder` needed). See
`Linglib/Scratch/PreLiePlanarCheck.lean` (counterexample showing the §1.7
pre-Lie identity is FALSE on planar trees, the headline reason for
nonplanarity).

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

/-- Cascade combinator: lift a `FreeMagma (LIToken ⊕ Nat) → β` aux to
    `SyntacticObject → β`, hiding the `FreeMagma.CommRel` machinery
    from downstream consumers. Same as `FreeCommMagma.lift` modulo the
    SO type ascription at the SO interface. The `_respects` hypothesis
    still has to be provided, but the type signature is consumer-friendly.

    Lives at `Minimalist.liftFM` (sibling of `leafShape` below), not
    inside the `SyntacticObject` namespace — `liftFM f h` takes no SO
    self-argument, so dot notation wouldn't apply. -/
abbrev liftFM {β : Type*} (f : FreeMagma (LIToken ⊕ Nat) → β)
    (h : ∀ a b, FreeMagma.CommRel a b → f a = f b) :
    SyntacticObject → β :=
  FreeCommMagma.lift f h

/-- Merge: the fundamental structure-building operation. Equal to
    `FreeCommMagma.mul` and to `(· * ·)`. Commutative: `merge x y = merge y x`
    as a strict equality on the quotient. -/
def merge (x y : SyntacticObject) : SyntacticObject :=
  x * y

/-- **Headline of the MCB Phase 1.0 nonplanar migration**:
    Merge is symmetric on the FreeCommMagma carrier.
    `merge x y = merge y x` as strict equality on the quotient,
    per [marcolli-chomsky-berwick-2025] Definition 1.1.1
    (book p. 22) + Remark 1.1.2 (p. 23). The earlier planar
    `TraceTree`-based theorem `merge_distinguishes_children`
    (`x ≠ y → merge x y ≠ merge y x`) is now PROVABLY FALSE; this
    `merge_comm` lemma is what replaces it at the substrate level.

    Available as a `simp` lemma so consumers can rewrite
    `merge x y` to `merge y x` (or vice versa) freely. -/
@[simp] theorem merge_comm (x y : SyntacticObject) : merge x y = merge y x := by
  unfold merge; exact mul_comm _ _

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
quotient. Per [marcolli-chomsky-berwick-2025] Remark 1.1.2 (book p. 23),
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

/-- Underlying phonological yield on a planar `FreeMagma` representative.
    Public so `HeadFunction.phonYieldWith` can compose it with a chosen
    `externalize` section. -/
def phonYieldPlanar : FreeMagma (LIToken ⊕ Nat) → List String
  | .of (.inl tok) =>
    let phon := tok.item.features.head?.map (·.phonForm) |>.getD ""
    if phon.isEmpty then [] else [phon]
  | .of (.inr _) => []
  | .mul a b => phonYieldPlanar a ++ phonYieldPlanar b

/-- Underlying linearization on a planar `FreeMagma` representative.
    Public so `HeadFunction.linearize` can compose it with a chosen
    `Section.σ` for harmonic head-initial linearization. -/
def linearizePlanar : FreeMagma (LIToken ⊕ Nat) → List LIToken
  | .of (.inl tok) => [tok]
  | .of (.inr _) => []
  | .mul l r => linearizePlanar l ++ linearizePlanar r

/-- Underlying leftmost-leaf on a planar `FreeMagma` representative.
    Exposed (not `private`) so `HeadFunction.head` can compose it with
    a chosen `Section.σ` for harmonic head-initial head extraction. -/
def leftmostLeafPlanar : FreeMagma (LIToken ⊕ Nat) → LIToken
  | .of (.inl tok) => tok
  | .of (.inr n) => mkTraceToken n
  | .mul l _ => leftmostLeafPlanar l

/-- Underlying rightmost-leaf on a planar `FreeMagma` representative.
    Mirror of `leftmostLeafPlanar` for harmonic head-final convention
    (per [marcolli-chomsky-berwick-2025] Lemma 1.13.5). -/
def rightmostLeafPlanar : FreeMagma (LIToken ⊕ Nat) → LIToken
  | .of (.inl tok) => tok
  | .of (.inr n) => mkTraceToken n
  | .mul _ r => rightmostLeafPlanar r

/-- Extract the phonological form from an LIToken. -/
def LIToken.phonForm (tok : LIToken) : String :=
  tok.item.features.head?.map (·.phonForm) |>.getD ""

/-- Underlying agreement on a planar representative: `phonYield` is the
    non-empty-phonForm filter of `linearize`. Used as a lemma for any
    `HeadFunction h` consumer that wants to relate `h.phonYield` to
    `h.linearize`. -/
theorem phonYield_eq_linearize_planar (fm : FreeMagma (LIToken ⊕ Nat)) :
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

end Minimalist
