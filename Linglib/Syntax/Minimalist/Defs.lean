import Mathlib.Data.Set.Basic
import Mathlib.Data.Multiset.Basic
import Linglib.Data.UD.Basic

/-!
# Syntactic Objects: the SO₀ alphabet
[chomsky-2013] [marcolli-chomsky-berwick-2025]

The **lexical alphabet** of the Minimalist Program: categorial features,
lexical items, and the `LIToken` leaves over which syntactic objects are
built. The `SyntacticObject` carrier itself — the MCB-faithful nonplanar
`SO` type — lives in `SyntacticObject.lean` (which imports this file for the
alphabet), so this `Defs` module is carrier-agnostic.

Per [marcolli-chomsky-berwick-2025] Def 1.1.1 (book p. 22), `SO₀` consists of
lexical items and syntactic features. Linglib encodes a leaf as an `LIToken`
(an instantiated `LexicalItem`); the carrier's leaf alphabet is `LIToken ⊕ Unit`
(lexical leaf `inl tok` vs the bare trace/structural vertex `inr ()`).

- `Cat`, `SelStack`, `SimpleLI`, `LexicalItem`, `LIToken`
- `ConventionDir` — harmonic head-side parameter (Lemma 1.13.5)
- `uposToCat` — UD POS → Minimalist `Cat` bridge
- `mkTraceToken`, `LIToken.phonForm` — carrier-free token helpers
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
    externalization (`SyntacticObject/Externalization.lean`). Mixed-direction
    languages (German head-final VP + head-initial CP) need a
    `headSide : Cat → ConventionDir` refinement, out of scope for §1.13-§1.16. -/
inductive ConventionDir where
  | initial
  | final
  deriving Repr, DecidableEq, Inhabited

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

/-- Extract the phonological form from an LIToken. -/
def LIToken.phonForm (tok : LIToken) : String :=
  tok.item.features.head?.map (·.phonForm) |>.getD ""

/-- The phonological form of a pronounced token; `none` when the form is empty. -/
def LIToken.phonForm? (tok : LIToken) : Option String :=
  let p := tok.phonForm
  if p.isEmpty then none else some p

/-- LIToken-level c-selection: `selector` selects `selected` iff
    `selector`'s outermost selectional feature equals `selected`'s outer
    category. A pure `LIToken` relation; no SO structure involved. -/
def LIToken.selects (selector selected : LIToken) : Prop :=
  selector.item.outerSel.head? = some selected.item.outerCat

instance (lt1 lt2 : LIToken) : Decidable (LIToken.selects lt1 lt2) := by
  unfold LIToken.selects; infer_instance

/-- Trace marker token: the canonical LIToken read off a bare trace vertex
    when a selection check needs an `LIToken` at that position. The `index`
    is recorded in the `id` field (sentinel ≥ 10000) but is **not** part of
    chain identity — MCB chain identity is workspace-level (Def 1.2.1), and the
    `SO` carrier's trace leaf is bare/index-free. Selection reads only the
    token's category (`.N`) and `outerSel` (`[]`), both index-independent. -/
def mkTraceToken (index : Nat) : LIToken :=
  ⟨.simple .N [] (phonForm := ""), index + 10000⟩

end Minimalist
