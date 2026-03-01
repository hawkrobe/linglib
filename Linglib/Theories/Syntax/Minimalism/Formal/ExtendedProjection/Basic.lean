/-
# Extended Projection

Formalization of Grimshaw (2005) Extended Projection theory.

## Key Ideas

An **Extended Projection** (EP) is a sequence of projections unified by:
1. **Category consistency**: all heads share [±V, ±N] features
2. **F-value monotonicity**: functional level (F-value) increases going up the tree

Standard EPs:
- Verbal: V (F0) → v (F1) → T (F2) → C (F3)
- Nominal: N (F0) → D (F1)

## Definitions

- `CatFeatures`: Grimshaw's [±V, ±N] decomposition of category
- `fValue`: Functional level within an EP (0 = lexical, 1+ = functional)
- `ExtendedProjection`: Structure capturing an EP spine with consistency/monotonicity
- `CatFamily`: The four category families (verbal, nominal, adjectival, adpositional)

-/

import Linglib.Theories.Syntax.Minimalism.Core.Labeling

namespace Minimalism

-- ═══════════════════════════════════════════════════════════════
-- Part 1: Categorial Features [±V, ±N]
-- ═══════════════════════════════════════════════════════════════

/-- Chomsky's (1970) [±V, ±N] categorial features, adopted by Grimshaw (2005)
    for Extended Projections. Cross-classifies the four lexical categories:
    - V = [+V, -N], N = [-V, +N], A = [+V, +N], P = [-V, -N]

    Functional categories inherit these from their lexical anchor.

    For an alternative where [N] and [V] carry semantic content (referentiality
    and temporal predication), see `CategorialFeatures` (Panagiotidis 2015). -/
structure CatFeatures where
  plusV : Bool   -- [+V] = verbal/adjectival
  plusN : Bool   -- [+N] = nominal/adjectival
  deriving Repr, DecidableEq, BEq

/-- Compute Chomsky's (1970) [±V, ±N] features from `Cat`.
    Functional categories inherit features from their lexical anchor:
    - v, T, C inherit [+V, -N] from V
    - n, Num, Q, D inherit [-V, +N] from N -/
def catFeatures : Cat → CatFeatures
  | .V     => ⟨true,  false⟩   -- [+V, -N]
  | .v     => ⟨true,  false⟩   -- [+V, -N] (light verb)
  | .Voice => ⟨true,  false⟩   -- [+V, -N] (Kratzer 1996)
  | .Appl  => ⟨true,  false⟩   -- [+V, -N] (Pylkkänen 2008)
  | .T     => ⟨true,  false⟩   -- [+V, -N]
  | .Foc   => ⟨true,  false⟩   -- [+V, -N] (Rizzi 1997 split-CP)
  | .Top   => ⟨true,  false⟩   -- [+V, -N] (Rizzi 1997 split-CP)
  | .Fin   => ⟨true,  false⟩   -- [+V, -N] (Rizzi 1997 split-CP)
  | .C     => ⟨true,  false⟩   -- [+V, -N]
  | .SA    => ⟨true,  false⟩   -- [+V, -N] (Speas & Tenny 2003)
  | .Force => ⟨true,  false⟩   -- [+V, -N] (Rizzi 1997 split-CP)
  | .Neg   => ⟨true,  false⟩   -- [+V, -N] (Pollock 1989)
  | .Mod   => ⟨true,  false⟩   -- [+V, -N] (Cinque 1999)
  | .Rel   => ⟨true,  false⟩   -- [+V, -N] (Rizzi 2001)
  | .Pol   => ⟨true,  false⟩   -- [+V, -N] (Laka 1990)
  | .Asp   => ⟨true,  false⟩   -- [+V, -N] (Cinque 1999)
  | .Evid  => ⟨true,  false⟩   -- [+V, -N] (Cinque 1999)
  | .N     => ⟨false, true⟩    -- [-V, +N]
  | .n     => ⟨false, true⟩    -- [-V, +N] (categorizer/gender, Marantz 2001)
  | .Num   => ⟨false, true⟩    -- [-V, +N] (number, Ritter 1991)
  | .Q     => ⟨false, true⟩    -- [-V, +N] (quantity/classifier, Borer 2005)
  | .D     => ⟨false, true⟩    -- [-V, +N]
  | .A     => ⟨true,  true⟩    -- [+V, +N]
  | .a     => ⟨true,  true⟩    -- [+V, +N] (adjectival categorizer, Panagiotidis 2015)
  | .P     => ⟨false, false⟩   -- [-V, -N]

-- ═══════════════════════════════════════════════════════════════
-- Part 2: F-Value (Functional Level)
-- ═══════════════════════════════════════════════════════════════

/-- Grimshaw's F-value: the functional level within an extended projection.

    F-values are globally aligned across category families to capture
    the verbal–nominal parallelism (Ritter 1991, Grimshaw 2005).

    The nominal spine follows Borer's (2005) ordering: Q (classifier /
    individuation, CL#) is at F2, below Num (number / counting, #)
    at F3. This reflects the semantic composition order: individuation
    must precede counting (you can't count what hasn't been individuated).
    See `Borer2005.lean` for the formal argument.

    | F-level | Role              | Verbal           | Nominal             |
    |---------|-------------------|------------------|---------------------|
    | F0      | Lexical (content) | V                | N                   |
    | F1      | Categorizer       | v, Voice, Appl   | n (gender/class)    |
    | F2      | Specification     | T, Neg, Asp, Mod | Q (classifier/CL#)  |
    | F3      | Inner edge        | Fin              | Num (number/#)      |
    | F4      | Discourse/ref     | Foc              | D (definiteness)    |
    | F5      | Topic             | Top, Rel         |                     |
    | F6      | Clause/force      | C, Force         |                     |
    | F7      | Speech act        | SA               |                     |

    **Verbal–nominal parallelism**: The parallelism is robust at F0
    (lexical anchors) and F1 (categorizers: v ↔ n). At F2–F3, the
    verbal and nominal spines are *analogous* but not isomorphic:
    T/Asp specify temporal properties while Q specifies individuation;
    Fin types the clause while Num types the nominal. The semantic
    functions differ, but both occupy the same structural zone.

    The verbal C-domain is internally ordered per Rizzi (1997):
    Fin(F3) < Foc(F4) < Top(F5) < C(F6). -/
def fValue : Cat → Nat
  | .V | .N | .A | .P          => 0   -- lexical (F0)
  | .v | .n | .a | .Voice | .Appl => 1  -- first functional / categorizer (F1)
  | .T | .Q | .Neg | .Mod
  | .Pol | .Asp | .Evid         => 2   -- specification domain (F2)
  | .Fin | .Num                 => 3   -- inner edge (F3)
  | .Foc | .D                   => 4   -- discourse / referential (F4)
  | .Top | .Rel                 => 5   -- topic field (F5, Rizzi 1997/2001)
  | .C | .Force                 => 6   -- complementizer/force (F6)
  | .SA                         => 7   -- speech act (F7, Speas & Tenny 2003)

-- ═══════════════════════════════════════════════════════════════
-- Part 3: Category Consistency and Monotonicity
-- ═══════════════════════════════════════════════════════════════

/-- Category consistency: two categories share [±V, ±N] features.
    This is the core constraint on Extended Projections —
    V and T are consistent (both [+V, -N]), but V and D are not. -/
def categoryConsistent (c1 c2 : Cat) : Bool :=
  catFeatures c1 == catFeatures c2

/-- F-value monotonicity: F-values must not decrease going up the tree.
    In an EP, each head's F-value is ≥ the one below it. -/
def fMonotone (lower upper : Cat) : Bool :=
  fValue lower ≤ fValue upper

/-- Perfect projection: same [±V, ±N] AND same F-value.
    E.g., two V heads (F0, [+V, -N]) are perfect projections of each other.
    Distinct from EP extension, where F-value increases. -/
def perfectProjection (c1 c2 : Cat) : Bool :=
  categoryConsistent c1 c2 && (fValue c1 == fValue c2)

-- ═══════════════════════════════════════════════════════════════
-- Part 4: L-Head vs F-Head
-- ═══════════════════════════════════════════════════════════════

/-- Is this category a lexical head (F0)?
    L-heads are content categories: V, N, A, P. -/
def isLHead (c : Cat) : Bool := fValue c == 0

/-- Is this category a functional head (F1+)?
    F-heads are functional categories: v, D, T, C. -/
def isFHead (c : Cat) : Bool := fValue c > 0

-- ═══════════════════════════════════════════════════════════════
-- Part 5: Category Family
-- ═══════════════════════════════════════════════════════════════

/-- The four lexical category families, each defining an EP domain.
    All categories in an EP must belong to the same family. -/
inductive CatFamily where
  | verbal        -- V, v, T, C          [+V, -N]
  | nominal       -- N, n, Num, Q, D     [-V, +N]
  | adjectival    -- A                   [+V, +N]
  | adpositional  -- P                   [-V, -N]
  deriving Repr, DecidableEq, BEq

/-- Map a category to its family.
    This determines which EP it can participate in. -/
def catFamily : Cat → CatFamily
  | .V | .v | .Voice | .Appl | .T | .Foc | .Top | .Fin | .C | .SA
  | .Force | .Neg | .Mod | .Rel | .Pol | .Asp | .Evid => .verbal
  | .N | .n | .Num | .Q | .D           => .nominal
  | .A | .a                              => .adjectival
  | .P                                  => .adpositional

-- ═══════════════════════════════════════════════════════════════
-- Part 5b: Categorial Features — Panagiotidis (2015)
-- ═══════════════════════════════════════════════════════════════

/-- Panagiotidis (2015) categorial features: [N] and [V] as substantive,
    LF-interpretable features with semantic content.

    - **[N]** = sortal perspective / referentiality (capacity to introduce a
      discourse referent, following Longobardi 1994/2005; §4.3 p84)
    - **[V]** = temporal perspective / eventivity (capacity to anchor to
      time/events; §4.3 p85)

    This contrasts with Chomsky's (1970) [±V, ±N] diacritics (see `CatFeatures`):
    Chomsky's features are arbitrary binary cross-classifiers, while Panagiotidis's
    are grounded in semantic substance. The key empirical difference is the status
    of P: Chomsky treats P as actively bearing [-V, -N]; Panagiotidis treats P as
    the **default** categorizer lacking both [N] and [V] (§4.3).

    **Interpretability distinction** (§5.8): On categorizers (v, n, a), these
    features are *interpretable* — they provide the LF-legible interpretive
    perspective (sortal or temporal). On higher functional heads (T, C, D, etc.),
    these features are *uninterpretable* copies that serve only for Agree/selection.
    This formalization does not encode the interpretable/uninterpretable distinction
    but records which features are present, which suffices for EP consistency.

    Despite the conceptual difference, the two systems produce the same four
    equivalence classes over categories (see `chomsky_panagiotidis_agree`). -/
structure CategorialFeatures where
  hasN : Bool   -- [N] = referentiality
  hasV : Bool   -- [V] = temporal predication
  deriving Repr, DecidableEq, BEq

/-- Map a category to Panagiotidis's (2015) categorial features.

    Categorizers (n, v, a) bear the substantive features; functional heads
    in the same EP inherit them (just as in Grimshaw's consistency requirement).
    P and its extended projection bear neither feature — P is the default case. -/
def categorialFeatures : Cat → CategorialFeatures
  | .V | .v | .Voice | .Appl | .T | .Foc | .Top | .Fin | .C | .SA
  | .Force | .Neg | .Mod | .Rel | .Pol | .Asp | .Evid => ⟨false, true⟩   -- [V]
  | .N | .n | .Num | .Q | .D           => ⟨true, false⟩   -- [N]
  | .A | .a                              => ⟨true, true⟩    -- [N, V]
  | .P                                  => ⟨false, false⟩  -- default (no features)

/-- Consistency under Panagiotidis's system: two categories share [N]/[V] features. -/
def categorialConsistent (c1 c2 : Cat) : Bool :=
  categorialFeatures c1 == categorialFeatures c2

/-- Chomsky's [±V, ±N] and Panagiotidis's [N]/[V] produce the same equivalence
    classes over all categories. They agree on which pairs are EP-consistent.

    The conceptual difference — P as [-V, -N] vs. P as default — is invisible
    to the consistency check: both systems group P only with itself. -/
theorem chomsky_panagiotidis_agree (c1 c2 : Cat) :
    categoryConsistent c1 c2 = categorialConsistent c1 c2 := by
  cases c1 <;> cases c2 <;> decide

-- ═══════════════════════════════════════════════════════════════
-- Part 6: Extended Projection Structure
-- ═══════════════════════════════════════════════════════════════

/-- An Extended Projection: a sequence of categories forming a projection chain
    with category consistency and F-value monotonicity.

    The spine lists categories from lowest (lexical head) to highest (functional). -/
structure ExtendedProjection where
  /-- Root syntactic object of the EP -/
  root : SyntacticObject
  /-- Categories along the spine, from lexical head (F0) upward -/
  spine : List Cat
  /-- All spine categories share [±V, ±N] features -/
  catConsistent : Bool
  /-- F-values are non-decreasing along the spine -/
  fMonotoneChain : Bool

/-- Check that a list of categories is category-consistent
    (all share the same [±V, ±N] features). -/
def allCategoryConsistent : List Cat → Bool
  | [] => true
  | [_] => true
  | c₁ :: c₂ :: rest => categoryConsistent c₁ c₂ && allCategoryConsistent (c₂ :: rest)

/-- Check that a list of categories has monotonically non-decreasing F-values. -/
def allFMonotone : List Cat → Bool
  | [] => true
  | [_] => true
  | c₁ :: c₂ :: rest => fMonotone c₁ c₂ && allFMonotone (c₂ :: rest)

/-- Compute the EP spine from a syntactic object by collecting categories
    along the head-projection chain. Returns pairs of (SO, Cat) from
    the deepest lexical head up to the root. -/
partial def computeEPSpine (so : SyntacticObject) : List (SyntacticObject × Cat) :=
  match so with
  | .leaf tok => [(so, tok.item.outerCat)]
  | .node a b =>
    -- Find which daughter is the head (projects)
    let headDaughter := if selectsB a b then a
                        else if selectsB b a then b
                        else a  -- default: left daughter
    let spineBelow := computeEPSpine headDaughter
    match getCategory so with
    | some c => spineBelow ++ [(so, c)]
    | none   => spineBelow

/-- Build an ExtendedProjection from a syntactic object. -/
def mkExtendedProjection (so : SyntacticObject) : ExtendedProjection :=
  let spinePairs := computeEPSpine so
  let cats := spinePairs.map Prod.snd
  { root := so
    spine := cats
    catConsistent := allCategoryConsistent cats
    fMonotoneChain := allFMonotone cats }

/-- Is this EP well-formed? (category consistent AND F-monotone) -/
def ExtendedProjection.isWellFormed (ep : ExtendedProjection) : Bool :=
  ep.catConsistent && ep.fMonotoneChain

/-- The family of an EP (determined by any element of the spine). -/
def ExtendedProjection.family (ep : ExtendedProjection) : Option CatFamily :=
  ep.spine.head?.map catFamily

/-- The lexical anchor of an EP (the F0 head at the bottom). -/
def ExtendedProjection.lexicalAnchor (ep : ExtendedProjection) : Option Cat :=
  ep.spine.head?.filter isLHead

/-- The highest functional head in the EP. -/
def ExtendedProjection.highestHead (ep : ExtendedProjection) : Option Cat :=
  ep.spine.getLast?

-- ═══════════════════════════════════════════════════════════════
-- Part 7: Bridge Theorems
-- ═══════════════════════════════════════════════════════════════

-- Existing Cat assignments are EP-consistent

/-- The verbal chain V → v → T → C is category-consistent:
    all share [+V, -N] features. -/
theorem verbal_chain_consistent :
    categoryConsistent .V .v ∧ categoryConsistent .v .T ∧
    categoryConsistent .T .C := by decide

/-- The nominal chain N → n → Q → Num → D is category-consistent:
    all have [-V, +N] features. Q (CL#, individuation) is below
    Num (#, counting) per Borer (2005). -/
theorem nominal_chain_consistent :
    categoryConsistent .N .n ∧ categoryConsistent .n .Q ∧
    categoryConsistent .Q .Num ∧ categoryConsistent .Num .D := by decide

-- F-values are monotone along standard chains

/-- F-values increase monotonically along the verbal chain:
    V(0) ≤ v(1) ≤ T(2) ≤ C(3). -/
theorem verbal_fvalues_monotone :
    fValue .V ≤ fValue .v ∧ fValue .v ≤ fValue .T ∧
    fValue .T ≤ fValue .C := by decide

/-- F-values increase along the nominal chain: N(0) ≤ n(1) ≤ Q(2) ≤ Num(3) ≤ D(4).
    Q (individuation) is below Num (counting) per Borer (2005). -/
theorem nominal_fvalues_monotone :
    fValue .N ≤ fValue .n ∧ fValue .n ≤ fValue .Q ∧
    fValue .Q ≤ fValue .Num ∧ fValue .Num ≤ fValue .D := by decide

-- Cross-family inconsistency

/-- V and N are NOT category-consistent (different [±V, ±N]). -/
theorem verbal_nominal_inconsistent :
    categoryConsistent .V .N = false := by decide

/-- V and D are NOT category-consistent (verbal ≠ nominal). -/
theorem verbal_determiner_inconsistent :
    categoryConsistent .V .D = false := by decide

-- L-head / F-head classification

/-- F0 is exactly the lexical heads. -/
theorem f0_iff_lexical (c : Cat) :
    isLHead c = true ↔ (c = .V ∨ c = .N ∨ c = .A ∨ c = .P) := by
  cases c <;> simp [isLHead, fValue]

/-- F1+ is exactly the functional heads. -/
theorem fpos_iff_functional (c : Cat) :
    isFHead c = true ↔ (c = .v ∨ c = .n ∨ c = .a ∨ c = .Num ∨ c = .Q ∨ c = .Voice ∨ c = .Appl ∨ c = .D ∨ c = .T ∨ c = .Foc ∨ c = .Top ∨ c = .Fin ∨ c = .C ∨ c = .SA ∨ c = .Force ∨ c = .Neg ∨ c = .Mod ∨ c = .Rel ∨ c = .Pol ∨ c = .Asp ∨ c = .Evid) := by
  cases c <;> simp [isFHead, fValue]

-- Family consistency

/-- Categories in the same family are category-consistent. -/
theorem same_family_consistent (c1 c2 : Cat) :
    catFamily c1 = catFamily c2 → categoryConsistent c1 c2 = true := by
  cases c1 <;> cases c2 <;> simp [catFamily] <;> decide

-- Full verbal chain is well-formed

/-- The full verbal EP spine [V, v, T, C] is category-consistent. -/
theorem full_verbal_ep_consistent :
    allCategoryConsistent [Cat.V, Cat.v, Cat.T, Cat.C] = true := by decide

/-- The full verbal EP spine [V, v, T, C] is F-monotone. -/
theorem full_verbal_ep_monotone :
    allFMonotone [Cat.V, Cat.v, Cat.T, Cat.C] = true := by decide

/-- The full nominal EP spine [N, n, Q, Num, D] is category-consistent. -/
theorem full_nominal_ep_consistent :
    allCategoryConsistent [Cat.N, Cat.n, Cat.Q, Cat.Num, Cat.D] = true := by decide

/-- The full nominal EP spine [N, n, Q, Num, D] is F-monotone. -/
theorem full_nominal_ep_monotone :
    allFMonotone [Cat.N, Cat.n, Cat.Q, Cat.Num, Cat.D] = true := by decide

-- Bridge to BarLevel (from XBar.lean)

/-- F0 categories correspond to BarLevel.zero (head),
    F1+ categories correspond to intermediate/maximal projections.
    This connects Grimshaw's F-level to X-bar bar levels. -/
theorem f0_corresponds_to_head :
    isLHead .V ∧ isLHead .N ∧ isLHead .A ∧ isLHead .P := by decide

/-- Functional heads (F1+) extend the projection beyond the lexical head. -/
theorem fhead_extends_projection :
    isFHead .v ∧ isFHead .n ∧ isFHead .a ∧ isFHead .Num ∧ isFHead .Q ∧
    isFHead .D ∧ isFHead .T ∧ isFHead .C := by decide

/-- The verbal and nominal spines are parallel at F0–F1
    (Grimshaw 2005): V ↔ N (lexical), v ↔ n (categorizer).

    At F2–F3 the spines diverge: T (temporal specification, F2)
    pairs with Q (individuation, F2), while Fin (clause-typing, F3)
    pairs with Num (number, F3). These are structural analogs
    occupying the same EP zone, but their semantic functions differ.
    See `borer_ordering_unique` in `Borer2005.lean` for the formal
    argument that Q must be below Num. -/
theorem verbal_nominal_parallel :
    fValue .V = fValue .N ∧ fValue .v = fValue .n ∧
    fValue .T = fValue .Q ∧ fValue .Fin = fValue .Num := by decide

/-- Is this category a categorizer (Panagiotidis 2015)?
    Categorizers bear substantive, interpretable [N]/[V] features
    and combine with acategorial roots to yield categorized items.

    **Important**: Panagiotidis (§4.5) argues categorizers are NOT functional
    heads — they are the only true *lexical* heads (roots being acategorial).
    Our F-value system (from Grimshaw 2005) places them at F1, which makes
    `isFHead` return true for categorizers. This reflects Grimshaw's architectural
    classification, not Panagiotidis's ontological claim about their nature. -/
def isCategorizer (c : Cat) : Bool :=
  match c with
  | .v | .n | .a => true
  | _            => false

/-- All three categorizers are at F1 in Grimshaw's (2005) F-value system.
    Panagiotidis (2015) predicts this parallelism; the F1 encoding is Grimshaw's. -/
theorem categorizers_at_f1 :
    fValue .v = 1 ∧ fValue .n = 1 ∧ fValue .a = 1 := by decide

/-- The three categorizers are parallel: all at the same F-level. -/
theorem categorizer_parallel :
    fValue .v = fValue .n ∧ fValue .n = fValue .a := by decide

/-- The adjectival categorizer is in the adjectival family (parallel to v→verbal, n→nominal). -/
theorem a_in_adjectival_family :
    catFamily .a = .adjectival := by decide

-- ═══════════════════════════════════════════════════════════════
-- Part 8: Split-CP Extended Projection (Rizzi 1997)
-- ═══════════════════════════════════════════════════════════════

/-- The verbal EP spine with Rizzi's (1997) split-CP layer:
    V → v → T → Fin → Foc → Top → C.
    Fin is the boundary between IP and CP; Foc and Top are
    discourse-related projections between Fin and C (= Force). -/
def splitCPVerbalEP : List Cat := [.V, .v, .T, .Fin, .Foc, .Top, .C]

/-- The split-CP spine is category-consistent: all heads share [+V, -N]. -/
theorem splitCP_ep_consistent :
    allCategoryConsistent splitCPVerbalEP = true := by decide

/-- The split-CP spine is F-monotone: 0 ≤ 1 ≤ 2 ≤ 3 ≤ 4 ≤ 5 ≤ 6.
    This is the key payoff of the fValue fix — before the fix, Fin/Foc/Top/C
    all had fValue 3, so any permutation would trivially pass. -/
theorem splitCP_ep_monotone :
    allFMonotone splitCPVerbalEP = true := by decide

/-- The reverse split-CP ordering [Top, Foc, Fin] is NOT monotone.
    This correctly rules out pathological orderings that the collapsed
    fValues (all = 3) would have accepted. -/
theorem reverse_splitCP_not_monotone :
    allFMonotone [Cat.Top, Cat.Foc, Cat.Fin] = false := by decide

/-- Verbal EP with NegP: V → v → Neg → T → Fin → C.
    Represents a clause with an IP-internal negation layer. -/
def negVerbalEP : List Cat := [.V, .v, .Neg, .T, .Fin, .C]

/-- The verbal EP with NegP is category-consistent. -/
theorem neg_verbal_ep_consistent :
    allCategoryConsistent negVerbalEP = true := by decide

/-- The verbal EP with NegP is F-monotone: 0 ≤ 1 ≤ 2 ≤ 2 ≤ 3 ≤ 6. -/
theorem neg_verbal_ep_monotone :
    allFMonotone negVerbalEP = true := by decide

/-- Full Rizzi left periphery: V → v → T → Fin → Foc → Top → Force.
    Force is the clause-typing head when the CP is fully split. -/
def fullRizziLP : List Cat := [.V, .v, .T, .Fin, .Foc, .Top, .Force]

/-- The full Rizzi left periphery is category-consistent. -/
theorem fullRizziLP_consistent :
    allCategoryConsistent fullRizziLP = true := by decide

/-- The full Rizzi left periphery is F-monotone. -/
theorem fullRizziLP_monotone :
    allFMonotone fullRizziLP = true := by decide

/-- Force and C have the same fValue (they're the same position when unsplit). -/
theorem force_equals_c_fvalue : fValue .Force = fValue .C := by decide

/-- Neg is in the specification domain (same F-level as T and Q). -/
theorem neg_in_specification_domain : fValue .Neg = fValue .T := by decide

/-- New functional heads are all in the verbal family. -/
theorem new_heads_verbal :
    catFamily .Force = .verbal ∧ catFamily .Neg = .verbal ∧
    catFamily .Mod = .verbal ∧ catFamily .Rel = .verbal ∧
    catFamily .Pol = .verbal := by decide

/-- Nominal functional heads are in the nominal family. -/
theorem nominal_functional_heads :
    catFamily .n = .nominal ∧ catFamily .Num = .nominal ∧
    catFamily .Q = .nominal := by decide

-- ═══════════════════════════════════════════════════════════════
-- Part 9: Complement Size (Egressy 2026, Wurmbrand 2014)
-- ═══════════════════════════════════════════════════════════════

/-- The structural size of a clausal complement, determined by the
    highest functional head projected.

    Complement size matters for tense Agree locality (Egressy 2026):
    a CP complement constitutes a phase boundary that blocks upward
    Agree for [uPAST], while a TP complement is transparent.

    Also relevant for Wurmbrand's (2014) three-way infinitival
    classification (restructuring ≈ vP, propositional ≈ TP,
    full finite ≈ CP). -/
structure ComplementSize where
  /-- The highest functional head in the complement -/
  highestHead : Cat
  deriving DecidableEq, BEq, Repr

/-- The F-level of a complement (derived from `fValue`). -/
def ComplementSize.fLevel (cs : ComplementSize) : Nat :=
  fValue cs.highestHead

/-- A complement is phase-sized (≥ CP) if its highest head is at or
    above the C level in the functional sequence. -/
def ComplementSize.isPhaseSized (cs : ComplementSize) : Bool :=
  fValue .C ≤ cs.fLevel

/-- A complement is transparent to tense Agree if it is smaller than
    a full CP — i.e., the highest head is below C in the fseq.

    Egressy (2026): TP complements (fValue 2) are transparent;
    CP complements (fValue 6) are opaque. -/
def ComplementSize.transparentToTenseAgree (cs : ComplementSize) : Bool :=
  cs.fLevel < fValue .C

/-- Standard complement sizes. -/
def ComplementSize.vP : ComplementSize := ⟨.v⟩
def ComplementSize.tP : ComplementSize := ⟨.T⟩
def ComplementSize.finP : ComplementSize := ⟨.Fin⟩
def ComplementSize.cP : ComplementSize := ⟨.C⟩
def ComplementSize.forceP : ComplementSize := ⟨.Force⟩
def ComplementSize.saP : ComplementSize := ⟨.SA⟩

-- ── Bridge theorems ──

/-- vP complements are transparent to tense Agree. -/
theorem vP_transparent : ComplementSize.vP.transparentToTenseAgree = true := by decide

/-- TP complements are transparent to tense Agree. -/
theorem tP_transparent : ComplementSize.tP.transparentToTenseAgree = true := by decide

/-- FinP complements are transparent to tense Agree. -/
theorem finP_transparent : ComplementSize.finP.transparentToTenseAgree = true := by decide

/-- CP complements are opaque to tense Agree. -/
theorem cP_opaque : ComplementSize.cP.transparentToTenseAgree = false := by decide

/-- ForceP complements are opaque to tense Agree. -/
theorem forceP_opaque : ComplementSize.forceP.transparentToTenseAgree = false := by decide

/-- SAP complements are opaque to tense Agree. -/
theorem saP_opaque : ComplementSize.saP.transparentToTenseAgree = false := by decide

/-- Size ordering: vP < TP < FinP < CP. -/
theorem complement_size_ordering :
    ComplementSize.vP.fLevel < ComplementSize.tP.fLevel ∧
    ComplementSize.tP.fLevel < ComplementSize.finP.fLevel ∧
    ComplementSize.finP.fLevel < ComplementSize.cP.fLevel := by decide

end Minimalism
