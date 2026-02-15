import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Algebra.BigOperators.Group.List.Defs

/-!
# Natural Logic Relations and Entailment Signatures (Icard 2012)

Framework-agnostic infrastructure for the natural logic relation algebra and
entailment signatures, following Icard (2012) "Inclusion and Exclusion in
Natural Language."

## Contents

1. **NLRelation** — 7 natural logic relations (≡, ⊑, ⊒, ^, |, ⌣, #)
2. **EntailmentSig** — 9 entailment signatures unifying monotonicity/additivity

## Key operations

- `NLRelation.join` (⋈): determines resultant relation from chained inferences
- `EntailmentSig.compose` (∘): composes entailment signatures
- `EntailmentSig.project` ([]^φ): projects a relation through a function of signature φ

## Algebraic structure

- `NLRelation` carries a `PartialOrder` + `BoundedOrder` (≡ = ⊥, # = ⊤)
- `EntailmentSig` carries a `PartialOrder` + `OrderBot` (all = ⊥) + `Monoid` (compose)

## References

- Icard, T. (2012). Inclusion and Exclusion in Natural Language.
  Studia Logica 100(4), 705–725.
- MacCartney, B. & Manning, C. (2009). An extended model of natural logic.
  IWCS-8.
-/

namespace Core.NaturalLogic

-- ============================================================================
-- §1 — NLRelation: Seven Natural Logic Relations
-- ============================================================================

/--
The seven basic set-theoretic relations between denotations (MacCartney &
Manning 2009, Icard 2012 §1).

| Symbol | Name         | Set relation     | Example            |
|--------|------------- |------------------|--------------------|
| ≡      | equivalence  | A = B            | couch / sofa       |
| ⊑      | forward      | A ⊂ B            | dog / animal       |
| ⊒      | reverse      | A ⊃ B            | animal / dog       |
| ^      | negation     | A ∩ B = ∅, A ∪ B = U | happy / unhappy |
| \|     | alternation  | A ∩ B = ∅         | cat / dog          |
| ⌣      | cover        | A ∪ B = U         | animal / nondog    |
| #      | independent  | all other cases   | hungry / tall      |
-/
inductive NLRelation where
  | equiv       -- ≡ : A = B
  | forward     -- ⊑ : A ⊂ B (forward entailment)
  | reverse     -- ⊒ : A ⊃ B (reverse entailment)
  | negation    -- ^ : complement (A ∩ B = ∅, A ∪ B = U)
  | alternation -- | : disjoint (A ∩ B = ∅)
  | cover       -- ⌣ : exhaustive (A ∪ B = U)
  | independent -- # : none of the above
  deriving DecidableEq, BEq, Repr

namespace NLRelation

/--
Informativity ordering on NL relations (Icard 2012, p.710).

R ≤ R' means R is at least as informative as R'. The lattice has ≡ at
the bottom (most informative) and # at the top (least informative).

Key: ^ (negation) refines both | (alternation) and ⌣ (cover), because
knowing sets are complementary tells you both that they're disjoint (|)
and exhaustive (⌣).
-/
def refines : NLRelation → NLRelation → Bool
  -- ≡ refines everything
  | .equiv, _ => true
  -- ⊑ refines |, ⌣, #
  | .forward, .forward => true
  | .forward, .alternation => true
  | .forward, .cover => true
  | .forward, .independent => true
  -- ⊒ refines |, ⌣, #
  | .reverse, .reverse => true
  | .reverse, .alternation => true
  | .reverse, .cover => true
  | .reverse, .independent => true
  -- ^ refines |, ⌣, #
  | .negation, .negation => true
  | .negation, .alternation => true
  | .negation, .cover => true
  | .negation, .independent => true
  -- | refines #
  | .alternation, .alternation => true
  | .alternation, .independent => true
  -- ⌣ refines #
  | .cover, .cover => true
  | .cover, .independent => true
  -- # refines only itself
  | .independent, .independent => true
  | _, _ => false

-- Mathlib order instances
instance : LE NLRelation where le a b := refines a b = true

private theorem NLRelation.le_refl (a : NLRelation) : refines a a = true := by
  cases a <;> rfl

private theorem NLRelation.le_trans (a b c : NLRelation) :
    refines a b = true → refines b c = true → refines a c = true := by
  cases a <;> cases b <;> cases c <;> simp only [refines] <;> intro h1 h2 <;> trivial

private theorem NLRelation.le_antisymm (a b : NLRelation) :
    refines a b = true → refines b a = true → a = b := by
  cases a <;> cases b <;> simp only [refines] <;> intro h1 h2 <;> trivial

instance : Preorder NLRelation where
  le_refl := NLRelation.le_refl
  le_trans _ _ _ := NLRelation.le_trans _ _ _
instance : PartialOrder NLRelation where
  le_antisymm _ _ := NLRelation.le_antisymm _ _
instance : Bot NLRelation := ⟨.equiv⟩
instance : Top NLRelation := ⟨.independent⟩
instance : OrderBot NLRelation where bot_le a := by cases a <;> rfl
instance : OrderTop NLRelation where le_top a := by cases a <;> rfl
instance : BoundedOrder NLRelation where
  __ := inferInstanceAs (OrderBot NLRelation)
  __ := inferInstanceAs (OrderTop NLRelation)

/--
Join operation ⋈ (Icard 2012, Lemma 1.5).

Given xRy and yR'z, determines the strongest relation x(R⋈R')z.
This is the "join" in the relation algebra sense (not lattice join).
-/
def join : NLRelation → NLRelation → NLRelation
  -- ≡ is the identity
  | .equiv, r => r
  | r, .equiv => r
  -- ⊑ column
  | .forward, .forward => .forward
  | .forward, .reverse => .independent
  | .forward, .negation => .cover
  | .forward, .alternation => .independent
  | .forward, .cover => .cover
  | .forward, .independent => .independent
  -- ⊒ column
  | .reverse, .forward => .independent
  | .reverse, .reverse => .reverse
  | .reverse, .negation => .alternation
  | .reverse, .alternation => .alternation
  | .reverse, .cover => .independent
  | .reverse, .independent => .independent
  -- ^ column
  | .negation, .forward => .alternation
  | .negation, .reverse => .cover
  | .negation, .negation => .equiv
  | .negation, .alternation => .reverse
  | .negation, .cover => .forward
  | .negation, .independent => .independent
  -- | column
  | .alternation, .forward => .alternation
  | .alternation, .reverse => .independent
  | .alternation, .negation => .forward
  | .alternation, .alternation => .independent
  | .alternation, .cover => .forward
  | .alternation, .independent => .independent
  -- ⌣ column
  | .cover, .forward => .independent
  | .cover, .reverse => .cover
  | .cover, .negation => .reverse
  | .cover, .alternation => .reverse
  | .cover, .cover => .independent
  | .cover, .independent => .independent
  -- # column
  | .independent, _ => .independent

-- Spot-checks from Lemma 1.5 table
#guard join .forward .forward == .forward       -- ⊑ ⋈ ⊑ = ⊑
#guard join .negation .negation == .equiv       -- ^ ⋈ ^ = ≡
#guard join .alternation .negation == .forward  -- | ⋈ ^ = ⊑
#guard join .negation .forward == .alternation  -- ^ ⋈ ⊑ = |
#guard join .cover .negation == .reverse        -- ⌣ ⋈ ^ = ⊒

/-- ≡ is the identity for join. -/
theorem join_identity_left (r : NLRelation) : join .equiv r = r := by
  cases r <;> rfl

theorem join_identity_right (r : NLRelation) : join r .equiv = r := by
  cases r <;> rfl

-- Note: join is NOT commutative. E.g., ^⋈⌣ = ⊑ but ⌣⋈^ = ⊒.
-- This is expected: xRy and yR'z is directional.

end NLRelation


-- ============================================================================
-- §2 — EntailmentSig: Entailment Signatures
-- ============================================================================

/--
Entailment signature (Icard 2012, §2).

An entailment signature classifies a function by its algebraic properties
with respect to ∨ and ∧. This unifies the separate monotonicity and
additivity hierarchies into one 9-element lattice.

| Symbol | Name              | Properties                    |
|--------|-------------------|-------------------------------|
| •      | all               | Preserves all 7 relations     |
| +      | mono              | Monotone (= UE)               |
| −      | anti              | Antitone (= DE)               |
| ⊕      | additive          | f(A∨B)=f(A)∨f(B), f(⊤)=⊤    |
| ◇      | antiAdd           | f(A∨B)=f(A)∧f(B)             |
| ⊞      | mult              | f(A∧B)=f(A)∧f(B), f(⊥)=⊥    |
| ⊟      | antiMult          | f(A∧B)=f(A)∨f(B), f(⊥)=⊤    |
| ⊕⊞     | addMult           | Additive + Multiplicative     |
| ◇⊟     | antiAddMult       | Anti-additive + Anti-mult     |
-/
inductive EntailmentSig where
  | all           -- • : preserves all relations
  | mono          -- + : monotone (UE)
  | anti          -- − : antitone (DE)
  | additive      -- ⊕ : additive
  | antiAdd       -- ◇ : anti-additive
  | mult          -- ⊞ : multiplicative
  | antiMult      -- ⊟ : anti-multiplicative
  | addMult       -- ⊕⊞ : additive + multiplicative (morphism)
  | antiAddMult   -- ◇⊟ : anti-additive + anti-multiplicative (anti-morphism)
  deriving DecidableEq, BEq, Repr

namespace EntailmentSig

/--
Refinement ordering on entailment signatures (Icard 2012, p.715).

The lattice has `all` at the bottom (most specific) and `mono`/`anti`
at the top of their respective halves.
-/
def refines : EntailmentSig → EntailmentSig → Bool
  -- all refines everything
  | .all, _ => true
  -- addMult refines additive, mult, mono
  | .addMult, .addMult => true
  | .addMult, .additive => true
  | .addMult, .mult => true
  | .addMult, .mono => true
  -- antiAddMult refines antiAdd, antiMult, anti
  | .antiAddMult, .antiAddMult => true
  | .antiAddMult, .antiAdd => true
  | .antiAddMult, .antiMult => true
  | .antiAddMult, .anti => true
  -- additive refines mono
  | .additive, .additive => true
  | .additive, .mono => true
  -- mult refines mono
  | .mult, .mult => true
  | .mult, .mono => true
  -- antiAdd refines anti
  | .antiAdd, .antiAdd => true
  | .antiAdd, .anti => true
  -- antiMult refines anti
  | .antiMult, .antiMult => true
  | .antiMult, .anti => true
  -- mono and anti refine only themselves
  | .mono, .mono => true
  | .anti, .anti => true
  | _, _ => false

-- Spot-checks for the refinement lattice
#guard refines .all .mono          -- • ≤ +
#guard refines .all .anti          -- • ≤ −
#guard refines .addMult .additive  -- ⊕⊞ ≤ ⊕
#guard refines .antiAddMult .anti  -- ◇⊟ ≤ −
#guard !refines .mono .additive    -- + ≰ ⊕
#guard !refines .additive .mult    -- ⊕ ≰ ⊞

-- Mathlib order instances
instance : LE EntailmentSig where le a b := refines a b = true

private theorem EntailmentSig.le_refl (a : EntailmentSig) : refines a a = true := by
  cases a <;> rfl

private theorem EntailmentSig.le_trans (a b c : EntailmentSig) :
    refines a b = true → refines b c = true → refines a c = true := by
  cases a <;> cases b <;> cases c <;> simp only [refines] <;> intro h1 h2 <;> trivial

private theorem EntailmentSig.le_antisymm (a b : EntailmentSig) :
    refines a b = true → refines b a = true → a = b := by
  cases a <;> cases b <;> simp only [refines] <;> intro h1 h2 <;> trivial

instance : Preorder EntailmentSig where
  le_refl := EntailmentSig.le_refl
  le_trans _ _ _ := EntailmentSig.le_trans _ _ _
instance : PartialOrder EntailmentSig where
  le_antisymm _ _ := EntailmentSig.le_antisymm _ _
instance : Bot EntailmentSig := ⟨.all⟩
instance : OrderBot EntailmentSig where bot_le a := by cases a <;> rfl

/--
Projection of a NL relation through a function of given signature
(Icard 2012, Lemma 2.4).

If xRy and f has signature φ, then f(x) [R]^φ f(y).
Returns the ≪-maximal relation guaranteed to hold between f(x) and f(y).

The table follows from the algebraic definitions:
- Additive: f(x∨y) = f(x)∨f(y), f(1)=1 → preserves ∨ → [∧]^⊕ = ∼ (cover from x∨y=1)
- Multiplicative: f(x∧y) = f(x)∧f(y), f(0)=0 → preserves ∧ → [|]^⊞ = | (disjoint from x∧y=0)
- Anti-additive: f(x∨y) = f(x)∧f(y), f(1)=0 → [∼]^◇ = | (from x∨y=1 ⟹ f(x)∧f(y)=0)
- Anti-multiplicative: f(x∧y) = f(x)∨f(y), f(0)=1 → [|]^⊟ = ∼ (from x∧y=0 ⟹ f(x)∨f(y)=1)
- Mono/anti alone: only preserves ⊑/⊒; ^, |, ∼ all weaken to #
-/
def project : NLRelation → EntailmentSig → NLRelation
  -- all (•): preserves everything
  | r, .all => r
  -- addMult (⊕⊞): full morphism, preserves all 7 relations
  | r, .addMult => r
  -- antiAddMult (◇⊟): full anti-morphism — swaps | ↔ ∼, preserves ^
  | .equiv, .antiAddMult => .equiv
  | .forward, .antiAddMult => .reverse
  | .reverse, .antiAddMult => .forward
  | .negation, .antiAddMult => .negation
  | .alternation, .antiAddMult => .cover        -- x∧y=0 ⟹ f(x)∨f(y)=1
  | .cover, .antiAddMult => .alternation         -- x∨y=1 ⟹ f(x)∧f(y)=0
  | .independent, .antiAddMult => .independent
  -- mono (+): preserves ⊑/⊒ only; ^, |, ∼ all weaken to #
  | .equiv, .mono => .equiv
  | .forward, .mono => .forward
  | .reverse, .mono => .reverse
  | .negation, .mono => .independent
  | .alternation, .mono => .independent
  | .cover, .mono => .independent
  | .independent, .mono => .independent
  -- anti (−): reverses ⊑↔⊒; ^, |, ∼ all weaken to #
  | .equiv, .anti => .equiv
  | .forward, .anti => .reverse
  | .reverse, .anti => .forward
  | .negation, .anti => .independent
  | .alternation, .anti => .independent
  | .cover, .anti => .independent
  | .independent, .anti => .independent
  -- additive (⊕): ∨-preserving → x∨y=1 ⟹ f(x)∨f(y)=1 (cover preserved)
  | .equiv, .additive => .equiv
  | .forward, .additive => .forward
  | .reverse, .additive => .reverse
  | .negation, .additive => .cover              -- x∨y=1 ⟹ f(x)∨f(y)=1
  | .alternation, .additive => .independent     -- x∧y=0 gives nothing
  | .cover, .additive => .cover                  -- x∨y=1 ⟹ f(x)∨f(y)=1
  | .independent, .additive => .independent
  -- antiAdd (◇): ∨→∧ — x∨y=1 ⟹ f(x)∧f(y)=0 (disjoint)
  | .equiv, .antiAdd => .equiv
  | .forward, .antiAdd => .reverse
  | .reverse, .antiAdd => .forward
  | .negation, .antiAdd => .alternation          -- x∨y=1 ⟹ f(x)∧f(y)=0
  | .alternation, .antiAdd => .independent       -- x∧y=0 gives nothing
  | .cover, .antiAdd => .alternation             -- x∨y=1 ⟹ f(x)∧f(y)=0
  | .independent, .antiAdd => .independent
  -- mult (⊞): ∧-preserving → x∧y=0 ⟹ f(x)∧f(y)=0 (disjointness preserved)
  | .equiv, .mult => .equiv
  | .forward, .mult => .forward
  | .reverse, .mult => .reverse
  | .negation, .mult => .alternation             -- x∧y=0 ⟹ f(x)∧f(y)=0
  | .alternation, .mult => .alternation          -- x∧y=0 ⟹ f(x)∧f(y)=0
  | .cover, .mult => .independent                -- x∨y=1 gives nothing
  | .independent, .mult => .independent
  -- antiMult (⊟): ∧→∨ — x∧y=0 ⟹ f(x)∨f(y)=1 (cover)
  | .equiv, .antiMult => .equiv
  | .forward, .antiMult => .reverse
  | .reverse, .antiMult => .forward
  | .negation, .antiMult => .cover               -- x∧y=0 ⟹ f(x)∨f(y)=1
  | .alternation, .antiMult => .cover            -- x∧y=0 ⟹ f(x)∨f(y)=1
  | .cover, .antiMult => .independent            -- x∨y=1 gives nothing
  | .independent, .antiMult => .independent

-- Spot-checks from Lemma 2.4 tables (p.715)
#guard project .forward .mono == .forward            -- [⊑]^+ = ⊑
#guard project .forward .anti == .reverse            -- [⊑]^− = ⊒
#guard project .negation .mono == .independent       -- [^]^+ = #
#guard project .negation .anti == .independent       -- [^]^− = #
#guard project .negation .additive == .cover         -- [^]^⊕ = ∼
#guard project .negation .mult == .alternation       -- [^]^⊞ = |
#guard project .negation .antiAddMult == .negation   -- [^]^◇⊟ = ^
#guard project .alternation .mult == .alternation    -- [|]^⊞ = |
#guard project .alternation .additive == .independent -- [|]^⊕ = #
#guard project .cover .additive == .cover            -- [∼]^⊕ = ∼
#guard project .cover .mult == .independent          -- [∼]^⊞ = #
#guard project .cover .antiAdd == .alternation       -- [∼]^◇ = |
#guard project .alternation .antiMult == .cover      -- [|]^⊟ = ∼
#guard project .alternation .antiAddMult == .cover   -- [|]^◇⊟ = ∼
#guard project .cover .antiAddMult == .alternation   -- [∼]^◇⊟ = |

/-- Projection preserves equiv for all signatures. -/
theorem project_equiv (φ : EntailmentSig) : project .equiv φ = .equiv := by
  cases φ <;> rfl

/-- Projection preserves independent for all signatures. -/
theorem project_independent (φ : EntailmentSig) : project .independent φ = .independent := by
  cases φ <;> rfl

/--
Recover an entailment signature from its projection of `forward` and
`negation`. These two probes uniquely identify each signature (up to
the observational equivalence of `all` ≅ `addMult`).
-/
private def fromProjectionPair : NLRelation → NLRelation → EntailmentSig
  | .forward, .independent => .mono
  | .forward, .cover       => .additive
  | .forward, .alternation => .mult
  | .forward, .negation    => .addMult
  | .reverse, .independent => .anti
  | .reverse, .alternation => .antiAdd
  | .reverse, .cover       => .antiMult
  | .reverse, .negation    => .antiAddMult
  | _, _ => .mono  -- unreachable for valid projection pairs

/--
Composition of entailment signatures (Icard 2012, Lemma 2.7).

**Derived from `project`**: compose(ψ, φ) is the unique signature whose
projection table matches projecting through φ then ψ. This makes
`projection_composition` hold by finite verification rather than
requiring two independently maintained tables to agree.

The signature is identified by probing with `forward` and `negation`,
which suffice to distinguish all 9 signatures (with `all` handled
separately as the identity element).
-/
def compose (ψ φ : EntailmentSig) : EntailmentSig :=
  match φ, ψ with
  | .all, s => s
  | s, .all => s
  | _, _ => fromProjectionPair
      (project (project .forward φ) ψ)
      (project (project .negation φ) ψ)

-- Spot-checks (Lemma 2.7 table, p.716)
#guard compose .anti .anti == .mono                   -- − ∘ − = +
#guard compose .antiAddMult .antiAddMult == .addMult  -- ◇⊟ ∘ ◇⊟ = ⊕⊞
#guard compose .additive .additive == .additive       -- ⊕ ∘ ⊕ = ⊕
#guard compose .antiAdd .additive == .antiAdd         -- ◇ ∘ ⊕ = ◇
#guard compose .addMult .anti == .anti                -- ⊕⊞ ∘ − = −
#guard compose .mult .antiAdd == .antiAdd             -- ⊞ ∘ ◇ = ◇
#guard compose .additive .antiMult == .antiMult       -- ⊕ ∘ ⊟ = ⊟
#guard compose .antiMult .antiAdd == .additive        -- ⊟ ∘ ◇ = ⊕
#guard compose .mult .mult == .mult                   -- ⊞ ∘ ⊞ = ⊞
#guard compose .additive .antiAdd == .anti            -- ⊕ ∘ ◇ = −

/-- `all` is the identity for composition. -/
theorem compose_identity_left (s : EntailmentSig) : compose .all s = s := by
  cases s <;> rfl

theorem compose_identity_right (s : EntailmentSig) : compose s .all = s := by
  cases s <;> rfl

/-- Composition is associative. -/
theorem compose_assoc (a b c : EntailmentSig) :
    compose (compose a b) c = compose a (compose b c) := by
  cases a <;> cases b <;> cases c <;> native_decide

-- Monoid instance (compose with identity `all`)
instance : Mul EntailmentSig where mul := compose
instance : One EntailmentSig where one := .all
instance : Monoid EntailmentSig where
  mul_assoc a b c := compose_assoc a b c
  one_mul := compose_identity_left
  mul_one := compose_identity_right

end EntailmentSig


-- ============================================================================
-- §3 — Entailment Strength Hierarchies
-- ============================================================================

/--
Strength of downward entailingness (Zwarts 1996).

Names the three levels of the DE hierarchy:
- `.weak` = DE only (licenses weak NPIs: ever, any)
- `.antiAdditive` = DE + ∨→∧ distributive (licenses strong NPIs: lift a finger)
- `.antiMorphic` = AA + ∧→∨ distributive (= negation)
-/
inductive DEStrength where
  | weak           -- Plain DE (licenses weak NPIs)
  | antiAdditive   -- DE + ∨-distributive (licenses strong NPIs)
  | antiMorphic    -- Anti-additive + ∧-distributive (= negation)
  deriving DecidableEq, BEq, Repr

/--
Strength of upward entailingness (dual of DEStrength).

Names the three levels of the UE hierarchy:
- `.weak` = plain UE (monotone)
- `.multiplicative` = UE + ∧-distributive
- `.additive` = UE + ∨-distributive (strongest)
-/
inductive UEStrength where
  | weak           -- Plain UE (monotone)
  | multiplicative -- UE + ∧-distributive
  | additive       -- UE + ∨-distributive (strongest)
  deriving DecidableEq, BEq, Repr

/--
Check if a context's DE strength is sufficient for an NPI.

`strengthSufficient contextStrength requiredStrength` returns true
when `contextStrength ≥ requiredStrength` in the Zwarts hierarchy.
-/
def strengthSufficient (contextStrength requiredStrength : DEStrength) : Bool :=
  match requiredStrength, contextStrength with
  | .weak, _ => true
  | .antiAdditive, .weak => false
  | .antiAdditive, _ => true
  | .antiMorphic, .antiMorphic => true
  | .antiMorphic, _ => false

#guard strengthSufficient .antiMorphic .weak          -- negation licenses weak NPIs
#guard strengthSufficient .antiMorphic .antiAdditive   -- negation licenses strong NPIs
#guard strengthSufficient .antiAdditive .weak          -- "no" licenses weak NPIs
#guard strengthSufficient .antiAdditive .antiAdditive   -- "no" licenses strong NPIs
#guard strengthSufficient .weak .weak                  -- "few" licenses weak NPIs
#guard !strengthSufficient .weak .antiAdditive          -- "few" does NOT license strong NPIs


-- ============================================================================
-- §4 — Signature ↔ Strength Bridge Maps
-- ============================================================================

namespace EntailmentSig

/--
Map an entailment signature to DE strength, derived from `project`.

A signature is DE iff it reverses forward entailment: `[⊑]^φ = ⊒`.
Within the DE side, anti-additivity is detected by `[∼]^φ = |`
(the ∨→∧ swap: x∨y=1 ⟹ f(x)∧f(y)=0), and anti-morphism additionally
requires `[|]^φ = ∼` (the ∧→∨ swap).

Returns `none` for UE-side signatures.
-/
def toDEStrength (φ : EntailmentSig) : Option DEStrength :=
  if project .forward φ != .reverse then none
  else if project .cover φ == .alternation then
    if project .alternation φ == .cover then some .antiMorphic
    else some .antiAdditive
  else some .weak

/--
Map an entailment signature to UE strength, derived from `project`.

A signature is UE iff it preserves forward entailment: `[⊑]^φ = ⊑`.
Additivity is detected by `[∼]^φ = ∼` (∨-preservation: x∨y=1 ⟹ f(x)∨f(y)=1),
and multiplicativity by `[|]^φ = |` (∧-preservation: x∧y=0 ⟹ f(x)∧f(y)=0).

Returns `none` for DE-side signatures.
-/
def toUEStrength (φ : EntailmentSig) : Option UEStrength :=
  if project .forward φ != .forward then none
  else if project .cover φ == .cover then some .additive
  else if project .alternation φ == .alternation then some .multiplicative
  else some .weak

-- DE strength — exhaustive verification against all 9 signatures
#guard toDEStrength .all == none
#guard toDEStrength .mono == none
#guard toDEStrength .additive == none
#guard toDEStrength .mult == none
#guard toDEStrength .addMult == none
#guard toDEStrength .anti == some .weak
#guard toDEStrength .antiAdd == some .antiAdditive
#guard toDEStrength .antiMult == some .weak
#guard toDEStrength .antiAddMult == some .antiMorphic

-- UE strength — exhaustive verification against all 9 signatures
#guard toUEStrength .all == some .additive
#guard toUEStrength .mono == some .weak
#guard toUEStrength .additive == some .additive
#guard toUEStrength .mult == some .multiplicative
#guard toUEStrength .addMult == some .additive
#guard toUEStrength .anti == none
#guard toUEStrength .antiAdd == none
#guard toUEStrength .antiMult == none
#guard toUEStrength .antiAddMult == none

end EntailmentSig


-- ============================================================================
-- §5 — Context Polarity
-- ============================================================================

/--
Whether a context preserves or reverses entailment direction.

This is a coarsening of `EntailmentSig`: all UE-side signatures collapse to
`.upward`, all DE-side signatures collapse to `.downward`. Contexts that are
neither monotone nor antitone (e.g., "exactly n") are `.nonMonotonic`.

Used by:
- NeoGricean: determines which alternatives count as "stronger"
- RSA: polarity-sensitive inference
- Any theory computing scalar implicatures
-/
inductive ContextPolarity where
  | upward       -- Preserves entailment (stronger alternatives)
  | downward     -- Reverses entailment (weaker alternatives become stronger)
  | nonMonotonic -- Neither (e.g., "exactly n")
  deriving DecidableEq, BEq, Repr

namespace ContextPolarity

/--
Compose context polarities.

This is the coarse composition table derived from the `EntailmentSig` monoid:
UE ∘ UE = UE, DE ∘ DE = UE (double negation), UE ∘ DE = DE, DE ∘ UE = DE.
Any composition involving `nonMonotonic` yields `nonMonotonic`.
-/
def compose : ContextPolarity → ContextPolarity → ContextPolarity
  | .upward, x => x
  | x, .upward => x
  | .downward, .downward => .upward
  | .nonMonotonic, _ => .nonMonotonic
  | _, .nonMonotonic => .nonMonotonic

#guard compose .upward .downward == .downward
#guard compose .downward .downward == .upward
#guard compose .downward .upward == .downward

end ContextPolarity

namespace EntailmentSig

/--
Map an entailment signature to the coarser `ContextPolarity` type,
derived from `project`.

A signature is UE iff it preserves forward entailment (`[⊑]^φ = ⊑`),
DE iff it reverses it (`[⊑]^φ = ⊒`).
-/
def toContextPolarity (φ : EntailmentSig) : ContextPolarity :=
  if project .forward φ == .forward then .upward
  else if project .forward φ == .reverse then .downward
  else .nonMonotonic

-- Exhaustive verification
#guard toContextPolarity .all == .upward
#guard toContextPolarity .mono == .upward
#guard toContextPolarity .additive == .upward
#guard toContextPolarity .mult == .upward
#guard toContextPolarity .addMult == .upward
#guard toContextPolarity .anti == .downward
#guard toContextPolarity .antiAdd == .downward
#guard toContextPolarity .antiMult == .downward
#guard toContextPolarity .antiAddMult == .downward

/--
`toContextPolarity` is a monoid homomorphism: composing signatures then
coarsening gives the same result as coarsening then composing polarities.

This theorem connects the fine-grained `EntailmentSig` monoid to the
coarse `ContextPolarity` composition, ensuring the two systems can never
disagree.
-/
theorem toContextPolarity_compose (φ ψ : EntailmentSig) :
    toContextPolarity (φ * ψ) =
    (toContextPolarity φ).compose (toContextPolarity ψ) := by
  cases φ <;> cases ψ <;> native_decide

/--
Compute the projectivity signature of a context from the signatures along
the path from the target position to the root (Icard 2012, Definition 2.9).

Given a parse tree and a target position (e.g., "dangerous" in
"Every job that involves a giant squid is dangerous"), the path collects
the `top` signature of each node from the target up to the root.
The composed signature is `List.prod`, using the `Monoid` instance.

Example from Icard §3.2:
  path = [⊞, ⊕, ◇]  (top(is) ∘ top(involves) ∘ top(every_restrictor))
  contextProjectivity path = ◇ (anti-additive)
-/
def contextProjectivity (path : List EntailmentSig) : EntailmentSig :=
  path.prod

/--
Project a NL relation through a context given by its signature path.
Combines `contextProjectivity` with `project`.
-/
def projectThrough (R : NLRelation) (path : List EntailmentSig) : NLRelation :=
  project R (contextProjectivity path)

-- Icard §2.4: path lists signatures from root (outermost) to target (innermost).
-- List.prod applies them right-to-left: the last element is applied first.

-- "animal" in "Every animal runs": path = [◇] (every_restrictor = anti-additive)
#guard contextProjectivity [.antiAdd] == .antiAdd

-- "runs" in "Every animal runs": path = [⊞] (every_scope = multiplicative)
#guard contextProjectivity [.mult] == .mult

-- "cat" in "No big cat runs": path = [◇, ⊕⊞] (no_restrictor = ◇, big = ⊕⊞)
-- ◇ ∘ ⊕⊞ = ◇ (anti-additive composed with morphism stays anti-additive)
#guard contextProjectivity [.antiAdd, .addMult] == .antiAdd

-- "runs" in "It's not the case that every animal runs":
-- path = [◇⊟, ⊞] (negation = ◇⊟, every_scope = ⊞)
-- ◇⊟ ∘ ⊞ = ⊟ (anti-multiplicative)
#guard contextProjectivity [.antiAddMult, .mult] == .antiMult

-- Double negation: ◇⊟ ∘ ◇⊟ = ⊕⊞ (morphism = preserves everything)
#guard contextProjectivity [.antiAddMult, .antiAddMult] == .addMult

-- And its polarity: morphism → upward
#guard toContextPolarity (contextProjectivity [.antiAddMult, .antiAddMult]) == .upward

end EntailmentSig


-- ============================================================================
-- §6 — Inference Rules
-- ============================================================================

/--
Projection composition (Icard 2012, Corollary 2.12).

Projecting through f then g is the same as projecting through g∘f.
This is the compositionality principle: nested function application
corresponds to signature composition.

Since `compose` is derived from `project` (via `fromProjectionPair`),
the only content of this theorem is that the two probe relations
(forward, negation) suffice to determine the full projection table.
-/
theorem projection_composition (R : NLRelation) (φ ψ : EntailmentSig) :
    EntailmentSig.project (EntailmentSig.project R φ) ψ =
    EntailmentSig.project R (EntailmentSig.compose ψ φ) := by
  cases R <;> cases φ <;> cases ψ <;> native_decide


-- ============================================================================
-- §7 — NPI Connection Theorems
-- ============================================================================

/--
Any DE-side signature licenses weak NPIs.

This connects Icard's signature lattice to Ladusaw (1980): a signature on
the DE side (anti, antiAdd, antiMult, antiAddMult) creates a DE context,
which is sufficient for weak NPI licensing.
-/
theorem de_signature_licenses_weak_npi (σ : EntailmentSig) :
    EntailmentSig.toContextPolarity σ = .downward →
    (EntailmentSig.toDEStrength σ).isSome = true := by
  cases σ <;> simp [EntailmentSig.toContextPolarity] <;> native_decide

/--
Anti-additive or stronger signature licenses strong NPIs.

Strong NPIs (lift a finger, in weeks) require anti-additive contexts
(Zwarts 1996). In Icard's system, this corresponds to signatures
antiAdd, antiAddMult — but NOT plain anti or antiMult.
-/
theorem strong_npi_requires_antiadditive (σ : EntailmentSig) :
    EntailmentSig.toDEStrength σ = some DEStrength.antiAdditive ∨
    EntailmentSig.toDEStrength σ = some DEStrength.antiMorphic →
    EntailmentSig.toContextPolarity σ = ContextPolarity.downward := by
  cases σ <;> simp [EntailmentSig.toContextPolarity] <;> native_decide

-- Verify: antiMult is DE but NOT anti-additive (licenses weak but not strong NPIs)
#guard EntailmentSig.toDEStrength .antiMult == some .weak
#guard EntailmentSig.toContextPolarity .antiMult == .downward


-- ============================================================================
-- §8 — Negation Signature & Projection Examples
-- ============================================================================

/-- Negation has the anti-morphism signature ◇⊟ (strongest DE signature). -/
def negationSig : EntailmentSig := .antiAddMult

#guard EntailmentSig.toContextPolarity negationSig == .downward
#guard EntailmentSig.toDEStrength negationSig == some DEStrength.antiMorphic

-- Monoid notation: negationSig * negationSig = double negation = morphism
#guard negationSig * negationSig == .addMult

-- negationSig ^ 2 = ⊕⊞ (via Monoid.npow)
#guard negationSig ^ 2 == .addMult

-- Negation is its own inverse (up to •/⊕⊞ equivalence):
-- ◇⊟ * ◇⊟ = ⊕⊞ (the monoid identity on non-• signatures)
#guard negationSig * negationSig * negationSig == negationSig

-- Composing negation with "every" scope: ◇⊟ * ⊞ = ⊟ (anti-multiplicative)
#guard negationSig * .mult == .antiMult

-- Chain composition: not(not(every ... )) scope = ⊟ * ◇⊟ * ◇⊟ = ⊟ * ⊕⊞ = ⊟
#guard .antiMult * negationSig * negationSig == .antiMult

-- Forward entailment (dog ⊑ animal) projected through various signatures:
#guard EntailmentSig.project .forward .mono == .forward           -- + : dog ⊑ animal ⟹ f(dog) ⊑ f(animal)
#guard EntailmentSig.project .forward .anti == .reverse           -- − : dog ⊑ animal ⟹ f(dog) ⊒ f(animal)
#guard EntailmentSig.project .forward .additive == .forward       -- ⊕ : same as mono for ⊑
#guard EntailmentSig.project .forward .antiAddMult == .reverse    -- ◇⊟ : same as anti for ⊑

-- Alternation (cat | dog) projected through various signatures:
#guard EntailmentSig.project .alternation .mono == .independent     -- + : mono alone can't track disjointness
#guard EntailmentSig.project .alternation .mult == .alternation     -- ⊞ : mult preserves ∧, so preserves |
#guard EntailmentSig.project .alternation .antiMult == .cover       -- ⊟ : anti-mult flips | to ∼

-- Cover (animal ∼ nondog) projected through various signatures:
#guard EntailmentSig.project .cover .additive == .cover             -- ⊕ : additive preserves ∨, so preserves ∼
#guard EntailmentSig.project .cover .mult == .independent           -- ⊞ : mult can't track ∨-structure
#guard EntailmentSig.project .cover .antiAdd == .alternation        -- ◇ : anti-additive flips ∼ to |
#guard EntailmentSig.project .cover .antiAddMult == .alternation    -- ◇⊟ : anti-morph swaps | ↔ ∼

end Core.NaturalLogic
