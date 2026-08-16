import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Data.Nat.Basic

/-!
# The natural-logic relation algebra
[icard-2012] [maccartney-manning-2009]

The seven natural-logic relations (≡ ⊑ ⊒ ^ | ⌣ #) and the nine
entailment signatures of [icard-2012], with the operations that run the
calculus: `join` chains relations, `project` pushes a relation through a
function of known signature, and `compose` — derived from `project` by
probing, so `projection_composition` holds by construction — makes the
signatures a monoid (identity `addMult`, `all` absorbing). Both
`Refines` orders are partial orders with `#` (resp. `•`) at top; there
is no bottom (`≡` does not refine the exclusion relations). Semantic
certification lives in `Logic/Natural/Soundness.lean`:
`NLRelation.Holds.join` for the join table, the `soundFor_*` row
theorems for projection.

## Main declarations

* `NLRelation`, `NLRelation.join`, `NLRelation.Refines` — the relation
  algebra.
* `EntailmentSig`, `EntailmentSig.project`, `EntailmentSig.compose` —
  signatures, projection, and the composition monoid.
* `EntailmentSig.contextProjectivity` — a position's signature as the
  monoid product along its path.
* `ContextPolarity`, `EntailmentSig.toContextPolarity` — the coarse
  UE/DE quotient, a monoid homomorphism target
  (`toContextPolarity_compose`).
-/

namespace NaturalLogic

/-! ### The seven relations -/

/--
The seven basic set-theoretic relations between denotations ([maccartney-manning-2009], [icard-2012] §1).

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
  deriving DecidableEq, Repr

namespace NLRelation

/--
Informativity ordering on NL relations.

R ≤ R' means R is at least as informative as R'. The lattice has ≡ at
# at the top (least informative); there is no bottom — the two diamonds
(≡ over ⊑/⊒, ^ over |/⌣) meet only at #.

`Refines R R'` is the implication ordering ([icard-2012] §1): `xRy`
entails `xR'y` (certified semantically by `NLRelation.Holds.of_refines`
in `Logic/Natural/Soundness.lean`). ≡ refines the inclusion
relations but not the exclusion relations (`x = y` does not make `x`,`y`
disjoint or exhaustive); ^ refines both | and ⌣.
-/
def Refines : NLRelation → NLRelation → Prop
  | .equiv, .equiv | .equiv, .forward
  | .equiv, .reverse | .equiv, .independent => True
  | .forward, .forward | .forward, .independent => True
  | .reverse, .reverse | .reverse, .independent => True
  | .negation, .negation | .negation, .alternation
  | .negation, .cover | .negation, .independent => True
  | .alternation, .alternation | .alternation, .independent => True
  | .cover, .cover | .cover, .independent => True
  | .independent, .independent => True
  | _, _ => False

instance : DecidableRel (α := NLRelation) Refines := fun a b =>
  match a, b with
  | .equiv, .equiv | .equiv, .forward | .equiv, .reverse
  | .equiv, .independent => isTrue trivial
  | .forward, .forward | .forward, .independent => isTrue trivial
  | .reverse, .reverse | .reverse, .independent => isTrue trivial
  | .negation, .negation | .negation, .alternation
  | .negation, .cover | .negation, .independent => isTrue trivial
  | .alternation, .alternation | .alternation, .independent => isTrue trivial
  | .cover, .cover | .cover, .independent => isTrue trivial
  | .independent, .independent => isTrue trivial
  | .equiv, .negation | .equiv, .alternation | .equiv, .cover
  | .forward, .equiv | .forward, .reverse | .forward, .negation
  | .forward, .alternation | .forward, .cover
  | .reverse, .equiv | .reverse, .forward | .reverse, .negation
  | .reverse, .alternation | .reverse, .cover
  | .negation, .equiv | .negation, .forward | .negation, .reverse
  | .alternation, .equiv | .alternation, .forward | .alternation, .reverse
  | .alternation, .negation | .alternation, .cover
  | .cover, .equiv | .cover, .forward | .cover, .reverse
  | .cover, .negation | .cover, .alternation
  | .independent, .equiv | .independent, .forward | .independent, .reverse
  | .independent, .negation | .independent, .alternation | .independent, .cover
    => isFalse not_false

instance : LE NLRelation := ⟨Refines⟩

instance decidableLE (a b : NLRelation) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (Refines a b))

private theorem Refines_refl (a : NLRelation) : Refines a a := by
  cases a <;> decide

private theorem Refines_trans (a b c : NLRelation) :
    Refines a b → Refines b c → Refines a c := by
  cases a <;> cases b <;> cases c <;> decide

private theorem Refines_antisymm (a b : NLRelation) :
    Refines a b → Refines b a → a = b := by
  cases a <;> cases b <;> decide

instance : Preorder NLRelation where
  le := Refines
  le_refl := Refines_refl
  le_trans := Refines_trans
instance : PartialOrder NLRelation where
  le_antisymm := Refines_antisymm
instance : Top NLRelation := ⟨.independent⟩
instance : OrderTop NLRelation where
  le_top a := show Refines a .independent by cases a <;> trivial

/--
Join operation ⋈ ([icard-2012], Lemma 1.5): given `xRy` and `yR'z`, the
strongest relation guaranteed between `x` and `z` — relation-algebra
join, not lattice join. The table is derived from the non-strict
`Holds` reading and certified cell-by-cell by `NLRelation.Holds.join`
in `Logic/Natural/Soundness.lean`.
-/
def join : NLRelation → NLRelation → NLRelation
  -- ≡ is the identity
  | .equiv, r => r
  | r, .equiv => r
  -- ⊑ column
  | .forward, .forward => .forward
  | .forward, .reverse => .independent
  | .forward, .negation => .alternation
  | .forward, .alternation => .alternation
  | .forward, .cover => .independent
  | .forward, .independent => .independent
  -- ⊒ column
  | .reverse, .forward => .independent
  | .reverse, .reverse => .reverse
  | .reverse, .negation => .cover
  | .reverse, .alternation => .independent
  | .reverse, .cover => .cover
  | .reverse, .independent => .independent
  -- ^ column
  | .negation, .forward => .cover
  | .negation, .reverse => .alternation
  | .negation, .negation => .equiv
  | .negation, .alternation => .reverse
  | .negation, .cover => .forward
  | .negation, .independent => .independent
  -- | column
  | .alternation, .forward => .independent
  | .alternation, .reverse => .alternation
  | .alternation, .negation => .forward
  | .alternation, .alternation => .independent
  | .alternation, .cover => .forward
  | .alternation, .independent => .independent
  -- ⌣ column
  | .cover, .forward => .cover
  | .cover, .reverse => .independent
  | .cover, .negation => .reverse
  | .cover, .alternation => .reverse
  | .cover, .cover => .independent
  | .cover, .independent => .independent
  -- # column
  | .independent, _ => .independent

-- Spot-checks from Lemma 1.5 table
example : join .forward .forward = .forward := rfl       -- ⊑ ⋈ ⊑ = ⊑
example : join .negation .negation = .equiv := rfl       -- ^ ⋈ ^ = ≡
example : join .alternation .negation = .forward := rfl  -- | ⋈ ^ = ⊑
example : join .negation .forward = .cover := rfl        -- ^ ⋈ ⊑ = ⌣
example : join .cover .negation = .reverse := rfl        -- ⌣ ⋈ ^ = ⊒

/-- ≡ is the identity for join. -/
theorem join_identity_left (r : NLRelation) : join .equiv r = r := by
  cases r <;> rfl

theorem join_identity_right (r : NLRelation) : join r .equiv = r := by
  cases r <;> rfl

-- Note: join is NOT commutative. E.g., ^⋈⌣ = ⊑ but ⌣⋈^ = ⊒.
-- This is expected: xRy and yR'z is directional.

end NLRelation


/-! ### Entailment signatures -/

/--
Entailment signature.

An entailment signature classifies a function by its algebraic properties
with respect to ∨ and ∧. This unifies the separate monotonicity and
additivity hierarchies into one 9-element lattice.

| Symbol | Name              | Properties                    |
|--------|-------------------|-------------------------------|
| •      | all               | Any function (no property)    |
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
  | all           -- • : any function (no property; projects everything to #)
  | mono          -- + : monotone (UE)
  | anti          -- − : antitone (DE)
  | additive      -- ⊕ : additive
  | antiAdd       -- ◇ : anti-additive
  | mult          -- ⊞ : multiplicative
  | antiMult      -- ⊟ : anti-multiplicative
  | addMult       -- ⊕⊞ : additive + multiplicative (morphism)
  | antiAddMult   -- ◇⊟ : anti-additive + anti-multiplicative (anti-morphism)
  deriving DecidableEq, Repr

namespace EntailmentSig

/--
Refinement ordering on entailment signatures: `σ.Refines τ` iff every
σ-function is a τ-function ([icard-2012]'s ≼, §2.2). `addMult`/`antiAddMult`
are the most specific elements of their halves; `all` (•, any function) is
the top — every class is contained in it. Certified semantically by
`EntailmentSig.SoundFor.of_refines` in `Logic/Natural/Soundness.lean`.
-/
def Refines : EntailmentSig → EntailmentSig → Prop
  | _, .all => True
  | .addMult, .addMult | .addMult, .additive
  | .addMult, .mult | .addMult, .mono => True
  | .antiAddMult, .antiAddMult | .antiAddMult, .antiAdd
  | .antiAddMult, .antiMult | .antiAddMult, .anti => True
  | .additive, .additive | .additive, .mono => True
  | .mult, .mult | .mult, .mono => True
  | .antiAdd, .antiAdd | .antiAdd, .anti => True
  | .antiMult, .antiMult | .antiMult, .anti => True
  | .mono, .mono => True
  | .anti, .anti => True
  | _, _ => False

instance : DecidableRel (α := EntailmentSig) Refines := fun a b =>
  match a, b with
  | .all, .all | .mono, .all | .anti, .all | .additive, .all
  | .antiAdd, .all | .mult, .all | .antiMult, .all
  | .addMult, .all | .antiAddMult, .all => isTrue trivial
  | .addMult, .addMult | .addMult, .additive
  | .addMult, .mult | .addMult, .mono => isTrue trivial
  | .antiAddMult, .antiAddMult | .antiAddMult, .antiAdd
  | .antiAddMult, .antiMult | .antiAddMult, .anti => isTrue trivial
  | .additive, .additive | .additive, .mono => isTrue trivial
  | .mult, .mult | .mult, .mono => isTrue trivial
  | .antiAdd, .antiAdd | .antiAdd, .anti => isTrue trivial
  | .antiMult, .antiMult | .antiMult, .anti => isTrue trivial
  | .mono, .mono => isTrue trivial
  | .anti, .anti => isTrue trivial
  | .all, .mono | .all, .anti | .all, .additive
  | .all, .antiAdd | .all, .mult | .all, .antiMult
  | .all, .addMult | .all, .antiAddMult => isFalse not_false
  | .mono, .anti | .mono, .additive
  | .mono, .antiAdd | .mono, .mult | .mono, .antiMult
  | .mono, .addMult | .mono, .antiAddMult => isFalse not_false
  | .anti, .mono | .anti, .additive
  | .anti, .antiAdd | .anti, .mult | .anti, .antiMult
  | .anti, .addMult | .anti, .antiAddMult => isFalse not_false
  | .additive, .anti | .additive, .antiAdd
  | .additive, .mult | .additive, .antiMult
  | .additive, .addMult | .additive, .antiAddMult => isFalse not_false
  | .antiAdd, .mono | .antiAdd, .additive
  | .antiAdd, .mult | .antiAdd, .antiMult
  | .antiAdd, .addMult | .antiAdd, .antiAddMult => isFalse not_false
  | .mult, .anti | .mult, .additive
  | .mult, .antiAdd | .mult, .antiMult
  | .mult, .addMult | .mult, .antiAddMult => isFalse not_false
  | .antiMult, .mono | .antiMult, .additive
  | .antiMult, .antiAdd | .antiMult, .mult
  | .antiMult, .addMult | .antiMult, .antiAddMult => isFalse not_false
  | .addMult, .anti | .addMult, .antiAdd
  | .addMult, .antiMult | .addMult, .antiAddMult => isFalse not_false
  | .antiAddMult, .mono | .antiAddMult, .additive
  | .antiAddMult, .mult | .antiAddMult, .addMult => isFalse not_false

instance : LE EntailmentSig := ⟨Refines⟩

instance decidableLE (a b : EntailmentSig) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (Refines a b))

-- Spot-checks for the refinement lattice
example : ¬ ((EntailmentSig.all : EntailmentSig) ≤ .mono) := by decide
example : (EntailmentSig.mono : EntailmentSig) ≤ .all := by decide
example : (EntailmentSig.anti : EntailmentSig) ≤ .all := by decide
example : (EntailmentSig.addMult : EntailmentSig) ≤ .additive := by decide
example : (EntailmentSig.antiAddMult : EntailmentSig) ≤ .anti := by decide
example : ¬ ((EntailmentSig.mono : EntailmentSig) ≤ .additive) := by decide
example : ¬ ((EntailmentSig.additive : EntailmentSig) ≤ .mult) := by decide

private theorem Refines_refl (a : EntailmentSig) : Refines a a := by
  cases a <;> decide

private theorem Refines_trans (a b c : EntailmentSig) :
    Refines a b → Refines b c → Refines a c := by
  cases a <;> cases b <;> cases c <;> decide

private theorem Refines_antisymm (a b : EntailmentSig) :
    Refines a b → Refines b a → a = b := by
  cases a <;> cases b <;> decide

instance : Preorder EntailmentSig where
  le := Refines
  le_refl := Refines_refl
  le_trans := Refines_trans
instance : PartialOrder EntailmentSig where
  le_antisymm := Refines_antisymm
instance : Top EntailmentSig := ⟨.all⟩
instance : OrderTop EntailmentSig where
  le_top a := show Refines a .all by cases a <;> trivial

/--
Projection of a NL relation through a function of given signature
([icard-2012], Lemma 2.4).

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
  -- all (•): any function — projects everything to # ([icard-2012] Lemma 2.4)
  | _, .all => .independent
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
example : project .forward .mono = .forward := rfl            -- [⊑]^+ = ⊑
example : project .forward .anti = .reverse := rfl            -- [⊑]^− = ⊒
example : project .negation .mono = .independent := rfl       -- [^]^+ = #
example : project .negation .anti = .independent := rfl       -- [^]^− = #
example : project .negation .additive = .cover := rfl         -- [^]^⊕ = ∼
example : project .negation .mult = .alternation := rfl       -- [^]^⊞ = |
example : project .negation .antiAddMult = .negation := rfl   -- [^]^◇⊟ = ^
example : project .alternation .mult = .alternation := rfl    -- [|]^⊞ = |
example : project .alternation .additive = .independent := rfl -- [|]^⊕ = #
example : project .cover .additive = .cover := rfl            -- [∼]^⊕ = ∼
example : project .cover .mult = .independent := rfl          -- [∼]^⊞ = #
example : project .cover .antiAdd = .alternation := rfl       -- [∼]^◇ = |
example : project .alternation .antiMult = .cover := rfl      -- [|]^⊟ = ∼
example : project .alternation .antiAddMult = .cover := rfl   -- [|]^◇⊟ = ∼
example : project .cover .antiAddMult = .alternation := rfl   -- [∼]^◇⊟ = |

/-- Every signature except • preserves equiv (• is the class of arbitrary
functions, which need not respect equivalence). -/
theorem project_equiv (φ : EntailmentSig) (h : φ ≠ .all) :
    project .equiv φ = .equiv := by
  cases φ <;> simp_all <;> rfl

/-- Projection preserves independent for all signatures. -/
theorem project_independent (φ : EntailmentSig) : project .independent φ = .independent := by
  cases φ <;> rfl

/--
Recover an entailment signature from its projection of `forward` and
`negation`. These two probes uniquely identify each signature (up to
•'s probe pair being `(#, #)`).
-/
private def fromProjectionPair : NLRelation → NLRelation → EntailmentSig
  | .independent, .independent => .all
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
Composition of entailment signatures ([icard-2012], Lemma 2.7).

**Derived from `project`**: compose(ψ, φ) is the unique signature whose
projection table matches projecting through φ then ψ. This makes
`projection_composition` hold by finite verification rather than
requiring two independently maintained tables to agree.

The signature is identified by probing with `forward` and `negation`,
which suffice to distinguish all 9 signatures (• included: its probe
pair is `(#, #)`, which makes it absorbing, [icard-2012] p. 716).
-/
def compose (ψ φ : EntailmentSig) : EntailmentSig :=
  fromProjectionPair
    (project (project .forward φ) ψ)
    (project (project .negation φ) ψ)

-- Spot-checks (Lemma 2.7 table, p.716)
example : compose .anti .anti = .mono := rfl                   -- − ∘ − = +
example : compose .antiAddMult .antiAddMult = .addMult := rfl  -- ◇⊟ ∘ ◇⊟ = ⊕⊞
example : compose .additive .additive = .additive := rfl       -- ⊕ ∘ ⊕ = ⊕
example : compose .antiAdd .additive = .antiAdd := rfl         -- ◇ ∘ ⊕ = ◇
example : compose .addMult .anti = .anti := rfl                -- ⊕⊞ ∘ − = −
example : compose .mult .antiAdd = .antiAdd := rfl             -- ⊞ ∘ ◇ = ◇
example : compose .additive .antiMult = .antiMult := rfl       -- ⊕ ∘ ⊟ = ⊟
example : compose .antiMult .antiAdd = .additive := rfl        -- ⊟ ∘ ◇ = ⊕
example : compose .mult .mult = .mult := rfl                   -- ⊞ ∘ ⊞ = ⊞
example : compose .additive .antiAdd = .anti := rfl            -- ⊕ ∘ ◇ = −
example : compose .all .mono = .all := rfl                     -- • ∘ + = • (absorbing)
example : compose .anti .all = .all := rfl                     -- − ∘ • = • (absorbing)

/-- `addMult` (⊕⊞, the morphism class) is the identity for composition
([icard-2012] Lemma 2.7). -/
theorem compose_identity_left (s : EntailmentSig) : compose .addMult s = s := by
  cases s <;> rfl

theorem compose_identity_right (s : EntailmentSig) : compose s .addMult = s := by
  cases s <;> rfl

/-- • is absorbing: composing with the no-property class yields the
no-property class ([icard-2012] p. 716: φ ∘ • = • = • ∘ φ). -/
theorem compose_all_left (s : EntailmentSig) : compose .all s = .all := by
  cases s <;> rfl

theorem compose_all_right (s : EntailmentSig) : compose s .all = .all := by
  cases s <;> rfl

/-- Composition is associative. -/
theorem compose_assoc (a b c : EntailmentSig) :
    compose (compose a b) c = compose a (compose b c) := by
  cases a <;> cases b <;> cases c <;> rfl

-- Monoid instance (compose with identity `addMult`)
instance : Mul EntailmentSig where mul := compose
instance : One EntailmentSig where one := .addMult
instance : Monoid EntailmentSig where
  mul_assoc a b c := compose_assoc a b c
  one_mul := compose_identity_left
  mul_one := compose_identity_right

end EntailmentSig


/-! ### Context polarity -/

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
  deriving DecidableEq, Repr

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

example : compose .upward .downward = .downward := rfl
example : compose .downward .downward = .upward := rfl
example : compose .downward .upward = .downward := rfl

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
example : toContextPolarity .all = .nonMonotonic := rfl
example : toContextPolarity .mono = .upward := rfl
example : toContextPolarity .additive = .upward := rfl
example : toContextPolarity .mult = .upward := rfl
example : toContextPolarity .addMult = .upward := rfl
example : toContextPolarity .anti = .downward := rfl
example : toContextPolarity .antiAdd = .downward := rfl
example : toContextPolarity .antiMult = .downward := rfl
example : toContextPolarity .antiAddMult = .downward := rfl

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
  cases φ <;> cases ψ <;> rfl

/--
Compute the projectivity signature of a context from the signatures along
the path from the target position to the root ([icard-2012], Definition 2.9).

Given a parse tree and a target position (e.g., "dangerous" in
"Every job that involves a giant squid is dangerous"), the path collects
the `top` signature of each node from the target up to the root.
The composed signature is `List.prod`, using the `Monoid` instance.

Example from Icard §3.2:
  path = [⊞, ⊕, ◇] (top(is) ∘ top(involves) ∘ top(every_restrictor))
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
example : contextProjectivity [.antiAdd] = .antiAdd := rfl

-- "runs" in "Every animal runs": path = [⊞] (every_scope = multiplicative)
example : contextProjectivity [.mult] = .mult := rfl

-- "cat" in "No big cat runs": path = [◇, ⊕⊞] (no_restrictor = ◇, big = ⊕⊞)
-- ◇ ∘ ⊕⊞ = ◇ (anti-additive composed with morphism stays anti-additive)
example : contextProjectivity [.antiAdd, .addMult] = .antiAdd := rfl

-- "runs" in "It's not the case that every animal runs":
-- path = [◇⊟, ⊞] (negation = ◇⊟, every_scope = ⊞)
-- ◇⊟ ∘ ⊞ = ⊟ (anti-multiplicative)
example : contextProjectivity [.antiAddMult, .mult] = .antiMult := rfl

-- Double negation: ◇⊟ ∘ ◇⊟ = ⊕⊞ (morphism = preserves everything)
example : contextProjectivity [.antiAddMult, .antiAddMult] = .addMult := rfl

-- And its polarity: morphism → upward
example : toContextPolarity (contextProjectivity [.antiAddMult, .antiAddMult]) = .upward := rfl

end EntailmentSig


/-! ### Projection composition -/

/--
Projection composition ([icard-2012], Corollary 2.12).

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
  cases R <;> cases φ <;> cases ψ <;> rfl


/-! ### The negation signature and worked projections -/

/-- Negation has the anti-morphism signature ◇⊟ (strongest DE signature). -/
def negationSig : EntailmentSig := .antiAddMult

example : EntailmentSig.toContextPolarity negationSig = .downward := rfl

-- Monoid notation: negationSig * negationSig = double negation = morphism
example : negationSig * negationSig = .addMult := rfl

-- negationSig ^ 2 = ⊕⊞ (via Monoid.npow)
example : negationSig ^ 2 = .addMult := rfl

-- Negation is its own inverse (up to •/⊕⊞ equivalence):
-- ◇⊟ * ◇⊟ = ⊕⊞ (the monoid identity on non-• signatures)
example : negationSig * negationSig * negationSig = negationSig := rfl

-- Composing negation with "every" scope: ◇⊟ * ⊞ = ⊟ (anti-multiplicative)
example : negationSig * .mult = .antiMult := rfl

-- Chain composition: not(not(every ... )) scope = ⊟ * ◇⊟ * ◇⊟ = ⊟ * ⊕⊞ = ⊟
example : .antiMult * negationSig * negationSig = .antiMult := rfl

-- Forward entailment (dog ⊑ animal) projected through various signatures:
example : EntailmentSig.project .forward .mono = .forward := rfl           -- + : dog ⊑ animal ⟹ f(dog) ⊑ f(animal)
example : EntailmentSig.project .forward .anti = .reverse := rfl           -- − : dog ⊑ animal ⟹ f(dog) ⊒ f(animal)
example : EntailmentSig.project .forward .additive = .forward := rfl       -- ⊕ : same as mono for ⊑
example : EntailmentSig.project .forward .antiAddMult = .reverse := rfl    -- ◇⊟ : same as anti for ⊑

-- Alternation (cat | dog) projected through various signatures:
example : EntailmentSig.project .alternation .mono = .independent := rfl     -- + : mono alone can't track disjointness
example : EntailmentSig.project .alternation .mult = .alternation := rfl     -- ⊞ : mult preserves ∧, so preserves |
example : EntailmentSig.project .alternation .antiMult = .cover := rfl       -- ⊟ : anti-mult flips | to ∼

-- Cover (animal ∼ nondog) projected through various signatures:
example : EntailmentSig.project .cover .additive = .cover := rfl             -- ⊕ : additive preserves ∨, so preserves ∼
example : EntailmentSig.project .cover .mult = .independent := rfl           -- ⊞ : mult can't track ∨-structure
example : EntailmentSig.project .cover .antiAdd = .alternation := rfl        -- ◇ : anti-additive flips ∼ to |
example : EntailmentSig.project .cover .antiAddMult = .alternation := rfl    -- ◇⊟ : anti-morph swaps | ↔ ∼

end NaturalLogic
