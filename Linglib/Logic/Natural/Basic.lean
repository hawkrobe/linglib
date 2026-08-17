import Mathlib.Data.Finset.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Tactic.DeriveFintype
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
signatures a monoid (identity `addMult`, `all` absorbing). Relations
are read non-strictly: each is the conjunction of its `constraints`
atoms, so distinct relations overlap and `≤` compares strength;
[maccartney-manning-2009]'s seven mutually exclusive relations are the
strict refinements. Both
implication orders arise as reverse inclusion of constraint sets via
`PartialOrder.lift`, with `#` (resp. `•`) at top and no bottom (`≡`
does not entail the exclusion relations). Semantic
certification lives in `Logic/Natural/Soundness.lean`:
`Relation.Holds.join` for the join table, the `soundFor_*` row
theorems for projection.

## Main declarations

* `Relation`, `Relation.join`, `Relation.constraints` — the
  relation algebra, ordered by reverse constraint inclusion.
* `Signature`, `Signature.project`, `Signature.compose` —
  signatures, projection, and the composition monoid.
* `Signature.contextProjectivity` — a position's signature as the
  monoid product along its path.
* `ContextPolarity`, `Signature.toContextPolarity` — the coarse
  UE/DE quotient, a monoid homomorphism target
  (`toContextPolarity_compose`).
-/

namespace NaturalLogic

/-! ### The seven relations -/

/-- The seven natural-logic relations between denotations. -/
inductive Relation where
  /-- Equivalence `≡` holds when the denotations coincide (*couch* / *sofa*). -/
  | equiv
  /-- Forward entailment `⊑` holds when `A ⊆ B` (*dog* / *animal*). -/
  | forward
  /-- Reverse entailment `⊒` holds when `A ⊇ B` (*animal* / *dog*). -/
  | reverse
  /-- Negation `^` holds when the denotations are disjoint and exhaustive
      (*happy* / *unhappy*). -/
  | negation
  /-- Alternation `|` holds when the denotations are disjoint (*cat* / *dog*). -/
  | alternation
  /-- Cover `⌣` holds when the denotations are exhaustive (*animal* / *nondog*). -/
  | cover
  /-- Independence `#` imposes no constraint (*hungry* / *tall*). -/
  | independent
  deriving DecidableEq, Fintype, Repr

namespace Relation

/-- The atomic lattice constraints a relation can impose
([icard-2012] Definition 1.2). -/
inductive Atom where
  /-- `x ≤ y`. -/
  | le
  /-- `y ≤ x`. -/
  | ge
  /-- `x ⊓ y = ⊥`. -/
  | disjoint
  /-- `x ⊔ y = ⊤`. -/
  | codisjoint
  deriving DecidableEq, Fintype, Repr

/-- The constraint set of a relation: each relation is the conjunction
of its atoms (`≡` = `{le, ge}`, `^` = `{disjoint, codisjoint}`, `#` =
`∅`), `≤` is reverse inclusion of constraint sets, and `Holds` (in
`Logic/Natural/Soundness.lean`) is their conjunction. -/
def constraints : Relation → Finset Atom
  | .equiv => {.le, .ge}
  | .forward => {.le}
  | .reverse => {.ge}
  | .negation => {.disjoint, .codisjoint}
  | .alternation => {.disjoint}
  | .cover => {.codisjoint}
  | .independent => ∅

theorem constraints_injective : Function.Injective constraints := by decide

/-- The implication order ([icard-2012]'s ≪): `R ≤ R'` iff `xRy` entails
`xR'y` — reverse inclusion of constraint sets, certified semantically by
`Relation.Holds.of_le`. `#` is the top; there is no bottom: the two
diamonds (`≡` over `⊑`/`⊒`, `^` over `|`/`⌣`) meet only at `#`, since
`x = y` makes `x`,`y` neither disjoint nor exhaustive. -/
instance : PartialOrder Relation :=
  .lift (fun R => OrderDual.toDual (constraints R))
    (OrderDual.toDual.injective.comp constraints_injective)

theorem le_iff {R R' : Relation} :
    R ≤ R' ↔ constraints R' ⊆ constraints R := Iff.rfl

instance : DecidableLE Relation := fun _ _ =>
  decidable_of_iff _ le_iff.symm

instance : OrderTop Relation where
  top := .independent
  le_top _ := le_iff.mpr (Finset.empty_subset _)

/--
Join operation ⋈ ([icard-2012], Lemma 1.5): given `xRy` and `yR'z`, the
strongest relation guaranteed between `x` and `z` — relation-algebra
join, not lattice join. The table is derived from the non-strict
`Holds` reading and certified cell-by-cell by `Relation.Holds.join`
in `Logic/Natural/Soundness.lean`.
-/
def join : Relation → Relation → Relation
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

/-- ≡ is the identity for join. -/
theorem join_identity_left (r : Relation) : join .equiv r = r := by
  cases r <;> rfl

theorem join_identity_right (r : Relation) : join r .equiv = r := by
  cases r <;> rfl

-- Note: join is NOT commutative. E.g., ^⋈⌣ = ⊑ but ⌣⋈^ = ⊒.
-- This is expected: xRy and yR'z is directional.

end Relation

/-! ### Entailment signatures -/

/-- The function classes a relation can be projected through, from
arbitrary (`•`) to anti-morphism (`◇⊟`). -/
inductive Signature where
  /-- An arbitrary function (`•`), projecting every relation to `#`. -/
  | all
  /-- A monotone function (`+`, upward entailing). -/
  | mono
  /-- An antitone function (`−`, downward entailing). -/
  | anti
  /-- An additive function (`⊕`), preserving joins. -/
  | additive
  /-- An anti-additive function (`◇`), turning joins into meets. -/
  | antiAdd
  /-- A multiplicative function (`⊞`), preserving meets. -/
  | mult
  /-- An anti-multiplicative function (`⊟`), turning meets into joins. -/
  | antiMult
  /-- A morphism (`⊕⊞`), additive and multiplicative. -/
  | addMult
  /-- An anti-morphism (`◇⊟`), anti-additive and anti-multiplicative. -/
  | antiAddMult
  deriving DecidableEq, Fintype, Repr

namespace Signature

/-- The function properties a signature can assert, closed under
implication (an additive function is monotone, so `⊕`'s set contains
`monotone`). -/
inductive Property where
  /-- Preserves `≤`. -/
  | monotone
  /-- Reverses `≤`. -/
  | antitone
  /-- Preserves `⊔`. -/
  | additive
  /-- Preserves `⊓`. -/
  | multiplicative
  /-- Sends `⊔` to `⊓`. -/
  | antiAdditive
  /-- Sends `⊓` to `⊔`. -/
  | antiMultiplicative
  deriving DecidableEq, Fintype, Repr

/-- The property set of a signature: `≤` is reverse inclusion, so
`addMult`/`antiAddMult` are the most specific elements of their halves
and `all` (`•`, no property) is the top. -/
def properties : Signature → Finset Property
  | .all => ∅
  | .mono => {.monotone}
  | .anti => {.antitone}
  | .additive => {.monotone, .additive}
  | .mult => {.monotone, .multiplicative}
  | .antiAdd => {.antitone, .antiAdditive}
  | .antiMult => {.antitone, .antiMultiplicative}
  | .addMult => {.monotone, .additive, .multiplicative}
  | .antiAddMult => {.antitone, .antiAdditive, .antiMultiplicative}

theorem properties_injective : Function.Injective properties := by decide

/-- The refinement order ([icard-2012]'s ≼, §2.2): `σ ≤ τ` iff every
σ-function is a τ-function — reverse inclusion of property sets,
certified semantically by `Signature.SoundFor.of_le` in
`Logic/Natural/Soundness.lean`. -/
instance : PartialOrder Signature :=
  .lift (fun σ => OrderDual.toDual (properties σ))
    (OrderDual.toDual.injective.comp properties_injective)

theorem le_iff {σ τ : Signature} :
    σ ≤ τ ↔ properties τ ⊆ properties σ := Iff.rfl

instance : DecidableLE Signature := fun _ _ =>
  decidable_of_iff _ le_iff.symm

instance : OrderTop Signature where
  top := .all
  le_top _ := le_iff.mpr (Finset.empty_subset _)

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
def project : Relation → Signature → Relation
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

/-- Every signature except • preserves equiv (• is the class of arbitrary
functions, which need not respect equivalence). -/
theorem project_equiv (φ : Signature) (h : φ ≠ .all) :
    project .equiv φ = .equiv := by
  cases φ <;> simp_all <;> rfl

/-- Projection preserves independent for all signatures. -/
theorem project_independent (φ : Signature) : project .independent φ = .independent := by
  cases φ <;> rfl

/--
Recover an entailment signature from its projection of `forward` and
`negation`. These two probes uniquely identify each signature (up to
•'s probe pair being `(#, #)`).
-/
private def fromProjectionPair : Relation → Relation → Signature
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
def compose (ψ φ : Signature) : Signature :=
  fromProjectionPair
    (project (project .forward φ) ψ)
    (project (project .negation φ) ψ)

/-- `addMult` (⊕⊞, the morphism class) is the identity for composition
([icard-2012] Lemma 2.7). -/
theorem compose_identity_left (s : Signature) : compose .addMult s = s := by
  cases s <;> rfl

theorem compose_identity_right (s : Signature) : compose s .addMult = s := by
  cases s <;> rfl

/-- • is absorbing: composing with the no-property class yields the
no-property class ([icard-2012] p. 716: φ ∘ • = • = • ∘ φ). -/
theorem compose_all_left (s : Signature) : compose .all s = .all := by
  cases s <;> rfl

theorem compose_all_right (s : Signature) : compose s .all = .all := by
  cases s <;> rfl

/-- Composition is associative. -/
theorem compose_assoc (a b c : Signature) :
    compose (compose a b) c = compose a (compose b c) := by
  cases a <;> cases b <;> cases c <;> rfl

-- Monoid instance (compose with identity `addMult`)
instance : Mul Signature where mul := compose
instance : One Signature where one := .addMult
instance : Monoid Signature where
  mul_assoc a b c := compose_assoc a b c
  one_mul := compose_identity_left
  mul_one := compose_identity_right

end Signature

/-! ### Context polarity -/

/-- Whether a context preserves or reverses entailment — the coarse
UE/DE quotient of `Signature` (`toContextPolarity`). -/
inductive ContextPolarity where
  /-- The context preserves entailment (upward entailing). -/
  | upward
  /-- The context reverses entailment (downward entailing). -/
  | downward
  /-- The context is neither monotone nor antitone (*exactly n*). -/
  | nonMonotonic
  deriving DecidableEq, Repr

namespace ContextPolarity

/--
Compose context polarities.

This is the coarse composition table derived from the `Signature` monoid:
UE ∘ UE = UE, DE ∘ DE = UE (double negation), UE ∘ DE = DE, DE ∘ UE = DE.
Any composition involving `nonMonotonic` yields `nonMonotonic`.
-/
def compose : ContextPolarity → ContextPolarity → ContextPolarity
  | .upward, x => x
  | x, .upward => x
  | .downward, .downward => .upward
  | .nonMonotonic, _ => .nonMonotonic
  | _, .nonMonotonic => .nonMonotonic

end ContextPolarity

namespace Signature

/--
Map an entailment signature to the coarser `ContextPolarity` type,
derived from `project`.

A signature is UE iff it preserves forward entailment (`[⊑]^φ = ⊑`),
DE iff it reverses it (`[⊑]^φ = ⊒`).
-/
def toContextPolarity (φ : Signature) : ContextPolarity :=
  if project .forward φ == .forward then .upward
  else if project .forward φ == .reverse then .downward
  else .nonMonotonic

/--
`toContextPolarity` is a monoid homomorphism: composing signatures then
coarsening gives the same result as coarsening then composing polarities.

This theorem connects the fine-grained `Signature` monoid to the
coarse `ContextPolarity` composition, ensuring the two systems can never
disagree.
-/
theorem toContextPolarity_compose (φ ψ : Signature) :
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
def contextProjectivity (path : List Signature) : Signature :=
  path.prod

/--
Project a NL relation through a context given by its signature path.
Combines `contextProjectivity` with `project`.
-/
def projectThrough (R : Relation) (path : List Signature) : Relation :=
  project R (contextProjectivity path)

-- Icard §2.4: path lists signatures from root (outermost) to target (innermost).
-- List.prod applies them right-to-left: the last element is applied first.

end Signature

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
theorem projection_composition (R : Relation) (φ ψ : Signature) :
    Signature.project (Signature.project R φ) ψ =
    Signature.project R (Signature.compose ψ φ) := by
  cases R <;> cases φ <;> cases ψ <;> rfl

/-! ### The negation signature -/

/-- Negation has the anti-morphism signature ◇⊟ (strongest DE signature). -/
def negationSignature : Signature := .antiAddMult

end NaturalLogic
