import Mathlib.Data.Finset.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Nat.Basic

/-!
# The natural-logic relation algebra

This file defines the seven natural-logic relations between
denotations (≡, ⊑, ⊒, ^, |, ⌣, #) and the nine entailment signatures
of [icard-2012], with the operations of the projectivity calculus:
chaining two relations, projecting a relation through a function of
known signature, and composing signatures.

A relation is read non-strictly, as the conjunction of its constraint
atoms: distinct relations overlap, and `R ≤ R'` iff `R` entails `R'`,
by reverse inclusion of constraint sets. The mutually exclusive seven
of [maccartney-manning-2009] are the strict refinements. Signatures
are ordered likewise by reverse inclusion of property sets; `#` and
`•` are the tops, and there is no bottom.

## Main declarations

* `Relation`: the seven relations, a monoid under `Relation.join` with
  identity `equiv` and absorbing element `independent`.
* `Relation.constraints`: a relation as a conjunction of atomic
  lattice constraints; the source of the implication order.
* `Signature`: the nine signatures, a monoid under `Signature.compose`
  with identity `addMult` and absorbing element `all`.
* `Signature.project`: projection of a relation through a signature —
  an action of the signature monoid on the relations
  (`MulAction Signature Relation`).
* `Signature.contextProjectivity`: the signature of a position, as the
  monoid product along its path.
* `ContextPolarity`: the coarse upward/downward quotient, a monoid
  homomorphism target (`toContextPolarity_compose`).

## Implementation notes

`compose` is derived from `project` by probing at the relations
`forward` and `negation`, so `projection_composition` holds by
construction. Associativity of `join` is printed in neither source and
is verified by `decide`. The tables are certified semantically in
`Logic/Natural/Soundness.lean` (`Relation.Holds.join`, the
`soundFor_*` rows) and shown tight in
`Logic/Natural/Completeness.lean`, which also derives the seven
relations as the nondegenerately realizable constraint conjunctions.

## References

* [icard-2012] — the projectivity calculus: the relations, signatures,
  and tables this file implements.
* [maccartney-manning-2009] — the extended natural-logic model; its §3
  join is exact relation composition, union-valued outside the seven.
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
`∅`), `≤` is reverse inclusion of constraint sets, and `Holds` is their
conjunction (`Relation.holds_iff` in `Logic/Natural/Soundness.lean`).
Exactly the seven images are nondegenerately realizable among the
sixteen subsets (`Relation.mem_range_constraints_iff` in
`Logic/Natural/Completeness.lean`). -/
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
`Holds` reading, certified sound cell-by-cell by `Relation.Holds.join`
in `Logic/Natural/Soundness.lean`, and tight by `Relation.isLeast_join`
in `Logic/Natural/Completeness.lean`: each cell is the least relation
sound for the chaining ([icard-2012]'s Definition 1.4;
[maccartney-manning-2009]'s §3 join is instead exact relation
composition, valued in *union relations* outside the seven on 17 of
the 49 cells — this table is its best single-relation weakening).
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

instance : Mul Relation := ⟨join⟩
instance : One Relation := ⟨.equiv⟩

/-- The relations form a monoid under ⋈ with identity `≡`. The identity
and absorption laws are printed in [icard-2012] (p. 710); associativity
appears in neither [icard-2012] nor [maccartney-manning-2009] and is
verified here by kernel `decide`. Not commutative: `^ ⋈ ⌣ = ⊑` but
`⌣ ⋈ ^ = ⊒` (chaining is directional). -/
instance : Monoid Relation where
  mul_assoc := by decide
  one_mul r := by cases r <;> rfl
  mul_one r := by cases r <;> rfl

/-- `#` absorbs on the left ([icard-2012] p. 710). -/
@[simp] theorem top_mul (r : Relation) : ⊤ * r = ⊤ := by cases r <;> rfl

/-- `#` absorbs on the right ([icard-2012] p. 710). -/
@[simp] theorem mul_top (r : Relation) : r * ⊤ = ⊤ := by cases r <;> rfl

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

/-- The projection of a relation through a function of the given
signature ([icard-2012] Definition 2.3, computed by his Lemma 2.4):
the strongest relation guaranteed between `f x` and `f y` when `x R y`
and `f` has signature `σ`. The rows are certified sound against the
function classes in `Logic/Natural/Soundness.lean` (`soundFor_*`). -/
def project : Relation → Signature → Relation
  | _, .all => .independent
  | r, .addMult => r
  | .equiv, .antiAddMult => .equiv
  | .forward, .antiAddMult => .reverse
  | .reverse, .antiAddMult => .forward
  | .negation, .antiAddMult => .negation
  | .alternation, .antiAddMult => .cover
  | .cover, .antiAddMult => .alternation
  | .independent, .antiAddMult => .independent
  | .equiv, .mono => .equiv
  | .forward, .mono => .forward
  | .reverse, .mono => .reverse
  | .negation, .mono => .independent
  | .alternation, .mono => .independent
  | .cover, .mono => .independent
  | .independent, .mono => .independent
  | .equiv, .anti => .equiv
  | .forward, .anti => .reverse
  | .reverse, .anti => .forward
  | .negation, .anti => .independent
  | .alternation, .anti => .independent
  | .cover, .anti => .independent
  | .independent, .anti => .independent
  | .equiv, .additive => .equiv
  | .forward, .additive => .forward
  | .reverse, .additive => .reverse
  | .negation, .additive => .cover
  | .alternation, .additive => .independent
  | .cover, .additive => .cover
  | .independent, .additive => .independent
  | .equiv, .antiAdd => .equiv
  | .forward, .antiAdd => .reverse
  | .reverse, .antiAdd => .forward
  | .negation, .antiAdd => .alternation
  | .alternation, .antiAdd => .independent
  | .cover, .antiAdd => .alternation
  | .independent, .antiAdd => .independent
  | .equiv, .mult => .equiv
  | .forward, .mult => .forward
  | .reverse, .mult => .reverse
  | .negation, .mult => .alternation
  | .alternation, .mult => .alternation
  | .cover, .mult => .independent
  | .independent, .mult => .independent
  | .equiv, .antiMult => .equiv
  | .forward, .antiMult => .reverse
  | .reverse, .antiMult => .forward
  | .negation, .antiMult => .cover
  | .alternation, .antiMult => .cover
  | .cover, .antiMult => .independent
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

/-- Projecting through `φ` and then `ψ` projects through the composite
signature ([icard-2012] Definition 2.6 and Lemma 2.7) — the `mul_smul`
law of `MulAction Signature Relation`. Since `compose` is derived from
`project` by probing at `forward` and `negation`, the content is that
the two probes determine the whole table. -/
theorem projection_composition (R : Relation) (φ ψ : Signature) :
    Signature.project (Signature.project R φ) ψ =
    Signature.project R (Signature.compose ψ φ) := by
  cases R <;> cases φ <;> cases ψ <;> rfl

instance : SMul Signature Relation := ⟨λ σ R => Signature.project R σ⟩

@[simp] theorem Signature.smul_def (σ : Signature) (R : Relation) :
    σ • R = Signature.project R σ := rfl

/-- Projection is an action of the signature monoid on the relations:
`projection_composition` is the `mul_smul` law. -/
instance : MulAction Signature Relation where
  one_smul := by decide
  mul_smul ψ φ R := (projection_composition R φ ψ).symm

/-! ### The negation signature -/

/-- Negation has the anti-morphism signature ◇⊟ (strongest DE signature). -/
def negationSignature : Signature := .antiAddMult

end NaturalLogic
