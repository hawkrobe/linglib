import Linglib.Theories.Semantics.Alternatives.Structural
import Linglib.Theories.Semantics.Alternatives.Symmetric

/-!
# Trinh & Haida 2015: Constraining the Derivation of Alternatives
@cite{trinh-haida-2015}

Trinh, T. & Haida, A. (2015). Constraining the derivation of alternatives.
Natural Language Semantics, 23(4), 249–270.

## Core Contribution

The **Atomicity constraint** (def 32): expressions in the substitution
source are syntactically atomic — their internal structure is inaccessible
to structural operations. This refines @cite{fox-katzir-2011} /
@cite{katzir-2007} to correctly distinguish:

- **Symmetry-breaking cases** (§3.2.2): "Bill ran and didn't smoke.
  John ran." → John smoked. Atomicity blocks "ran ∧ smoked" from F(S),
  so A = {run, run ∧ ¬smoke} satisfies Conditions on A (27), and
  EXH derives ¬(run ∧ ¬smoke).

- **Symmetry-preserving cases** (§3.2.3): "Bill ate exactly three.
  John ate three." → ✗John ate exactly three. Atomicity is vacuous;
  Conditions on A (27c) force "four" into A, creating symmetry.

## Key Definitions

- `inBooleanClosure`: p is determined by a set of propositions (27c)
- `isValidDomain`: Conditions on A (27) for EXH domains
- `ATree` / `ATStructOp`: parse trees with AT-marking; structural
  operations that cannot enter AT-marked nodes
- `structuralAlternativesAT`: F_AT(S) ⊆ F(S)
-/

namespace Alternatives.AtomicConstraint

open StructuralAlternatives (PFTree SynCat)
open Alternatives.Symmetric (isSymmetric)
open Exhaustification.InnocentExclusion (exhB ieIndices nonWeakerIndices)


-- ════════════════════════════════════════════════════════════════════
-- §1  Boolean Closure
-- ════════════════════════════════════════════════════════════════════

/-- A proposition `p` is in the **Boolean closure** of `alts`:
    `p` is determined by the truth values of elements of `alts`.
    Whenever two worlds agree on all elements of `alts`, they agree
    on `p`. Used in Condition (27c). -/
def inBooleanClosure {W : Type} (domain : List W)
    (alts : List (W → Bool)) (p : W → Bool) : Bool :=
  domain.all fun w₁ => domain.all fun w₂ =>
    !(alts.all fun a => a w₁ == a w₂) || (p w₁ == p w₂)


-- ════════════════════════════════════════════════════════════════════
-- §2  Conditions on A (def 27)
-- ════════════════════════════════════════════════════════════════════

/-- Extensional equality on a finite domain. -/
def propEqOn {W : Type} (domain : List W) (p q : W → Bool) : Bool :=
  domain.all fun w => p w == q w

/-- Extensional membership via `propEqOn`. -/
def propMemOn {W : Type} (domain : List W) (p : W → Bool)
    (alts : List (W → Bool)) : Bool :=
  alts.any fun a => propEqOn domain p a

/-- **Conditions on A** (27): `A` is a valid domain of EXH for
    prejacent `S` given formal alternatives `formalAlts` = F(S).

    (27a) A ⊆ F(S)
    (27b) S ∈ A
    (27c) No S' in F(S) \ A is in the Boolean closure of A -/
def isValidDomain {W : Type} (domain : List W)
    (formalAlts : List (W → Bool)) (prejacent : W → Bool)
    (domainOfEXH : List (W → Bool)) : Bool :=
  domainOfEXH.all (fun a => propMemOn domain a formalAlts) &&
  propMemOn domain prejacent domainOfEXH &&
  formalAlts.all fun s' =>
    propMemOn domain s' domainOfEXH ||
    !inBooleanClosure domain domainOfEXH s'


-- ════════════════════════════════════════════════════════════════════
-- §3  ATree and ATStructOp (Atomicity Constraint, def 32)
-- ════════════════════════════════════════════════════════════════════

/-- Parse tree with optional AT-marking. AT-marked nodes (`atNode`)
    preserve content for semantic interpretation but are inaccessible
    to structural operations — implementing the Atomicity constraint
    (def 32): "Expressions in the substitution source are syntactically
    atomic." -/
inductive ATree (W : Type) where
  | leaf (cat : SynCat) (word : W)
  | node (cat : SynCat) (children : List (ATree W))
  | atNode (cat : SynCat) (content : PFTree W)

namespace ATree

variable {W : Type}

def cat : ATree W → SynCat
  | .leaf c _ | .node c _ | .atNode c _ => c

/-- Expand to `PFTree` by unsealing AT-marked nodes. -/
def expand : ATree W → PFTree W
  | .leaf c w => .leaf c w
  | .node c cs => .node c (expandList cs)
  | .atNode _ content => content
where
  expandList : List (ATree W) → List (PFTree W)
  | [] => []
  | t :: ts => t.expand :: expandList ts

/-- Lift a `PFTree` to `ATree` (no AT-marking). -/
def lift : PFTree W → ATree W
  | .leaf c w => .leaf c w
  | .node c cs => .node c (liftList cs)
where
  liftList : List (PFTree W) → List (ATree W)
  | [] => []
  | t :: ts => lift t :: liftList ts

end ATree

/-- Structural operation respecting Atomicity. Like `StructOp` but
    `inChild` can only descend into `.node`, NOT `.atNode`. AT-marked
    material is opaque to further syntactic manipulation. -/
inductive ATStructOp {W : Type} (source : List (ATree W)) :
    ATree W → ATree W → Prop where
  | subst {φ ψ : ATree W}
    (h_cat : ψ.cat = φ.cat) (h_src : ψ ∈ source) :
    ATStructOp source φ ψ
  | delete {cat : SynCat} {cs : List (ATree W)}
    (i : Fin cs.length) :
    ATStructOp source (.node cat cs) (.node cat (cs.eraseIdx i))
  | contract {cat : SynCat} {cs : List (ATree W)}
    {child : ATree W}
    (h_mem : child ∈ cs) (h_cat : child.cat = cat) :
    ATStructOp source (.node cat cs) child
  | inChild {cat : SynCat} {cs : List (ATree W)}
    (i : Fin cs.length) {ψ_child : ATree W}
    (h_step : ATStructOp source (cs.get i) ψ_child) :
    -- Only matches .node — NOT .atNode. This is the constraint.
    ATStructOp source (.node cat cs) (.node cat (cs.set i ψ_child))

/-- AT-constrained reachability (reflexive-transitive closure). -/
def atReachable {W : Type} (source : List (ATree W))
    (ψ φ : ATree W) : Prop :=
  Relation.ReflTransGen (ATStructOp source) φ ψ

/-- The substitution source with Atomicity:
    lexical items + subtrees of S are lifted (transparent);
    contextual constituents are wrapped in `atNode` (opaque). -/
def atomicSubstitutionSource {W : Type}
    (lexicon : List (PFTree W))
    (φ : PFTree W)
    (context : List (PFTree W)) : List (ATree W) :=
  (lexicon ++ φ.subtrees).map ATree.lift ++
  context.map (fun t => .atNode t.cat t)

/-- **F_AT(S)**: formal alternatives derivable under Atomicity.
    S' ∈ F_AT(S) iff ∃ ATree `t` reachable from `lift(S)` via
    AT-constrained operations with `t.expand = S'`. -/
def structuralAlternativesAT {W : Type}
    (lex : List (PFTree W))
    (φ : PFTree W)
    (context : List (PFTree W)) : Set (PFTree W) :=
  {ψ | ∃ t, atReachable (atomicSubstitutionSource lex φ context)
    t (ATree.lift φ) ∧ t.expand = ψ}


-- ════════════════════════════════════════════════════════════════════
-- §4  Symmetry Breaking: Run / Smoke (§3.2.2, ex. 20a, 34–36)
-- ════════════════════════════════════════════════════════════════════

/-!
## Symmetry Breaking

(34) Bill went for a run and didn't smoke. John (only) went for a run.
     Inference: ¬[John went for a run and didn't smoke] → John smoked.

Atomicity blocks "ran ∧ smoked" from F(S) because deriving it requires
modifying the interior of the AT-marked contextual constituent
"ran ∧ ¬smoked" (removing the NegP). This leaves A = {run, run ∧ ¬smoke}
as a valid domain satisfying (27c), and EXH(A)(run) = run ∧ smoke. -/

section RunSmoke

/-- Four activity worlds (run and smoke are independent). -/
inductive AW where | rs | rns | s | ns
  deriving DecidableEq, BEq, Repr

private def awDomain : List AW := [.rs, .rns, .s, .ns]

private def ran : AW → Bool
  | .rs | .rns => true | _ => false
private def smoked : AW → Bool
  | .rs | .s => true | _ => false
private def didntSmoke : AW → Bool
  | .rns | .ns => true | _ => false
private def ranNotSmoked : AW → Bool
  | .rns => true | _ => false

/-- F_AT(S) = {run, smoke, ¬smoke, run ∧ ¬smoke}. -/
private def fATrun : List (AW → Bool) :=
  [ran, smoked, didntSmoke, ranNotSmoked]

/-- A = {run, run ∧ ¬smoke} — the domain of EXH after Atomicity
    excludes "run ∧ smoke" from F(S). -/
private def domainA : List (AW → Bool) := [ran, ranNotSmoked]

/-- A satisfies all three Conditions on A (27). Crucially, (27c)
    holds: neither "smoke" nor "¬smoke" is in BC({run, run ∧ ¬smoke})
    because the 4-world domain distinguishes them from all Boolean
    combinations. -/
theorem run_valid_domain :
    isValidDomain awDomain fATrun ran domainA = true := by
  native_decide

/-- EXH(A)(run) = run ∧ smoke: the correct empirical inference.
    exhB negates "run ∧ ¬smoke" (the only non-weaker alternative
    in A), deriving that John smoked. -/
theorem run_exh_correct :
    ∀ w : AW, exhB awDomain domainA ran w = (ran w && smoked w) := by
  intro w; cases w <;> native_decide

/-- Without Atomicity, F(S) would also contain "run ∧ smoke" = {rs}.
    With this alternative, smoked and ranNotSmoked become symmetric
    on the run-restricted domain, and exhB over F(S) is vacuous. -/
private def ranAndSmoked : AW → Bool
  | .rs => true | _ => false

theorem without_atomicity_vacuous :
    ∀ w : AW,
      exhB awDomain [ran, smoked, didntSmoke, ranNotSmoked, ranAndSmoked]
        ran w = ran w := by
  intro w; cases w <;> native_decide

end RunSmoke


-- ════════════════════════════════════════════════════════════════════
-- §5  Symmetry Preserving: Three Cookies (§3.2.3, ex. 21a, 41–43)
-- ════════════════════════════════════════════════════════════════════

/-!
## Symmetry Preserving

(41) Bill ate exactly three cookies. John (only) ate three cookies.
     *Inference: ¬[John ate exactly three cookies]

Atomicity is vacuous here (alternatives are derived by simple lexical
substitution). The non-attested inference is blocked by Conditions on
A (27c): "four" ∈ BC({three, exactly_three}), so excluding "four"
from A is impossible, but including it creates symmetry. -/

section ThreeCookies

/-- Three cookie worlds: ate exactly 3, 4, or 5. -/
inductive CW where | w3 | w4 | w5
  deriving DecidableEq, BEq, Repr

private def cwDomain : List CW := [.w3, .w4, .w5]

/-- "three" = at least 3 (lower-bound reading). -/
private def three : CW → Bool := fun _ => true
/-- "exactly three" = exactly 3. -/
private def exactlyThree : CW → Bool
  | .w3 => true | _ => false
/-- "four" = at least 4. -/
private def four : CW → Bool
  | .w4 | .w5 => true | .w3 => false

private def fCookies : List (CW → Bool) := [three, exactlyThree, four]

/-- "four" is in BC({three, exactly_three}): worlds agreeing on both
    "three" (always true) and "exactly_three" always agree on "four",
    because four ≡ three ∧ ¬exactly_three on this domain. -/
theorem four_in_bc :
    inBooleanClosure cwDomain [three, exactlyThree] four = true := by
  native_decide

/-- A = {three, exactly_three} violates (27c): "four" is excluded
    from A but is in BC(A). -/
theorem restricted_domain_invalid :
    isValidDomain cwDomain fCookies three [three, exactlyThree]
      = false := by
  native_decide

/-- A = F(S) = {three, exactly_three, four} satisfies (27). -/
theorem full_domain_valid :
    isValidDomain cwDomain fCookies three fCookies = true := by
  native_decide

/-- "exactly_three" and "four" are symmetric alternatives of "three":
    they partition its denotation. -/
theorem cookies_symmetric :
    isSymmetric cwDomain three exactlyThree four = true := by
  native_decide

/-- With A = F(S) (the only valid domain), exhB is vacuous:
    the symmetric alternatives make exhaustification identity. -/
theorem cookies_exh_vacuous :
    ∀ w : CW, exhB cwDomain fCookies three w = three w := by
  intro w; cases w <;> native_decide

end ThreeCookies


-- ════════════════════════════════════════════════════════════════════
-- §6  Extended Constraints for the Switching Problem (§4.2, def 60)
-- ════════════════════════════════════════════════════════════════════

/-!
## Switching Problem Constraints

For structures where a weak scalar item embeds a strong one
(e.g., [some[all]]), Atomicity alone is insufficient. The paper
adds three constraints on the derivation of formal alternatives:

(60a) Only non-AT-marked expressions are replaceable.
(60b) The most deeply embedded replaceable expression must be
      replaced first (bottom-up).
(60c) No replacement may yield a sentence logically weaker than
      the prejacent.

These constraints prevent "some" and "all" from switching places
under negation while still allowing the correct indirect implicature
derivation. (60a) is already captured by `ATStructOp` (no `inChild`
into `atNode`). (60b) and (60c) are additional derivation-order and
semantic monotonicity constraints: -/

/-- (60b) Bottom-up ordering: the replacement position must be at
    least as deeply embedded as any other replaceable position.
    Modeled as a property of a derivation step at position `pos`
    in a tree of depth `maxDepth`. -/
def bottomUpOrdering (pos maxReplaceable : Nat) : Prop :=
  pos ≥ maxReplaceable

/-- (60c) Semantic monotonicity: the result of a replacement step
    must not be logically weaker than the input (on the domain). -/
def nonWeakeningStep {W : Type} (domain : List W)
    (before after : W → Bool) : Bool :=
  !(domain.any fun w => before w && !after w) ||
  domain.any fun w => after w && !before w


end Alternatives.AtomicConstraint
