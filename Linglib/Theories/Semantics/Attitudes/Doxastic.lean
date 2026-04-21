/-
# Doxastic Attitude Semantics
@cite{pearl-2000} @cite{glass-2025} @cite{hintikka-1962} @cite{roberts-ozyildiz-2025}

Modal/accessibility-based semantics for doxastic attitude verbs like
`believe`, `know`, `think`.

## Semantic Mechanism

Doxastic attitudes use Hintikka-style accessibility relations:
- R(x, w, w') means w' is compatible with what x believes/knows in w
- ⟦x believes p⟧(w) = ∀w'. R(x,w,w') → p(w')

## PrProp Decomposition

`DoxasticPredicate.toPrProp` decomposes a doxastic predicate into a
`PrProp` (partial proposition):
- `presup` = veridicality check (for veridical verbs: p(w); otherwise: true)
- `assertion` = universal modal (∀w'. R(x,w,w') → p(w'))

This connects doxastic attitudes to the presupposition infrastructure
in `Core.Presupposition`, enabling uniform treatment of factive
presuppositions, projection, and the @cite{glass-2025} typology.

## PresupClass

`PresupClass` classifies doxastic verbs by their presuppositional profile:
- `.factive` (know): presup = p → satisfies PLC
- `.nonfactive` (believe): no presupposition → PLC does not apply
- `.contrafactive` (hypothetical *contra*): presup = ¬p → violates PLC (UNATTESTED)

## Question Embedding

Doxastic attitudes can embed questions via exhaustive interpretation:
- ⟦x knows Q⟧ = ∃p ∈ Q. p(w) ∧ x knows p

-/

import Linglib.Core.Discourse.IllocutionaryForce
import Linglib.Core.Discourse.Intentionality
import Linglib.Core.Discourse.Commitment
import Linglib.Core.Semantics.Presupposition
import Linglib.Core.IntensionalLogic.RestrictedModality
import Linglib.Core.StructuralEquationModel
import Linglib.Core.Lexical.VerbClass
import Linglib.Theories.Semantics.Questions.Denotation.Hamblin

namespace Semantics.Attitudes.Doxastic

open Core (Situation)

open Core.Verbs (Veridicality)
export Core.Verbs (Veridicality)

-- Accessibility Relations

/--
Doxastic accessibility relation type (Prop-valued, mathlib convention).

`R agent evalWorld accessibleWorld` holds iff accessibleWorld is compatible
with what agent believes/knows in evalWorld. For computational evaluation
add `[DecidableRel (R agent)]` instances at use sites.
-/
abbrev AccessRel (W E : Type*) := E → W → W → Prop

/--
Universal modal: holds at w iff p holds at all accessible worlds.

⟦□p⟧(w) = ∀w' ∈ worlds. R(agent, w, w') → p(w')
-/
def boxAt {W E : Type*} (R : AccessRel W E) (agent : E) (w : W)
    (worlds : List W) (p : W → Prop) : Prop :=
  ∀ w' ∈ worlds, R agent w w' → p w'

/--
Existential modal: holds at w iff p holds at some accessible world.

⟦◇p⟧(w) = ∃w' ∈ worlds. R(agent, w, w') ∧ p(w')
-/
def diaAt {W E : Type*} (R : AccessRel W E) (agent : E) (w : W)
    (worlds : List W) (p : W → Prop) : Prop :=
  ∃ w' ∈ worlds, R agent w w' ∧ p w'

instance boxAt_decidable {W E : Type*} (R : AccessRel W E) [∀ a w w', Decidable (R a w w')]
    (agent : E) (w : W) (worlds : List W) (p : W → Prop) [DecidablePred p] :
    Decidable (boxAt R agent w worlds p) :=
  inferInstanceAs (Decidable (∀ w' ∈ worlds, _))

instance diaAt_decidable {W E : Type*} (R : AccessRel W E) [∀ a w w', Decidable (R a w w')]
    (agent : E) (w : W) (worlds : List W) (p : W → Prop) [DecidablePred p] :
    Decidable (diaAt R agent w worlds p) :=
  inferInstanceAs (Decidable (∃ w' ∈ worlds, _))

-- ============================================================================
-- Presuppositional Classification (@cite{glass-2025})
-- ============================================================================

/-!
## Presuppositional Classification of Doxastic Verbs

@cite{glass-2025} proposes a typology of belief verbs based on their
presuppositional profile — what they require of the Common Ground:

- **Factive** (know): presupposes p — CG must entail p
- **Nonfactive** (think): no presupposition — no CG requirement
- **Contrafactive** (hypothetical *contra*): would presuppose ¬p — UNATTESTED
- **Weak contrafactive** (Mandarin yǐwéi): postsupposition ◇¬p — CG compatible with ¬p

The key insight: this classification is DERIVED from the `PrProp` produced by
`DoxasticPredicate.toPrProp`, not stipulated as a separate type. The presup
field of the PrProp determines the classification.

Postsuppositions (yǐwéi's ◇¬p) are output-context constraints, formalized
separately in `Core.Postsupposition`.
-/

/--
Classification of a doxastic verb's presuppositional profile.

This emerges from the presup field of the `PrProp` produced by
`DoxasticPredicate.toPrProp`. Not a primitive — a derived label.
-/
inductive PresupClass where
  | factive         -- presup = p (know: CG must entail p)
  | contrafactive   -- presup = ¬p (hypothetical *contra*: CG must entail ¬p — UNATTESTED)
  | nonfactive      -- presup = true (believe/think: no CG requirement)
  | other           -- none of the above
  deriving DecidableEq, Repr

/-- Classify a doxastic verb by its veridicality. -/
def classifyVeridicality : Veridicality → PresupClass
  | .veridical => .factive
  | .nonVeridical => .nonfactive

/-- Veridical verbs are factive. -/
theorem veridical_is_factive :
    classifyVeridicality .veridical = .factive := rfl

/-- Non-veridical verbs are nonfactive. -/
theorem nonVeridical_is_nonfactive :
    classifyVeridicality .nonVeridical = .nonfactive := rfl

-- ============================================================================
-- Causal Models for Lexical Coherence (Roberts & Özyıldız 2025)
-- ============================================================================

/-!
## Causal Explanation of the Contrafactive Gap

Roberts & Özyıldız (2025) propose that the contrafactive gap follows from
a general constraint on lexicalization: **presupposed content must be
causally upstream of at-issue content**.

### The Predicate Lexicalization Constraint (PLC)

A verbal predicate V with at-issue content α can have presupposition π iff
in the normative world wₙ, a causal chain from π(wₙ) to α(wₙ) can be
constructed for any assignment of the arguments of V.

### Why Factives Work (know)

For "Delilah knows that Konstanz is in Germany":
- Presupposition: p (Konstanz is in Germany)
- At-issue: B(d)(p) (Delilah believes Konstanz is in Germany)

Causal chain: p → indic(p) → acq(d)(iₚ) → B(d)(p)

1. The fact p generates indicators (evidence) for p
2. Delilah can become acquainted with these indicators
3. This acquaintance leads to belief formation

### Why Strong Contrafactives Don't Work (contra)

For hypothetical "Marianne contras that the Earth is flat":
- Presupposition: ¬p (Earth is round, i.e., ¬flat)
- At-issue: B(m)(p) (Marianne believes Earth is flat)

NO causal chain: ¬p (ROUND) does NOT generate indicators for p (FLAT)
- ROUND generates indicators for ROUND
- There's no typical causal path from ¬p to B(x)(p)

This asymmetry DERIVES the gap from independent causal-cognitive principles.

-/

-- ============================================================================
-- Causal Model Infrastructure (via Core.StructuralEquationModel)
-- ============================================================================

/-!
The belief formation causal model uses `Core.StructuralEquationModel` —
the same Pearl-style SCM framework used for resultatives, prerequisite
semantics, and counterfactual conditionals. This avoids a parallel
graph implementation and connects the PLC to the full causal infrastructure
(interventions, counterfactuals, monotonicity proofs).
-/

open Core.StructuralEquationModel

-- ============================================================================
-- Belief Formation Causal Model (Roberts & Özyıldız 2025)
-- ============================================================================

/-!
Standard variables in belief formation, represented as
`Core.StructuralEquationModel.Variable`.
-/
namespace BeliefVars

def p : Variable := ⟨"p"⟩
def not_p : Variable := ⟨"¬p"⟩
def indic_p : Variable := ⟨"indic(p)"⟩
def indic_not_p : Variable := ⟨"indic(¬p)"⟩
def acq_a_ip : Variable := ⟨"acq(a)(iₚ)"⟩
def acq_a_inp : Variable := ⟨"acq(a)(i¬ₚ)"⟩
def B_a_p : Variable := ⟨"B(a)(p)"⟩
def B_a_not_p : Variable := ⟨"B(a)(¬p)"⟩

end BeliefVars

/--
The standard causal dynamics for knowledge/belief formation, expressed as
structural equations in the `Core.StructuralEquationModel` framework.

Each `CausalLaw.simple c e` says: if c is true, then e becomes true.
The chain p → indic(p) → acq(a)(iₚ) → B(a)(p) is four simple laws;
`normalDevelopment` propagates to fixpoint.

Key structural equations:
- indic(p) := p ∨ q (p is sufficient for its indicators; q = other sources)
- acq(a)(iₚ) := indic(p) ∧ exp(a)(iₚ) (acquaintance requires indicator + experience)
- B(a)(p) := acq(a)(iₚ) (belief results from acquaintance with evidence)
-/
def beliefFormationDynamics : CausalDynamics :=
  ⟨[ -- p generates indicators for p
     CausalLaw.simple BeliefVars.p BeliefVars.indic_p,
     -- ¬p generates indicators for ¬p, not for p
     CausalLaw.simple BeliefVars.not_p BeliefVars.indic_not_p,
     -- Acquiring indicator for p leads to belief in p
     CausalLaw.simple BeliefVars.indic_p BeliefVars.acq_a_ip,
     CausalLaw.simple BeliefVars.acq_a_ip BeliefVars.B_a_p,
     -- Acquiring indicator for ¬p leads to belief in ¬p
     CausalLaw.simple BeliefVars.indic_not_p BeliefVars.acq_a_inp,
     CausalLaw.simple BeliefVars.acq_a_inp BeliefVars.B_a_not_p ]⟩

-- ============================================================================
-- The Predicate Lexicalization Constraint
-- ============================================================================

/--
**Predicate Lexicalization Constraint (PLC)**

A verbal predicate with at-issue content α can have presupposition π iff
setting π to true and running `normalDevelopment` produces α.

This uses `causallySufficient` from `Core.StructuralEquationModel`:
the presupposition being true must be causally sufficient for the
at-issue content in the belief formation model. This is stronger than
mere graph reachability — it actually runs the structural equations.

This is the central constraint from Roberts & Özyıldız (2025).
-/
def satisfiesPLC (presup atIssue : Variable)
    (dyn : CausalDynamics := beliefFormationDynamics) : Bool :=
  causallySufficient dyn Situation.empty presup atIssue

-- ============================================================================
-- Deriving the Contrafactive Gap
-- ============================================================================

/--
**Theorem: Factives satisfy the PLC**

For "x knows p":
- Presupposition: p
- At-issue: B(a)(p)
- Causal chain: p → indic(p) → acq(a)(iₚ) → B(a)(p) ✓
-/
theorem factive_satisfies_plc :
    satisfiesPLC BeliefVars.p BeliefVars.B_a_p = true := by
  decide

/--
**Theorem: Strong contrafactives VIOLATE the PLC**

For hypothetical "x contras p":
- Presupposition: ¬p
- At-issue: B(a)(p)
- NO causal chain from ¬p to B(a)(p) ✗

This is because ¬p generates indicators for ¬p, not for p.
The fact that the Earth is round does not generate evidence
that the Earth is flat.
-/
theorem strong_contrafactive_violates_plc :
    satisfiesPLC BeliefVars.not_p BeliefVars.B_a_p = false := by
  decide

/--
**The Contrafactive Gap Theorem**

The asymmetry between factives and strong contrafactives follows from
the Predicate Lexicalization Constraint:

1. Factives (know): presup p → at-issue B(a)(p) — PLC SATISFIED
2. Strong contrafactives (contra): presup ¬p → at-issue B(a)(p) — PLC VIOLATED

This DERIVES the gap from the independently motivated causal constraint.
-/
theorem contrafactive_gap :
    satisfiesPLC BeliefVars.p BeliefVars.B_a_p = true ∧
    satisfiesPLC BeliefVars.not_p BeliefVars.B_a_p = false := by
  exact ⟨factive_satisfies_plc, strong_contrafactive_violates_plc⟩

/--
**Corollary: The asymmetry is structural, not stipulated**

The contrafactive gap emerges from the structure of belief formation:
- Beliefs are formed based on evidence
- Evidence for p comes from p being true
- Evidence for p does NOT come from ¬p being true

Therefore any predicate trying to presuppose ¬p while asserting B(x)(p)
is describing a causally incoherent eventuality.
-/
theorem contrafactive_gap_is_structural :
    -- p is causally sufficient for B(a)(p)
    causallySufficient beliefFormationDynamics .empty BeliefVars.p BeliefVars.B_a_p = true ∧
    -- ¬p is NOT causally sufficient for B(a)(p)
    causallySufficient beliefFormationDynamics .empty BeliefVars.not_p BeliefVars.B_a_p = false ∧
    -- But ¬p IS causally sufficient for B(a)(¬p)
    causallySufficient beliefFormationDynamics .empty BeliefVars.not_p BeliefVars.B_a_not_p = true := by
  decide

-- ============================================================================
-- Why Weak Contrafactives Escape the Gap
-- ============================================================================

/-!
## Weak Contrafactives (yǐwéi) and the PLC

Weak contrafactives like Mandarin yǐwéi don't violate the PLC because
their projective content is fundamentally different:

1. **Not a presupposition**: @cite{glass-2025} argues yǐwéi's falsity inference
   is a postsupposition (about output context) not presupposition (input).
   Postsuppositions are formalized in `Core.Postsupposition`.

2. **Different requirement**: yǐwéi requires CG ◇ ¬p (CG compatible with ¬p),
   not CG ⊨ ¬p (CG entails ¬p)

3. **No causal incoherence**: "p is unsettled in CG" is compatible with
   "there's evidence for p that x acquired" — these are about different
   epistemic states (communal knowledge vs individual belief)

The PLC only constrains the relationship between presupposition and
at-issue content within the SAME eventuality. Postsuppositions about
discourse context update are not subject to this constraint.
-/

-- ============================================================================
-- PLC Validation via PresupClass
-- ============================================================================

/--
Map a `PresupClass` to the corresponding causal variables for PLC checking.

- Factive: presup = p, at-issue = B(a)(p)
- Contrafactive: presup = ¬p, at-issue = B(a)(p)

For nonfactive (no presupposition) and other, the PLC doesn't apply.
-/
def presupClassToCausalVars : PresupClass → Option (Variable × Variable)
  | .factive => some (BeliefVars.p, BeliefVars.B_a_p)
  | .contrafactive => some (BeliefVars.not_p, BeliefVars.B_a_p)
  | .nonfactive => none
  | .other => none

/--
Check if a `PresupClass` satisfies the Predicate Lexicalization Constraint.

Returns `none` if the PLC doesn't apply (nonfactive, postsuppositions).
Returns `some true` if it satisfies PLC, `some false` if it violates PLC.
-/
def presupClassSatisfiesPLC (pc : PresupClass) : Option Bool :=
  match presupClassToCausalVars pc with
  | none => none
  | some (presup, atIssue) => some (satisfiesPLC presup atIssue)

/--
Is this presuppositional profile valid (attestable)?

Valid means: either satisfies PLC (factives) or not subject to PLC
(nonfactives, postsuppositions). Invalid = violates PLC (contrafactives).
-/
def presupClassIsValid (pc : PresupClass) : Bool :=
  match presupClassSatisfiesPLC pc with
  | none => true
  | some b => b

/-- Factive presuppositions are valid (satisfy PLC). -/
theorem factive_presup_valid :
    presupClassIsValid .factive = true := by
  simp [presupClassIsValid, presupClassSatisfiesPLC, presupClassToCausalVars]
  exact factive_satisfies_plc

/-- Contrafactive presuppositions are invalid (violate PLC). -/
theorem contrafactive_presup_invalid :
    presupClassIsValid .contrafactive = false := by
  simp [presupClassIsValid, presupClassSatisfiesPLC, presupClassToCausalVars]
  exact strong_contrafactive_violates_plc

/-- Nonfactive verbs are trivially valid (no presupposition to check). -/
theorem nonfactive_presup_valid :
    presupClassIsValid .nonfactive = true := rfl

-- ============================================================================
-- Additional Derived Properties
-- ============================================================================

variable {W : Type*}

/--
Veridicality constraint: if veridical, p must hold at the evaluation world.

For "know", we require p(w) at the evaluation world w.
-/
def veridicalityHolds {W : Type*} (v : Veridicality) (p : W → Prop) (w : W) : Prop :=
  match v with
  | .veridical => p w
  | .nonVeridical => True

instance veridicalityHolds_decidable {W : Type*} (v : Veridicality) (p : W → Prop)
    [DecidablePred p] (w : W) : Decidable (veridicalityHolds v p w) := by
  cases v <;> simp [veridicalityHolds] <;> infer_instance

-- Doxastic Predicate Structure

/--
A doxastic attitude predicate.

Bundles the accessibility relation with veridicality and other properties.
-/
structure DoxasticPredicate (W E : Type*) where
  /-- Name of the predicate -/
  name : String
  /-- Accessibility relation -/
  access : AccessRel W E
  /-- Veridicality (veridical or not) -/
  veridicality : Veridicality
  /-- Does it create an opaque context? (substitution failures) -/
  createsOpaqueContext : Bool := true

/--
Semantics for a doxastic predicate taking a proposition.

⟦x V that p⟧(w) = (veridicalityHolds V p w) ∧ ∀w'. R(x,w,w') → p(w')

For veridical predicates, we also require p(w).
-/
def DoxasticPredicate.holdsAt {W E : Type*}
    (V : DoxasticPredicate W E) (agent : E) (p : W → Prop)
    (w : W) (worlds : List W) : Prop :=
  veridicalityHolds V.veridicality p w ∧ boxAt V.access agent w worlds p

instance DoxasticPredicate.holdsAt_decidable {W E : Type*}
    (V : DoxasticPredicate W E) [∀ a w w', Decidable (V.access a w w')]
    (agent : E) (p : W → Prop) [DecidablePred p] (w : W) (worlds : List W) :
    Decidable (V.holdsAt agent p w worlds) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- ============================================================================
-- PrProp Construction: Doxastic Predicates as Partial Propositions
-- ============================================================================

open Core.Presupposition

/--
Convert a doxastic predicate application to a `PrProp`.

The decomposition makes the presuppositional structure explicit:
- `presup` = veridicality check (for veridical: p(w); for non-veridical: true)
- `assertion` = universal modal (∀w'. R(x,w,w') → p(w'))

`holdsAt` computes `presup(w) && assertion(w)` — the same as `PrProp.holds`.
-/
def DoxasticPredicate.toPrProp {W E : Type*}
    (V : DoxasticPredicate W E) (agent : E) (p : W → Prop)
    (worlds : List W) : PrProp W :=
  { presup := λ w => veridicalityHolds V.veridicality p w
  , assertion := λ w => boxAt V.access agent w worlds p }

/-- `toPrProp` decomposes `holdsAt`: the presup field is the veridicality
    check and the assertion field is the modal. -/
theorem DoxasticPredicate.toPrProp_presup {W E : Type*}
    (V : DoxasticPredicate W E) (agent : E) (p : W → Prop)
    (w : W) (worlds : List W) :
    (V.toPrProp agent p worlds).presup w =
    veridicalityHolds V.veridicality p w := rfl

theorem DoxasticPredicate.toPrProp_assertion {W E : Type*}
    (V : DoxasticPredicate W E) (agent : E) (p : W → Prop)
    (w : W) (worlds : List W) :
    (V.toPrProp agent p worlds).assertion w =
    boxAt V.access agent w worlds p := rfl

/-- PrProp for a hypothetical contrafactive verb: presupposes ¬p,
    asserts agent believes p. UNATTESTED — see @cite{glass-2025}. -/
def contrafactivePrProp {W E : Type*} (R : AccessRel W E) (agent : E)
    (p : W → Prop) (worlds : List W) : PrProp W :=
  { presup := λ w => ¬ p w
  , assertion := λ w => boxAt R agent w worlds p }

/--
Semantics for doxastic predicate taking a Hamblin question.

Following @cite{karttunen-1977}, "know Q" means knowing the true answer:
⟦x knows Q⟧(w) = ∃p ∈ Q. p(w) ∧ x knows p

For non-veridical predicates, we drop the p(w) requirement:
⟦x believes Q⟧(w) = ∃p ∈ Q. x believes p
-/
def DoxasticPredicate.holdsAtQuestion {W E : Type*}
    (V : DoxasticPredicate W E) (agent : E) (Q : (W → Prop) → Prop)
    (w : W) (worlds : List W) (answers : List (W → Prop)) : Prop :=
  ∃ p ∈ answers,
    Q p ∧
    (match V.veridicality with
     | .veridical => p w
     | .nonVeridical => True) ∧
    boxAt V.access agent w worlds p

-- Standard Doxastic Predicates (Abstract)

/--
Abstract "believe" predicate template.

Users instantiate with their specific accessibility relation.
-/
def believeTemplate {W E : Type*} (R : AccessRel W E) : DoxasticPredicate W E :=
  { name := "believe"
  , access := R
  , veridicality := .nonVeridical
  , createsOpaqueContext := true
  }

/--
Abstract "know" predicate template.

Veridical: knowing p requires p to be true.
-/
def knowTemplate {W E : Type*} (R : AccessRel W E) : DoxasticPredicate W E :=
  { name := "know"
  , access := R
  , veridicality := .veridical
  , createsOpaqueContext := true
  }

/--
Abstract "think" predicate template.

Non-veridical, typically less commitment than "believe".
-/
def thinkTemplate {W E : Type*} (R : AccessRel W E) : DoxasticPredicate W E :=
  { name := "think"
  , access := R
  , veridicality := .nonVeridical
  , createsOpaqueContext := true
  }

-- Properties and Theorems

/--
Veridical predicates entail their complement.

If x knows p at w, then p is true at w.
-/
theorem veridical_entails_complement {W E : Type*}
    (V : DoxasticPredicate W E) (hV : V.veridicality = .veridical)
    (agent : E) (p : W → Prop) (w : W) (worlds : List W)
    (holds : V.holdsAt agent p w worlds) : p w := by
  unfold DoxasticPredicate.holdsAt at holds
  simp only [hV, veridicalityHolds] at holds
  exact holds.1

/--
Non-veridical predicates don't entail their complement.

There exist cases where x believes p but p is false.
-/
theorem nonVeridical_not_entails {W E : Type*} [Inhabited W] [Inhabited E]
    (V : DoxasticPredicate W E) (hV : V.veridicality = .nonVeridical) :
    ∃ (agent : E) (p : W → Prop) (w : W) (worlds : List W),
      V.holdsAt agent p w worlds ∧ ¬ p w :=
  -- Use empty worlds list: boxAt is vacuously true, p w can be False
  ⟨default, fun _ => False, default, [], by
    simp [DoxasticPredicate.holdsAt, hV, veridicalityHolds, boxAt]⟩

/--
Doxastic predicates are closed under known implication.

If x knows p and x knows (p → q), then x knows q.
(This is the K axiom of modal logic)
-/
theorem doxastic_k_axiom {W E : Type*}
    (V : DoxasticPredicate W E) (agent : E) (p q : W → Prop)
    (w : W) (worlds : List W)
    (hp : boxAt V.access agent w worlds p)
    (hpq : boxAt V.access agent w worlds (λ w' => p w' → q w')) :
    boxAt V.access agent w worlds q := by
  intro w' hw' hR
  exact hpq w' hw' hR (hp w' hw' hR)

-- Substitution and Opacity

/-!
## Substitution and Opacity

Opaque contexts block substitution of co-referential terms.

Even if a = b (extensionally), "x believes Fa" may differ from "x believes Fb"
because the agent may not know a = b.

This is formalized by the `createsOpaqueContext` field: when true, the predicate
operates on intensions (functions from worlds), not extensions.
-/

/--
For opaque predicates, substitution failure is possible.

This is a statement that the predicate distinguishes intensions that
happen to have the same extension at the evaluation world.
-/
def substitutionMayFail {W E : Type*} (V : DoxasticPredicate W E) : Prop :=
  V.createsOpaqueContext = true →
  ∃ (agent : E) (p q : W → Prop) (w : W) (worlds : List W),
    (p w ↔ q w) ∧  -- Same extension at w
    p ≠ q ∧        -- Different intensions
    ¬ (V.holdsAt agent p w worlds ↔ V.holdsAt agent q w worlds)

-- De Dicto vs De Re

/--
De dicto reading: quantifier under the attitude.

"John believes someone is a spy" (de dicto) =
John believes ∃x. spy(x)
-/
def deDicto {W E : Type*} (V : DoxasticPredicate W E)
    (agent : E) (p : W → Prop) (w : W) (worlds : List W) : Prop :=
  V.holdsAt agent p w worlds

/--
De re reading: quantifier over the attitude.

"John believes someone is a spy" (de re) =
∃x. John believes spy(x)

Here we need a domain of individuals to quantify over.
-/
def deRe {W E D : Type*} (V : DoxasticPredicate W E)
    (agent : E) (predicate : D → W → Prop) (domain : List D)
    (w : W) (worlds : List W) : Prop :=
  ∃ x ∈ domain, V.holdsAt agent (predicate x) w worlds

-- Connection to Scalar Implicature

/-!
## Attitude Embedding and Scalar Implicature

When scalar expressions are embedded under attitudes, the implicature
can be computed locally (inside the attitude) or globally (about speaker):

**Global**: Speaker implicates ¬(speaker believes all)
**Local**: x believes (some ∧ ¬all) [apparent local reading]

@cite{goodman-stuhlmuller-2013} show the "local" reading arises from
pragmatic inference about speaker knowledge, not true local computation.

See `RSA/Implementations/GoodmanStuhlmuller2013.lean` for the RSA treatment.
-/

-- ════════════════════════════════════════════════════════════════
-- Bridge: Veridicality → @cite{searle-1983} Causal Self-Referentiality
-- ════════════════════════════════════════════════════════════════

open Core.Discourse (PsychMode CausalSelfRef)

/-- Map veridicality to @cite{searle-1983}'s psychological mode.

    Veridical attitudes (know, realize) are like perception: the world must
    *cause* the mental state (you can only know p if p is the case and your
    epistemic state is appropriately caused by p's being the case).
    Non-veridical attitudes (believe, think) are like belief: satisfaction
    depends only on whether p obtains, not on the causal chain. -/
def psychMode : Veridicality → PsychMode
  | .veridical    => .perception  -- know: world must cause the state
  | .nonVeridical  => .belief     -- believe: no causal requirement

/-- Veridical attitudes are causally self-referential (world→state);
    non-veridical attitudes are not. This connects the linguistic
    veridicality distinction to @cite{searle-1983}'s metaphysics:
    knowledge requires the world to cause the knowing, while belief
    requires only that the content match reality. -/
theorem veridical_self_referential :
    (psychMode .veridical).causalSelfRef = .worldToState ∧
    (psychMode .nonVeridical).causalSelfRef = .none :=
  ⟨rfl, rfl⟩

end Semantics.Attitudes.Doxastic
