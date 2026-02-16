/-
# Doxastic Attitude Semantics

Modal/accessibility-based semantics for doxastic attitude verbs like
`believe`, `know`, `think`.

## Semantic Mechanism

Doxastic attitudes use Hintikka-style accessibility relations:
- R(x, w, w') means w' is compatible with what x believes/knows in w
- ⟦x believes p⟧(w) = ∀w'. R(x,w,w') → p(w')

## Veridicality

- **Veridical** (know, realize): x V p ⊢ p
- **Non-veridical** (believe, think): x V p ⊬ p

## Question Embedding

Doxastic attitudes can embed questions via exhaustive interpretation:
- ⟦x knows Q⟧ = ∀p ∈ Q. (p true → x knows p) ∧ (p false → x knows ¬p)

## References

- Hintikka (1969). Knowledge and Belief.
- Heim (1992). Presupposition projection and the semantics of attitude verbs.
- Karttunen (1977). Syntax and semantics of questions.
-/

import Linglib.Core.Proposition
import Linglib.Core.ModalLogic
import Linglib.Theories.Semantics.Questions.Hamblin

namespace IntensionalSemantics.Attitude.Doxastic

open Core.Proposition

-- Accessibility Relations

/--
Doxastic accessibility relation type.

R(agent, evalWorld, accessibleWorld) = true iff accessibleWorld is compatible
with what agent believes/knows in evalWorld.
-/
abbrev AccessRel (W E : Type*) := Core.ModalLogic.AgentAccessRel W E

/--
Universal modal: true at w iff p true at all accessible worlds.

⟦□p⟧(w) = ∀w'. R(w,w') → p(w')
-/
def boxAt {W E : Type*} (R : AccessRel W E) (agent : E) (w : W)
    (worlds : List W) (p : W → Bool) : Bool :=
  worlds.all λ w' => !R agent w w' || p w'

/--
Existential modal: true at w iff p true at some accessible world.

⟦◇p⟧(w) = ∃w'. R(w,w') ∧ p(w')
-/
def diaAt {W E : Type*} (R : AccessRel W E) (agent : E) (w : W)
    (worlds : List W) (p : W → Bool) : Bool :=
  worlds.any λ w' => R agent w w' && p w'

-- Veridicality

/--
A doxastic predicate is veridical if believing/knowing p entails p is true.

Veridical: know, realize, discover
Non-veridical: believe, think, suspect
-/
inductive Veridicality where
  | veridical      -- x V p ⊢ p (knowledge, factives)
  | nonVeridical   -- x V p ⊬ p (belief, opinion)
  deriving DecidableEq, Repr, BEq

-- Common Ground Requirements (Glass 2025)

/--
Common Ground requirement polarity: does the verb place requirements on p or ¬p?

Glass (2025) distinguishes belief verbs by whether their projective content
concerns p (positive) or ¬p (negative).
-/
inductive CGPolarity where
  | positive   -- requirement concerns p (e.g., know requires p)
  | negative   -- requirement concerns ¬p (e.g., yǐwéi requires ◇¬p)
  deriving DecidableEq, Repr, BEq

/--
Common Ground requirement strength: entailment (□) or compatibility (◇)?

- `necessity`: CG must entail the condition (∀w ∈ c. φ(w))
- `possibility`: CG must be compatible with the condition (∃w ∈ c. φ(w))
-/
inductive CGStrength where
  | necessity    -- □: all CG worlds satisfy condition
  | possibility  -- ◇: some CG world satisfies condition
  deriving DecidableEq, Repr, BEq

/--
Common Ground requirement for belief verbs.

Glass (2025) proposes a 2×2 typology based on polarity × strength:
- Factive (know): positive × necessity → CG ⊨ p
- Nonfactive (think): no requirement
- Weak contrafactive (yǐwéi): negative × possibility → CG ◇ ¬p
- Strong contrafactive (contra): negative × necessity → CG ⊨ ¬p (UNATTESTED)

The key insight: weak contrafactives exist (Mandarin yǐwéi), but strong
contrafactives requiring ¬p to be Common Ground are systematically absent.
-/
structure CGRequirement where
  polarity : CGPolarity
  strength : CGStrength
  deriving DecidableEq, Repr, BEq

namespace CGRequirement

/-- Factive requirement: CG entails p (know, realize) -/
def factive : CGRequirement := ⟨.positive, .necessity⟩

/-- Weak contrafactive: CG compatible with ¬p (Mandarin yǐwéi) -/
def weakContrafactive : CGRequirement := ⟨.negative, .possibility⟩

/-- Strong contrafactive: CG entails ¬p (hypothetical "contra" - UNATTESTED) -/
def strongContrafactive : CGRequirement := ⟨.negative, .necessity⟩

/-- Is this requirement satisfied given a context set and proposition? -/
def satisfied {W : Type*} (req : CGRequirement) (contextSet : List W) (p : W → Bool) : Bool :=
  match req.polarity, req.strength with
  | .positive, .necessity => contextSet.all p           -- ∀w ∈ c. p(w)
  | .positive, .possibility => contextSet.any p         -- ∃w ∈ c. p(w)
  | .negative, .necessity => contextSet.all (!p ·)      -- ∀w ∈ c. ¬p(w)
  | .negative, .possibility => contextSet.any (!p ·)    -- ∃w ∈ c. ¬p(w)

end CGRequirement

-- ============================================================================
-- Derivation: Veridicality → CG Requirement
-- ============================================================================

/-!
## Deriving CG Requirements from Semantic Structure

Glass (2025) shows that for DOXASTIC verbs, the CG requirement is NOT a
separate lexical property - it follows from VERIDICALITY:

- **Veridical** (know): presupposes p → factive CG requirement
- **Non-veridical** (believe): no presupposition → no CG requirement

The key insight: `cgRequirement` should be DERIVED, not stipulated.

### Postsuppositions (yǐwéi)

yǐwéi is special: it has a POSTSUPPOSITION (output-context constraint),
not a presupposition (input-context constraint). Its requirement ◇¬p
applies AFTER the utterance updates the context.

This is genuinely lexical (exceptional) and not derivable from veridicality.
-/

/--
Derive CG requirement from veridicality for doxastic verbs.

This captures the systematic relationship:
- Veridical verbs presuppose their complement → factive requirement
- Non-veridical verbs have no presupposition → no requirement

Note: Postsuppositions (like yǐwéi's ◇¬p) are NOT captured here
because they're about output context, not input presupposition.
-/
def deriveCGRequirement (v : Veridicality) : Option CGRequirement :=
  match v with
  | .veridical => some CGRequirement.factive       -- know → CG ⊨ p
  | .nonVeridical => none                          -- believe → no requirement

/--
**Theorem**: Factives have factive CG requirements.

This is a DERIVATION, not a stipulation. The factive presupposition
follows from the verb being veridical.
-/
theorem veridical_implies_factive :
    deriveCGRequirement .veridical = some CGRequirement.factive := rfl

/--
**Theorem**: Non-veridical verbs have no CG requirement.

This is why believe/think don't presuppose anything about p.
-/
theorem nonVeridical_implies_none :
    deriveCGRequirement .nonVeridical = none := rfl

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

### References

- Pearl (2000). Causality: Models, Reasoning, and Inference.
- Roberts & Simons (2024). Presupposition as ontological precondition.
- Roberts & Özyıldız (2025). A causal explanation for the contrafactive gap.
-/

-- ============================================================================
-- Causal Model Infrastructure (Pearl 2000)
-- ============================================================================

/--
A variable in a causal model. Variables can be exogenous (external) or
endogenous (determined by structural equations).
-/
structure CausalVar where
  name : String
  deriving DecidableEq, Repr, BEq, Hashable

/--
A causal edge represents direct causal influence: (parent, child) means
the value of parent directly influences the value of child.
-/
structure CausalEdge where
  parent : CausalVar
  child : CausalVar
  deriving Repr, BEq

/--
A causal model M = (U, V, E) where:
- exog: Exogenous variables (determined externally)
- endog: Endogenous variables (determined by structural equations)
- edges: Causal edges representing direct influence

This is a simplified Pearl (2000) causal model for our purposes.
-/
structure CausalModel where
  exog : List CausalVar
  endog : List CausalVar
  edges : List CausalEdge
  deriving Repr

namespace CausalModel

/-- All variables in the model -/
def allVars (M : CausalModel) : List CausalVar :=
  M.exog ++ M.endog

/-- Get parents of a variable (direct causes) -/
def parents (M : CausalModel) (v : CausalVar) : List CausalVar :=
  (M.edges.filter (·.child == v)).map (·.parent)

/-- Get children of a variable (direct effects) -/
def children (M : CausalModel) (v : CausalVar) : List CausalVar :=
  (M.edges.filter (·.parent == v)).map (·.child)

/--
Check if there's a causal path from v₁ to v₂.

A causal chain exists from v₁ to v₂ iff altering v₁ can alter v₂.
This is the transitive closure of the edge relation.
-/
def hasCausalChain (M : CausalModel) (v1 v2 : CausalVar) : Bool :=
  -- BFS to find if v2 is reachable from v1
  let rec search (frontier : List CausalVar) (visited : List CausalVar) (fuel : Nat) : Bool :=
    match fuel with
    | 0 => false  -- Timeout
    | fuel + 1 =>
      if frontier.isEmpty then false
      else if frontier.any (· == v2) then true
      else
        let newVisited := visited ++ frontier
        let newFrontier := frontier.flatMap (M.children ·) |>.filter (fun v => !newVisited.any (· == v))
        search newFrontier newVisited fuel
  search [v1] [] (M.allVars.length + 1)

end CausalModel

-- ============================================================================
-- Belief Formation Causal Model (Roberts & Özyıldız 2025)
-- ============================================================================

/-!
Standard variables in belief formation causal models.
-/
namespace BeliefVars

/-- The proposition p being true/false -/
def p : CausalVar := ⟨"p"⟩

/-- The negation ¬p -/
def not_p : CausalVar := ⟨"¬p"⟩

/-- Indicators (evidence) for p: indic(p) -/
def indic_p : CausalVar := ⟨"indic(p)"⟩

/-- Indicators (evidence) for ¬p: indic(¬p) -/
def indic_not_p : CausalVar := ⟨"indic(¬p)"⟩

/-- Agent a acquires indicator for p: acq(a)(iₚ) -/
def acq_a_ip : CausalVar := ⟨"acq(a)(iₚ)"⟩

/-- Agent a acquires indicator for ¬p: acq(a)(i¬ₚ) -/
def acq_a_inp : CausalVar := ⟨"acq(a)(i¬ₚ)"⟩

/-- Agent believes p: B(a)(p) -/
def B_a_p : CausalVar := ⟨"B(a)(p)"⟩

/-- Agent believes ¬p: B(a)(¬p) -/
def B_a_not_p : CausalVar := ⟨"B(a)(¬p)"⟩

end BeliefVars

/--
The standard causal model for knowledge/belief formation.

This captures the Roberts & Özyıldız insight that:
1. Facts generate indicators (evidence)
2. Agents acquire indicators through experience
3. Acquisition of indicators leads to belief formation

Key structural equations:
- indic(p) := p ∨ q  (p is sufficient for its indicators; q = other sources)
- acq(a)(iₚ) := indic(p) ∧ exp(a)(iₚ)  (acquaintance requires indicator + experience)
- B(a)(p) := acq(a)(iₚ)  (belief results from acquaintance with evidence)
-/
def beliefFormationModel : CausalModel :=
  { exog := [BeliefVars.p, BeliefVars.not_p]
  , endog := [BeliefVars.indic_p, BeliefVars.indic_not_p,
              BeliefVars.acq_a_ip, BeliefVars.acq_a_inp,
              BeliefVars.B_a_p, BeliefVars.B_a_not_p]
  , edges := [
      -- p generates indicators for p
      ⟨BeliefVars.p, BeliefVars.indic_p⟩,
      -- ¬p generates indicators for ¬p, not for p
      ⟨BeliefVars.not_p, BeliefVars.indic_not_p⟩,
      -- Acquiring indicator for p leads to belief in p
      ⟨BeliefVars.indic_p, BeliefVars.acq_a_ip⟩,
      ⟨BeliefVars.acq_a_ip, BeliefVars.B_a_p⟩,
      -- Acquiring indicator for ¬p leads to belief in ¬p
      ⟨BeliefVars.indic_not_p, BeliefVars.acq_a_inp⟩,
      ⟨BeliefVars.acq_a_inp, BeliefVars.B_a_not_p⟩
    ]
  }

-- ============================================================================
-- The Predicate Lexicalization Constraint
-- ============================================================================

/--
**Predicate Lexicalization Constraint (PLC)**

A verbal predicate with at-issue content α can have presupposition π iff
there exists a causal chain from π to α in the belief formation model.

This is the central constraint from Roberts & Özyıldız (2025).
-/
def satisfiesPLC (presup atIssue : CausalVar) (M : CausalModel := beliefFormationModel) : Bool :=
  M.hasCausalChain presup atIssue

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
  native_decide

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
  native_decide

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
    -- There exists a causal path from p to B(a)(p)
    beliefFormationModel.hasCausalChain BeliefVars.p BeliefVars.B_a_p = true ∧
    -- There is NO causal path from ¬p to B(a)(p)
    beliefFormationModel.hasCausalChain BeliefVars.not_p BeliefVars.B_a_p = false ∧
    -- But there IS a path from ¬p to B(a)(¬p)
    beliefFormationModel.hasCausalChain BeliefVars.not_p BeliefVars.B_a_not_p = true := by
  native_decide

-- ============================================================================
-- Why Weak Contrafactives Escape the Gap
-- ============================================================================

/-!
## Weak Contrafactives (yǐwéi) and the PLC

Weak contrafactives like Mandarin yǐwéi don't violate the PLC because
their projective content is fundamentally different:

1. **Not a presupposition**: Glass (2022) argues yǐwéi's falsity inference
   is a postsupposition (about output context) not presupposition (input)

2. **Different requirement**: yǐwéi requires CG ◇ ¬p (CG compatible with ¬p),
   not CG ⊨ ¬p (CG entails ¬p)

3. **No causal incoherence**: "p is unsettled in CG" is compatible with
   "there's evidence for p that x acquired" — these are about different
   epistemic states (communal knowledge vs individual belief)

The PLC only constrains the relationship between presupposition and
at-issue content within the SAME eventuality. Postsuppositions about
discourse context update are not subject to this constraint.
-/

/--
Weak contrafactive is NOT a strong contrafactive - different structure.
The requirement is ∃w ∈ CG. ¬p(w), not ∀w ∈ CG. ¬p(w).
-/
theorem weak_vs_strong_contrafactive :
    CGRequirement.weakContrafactive ≠ CGRequirement.strongContrafactive := by
  intro h
  have : CGRequirement.weakContrafactive.strength = CGRequirement.strongContrafactive.strength := by
    rw [h]
  simp [CGRequirement.weakContrafactive, CGRequirement.strongContrafactive] at this

-- ============================================================================
-- Additional Derived Properties
-- ============================================================================

variable {W : Type*}

/--
Veridicality constraint: if veridical, accessible worlds ⊆ actual world's p-value.

For "know", we require: p(w) = true for the evaluation world w.
-/
def veridicalityHolds {W : Type*} (v : Veridicality) (p : W → Bool) (w : W) : Bool :=
  match v with
  | .veridical => p w  -- Must be true at evaluation world
  | .nonVeridical => true  -- No constraint

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

For veridical predicates, we also require p(w) = true.
-/
def DoxasticPredicate.holdsAt {W E : Type*}
    (V : DoxasticPredicate W E) (agent : E) (p : W → Bool)
    (w : W) (worlds : List W) : Bool :=
  veridicalityHolds V.veridicality p w && boxAt V.access agent w worlds p

/--
Semantics for doxastic predicate taking a Hamblin question.

Following Karttunen (1977), "know Q" means knowing the true answer:
⟦x knows Q⟧(w) = ∃p ∈ Q. p(w) ∧ x knows p

For non-veridical predicates, we drop the p(w) requirement:
⟦x believes Q⟧(w) = ∃p ∈ Q. x believes p
-/
def DoxasticPredicate.holdsAtQuestion {W E : Type*}
    (V : DoxasticPredicate W E) (agent : E) (Q : (W → Bool) → Bool)
    (w : W) (worlds : List W) (answers : List (W → Bool)) : Bool :=
  answers.any λ p =>
    Q p &&  -- p is an answer to Q
    (match V.veridicality with
     | .veridical => p w  -- For know: p must be true
     | .nonVeridical => true) &&  -- For believe: no truth requirement
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
    (agent : E) (p : W → Bool) (w : W) (worlds : List W)
    (holds : V.holdsAt agent p w worlds = true) : p w = true := by
  unfold DoxasticPredicate.holdsAt at holds
  simp only [hV, veridicalityHolds, Bool.and_eq_true] at holds
  exact holds.1

/--
Non-veridical predicates don't entail their complement.

There exist cases where x believes p but p is false.
-/
theorem nonVeridical_not_entails {W E : Type*} [Inhabited W] [Inhabited E]
    (V : DoxasticPredicate W E) (hV : V.veridicality = .nonVeridical) :
    ∃ (agent : E) (p : W → Bool) (w : W) (worlds : List W),
      V.holdsAt agent p w worlds = true ∧ p w = false :=
  -- Use empty worlds list: boxAt is vacuously true, p w can be false
  ⟨default, fun _ => false, default, [], by simp [DoxasticPredicate.holdsAt, hV, veridicalityHolds, boxAt]⟩

/--
Doxastic predicates are closed under known implication.

If x knows p and x knows (p → q), then x knows q.
(This is the K axiom of modal logic)
-/
theorem doxastic_k_axiom {W E : Type*}
    (V : DoxasticPredicate W E) (agent : E) (p q : W → Bool)
    (w : W) (worlds : List W)
    (hp : boxAt V.access agent w worlds p = true)
    (hpq : boxAt V.access agent w worlds (λ w' => !p w' || q w') = true) :
    boxAt V.access agent w worlds q = true := by
  simp only [boxAt, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at *
  intro w' hw'
  cases hR : V.access agent w w'
  · left; rfl
  · right
    have h1 := hp w' hw'; simp [hR] at h1
    have h2 := hpq w' hw'; simp [hR, h1] at h2
    exact h2

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
  ∃ (agent : E) (p q : W → Bool) (w : W) (worlds : List W),
    p w = q w ∧  -- Same extension at w
    p ≠ q ∧      -- Different intensions
    V.holdsAt agent p w worlds ≠ V.holdsAt agent q w worlds

-- De Dicto vs De Re

/--
De dicto reading: quantifier under the attitude.

"John believes someone is a spy" (de dicto) =
John believes ∃x. spy(x)
-/
def deDicto {W E : Type*} (V : DoxasticPredicate W E)
    (agent : E) (p : W → Bool) (w : W) (worlds : List W) : Bool :=
  V.holdsAt agent p w worlds

/--
De re reading: quantifier over the attitude.

"John believes someone is a spy" (de re) =
∃x. John believes spy(x)

Here we need a domain of individuals to quantify over.
-/
def deRe {W E D : Type*} (V : DoxasticPredicate W E)
    (agent : E) (predicate : D → W → Bool) (domain : List D)
    (w : W) (worlds : List W) : Bool :=
  domain.any λ x => V.holdsAt agent (predicate x) w worlds

-- Connection to Scalar Implicature

/-!
## Attitude Embedding and Scalar Implicature

When scalar expressions are embedded under attitudes, the implicature
can be computed locally (inside the attitude) or globally (about speaker):

**Global**: Speaker implicates ¬(speaker believes all)
**Local**: x believes (some ∧ ¬all) [apparent local reading]

Goodman & Stuhlmüller (2013) show the "local" reading arises from
pragmatic inference about speaker knowledge, not true local computation.

See `RSA/Implementations/GoodmanStuhlmuller2013.lean` for the RSA treatment.
-/

end IntensionalSemantics.Attitude.Doxastic
