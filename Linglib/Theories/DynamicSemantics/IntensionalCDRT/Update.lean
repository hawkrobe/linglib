/-
# Flat Update Operations for ICDRT

Hofmann (2025) §2.3-2.4: The core innovation of flat update semantics.

## Flat Update

In standard DRT, discourse referents introduced under negation are
inaccessible for later anaphora:
  "There's no bathroom. #It is upstairs."  -- standard DRT: infelicitous

Hofmann's flat update changes this:
1. All drefs are introduced globally (at the top level)
2. Propositional drefs track WHERE drefs were introduced (local context)
3. Accessibility depends on local context, not syntactic scope

## The Relative Variable Update: i[φ : v]j

The central mechanism is relative variable update:
  i[φ : v]j iff j differs from i at most in that j(v) is some entity
            that exists in the local context φ^j

This allows indefinites to "scope out" while tracking their local context.

## Example: Double Negation

"It's not the case that there's no bathroom."
1. Outer negation: swaps positive/negative
2. Inner negation: introduces dref in negative update
3. Double negation: dref accessible in positive update!

## References

- Hofmann (2025) §2.3-2.4
- Groenendijk & Stokhof (1991). Dynamic Predicate Logic.
-/

import Linglib.Theories.DynamicSemantics.IntensionalCDRT.Basic

namespace Theories.DynamicSemantics.IntensionalCDRT

open Core


/--
Relative variable update: i[φ : v]j

Given propositional dref φ (the local context) and individual variable v,
assignment j is a "φ-v extension" of assignment i iff:
1. j agrees with i on all propositional variables
2. j agrees with i on all individual variables except possibly v
3. j(v) is some entity e such that e exists in all worlds of φ^j

In Hofmann's notation (Definition 1, p.11):
  i[φ : v]j iff ∃e: j = i[v ↦ e] and j(v) ∈ DOM_e(φ^j)
  where DOM_e(p) = { e | ∀w ∈ p: e ≠ ⋆ }

Note: j(v) must be a real entity (not ⋆) that exists throughout φ^j.
-/
def relativeVarUpdate {W E : Type*}
    (φ : PVar)  -- The propositional variable tracking local context
    (v : IVar)  -- The individual variable being bound
    (i j : ICDRTAssignment W E)
    : Prop :=
  -- j agrees with i on all propositional variables
  (∀ p : PVar, j.prop p = i.prop p) ∧
  -- j agrees with i on all individual variables except v
  (∀ u : IVar, u ≠ v → j.indiv u = i.indiv u) ∧
  -- j(v) is a real entity (not ⋆)
  (∃ e : E, j.indiv v = .some e) ∧
  -- The entity exists in all worlds of the local context φ^j
  -- (Since j.indiv v is guaranteed to be .some e, this is automatic)
  True

notation:50 i "[" φ " : " v "]" j => relativeVarUpdate φ v i j

/--
Alternative formulation: the entity domain in a local context.

DOM_e(p) = { e | e is defined throughout p }

For individual drefs that map to ⋆ in some worlds of p, those drefs
are not in the entity domain of p.
-/
def entityDomain {W E : Type*} (p : Set W) (dref : W → Entity E) : Set E :=
  { e | ∀ w ∈ p, dref w = .some e }

/--
Relative variable update with existential witness made explicit.
-/
def relativeVarUpdate' {W E : Type*}
    (φ : PVar)
    (v : IVar)
    (i j : ICDRTAssignment W E)
    : Prop :=
  -- j agrees with i on propositional assignments
  j.prop = i.prop ∧
  -- j = i[v ↦ e] for some real entity e
  (∃ e : E,
    j.indiv v = .some e ∧
    ∀ u : IVar, u ≠ v → j.indiv u = i.indiv u)


/--
Flat existential update: ∃v.φ

The existential introduces v globally,
but the propositional dref tracks the local context.

In Hofmann's system:
  ⟦∃v.φ⟧^+ c = { (j, w) | ∃i: (i,w) ∈ c and i[p:v]j and (j,w) ∈ ⟦φ⟧^+ }

where p is a fresh propositional variable that will track the local context
where v has a referent.
-/
def flatExists {W E : Type*}
    (p : PVar)   -- Fresh propositional variable for local context
    (v : IVar)   -- Individual variable being bound
    (body : IContext W E → IContext W E)  -- The scope
    (c : IContext W E)
    : IContext W E :=
  { jw | ∃ i, (i, jw.2) ∈ c ∧ relativeVarUpdate' p v i jw.1 ∧ jw ∈ body c }

/--
Flat existential with explicit entity quantification.

This version makes clear that we quantify over entities e,
extend the assignment, and track the local context.
-/
def flatExistsExplicit {W E : Type*}
    (p : PVar)
    (v : IVar)
    (localCtx : ICDRTAssignment W E → Set W)  -- The local context where v exists
    (body : IContext W E → IContext W E)
    (c : IContext W E)
    : IContext W E :=
  { jw |
    ∃ i e,
      -- i was in the original context
      (i, jw.2) ∈ c ∧
      -- j extends i by binding v to e
      jw.1 = i.updateIndiv v (.some e) ∧
      -- j also records the local context in propositional variable p
      jw.1.prop p = localCtx jw.1 ∧
      -- (j, w) survives the body update
      jw ∈ body c }


/--
Extend context with random assignment for variable v.

Unlike standard randomAssign, this:
1. Only assigns real entities (not ⋆)
2. Tracks assignments in all worlds (flat)
-/
def extendContext {W E : Type*}
    (c : IContext W E)
    (v : IVar)
    (domain : Set E)
    : IContext W E :=
  { jw |
    ∃ i e,
      (i, jw.2) ∈ c ∧
      e ∈ domain ∧
      jw.1 = i.updateIndiv v (.some e) }

/--
Extend context and track local context in propositional variable.
-/
def extendContextWithLocal {W E : Type*}
    (c : IContext W E)
    (v : IVar)
    (p : PVar)
    (domain : Set E)
    (localCtx : Set W)
    : IContext W E :=
  { jw |
    ∃ i e,
      (i, jw.2) ∈ c ∧
      e ∈ domain ∧
      jw.1 = (i.updateIndiv v (.some e)).updateProp p localCtx }


/--
Update context with proposition, yielding local context.

The local context is the set of worlds where the proposition holds.
-/
def updateWithProposition {W E : Type*}
    (c : IContext W E)
    (prop : W → Prop)
    : IContext W E × Set W :=
  let c' := c.update prop
  let localCtx := { w | ∃ g, (g, w) ∈ c' }
  (c', localCtx)

/--
Update relative to a propositional dref (local context).

⟦φ⟧_p evaluates φ in the local context p, not the global context.
-/
def updateInLocalContext {W E : Type*}
    (c : IContext W E)
    (p : PVar)
    (prop : ICDRTAssignment W E → W → Prop)
    : IContext W E :=
  { gw ∈ c | ∀ w' ∈ gw.1.prop p, prop gw.1 w' }


/--
Initialize propositional dref to the current context's worlds.

When introducing an existential, the propositional dref is set to
the current local context (worlds where the indefinite is introduced).
-/
def initPropDref {W E : Type*}
    (c : IContext W E)
    (p : PVar)
    (g : ICDRTAssignment W E)
    : Set W :=
  { w | (g, w) ∈ c }

/--
Narrow propositional dref after update.

When updating with a proposition, propositional drefs that track
local contexts should be narrowed accordingly.
-/
def narrowPropDref {W E : Type*}
    (g : ICDRTAssignment W E)
    (p : PVar)
    (prop : W → Prop)
    : ICDRTAssignment W E :=
  g.updateProp p { w ∈ g.prop p | prop w }


/--
Bilateral ICDRT denotation: positive and negative updates.

Following Hofmann's bilateral approach (building on Elliott & Sudo):
- Positive update: what survives assertion
- Negative update: what survives denial

The key property: negation swaps positive and negative.
-/
structure BilateralICDRT (W : Type*) (E : Type*) where
  /-- Positive update (assertion) -/
  positive : IContext W E → IContext W E
  /-- Negative update (denial) -/
  negative : IContext W E → IContext W E

namespace BilateralICDRT

variable {W E : Type*}

/-- Negation: swap positive and negative -/
def neg (φ : BilateralICDRT W E) : BilateralICDRT W E where
  positive := φ.negative
  negative := φ.positive

/-- Double negation elimination (definitional!) -/
@[simp]
theorem neg_neg (φ : BilateralICDRT W E) : φ.neg.neg = φ := rfl

/-- Atomic proposition -/
def atom (prop : W → Prop) : BilateralICDRT W E where
  positive := λ c => c.update prop
  negative := λ c => c.update (λ w => ¬prop w)

/-- Conjunction: sequence positive updates -/
def conj (φ ψ : BilateralICDRT W E) : BilateralICDRT W E where
  positive := λ c => ψ.positive (φ.positive c)
  negative := λ c => φ.negative c ∪ (φ.positive c ∩ ψ.negative (φ.positive c))

/-- Notation -/
prefix:max "∼" => neg
infixl:65 " ⊗ " => conj

end BilateralICDRT


/--
Flat existential with bilateral structure.

The existential introduces drefs in both positive and negative
updates. This is what makes double negation accessible:

⟦¬¬∃x.P(x)⟧^+ = ⟦∃x.P(x)⟧^+ (by DNE)

The dref x introduced in the inner scope is accessible in the outer scope
because flat update introduces it globally.
-/
def BilateralICDRT.exists_ {W E : Type*}
    (p : PVar)
    (v : IVar)
    (domain : Set E)
    (body : BilateralICDRT W E)
    : BilateralICDRT W E where
  positive := λ c =>
    let extended := extendContext c v domain
    body.positive extended
  negative := λ c =>
    -- For negative: no entity makes the body true
    { gw ∈ c | ∀ e ∈ domain,
        let g' := gw.1.updateIndiv v (.some e)
        (g', gw.2) ∉ body.positive (extendContext c v domain) }


end Theories.DynamicSemantics.IntensionalCDRT
