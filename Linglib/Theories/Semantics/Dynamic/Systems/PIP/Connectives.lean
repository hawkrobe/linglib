import Linglib.Theories.Semantics.Dynamic.Systems.PIP.Basic

/-!
# PIP Connectives and Modal Operators

@cite{keshet-abney-2024} @cite{frank-1997} @cite{kratzer-1991} @cite{veltman-1996}Dynamic encoding of PIP connectives (Keshet & Abney 2024):
- Conjunction, negation, disjunction (with label floating)
- Labeled existential quantification
- Modal operators (must, might, would) as world quantifiers
- External vs. local variable binding

## Label Floating

In PIP, formula labels (X ≡ φ) are tautological and float freely to
the top of any discourse. Our dynamic encoding simulates this by
threading labels through all operators monotonically: labels from
earlier operators are always available to later ones.

## Modals as World Quantifiers

PIP's modals are generalized quantifiers over worlds (paper Section 2.5):
- MIGHT^β_w(W₁, W₂) ≜ SOME(β_w ∩ W₁, W₂)
- MUST^β_w(W₁, W₂) ≜ EVERY(β_w ∩ W₁, W₂)

Our encoding parameterizes by an accessibility relation (equivalent to
a Kratzer modal base β) and quantifies over accessible worlds.

-/

namespace Semantics.Dynamic.PIP

open Semantics.Dynamic.Core
open Semantics.Dynamic.IntensionalCDRT

variable {W E : Type*}


-- ============================================================
-- Core Connectives
-- ============================================================

/--
Atomic predicate: filters the info state to pairs satisfying the predicate.
Labels are preserved.
-/
def atom (pred : ICDRTAssignment W E → W → Bool) : PUpdate W E :=
  λ d => d.mapInfo (λ c => { gw ∈ c | pred gw.1 gw.2 })

/--
Negation: complement of info state relative to input.
Labels are **preserved** — this is the key property enabling cross-negation
anaphora (bathroom sentences).
-/
def negation (φ : PUpdate W E) : PUpdate W E :=
  λ d =>
    let result := φ d
    -- Labels come from the body (which may have registered new labels)
    -- Info state: keep pairs from input that did NOT survive φ
    { info := { gw ∈ d.info | gw ∉ result.info }
      labels := result.labels }

/--
Conjunction: sequential update. Labels accumulate across both conjuncts.
-/
def conj (φ ψ : PUpdate W E) : PUpdate W E :=
  λ d => ψ (φ d)

/--
Disjunction: union of positive updates with label floating.

Labels from the first disjunct are available to the second, simulating
PIP's label floating (X ≡ φ is tautological and floats freely).
Both disjuncts evaluate from the same input info state, but the second
disjunct inherits labels from the first.

This is the key operator for bathroom sentences:
  "Either there's no bathroom, or it's upstairs."
The label for "bathroom" is registered in the first disjunct (under
negation) and floated to the second for DEF_α resolution.

Note: both disjuncts evaluate from the same input info state `d.info`.
This is what distinguishes disjunction from conjunction (sequential
update) and correctly predicts that "There's no bathroom. It's upstairs."
fails (conjunction) while "Either...or..." succeeds (disjunction).
-/
def disj (φ ψ : PUpdate W E) : PUpdate W E :=
  λ d =>
    let left := φ d
    -- Second disjunct inherits labels from first (PIP label floating)
    let right := ψ { d with labels := left.labels }
    { info := left.info ∪ right.info
      labels := right.labels }


-- ============================================================
-- Existential Quantification
-- ============================================================

/--
Labeled existential: ∃^α x. φ

The core mechanism for description-based anaphora:
1. For each (g, w) in the input, and each entity e in the domain,
   add (g[x ↦ e], w) to the extended context
2. Register label α with the description ⟨x, bodyPred⟩
3. Evaluate the body φ in the extended context

The label α persists in the discourse state, surviving subsequent
negation and modal operators. This is what enables:
- Modal subordination: "A wolf might come in. It would eat you."
- Bathroom sentences: "Either there's no bathroom, or it's upstairs."
- Paycheck pronouns: "John spent his paycheck. Bill saved it."
-/
def existsLabeled (α : FLabel) (v : IVar) (domain : Set E)
    (bodyPred : ICDRTAssignment W E → W → Bool)
    (body : PUpdate W E) : PUpdate W E :=
  λ d =>
    let extended : IContext W E :=
      { gw | ∃ g₀ e, (g₀, gw.2) ∈ d.info ∧
                      e ∈ domain ∧
                      gw.1 = g₀.updateIndiv v (.some e) }
    let desc : Description W E := ⟨v, bodyPred⟩
    let d' : Discourse W E := ⟨extended, d.labels.register α desc⟩
    body d'

/--
Unlabeled existential: standard ∃x. φ without descriptive tracking.
-/
def exists_ (v : IVar) (domain : Set E)
    (body : PUpdate W E) : PUpdate W E :=
  λ d =>
    let extended : IContext W E :=
      { gw | ∃ g₀ e, (g₀, gw.2) ∈ d.info ∧
                      e ∈ domain ∧
                      gw.1 = g₀.updateIndiv v (.some e) }
    body { d with info := extended }

/--
Universal quantification: ∀x. φ ≡ ¬∃x.¬φ
-/
def forall_ (v : IVar) (domain : Set E)
    (body : PUpdate W E) : PUpdate W E :=
  negation (exists_ v domain (negation body))


-- ============================================================
-- Modal Operators
-- ============================================================

/--
PIP accessibility relation: decidable relation between worlds.
-/
abbrev PAccessRel (W : Type*) := W → W → Bool

/--
Modal context expansion: adds accessible-world pairs to the context.

Before evaluating the body of a modal, the context must include
assignment-world pairs at accessible worlds. This mirrors the standard
dynamic semantics treatment where modals shift the evaluation world
(Veltman 1996, Frank 1997, Brasoveanu 2010): predicates inside the
modal body are evaluated at accessible worlds, not just the evaluation world.

Without expansion, a context filtered to a single evaluation world
would produce no accessible-world pairs for universal modals to check,
making must/would vacuously satisfied and losing the modal subordination
mechanism.
-/
def modalExpand (c : IContext W E) (access : PAccessRel W) : IContext W E :=
  c ∪ { gw | ∃ w₀, (gw.1, w₀) ∈ c ∧ access w₀ gw.2 = true }

/-- Modal expansion includes all original pairs. -/
theorem modalExpand_superset (c : IContext W E) (access : PAccessRel W) :
    c ⊆ modalExpand c access := by
  intro x hx; left; exact hx

/-- Modal expansion adds accessible-world pairs. -/
theorem modalExpand_adds_accessible (c : IContext W E) (access : PAccessRel W)
    (g : ICDRTAssignment W E) (w₀ w₁ : W)
    (hc : (g, w₀) ∈ c) (hacc : access w₀ w₁ = true) :
    (g, w₁) ∈ modalExpand c access := by
  right; exact ⟨w₀, hc, hacc⟩

/--
Modal necessity (must): universal quantification over accessible worlds.

  must_R(φ) holds at (g, w₀) iff for all w₁ accessible from w₀,
  (g, w₁) survives φ.

The body is evaluated on an **expanded** context (via `modalExpand`) that
includes pairs at all accessible worlds, mirroring PIP's world-subscripted
predicates P_{w₁} (Veltman 1996, Frank 1997).

The world variable is **external**: quantified by the modal from outside
the scope of any indefinites in φ. The individual variables introduced
by existentials inside φ are **local**.

This external/local distinction is what makes PIP's treatment of modal
subordination work: "A wolf might come in" introduces the wolf (local)
under the modal's world quantification (external). The wolf's descriptive
content (via the label) is accessible in subsequent discourse.
-/
def must (access : PAccessRel W) (allWorlds : List W)
    (body : PUpdate W E) : PUpdate W E :=
  λ d =>
    let bodyResult := body { d with info := modalExpand d.info access }
    let result : IContext W E :=
      { gw ∈ d.info |
        ∀ w₁ ∈ allWorlds, access gw.2 w₁ = true → (gw.1, w₁) ∈ bodyResult.info }
    -- Labels from the body propagate outward
    { info := result, labels := bodyResult.labels }

/--
Modal possibility (might): existential quantification over accessible worlds.

  might_R(φ) holds at (g, w₀) iff there exists w₁ accessible from w₀
  such that (g, w₁) survives φ.

Like `must`, the body is evaluated on an expanded context (via `modalExpand`)
and the world variable is external.
-/
def might (access : PAccessRel W) (allWorlds : List W)
    (body : PUpdate W E) : PUpdate W E :=
  λ d =>
    let bodyResult := body { d with info := modalExpand d.info access }
    let result : IContext W E :=
      { gw ∈ d.info |
        ∃ w₁ ∈ allWorlds, access gw.2 w₁ = true ∧ (gw.1, w₁) ∈ bodyResult.info }
    { info := result, labels := bodyResult.labels }

/--
Modal subordination operator (would): universal quantification over
the same accessibility relation as the prior modal.

In the paper (example 49, p. 9:23), "It would eat you first" is
analyzed as MUST^{a₀}_{w*}([w₁]; DEF_X{x}; EAT_{w₁}{x, you}),
where a₀ is the same accessibility relation from "might" in the
preceding sentence. So `would` = `must` with the inherited modal base.
-/
def would (access : PAccessRel W) (allWorlds : List W)
    (body : PUpdate W E) : PUpdate W E :=
  must access allWorlds body


-- ============================================================
-- Key Properties
-- ============================================================

section Properties

variable (d : Discourse W E) (α : FLabel)

/--
Labels survive negation.

This is the fundamental property enabling cross-negation anaphora
(bathroom sentences). Negation affects the info state but the label
registry from the body is preserved.
-/
theorem labels_survive_negation (φ : PUpdate W E) (desc : Description W E)
    (h : (φ d).labels.lookup α = some desc) :
    (negation φ d).labels.lookup α = some desc := h

/--
Labels survive conjunction (left-to-right).

Labels registered by the first conjunct are available to the second.
-/
theorem labels_survive_conj_left (φ ψ : PUpdate W E) (desc : Description W E)
    (_h : (φ d).labels.lookup α = some desc)
    (h_pres : (ψ (φ d)).labels.lookup α = some desc) :
    (conj φ ψ d).labels.lookup α = some desc := h_pres

/--
Labels survive modal operators.

Labels registered inside a modal scope propagate to the outer
discourse state. This is what enables modal subordination.
-/
theorem labels_survive_must (access : PAccessRel W) (allWorlds : List W)
    (body : PUpdate W E) (desc : Description W E)
    (h : (body { d with info := modalExpand d.info access }).labels.lookup α = some desc) :
    (must access allWorlds body d).labels.lookup α = some desc := h

theorem labels_survive_might (access : PAccessRel W) (allWorlds : List W)
    (body : PUpdate W E) (desc : Description W E)
    (h : (body { d with info := modalExpand d.info access }).labels.lookup α = some desc) :
    (might access allWorlds body d).labels.lookup α = some desc := h

/--
Labels from the first disjunct are available in the output.

In PIP, X ≡ φ is tautological and floats freely across all operators.
Our encoding simulates this by flowing labels from the first disjunct
through the second. If the second disjunct preserves labels (as all
PIP operators do), the output contains all labels from both disjuncts.
-/
theorem labels_survive_disj (φ ψ : PUpdate W E) (desc : Description W E)
    (_h_left : (φ d).labels.lookup α = some desc)
    (h_pres : (ψ { d with labels := (φ d).labels }).labels.lookup α = some desc) :
    (disj φ ψ d).labels.lookup α = some desc := h_pres

end Properties


-- ============================================================
-- Binding Mode Classification
-- ============================================================

/--
Under a modal, the world variable is external and individual
variables introduced by existentials are local.

  might(∃^α x. wolf(x) ∧ come-in(x))
       ↑ external world    ↑ local x

This classification falls out from the scoping structure:
- The modal quantifies over worlds from outside
- The existential binds x from inside
-/
def modalBindings (worldVar individualVar : IVar) (α : FLabel) :
    List BoundVar :=
  [ ⟨worldVar, .external, none⟩,
    ⟨individualVar, .local, some α⟩ ]

/--
Under a quantifier, both the bound variable and restrictor
variable are local.

  every(∃x. farmer(x))(∃y. donkey(y) ∧ owns(x,y) → beats(x,y))
       ↑ local x        ↑ local y
-/
def quantifierBindings (boundVar restrictorVar : IVar) :
    List BoundVar :=
  [ ⟨boundVar, .local, none⟩,
    ⟨restrictorVar, .local, none⟩ ]


end Semantics.Dynamic.PIP
