import Linglib.Theories.Discourse.DiscourseRef
import Linglib.Theories.Discourse.Connectives.Defs
import Linglib.Theories.Discourse.Effects.HasFiberedLookup
import Mathlib.Data.Set.Basic

/-!
# Intensional Dynamic Semantics — Generic Substrate

@cite{muskens-1996} @cite{stone-1999} @cite{brasoveanu-2006} @cite{hofmann-2025}

Generic infrastructure for dynamic semantics built over `ICDRTAssignment`
(individual drefs as `IVar → W → Entity E` plus propositional drefs as
`PVar → Set W`). This is a layer above `Dynamic/Core/DiscourseRef.lean`
(which owns the assignment type) and below paper-specific theories such as
@cite{hofmann-2025} (whose paper apparatus lives in
`Phenomena/Anaphora/Studies/Hofmann2025.lean`).

## Main definitions

| Layer | Names |
|-------|-------|
| Information state | `IContext` (set of assignment-world pairs), `DynProp` (context transformer) |
| Update relations | `ICDRTUpdate`, `ICDRTUpdate.{seq, idUp, toDynProp}` |
| Variable updates | `propVarUp`, `indivVarUp`, `multiVarUp`, `relVarUp` |
| Dynamic conditions | `dynInclusion`, `dynIdentity`, `dynComplement`, `isComplement`, `dynUnion` |
| Predication | `dynPred`, `localEntailment` |
| Veridicality typology | `veridicalIndiv/Prop`, `counterfactualIndiv/Prop`, `hypotheticalIndiv/Prop`, `accessible`, `subsetReq` |
| Static-to-dynamic bridge | `fiberDRS`, `toDynProp_eq_lift_fiberDRS` |

## Architecture

```
ICDRTUpdate W E ──fiberDRS──→ DRS (ICDRTAssignment W E × W) ──lift──→ CCP (... × W)
       ‖                              ‖                                    ‖
   DRS (Assign)              DRS (Assign × World)                 DynProp W E
       │                              │                                    │
    seq = dseq              dseq (fiber level)                    CCP.seq
```

The factorization `toDynProp = lift ∘ fiberDRS` separates two concerns:
- `fiberDRS`: embed assignment-only relations into pair relations (passive worlds)
- `lift`: convert relational meanings to set-transformer meanings

`toDynProp` is always distributive (corollary of `lift_isDistributive`).
This is the algebraic content of @cite{hofmann-2025}'s observation that
ICDRT-style negation via propositional dref complementation stays
distributive — unlike test-based dynamic negation that inspects whole
states.
-/

namespace Semantics.Dynamic.Core

open Core (Assignment)
open Core.DynProp

variable {W E : Type*}


-- ════════════════════════════════════════════════════════════════
-- § 1. Information States and Context Transformers
-- ════════════════════════════════════════════════════════════════

namespace ICDRTAssignment

/-- Notation for individual variable lookup -/
notation g "⟦" v "⟧ᵢ" => ICDRTAssignment.indiv g v

/-- Notation for propositional variable lookup -/
notation g "⟦" p "⟧ₚ" => ICDRTAssignment.prop g p

end ICDRTAssignment

/-- Set of assignment-world pairs (information state in flat update).

Kept as `abbrev` so it inherits `Set α`'s `Membership`,
`EmptyCollection`, `HasSubset`, `Union`, `Inter`, and `Singleton`
instances (and the corresponding `Set` API) directly. -/
abbrev IContext (W : Type*) (E : Type*) := Set (ICDRTAssignment W E × W)

namespace IContext

/-- The trivial context (all possibilities) -/
def univ : IContext W E := Set.univ

/-- The absurd context (no possibilities) -/
def empty : IContext W E := ∅

/-- Context is consistent (non-empty) -/
def consistent (c : IContext W E) : Prop := c.Nonempty

/-- Worlds in the context (projection) -/
def worlds (c : IContext W E) : Set W := { w | ∃ g, (g, w) ∈ c }

/-- Update with a world-predicate -/
def update (c : IContext W E) (p : W → Prop) : IContext W E :=
  { gw ∈ c | p gw.2 }

/-- Update with an assignment-world predicate -/
def updateFull (c : IContext W E) (p : ICDRTAssignment W E → W → Prop) : IContext W E :=
  { gw ∈ c | p gw.1 gw.2 }

notation:max c "⟦" p "⟧" => IContext.update c p

end IContext

/-- Context-to-context transformer (sentence denotation). -/
def DynProp (W : Type*) (E : Type*) := IContext W E → IContext W E

namespace DynProp

/-- Identity (says nothing). Aliases `CCP.id`. -/
def id : DynProp W E := λ c => c

/-- Absurd (contradiction). Aliases `CCP.absurd`. -/
def absurd : DynProp W E := λ _ => ∅

/-- Lift a classical proposition to a context filter. -/
def ofProp (p : W → Prop) : DynProp W E := λ c => c.update p

end DynProp


-- ════════════════════════════════════════════════════════════════
-- § 2. Updates as Static Relations (after @cite{muskens-1996})
-- ════════════════════════════════════════════════════════════════

/-- Static update relation between input and output assignments.

Following @cite{muskens-1996}'s Compositional DRT, dynamic updates are
relations between assignments rather than operations on sets of
assignment-world pairs. The lift to context transformers is done by
`toDynProp` below. -/
def ICDRTUpdate (W : Type*) (E : Type*) :=
  ICDRTAssignment W E → ICDRTAssignment W E → Prop

namespace ICDRTUpdate

/-- Sequencing (`;`): relational composition.
    `(D₁ ; D₂)(i)(j) ↔ ∃k, D₁(i)(k) ∧ D₂(k)(j)` -/
def seq (D₁ D₂ : ICDRTUpdate W E) : ICDRTUpdate W E :=
  λ i j => ∃ k, D₁ i k ∧ D₂ k j

infixl:60 " ⨟ " => seq

/-- Identity update: output equals input. -/
def idUp : ICDRTUpdate W E := λ i j => i = j

/-- An update is successful from `i` if some output `j` exists. -/
def successful (D : ICDRTUpdate W E) (i : ICDRTAssignment W E) : Prop :=
  ∃ j, D i j

/-- Lift a static update relation to a context update on information states. -/
def toDynProp (D : ICDRTUpdate W E) : DynProp W E :=
  λ c => { p | ∃ i, (i, p.2) ∈ c ∧ D i p.1 }

/-- Identity update lifts to identity on contexts. -/
theorem idUp_toDynProp (c : IContext W E) :
    ICDRTUpdate.idUp.toDynProp c = c :=
  Set.ext (λ ⟨j, _⟩ =>
    ⟨λ ⟨_, hic, rfl⟩ => hic, λ hjc => ⟨j, hjc, rfl⟩⟩)

/-- Sequential composition lifts to function composition on contexts. -/
theorem seq_toDynProp (D₁ D₂ : ICDRTUpdate W E) (c : IContext W E) :
    (seq D₁ D₂).toDynProp c = D₂.toDynProp (D₁.toDynProp c) :=
  Set.ext (λ ⟨_, _⟩ =>
    ⟨λ ⟨i, hic, k, h1, h2⟩ => ⟨k, ⟨i, hic, h1⟩, h2⟩,
     λ ⟨k, ⟨i, hic, h1⟩, h2⟩ => ⟨i, hic, k, h1, h2⟩⟩)

end ICDRTUpdate


-- ════════════════════════════════════════════════════════════════
-- § 3. Variable Updates
-- ════════════════════════════════════════════════════════════════

/-- Propositional variable update: `j` differs from `i` at most in the value of `p`.
`i[p]j` -/
def propVarUp (p : PVar) (i j : ICDRTAssignment W E) : Prop :=
  (∀ q : PVar, q ≠ p → j.prop q = i.prop q) ∧
  (∀ v : IVar, j.indiv v = i.indiv v)

/-- Individual variable update: `j` differs from `i` at most in the value of `v`.
`i[v]j` -/
def indivVarUp (v : IVar) (i j : ICDRTAssignment W E) : Prop :=
  (∀ p : PVar, j.prop p = i.prop p) ∧
  (∀ u : IVar, u ≠ v → j.indiv u = i.indiv u)

/-- Multi-variable update: `j` differs from `i` at most in the listed prop/indiv vars. -/
def multiVarUp (ps : List PVar) (vs : List IVar)
    (i j : ICDRTAssignment W E) : Prop :=
  (∀ p : PVar, p ∉ ps → j.prop p = i.prop p) ∧
  (∀ v : IVar, v ∉ vs → j.indiv v = i.indiv v)

/-- Relative variable update: `i[φ : v]j`.

`j` differs from `i` at most in `v`, AND for every world `w`,
`φ(j)(w) ↔ v(j)(w) ≠ ⋆`.

The biconditional (not just implication) is crucial: it ensures that
`v` has a referent in all and only the φ-worlds, preventing drefs under
negation from having global referents. Following @cite{hofmann-2025}
Definition 25. -/
def relVarUp (φ : PVar) (v : IVar) (i j : ICDRTAssignment W E) : Prop :=
  indivVarUp v i j ∧
  (∀ w : W, w ∈ j.prop φ ↔ j.indiv v w ≠ .star)


-- ════════════════════════════════════════════════════════════════
-- § 4. Dynamic Conditions on Propositional Drefs
-- ════════════════════════════════════════════════════════════════

/-- Dynamic inclusion: `φ₁(i) ⊆ φ₂(i)`. -/
def dynInclusion (φ₁ φ₂ : PVar) (i : ICDRTAssignment W E) : Prop :=
  i.prop φ₁ ⊆ i.prop φ₂

notation:50 φ₁ " ∈ₚ " φ₂ " at " i => dynInclusion φ₁ φ₂ i

/-- Dynamic identity: `α(i) = β(i)`. -/
def dynIdentity (α β : PVar) (i : ICDRTAssignment W E) : Prop :=
  i.prop α = i.prop β

/-- Dynamic complementation: set-theoretic complement of a propositional dref. -/
def dynComplement (φ : PVar) (i : ICDRTAssignment W E) : Set W :=
  (i.prop φ)ᶜ

/-- Condition: `φ₁` is the complement of `φ₂` at state `i`.
The negation condition `φ₁ ≡ φ̄₂`. -/
def isComplement (φ₁ φ₂ : PVar) (i : ICDRTAssignment W E) : Prop :=
  i.prop φ₁ = (i.prop φ₂)ᶜ

/-- Dynamic union: `φ₁(i) ∪ φ₂(i)`. -/
def dynUnion (φ₁ φ₂ : PVar) (i : ICDRTAssignment W E) : Set W :=
  i.prop φ₁ ∪ i.prop φ₂


-- ════════════════════════════════════════════════════════════════
-- § 5. Predication and Local Entailment
-- ════════════════════════════════════════════════════════════════

/-- Dynamic predication: `R_φ(v)`.

A unary predicate `R` interpreted relative to a propositional dref `φ`
(the local context):

`R_φ(v) := λi. ∀w.(φ(i)(w) → R(v(i)(w))(w))`

Holds when the predicate `R` applies to `v`'s referent in every world
of the local context `φ`. The universal falsifier ⋆ never satisfies
`R`, so a `⋆`-valued referent in any φ-world makes `dynPred` fail. -/
def dynPred (R : E → W → Prop) (φ : PVar) (v : IVar)
    (i : ICDRTAssignment W E) : Prop :=
  ∀ w ∈ i.prop φ,
    match i.indiv v w with
    | .some e => R e w
    | .star => False

/-- Local contextual entailment: `v` has a defined referent throughout `φ(i)`.

`∀w.(φ(i)(w) → v(i)(w) ≠ ⋆_e)`

A precondition for anaphora to `v` resolved in local context `φ`. -/
def localEntailment (φ : PVar) (v : IVar)
    (i : ICDRTAssignment W E) : Prop :=
  ∀ w ∈ i.prop φ, i.indiv v w ≠ .star

/-- Predication entails existence: a successful predication of `R` to `v`
implies `v(i)(w) ≠ ⋆`. -/
theorem pred_entails_existence (v : IVar) (i : ICDRTAssignment W E)
    (w : W) (e : E) (hv : i.indiv v w = .some e) :
    i.indiv v w ≠ .star := by
  rw [hv]; exact fun h => nomatch h


-- ════════════════════════════════════════════════════════════════
-- § 6. Veridicality Typology
-- ════════════════════════════════════════════════════════════════

/-- Veridical individual dref: `v` has a referent in all `φ_DC`-worlds. -/
def veridicalIndiv (φ_DC : PVar) (v : IVar)
    (i : ICDRTAssignment W E) : Prop :=
  ∀ w ∈ i.prop φ_DC, i.indiv v w ≠ .star

/-- Veridical propositional dref: `φ_DC(i) ⊆ δ(i)`. -/
def veridicalProp (φ_DC : PVar) (δ : PVar)
    (i : ICDRTAssignment W E) : Prop :=
  i.prop φ_DC ⊆ i.prop δ

/-- Counterfactual individual dref: `v` maps to `⋆` in all `φ_DC`-worlds. -/
def counterfactualIndiv (φ_DC : PVar) (v : IVar)
    (i : ICDRTAssignment W E) : Prop :=
  ∀ w ∈ i.prop φ_DC, i.indiv v w = .star

/-- Counterfactual propositional dref: `φ_DC(i) ∩ δ(i) = ∅`. -/
def counterfactualProp (φ_DC : PVar) (δ : PVar)
    (i : ICDRTAssignment W E) : Prop :=
  i.prop φ_DC ∩ i.prop δ = ∅

/-- Hypothetical individual dref: neither veridical nor counterfactual. -/
def hypotheticalIndiv (φ_DC : PVar) (v : IVar)
    (i : ICDRTAssignment W E) : Prop :=
  ¬veridicalIndiv φ_DC v i ∧ ¬counterfactualIndiv φ_DC v i

/-- Hypothetical propositional dref: neither veridical nor counterfactual. -/
def hypotheticalProp (φ_DC : PVar) (δ : PVar)
    (i : ICDRTAssignment W E) : Prop :=
  ¬veridicalProp φ_DC δ i ∧ ¬counterfactualProp φ_DC δ i

/-- Accessibility: `v` is accessible at the anaphor site `φ_anaphor` iff
it is locally entailed there and the discourse is consistent. -/
def accessible (φ_anaphor : PVar) (v : IVar)
    (φ_DC : PVar) (i : ICDRTAssignment W E) : Prop :=
  localEntailment φ_anaphor v i ∧ (i.prop φ_DC).Nonempty

/-- Subset requirement: indefinite at `φ_antecedent` can antecede pronoun at
`φ_anaphor` only when `φ_anaphor(i) ⊆ φ_antecedent(i)`. -/
def subsetReq (φ_anaphor φ_antecedent : PVar)
    (i : ICDRTAssignment W E) : Prop :=
  i.prop φ_anaphor ⊆ i.prop φ_antecedent


-- ════════════════════════════════════════════════════════════════
-- § 7. Multi-Agent Discourse Contexts
-- ════════════════════════════════════════════════════════════════

/-- Generic declarative-assertion subset condition: `φ_DC(j) ⊆ φ(j)`.

Definitionally identical to `dynInclusion φ_DC φ j`; kept as a
separate name because the speech-act literature reads it as
"the speaker's commitment set is updated to a subset of the
asserted content". -/
def decCondition (φ_DC : PVar) (φ : PVar) (j : ICDRTAssignment W E) : Prop :=
  j.prop φ_DC ⊆ j.prop φ

/-- A multi-agent discourse context: a current discourse state plus an
assignment from interlocutors to commitment-set propositional variables.

Each interlocutor `x` has their own commitment-set dref `dcVar x`. This
is the multi-agent generalization of single-state dynamic semantics —
distinct interlocutors can carry contradictory commitments simultaneously
without making the discourse inconsistent. -/
structure DiscContext (W : Type*) (E : Type*) (Speaker : Type*) where
  /-- Current discourse state -/
  state : ICDRTAssignment W E
  /-- Map from interlocutors to their commitment-set propositional variables -/
  dcVar : Speaker → PVar

namespace DiscContext

/-- Discourse consistency: every interlocutor's commitment set is nonempty.
`∀x ∈ INT, φ_{DC_x}(i) ≠ ∅` -/
def consistent {Speaker : Type*} (c : DiscContext W E Speaker) : Prop :=
  ∀ x : Speaker, (c.state.prop (c.dcVar x)).Nonempty

/-- An update `D` is *successful* in context `C` iff some output assignment
exists. -/
def updateSuccessful {Speaker : Type*} (c : DiscContext W E Speaker)
    (D : ICDRTUpdate W E) : Prop :=
  ∃ j, D c.state j

/-- An update is *acceptable* iff it is successful AND leaves all commitment
sets nonempty (preserves discourse consistency). -/
def updateAcceptable {Speaker : Type*} (c : DiscContext W E Speaker)
    (D : ICDRTUpdate W E) : Prop :=
  ∃ j, D c.state j ∧ ∀ x : Speaker, (j.prop (c.dcVar x)).Nonempty

/-- Null assignment: every propositional dref maps to all worlds; every
individual dref maps to ⋆ in every world. The "no information yet" state. -/
def nullAssignment : ICDRTAssignment W E where
  prop := λ _ => Set.univ
  indiv := λ _ _ => .star

/-- Initial discourse context: null assignment, every commitment set
equal to the full set of worlds. -/
def initialContext {Speaker : Type*} (dcVar : Speaker → PVar) :
    DiscContext W E Speaker where
  state := nullAssignment
  dcVar := dcVar

/-- The initial context is always consistent. -/
theorem initialContext_consistent [Nonempty W]
    {Speaker : Type*} {dcVar : Speaker → PVar} :
    (initialContext dcVar : DiscContext W E Speaker).consistent := by
  intro _; exact Set.univ_nonempty

end DiscContext


-- ════════════════════════════════════════════════════════════════
-- § 8. Pragmatic and Propositional Maximization
-- ════════════════════════════════════════════════════════════════

/-- Pragmatic maximization for commitment sets.

Output `j` is pragmatically privileged when no other possible output `h`
assigns a proper superset to any interlocutor's commitment-set dref:

`max_DC(D)(i)(j) := D(i)(j) ∧ ∀h x. D(i)(h) → ¬(φ_{DC_x}(j) ⊊ φ_{DC_x}(h))`

A formal articulation of the Gricean Quantity maxim: speakers commit to
the strongest claim supported by the evidence. -/
def pragMaxDC {Speaker : Type*} (dcVar : Speaker → PVar) (D : ICDRTUpdate W E)
    (i j : ICDRTAssignment W E) : Prop :=
  D i j ∧ ∀ h, D i h → ∀ x : Speaker, ¬(j.prop (dcVar x) ⊂ h.prop (dcVar x))

/-- Propositional maximization: `max_φ(D)`.

Restricts outputs to those where propositional dref `φ` is maximal — no
other successful output `k` assigns a proper superset to `φ`:

`max_φ(D)(i)(j) := D(i)(j) ∧ ∀k. D(i)(k) → ¬(φ(j) ⊊ φ(k))`

Used to ensure local contexts are as wide as the truth conditions allow,
e.g. for the inner content of a negated existential. -/
def propMaxOp (φ : PVar) (D : ICDRTUpdate W E)
    (i j : ICDRTAssignment W E) : Prop :=
  D i j ∧ ∀ k, D i k → ¬(j.prop φ ⊂ k.prop φ)

/-- Doxastic accessibility condition for an attitude verb's local context.

`believe_φ'(δ^v) ≡ [φ' | DOX(δ,φ) ⊆ φ']`

`dox j` returns the set of worlds compatible with the agent's beliefs
at assignment `j`; the condition asserts that `φ'` contains them. -/
def believeCondition (φ_belief : PVar) (dox : ICDRTAssignment W E → Set W)
    (j : ICDRTAssignment W E) : Prop :=
  dox j ⊆ j.prop φ_belief


-- ════════════════════════════════════════════════════════════════
-- § 9. Structural Theorems
-- ════════════════════════════════════════════════════════════════

/-- Local entailment follows from relative variable update. The biconditional
in `relVarUp` (Definition 25ii) directly yields local contextual entailment
at the output assignment. -/
theorem relVarUp_implies_localEntailment (φ : PVar) (v : IVar)
    (i j : ICDRTAssignment W E) (h : relVarUp φ v i j) :
    localEntailment φ v j :=
  λ w hw => (h.2 w).mp hw

/-- Veridical dref + DC-subsumed anaphor context + consistency → accessibility. -/
theorem veridical_implies_accessible (φ_DC φ_anaphor : PVar) (v : IVar)
    (i : ICDRTAssignment W E)
    (h_veridical : veridicalIndiv φ_DC v i)
    (h_subset : i.prop φ_anaphor ⊆ i.prop φ_DC)
    (h_consistent : (i.prop φ_DC).Nonempty) :
    accessible φ_anaphor v φ_DC i :=
  ⟨λ w hw => h_veridical w (h_subset hw), h_consistent⟩

/-- Counterfactual dref in veridical anaphor context → inaccessibility. -/
theorem counterfactual_veridical_fails (φ_DC φ_anaphor φ_antecedent : PVar)
    (v : IVar) (i : ICDRTAssignment W E)
    (h_cf : counterfactualIndiv φ_DC v i)
    (h_dc_veridical : i.prop φ_DC ⊆ i.prop φ_anaphor)
    (h_subset : subsetReq φ_anaphor φ_antecedent i)
    (h_rel : ∀ w, w ∈ i.prop φ_antecedent ↔ i.indiv v w ≠ .star) :
    ¬accessible φ_anaphor v φ_DC i := by
  intro ⟨_h_ent, h_ne⟩
  obtain ⟨w, hw⟩ := h_ne
  have h_in_anaphor := h_dc_veridical hw
  have h_in_ante := h_subset h_in_anaphor
  have h_ne_star := (h_rel w).mp h_in_ante
  exact h_ne_star (h_cf w hw)

/-- Double complementation collapses: `φ₁ ≡ φ̄₂` and `φ₃ ≡ φ̄₁` give `φ₃ = φ₂`. -/
theorem double_complement_eq (φ₁ φ₂ φ₃ : PVar) (i : ICDRTAssignment W E)
    (h1 : isComplement φ₁ φ₂ i)
    (h2 : isComplement φ₃ φ₁ i) :
    i.prop φ₃ = i.prop φ₂ := by
  rw [isComplement] at h1 h2
  rw [h2, h1, compl_compl]

/-- Disjunction enables anaphora across disjuncts: if `v` is defined in all
`φ₃`-worlds and the anaphor's local context is contained in `φ₃`, then `v`
is locally entailed at the anaphor site. -/
theorem disjunction_enables_anaphora (φ₃ φ_a : PVar) (v : IVar)
    (i : ICDRTAssignment W E)
    (h_sub : i.prop φ_a ⊆ i.prop φ₃)
    (h_rel : ∀ w, w ∈ i.prop φ₃ → i.indiv v w ≠ .star) :
    localEntailment φ_a v i :=
  λ w hw => h_rel w (h_sub hw)

/-- Veridicality trichotomy: every individual dref is veridical, counterfactual,
or hypothetical relative to any speaker. -/
theorem veridicality_trichotomy (φ_DC : PVar) (v : IVar)
    (i : ICDRTAssignment W E) :
    veridicalIndiv φ_DC v i ∨ counterfactualIndiv φ_DC v i ∨ hypotheticalIndiv φ_DC v i := by
  by_cases hv : veridicalIndiv φ_DC v i
  · exact Or.inl hv
  · by_cases hc : counterfactualIndiv φ_DC v i
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr ⟨hv, hc⟩)

/-- Veridical and counterfactual are incompatible given a nonempty DC. -/
theorem veridical_counterfactual_exclusive (φ_DC : PVar) (v : IVar)
    (i : ICDRTAssignment W E)
    (hv : veridicalIndiv φ_DC v i) (hc : counterfactualIndiv φ_DC v i) :
    ¬(i.prop φ_DC).Nonempty :=
  λ ⟨w, hw⟩ => absurd (hc w hw) (hv w hw)

/-- The universal falsifier blocks dynamic predication: if `v` maps to `⋆` at
some `w ∈ φ`, then `R_φ(v)` fails. -/
theorem star_blocks_dynPred (R : E → W → Prop) (φ : PVar) (v : IVar)
    (i : ICDRTAssignment W E) (w : W)
    (hw : w ∈ i.prop φ) (hstar : i.indiv v w = .star)
    (hpred : dynPred R φ v i) : False := by
  have := hpred w hw; rw [hstar] at this; exact this

/-- Subset condition + complementation derive counterfactuality of the
inner content. The shape `DC ⊆ φ_outer ∧ φ_outer = φ̄_inner ⟹ DC ∩ φ_inner = ∅`
is the core algebraic move that turns negation into commitment-set
counterfactuality (the recipe used by @cite{hofmann-2025}'s analysis of
"there isn't a bathroom"). -/
theorem dec_complement_counterfactual (φ_DC φ_outer φ_inner : PVar)
    (i : ICDRTAssignment W E)
    (h_comp : isComplement φ_outer φ_inner i)
    (h_dec : dynInclusion φ_DC φ_outer i) :
    counterfactualProp φ_DC φ_inner i := by
  unfold counterfactualProp isComplement dynInclusion at *
  rw [h_comp] at h_dec
  ext w
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hw_dc, hw_inner⟩
  exact h_dec hw_dc hw_inner


-- ════════════════════════════════════════════════════════════════
-- § 10. Fiberwise Lift to CCP
-- ════════════════════════════════════════════════════════════════

/-- Embed an assignment-only relation into a pair relation with passive worlds.

`fiberDRS D (i, w) (j, w') ↔ w = w' ∧ D i j`

ICDRT updates operate on assignments only and worlds are inert fibers.
`fiberDRS` makes this structure explicit at the type level of
`DRS (ICDRTAssignment W E × W)`. -/
def fiberDRS (D : ICDRTUpdate W E) : DRS (ICDRTAssignment W E × W) :=
  λ ⟨i, w⟩ ⟨j, w'⟩ => w = w' ∧ D i j

/-- `toDynProp = lift ∘ fiberDRS`: the static-to-dynamic bridge factors
through fiberwise embedding followed by relational image. -/
theorem toDynProp_eq_lift_fiberDRS (D : ICDRTUpdate W E) :
    D.toDynProp = lift (fiberDRS D) := by
  funext σ
  apply Set.ext; intro ⟨j, w⟩
  simp only [ICDRTUpdate.toDynProp, lift, fiberDRS, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, hic, hD⟩
    exact ⟨⟨i, w⟩, hic, rfl, hD⟩
  · rintro ⟨⟨i, _⟩, hiw, rfl, hD⟩
    exact ⟨i, hiw, hD⟩

/-- `fiberDRS` preserves sequential composition. -/
theorem fiberDRS_seq (D₁ D₂ : ICDRTUpdate W E) :
    fiberDRS (ICDRTUpdate.seq D₁ D₂) = dseq (fiberDRS D₁) (fiberDRS D₂) := by
  funext p q; cases p; cases q
  simp only [fiberDRS, ICDRTUpdate.seq, dseq, eq_iff_iff]
  constructor
  · rintro ⟨rfl, k, h1, h2⟩
    exact ⟨⟨k, _⟩, ⟨rfl, h1⟩, ⟨rfl, h2⟩⟩
  · rintro ⟨⟨k, _⟩, ⟨rfl, h1⟩, ⟨rfl, h2⟩⟩
    exact ⟨rfl, k, h1, h2⟩

/-- `fiberDRS` preserves identity. -/
theorem fiberDRS_idUp :
    fiberDRS (ICDRTUpdate.idUp : ICDRTUpdate W E) = λ p q => p = q := by
  funext p q; cases p; cases q
  simp only [fiberDRS, ICDRTUpdate.idUp, eq_iff_iff, Prod.mk.injEq]
  exact ⟨λ ⟨h1, h2⟩ => ⟨h2, h1⟩, λ ⟨h1, h2⟩ => ⟨h2, h1⟩⟩

/-- `fiberDRS` is a monoid homomorphism `(ICDRTUpdate, seq, idUp) → (DRS, dseq, id)`. -/
theorem fiberDRS_homomorphism :
    (∀ (D₁ D₂ : ICDRTUpdate W E),
      fiberDRS (ICDRTUpdate.seq D₁ D₂) = dseq (fiberDRS D₁) (fiberDRS D₂)) ∧
    fiberDRS (ICDRTUpdate.idUp : ICDRTUpdate W E) = λ p q => p = q :=
  ⟨fiberDRS_seq, fiberDRS_idUp⟩


-- ════════════════════════════════════════════════════════════════
-- § 11. Distributivity, Test Eliminativity, and Round-Trip
-- ════════════════════════════════════════════════════════════════

/-- `toDynProp D` is always distributive: it processes each
assignment-world pair independently. Corollary of `lift_isDistributive`. -/
theorem toDynProp_isDistributive (D : ICDRTUpdate W E) :
    IsDistributive (D.toDynProp) := by
  rw [toDynProp_eq_lift_fiberDRS]
  exact lift_isDistributive (fiberDRS D)

/-- A test update — one that preserves the assignment — lifts to an
eliminative CCP: it can only shrink the context, never grow it. -/
theorem toDynProp_test_eliminative (C : ICDRTAssignment W E → Prop) :
    IsEliminative (ICDRTUpdate.toDynProp (λ i j => i = j ∧ C j)) := by
  intro _ ⟨_, _⟩ hjw
  obtain ⟨_, hiw, rfl, _⟩ := hjw
  exact hiw

/-- The DEC condition lifts to an eliminative CCP: assertion narrows the
context (removes worlds from the commitment set). -/
theorem toDynProp_dec_eliminative (φ_DC φ : PVar) :
    IsEliminative (ICDRTUpdate.toDynProp
      (λ i j : ICDRTAssignment W E => i = j ∧ decCondition φ_DC φ j)) :=
  toDynProp_test_eliminative _

/-- ICDRT-style negation via complementation stays distributive — unlike
test-based dynamic negation that inspects the whole input state. -/
theorem complement_update_distributive (φ_outer φ_inner : PVar) :
    IsDistributive (ICDRTUpdate.toDynProp
      (λ i j : ICDRTAssignment W E =>
        i = j ∧ isComplement φ_outer φ_inner j)) :=
  toDynProp_isDistributive _

/-- Round-trip: lowering the CCP back to a relation recovers the fiberwise
embedding. Combined with `lower_lift`, this shows no information is lost
in the `fiberDRS`/`lift` factorization. -/
theorem lower_toDynProp (D : ICDRTUpdate W E) :
    lower (D.toDynProp) = fiberDRS D := by
  rw [toDynProp_eq_lift_fiberDRS, lower_lift]

/-- `toDynProp` preserves sequential composition — algebraic derivation via
`fiberDRS_seq` + `lift_dseq`. -/
theorem toDynProp_seq_algebraic (D₁ D₂ : ICDRTUpdate W E) (c : IContext W E) :
    (ICDRTUpdate.seq D₁ D₂).toDynProp c = CCP.seq D₁.toDynProp D₂.toDynProp c := by
  conv_lhs => rw [toDynProp_eq_lift_fiberDRS, fiberDRS_seq, lift_dseq]
  conv_rhs => rw [toDynProp_eq_lift_fiberDRS D₁, toDynProp_eq_lift_fiberDRS D₂]

/-- `toDynProp` preserves identity — algebraic derivation via `fiberDRS_idUp`. -/
theorem toDynProp_id_algebraic (c : IContext W E) :
    ICDRTUpdate.idUp.toDynProp c = CCP.id c := by
  rw [toDynProp_eq_lift_fiberDRS, fiberDRS_idUp]
  apply Set.ext; intro ⟨j, w⟩
  simp only [lift, CCP.id, Set.mem_setOf_eq]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact hp
  · intro hjw; exact ⟨⟨j, w⟩, hjw, rfl⟩


-- ════════════════════════════════════════════════════════════════
-- § Dynamic.Context typeclass instances for ICDRTAssignment
-- ════════════════════════════════════════════════════════════════

/-! Register `ICDRTAssignment W E` as an instance of the abstract
`Dynamic.Context` typeclass family. With these instances, every
predicate and theorem in `Dynamic.Context` (e.g.
`counterfactual_blocks_veridical`, `multi_counterfactual_blocks_veridical`)
applies to ICDRT contexts without re-proof. -/

open Semantics.Dynamic.Context in
instance instHasIndivDrefs_ICDRT :
    HasIndivDrefs (ICDRTAssignment W E) IVar W E where
  iLookup i v w := i.indiv v w
  iVarUp v i j := indivVarUp v i j
  iVarUp_other _ _ _ u := λ ⟨_, hu⟩ hne => funext (λ _ => by rw [hu u hne])

open Semantics.Dynamic.Context in
instance instHasPropDrefs_ICDRT :
    HasPropDrefs (ICDRTAssignment W E) PVar W where
  pLookup i p := i.prop p
  pVarUp p i j := propVarUp p i j
  pVarUp_other _ _ _ q := λ ⟨hq, _⟩ hne => hq q hne

/-- The generic `Dynamic.Context.localEntailment` agrees definitionally
with the concrete `localEntailment` on ICDRT. -/
theorem localEntailment_eq_context (φ : PVar) (v : IVar)
    (i : ICDRTAssignment W E) :
    Semantics.Dynamic.Context.localEntailment (W := W) φ v i ↔
      localEntailment φ v i := Iff.rfl

/-- The generic `Dynamic.Context.veridicalIndiv` agrees definitionally
with the concrete `veridicalIndiv` on ICDRT. -/
theorem veridicalIndiv_eq_context (φ_DC : PVar) (v : IVar)
    (i : ICDRTAssignment W E) :
    Semantics.Dynamic.Context.veridicalIndiv (W := W) φ_DC v i ↔
      veridicalIndiv φ_DC v i := Iff.rfl

/-- The generic `Dynamic.Context.subsetReq` agrees definitionally with
the concrete `subsetReq` on ICDRT. -/
theorem subsetReq_eq_context (a b : PVar) (i : ICDRTAssignment W E) :
    Semantics.Dynamic.Context.subsetReq (W := W) a b i ↔
      subsetReq a b i := Iff.rfl

/-- The generic `Dynamic.Context.decCondition` agrees definitionally
with the concrete `decCondition` on ICDRT. -/
theorem decCondition_eq_context (φ_DC φ : PVar) (i : ICDRTAssignment W E) :
    Semantics.Dynamic.Context.decCondition (W := W) φ_DC φ i ↔
      decCondition φ_DC φ i := Iff.rfl

/-- Hofmann's `relVarUp` agrees with the generic
`Dynamic.Context.relVarUp` (modulo set-extensionality on the
biconditional). The cross-field operation is a *definition* over the
basic typeclass operations, not a separate axiom. -/
theorem relVarUp_eq_context (φ : PVar) (v : IVar)
    (i j : ICDRTAssignment W E) :
    relVarUp φ v i j ↔
    Semantics.Dynamic.Context.relVarUp
      (Ctx := ICDRTAssignment W E) (E := E) φ v i j := by
  refine ⟨λ ⟨hiv, hbi⟩ => ⟨hiv, ?_⟩, λ ⟨hiv, heq⟩ => ⟨hiv, ?_⟩⟩
  · ext w
    show w ∈ j.prop φ ↔
      Semantics.Dynamic.Context.HasFiberedLookup.iLookup j v w ≠ Entity.star
    exact hbi w
  · intro w
    show w ∈ j.prop φ ↔ j.indiv v w ≠ Entity.star
    have h₁ : j.prop φ =
        Semantics.Dynamic.Context.HasPropDrefs.pLookup
          (Ctx := ICDRTAssignment W E) j φ := rfl
    rw [h₁, heq]; rfl


end Semantics.Dynamic.Core
