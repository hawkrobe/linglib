import Linglib.Semantics.Dynamic.ICDRT.Defs
import Linglib.Semantics.Dynamic.Update
import Linglib.Semantics.Dynamic.Lookup
import Mathlib.Data.Set.Basic

/-!
# Intensional CDRT

[muskens-1996] [stone-1999] [brasoveanu-2006] [hofmann-2025]

ICDRT ([hofmann-2025]'s intensional extension of [muskens-1996]'s
Compositional DRT): dynamic semantics built over `ICDRTAssignment`
(individual drefs as `IVar → W → Entity E` plus propositional drefs as
`PVar → Set W`). This is a layer above `ICDRT/Defs.lean` (which owns the
carrier types) and below paper-specific theories such as [hofmann-2025]
(whose paper apparatus lives in `Studies/Hofmann2025.lean`).

## Main definitions

- `IContext`, `DynProp`: information states (sets of assignment-world
  pairs) and context transformers over them (the spine's `CCP` at ICDRT
  possibilities).
- `ICDRTUpdate`, with `seq`, `idUp`, and the lift `toUpdate`: static
  update relations between assignments, after [muskens-1996].
- `propVarUp`, `indivVarUp`, `multiVarUp`, `relVarUp`: variable updates.
- `dynInclusion`, `isComplement`: dynamic conditions on propositional drefs.
- `dynPred`, `localEntailment`: predication and local contextual entailment.
- `veridicalIndiv`, `counterfactualIndiv`, `hypotheticalIndiv`,
  `counterfactualProp`, `accessible`, `subsetReq`: the veridicality typology.
- `fiberDRS`, `toUpdate_eq_lift_fiberDRS`: the static-to-dynamic bridge.

The factorization `toUpdate = lift ∘ fiberDRS` separates two concerns:
`fiberDRS` embeds assignment-only relations into pair relations (passive
worlds), and `lift` converts relational meanings to set-transformer
meanings. Consequently `toUpdate` is always distributive (corollary of
`lift_isDistributive`) — the algebraic content of [hofmann-2025]'s
observation that ICDRT-style negation via propositional dref
complementation stays distributive, unlike test-based dynamic negation
that inspects whole states.
-/

namespace DynamicSemantics

open Core (Assignment)

variable {W E : Type*}
variable (φ φ₁ φ₂ φ₃ φ_DC φ_anaphor φ_antecedent : PVar) (v : IVar)
variable (i j : ICDRTAssignment W E)

/-! ### Information states and context transformers -/

/-- Set of assignment-world pairs (information state in flat update).

Kept as `abbrev` so it inherits `Set α`'s `Membership`,
`EmptyCollection`, `HasSubset`, `Union`, `Inter`, and `Singleton`
instances (and the corresponding `Set` API) directly. -/
abbrev IContext (W : Type*) (E : Type*) := Set (ICDRTAssignment W E × W)

namespace IContext

/-- The trivial context (all possibilities) -/
def univ : IContext W E := Set.univ

/-- Update with a world-predicate -/
def update (c : IContext W E) (p : W → Prop) : IContext W E :=
  { gw ∈ c | p gw.2 }

end IContext

/-- Context-to-context transformer (sentence denotation): the spine's
`CCP` at ICDRT possibilities. -/
abbrev DynProp (W : Type*) (E : Type*) := CCP (ICDRTAssignment W E × W)

namespace DynProp

/-- Identity (says nothing): the spine's `CCP.id`. -/
abbrev id : DynProp W E := CCP.id

/-- Absurd (contradiction): the spine's `CCP.absurd`. -/
abbrev absurd : DynProp W E := CCP.absurd

end DynProp

/-! ### Updates as static relations -/

/-- Static update relation between input and output assignments.

Following [muskens-1996]'s Compositional DRT, dynamic updates are
relations between assignments rather than operations on sets of
assignment-world pairs. The lift to context transformers is done by
`toUpdate` below. -/
def ICDRTUpdate (W : Type*) (E : Type*) :=
  ICDRTAssignment W E → ICDRTAssignment W E → Prop

namespace ICDRTUpdate

variable (D D₁ D₂ : ICDRTUpdate W E) (c : IContext W E)

/-- Sequencing (`;`): relational composition.
    `(D₁ ; D₂)(i)(j) ↔ ∃k, D₁(i)(k) ∧ D₂(k)(j)` -/
def seq : ICDRTUpdate W E :=
  λ i j => ∃ k, D₁ i k ∧ D₂ k j

infixl:60 " ⨟ " => seq

/-- Identity update: output equals input. -/
def idUp : ICDRTUpdate W E := λ i j => i = j

/-- Lift a static update relation to a context update on information states. -/
def toUpdate : DynProp W E :=
  λ c => { p | ∃ i, (i, p.2) ∈ c ∧ D i p.1 }

/-- Identity update lifts to identity on contexts. -/
theorem idUp_toUpdate : ICDRTUpdate.idUp.toUpdate c = c :=
  Set.ext (λ ⟨j, _⟩ =>
    ⟨λ ⟨_, hic, rfl⟩ => hic, λ hjc => ⟨j, hjc, rfl⟩⟩)

/-- Sequential composition lifts to function composition on contexts. -/
theorem seq_toUpdate : (seq D₁ D₂).toUpdate c = D₂.toUpdate (D₁.toUpdate c) :=
  Set.ext (λ ⟨_, _⟩ =>
    ⟨λ ⟨i, hic, k, h1, h2⟩ => ⟨k, ⟨i, hic, h1⟩, h2⟩,
     λ ⟨k, ⟨i, hic, h1⟩, h2⟩ => ⟨i, hic, k, h1, h2⟩⟩)

end ICDRTUpdate

/-! ### Variable updates -/

/-- Propositional variable update: `j` differs from `i` at most in the value of `p`.
`i[p]j` -/
def propVarUp (p : PVar) (i j : ICDRTAssignment W E) : Prop :=
  (∀ q : PVar, q ≠ p → j.prop q = i.prop q) ∧
  (∀ v : IVar, j.indiv v = i.indiv v)

/-- Individual variable update: `j` differs from `i` at most in the value of `v`.
`i[v]j` -/
def indivVarUp : Prop :=
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
negation from having global referents. Following [hofmann-2025]
Definition 25. -/
def relVarUp : Prop :=
  indivVarUp v i j ∧
  (∀ w : W, w ∈ j.prop φ ↔ j.indiv v w ≠ .star)

/-! ### Dynamic conditions on propositional drefs -/

/-- Dynamic inclusion: `φ₁(i) ⊆ φ₂(i)`. -/
def dynInclusion : Prop :=
  i.prop φ₁ ⊆ i.prop φ₂

/-- Condition: `φ₁` is the complement of `φ₂` at state `i`.
The negation condition `φ₁ ≡ φ̄₂`. -/
def isComplement : Prop :=
  i.prop φ₁ = (i.prop φ₂)ᶜ

/-! ### Predication and local entailment -/

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
def localEntailment : Prop :=
  ∀ w ∈ i.prop φ, i.indiv v w ≠ .star

/-! ### Veridicality typology -/

/-- Veridical individual dref: `v` has a referent in all `φ_DC`-worlds —
`localEntailment` read at the commitment set. -/
abbrev veridicalIndiv : Prop := localEntailment φ_DC v i

/-- Counterfactual individual dref: `v` maps to `⋆` in all `φ_DC`-worlds. -/
def counterfactualIndiv : Prop :=
  ∀ w ∈ i.prop φ_DC, i.indiv v w = .star

/-- Counterfactual propositional dref: `φ_DC(i) ∩ δ(i) = ∅`. -/
def counterfactualProp (φ_DC δ : PVar) (i : ICDRTAssignment W E) : Prop :=
  i.prop φ_DC ∩ i.prop δ = ∅

/-- Hypothetical individual dref: neither veridical nor counterfactual. -/
def hypotheticalIndiv : Prop :=
  ¬veridicalIndiv φ_DC v i ∧ ¬counterfactualIndiv φ_DC v i

/-- Accessibility: `v` is accessible at the anaphor site `φ_anaphor` iff
it is locally entailed there and the discourse is consistent. -/
def accessible (φ_anaphor : PVar) (v : IVar)
    (φ_DC : PVar) (i : ICDRTAssignment W E) : Prop :=
  localEntailment φ_anaphor v i ∧ (i.prop φ_DC).Nonempty

/-- Subset requirement: indefinite at `φ_antecedent` can antecede pronoun at
`φ_anaphor` only when `φ_anaphor(i) ⊆ φ_antecedent(i)` — `dynInclusion` at
the anaphor site. -/
abbrev subsetReq : Prop := dynInclusion φ_anaphor φ_antecedent i

/-! ### Multi-agent discourse contexts -/

/-- Generic declarative-assertion subset condition: `φ_DC(j) ⊆ φ(j)` —
`dynInclusion` under the speech-act reading "the speaker's commitment set
is updated to a subset of the asserted content". -/
abbrev decCondition (φ_DC φ : PVar) (j : ICDRTAssignment W E) : Prop :=
  dynInclusion φ_DC φ j

/-- **Counterfactual antecedent blocks veridical anaphor**
([hofmann-2025]'s bathroom-sentence theorem: "There isn't a bathroom.
#It is upstairs."). If `j` extends `i` keeping the commitment set and the
negated content fixed, the antecedent is counterfactual
(`φ_DC(i) ∩ φ_neg(i) = ∅`), and `j` satisfies both the DEC condition and
the anaphor's subset requirement, then the discourse is inconsistent.

Frameworks without propositional-dref structure have no analogue —
[charlow-2019]'s `State W E` handles the same phenomenon by
alternative-set filtering (`Studies/Charlow2019.lean`). -/
theorem counterfactual_blocks_veridical (i j : ICDRTAssignment W E)
    (φ_DC φ_anaphor φ_neg : PVar)
    (h_extends_DC : j.prop φ_DC = i.prop φ_DC)
    (h_extends_neg : j.prop φ_neg = i.prop φ_neg)
    (h_disjoint : counterfactualProp φ_DC φ_neg i)
    (h_dec : decCondition φ_DC φ_anaphor j)
    (h_subset : subsetReq φ_anaphor φ_neg j) :
    ¬(j.prop φ_DC).Nonempty := by
  rintro ⟨w, hw⟩
  have hmem : w ∈ i.prop φ_DC ∩ i.prop φ_neg :=
    ⟨h_extends_DC ▸ hw, h_extends_neg ▸ h_subset (h_dec hw)⟩
  rw [h_disjoint] at hmem
  exact hmem

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
    (initialContext dcVar : DiscContext W E Speaker).consistent :=
  λ _ => Set.univ_nonempty

end DiscContext

/-! ### Pragmatic and propositional maximization -/

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

/-! ### Structural theorems -/

/-- Local entailment follows from relative variable update. The biconditional
in `relVarUp` (Definition 25ii) directly yields local contextual entailment
at the output assignment. -/
theorem relVarUp_implies_localEntailment (h : relVarUp φ v i j) :
    localEntailment φ v j :=
  λ w hw => (h.2 w).mp hw

/-- Veridical dref + DC-subsumed anaphor context + consistency → accessibility. -/
theorem veridical_implies_accessible
    (h_veridical : veridicalIndiv φ_DC v i)
    (h_subset : i.prop φ_anaphor ⊆ i.prop φ_DC)
    (h_consistent : (i.prop φ_DC).Nonempty) :
    accessible φ_anaphor v φ_DC i :=
  ⟨λ w hw => h_veridical w (h_subset hw), h_consistent⟩

/-- Counterfactual dref in veridical anaphor context → inaccessibility. -/
theorem counterfactual_veridical_fails
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
theorem double_complement_eq
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
theorem veridicality_trichotomy :
    veridicalIndiv φ_DC v i ∨ counterfactualIndiv φ_DC v i ∨ hypotheticalIndiv φ_DC v i := by
  tauto

/-- Veridical and counterfactual are incompatible given a nonempty DC. -/
theorem veridical_counterfactual_exclusive
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
counterfactuality (the recipe used by [hofmann-2025]'s analysis of
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

/-! ### Fiberwise lift to CCP -/

variable (D D₁ D₂ : ICDRTUpdate W E)

/-- Embed an assignment-only relation into a pair relation with passive worlds.

`fiberDRS D (i, w) (j, w') ↔ w = w' ∧ D i j`

ICDRT updates operate on assignments only and worlds are inert fibers.
`fiberDRS` makes this structure explicit at the type level of
`Update (ICDRTAssignment W E × W)`. -/
def fiberDRS : Update (ICDRTAssignment W E × W) :=
  λ ⟨i, w⟩ ⟨j, w'⟩ => w = w' ∧ D i j

/-- `toUpdate = lift ∘ fiberDRS`: the static-to-dynamic bridge factors
through fiberwise embedding followed by relational image. -/
theorem toUpdate_eq_lift_fiberDRS : D.toUpdate = lift (fiberDRS D) := by
  funext σ
  apply Set.ext; intro ⟨j, w⟩
  simp only [ICDRTUpdate.toUpdate, lift, fiberDRS, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, hic, hD⟩
    exact ⟨⟨i, w⟩, hic, rfl, hD⟩
  · rintro ⟨⟨i, _⟩, hiw, rfl, hD⟩
    exact ⟨i, hiw, hD⟩

/-- `fiberDRS` preserves sequential composition. -/
theorem fiberDRS_seq :
    fiberDRS (ICDRTUpdate.seq D₁ D₂) = dseq (fiberDRS D₁) (fiberDRS D₂) := by
  funext p q; cases p; cases q
  simp only [fiberDRS, ICDRTUpdate.seq, dseq, Relation.Comp, eq_iff_iff]
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

/-! ### Distributivity and test eliminativity -/

/-- `toUpdate D` is always distributive: it processes each
assignment-world pair independently. Corollary of `lift_isDistributive`. -/
theorem toUpdate_isDistributive : IsDistributive (D.toUpdate) := by
  rw [toUpdate_eq_lift_fiberDRS]
  exact lift_isDistributive (fiberDRS D)

/-- A test update — one that preserves the assignment — lifts to an
eliminative CCP: it can only shrink the context, never grow it. -/
theorem toUpdate_test_eliminative (C : ICDRTAssignment W E → Prop) :
    IsEliminative (ICDRTUpdate.toUpdate (λ i j => i = j ∧ C j)) := by
  intro _ ⟨_, _⟩ hjw
  obtain ⟨_, hiw, rfl, _⟩ := hjw
  exact hiw

/-! ### Fibered lookup instance -/

/-- ICDRT contexts expose the shared lookup interface at `M = Entity`
(`Dynamic/Lookup.lean`), making ICDRT lookups comparable with the
extensional (`M = Id`) and [charlow-2019] (`M = Set`) families. -/
instance : DynamicSemantics.HasFiberedLookup Entity
    (ICDRTAssignment W E) IVar W E where
  iLookup i v w := i.indiv v w

end DynamicSemantics
