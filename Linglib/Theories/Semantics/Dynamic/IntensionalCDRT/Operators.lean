import Linglib.Theories.Semantics.Dynamic.IntensionalCDRT.Basic

/-!
# ICDRT Operators

Core operators of Intensional Compositional DRT, following
@cite{hofmann-2025} §3.

## Static update semantics

ICDRT emulates dynamic update in static logic (@cite{muskens-1996}).
Updates are relations between individual assignments `i → j`, not
operations on sets of assignment-world pairs. Sentential operators
contribute static conditions on propositional drefs, distinguishing
ICDRT from nested-update systems.

## Main definitions

* `ICDRTUpdate` — static relation between assignments (Definition 17)
* `dynInclusion` — φ ∈ ψ (Definition 20b)
* `dynIdentity` — α ≡ β (Definition 21b)
* `dynComplementation` — φ̄ (Definition 21c)
* `dynUnion` — φ ∪ ψ (footnote 11)
* `dynPredication` — R_φ(v) (Definition 27)
* `localEntailment` — v entailed in φ at i (Definition 28)
* `decCondition` — DEC_S^φ declarative assertion condition (Definition 22)
* `isComplement` — φ₁ ≡ φ̄₂ complementation condition (Definition 23)
* `pragMaxDC` — pragmatic maximization for commitment sets (Definition 35)
* `propMaxOp` — propositional maximization max_φ (Definition 40)
* `believeCondition` — doxastic accessibility condition (Appendix C)

-/

namespace Semantics.Dynamic.IntensionalCDRT

open Core


-- ════════════════════════════════════════════════════════════════
-- § 1. Updates as Static Relations (Definition 17)
-- ════════════════════════════════════════════════════════════════

variable {W E : Type*}

/--
An ICDRT update: a static relation between input and output assignments.

In @cite{hofmann-2025} (Definition 17):
  `[δ₁,...,δₙ | C₁,...,Cₙ] := λi.λj. i[δ₁,...,δₙ]j ∧ C₁(j) ∧ ... ∧ Cₙ(j)`

Updates are interpreted as static relations between assignments,
following @cite{muskens-1996}'s Compositional DRT.
-/
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

/-- An update is successful from i if some output j exists. -/
def successful (D : ICDRTUpdate W E) (i : ICDRTAssignment W E) : Prop :=
  ∃ j, D i j

/-- Lift a static update relation to a context update on information states.
    Bridge between ICDRT's static relation semantics and the flat-update
    context semantics of `IContext`/`DynProp` in Basic.lean. -/
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
-- § 2. Variable Update
-- ════════════════════════════════════════════════════════════════

/--
Propositional variable update: j differs from i at most in the value of p.
`i[p]j`
-/
def propVarUp (p : PVar) (i j : ICDRTAssignment W E) : Prop :=
  (∀ q : PVar, q ≠ p → j.prop q = i.prop q) ∧
  (∀ v : IVar, j.indiv v = i.indiv v)

/--
Individual variable update: j differs from i at most in the value of v.
`i[v]j`
-/
def indivVarUp (v : IVar) (i j : ICDRTAssignment W E) : Prop :=
  (∀ p : PVar, j.prop p = i.prop p) ∧
  (∀ u : IVar, u ≠ v → j.indiv u = i.indiv u)

/--
Multi-variable update: j differs from i at most in the listed prop/indiv vars.
-/
def multiVarUp (ps : List PVar) (vs : List IVar)
    (i j : ICDRTAssignment W E) : Prop :=
  (∀ p : PVar, p ∉ ps → j.prop p = i.prop p) ∧
  (∀ v : IVar, v ∉ vs → j.indiv v = i.indiv v)

/--
Relative variable update (Definition 25): `i[φ : v]j`

(25i) j differs from i at most in v.
(25ii) For any world w, `φ(j)(w) ↔ v(j)(w) ≠ ⋆`.

This ensures v has a referent in all and only the φ-worlds.
The biconditional (not just implication) is crucial: it prevents
drefs under negation from having global referents.
-/
def relVarUp (φ : PVar) (v : IVar) (i j : ICDRTAssignment W E) : Prop :=
  indivVarUp v i j ∧
  (∀ w : W, w ∈ j.prop φ ↔ j.indiv v w ≠ .star)


-- ════════════════════════════════════════════════════════════════
-- § 3. Dynamic Conditions (Definitions 20–21)
-- ════════════════════════════════════════════════════════════════

/--
Dynamic inclusion (Definition 20b): `φ₁ ∈ φ₂`

A condition on assignments: at state i, the set of worlds in φ₁
is a subset of the set of worlds in φ₂.

`φ_{DC_S} ∈ φ₁ = λi. φ_{DC_S}(i) ⊆ φ₁(i)`
-/
def dynInclusion (φ₁ φ₂ : PVar) (i : ICDRTAssignment W E) : Prop :=
  i.prop φ₁ ⊆ i.prop φ₂

notation:50 φ₁ " ∈ₚ " φ₂ " at " i => dynInclusion φ₁ φ₂ i

/--
Dynamic identity (Definition 21b): `α ≡ β`

At state i, drefs α and β point to the same set of worlds.
`α ≡ β := λi. α(i) = β(i)`
-/
def dynIdentity (α β : PVar) (i : ICDRTAssignment W E) : Prop :=
  i.prop α = i.prop β

/--
Dynamic complementation (Definition 21c): `φ̄`

The complement of a propositional dref.
`φ̄ := λi. φ̄(i)` where φ̄(i) is the set-theoretic complement of φ(i).
-/
def dynComplement (φ : PVar) (i : ICDRTAssignment W E) : Set W :=
  (i.prop φ)ᶜ

/--
Condition: φ₁ is the complement of φ₂ at state i.
`φ₁ ≡ φ̄₂` — the negation condition from NOT (Definition 23).
-/
def isComplement (φ₁ φ₂ : PVar) (i : ICDRTAssignment W E) : Prop :=
  i.prop φ₁ = (i.prop φ₂)ᶜ

/--
Dynamic union (footnote 11): `φ₁ ∪ φ₂`

Used in disjunction (§4.2): the matrix proposition is the union
of the disjunct propositions.
`φ₁ ⊎ φ₂ := λi. φ₁(i) ∪ φ₂(i)`
-/
def dynUnion (φ₁ φ₂ : PVar) (i : ICDRTAssignment W E) : Set W :=
  i.prop φ₁ ∪ i.prop φ₂


-- ════════════════════════════════════════════════════════════════
-- § 4. Predication and Entailment (Definitions 27–28)
-- ════════════════════════════════════════════════════════════════

/--
Dynamic predication (Definition 27): `R_φ(v)`

Conditions involving predicates are interpreted relative to a
propositional dref φ (the local context):

`R_φ(v) := λi. ∀w.(φ(i)(w) → R(v(i)(w))(w))`

This ensures the predicate holds of v's referent in all worlds
of the local context φ.
-/
def dynPred (R : E → W → Prop) (φ : PVar) (v : IVar)
    (i : ICDRTAssignment W E) : Prop :=
  ∀ w ∈ i.prop φ,
    match i.indiv v w with
    | .some e => R e w
    | .star => False

/--
Local contextual entailment (Definition 28):
`v` is entailed in the context of `φ` at `i`, iff for each world `w`
in `φ(i)`, `v(i)` has an existing referent (i.e., `v(i)(w) ≠ ⋆`).

`∀w.(φ(i)(w) → v(i)(w) ≠ ⋆_e)`
-/
def localEntailment (φ : PVar) (v : IVar)
    (i : ICDRTAssignment W E) : Prop :=
  ∀ w ∈ i.prop φ, i.indiv v w ≠ .star

/--
Predication entails existence (Definition 29b):
If v(i)(w) = some e and R(e)(w) holds, then v(i)(w) ≠ ⋆.

For any unary relation R, assignment i, individual dref v, and world w.
-/
theorem pred_entails_existence (v : IVar) (i : ICDRTAssignment W E)
    (w : W) (e : E) (hv : i.indiv v w = .some e) :
    i.indiv v w ≠ .star := by
  rw [hv]; exact fun h => nomatch h


-- ════════════════════════════════════════════════════════════════
-- § 5. DEC and NOT Operators (Definitions 22–23)
-- ════════════════════════════════════════════════════════════════

/--
Declarative assertion operator (Definition 22): `DEC_S^φ`

`DEC_S^φ ≡ λP. λφ. [φ | φ_{DC_S} ∈ φ]; P(φ)`

The DEC operator:
1. Introduces a propositional dref φ for the assertion content
2. Constrains φ_{DC_S} ⊆ φ (assertion = intersective update of context set)
3. Applies the scope P to φ

The condition φ_{DC_S} ∈ φ narrows permissible values of φ_{DC_S} to
subsets of φ, modeling the pragmatics of intersective assertion.

We factor out DEC as a condition on the output assignment.
-/
def decCondition (φ_DC : PVar) (φ : PVar) (j : ICDRTAssignment W E) : Prop :=
  j.prop φ_DC ⊆ j.prop φ



-- ════════════════════════════════════════════════════════════════
-- § 6. Discourse Contexts and Consistency (Definitions 31–34)
-- ════════════════════════════════════════════════════════════════

/--
A discourse context (Definition 31): `C = ⟨M, INT, i⟩`

- `INT` is the set of interlocutors
- `i` is the current discourse state (assignment)
- Each interlocutor x ∈ INT has a commitment-set dref φ_{DC_x}

We omit M (the model) since it is implicit in the Lean universe.
-/
structure DiscContext (W : Type*) (E : Type*) (Speaker : Type*) where
  /-- Current discourse state -/
  state : ICDRTAssignment W E
  /-- Maps each interlocutor to their commitment-set propositional variable -/
  dcVar : Speaker → PVar

namespace DiscContext

variable {W E Speaker : Type*}

/-- Discourse consistency (Definition 31):
    All interlocutor commitment sets are nonempty.
    `∀x ∈ INT, φ_{DC_x}(i) ≠ ∅` -/
def consistent (c : DiscContext W E Speaker) : Prop :=
  ∀ x : Speaker, (c.state.prop (c.dcVar x)).Nonempty

/-- An update D is successful in context C iff there exists an output j
    such that D(i)(j) holds (Definition 34). -/
def updateSuccessful (c : DiscContext W E Speaker) (D : ICDRTUpdate W E) : Prop :=
  ∃ j, D c.state j

/-- An update is acceptable iff it is successful AND leaves all
    commitment sets nonempty (discourse consistency). -/
def updateAcceptable (c : DiscContext W E Speaker) (D : ICDRTUpdate W E) : Prop :=
  ∃ j, D c.state j ∧ ∀ x : Speaker, (j.prop (c.dcVar x)).Nonempty

/-- Null assignment (Definition 32): `i₀`.
    All propositional drefs map to the set of all worlds;
    all individual drefs map to ⋆ in every world. -/
def nullAssignment : ICDRTAssignment W E where
  prop := λ _ => Set.univ
  indiv := λ _ _ => .star

/-- Initial discourse context (Definition 33): `C₀ = ⟨M, INT, i₀⟩`.
    All interlocutors start with commitment sets equal to the full set of worlds. -/
def initialContext (dcVar : Speaker → PVar) : DiscContext W E Speaker where
  state := nullAssignment
  dcVar := dcVar

/-- The initial context is always consistent: all commitment sets are
    nonempty (they equal the full set of worlds). -/
theorem initialContext_consistent [Nonempty W] {dcVar : Speaker → PVar} :
    (initialContext dcVar : DiscContext W E Speaker).consistent := by
  intro _; exact Set.univ_nonempty

end DiscContext


-- ════════════════════════════════════════════════════════════════
-- § 7. Maximization (Definitions 35 and 40)
-- ════════════════════════════════════════════════════════════════

/--
Pragmatic maximization for commitment sets (Definition 35).

When updating context C with D, output j is pragmatically privileged when
no other possible output h assigns a proper superset to any DC dref.

(35a) D(i_C)(j) = 1
(35b) ∀h,x: D(i_C)(h) ∧ x ∈ INT → ¬(φ_{DC_x}(j) ⊂ φ_{DC_x}(h))

This implements Gricean Quantity: speakers commit to the strongest
claim supported by the evidence.
-/
def pragMaxDC {Speaker : Type*} (dcVar : Speaker → PVar) (D : ICDRTUpdate W E)
    (i j : ICDRTAssignment W E) : Prop :=
  D i j ∧ ∀ h, D i h → ∀ x : Speaker, ¬(j.prop (dcVar x) ⊂ h.prop (dcVar x))

/--
Propositional maximization (Definition 40): `max_φ(D)`

Restricts outputs to those where propositional dref φ is maximal:
no other successful output k assigns a proper superset to φ.

`max_φ(D) := λi.λj. D(i)(j) ∧ ∀k(D(i)(k) → ¬(φ(j) ⊂ φ(k)))`

Essential for correct truth conditions under negation: ensures
φ₂ (the local context of the negated existential) is the maximal
set of worlds where there is a bathroom.
-/
def propMaxOp (φ : PVar) (D : ICDRTUpdate W E)
    (i j : ICDRTAssignment W E) : Prop :=
  D i j ∧ ∀ k, D i k → ¬(j.prop φ ⊂ k.prop φ)


-- ════════════════════════════════════════════════════════════════
-- § 8. Veridicality and Accessibility (Definitions 36–39)
-- ════════════════════════════════════════════════════════════════

/--
Veridical individual dref (Definition 36a): v is veridical relative to
interlocutor x at discourse state i iff v has a referent (≠ ⋆) in all
worlds of x's commitment set.

`∀w(w ∈ φ_{DC_x}(i) → δ(i)(w) ≠ ⋆)`
-/
def veridicalIndiv (φ_DC : PVar) (v : IVar)
    (i : ICDRTAssignment W E) : Prop :=
  ∀ w ∈ i.prop φ_DC, i.indiv v w ≠ .star

/--
Veridical propositional dref (Definition 36b): φ is veridical relative to
interlocutor x at discourse state i iff x's commitment set entails φ.

`φ_{DC_x}(i) ⊆ δ(i)`
-/
def veridicalProp (φ_DC : PVar) (δ : PVar)
    (i : ICDRTAssignment W E) : Prop :=
  i.prop φ_DC ⊆ i.prop δ

/--
Counterfactual individual dref (Definition 37a): v is counterfactual
relative to x at i iff v maps to ⋆ in all worlds of x's commitment set.

`∀w(w ∈ φ_{DC_x}(i) → δ(i)(w) = ⋆)`
-/
def counterfactualIndiv (φ_DC : PVar) (v : IVar)
    (i : ICDRTAssignment W E) : Prop :=
  ∀ w ∈ i.prop φ_DC, i.indiv v w = .star

/--
Counterfactual propositional dref (Definition 37b): φ is counterfactual
relative to x at i iff x's commitment set is disjoint from φ.

`φ_{DC_x}(i) ∩ δ(i) = ∅`
-/
def counterfactualProp (φ_DC : PVar) (δ : PVar)
    (i : ICDRTAssignment W E) : Prop :=
  i.prop φ_DC ∩ i.prop δ = ∅

/--
Hypothetical individual dref: v is hypothetical relative to x at i iff
v has a referent in some DC worlds but maps to ⋆ in others.
This is the third veridicality category (alongside veridical and
counterfactual), representing uncertain existence.
-/
def hypotheticalIndiv (φ_DC : PVar) (v : IVar)
    (i : ICDRTAssignment W E) : Prop :=
  ¬veridicalIndiv φ_DC v i ∧ ¬counterfactualIndiv φ_DC v i

/--
Hypothetical propositional dref: φ is hypothetical relative to x at i iff
x's DC neither entails φ nor is disjoint from φ.
-/
def hypotheticalProp (φ_DC : PVar) (δ : PVar)
    (i : ICDRTAssignment W E) : Prop :=
  ¬veridicalProp φ_DC δ i ∧ ¬counterfactualProp φ_DC δ i

/--
Accessibility (Definition 38): v is accessible for pronoun β_v at state i,
iff v is locally entailed in the local context of β_v and the discourse
is consistent at i.
-/
def accessible (φ_anaphor : PVar) (v : IVar)
    (φ_DC : PVar) (i : ICDRTAssignment W E) : Prop :=
  localEntailment φ_anaphor v i ∧ (i.prop φ_DC).Nonempty

/--
Subset requirement (Definition 39): indefinite α^v can antecede
pronoun β_v at state i only if the local context of β_v is a
subset of the local context of α^v.
-/
def subsetReq (φ_anaphor φ_antecedent : PVar)
    (i : ICDRTAssignment W E) : Prop :=
  i.prop φ_anaphor ⊆ i.prop φ_antecedent


-- ════════════════════════════════════════════════════════════════
-- § 9. Structural Theorems
-- ════════════════════════════════════════════════════════════════

/--
Local entailment follows from relative variable update.

This is the key structural connection in @cite{hofmann-2025}: the biconditional
in Definition 25ii (`∀w. φ(j)(w) ↔ v(j)(w) ≠ ⋆`) directly yields
local contextual entailment (Definition 28) at the output assignment.

This links indefinite introduction to pronoun resolution: any dref
introduced by relative variable update is locally entailed in its
own local context, making it accessible for subsequent anaphora.
-/
theorem relVarUp_implies_localEntailment (φ : PVar) (v : IVar)
    (i j : ICDRTAssignment W E) (h : relVarUp φ v i j) :
    localEntailment φ v j :=
  λ w hw => (h.2 w).mp hw

/--
Veridical dref is accessible: if v is veridical (exists in all DC worlds),
the anaphor's local context is entailed by DC, and discourse is consistent,
then v is accessible.
-/
theorem veridical_implies_accessible (φ_DC φ_anaphor : PVar) (v : IVar)
    (i : ICDRTAssignment W E)
    (h_veridical : veridicalIndiv φ_DC v i)
    (h_subset : i.prop φ_anaphor ⊆ i.prop φ_DC)
    (h_consistent : (i.prop φ_DC).Nonempty) :
    accessible φ_anaphor v φ_DC i :=
  ⟨λ w hw => h_veridical w (h_subset hw), h_consistent⟩

/--
Counterfactual dref in veridical context creates contradiction:
If v is counterfactual (maps to ⋆ in all DC worlds), and the anaphor's
local context is veridical (DC ⊆ φ_anaphor), and by the subset requirement
φ_anaphor ⊆ φ_antecedent, then either discourse is inconsistent or
local entailment fails.
-/
theorem counterfactual_veridical_fails (φ_DC φ_anaphor φ_antecedent : PVar)
    (v : IVar) (i : ICDRTAssignment W E)
    (h_cf : counterfactualIndiv φ_DC v i)
    (h_dc_veridical : i.prop φ_DC ⊆ i.prop φ_anaphor)
    (h_subset : subsetReq φ_anaphor φ_antecedent i)
    (h_rel : ∀ w, w ∈ i.prop φ_antecedent ↔ i.indiv v w ≠ .star) :
    ¬accessible φ_anaphor v φ_DC i := by
  intro ⟨h_ent, h_ne⟩
  obtain ⟨w, hw⟩ := h_ne
  have h_in_anaphor := h_dc_veridical hw
  have h_in_ante := h_subset h_in_anaphor
  have h_ne_star := (h_rel w).mp h_in_ante
  exact h_ne_star (h_cf w hw)

/--
Double complementation: if φ₁ ≡ φ̄₂ and φ₃ ≡ φ̄₁, then φ₃ = φ₂.
This is how double negation restores veridicality: the doubly-negated
indefinite's local context equals the original.
-/
theorem double_complement_eq (φ₁ φ₂ φ₃ : PVar) (i : ICDRTAssignment W E)
    (h1 : isComplement φ₁ φ₂ i)
    (h2 : isComplement φ₃ φ₁ i) :
    i.prop φ₃ = i.prop φ₂ := by
  rw [isComplement] at h1 h2
  rw [h2, h1, compl_compl]

/--
Disjunction enables anaphora: if v has a referent in all φ₃-worlds
(the second disjunct), and the anaphor's local context φ_a ⊆ φ₃,
then v is locally entailed in φ_a — even though v may be counterfactual
relative to the overall assertion. This works because disjunction
does NOT require overlap between disjunct propositions.
-/
theorem disjunction_enables_anaphora (φ₃ φ_a : PVar) (v : IVar)
    (i : ICDRTAssignment W E)
    (h_sub : i.prop φ_a ⊆ i.prop φ₃)
    (h_rel : ∀ w, w ∈ i.prop φ₃ → i.indiv v w ≠ .star) :
    localEntailment φ_a v i :=
  λ w hw => h_rel w (h_sub hw)


/--
Veridicality trichotomy: every individual dref is veridical, counterfactual,
or hypothetical relative to any speaker. These three categories are exhaustive.
-/
theorem veridicality_trichotomy (φ_DC : PVar) (v : IVar)
    (i : ICDRTAssignment W E) :
    veridicalIndiv φ_DC v i ∨ counterfactualIndiv φ_DC v i ∨ hypotheticalIndiv φ_DC v i := by
  by_cases hv : veridicalIndiv φ_DC v i
  · exact Or.inl hv
  · by_cases hc : counterfactualIndiv φ_DC v i
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr ⟨hv, hc⟩)

/--
Veridical and counterfactual are mutually exclusive given nonempty DC:
if v has a referent in all DC worlds AND maps to ⋆ in all DC worlds,
then DC must be empty.
-/
theorem veridical_counterfactual_exclusive (φ_DC : PVar) (v : IVar)
    (i : ICDRTAssignment W E)
    (hv : veridicalIndiv φ_DC v i) (hc : counterfactualIndiv φ_DC v i) :
    ¬(i.prop φ_DC).Nonempty :=
  λ ⟨w, hw⟩ => absurd (hc w hw) (hv w hw)

/--
Star blocks dynamic predication: if v maps to ⋆ at any world w ∈ φ,
then R_φ(v) fails. This connects the universal falsifier axiom
(@cite{hofmann-2025} §2.1) to ICDRT's predication mechanism.
-/
theorem star_blocks_dynPred (R : E → W → Prop) (φ : PVar) (v : IVar)
    (i : ICDRTAssignment W E) (w : W)
    (hw : w ∈ i.prop φ) (hstar : i.indiv v w = .star)
    (hpred : dynPred R φ v i) : False := by
  have := hpred w hw; rw [hstar] at this; exact this

/--
Negated existential truth conditions: DEC + complementation implies
the existential's content is counterfactual relative to the speaker.

When a speaker asserts "there is no bathroom":
- DEC constrains DC ⊆ φ_outer (the assertion content)
- NOT constrains φ_outer = (φ_inner)ᶜ (complementation)
- Together: DC ∩ φ_inner = ∅ (bathroom worlds are counterfactual)

This derivation connects three independent ICDRT mechanisms and has
no analog in BUS (which lacks per-speaker commitment sets).
-/
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


/--
Attitude verb condition: `believe^{φ'}(δ^v)` (Appendix C).

The attitude verb introduces a propositional dref φ' for the agent's
doxastic state. `dox j` returns the set of worlds compatible with
the agent's beliefs at assignment `j`.

`believe_φ'(δ^v) ≡ [φ' | DOX(δ,φ) ⊆ φ']; P(φ')`

where DOX(δ,φ)(i) is the set of worlds compatible with δ's beliefs
in context φ at assignment i.
-/
def believeCondition (φ_belief : PVar) (dox : ICDRTAssignment W E → Set W)
    (j : ICDRTAssignment W E) : Prop :=
  dox j ⊆ j.prop φ_belief


end Semantics.Dynamic.IntensionalCDRT
