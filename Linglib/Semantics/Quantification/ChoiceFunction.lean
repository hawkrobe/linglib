import Mathlib.Init
import Linglib.Core.Logic.Intensional.Rigidity
import Linglib.Core.Logic.Quantification.Basic

/-!
# Choice Functions for Indefinite Determiners
[reinhart-1997] [kratzer-1998-pseudoscope] [winter-1997]

Choice functions provide an alternative to existential quantification for
the semantics of indefinite NPs. A choice function selects a single
individual from a non-empty set, yielding a referential (type *e*) meaning
for the indefinite DP.

## Motivation

The standard ∃-quantifier analysis of indefinites predicts scope via QR
or alternative mechanisms. Choice functions predict scope via the binding
site of the choice function variable itself:

- **Free CF variable** (Reinhart): existentially closed at any scope site
  → flexible scope (wide, intermediate, narrow)
- **Contextually bound CF** (Kratzer): situation parameter determines
  scope → scope fixed by situation binding

## World-Skolemized Choice Functions

[mirrazi-2024] proposes that indefinite determiners can introduce a
world variable into the choice function, yielding type `⟨s, ⟨⟨e,t⟩, e⟩⟩`.
When this world variable is **bound** by an intensional operator, the CF
picks possibly different individuals in different worlds (de dicto), while
the existential closure over the CF itself can sit above negation (wide
pseudo-scope). When the world variable is **free**, the CF is evaluated at
the actual world (de re). This is captured by connecting `SkolemCF` to
`Core.SitVarStatus`.

## Application to African Languages

[zimmermann-2008] analyses Hausa *wani/wata* as a standard
∃-quantifier, predicting flexible scope via QR.

[owusu-2022] analyses Akan *bí* as an unambiguous choice function whose
situation pronoun ties the CF and the NP to a single index (`SkolemCF`),
explaining why *bí* takes obligatory wide scope under negation: the
contextually-given CF is fixed before negation applies, and negation
binds no situation variable that could shift it.
-/

namespace Semantics.Quantification.ChoiceFunction

/-! ### Choice Functions -/

/-- A choice function selects an individual from a property.
    [reinhart-1997]: type `⟨⟨e,t⟩, e⟩`. -/
def CF (E : Type*) := (E → Prop) → E

/-- A choice function is **correct** if it always selects a member
    of the input set (when non-empty). -/
def CF.isCorrect {E : Type*} (f : CF E) : Prop :=
  ∀ (P : E → Prop), (∃ x, P x) → P (f P)

/-- An indefinite DP with choice function semantics denotes an
    individual: the result of applying the CF to the NP-property.

    ⟦a/some N⟧^f = f(⟦N⟧) -/
def cfIndefSem {E : Type*} (f : CF E) (nounProp : E → Prop) : E :=
  f nounProp

/-! ### Skolemized Choice Functions -/

/-- A situation-indexed (skolemized) choice function.

    [kratzer-1998-pseudoscope] introduced contextually-given CFs with
    pronoun-like skolem indices (individual arguments); [owusu-2022] adds
    a situation index shared by the CF and its NP argument, and
    [mirrazi-2024] a world index. [owusu-2022]'s entry:

    ⟦bí⟧ = λs.λP : CH(f_s). f_s(P(s))

    Scope is determined by the binding site of `s`:
    - `s` bound by a higher operator → wide scope
    - `s` bound locally (e.g., under a modal) → narrow scope
    - `s` free (contextually resolved) → specific/wide scope -/
def SkolemCF (S E : Type*) := S → CF E

/-- Apply a skolemized CF at a particular situation. -/
def SkolemCF.apply {S E : Type*} (f : SkolemCF S E)
    (s : S) (nounProp : E → Prop) : E :=
  f s nounProp

/-- A skolemized CF is correct if it is correct at every situation. -/
def SkolemCF.isCorrect {S E : Type*} (f : SkolemCF S E) : Prop :=
  ∀ (s : S), (f s).isCorrect

/-! ### Indefinite Analysis Type -/

/-- The two main semantic analyses of indefinite determiners.

    The analysis type structurally determines scope potential:
    - ∃-quantifiers scope via QR/alternative mechanisms → flexible
    - Choice functions scope via situation variable binding →
      obligatory wide scope under non-intensional operators

    [reinhart-1997]: the key empirical distinction is scope under
    negation. ∃-quantifiers allow narrow scope (¬ > ∃); choice functions
    force wide scope (∃ > ¬) because negation cannot shift the situation
    variable.

    Cross-linguistic evidence: Hausa *wani/wata* (∃) vs Akan *bí* (CF)
    ([zimmermann-2026]). -/
inductive IndefType where
  | existential    -- ∃-quantifier: scope via QR (wide + narrow)
  | choiceFunction -- Choice function: scope via situation binding
  deriving DecidableEq, Repr

/-- Whether wide pseudo-scope de dicto readings are predicted.

    [mirrazi-2024] §3: the pseudo-de dicto reading requires BOTH:
    (1) CF semantics — to separate ∃-closure (above negation) from
        descriptive content (below the intensional operator)
    (2) A world variable on the determiner — so the CF's output varies
        across worlds, yielding de dicto construal

    This DERIVES the cross-linguistic variation: Farsi (CF + world var) ✓,
    German/French (no world var on indefinite determiners) ✗.
    [schwarz-2012]. -/
def IndefType.canPseudoDeDicto (t : IndefType) (hasWorldVar : Bool) : Bool :=
  match t with
  | .choiceFunction => hasWorldVar
  | .existential    => false

/-! ### Scope via Situation Binding -/

/-- The wide-scope (∃ > ¬) reading of a CF-indefinite under negation,
    ⟦¬[bí N VP]⟧ = ¬VP(f(N)), is *specific*: a correct CF selects a
    restrictor member, so ¬VP(f(N)) entails the witnessed
    ∃x[N(x) ∧ ¬VP(x)] — without entailing the narrow-scope
    ¬∃x[N(x) ∧ VP(x)] (the readings diverge whenever `N` is not
    `VP`-uniform). Contrast ⟦¬[wani N VP]⟧ = ¬∃x[N(x) ∧ VP(x)]. -/
theorem cf_wide_scope_specific {E : Type*} (f : CF E) (hf : f.isCorrect)
    {N VP : E → Prop} (hN : ∃ x, N x) (h : ¬ VP (f N)) :
    ∃ x, N x ∧ ¬ VP x :=
  ⟨f N, hf N hN, h⟩

/-- A correct CF's output satisfies `VP` whenever every restrictor member
    does — the degenerate case in which the wide (∃ > ¬) and narrow
    (¬ > ∃) readings coincide. The CF-essential content of the wide-scope
    reading is `cf_wide_scope_specific`. -/
theorem cf_wide_scope_under_negation {E : Type*}
    (f : CF E) (hf : f.isCorrect)
    (N : E → Prop) (VP : E → Prop)
    (hNonEmpty : ∃ x, N x) (hAll : ∀ x, N x → VP x) :
    VP (f N) :=
  hAll (f N) (hf N hNonEmpty)

/-- An ∃-quantifier can take narrow scope under negation:
    ¬∃x[N(x) ∧ VP(x)] is satisfiable even when N is non-empty. -/
theorem exists_narrow_scope_under_negation {E : Type*}
    (N : E → Prop) (VP : E → Prop)
    (hNoMatch : ∀ x, N x → ¬VP x) :
    ¬∃ x, N x ∧ VP x :=
  fun ⟨x, hNx, hVPx⟩ => hNoMatch x hNx hVPx

/-! ### World Variable and De Re / De Dicto -/

open Core.SitVarStatus (SitVarStatus)

/-- Evaluate a skolemized CF according to the status of its world variable.
    - `SitVarStatus.free`: evaluate at `w₀` (the actual world) → de re
    - `SitVarStatus.bound`: evaluate at the bound world `w'` → de dicto

    [mirrazi-2024] §3: this is the mechanism that produces wide
    pseudo-scope de dicto readings. The ∃-closure over `f` sits above
    negation (wide scope), while the world argument is bound by the
    intensional operator (de dicto). -/
def SkolemCF.evalAt {S E : Type*} (f : SkolemCF S E)
    (status : SitVarStatus) (w₀ wBound : S) (nounProp : E → Prop) : E :=
  match status with
  | .free  => f w₀ nounProp
  | .bound => f wBound nounProp

/-- A world-skolemized CF can return different individuals at different
    worlds — this is what solves the fixed-set problem.

    [mirrazi-2024] ex. (45): even when the NP extension is rigid (the
    same set at every world), a world-skolemized CF `f(w', P)` can pick
    different members at different worlds because `f` is a function of `w'`. -/
theorem SkolemCF.cross_world_variation {S E : Type*}
    (f : SkolemCF S E) (w₁ w₂ : S) (P : E → Prop)
    (hVary : f w₁ P ≠ f w₂ P) :
    f.evalAt .bound w₁ w₂ P ≠ f.evalAt .bound w₂ w₁ P := by
  simp [SkolemCF.evalAt]
  exact Ne.symm hVary

/-! ### Bridge to B&C existential semantics

The Reinhart 1997 vs B&C 1981 schism: indefinites can be analyzed as
referential (CF, type *e*) or quantificational (`some_sem`, type
⟨⟨e,t⟩,⟨⟨e,t⟩,t⟩⟩).

The two analyses agree on the simple case (one-way bridge below) but
diverge on island-escape and pseudo-de-dicto readings. The asymmetry is
*deliberately exposed*, not collapsed: that visibility is the linglib
thesis. -/

open Core.Quantification

/-- Forward bridge: a correct CF, applied to the noun property, witnesses
    the corresponding `some_sem` reading whenever the restrictor is
    non-empty. The CF-output `f N` is in `N` (by correctness) and satisfies
    `VP` (by hypothesis), so it witnesses `∃ x, N x ∧ VP x`. -/
theorem cfIndefSem_implies_some_sem {α : Type*}
    (f : CF α) (hf : f.isCorrect)
    (N VP : α → Prop) (hN : ∃ x, N x) :
    VP (cfIndefSem f N) → some_sem N VP :=
  fun hVP => ⟨f N, hf N hN, hVP⟩

/-- Different correct CFs make different `some_sem`-predictions on the same
    noun/VP pair. The CF must commit in advance to a specific element; this
    commitment can disagree with the existential reading's witness.

    Witness: domain `Bool`, with noun `N = ⊤` (both inhabitants count) and
    `VP = (· = true)`. The CF `f₁` (prefer-true) hits the witness; the CF
    `f₂` (prefer-false) does not. Both are correct.

    This makes the framework asymmetry visible at the propositional level:
    `some_sem` is existence-of-witness; CF is commitment-to-witness, and
    multiple correct CFs commit differently. The deeper divergence —
    island-escape and pseudo-de-dicto under intensional operators — is
    out of scope here but motivated by the same structural gap. -/
theorem correct_cfs_disagree_on_some_sem :
    ∃ (f₁ f₂ : CF Bool), f₁.isCorrect ∧ f₂.isCorrect ∧
      ∃ (N VP : Bool → Prop),
        some_sem N VP ∧ VP (cfIndefSem f₁ N) ∧ ¬ VP (cfIndefSem f₂ N) := by
  classical
  -- f₁ prefers `true`: pick `true` whenever `P true`, else `false`.
  -- f₂ prefers `false`: dual.
  let f₁ : CF Bool := fun P => if P true then true else false
  let f₂ : CF Bool := fun P => if P false then false else true
  have hf₁ : f₁.isCorrect := by
    intro P ⟨x, hPx⟩
    show P (if P true then true else false)
    by_cases h : P true
    · simp [h]
    · simp [h]; cases x; exacts [hPx, absurd hPx h]
  have hf₂ : f₂.isCorrect := by
    intro P ⟨x, hPx⟩
    show P (if P false then false else true)
    by_cases h : P false
    · simp [h]
    · simp [h]; cases x; exacts [absurd hPx h, hPx]
  refine ⟨f₁, f₂, hf₁, hf₂, fun _ => True, (· = true), ⟨true, trivial, rfl⟩, ?_, ?_⟩
  · show f₁ (fun _ => True) = true
    simp [f₁]
  · show ¬ f₂ (fun _ => True) = true
    simp [f₂]

end Semantics.Quantification.ChoiceFunction
