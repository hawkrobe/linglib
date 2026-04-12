import Linglib.Core.Semantics.Proposition

/-!
# Parameterized Update

Framework-agnostic infrastructure for semantics and pragmatics with
**parameter uncertainty**: meaning depends on a parameter (threshold,
compositional context, comparison class, variable assignment) and
truth at a world involves quantifying over available parameters.

## The Fiber Bundle

A fragment set F ⊆ P × W is a fiber bundle over worlds W. The fiber
at w is F_w = {p : F(p, w)} — the parameters available at that world.
An assertion φ with parameterized semantics ⟦φ⟧ : P → W → Prop acts
as a **fiberwise filter**: F' = {(p, w) ∈ F : ⟦φ⟧(p, w)}.

Different linguistic theories differ in how they project from the bundle
back to worlds, using the ∃ ⊣ Δ ⊣ ∀ adjunction:

- **∃-projection** (@cite{caie-2023}, Barker 2002):
  w survives iff ∃ p ∈ F_w, ⟦φ⟧(p, w)
- **∀-projection** (supervaluation, Fine 1975):
  w survives iff ∀ p ∈ F_w, ⟦φ⟧(p, w)
- **Σ-projection** (RSA, @cite{lassiter-goodman-2017}):
  score(w) = Σ_p weight(p) · ⟦φ⟧(p, w)

The first two are De Morgan duals (`not_forall`): ¬(∀p.φ) ↔ ∃p.¬φ.
The third is a soft interpolation (not formalized here; see RSA).

## Instances

| Theory              | P (parameter)         | Projection |
|---------------------|-----------------------|------------|
| Caie 2023           | compositional context | ∃          |
| Supervaluation      | precisification       | ∀          |
| RSA (L&G 2017)      | threshold θ           | Σ          |
| CCP                 | variable assignment   | ∃          |
| Klein 1980          | comparison class      | ∃ (comp.)  |

## Monotone Collapse

When semantics is antitone in the parameter (e.g., `d > θ` for degree
semantics), the projections collapse to extremal checks:
- ∃ p ∈ F_w, sem(p, w) ↔ sem(min(F_w), w)
- ∀ p ∈ F_w, sem(p, w) ↔ sem(max(F_w), w)

The gap between min and max is the **borderline region**: worlds where
∃-projection and ∀-projection disagree.

## Contextual Pruning

Sequential assertion with pruning — the mechanism by which earlier
assertions constrain which parameters are available for later ones —
reduces to a single update checking both conditions. This holds for
both ∃ and ∀ projection.
-/

namespace Core.Semantics.ParameterizedUpdate

open Core.Proposition (Prop')

-- ════════════════════════════════════════════════════════════════
-- § 1. Fragment Sets
-- ════════════════════════════════════════════════════════════════

variable {P W : Type*}

/-- A fragment set: a relation between parameters and worlds.
    F(p, w) holds iff parameter p is available at world w.
    The fiber at w is F_w = {p : F p w}.

    Generalizes `InterpAssignment C W` from @cite{caie-2023}
    (argument order swapped). -/
abbrev FragmentSet (P W : Type*) := P → W → Prop

/-- Fiberwise filter: restrict a fragment set to parameter–world pairs
    where the semantics holds.

    Generalizes Contextual Pruning (@cite{caie-2023}): after asserting α,
    only parameters that made α true remain available. -/
def fiberwiseFilter (F : FragmentSet P W) (sem : P → W → Prop) :
    FragmentSet P W :=
  λ p w => F p w ∧ sem p w


-- ════════════════════════════════════════════════════════════════
-- § 2. Projection Operators
-- ════════════════════════════════════════════════════════════════

/-- Existential projection: w survives iff some parameter in F_w makes
    the semantics true.

    This is @cite{caie-2023}'s disjunctive updating and Barker 2002's
    dynamics of vagueness. -/
def existentialProjection (F : FragmentSet P W) (sem : P → W → Prop) :
    Prop' W :=
  λ w => ∃ p, F p w ∧ sem p w

/-- Universal projection: w survives iff all parameters in F_w make the
    semantics true.

    This is super-truth (Fine 1975): truth under all admissible
    precisifications. -/
def universalProjection (F : FragmentSet P W) (sem : P → W → Prop) :
    Prop' W :=
  λ w => ∀ p, F p w → sem p w


-- ════════════════════════════════════════════════════════════════
-- § 3. Context-Set-Gated Updates
-- ════════════════════════════════════════════════════════════════

/-- Existential update: restrict to the context set, then ∃-project.

    `existentialUpdate cs F sem w ↔ w ∈ cs ∧ ∃ p ∈ F_w, sem(p, w)`. -/
def existentialUpdate (cs : Prop' W) (F : FragmentSet P W)
    (sem : P → W → Prop) : Prop' W :=
  λ w => cs w ∧ existentialProjection F sem w

/-- Universal update: restrict to the context set, then ∀-project.

    `universalUpdate cs F sem w ↔ w ∈ cs ∧ ∀ p ∈ F_w, sem(p, w)`. -/
def universalUpdate (cs : Prop' W) (F : FragmentSet P W)
    (sem : P → W → Prop) : Prop' W :=
  λ w => cs w ∧ universalProjection F sem w


-- ════════════════════════════════════════════════════════════════
-- § 4. De Morgan Duality
-- ════════════════════════════════════════════════════════════════

/-- **De Morgan duality** (∃-side): ∃-projection of sem ↔
    negation of ∀-projection of the negation. -/
theorem deMorgan_existential_universal (F : FragmentSet P W)
    (sem : P → W → Prop) (w : W) :
    existentialProjection F sem w ↔
    ¬ universalProjection F (λ p w => ¬ sem p w) w := by
  constructor
  · intro ⟨p, hF, hs⟩ hall; exact hall p hF hs
  · intro h; by_contra hne
    exact h fun p hF hs => hne ⟨p, hF, hs⟩

/-- **De Morgan duality** (∀-side): ∀-projection of sem ↔
    negation of ∃-projection of the negation. -/
theorem deMorgan_universal_existential (F : FragmentSet P W)
    (sem : P → W → Prop) (w : W) :
    universalProjection F sem w ↔
    ¬ existentialProjection F (λ p w => ¬ sem p w) w := by
  constructor
  · intro hall ⟨p, hF, hs⟩; exact hs (hall p hF)
  · intro h p hF; by_contra hs; exact h ⟨p, hF, hs⟩


-- ════════════════════════════════════════════════════════════════
-- § 5. Monotone Collapse
-- ════════════════════════════════════════════════════════════════

/-- Monotone collapse (∃): when sem is antitone in p and F_w has a
    minimum element, ∃-projection reduces to checking the minimum.

    For degree semantics: `⟦tall⟧(θ, w) = degree(w) > θ` is antitone
    in θ. The ∃-projection `∃ θ ∈ Θ, degree(w) > θ` collapses to
    `degree(w) > min(Θ)`. -/
theorem monotoneCollapse_exists [Preorder P]
    (F : FragmentSet P W) (sem : P → W → Prop) (w : W) (p₀ : P)
    (h_mem : F p₀ w)
    (h_min : ∀ p, F p w → p₀ ≤ p)
    (h_anti : ∀ p₁ p₂ : P, p₁ ≤ p₂ → sem p₂ w → sem p₁ w) :
    existentialProjection F sem w ↔ sem p₀ w := by
  constructor
  · intro ⟨p, hF, hs⟩; exact h_anti p₀ p (h_min p hF) hs
  · intro hs; exact ⟨p₀, h_mem, hs⟩

/-- Monotone collapse (∀): when sem is antitone in p and F_w has a
    maximum element, ∀-projection reduces to checking the maximum.

    For degree semantics: the ∀-projection `∀ θ ∈ Θ, degree(w) > θ`
    collapses to `degree(w) > max(Θ)`. -/
theorem monotoneCollapse_forall [Preorder P]
    (F : FragmentSet P W) (sem : P → W → Prop) (w : W) (p₀ : P)
    (h_mem : F p₀ w)
    (h_max : ∀ p, F p w → p ≤ p₀)
    (h_anti : ∀ p₁ p₂ : P, p₁ ≤ p₂ → sem p₂ w → sem p₁ w) :
    universalProjection F sem w ↔ sem p₀ w := by
  constructor
  · intro hall; exact hall p₀ h_mem
  · intro hs p hF; exact h_anti p p₀ (h_max p hF) hs

/-- Corollary: when sem is antitone and F_w has both min and max,
    the ∃ and ∀ projections agree iff w is outside the **borderline
    region** — either sem holds at the hardest parameter (clearly in)
    or fails at the easiest parameter (clearly out).

    The borderline region where projections disagree is precisely
    `sem p_min w ∧ ¬ sem p_max w`. -/
theorem projections_agree_iff_clear [Preorder P]
    (F : FragmentSet P W) (sem : P → W → Prop) (w : W) (p_min p_max : P)
    (hmin_mem : F p_min w) (hmax_mem : F p_max w)
    (h_min : ∀ p, F p w → p_min ≤ p)
    (h_max : ∀ p, F p w → p ≤ p_max)
    (h_anti : ∀ p₁ p₂ : P, p₁ ≤ p₂ → sem p₂ w → sem p₁ w) :
    (existentialProjection F sem w ↔ universalProjection F sem w) ↔
    (sem p_max w ∨ ¬ sem p_min w) := by
  rw [monotoneCollapse_exists F sem w p_min hmin_mem h_min h_anti,
      monotoneCollapse_forall F sem w p_max hmax_mem h_max h_anti]
  constructor
  · intro ⟨mp, _⟩
    by_cases h : sem p_min w
    · exact Or.inl (mp h)
    · exact Or.inr h
  · intro h
    cases h with
    | inl hmax => exact ⟨λ _ => hmax, λ hs => h_anti p_min p_max
        (h_min p_max hmax_mem) hs⟩
    | inr hmin => exact ⟨λ hs => absurd hs hmin, λ hs => h_anti p_min p_max
        (h_min p_max hmax_mem) hs⟩


-- ════════════════════════════════════════════════════════════════
-- § 6. Sequential Update (Contextual Pruning)
-- ════════════════════════════════════════════════════════════════

/-- Sequential ∃-update with pruning: asserting α then β (where β's
    parameters are pruned by α) equals a single ∃-update checking
    both α and β.

    This is the general form of Contextual Pruning (@cite{caie-2023}):
    the two-step process (update context set by α, prune parameters
    by α, then update by β) is equivalent to a single update requiring
    both α and β under the same parameter. -/
theorem sequential_existentialUpdate (cs : Prop' W) (F : FragmentSet P W)
    (sem₁ sem₂ : P → W → Prop) :
    existentialUpdate
      (existentialUpdate cs F sem₁)
      (fiberwiseFilter F sem₁)
      sem₂ =
    existentialUpdate cs F (λ p w => sem₁ p w ∧ sem₂ p w) := by
  funext w
  simp only [existentialUpdate, existentialProjection, fiberwiseFilter]
  exact propext ⟨
    λ ⟨⟨hcs, _⟩, p, ⟨hF, hs₁⟩, hs₂⟩ => ⟨hcs, p, hF, hs₁, hs₂⟩,
    λ ⟨hcs, p, hF, hs₁, hs₂⟩ => ⟨⟨hcs, p, hF, hs₁⟩, p, ⟨hF, hs₁⟩, hs₂⟩⟩

/-- Sequential ∀-update with pruning: asserting α then β (where β's
    parameters are pruned by α) equals a single ∀-update checking
    both α and β.

    The ∀ case works because: if all parameters satisfy α (first step),
    then "pruned parameters" = "all parameters", so requiring β for
    pruned parameters = requiring β for all parameters. -/
theorem sequential_universalUpdate (cs : Prop' W) (F : FragmentSet P W)
    (sem₁ sem₂ : P → W → Prop) :
    universalUpdate
      (universalUpdate cs F sem₁)
      (fiberwiseFilter F sem₁)
      sem₂ =
    universalUpdate cs F (λ p w => sem₁ p w ∧ sem₂ p w) := by
  funext w
  simp only [universalUpdate, universalProjection, fiberwiseFilter]
  exact propext ⟨
    λ ⟨⟨hcs, h₁⟩, h₂⟩ =>
      ⟨hcs, λ p hF => ⟨h₁ p hF, h₂ p ⟨hF, h₁ p hF⟩⟩⟩,
    λ ⟨hcs, hall⟩ =>
      ⟨⟨hcs, λ p hF => (hall p hF).1⟩,
       λ p ⟨hF, _⟩ => (hall p hF).2⟩⟩


-- ════════════════════════════════════════════════════════════════
-- § 7. Structural Properties
-- ════════════════════════════════════════════════════════════════

/-- ∃-projection is monotone in F: expanding available parameters
    can only add surviving worlds. -/
theorem existentialProjection_mono (F₁ F₂ : FragmentSet P W)
    (sem : P → W → Prop) (h : ∀ p w, F₁ p w → F₂ p w) (w : W) :
    existentialProjection F₁ sem w → existentialProjection F₂ sem w :=
  λ ⟨p, hF, hs⟩ => ⟨p, h p w hF, hs⟩

/-- ∀-projection is antitone in F: expanding available parameters
    can only remove surviving worlds (more to check). -/
theorem universalProjection_anti (F₁ F₂ : FragmentSet P W)
    (sem : P → W → Prop) (h : ∀ p w, F₁ p w → F₂ p w) (w : W) :
    universalProjection F₂ sem w → universalProjection F₁ sem w :=
  λ hall p hF₁ => hall p (h p w hF₁)

/-- ∃-update only removes worlds from the context set. -/
theorem existentialUpdate_restricts (cs : Prop' W) (F : FragmentSet P W)
    (sem : P → W → Prop) (w : W) :
    existentialUpdate cs F sem w → cs w :=
  And.left

/-- ∀-update only removes worlds from the context set. -/
theorem universalUpdate_restricts (cs : Prop' W) (F : FragmentSet P W)
    (sem : P → W → Prop) (w : W) :
    universalUpdate cs F sem w → cs w :=
  And.left

/-- Fiberwise filter only removes parameters. -/
theorem fiberwiseFilter_sub (F : FragmentSet P W) (sem : P → W → Prop)
    (p : P) (w : W) :
    fiberwiseFilter F sem p w → F p w :=
  And.left

/-- ∀-update implies ∃-update when the fiber is non-empty.
    Super-truth implies disjunctive survival. -/
theorem universalUpdate_implies_existentialUpdate (cs : Prop' W)
    (F : FragmentSet P W) (sem : P → W → Prop) (w : W)
    (h_ne : ∃ p, F p w) :
    universalUpdate cs F sem w → existentialUpdate cs F sem w :=
  λ ⟨hcs, hall⟩ => let ⟨p, hF⟩ := h_ne; ⟨hcs, p, hF, hall p hF⟩

/-- When F_w is a singleton {p₀}, both projections agree with
    a direct check of sem(p₀, w). No parameter uncertainty. -/
theorem singleton_projections_agree (p₀ : P) (sem : P → W → Prop) (w : W) :
    existentialProjection (λ p _ => p = p₀) sem w ↔
    universalProjection (λ p _ => p = p₀) sem w := by
  constructor
  · intro ⟨_, hp, hs⟩ p hp'; subst hp; subst hp'; exact hs
  · intro hall; exact ⟨p₀, rfl, hall p₀ rfl⟩

/-- Singleton ∃-update reduces to propositional filtering. -/
theorem existentialUpdate_singleton (cs : Prop' W) (p₀ : P)
    (sem : P → W → Prop) :
    existentialUpdate cs (λ p _ => p = p₀) sem =
    λ w => cs w ∧ sem p₀ w := by
  funext w
  simp only [existentialUpdate, existentialProjection]
  exact propext ⟨
    λ ⟨hcs, _, hp, hs⟩ => by subst hp; exact ⟨hcs, hs⟩,
    λ ⟨hcs, hs⟩ => ⟨hcs, p₀, rfl, hs⟩⟩

end Core.Semantics.ParameterizedUpdate
