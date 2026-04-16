import Linglib.Theories.Semantics.BSML.Defs

/-!
# BSML Pragmatic Enrichment
@cite{aloni-2022}

Pragmatic enrichment [·]⁺ (Definition 6) adds non-emptiness constraints
recursively to every subformula, capturing the "neglect-zero" tendency
in human cognition: speakers/hearers ignore empty witness sets.

## Key Properties

- **Fact 1**: Enrichment strengthens — [α]⁺ ⊨ α (support + anti-support) for NE-free α
- **Fact 2**: Enriched formula entails original plus NE — [α]⁺ ⊨ α ∧ NE for NE-free α
- **Fact 9**: Enrichment vacuous under single negation — ¬[α]⁺ ≡ ¬α for positive α
- **Fact 10**: Enrichment NOT vacuous under double negation — ¬¬[p]⁺ ≢ ¬¬p

## Architecture

Enrichment is the bridge between BSML's split disjunction (a semantic
mechanism) and free choice (a pragmatic inference). The enrichment function
transforms a formula so that empty teams are excluded at every level, and
the combination with split disjunction forces both disjuncts to have
non-empty witnesses — yielding free choice.
-/

namespace Semantics.BSML

variable {W : Type*} [DecidableEq W] [Fintype W]

-- ============================================================================
-- §1: Pragmatic Enrichment (Definition 6)
-- ============================================================================

/--
Pragmatic enrichment [·]⁺ (Definition 6 from @cite{aloni-2022}).

Recursively adds non-emptiness constraints at every level:
- `[p]⁺ = p ∧ NE`
- `[NE]⁺ = NE`
- `[¬φ]⁺ = ¬[φ]⁺ ∧ NE`
- `[φ ∧ ψ]⁺ = ([φ]⁺ ∧ [ψ]⁺) ∧ NE`
- `[φ ∨ ψ]⁺ = ([φ]⁺ ∨ [ψ]⁺) ∧ NE`
- `[◇φ]⁺ = ◇[φ]⁺ ∧ NE`
- `[□φ]⁺ = □[φ]⁺ ∧ NE`
-/
def enrich : BSMLFormula → BSMLFormula
  | .atom p => .conj (.atom p) .ne
  | .ne => .ne
  | .neg φ => .conj (.neg (enrich φ)) .ne
  | .conj φ ψ => .conj (.conj (enrich φ) (enrich ψ)) .ne
  | .disj φ ψ => .conj (.disj (enrich φ) (enrich ψ)) .ne
  | .poss φ => .conj (.poss (enrich φ)) .ne

-- ============================================================================
-- §2: Structure Lemmas
-- ============================================================================

theorem enrich_neg_structure (φ : BSMLFormula) :
    enrich (.neg φ) = .conj (.neg (enrich φ)) .ne := rfl

theorem enrich_conj_structure (φ ψ : BSMLFormula) :
    enrich (.conj φ ψ) = .conj (.conj (enrich φ) (enrich ψ)) .ne := rfl

theorem enrich_disj_structure (φ ψ : BSMLFormula) :
    enrich (.disj φ ψ) = .conj (.disj (enrich φ) (enrich ψ)) .ne := rfl

theorem enrich_poss_structure (φ : BSMLFormula) :
    enrich (.poss φ) = .conj (.poss (enrich φ)) .ne := rfl

-- ============================================================================
-- §3: Enriched Support Implies Non-emptiness
-- ============================================================================

/-- If an enriched formula is supported, the team is non-empty. -/
theorem enriched_support_implies_nonempty (M : BSMLModel W)
    (φ : BSMLFormula) (t : Finset W)
    (h : support M (enrich φ) t) : t.Nonempty := by
  cases φ with
  | ne => exact h
  | _ => exact h.2

-- ============================================================================
-- §4: Core Split Lemma
-- ============================================================================

/-- If disjunction is supported, there exists a split where both parts
    support their disjuncts. -/
theorem split_exists (M : BSMLModel W)
    (φ ψ : BSMLFormula) (t : Finset W)
    (h : support M (.disj φ ψ) t) :
    ∃ t₁ t₂ : Finset W, support M φ t₁ ∧ support M ψ t₂ := by
  obtain ⟨t₁, t₂, _, h₁, h₂⟩ := h
  exact ⟨t₁, t₂, h₁, h₂⟩

/-- Enriched disjunction forces both parts of split to be non-empty. -/
theorem enriched_split_forces_both_nonempty (M : BSMLModel W)
    (φ ψ : BSMLFormula) (t : Finset W)
    (h : support M (.disj (enrich φ) (enrich ψ)) t) :
    ∃ t₁ t₂ : Finset W,
      t₁.Nonempty ∧ t₂.Nonempty ∧
      support M (enrich φ) t₁ ∧ support M (enrich ψ) t₂ := by
  obtain ⟨t₁, t₂, _, h₁, h₂⟩ := h
  exact ⟨t₁, t₂,
    enriched_support_implies_nonempty M φ t₁ h₁,
    enriched_support_implies_nonempty M ψ t₂ h₂,
    h₁, h₂⟩

-- ============================================================================
-- §5: Anti-support of (φ ∧ NE) stripping
-- ============================================================================

/-- Anti-support of (φ ∧ NE) implies anti-support of φ.
    From the SPLIT, one part anti-supports φ and the other (anti-supporting NE)
    is empty, so the first part is the whole team. -/
theorem antiSupport_strip_ne (M : BSMLModel W)
    (φ : BSMLFormula) (t : Finset W)
    (h : antiSupport M (.conj φ .ne) t) :
    antiSupport M φ t := by
  obtain ⟨t₁, t₂, hunion, h₁, h₂⟩ := h
  -- h₂ : t₂ = ∅, so t₁ = t
  subst h₂; simp at hunion; subst hunion; exact h₁

/-- Anti-support of φ implies anti-support of (φ ∧ NE).
    Use the trivial split (t, ∅). -/
theorem antiSupport_conj_ne_of_antiSupport (M : BSMLModel W)
    (φ : BSMLFormula) (t : Finset W)
    (h : antiSupport M φ t) :
    antiSupport M (.conj φ .ne) t :=
  ⟨t, ∅, by simp, h, rfl⟩

/-- Anti-support of (φ ∧ NE) ↔ anti-support of φ. -/
theorem antiSupport_conj_ne_iff (M : BSMLModel W)
    (φ : BSMLFormula) (t : Finset W) :
    antiSupport M (.conj φ .ne) t ↔ antiSupport M φ t :=
  ⟨antiSupport_strip_ne M φ t, antiSupport_conj_ne_of_antiSupport M φ t⟩

-- ============================================================================
-- §6: Anti-support Monotonicity
-- ============================================================================

/-- Anti-support monotonicity for ◇: if antiSupport of φ implies antiSupport of ψ
    for all teams, then ◇φ anti-support implies ◇ψ anti-support. -/
theorem antiSupport_poss_weaken (M : BSMLModel W)
    (φ ψ : BSMLFormula) (t : Finset W)
    (hmono : ∀ t' : Finset W, antiSupport M φ t' → antiSupport M ψ t')
    (h : antiSupport M (.poss φ) t) :
    antiSupport M (.poss ψ) t :=
  fun w hw => hmono _ (h w hw)

-- ============================================================================
-- §7: Enrichment Strengthens (Fact 1)
-- ============================================================================

/-- Both directions of Fact 1 (enrichment strengthens), proved by simultaneous
    induction on formula structure. -/
private theorem enrichment_strengthens_both (M : BSMLModel W)
    (φ : BSMLFormula) (hNE : φ.isNEFree = true) :
    (∀ t, support M (enrich φ) t → support M φ t) ∧
    (∀ t, antiSupport M (enrich φ) t → antiSupport M φ t) := by
  induction φ with
  | ne => simp [BSMLFormula.isNEFree] at hNE
  | atom p =>
    exact ⟨fun t h => h.1, fun t h => antiSupport_strip_ne M (.atom p) t h⟩
  | neg ψ ih =>
    have ⟨ih_s, ih_a⟩ := ih (by simp [BSMLFormula.isNEFree] at hNE; exact hNE)
    exact ⟨fun t h => ih_a t h.1, fun t h => ih_s t (antiSupport_strip_ne M _ t h)⟩
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    have hψ₁ : ψ₁.isNEFree = true := by
      simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.1
    have hψ₂ : ψ₂.isNEFree = true := by
      simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.2
    have ⟨ih₁_s, ih₁_a⟩ := ih₁ hψ₁
    have ⟨ih₂_s, ih₂_a⟩ := ih₂ hψ₂
    constructor
    · intro t h; exact ⟨ih₁_s t h.1.1, ih₂_s t h.1.2⟩
    · intro t h
      have h' := antiSupport_strip_ne M (.conj (enrich ψ₁) (enrich ψ₂)) t h
      obtain ⟨s₁, s₂, hunion, h₁, h₂⟩ := h'
      exact ⟨s₁, s₂, hunion, ih₁_a s₁ h₁, ih₂_a s₂ h₂⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    have hψ₁ : ψ₁.isNEFree = true := by
      simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.1
    have hψ₂ : ψ₂.isNEFree = true := by
      simp only [BSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.2
    have ⟨ih₁_s, ih₁_a⟩ := ih₁ hψ₁
    have ⟨ih₂_s, ih₂_a⟩ := ih₂ hψ₂
    constructor
    · intro t h
      obtain ⟨s₁, s₂, hunion, h₁, h₂⟩ := h.1
      exact ⟨s₁, s₂, hunion, ih₁_s s₁ h₁, ih₂_s s₂ h₂⟩
    · intro t h
      have h' := antiSupport_strip_ne M (.disj (enrich ψ₁) (enrich ψ₂)) t h
      exact ⟨ih₁_a t h'.1, ih₂_a t h'.2⟩
  | poss ψ ih =>
    have ⟨ih_s, ih_a⟩ := ih (by simp [BSMLFormula.isNEFree] at hNE; exact hNE)
    constructor
    · intro t h w hw
      obtain ⟨s, hs, hne, hsupp⟩ := h.1 w hw
      exact ⟨s, hs, hne, ih_s s hsupp⟩
    · intro t h
      have h' := antiSupport_strip_ne M (.poss (enrich ψ)) t h
      exact fun w hw => ih_a _ (h' w hw)

/--
Enrichment strengthens: [α]⁺ ⊨ α (Fact 1 from @cite{aloni-2022}).

For NE-free α, if a team supports the enriched formula [α]⁺, it also
supports the original α.
-/
theorem enrichment_strengthens_support (M : BSMLModel W)
    (φ : BSMLFormula) (t : Finset W)
    (hNE : φ.isNEFree = true)
    (h : support M (enrich φ) t) :
    support M φ t :=
  (enrichment_strengthens_both M φ hNE).1 t h

/-- Enrichment strengthens (anti-support direction of Fact 1). -/
theorem enrichment_strengthens_antiSupport (M : BSMLModel W)
    (φ : BSMLFormula) (t : Finset W)
    (hNE : φ.isNEFree = true)
    (h : antiSupport M (enrich φ) t) :
    antiSupport M φ t :=
  (enrichment_strengthens_both M φ hNE).2 t h

-- ============================================================================
-- §8: Enrichment Entails Original Plus NE (Fact 2)
-- ============================================================================

/--
Fact 2 from @cite{aloni-2022}: [α]⁺ ⊨ α ∧ NE for NE-free α.
-/
theorem enrichment_entails_conj_ne (M : BSMLModel W)
    (φ : BSMLFormula) (t : Finset W)
    (hNE : φ.isNEFree = true)
    (h : support M (enrich φ) t) :
    support M (.conj φ .ne) t :=
  ⟨enrichment_strengthens_support M φ t hNE h,
   enriched_support_implies_nonempty M φ t h⟩

-- ============================================================================
-- §9: Enrichment Vacuous Under Single Negation (Fact 9)
-- ============================================================================

/--
Pragmatic enrichment is vacuous under single negation for positive formulas
(Fact 9 from @cite{aloni-2022}).

For positive α (no negation): ¬[α]⁺ ≡ ¬α (both support and anti-support).
-/
theorem enrichment_vacuous_under_negation (M : BSMLModel W)
    (φ : BSMLFormula) (t : Finset W)
    (hPos : φ.isPositive = true) :
    antiSupport M (enrich φ) t ↔ antiSupport M φ t := by
  induction φ generalizing t with
  | atom p => exact antiSupport_conj_ne_iff M (.atom p) t
  | ne => exact Iff.rfl
  | neg _ => simp [BSMLFormula.isPositive] at hPos
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    simp only [BSMLFormula.isPositive, Bool.and_eq_true] at hPos
    simp only [enrich]
    rw [antiSupport_conj_ne_iff]
    show (∃ t₁ t₂, t₁ ∪ t₂ = t ∧ antiSupport M (enrich ψ₁) t₁ ∧
          antiSupport M (enrich ψ₂) t₂) ↔
         (∃ t₁ t₂, t₁ ∪ t₂ = t ∧ antiSupport M ψ₁ t₁ ∧ antiSupport M ψ₂ t₂)
    constructor
    · rintro ⟨t₁, t₂, hu, h₁, h₂⟩
      exact ⟨t₁, t₂, hu, (ih₁ t₁ hPos.1).mp h₁, (ih₂ t₂ hPos.2).mp h₂⟩
    · rintro ⟨t₁, t₂, hu, h₁, h₂⟩
      exact ⟨t₁, t₂, hu, (ih₁ t₁ hPos.1).mpr h₁, (ih₂ t₂ hPos.2).mpr h₂⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    simp only [BSMLFormula.isPositive, Bool.and_eq_true] at hPos
    simp only [enrich]
    rw [antiSupport_conj_ne_iff]
    show antiSupport M (enrich ψ₁) t ∧ antiSupport M (enrich ψ₂) t ↔
         antiSupport M ψ₁ t ∧ antiSupport M ψ₂ t
    exact ⟨fun ⟨h₁, h₂⟩ => ⟨(ih₁ t hPos.1).mp h₁, (ih₂ t hPos.2).mp h₂⟩,
           fun ⟨h₁, h₂⟩ => ⟨(ih₁ t hPos.1).mpr h₁, (ih₂ t hPos.2).mpr h₂⟩⟩
  | poss ψ ih =>
    simp only [BSMLFormula.isPositive] at hPos
    simp only [enrich]
    rw [antiSupport_conj_ne_iff]
    show (∀ w ∈ t, antiSupport M (enrich ψ) (M.access w)) ↔
         (∀ w ∈ t, antiSupport M ψ (M.access w))
    exact ⟨fun h w hw => (ih _ hPos).mp (h w hw),
           fun h w hw => (ih _ hPos).mpr (h w hw)⟩

/-- Fact 9, support direction: support M (.neg (enrich φ)) t ↔ support M (.neg φ) t. -/
theorem enrichment_vacuous_under_negation_support (M : BSMLModel W)
    (φ : BSMLFormula) (t : Finset W)
    (hPos : φ.isPositive = true) :
    support M (.neg (enrich φ)) t ↔ support M (.neg φ) t :=
  enrichment_vacuous_under_negation M φ t hPos

-- ============================================================================
-- §10: BSML+ Consequence (enriched formulas)
-- ============================================================================

/-- BSML+ consequence: consequence between enriched formulas.
    α ⊨_{BSML+} β iff [α]⁺ ⊨_{BSML} [β]⁺ (@cite{aloni-2022} §6.3.1). -/
def consequencePlus (φ ψ : BSMLFormula) : Prop :=
  ∀ (M : BSMLModel W) (t : Finset W), support M (enrich φ) t → support M (enrich ψ) t

-- ============================================================================
-- §11: BSML* ↔ BSML+ for Classical Positive Formulas (Fact 13)
-- ============================================================================

/-- A formula is classical positive: no NE atom and no negation.
    These are the formulas for which BSML* and BSML+ consequence coincide
    (@cite{aloni-2022} Fact 13). -/
def BSMLFormula.isClassicalPositive (φ : BSMLFormula) : Bool :=
  φ.isNEFree && φ.isPositive

/-- For classical positive formulas, enriched support is equivalent to BSML*
    support plus non-emptiness. The key insight is that enrichment adds NE at
    every level, which exactly matches BSML*'s exclusion of ∅ from all
    intermediate states (including disjunction splits). -/
private theorem enriched_iff_star_nonempty (M : BSMLModel W)
    (φ : BSMLFormula) (t : Finset W)
    (hCP : φ.isClassicalPositive = true) :
    support M (enrich φ) t ↔ supportStar M φ t ∧ t.Nonempty := by
  induction φ generalizing t with
  | ne => simp [BSMLFormula.isClassicalPositive, BSMLFormula.isNEFree] at hCP
  | neg _ => simp [BSMLFormula.isClassicalPositive, BSMLFormula.isPositive] at hCP
  | atom _ => exact Iff.rfl
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    have hψ₁ : ψ₁.isClassicalPositive = true := by
      simp only [BSMLFormula.isClassicalPositive, BSMLFormula.isNEFree,
                  BSMLFormula.isPositive, Bool.and_eq_true] at hCP ⊢
      exact ⟨hCP.1.1, hCP.2.1⟩
    have hψ₂ : ψ₂.isClassicalPositive = true := by
      simp only [BSMLFormula.isClassicalPositive, BSMLFormula.isNEFree,
                  BSMLFormula.isPositive, Bool.and_eq_true] at hCP ⊢
      exact ⟨hCP.1.2, hCP.2.2⟩
    simp only [enrich, support, eval, supportStar]
    constructor
    · intro ⟨⟨h₁, h₂⟩, hne⟩
      exact ⟨⟨((ih₁ t hψ₁).mp h₁).1, ((ih₂ t hψ₂).mp h₂).1⟩, hne⟩
    · intro ⟨⟨h₁, h₂⟩, hne⟩
      exact ⟨⟨(ih₁ t hψ₁).mpr ⟨h₁, hne⟩, (ih₂ t hψ₂).mpr ⟨h₂, hne⟩⟩, hne⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    have hψ₁ : ψ₁.isClassicalPositive = true := by
      simp only [BSMLFormula.isClassicalPositive, BSMLFormula.isNEFree,
                  BSMLFormula.isPositive, Bool.and_eq_true] at hCP ⊢
      exact ⟨hCP.1.1, hCP.2.1⟩
    have hψ₂ : ψ₂.isClassicalPositive = true := by
      simp only [BSMLFormula.isClassicalPositive, BSMLFormula.isNEFree,
                  BSMLFormula.isPositive, Bool.and_eq_true] at hCP ⊢
      exact ⟨hCP.1.2, hCP.2.2⟩
    simp only [enrich, support, eval, supportStar]
    constructor
    · intro ⟨⟨t₁, t₂, hu, h₁, h₂⟩, hne⟩
      have ⟨hs₁, hne₁⟩ := (ih₁ t₁ hψ₁).mp h₁
      have ⟨hs₂, hne₂⟩ := (ih₂ t₂ hψ₂).mp h₂
      exact ⟨⟨t₁, t₂, hu, hne₁, hne₂, hs₁, hs₂⟩, hne⟩
    · intro ⟨⟨t₁, t₂, hu, hne₁, hne₂, hs₁, hs₂⟩, hne⟩
      exact ⟨⟨t₁, t₂, hu, (ih₁ t₁ hψ₁).mpr ⟨hs₁, hne₁⟩,
              (ih₂ t₂ hψ₂).mpr ⟨hs₂, hne₂⟩⟩, hne⟩
  | poss ψ ih =>
    have hψ : ψ.isClassicalPositive = true := by
      simp only [BSMLFormula.isClassicalPositive, BSMLFormula.isNEFree,
                  BSMLFormula.isPositive] at hCP; exact hCP
    simp only [enrich, support, eval, supportStar]
    constructor
    · intro ⟨hposs, hne⟩
      refine ⟨fun w hw => ?_, hne⟩
      obtain ⟨s, hs, hne_s, hsupp⟩ := hposs w hw
      exact ⟨s, hs, hne_s, ((ih s hψ).mp hsupp).1⟩
    · intro ⟨hposs, hne⟩
      refine ⟨fun w hw => ?_, hne⟩
      obtain ⟨s, hs, hne_s, hstar⟩ := hposs w hw
      exact ⟨s, hs, hne_s, (ih s hψ).mpr ⟨hstar, hne_s⟩⟩

/--
For classical positive formulas, BSML* and BSML+ consequence coincide
(Fact 13 from @cite{aloni-2022}).

If we restrict to positive formulas without NE or ¬, then ruling out the
empty state syntactically (via [·]⁺ enrichment) is equivalent to ruling
it out model-theoretically (via BSML* non-empty restriction).
-/
theorem bsmlStar_iff_bsmlPlus (φ ψ : BSMLFormula)
    (hφ : φ.isClassicalPositive = true) (hψ : ψ.isClassicalPositive = true) :
    consequenceStar (W := W) φ ψ ↔ consequencePlus (W := W) φ ψ := by
  constructor
  · intro hStar M t hEnrich
    have ⟨hφ_star, hne⟩ := (enriched_iff_star_nonempty M φ t hφ).mp hEnrich
    exact (enriched_iff_star_nonempty M ψ t hψ).mpr ⟨hStar M t hne hφ_star, hne⟩
  · intro hPlus M t hne hφ_star
    have hEnrich := (enriched_iff_star_nonempty M φ t hφ).mpr ⟨hφ_star, hne⟩
    exact ((enriched_iff_star_nonempty M ψ t hψ).mp (hPlus M t hEnrich)).1

-- ============================================================================
-- §12: Enrichment Not Vacuous Under Double Negation (Fact 10)
-- ============================================================================

/--
Pragmatic enrichment is NOT vacuous under double negation
(Fact 10 from @cite{aloni-2022}).

While Fact 9 shows ¬[α]⁺ ≡ ¬α for positive α (enrichment is vacuous under
single negation), under **double** negation enrichment has a non-trivial effect:
`¬¬[p]⁺ = ¬¬(p ∧ NE) = p ∧ NE ≢ p = ¬¬p`.

The counterexample is the empty team: ∅ vacuously supports p but does not
support p ∧ NE (the NE conjunct fails).
-/
theorem enrichment_not_vacuous_under_double_negation :
    ∃ (W : Type) (_ : DecidableEq W) (_ : Fintype W)
      (M : BSMLModel W) (t : Finset W),
      -- ¬¬p holds on ∅ (by DNE, = vacuous support of p)
      support M (.neg (.neg (.atom "p"))) t ∧
      -- but ¬¬[p]⁺ fails on ∅ (= p ∧ NE requires non-emptiness)
      ¬support M (.neg (.neg (enrich (.atom "p")))) t := by
  refine ⟨Bool, inferInstance, inferInstance,
    ⟨fun _ => Finset.univ, fun _ _ => true⟩, ∅, ?_, ?_⟩
  · -- support M (¬¬p) ∅ = support M p ∅ = vacuously true
    intro w hw; exact absurd hw (by simp)
  · -- ¬support M (¬¬(p ∧ NE)) ∅ = ¬(∅.Nonempty) (NE fails on ∅)
    intro h; exact Finset.not_nonempty_empty h.2

end Semantics.BSML
