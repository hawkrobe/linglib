import Linglib.Theories.Semantics.BSML.Defs

/-!
# BSML Classical Validities
@cite{aloni-2022}

BSML preserves several classical validities despite its non-classical
bilateral semantics. This module proves the key equivalences from
@cite{aloni-2022} and formalizes the non-classical properties of
bilateral negation.

## Key Results

| Result | Statement |
|--------|-----------|
| DNE (Fact 6) | ¬¬φ ≡ φ (already in Defs.lean) |
| Box-Diamond (Fact 6) | □φ ≡ ¬◇¬φ (definitional: □ is an abbreviation) |
| De Morgan (Fact 6) | ¬(φ ∧ ψ) ≡ ¬φ ∨ ¬ψ; ¬(φ ∨ ψ) ≡ ¬φ ∧ ¬ψ |
| Incompatibility (Fact 7) | s ⊨ ¬φ ⇒ s∩t=∅ for all t ⊨ φ |
| Replacement failure (Fact 8) | φ ≡ ψ ⇏ ¬φ ≡ ¬ψ (counterexample) |

Facts 6 proofs are definitional. Fact 7 connects to the philosophy of
negation as incompatibility. Fact 8 demonstrates NE's non-classical behavior.
-/

namespace Semantics.BSML

variable {W : Type*} [DecidableEq W] [Fintype W]

-- ============================================================================
-- §1: Box-Diamond Duality (Fact 6, @cite{aloni-2022})
-- ============================================================================

/-- Box-diamond duality (support): definitionally equal since □ := ¬◇¬. -/
theorem box_diamond_duality_support (M : BSMLModel W)
    (φ : BSMLFormula) (t : Finset W) :
    support M φ.nec t ↔ support M (.neg (.poss (.neg φ))) t := Iff.rfl

/-- Box-diamond duality (anti-support): definitionally equal. -/
theorem box_diamond_duality_antiSupport (M : BSMLModel W)
    (φ : BSMLFormula) (t : Finset W) :
    antiSupport M φ.nec t ↔ antiSupport M (.neg (.poss (.neg φ))) t := Iff.rfl

-- ============================================================================
-- §2: De Morgan Laws (Facts 6c, 6d)
-- ============================================================================

/-- De Morgan for conjunction (support): ¬(φ ∧ ψ) ≡ ¬φ ∨ ¬ψ.
    Both sides reduce to the same SPLIT existential. -/
theorem deMorgan_conj_support (M : BSMLModel W)
    (φ ψ : BSMLFormula) (t : Finset W) :
    support M (.neg (.conj φ ψ)) t ↔
    support M (.disj (.neg φ) (.neg ψ)) t := Iff.rfl

/-- De Morgan for conjunction (anti-support). -/
theorem deMorgan_conj_antiSupport (M : BSMLModel W)
    (φ ψ : BSMLFormula) (t : Finset W) :
    antiSupport M (.neg (.conj φ ψ)) t ↔
    antiSupport M (.disj (.neg φ) (.neg ψ)) t := Iff.rfl

/-- De Morgan for disjunction (support): ¬(φ ∨ ψ) ≡ ¬φ ∧ ¬ψ. -/
theorem deMorgan_disj_support (M : BSMLModel W)
    (φ ψ : BSMLFormula) (t : Finset W) :
    support M (.neg (.disj φ ψ)) t ↔
    support M (.conj (.neg φ) (.neg ψ)) t := Iff.rfl

/-- De Morgan for disjunction (anti-support). -/
theorem deMorgan_disj_antiSupport (M : BSMLModel W)
    (φ ψ : BSMLFormula) (t : Finset W) :
    antiSupport M (.neg (.disj φ ψ)) t ↔
    antiSupport M (.conj (.neg φ) (.neg ψ)) t := Iff.rfl

-- ============================================================================
-- §3: Equivalence Theorems
-- ============================================================================

/-- DNE is a full bilateral equivalence. -/
theorem dne_equivalent (φ : BSMLFormula) :
    equivalent (W := W) (.neg (.neg φ)) φ :=
  fun _ _ => ⟨Iff.rfl, Iff.rfl⟩

/-- Box-diamond duality is a full bilateral equivalence. -/
theorem box_diamond_equivalent (φ : BSMLFormula) :
    equivalent (W := W) φ.nec (.neg (.poss (.neg φ))) :=
  fun _ _ => ⟨Iff.rfl, Iff.rfl⟩

/-- De Morgan for conjunction is a full bilateral equivalence. -/
theorem deMorgan_conj_equivalent (φ ψ : BSMLFormula) :
    equivalent (W := W) (.neg (.conj φ ψ)) (.disj (.neg φ) (.neg ψ)) :=
  fun _ _ => ⟨Iff.rfl, Iff.rfl⟩

/-- De Morgan for disjunction is a full bilateral equivalence. -/
theorem deMorgan_disj_equivalent (φ ψ : BSMLFormula) :
    equivalent (W := W) (.neg (.disj φ ψ)) (.conj (.neg φ) (.neg ψ)) :=
  fun _ _ => ⟨Iff.rfl, Iff.rfl⟩

-- ============================================================================
-- §4: Negation and Incompatibility (Fact 7)
-- ============================================================================

/-- Core incompatibility: anti-support and support cannot overlap at any world.
    This is the engine behind Fact 7 — proved by structural induction on φ. -/
private theorem support_antiSupport_incompatible (M : BSMLModel W)
    (φ : BSMLFormula) :
    ∀ (s t : Finset W),
      antiSupport M φ s → support M φ t →
      ∀ w, w ∈ s → w ∉ t := by
  induction φ with
  | atom p =>
    intro s t hs ht w hsw htw
    have := hs w hsw; have := ht w htw
    simp_all
  | ne =>
    intro s _ hs _ w hsw
    rw [hs] at hsw; exact absurd hsw (by simp)
  | neg ψ ih =>
    intro s t hs ht w hsw htw
    exact ih t s ht hs w htw hsw
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    intro s t hs ht w hsw htw
    obtain ⟨s₁, s₂, hunion, h₁, h₂⟩ := hs
    have hw_union : w ∈ s₁ ∪ s₂ := hunion ▸ hsw
    rcases Finset.mem_union.mp hw_union with h | h
    · exact ih₁ s₁ t h₁ ht.1 w h htw
    · exact ih₂ s₂ t h₂ ht.2 w h htw
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    intro s t hs ht w hsw htw
    obtain ⟨t₁, t₂, hunion, h₁, h₂⟩ := ht
    have hw_union : w ∈ t₁ ∪ t₂ := hunion ▸ htw
    rcases Finset.mem_union.mp hw_union with h | h
    · exact ih₁ s t₁ hs.1 h₁ w hsw h
    · exact ih₂ s t₂ hs.2 h₂ w hsw h
  | poss ψ ih =>
    intro s t hs ht w hsw htw
    have h_anti := hs w hsw
    obtain ⟨s', hs'_sub, hs'_ne, hs'_supp⟩ := ht w htw
    obtain ⟨v, hv_s'⟩ := hs'_ne
    have hv_acc := hs'_sub (Finset.mem_coe.mpr hv_s')
    exact ih (M.access w) s' h_anti hs'_supp v hv_acc hv_s'

/--
Negation and incompatibility (Fact 7 from @cite{aloni-2022}).

If s supports ¬φ, then s and any t supporting φ are disjoint.
-/
theorem negation_incompatibility (M : BSMLModel W)
    (φ : BSMLFormula) (s t : Finset W)
    (hs : support M (.neg φ) s) (ht : support M φ t) :
    Disjoint s t := by
  rw [Finset.disjoint_left]
  exact support_antiSupport_incompatible M φ s t hs ht

-- ============================================================================
-- §5: Failure of Replacement under Negation (Fact 8)
-- ============================================================================

/--
Failure of replacement under negation (Fact 8 from @cite{aloni-2022}).

In BSML, φ ≡ ψ does NOT imply ¬φ ≡ ¬ψ. Counterexample: ⊥₁ = p ∧ ¬p
and ⊥₂ = ¬NE are equivalent, but ¬⊥₁ ≠ ¬⊥₂.
-/
theorem replacement_failure_counterexample :
    ∃ (W : Type) (_ : DecidableEq W) (_ : Fintype W)
      (M : BSMLModel W) (t : Finset W),
      (support M (.conj (.atom "p") (.neg (.atom "p"))) t ↔
       support M (.neg .ne) t) ∧
      ¬(support M (.neg (.conj (.atom "p") (.neg (.atom "p")))) t ↔
        support M (.neg (.neg .ne)) t) := by
  refine ⟨Bool, inferInstance, inferInstance,
    ⟨λ _ => Finset.univ, λ _ _ => true⟩, ∅, ?_, ?_⟩
  · -- Both sides True (vacuous on ∅): p∧¬p and ¬NE both hold on ∅
    exact ⟨fun _ => rfl,
           fun _ => ⟨fun w hw => absurd hw (by simp),
                     fun w hw => absurd hw (by simp)⟩⟩
  · -- LHS = antiSupport(.conj p ¬p) ∅ = True (trivial split ∅,∅)
    -- RHS = support .ne ∅ = ∅.Nonempty = False
    intro h
    have : (∅ : Finset Bool).Nonempty := h.mp
      ⟨∅, ∅, by simp,
       fun w hw => absurd hw (by simp),
       fun w hw => absurd hw (by simp)⟩
    exact Finset.not_nonempty_empty this

end Semantics.BSML
