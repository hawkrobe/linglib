import Linglib.Theories.Semantics.BSML.Enrichment

/-!
# BSML Free Choice Theorems
@cite{aloni-2022}

Pragmatic enrichment combined with split disjunction derives free choice
inferences. This module proves the core FC results from @cite{aloni-2022}
for arbitrary NE-free formulas.

## Key Results

| Result | Statement |
|--------|-----------|
| Modal Disjunction (Fact 3) | [α ∨ β]⁺ ⊨_S ◇α ∧ ◇β (NE-free α,β; R state-based) |
| Narrow Scope FC (Fact 4) | [◇(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β (NE-free α,β) |
| Wide Scope FC (Fact 5) | [◇α ∨ ◇β]⁺ ⊨ ◇α ∧ ◇β (NE-free α,β; R indisputable) |
| Dual Prohibition (Fact 11) | [¬◇(α ∨ β)]⁺ ⊨ ¬◇α ∧ ¬◇β (NE-free α,β) |
| Double Negation FC (Fact 12) | [¬¬◇(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β (NE-free α,β) |
| Negative FC failure (Fact 14) | ◇¬(α∧β) ⊭_{BSML+} ◇¬α; ¬□(α∧β) ⊭_{BSML+} ¬□α |

## Proof Architecture

Free choice is DERIVED from three independent principles:
1. **Split disjunction**: team is partitioned for ∨
2. **NE enrichment**: [·]⁺ adds non-emptiness constraints recursively
3. **NE non-flatness**: empty teams fail NE, so both parts must be non-empty
-/

namespace Semantics.BSML

variable {W : Type*} [DecidableEq W] [Fintype W]

-- ============================================================================
-- §1: Flatness
-- ============================================================================

/-- A team property is flat if it is downward closed under subset. -/
def isFlat (prop : Finset W → Prop) : Prop :=
  ∀ t t' : Finset W, t' ⊆ t → prop t → prop t'

/-- Atoms are flat. -/
theorem atom_is_flat (M : BSMLModel W) (p : String) :
    isFlat (λ t => support M (.atom p) t) :=
  fun _ _ hSub hSupp w hw => hSupp w (hSub hw)

/-- NE is NOT flat. -/
theorem ne_not_flat [Nonempty W] (M : BSMLModel W) :
    ¬isFlat (λ t => support M .ne t) := by
  intro hFlat
  have hFull : (Finset.univ : Finset W).Nonempty := Finset.univ_nonempty
  have := hFlat Finset.univ ∅ (Finset.empty_subset _) hFull
  exact Finset.not_nonempty_empty this

-- ============================================================================
-- §2: Narrow-scope Free Choice (Fact 4)
-- ============================================================================

/--
Narrow-scope Free Choice: [◇(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β (for NE-free α, β)

(Fact 4 from @cite{aloni-2022})

The enriched disjunction inside ◇ splits the accessible subteam into
two non-empty parts (by enrichment + NE). Each part supports its
respective disjunct (by `enrichment_strengthens_support`), and each
is a subset of R[w] (via the union), yielding ◇α and ◇β.
-/
theorem narrowScopeFC (M : BSMLModel W)
    (α β : BSMLFormula) (t : Finset W)
    (hα : α.isNEFree = true) (hβ : β.isNEFree = true)
    (h : support M (enrich (.poss (.disj α β))) t) :
    support M (.poss α) t ∧ support M (.poss β) t := by
  have hPoss := h.1
  constructor
  · intro w hw
    obtain ⟨s, hs_sub, _, hs_supp⟩ := hPoss w hw
    obtain ⟨s₁, s₂, hunion, h₁, _⟩ := hs_supp.1
    have hs₁ : s₁ ⊆ M.access w := (hunion ▸ Finset.subset_union_left).trans hs_sub
    exact ⟨s₁, hs₁, enriched_support_implies_nonempty M α s₁ h₁,
            enrichment_strengthens_support M α s₁ hα h₁⟩
  · intro w hw
    obtain ⟨s, hs_sub, _, hs_supp⟩ := hPoss w hw
    obtain ⟨s₁, s₂, hunion, _, h₂⟩ := hs_supp.1
    have hs₂ : s₂ ⊆ M.access w := (hunion ▸ Finset.subset_union_right).trans hs_sub
    exact ⟨s₂, hs₂, enriched_support_implies_nonempty M β s₂ h₂,
            enrichment_strengthens_support M β s₂ hβ h₂⟩

-- ============================================================================
-- §3: Wide-scope Free Choice (Fact 5)
-- ============================================================================

/--
Wide-scope Free Choice: [◇α ∨ ◇β]⁺ ⊨ ◇α ∧ ◇β (for NE-free α, β with
indisputable R)

(Fact 5 from @cite{aloni-2022})

The disjunction splits t = t₁ ∪ t₂. From t₁ pick w₁ — it has a subteam
s_a ⊆ R[w₁] supporting α. By indisputability R[w] = R[w₁] for all w ∈ t,
so s_a ⊆ R[w], yielding ◇α at every world. Symmetrically for β.
-/
theorem wideScopeFC (M : BSMLModel W)
    (α β : BSMLFormula) (t : Finset W)
    (hα : α.isNEFree = true) (hβ : β.isNEFree = true)
    (hInd : M.isIndisputable t)
    (h : support M (enrich (.disj (.poss α) (.poss β))) t) :
    support M (.poss α) t ∧ support M (.poss β) t := by
  obtain ⟨t₁, t₂, hunion, h₁, h₂⟩ := h.1
  -- Pick w₁ ∈ t₁, get subteam s_a ⊆ R[w₁] supporting enriched α
  obtain ⟨w₁, hw₁⟩ := enriched_support_implies_nonempty M (.poss α) t₁ h₁
  obtain ⟨s_a, hs_a_sub, hne_a, hs_a_supp⟩ := h₁.1 w₁ hw₁
  have hw₁_t : w₁ ∈ t := by rw [← hunion]; exact Finset.mem_union_left t₂ hw₁
  -- Pick w₂ ∈ t₂, get subteam s_b ⊆ R[w₂] supporting enriched β
  obtain ⟨w₂, hw₂⟩ := enriched_support_implies_nonempty M (.poss β) t₂ h₂
  obtain ⟨s_b, hs_b_sub, hne_b, hs_b_supp⟩ := h₂.1 w₂ hw₂
  have hw₂_t : w₂ ∈ t := by rw [← hunion]; exact Finset.mem_union_right t₁ hw₂
  constructor
  · -- ◇α: by indisputability, R[w] = R[w₁] for all w ∈ t
    intro w hw
    have heq := hInd w₁ hw₁_t w hw
    exact ⟨s_a, heq ▸ hs_a_sub, hne_a, enrichment_strengthens_support M α s_a hα hs_a_supp⟩
  · -- ◇β: symmetrically via w₂
    intro w hw
    have heq := hInd w₂ hw₂_t w hw
    exact ⟨s_b, heq ▸ hs_b_sub, hne_b, enrichment_strengthens_support M β s_b hβ hs_b_supp⟩

-- ============================================================================
-- §4: Modal Disjunction (Fact 3)
-- ============================================================================

/--
Modal Disjunction: [α ∨ β]⁺ ⊨_S ◇α ∧ ◇β (for NE-free α, β with state-based R)

(Fact 3 from @cite{aloni-2022})

Plain disjunction under enrichment, with state-based accessibility,
derives possibility of each disjunct — without needing ◇ in the formula.
The proof: enriched disjunction splits into two **non-empty** substates
(by enrichment + NE). By state-basedness R[w] = t, so each substate is
a non-empty subset of R[w], yielding ◇α and ◇β.
-/
theorem modalDisjunction (M : BSMLModel W)
    (α β : BSMLFormula) (t : Finset W)
    (hα : α.isNEFree = true) (hβ : β.isNEFree = true)
    (hSB : M.isStateBased t)
    (h : support M (enrich (.disj α β)) t) :
    support M (.poss α) t ∧ support M (.poss β) t := by
  -- Unpack enriched disjunction: t = t₁ ∪ t₂ with enriched support
  obtain ⟨t₁, t₂, hunion, h₁, h₂⟩ := h.1
  -- Enriched support → non-empty substates and original support
  have hne₁ := enriched_support_implies_nonempty M α t₁ h₁
  have hne₂ := enriched_support_implies_nonempty M β t₂ h₂
  have hα₁ := enrichment_strengthens_support M α t₁ hα h₁
  have hβ₂ := enrichment_strengthens_support M β t₂ hβ h₂
  -- Subset relations from the union
  have ht₁_sub : t₁ ⊆ t := hunion ▸ Finset.subset_union_left
  have ht₂_sub : t₂ ⊆ t := hunion ▸ Finset.subset_union_right
  constructor
  · -- ◇α: for each w ∈ t, R[w] = t (state-based), t₁ ⊆ t = R[w]
    intro w hw
    refine ⟨t₁, ?_, hne₁, hα₁⟩
    rw [hSB w hw]; exact ht₁_sub
  · -- ◇β: same argument with t₂
    intro w hw
    refine ⟨t₂, ?_, hne₂, hβ₂⟩
    rw [hSB w hw]; exact ht₂_sub

-- ============================================================================
-- §5: Dual Prohibition (Fact 11)
-- ============================================================================

/--
Dual Prohibition: [¬◇(α ∨ β)]⁺ ⊨ ¬◇α ∧ ¬◇β (for NE-free α, β)

(Fact 11 from @cite{aloni-2022})

Under negation, FC is correctly cancelled: the enriched prohibition
of the disjunction entails prohibition of each disjunct. The proof
strips enrichment from the anti-supported disjuncts using Fact 1
(`enrichment_strengthens_antiSupport`).
-/
theorem dualProhibition (M : BSMLModel W)
    (α β : BSMLFormula) (t : Finset W)
    (hα : α.isNEFree = true) (hβ : β.isNEFree = true)
    (h : support M (enrich (.neg (.poss (.disj α β)))) t) :
    support M (.neg (.poss α)) t ∧
    support M (.neg (.poss β)) t := by
  have hPoss := antiSupport_strip_ne M (.poss (enrich (.disj α β))) t h.1
  constructor
  · exact antiSupport_poss_weaken M _ _ t
      (fun t' h' =>
        let h_disj := antiSupport_strip_ne M (.disj (enrich α) (enrich β)) t' h'
        enrichment_strengthens_antiSupport M α t' hα h_disj.1) hPoss
  · exact antiSupport_poss_weaken M _ _ t
      (fun t' h' =>
        let h_disj := antiSupport_strip_ne M (.disj (enrich α) (enrich β)) t' h'
        enrichment_strengthens_antiSupport M β t' hβ h_disj.2) hPoss

-- ============================================================================
-- §6: Double Negation Free Choice (Fact 12)
-- ============================================================================

/--
Double Negation FC: [¬¬◇(α ∨ β)]⁺ ⊨ ◇α ∧ ◇β (for NE-free α, β)

(Fact 12 from @cite{aloni-2022})

Under double negation, FC effects re-emerge. Stripping the enrichment
around ¬ reveals `support M (enrich (◇(α∨β))) t` (by bilateral negation
swap), and narrow-scope FC (Fact 4) applies.
-/
theorem doubleNegationFC (M : BSMLModel W)
    (α β : BSMLFormula) (t : Finset W)
    (hα : α.isNEFree = true) (hβ : β.isNEFree = true)
    (h : support M (enrich (.neg (.neg (.poss (.disj α β))))) t) :
    support M (.poss α) t ∧ support M (.poss β) t := by
  have h_strip := antiSupport_strip_ne M
    (.neg (enrich (.poss (.disj α β)))) t h.1
  exact narrowScopeFC M α β t hα hβ h_strip

-- ============================================================================
-- §7: Negative Free Choice Failures (Fact 14)
-- ============================================================================

section NegativeFC

/--
Negative FC fails in BSML+ (Fact 14 from @cite{aloni-2022}).

In BSML* (where ∅ is excluded), ◇¬(α ∧ β) ⊨ ◇¬α. But in BSML+
(with pragmatic enrichment), this inference is NOT valid.

Counterexample: single world w where a=true, b=false, R[w]={w}, team={w}.
- [◇¬(a ∧ b)]⁺ holds: the split (∅, {w}) anti-supports a ∧ b
  (∅ vacuously anti-supports a, {w} anti-supports b since b(w)=false)
- [◇¬a]⁺ fails: the only accessible subteam {w} has a(w)=true,
  so no non-empty subteam anti-supports a
-/
private def negFCModel : BSMLModel Unit where
  access := fun _ => Finset.univ
  val := fun p _ => match p with
    | "a" => true
    | _ => false

private def negFCTeam : Finset Unit := Finset.univ

private def negFC_poss_premise : BSMLFormula :=
  .poss (.neg (.conj (.atom "a") (.atom "b")))

private def negFC_poss_conclusion : BSMLFormula :=
  .poss (.neg (.atom "a"))

/-- ◇¬(a ∧ b): enriched premise IS supported on the counterexample team. -/
theorem negFC_poss_premise_holds :
    support negFCModel (enrich negFC_poss_premise) negFCTeam := by
  decide

/-- ◇¬a: enriched conclusion is NOT supported on the counterexample team. -/
theorem negFC_poss_conclusion_fails :
    ¬support negFCModel (enrich negFC_poss_conclusion) negFCTeam := by
  decide

/-- Fact 14 (◇ version): ◇¬(α ∧ β) ⊭_{BSML+} ◇¬α.
    Negative FC does not hold under pragmatic enrichment. -/
theorem negativeFC_poss_fails_bsmlPlus :
    ¬consequencePlus (W := Unit)
      (.poss (.neg (.conj (.atom "a") (.atom "b"))))
      (.poss (.neg (.atom "a"))) := by
  intro h
  exact negFC_poss_conclusion_fails (h negFCModel negFCTeam negFC_poss_premise_holds)

private def negFC_nec_premise : BSMLFormula :=
  .neg (BSMLFormula.nec (.conj (.atom "a") (.atom "b")))

private def negFC_nec_conclusion : BSMLFormula :=
  .neg (BSMLFormula.nec (.atom "a"))

/-- ¬□(a ∧ b): enriched premise IS supported on the counterexample team. -/
theorem negFC_nec_premise_holds :
    support negFCModel (enrich negFC_nec_premise) negFCTeam := by
  decide

/-- ¬□a: enriched conclusion is NOT supported on the counterexample team. -/
theorem negFC_nec_conclusion_fails :
    ¬support negFCModel (enrich negFC_nec_conclusion) negFCTeam := by
  decide

/-- Fact 14 (□ version): ¬□(α ∧ β) ⊭_{BSML+} ¬□α.
    Negative FC with necessity also fails under pragmatic enrichment. -/
theorem negativeFC_nec_fails_bsmlPlus :
    ¬consequencePlus (W := Unit)
      (.neg (BSMLFormula.nec (.conj (.atom "a") (.atom "b"))))
      (.neg (BSMLFormula.nec (.atom "a"))) := by
  intro h
  exact negFC_nec_conclusion_fails (h negFCModel negFCTeam negFC_nec_premise_holds)

end NegativeFC

end Semantics.BSML
