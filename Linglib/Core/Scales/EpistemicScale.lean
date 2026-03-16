import Linglib.Core.Scales.EpistemicScale.Defs
import Linglib.Core.Scales.EpistemicScale.Entailments
import Linglib.Core.Scales.EpistemicScale.Representability
import Linglib.Core.Scales.EpistemicScale.Cancellation88

/-!
# Epistemic Comparative Likelihood — Main Theorems

@cite{holliday-icard-2013} @cite{halpern-2003} @cite{kraft-pratt-seidenberg-1959} @cite{van-der-hoek-1996}

Re-exports `EpistemicScale.Defs` (axioms, structures, semantics),
`EpistemicScale.Representability` (KPS counterexample, Fin 0–3 proofs),
and `EpistemicScale.Cancellation88` (Fin 4 via Scott cancellation),
then states the top-level KPS theorems (8a, 8b) and completeness results.
-/

namespace Core.Scale

-- ── Theorem 8 (Kraft, @cite{kraft-pratt-seidenberg-1959}) ───

set_option maxHeartbeats 1600000 in
/-- **Theorem 8a**: for |W| < 5,
    every FA model is representable by a finitely additive probability
    measure. Below 5 worlds, the logics FA and FP∞ coincide.

    The proof transfers an arbitrary `Fintype W` to `Fin n` via
    `Fintype.equivFin`, applies the per-cardinality proof for n ∈ {0,1,2,3,4},
    and transports the resulting measure back. -/
theorem theorem8a {W : Type*} [Fintype W]
    (sys : EpistemicSystemFA W) (hcard : Fintype.card W < 5) :
    ∃ (m : FinAddMeasure W), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  haveI : DecidableEq W := Classical.typeDecidableEq W
  let e := Fintype.equivFin W
  set n := Fintype.card W with hn_def
  interval_cases n
  · -- n = 0: impossible
    exfalso
    have : (∅ : Set (Fin 0)) = Set.univ := by ext x; exact Fin.elim0 x
    exact (transportFA e sys).nonTrivial (this ▸ (transportFA e sys).refl ∅)
  · -- n = 1
    obtain ⟨m', hm'⟩ := theorem8a_fin1 (transportFA e sys)
    exact ⟨transportMeasure e m', transfer_repr e sys m' hm'⟩
  · -- n = 2
    obtain ⟨m', hm'⟩ := theorem8a_fin2 (transportFA e sys)
    exact ⟨transportMeasure e m', transfer_repr e sys m' hm'⟩
  · -- n = 3
    obtain ⟨m', hm'⟩ := theorem8a_fin3 (transportFA e sys)
    exact ⟨transportMeasure e m', transfer_repr e sys m' hm'⟩
  · -- n = 4
    obtain ⟨m', hm'⟩ := theorem8a_fin4 (transportFA e sys)
    exact ⟨transportMeasure e m', transfer_repr e sys m' hm'⟩

/-- **Theorem 8b**: for |W| ≥ 5,
    FA is strictly weaker than FP∞ — there exists a 5-element type
    with an FA ordering admitting no finitely additive measure
    representation. -/
theorem theorem8b :
    ∃ (W : Type) (_ : Fintype W) (sys : EpistemicSystemFA W),
      Fintype.card W = 5 ∧
      ¬∃ (m : FinAddMeasure W), ∀ A B, sys.ge A B ↔ m.inducedGe A B :=
  ⟨Fin 5, inferInstance, kpsSystemFA, Fintype.card_fin 5, kps_not_representable⟩

-- ── Completeness (Theorems 2 and 6) ─────────────

attribute [local instance] Classical.propDecidable

/-- Count of finsets dominated by A under the ge ordering. -/
private noncomputable def belowCount {W : Type*} [Fintype W]
    (sys : EpistemicSystemFA W) (A : Set W) : ℕ :=
  (Finset.univ.filter (fun S : Finset W => sys.ge A ↑S)).card

private theorem belowCount_univ {W : Type*} [Fintype W]
    (sys : EpistemicSystemFA W) :
    belowCount sys Set.univ = Fintype.card (Finset W) := by
  unfold belowCount
  rw [Finset.filter_true_of_mem]
  · exact Finset.card_univ
  · intro S _; exact sys.mono _ _ (Set.subset_univ _)

private theorem belowCount_mono {W : Type*} [Fintype W]
    (sys : EpistemicSystemFA W) (A B : Set W)
    (h : sys.ge A B) : belowCount sys A ≥ belowCount sys B := by
  unfold belowCount
  apply Finset.card_le_card
  intro S hS
  rw [Finset.mem_filter] at hS ⊢
  exact ⟨hS.1, sys.trans _ _ _ h hS.2⟩

private theorem belowCount_strict {W : Type*} [Fintype W]
    (sys : EpistemicSystemFA W) (A B : Set W)
    (h : ¬sys.ge A B) : belowCount sys A < belowCount sys B := by
  unfold belowCount
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro S hS
    rw [Finset.mem_filter] at hS ⊢
    have hBA := (sys.total A B).resolve_left h
    exact ⟨hS.1, sys.trans _ _ _ hBA hS.2⟩
  · intro hsub
    have : B.toFinset ∈ Finset.univ.filter (fun S : Finset W => sys.ge A ↑S) :=
      hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [Set.coe_toFinset]; exact sys.refl B⟩)
    rw [Finset.mem_filter] at this
    rw [Set.coe_toFinset] at this
    exact h this.2

private theorem belowCount_iff {W : Type*} [Fintype W]
    (sys : EpistemicSystemFA W) (A B : Set W) :
    belowCount sys A ≥ belowCount sys B ↔ sys.ge A B := by
  constructor
  · intro hcount
    by_contra hng
    have := belowCount_strict sys A B hng
    omega
  · exact belowCount_mono sys A B

private theorem ge_div_iff {a b d : ℚ} (hd : 0 < d) :
    a / d ≥ b / d ↔ a ≥ b := by
  rw [ge_iff_le, ge_iff_le, div_le_div_iff_of_pos_right hd]

/-- **Theorem 6 completeness** (@cite{holliday-icard-2013}, Theorem 6; @cite{van-der-hoek-1996}):
    every EpistemicSystemFA is representable by a **qualitatively additive** measure.

    Construction: define μ(A) = |{S : Finset W | ge A S}| / 2^|W|.
    Totality + transitivity of ge ensure μ A ≥ μ B ↔ ge A B;
    qualitative additivity then follows from Axiom A. -/
theorem theorem6_completeness {W : Type*} [Fintype W]
    (sys : EpistemicSystemFA W) :
    ∃ (m : QualAddMeasure W), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  classical
  let N : ℚ := Fintype.card (Finset W)
  have hN_pos : (0 : ℚ) < N := Nat.cast_pos.mpr Fintype.card_pos
  let mu : Set W → ℚ := fun A => (belowCount sys A : ℚ) / N
  refine ⟨⟨mu, ?nonneg, ?total, ?qualAdd⟩, ?repr⟩
  case nonneg =>
    intro A; exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hN_pos)
  case total =>
    show (belowCount sys Set.univ : ℚ) / N = 1
    rw [belowCount_univ]; exact div_self (ne_of_gt hN_pos)
  case qualAdd =>
    intro A B
    show (belowCount sys A : ℚ) / N ≥ (belowCount sys B : ℚ) / N ↔
         (belowCount sys (A \ B) : ℚ) / N ≥ (belowCount sys (B \ A) : ℚ) / N
    rw [ge_div_iff hN_pos, ge_div_iff hN_pos]
    constructor
    · intro h
      have hge := (belowCount_iff sys A B).mp (by exact_mod_cast h)
      exact_mod_cast (belowCount_iff sys (A \ B) (B \ A)).mpr (sys.additive A B |>.mp hge)
    · intro h
      have hge := (belowCount_iff sys (A \ B) (B \ A)).mp (by exact_mod_cast h)
      exact_mod_cast (belowCount_iff sys A B).mpr (sys.additive A B |>.mpr hge)
  case repr =>
    intro A B
    show sys.ge A B ↔ (belowCount sys A : ℚ) / N ≥ (belowCount sys B : ℚ) / N
    rw [ge_div_iff hN_pos]
    exact ⟨fun h => by exact_mod_cast (belowCount_iff sys A B).mpr h,
           fun h => (belowCount_iff sys A B).mp (by exact_mod_cast h)⟩

/-- Helper: if ge A {b} for every b ∈ B, then ge A B, given monotonicity (T)
    and right-union (J). Proved by Finset induction on B.toFinset. -/
private lemma ge_of_forall_singleton {W : Type*} [Fintype W]
    {ge : Set W → Set W → Prop}
    (hT : EpistemicAxiom.T ge)
    (hJ : EpistemicAxiom.J ge)
    (A B : Set W) (h : ∀ b ∈ B, ge A {b}) : ge A B := by
  classical
  suffices ∀ (s : Finset W), (∀ b, b ∈ s → ge A {b}) → ge A (↑s) by
    rw [← Set.coe_toFinset B]
    exact this B.toFinset (fun b hb => h b (Set.mem_toFinset.mp hb))
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.coe_empty]
    exact hT ∅ A (Set.empty_subset A)
  | @insert b s hbs ih =>
    intro hsub
    rw [Finset.coe_insert]
    exact hJ A _ _ (hsub _ (Finset.mem_insert_self _ _))
      (ih (fun c hc => hsub c (Finset.mem_insert_of_mem hc)))

/-- **Theorem 2** (@cite{halpern-2003}, Thm. 7.5.1a; @cite{holliday-icard-2013}):
    an epistemic system satisfying R, T, Tran, J (right-union),
    and DS (determination by singletons) is representable by Lewis's l-lifting
    from a reflexive preorder on worlds.

    The paper states this as a *logic* completeness theorem for **WJR**
    (K + BT + Tran + J + Mon + R). We prove the underlying per-model
    *representation* result, which is the model-theoretic core: the semantic
    hypotheses (R, T, Tran, J, DS) correspond to WJR's axioms evaluated
    on a single model, without formalizing the syntax or proof system.

    Construction: `ge_w u v := sys.ge {u} {v}`. -/
theorem theorem2_completeness {W : Type*} [Fintype W]
    (sys : EpistemicSystemW W)
    (hTran : ∀ A B C : Set W, sys.ge A B → sys.ge B C → sys.ge A C)
    (hJ : EpistemicAxiom.J sys.ge)
    (hDS : EpistemicAxiom.DS sys.ge) :
    ∃ (ge_w : W → W → Prop) (_ : ∀ w, ge_w w w),
      ∀ A B, sys.ge A B ↔ halpernLift ge_w A B := by
  refine ⟨fun u v => sys.ge {u} {v}, fun w => sys.refl {w}, fun A B => ?_⟩
  constructor
  · -- Forward: sys.ge A B → halpernLift (fun u v => sys.ge {u} {v}) A B
    intro hAB b hbB
    -- {b} ⊆ B, so sys.ge B {b} by monotonicity (Axiom T)
    have hBb : sys.ge B {b} := sys.mono {b} B (Set.singleton_subset_iff.mpr hbB)
    -- Transitivity: sys.ge A B → sys.ge B {b} → sys.ge A {b}
    have hAb : sys.ge A {b} := hTran A B {b} hAB hBb
    -- DS: sys.ge A {b} → ∃ a ∈ A, sys.ge {a} {b}
    exact hDS A b hAb
  · -- Backward: halpernLift → sys.ge A B
    intro hLift
    apply ge_of_forall_singleton sys.mono hJ A B
    intro b hbB
    obtain ⟨a, haA, hab⟩ := hLift b hbB
    -- {a} ⊆ A, so sys.ge A {a} by monotonicity
    have hAa : sys.ge A {a} := sys.mono {a} A (Set.singleton_subset_iff.mpr haA)
    -- Transitivity: sys.ge A {a} → sys.ge {a} {b} → sys.ge A {b}
    exact hTran A {a} {b} hAa hab

-- ── Bridge: Axiom A ↔ FA ────────────────────────

/-- **Algebraic bridge**: Axiom A and the finite additivity property
    of `AdditiveScale` are equivalent for any comparison on sets. -/
theorem axiomA_iff_fa {W : Type*} (ge : Set W → Set W → Prop) :
    EpistemicAxiom.A ge ↔
    (∀ A B C : Set W, (∀ x, x ∈ A → x ∉ C) → (∀ x, x ∈ B → x ∉ C) →
      (ge A B ↔ ge (A ∪ C) (B ∪ C))) := by
  constructor
  · intro hA A B C hAC hBC
    have h1 := hA A B
    have h2 := hA (A ∪ C) (B ∪ C)
    have hd1 : (A ∪ C) \ (B ∪ C) = A \ B := by
      ext x; simp only [Set.mem_diff, Set.mem_union]
      constructor
      · rintro ⟨hx | hx, hnx⟩
        · exact ⟨hx, fun hb => hnx (Or.inl hb)⟩
        · exact absurd (Or.inr hx) hnx
      · rintro ⟨hxA, hxnB⟩
        exact ⟨Or.inl hxA, fun h => h.elim hxnB (hAC x hxA)⟩
    have hd2 : (B ∪ C) \ (A ∪ C) = B \ A := by
      ext x; simp only [Set.mem_diff, Set.mem_union]
      constructor
      · rintro ⟨hx | hx, hnx⟩
        · exact ⟨hx, fun ha => hnx (Or.inl ha)⟩
        · exact absurd (Or.inr hx) hnx
      · rintro ⟨hxB, hxnA⟩
        exact ⟨Or.inl hxB, fun h => h.elim hxnA (hBC x hxB)⟩
    rw [hd1, hd2] at h2
    exact h1.trans h2.symm
  · intro hFA A B
    have hdA : ∀ x, x ∈ A \ B → x ∉ A ∩ B :=
      fun x ⟨_, hxnB⟩ ⟨_, hxB⟩ => hxnB hxB
    have hdB : ∀ x, x ∈ B \ A → x ∉ A ∩ B :=
      fun x ⟨_, hxnA⟩ ⟨hxA, _⟩ => hxnA hxA
    have hA_eq : (A \ B) ∪ (A ∩ B) = A := Set.diff_union_inter A B
    have hB_eq : (B \ A) ∪ (A ∩ B) = B := by
      rw [Set.inter_comm]; exact Set.diff_union_inter B A
    have h := hFA (A \ B) (B \ A) (A ∩ B) hdA hdB
    rw [hA_eq, hB_eq] at h
    exact h.symm

-- ── EpistemicTag + Five Frameworks ──────────────

/-- Binary epistemic classification, parallel to `MereoTag`. -/
inductive EpistemicTag where
  | finitelyAdditive
  | qualitative
  deriving DecidableEq, BEq, Repr

instance : LicensingPipeline EpistemicTag where
  toBoundedness
    | .finitelyAdditive => .closed
    | .qualitative => .open_

theorem epistemicFA_licensed :
    LicensingPipeline.isLicensed EpistemicTag.finitelyAdditive = true := rfl

theorem epistemicQualitative_blocked :
    LicensingPipeline.isLicensed EpistemicTag.qualitative = false := rfl

theorem five_frameworks_agree
    (m : MereoTag) (e : EpistemicTag)
    (h : LicensingPipeline.toBoundedness m = LicensingPipeline.toBoundedness e) :
    LicensingPipeline.isLicensed m = LicensingPipeline.isLicensed e :=
  LicensingPipeline.universal m e h

theorem epistemicFA_eq_qua :
    LicensingPipeline.isLicensed EpistemicTag.finitelyAdditive =
    LicensingPipeline.isLicensed MereoTag.qua := rfl

theorem epistemicQualitative_eq_cum :
    LicensingPipeline.isLicensed EpistemicTag.qualitative =
    LicensingPipeline.isLicensed MereoTag.cum := rfl

end Core.Scale
