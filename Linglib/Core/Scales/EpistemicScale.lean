import Linglib.Core.Scales.EpistemicScale.Defs
import Linglib.Core.Scales.EpistemicScale.Fin4

/-!
# Epistemic Comparative Likelihood — Main Theorems

Re-exports `EpistemicScale.Defs` (core definitions, Fin 1/2/3/5) and
`EpistemicScale.Fin4` (Fin 4 representation theorem), then states the
top-level KPS theorems (8a, 8b) and completeness results.
-/

namespace Core.Scale

-- ── Theorem 8 (Kraft, Pratt & Seidenberg 1959) ───

set_option maxHeartbeats 1600000 in
/-- **Theorem 8a** (Kraft, Pratt & Seidenberg 1959): for |W| < 5,
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

/-- **Theorem 8b** (Kraft, Pratt & Seidenberg 1959): for |W| ≥ 5,
    FA is strictly weaker than FP∞ — there exists a 5-element type
    with an FA ordering admitting no finitely additive measure
    representation. -/
theorem theorem8b :
    ∃ (W : Type) (_ : Fintype W) (sys : EpistemicSystemFA W),
      Fintype.card W = 5 ∧
      ¬∃ (m : FinAddMeasure W), ∀ A B, sys.ge A B ↔ m.inducedGe A B :=
  ⟨Fin 5, inferInstance, kpsSystemFA, Fintype.card_fin 5, kps_not_representable⟩

-- ── Completeness (Theorems 6–7) ──────────────────

/-- **Theorem 6 completeness** (Holliday & Icard 2013, Theorem 6; van der Hoek 1996):
    every EpistemicSystemFA is representable by a **qualitatively additive** measure. -/
theorem theorem6_completeness {W : Type*} [Fintype W]
    (sys : EpistemicSystemFA W) :
    ∃ (m : QualAddMeasure W), ∀ A B, sys.ge A B ↔ m.inducedGe A B :=
  sorry -- van der Hoek (1996); linear extension of qualitative probability

/-- **Theorem 2 completeness** (Halpern 2003; Holliday & Icard 2013 §3):
    every system satisfying R, T, BT, Tran, J, Mon (System WJR) is
    representable by Lewis's l-lifting from a reflexive preorder on worlds. -/
theorem theorem7_completeness {W : Type*} [Fintype W]
    (sys : EpistemicSystemW W) :
    ∃ (ge_w : W → W → Prop) (_ : ∀ w, ge_w w w),
      ∀ A B, sys.ge A B ↔ halpernLift ge_w A B :=
  sorry -- Halpern (2003); requires WJR axioms for completeness

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
