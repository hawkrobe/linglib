import Linglib.Theories.Semantics.Plurality.Distributivity

/-!
# Candidate Interpretations for Plural Predication

Formalizes @cite{kriz-spector-2021}'s candidate interpretation framework:
the set of sub-plurality propositions, truth-on-all-readings,
QUD-based strong relevance filtering, the H parameter, and
candidate conjunction.

## Dependency

Imports `Distributivity.lean` for basic plural predicates (`allSatisfy`,
`noneSatisfy`, `pluralTruthValue`, `Tolerance`, `distMaximal`, `distTolerant`).
-/

namespace Semantics.Plurality.Distributivity

variable {Atom W : Type*} [DecidableEq Atom]

-- Part 4: Candidate Interpretations

/--
The candidate proposition for sub-plurality z: "P holds of all atoms in z".
-/
def candidateProp (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (z : Finset Atom) : (W → Prop) :=
  fun w => ∀ a ∈ z, P a w

instance candidateProp.instDecidable (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (z : Finset Atom) (w : W) :
    Decidable (candidateProp P z w) := by unfold candidateProp; infer_instance

/--
Full candidate set: all sub-plurality propositions.

This is the set S from @cite{kriz-spector-2021} before relevance filtering.
-/
def fullCandidateSet (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) : Set ((W → Prop)) :=
  { p | ∃ z ∈ x.powerset, z.Nonempty ∧ p = candidateProp P z }

/--
Candidate set parameterized by tolerance.

With identity tolerance: only the maximal candidate.
With trivial tolerance: all nonempty sub-plurality candidates.
-/
def candidateSet (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (tol : Tolerance Atom) (x : Finset Atom) : Set ((W → Prop)) :=
  { p | ∃ z ∈ x.powerset, z.Nonempty ∧ tol.rel z x ∧ p = candidateProp P z }

-- Part 5: Truth on All Readings

/-- All candidates in the set hold at w -/
def trueOnAll (candidates : Set ((W → Prop))) (w : W) : Prop :=
  ∀ p ∈ candidates, p w

/-- All candidates in the set fail at w -/
def falseOnAll (candidates : Set ((W → Prop))) (w : W) : Prop :=
  ∀ p ∈ candidates, ¬ p w

/-- Some candidates true, some false (the gap) -/
def gapOnCandidates (candidates : Set ((W → Prop))) (w : W) : Prop :=
  (∃ p ∈ candidates, p w) ∧ (∃ p ∈ candidates, ¬ p w)

-- Part 6: Key Correspondence Theorems

/--
Theorem: The maximal candidate is exactly distMaximal.
-/
theorem candidateProp_x_eq_distMaximal (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) :
    candidateProp P x = distMaximal P x := rfl

/--
Theorem: With identity tolerance, the candidate set is a singleton
containing only the maximal candidate.
-/
theorem identity_candidateSet_eq_singleton (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (hne : x.Nonempty) :
    candidateSet P Tolerance.identity x = {candidateProp P x} := by
  ext p
  simp only [candidateSet, Set.mem_setOf_eq, Set.mem_singleton_iff,
             Finset.mem_powerset, Tolerance.identity]
  refine ⟨fun ⟨z, _, _, hz_eq, hp⟩ => ?_, fun hp => ?_⟩
  · rw [← hz_eq, hp]
  · exact ⟨x, Finset.Subset.refl x, hne, rfl, hp⟩

/-- With trivial tolerance, fullCandidateSet = candidateSet. -/
theorem fullCandidateSet_eq_candidateSet_trivial (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) :
    fullCandidateSet P x = candidateSet P Tolerance.trivial x := by
  ext p
  simp only [fullCandidateSet, candidateSet, Set.mem_setOf_eq]
  refine ⟨fun ⟨z, hz_mem, hne, hp⟩ => ?_, fun ⟨z, hz_mem, hne, _, hp⟩ => ?_⟩
  · exact ⟨z, hz_mem, hne, Finset.mem_powerset.mp hz_mem, hp⟩
  · exact ⟨z, hz_mem, hne, hp⟩

/--
Theorem: trueOnAll for the full candidate set iff all atoms satisfy P.
-/
theorem trueOnAll_full_iff_allSatisfy (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    trueOnAll (fullCandidateSet P x) w ↔ allSatisfy P x w := by
  refine ⟨fun h a ha => ?_, fun h p hp => ?_⟩
  · -- (→): Use singleton candidate {a}
    have hsing : candidateProp P {a} ∈ fullCandidateSet P x :=
      ⟨{a}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr ha),
       ⟨a, Finset.mem_singleton.mpr rfl⟩, rfl⟩
    have := h (candidateProp P {a}) hsing
    simp only [candidateProp, Finset.mem_singleton, forall_eq] at this
    exact this
  · -- (←): If allSatisfy, every sub-plurality candidate is true
    obtain ⟨z, hz_mem, _, rfl⟩ := hp
    intro a ha
    exact h a (Finset.mem_powerset.mp hz_mem ha)

/--
Theorem: falseOnAll for full candidates iff no atom satisfies P
(when x is nonempty).
-/
theorem falseOnAll_full_iff_noneSatisfy (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) (hne : x.Nonempty) :
    falseOnAll (fullCandidateSet P x) w ↔ noneSatisfy P x w := by
  refine ⟨fun h a ha hPa => ?_, fun h p hp => ?_⟩
  · -- (→): Use singleton {a}
    have hsing : candidateProp P {a} ∈ fullCandidateSet P x :=
      ⟨{a}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr ha),
       ⟨a, Finset.mem_singleton.mpr rfl⟩, rfl⟩
    have hf := h (candidateProp P {a}) hsing
    apply hf
    intro b hb; rw [Finset.mem_singleton.mp hb]; exact hPa
  · -- (←): If noneSatisfy, every nonempty sub-plurality candidate is false
    obtain ⟨z, hz_mem, ⟨a, ha⟩, rfl⟩ := hp
    intro hall
    exact h a (Finset.mem_powerset.mp hz_mem ha) (hall a ha)

/--
Main Theorem: The trivalent semantics matches the candidate interpretation framework.
-/
theorem pluralTruthValue_eq_candidateSemantics (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) (hne : x.Nonempty) :
    (pluralTruthValue P x w = .true ↔ trueOnAll (fullCandidateSet P x) w) ∧
    (pluralTruthValue P x w = .false ↔ falseOnAll (fullCandidateSet P x) w) ∧
    (pluralTruthValue P x w = .indet ↔ gapOnCandidates (fullCandidateSet P x) w) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [pluralTruthValue_eq_true_iff, trueOnAll_full_iff_allSatisfy]
  · rw [pluralTruthValue_eq_false_iff, falseOnAll_full_iff_noneSatisfy P x w hne]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hne, h⟩⟩
  · rw [pluralTruthValue_eq_gap_iff]
    refine ⟨fun ⟨⟨a, ha, hPa⟩, ⟨b, hb, hPb⟩⟩ => ?_, fun ⟨⟨pt, hpt_mem, hpt_true⟩, ⟨pf, hpf_mem, hpf_false⟩⟩ => ?_⟩
    · -- (→): Singleton candidates supply true and false witnesses
      refine ⟨⟨candidateProp P {a}, ?_, ?_⟩, ⟨candidateProp P {b}, ?_, ?_⟩⟩
      · exact ⟨{a}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr ha),
               ⟨a, Finset.mem_singleton.mpr rfl⟩, rfl⟩
      · intro c hc; rw [Finset.mem_singleton.mp hc]; exact hPa
      · exact ⟨{b}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hb),
               ⟨b, Finset.mem_singleton.mpr rfl⟩, rfl⟩
      · intro hsing; exact hPb (hsing b (Finset.mem_singleton.mpr rfl))
    · -- (←): Witnesses give atoms with both true and false
      obtain ⟨z, hz, ⟨b, hb⟩, rfl⟩ := hpt_mem
      obtain ⟨z', hz', _, rfl⟩ := hpf_mem
      -- pt true: ∀a ∈ z, P a w; pf false: ¬ ∀a ∈ z', P a w
      refine ⟨⟨b, Finset.mem_powerset.mp hz hb, hpt_true b hb⟩, ?_⟩
      -- Need: ∃ a ∈ x, ¬ P a w
      by_contra hc
      push Not at hc
      apply hpf_false
      intro a ha
      exact hc a (Finset.mem_powerset.mp hz' ha)

-- Strong Relevance and QUD Filtering

section StrongRelevance

variable [Fintype W] [DecidableEq W]

/--
Strong relevance: a proposition aligns with a QUD's partition.

A proposition p is strongly relevant to QUD q iff p respects the partition:
if two worlds are q-equivalent, then p has the same truth value at both.
-/
def isStronglyRelevantProp (q : QUD W) (p : (W → Prop)) [DecidablePred p] : Prop :=
  ∀ w1 w2 : W, q.r w1 w2 → (p w1 ↔ p w2)

/-- Filter candidate set to strongly relevant propositions. Decidability is
    handled per-call by the consumer; we keep the membership Set-based. -/
def stronglyRelevantSet (q : QUD W) (candidates : Set ((W → Prop))) : Set ((W → Prop)) :=
  { p ∈ candidates | ∀ w1 w2 : W, q.r w1 w2 → (p w1 ↔ p w2) }

/-- With exact QUD, all propositions are strongly relevant. -/
theorem exact_all_relevant [LawfulBEq W] (p : (W → Prop)) [DecidablePred p] :
    isStronglyRelevantProp (QUD.exact (M := W)) p := by
  intro w1 w2 h
  rw [show w1 = w2 from h]

/-- With exact QUD, the filtered set equals the original set. -/
theorem exact_stronglyRelevantSet_eq [LawfulBEq W] (candidates : Set ((W → Prop))) :
    stronglyRelevantSet (QUD.exact (M := W)) candidates = candidates := by
  ext p
  simp only [stronglyRelevantSet, Set.mem_sep_iff]
  refine ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, ?_⟩⟩
  intro w1 w2 hr
  rw [show w1 = w2 from hr]

/-- With trivial QUD, only constant propositions are strongly relevant. -/
theorem trivial_relevant_iff_constant (p : (W → Prop)) [DecidablePred p] :
    isStronglyRelevantProp (QUD.trivial (M := W)) p ↔ (∀ w1 w2 : W, p w1 ↔ p w2) := by
  simp only [isStronglyRelevantProp, QUD.trivial_r]
  exact ⟨fun h w1 w2 => h w1 w2 ⟨⟩, fun h _ _ _ => h _ _⟩

/--
Non-Maximality Theorem: With a coarse QUD that groups "all P" with "almost all P",
the maximal candidate may not be strongly relevant, allowing non-maximal readings.
-/
theorem nonMaximality_from_coarse_qud (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (q : QUD W) (w_all w_almost : W)
    (h_equiv : q.r w_all w_almost)
    (h_all : allSatisfy P x w_all)
    (h_not_all : ¬ allSatisfy P x w_almost) :
    ¬ isStronglyRelevantProp q (candidateProp P x) := by
  intro hsr
  have heq := hsr w_all w_almost h_equiv
  exact h_not_all (heq.mp h_all)

end StrongRelevance

-- Correspondence Theorems

section Correspondence

variable [Fintype W] [DecidableEq W]

/-- With identity tolerance, the only tolerant sub-plurality is x itself. -/
theorem identity_tolerant_iff_eq (x z : Finset Atom) :
    Tolerance.identity.rel z x ↔ z = x := Iff.rfl

/-- Maximal proposition is always strongly relevant to exact QUD. -/
theorem maximal_relevant_to_exact [LawfulBEq W] (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) :
    isStronglyRelevantProp (QUD.exact (M := W)) (candidateProp P x) :=
  exact_all_relevant _

/-- distMaximal IS the maximal candidate proposition. -/
theorem distMaximal_eq_maximal_candidate (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    distMaximal P x w ↔ candidateProp P x w := Iff.rfl

/-- distTolerant unfolds to existence of a nonempty tolerant witness. -/
theorem distTolerant_iff_exists_tolerant (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (tol : Tolerance Atom) (x : Finset Atom) (w : W) :
    distTolerant P tol x w ↔
    ∃ z ∈ x.powerset, z.Nonempty ∧ tol.rel z x ∧ (∀ a ∈ z, P a w) := Iff.rfl

end Correspondence

-- ════════════════════════════════════════════════════════════════════════════
-- The Homogeneity Parameter H (@cite{kriz-spector-2021} §5.3)
-- ════════════════════════════════════════════════════════════════════════════

/-! The deepest compositional innovation of @cite{kriz-spector-2021}: interpretation
    is parameterized by H, which maps each argument position to a candidate
    denotation. -/

section HomogeneityParameter

variable {Atom W : Type*} [DecidableEq Atom] [Fintype Atom]

/-- A homogeneity parameter selects, for each plurality, a nonempty
    sub-plurality to serve as the effective argument. -/
abbrev HomParam (Atom : Type*) := Finset Atom → Finset Atom

/-- An admissible homogeneity parameter maps x to a nonempty sub-plurality of x. -/
def isAdmissible (H : HomParam Atom) (x : Finset Atom) : Prop :=
  H x ⊆ x ∧ (H x).Nonempty

/-- The identity parameter: H(x) = x (universal/maximal reading). -/
def HomParam.id : HomParam Atom := fun x => x

theorem HomParam.id_admissible (x : Finset Atom) (hne : x.Nonempty) :
    isAdmissible (HomParam.id (Atom := Atom)) x :=
  ⟨Finset.Subset.refl x, hne⟩

/-- Interpretation of a distributive predicate parameterized by H:
    "P holds of all atoms in H(x)." -/
def interpWithH (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (H : HomParam Atom) (x : Finset Atom) (w : W) : Prop :=
  ∀ a ∈ H x, P a w

instance interpWithH.instDecidable (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (H : HomParam Atom) (x : Finset Atom) (w : W) :
    Decidable (interpWithH P H x w) := by unfold interpWithH; infer_instance

/-- With H = id, interpretation reduces to allSatisfy. -/
theorem interpWithH_id (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) :
    interpWithH P HomParam.id x w ↔ allSatisfy P x w := Iff.rfl

/-- `all` as universal quantification over admissible H. -/
def allViaForallH (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) : Prop :=
  ∀ H : HomParam Atom, isAdmissible H x → interpWithH P H x w

/-- `allViaForallH` ↔ `allSatisfy`: universal quantification over H reduces
    to the simple universal check on atoms. -/
theorem allViaForallH_iff_allSatisfy (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    allViaForallH P x w ↔ allSatisfy P x w := by
  refine ⟨fun hall a ha => ?_, fun hall H hAdm a ha => hall a (hAdm.1 ha)⟩
  -- (→): Use singleton parameter for each atom
  have hAdm : isAdmissible (fun _ => ({a} : Finset Atom)) x :=
    ⟨Finset.singleton_subset_iff.mpr ha, ⟨a, Finset.mem_singleton.mpr rfl⟩⟩
  have := hall (fun _ => {a}) hAdm
  exact this a (Finset.mem_singleton.mpr rfl)

/-- The trivalent truth value via H quantification matches `pluralTruthValue`. -/
theorem forallH_true_iff_pluralTrue (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    allViaForallH P x w ↔ pluralTruthValue P x w = .true := by
  rw [allViaForallH_iff_allSatisfy, pluralTruthValue_eq_true_iff]

end HomogeneityParameter

-- ════════════════════════════════════════════════════════════════════════════
-- Candidate Conjunction (@cite{kriz-spector-2021} §3.2)
-- ════════════════════════════════════════════════════════════════════════════

/-! K&S 2021's key departure from @cite{malamud-2012}: the overall meaning of a
    sentence is the CONJUNCTION of all strongly relevant candidate interpretations,
    not the disjunction. -/

section CandidateConjunction

variable {W : Type*}

/-- The truth-on-all-readings principle: TRUE iff all hold, FALSE iff none
    hold, GAP iff mixed. (Classical logic + Decidable per-candidate.) -/
theorem candidateConjunction_trichotomy (candidates : Set ((W → Prop))) (w : W)
    (decAll : Decidable (trueOnAll candidates w))
    (decNone : Decidable (falseOnAll candidates w)) :
    trueOnAll candidates w ∨ falseOnAll candidates w ∨
    gapOnCandidates candidates w := by
  by_cases hall : trueOnAll candidates w
  · exact Or.inl hall
  · by_cases hnone : falseOnAll candidates w
    · exact Or.inr (Or.inl hnone)
    · right; right
      simp only [trueOnAll] at hall
      simp only [falseOnAll] at hnone
      push Not at hall hnone
      obtain ⟨p₁, hp₁, hne₁⟩ := hall
      obtain ⟨p₂, hp₂, hne₂⟩ := hnone
      -- hne₁ : ¬ p₁ w (false witness); hne₂ : p₂ w (true witness)
      exact ⟨⟨p₂, hp₂, hne₂⟩, ⟨p₁, hp₁, hne₁⟩⟩

/-- Conjunction of candidates yields exactly the same three-way partition
    as `pluralTruthValue` for the full candidate set. -/
theorem candidateConjunction_eq_plural (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] [DecidableEq Atom]
    (x : Finset Atom) (w : W) (hne : x.Nonempty) :
    (trueOnAll (fullCandidateSet P x) w ↔ pluralTruthValue P x w = .true) ∧
    (falseOnAll (fullCandidateSet P x) w ↔ pluralTruthValue P x w = .false) := by
  have h := pluralTruthValue_eq_candidateSemantics P x w hne
  exact ⟨h.1.symm, h.2.1.symm⟩

end CandidateConjunction

end Semantics.Plurality.Distributivity
