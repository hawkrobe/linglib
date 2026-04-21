/-
# Candidate Interpretations for Plural Predication

Formalizes @cite{kriz-spector-2021}'s candidate interpretation framework:
the set of sub-plurality propositions, truth-on-all-readings,
QUD-based strong relevance filtering, the H parameter, and
candidate conjunction.

## Dependency

Imports `Distributivity.lean` for basic plural predicates (`allSatisfy`,
`noneSatisfy`, `pluralTruthValue`, `Tolerance`, `distMaximal`, `distTolerant`).
-/

import Linglib.Theories.Semantics.Plurality.Distributivity

namespace Semantics.Plurality.Distributivity

variable {Atom W : Type*} [DecidableEq Atom]

-- Part 4: Candidate Interpretations

/--
The candidate proposition for sub-plurality z: "P holds of all atoms in z".
-/
def candidateProp (P : Atom → W → Bool) (z : Finset Atom) : (W → Bool) :=
  λ w => decide (∀ a ∈ z, P a w = true)

/--
Full candidate set: all sub-plurality propositions.

This is the set S from @cite{kriz-spector-2021} before relevance filtering.
-/
def fullCandidateSet (P : Atom → W → Bool) (x : Finset Atom) : Set ((W → Bool)) :=
  { p | ∃ z ∈ x.powerset, z.Nonempty ∧ p = candidateProp P z }

/--
Candidate set parameterized by tolerance.

With identity tolerance: only the maximal candidate.
With full tolerance: all nonempty sub-plurality candidates.

The nonemptiness constraint matches `fullCandidateSet` and `distTolerant`:
empty sub-pluralities would create vacuously true candidates.
-/
def candidateSet (P : Atom → W → Bool) (tol : Tolerance Atom)
    (x : Finset Atom) : Set ((W → Bool)) :=
  { p | ∃ z ∈ x.powerset, z.Nonempty ∧ tol.rel z x = true ∧ p = candidateProp P z }

-- Part 5: Truth on All Readings

/-- All candidates in the set are true at w -/
def trueOnAll (candidates : Set ((W → Bool))) (w : W) : Prop :=
  ∀ p ∈ candidates, p w = true

/-- All candidates in the set are false at w -/
def falseOnAll (candidates : Set ((W → Bool))) (w : W) : Prop :=
  ∀ p ∈ candidates, p w = false

/-- Some candidates true, some false (the gap) -/
def gapOnCandidates (candidates : Set ((W → Bool))) (w : W) : Prop :=
  (∃ p ∈ candidates, p w = true) ∧ (∃ p ∈ candidates, p w = false)

-- Part 6: Key Correspondence Theorems

/--
Theorem: The maximal candidate is exactly distMaximal.
-/
theorem candidateProp_x_eq_distMaximal (P : Atom → W → Bool) (x : Finset Atom) :
    candidateProp P x = distMaximal P x := by
  rfl

/--
Theorem: With identity tolerance, the candidate set is a singleton
containing only the maximal candidate.
-/
theorem identity_candidateSet_eq_singleton (P : Atom → W → Bool) (x : Finset Atom)
    (hne : x.Nonempty) :
    candidateSet P Tolerance.identity x = {candidateProp P x} := by
  ext p
  simp only [candidateSet, Set.mem_setOf_eq, Set.mem_singleton_iff,
             Finset.mem_powerset, Tolerance.identity, beq_iff_eq]
  constructor
  · intro ⟨z, _, _, hz_eq, hp⟩
    rw [← hz_eq, hp]
  · intro hp
    exact ⟨x, Finset.Subset.refl x, hne, rfl, hp⟩

/-- With full tolerance, fullCandidateSet = candidateSet (both require nonempty). -/
theorem fullCandidateSet_eq_candidateSet_full (P : Atom → W → Bool) (x : Finset Atom) :
    fullCandidateSet P x = candidateSet P Tolerance.full x := by
  ext p
  simp only [fullCandidateSet, candidateSet, Set.mem_setOf_eq]
  constructor
  · intro ⟨z, hz_mem, hne, hp⟩
    exact ⟨z, hz_mem, hne, by simp [Tolerance.full, Finset.mem_powerset.mp hz_mem], hp⟩
  · intro ⟨z, hz_mem, hne, _, hp⟩
    exact ⟨z, hz_mem, hne, hp⟩

/--
Theorem: trueOnAll for the full candidate set iff all atoms satisfy P.

This connects the candidate framework to the simple universal condition.
-/
theorem trueOnAll_full_iff_allSatisfy (P : Atom → W → Bool) (x : Finset Atom) (w : W) :
    trueOnAll (fullCandidateSet P x) w ↔ allSatisfy P x w = true := by
  constructor
  · -- (→): If all candidates true, then all atoms satisfy P
    intro h
    simp only [allSatisfy, decide_eq_true_eq]
    intro a ha
    -- The singleton {a} is in fullCandidateSet (nonempty!)
    have hsing : candidateProp P {a} ∈ fullCandidateSet P x := by
      simp only [fullCandidateSet, Set.mem_setOf_eq, Finset.mem_powerset]
      exact ⟨{a}, Finset.singleton_subset_iff.mpr ha, ⟨a, Finset.mem_singleton.mpr rfl⟩, rfl⟩
    have := h (candidateProp P {a}) hsing
    simp only [candidateProp, decide_eq_true_eq, Finset.mem_singleton, forall_eq] at this
    exact this
  · -- (←): If all atoms satisfy P, then all candidates are true
    intro h p hp
    simp only [fullCandidateSet, Set.mem_setOf_eq, Finset.mem_powerset] at hp
    obtain ⟨z, hz, _, rfl⟩ := hp
    simp only [candidateProp, decide_eq_true_eq]
    intro a ha
    simp only [allSatisfy, decide_eq_true_eq] at h
    exact h a (hz ha)

/--
Theorem: falseOnAll for full candidates iff no atom satisfies P.

- (→): Singleton candidates {a} false → each P(a) fails.
- (←): No P(a) holds → for any nonempty z ⊆ x, some atom in z fails P.
-/
theorem falseOnAll_full_iff_noneSatisfy (P : Atom → W → Bool) (x : Finset Atom) (w : W)
    (hne : x.Nonempty) :
    falseOnAll (fullCandidateSet P x) w ↔ noneSatisfy P x w = true := by
  constructor
  · -- (→): If all nonempty candidates false, then no atom satisfies P
    intro h
    simp only [noneSatisfy, decide_eq_true_eq]
    intro a ha
    have hsing : candidateProp P {a} ∈ fullCandidateSet P x := by
      simp only [fullCandidateSet, Set.mem_setOf_eq, Finset.mem_powerset]
      exact ⟨{a}, Finset.singleton_subset_iff.mpr ha, ⟨a, Finset.mem_singleton.mpr rfl⟩, rfl⟩
    have hf := h (candidateProp P {a}) hsing
    simp only [candidateProp, Finset.mem_singleton, forall_eq] at hf
    cases hP : P a w <;> simp_all
  · -- (←): If no atom satisfies P, then all nonempty candidates are false
    intro h p hp
    simp only [fullCandidateSet, Set.mem_setOf_eq, Finset.mem_powerset] at hp
    obtain ⟨z, hz, hzne, rfl⟩ := hp
    simp only [candidateProp]
    rw [decide_eq_false_iff_not]
    intro hall
    obtain ⟨a, ha⟩ := hzne
    simp only [noneSatisfy, decide_eq_true_eq] at h
    have := h a (hz ha)
    exact absurd (hall a ha) (by simp [this])

/--
Main Theorem: The trivalent semantics matches the candidate interpretation framework.

pluralTruthValue P x w equals:
-.true iff trueOnAll (fullCandidateSet P x) w
-.false iff falseOnAll (fullCandidateSet P x) w
-.gap iff gapOnCandidates (fullCandidateSet P x) w

This is the central correspondence theorem of @cite{kriz-spector-2021}, showing that the
simple trivalent semantics (based on all/some/none) coincides with the more
sophisticated "truth on all readings" approach.

- TRUE: via `trueOnAll_full_iff_allSatisfy` + `pluralTruthValue_eq_true_iff`
- FALSE: via `falseOnAll_full_iff_noneSatisfy` + `pluralTruthValue_eq_false_iff`
- GAP: singleton witnesses for both true and false candidates
-/
theorem pluralTruthValue_eq_candidateSemantics (P : Atom → W → Bool) (x : Finset Atom) (w : W)
    (hne : x.Nonempty) :
    (pluralTruthValue P x w = .true ↔ trueOnAll (fullCandidateSet P x) w) ∧
    (pluralTruthValue P x w = .false ↔ falseOnAll (fullCandidateSet P x) w) ∧
    (pluralTruthValue P x w = .gap ↔ gapOnCandidates (fullCandidateSet P x) w) := by
  refine ⟨?_, ?_, ?_⟩
  · -- .true ↔ trueOnAll
    rw [pluralTruthValue_eq_true_iff, trueOnAll_full_iff_allSatisfy]
  · -- .false ↔ falseOnAll
    rw [pluralTruthValue_eq_false_iff, falseOnAll_full_iff_noneSatisfy P x w hne]
    constructor
    · intro ⟨_, h⟩; exact h
    · intro h
      refine ⟨?_, h⟩
      simp only [allSatisfy, noneSatisfy, decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢
      push_neg
      obtain ⟨a, ha⟩ := hne
      exact ⟨a, ha, by simp [h a ha]⟩
  · -- .gap ↔ gapOnCandidates
    rw [pluralTruthValue_eq_gap_iff]
    constructor
    · -- →: neither all nor none → true and false witnesses
      intro ⟨hNotAll, hNotNone⟩
      simp only [allSatisfy, noneSatisfy, decide_eq_false_iff_not] at hNotAll hNotNone
      push_neg at hNotAll hNotNone
      obtain ⟨a, ha, hPa⟩ := hNotAll
      obtain ⟨b, hb, hPb⟩ := hNotNone
      constructor
      · -- ∃ true candidate: singleton {b} where P b w = true
        refine ⟨candidateProp P {b}, ?_, ?_⟩
        · exact ⟨{b}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hb),
                 ⟨b, Finset.mem_singleton.mpr rfl⟩, rfl⟩
        · simp only [candidateProp, decide_eq_true_eq, Finset.mem_singleton, forall_eq]
          cases hP : P b w <;> simp_all
      · -- ∃ false candidate: singleton {a} where P a w = false
        refine ⟨candidateProp P {a}, ?_, ?_⟩
        · exact ⟨{a}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr ha),
                 ⟨a, Finset.mem_singleton.mpr rfl⟩, rfl⟩
        · simp only [candidateProp, decide_eq_false_iff_not, Finset.mem_singleton, forall_eq]
          cases hP : P a w <;> simp_all
    · -- ←: true and false witnesses → neither all nor none
      intro ⟨⟨pt, hpt_mem, hpt_true⟩, ⟨pf, hpf_mem, hpf_false⟩⟩
      constructor
      · -- allSatisfy = false: from false candidate, find atom where P fails
        obtain ⟨z, hz, hzne, rfl⟩ := hpf_mem
        simp only [candidateProp, decide_eq_false_iff_not] at hpf_false
        push_neg at hpf_false
        obtain ⟨a, ha, hPa⟩ := hpf_false
        simp only [allSatisfy, decide_eq_false_iff_not]
        push_neg
        exact ⟨a, Finset.mem_powerset.mp hz ha, by cases h : P a w <;> simp_all⟩
      · -- noneSatisfy = false: from true candidate, find atom where P holds
        obtain ⟨z, hz, hzne, rfl⟩ := hpt_mem
        simp only [candidateProp, decide_eq_true_eq] at hpt_true
        obtain ⟨a, ha⟩ := hzne
        simp only [noneSatisfy, decide_eq_false_iff_not]
        push_neg
        exact ⟨a, Finset.mem_powerset.mp hz ha, by cases h : P a w <;> simp_all [hpt_true a ha]⟩

-- Strong Relevance and QUD Filtering

section StrongRelevance

variable [Fintype W] [DecidableEq W]

/--
Strong relevance: a proposition aligns with a QUD's partition.

A proposition p is strongly relevant to QUD q iff p respects the partition:
if two worlds are q-equivalent, then p has the same truth value at both.

This is the key filtering mechanism from @cite{kriz-spector-2021} Section 3.
-/
def isStronglyRelevantProp (q : QUD W) (p : (W → Bool)) : Prop :=
  ∀ w1 w2 : W, q.r w1 w2 → p w1 = p w2

/-- Decidable version -/
def isStronglyRelevant (q : QUD W) (p : (W → Bool)) : Bool :=
  decide (∀ w1 w2 : W, q.r w1 w2 → p w1 = p w2)

/-- Filter candidate set to strongly relevant propositions -/
def stronglyRelevantSet (q : QUD W) (candidates : Set ((W → Bool))) : Set ((W → Bool)) :=
  { p ∈ candidates | isStronglyRelevantProp q p }

/--
Theorem: With exact QUD, all propositions are strongly relevant.

The exact QUD distinguishes all worlds, so every proposition trivially
respects the partition.
-/
theorem exact_all_relevant [LawfulBEq W] (p : (W → Bool)) :
    isStronglyRelevantProp (QUD.exact (M := W)) p := by
  intro w1 w2 h
  exact congrArg p h

/--
Corollary: With exact QUD, the filtered set equals the original set.
-/
theorem exact_stronglyRelevantSet_eq [LawfulBEq W] (candidates : Set ((W → Bool))) :
    stronglyRelevantSet (QUD.exact (M := W)) candidates = candidates := by
  ext p
  simp only [stronglyRelevantSet, Set.mem_sep_iff]
  constructor
  · intro ⟨h, _⟩; exact h
  · intro h; exact ⟨h, exact_all_relevant p⟩

/--
Theorem: With trivial QUD, only constant propositions are strongly relevant.
-/
theorem trivial_relevant_iff_constant (p : (W → Bool)) :
    isStronglyRelevantProp (QUD.trivial (M := W)) p ↔ (∀ w1 w2 : W, p w1 = p w2) := by
  simp only [isStronglyRelevantProp, QUD.trivial_r]
  exact ⟨λ h w1 w2 => h w1 w2 ⟨⟩, λ h _ _ _ => h _ _⟩

/--
Non-Maximality Theorem: With a coarse QUD that groups "all P" with "almost all P",
the maximal candidate may not be strongly relevant, allowing non-maximal readings.

This is the formal content of @cite{kriz-spector-2021} Section 3's relevance filtering.

Proof idea:
- If q groups w_all (where all satisfy P) with w_almost (where not all satisfy),
  then candidateProp P x has different values at these QUD-equivalent worlds.
- But strong relevance requires same values at QUD-equivalent worlds.
- Contradiction.

The proof is by contradiction: strong relevance + QUD equivalence forces the
maximal candidate to agree on w_all and w_almost, but allSatisfy gives
different values.
-/
theorem nonMaximality_from_coarse_qud (P : Atom → W → Bool) (x : Finset Atom)
    (q : QUD W) (w_all w_almost : W)
    (h_equiv : q.r w_all w_almost)
    (h_all : allSatisfy P x w_all = true)
    (h_not_all : allSatisfy P x w_almost = false) :
    ¬isStronglyRelevantProp q (candidateProp P x) := by
  intro hsr
  have heq := hsr w_all w_almost h_equiv
  -- candidateProp P x w = allSatisfy P x w (definitionally)
  change allSatisfy P x w_all = allSatisfy P x w_almost at heq
  rw [h_all, h_not_all] at heq
  exact absurd heq (by decide)

end StrongRelevance

-- Correspondence Theorems

section Correspondence

variable [Fintype W] [DecidableEq W]

/--
With identity tolerance, the only tolerant sub-plurality is x itself.

This is because z ⪯ x under identity tolerance iff z = x.
-/
theorem identity_tolerant_iff_eq (x z : Finset Atom) :
    Tolerance.identity.rel z x = true ↔ z = x := by
  simp only [Tolerance.identity, beq_iff_eq]

/--
Identity tolerance candidate set contains exactly the maximal proposition.

NOTE: This is a variant of identity_candidateSet_eq_singleton,
stating it in terms of the explicit proposition form.
-/
theorem identity_candidateSet_singleton' (P : Atom → W → Bool) (x : Finset Atom)
    (hne : x.Nonempty) :
    candidateSet P Tolerance.identity x =
    {λ w => decide (∀ a ∈ x, P a w = true)} := by
  -- This follows from identity_candidateSet_eq_singleton + candidateProp definition
  rw [identity_candidateSet_eq_singleton P x hne]
  rfl

/--
Strong relevance (propositional version): respects QUD partition.
-/
theorem stronglyRelevant_iff (q : QUD W) (p : (W → Bool)) :
    isStronglyRelevantProp q p ↔ ∀ w1 w2, q.r w1 w2 → p w1 = p w2 := by
  rfl

/--
With exact QUD, all propositions are strongly relevant.

The exact QUD distinguishes all worlds, so every proposition aligns with it.
-/
theorem exact_all_stronglyRelevant [LawfulBEq W] (p : (W → Bool)) :
    isStronglyRelevantProp (QUD.exact (M := W)) p := by
  intro w1 w2 h
  exact congrArg p h

/--
With trivial QUD, only constant propositions are strongly relevant.

The trivial QUD groups all worlds together, so a proposition is relevant
iff it has the same value at all worlds.
-/
theorem trivial_stronglyRelevant_iff (p : (W → Bool)) :
    isStronglyRelevantProp (QUD.trivial (M := W)) p ↔ (∀ w1 w2 : W, p w1 = p w2) := by
  simp only [isStronglyRelevantProp, QUD.trivial_r]
  exact ⟨λ h w1 w2 => h w1 w2 ⟨⟩, λ h _ _ _ => h _ _⟩

/--
Key Theorem: The maximal proposition is always strongly relevant to exact QUD.

This shows the connection between `distMaximal` and the truth-on-all-readings
approach: under the exact QUD, the maximal candidate is always relevant.
-/
theorem maximal_relevant_to_exact [LawfulBEq W] (P : Atom → W → Bool) (x : Finset Atom) :
    isStronglyRelevantProp (QUD.exact (M := W))
      (λ w => decide (∀ a ∈ x, P a w = true)) :=
  exact_all_stronglyRelevant _

/--
Correspondence Theorem: distMaximal characterizes truth on the maximal candidate.

The algebraic operator `distMaximal` equals the truth value of the unique candidate
generated by identity tolerance. This connects the operator-based approach
to the pragmatic truth-on-all-readings approach of Križ & @cite{kriz-spector-2021}.
-/
theorem distMaximal_eq_maximal_candidate (P : Atom → W → Bool) (x : Finset Atom) (w : W) :
    distMaximal P x w = (λ w => decide (∀ a ∈ x, P a w = true)) w := by
  rfl

/--
Correspondence Theorem: distTolerant unfolds to existence of a nonempty tolerant witness.

This connects the operator to the candidate interpretation framework.
-/
theorem distTolerant_iff_exists_tolerant (P : Atom → W → Bool) (tol : Tolerance Atom)
    (x : Finset Atom) (w : W) :
    distTolerant P tol x w = true ↔
    ∃ z ∈ x.powerset, z.Nonempty ∧ tol.rel z x = true ∧ (∀ a ∈ z, P a w = true) := by
  simp only [distTolerant, decide_eq_true_iff]

end Correspondence

-- ════════════════════════════════════════════════════════════════════════════
-- The Homogeneity Parameter H (@cite{kriz-spector-2021} §5.3)
-- ════════════════════════════════════════════════════════════════════════════

/-! The deepest compositional innovation of @cite{kriz-spector-2021}: interpretation
    is parameterized by H, which maps each argument position to a candidate
    denotation. For the Finset-based setting, H selects a sub-plurality z ⊆ x
    for each plurality x. The predicate is then evaluated on z instead of x.

    The semantic effect of `all` is to *universally quantify* over admissible
    values of H — not merely to collapse gaps. This explains:
    - Why `all` removes homogeneity (∀H forces agreement across candidates)
    - Why `all` interacts scopally with negation
    - Why `all` selectively targets one argument position

    The `removeGap` operation in `Homogeneity.lean` is a *consequence* of
    ∀H quantification, not a primitive. -/

section HomogeneityParameter

variable {Atom W : Type*} [DecidableEq Atom] [Fintype Atom]

/-- A homogeneity parameter selects, for each plurality, a nonempty
    sub-plurality to serve as the effective argument.
    @cite{kriz-spector-2021} §5.3.1: H(n, x) ∈ Cand_x. -/
abbrev HomParam (Atom : Type*) := Finset Atom → Finset Atom

/-- An admissible homogeneity parameter maps x to a nonempty sub-plurality of x.
    This is the Finset-level analog of H(n, x) ∈ Cand_x for distributive predicates,
    where the candidates are all nonempty sub-pluralities. -/
def isAdmissible (H : HomParam Atom) (x : Finset Atom) : Prop :=
  H x ⊆ x ∧ (H x).Nonempty

/-- The identity parameter: H(x) = x (universal/maximal reading). -/
def HomParam.id : HomParam Atom := fun x => x

theorem HomParam.id_admissible (x : Finset Atom) (hne : x.Nonempty) :
    isAdmissible (HomParam.id (Atom := Atom)) x :=
  ⟨Finset.Subset.refl x, hne⟩

/-- Interpretation of a distributive predicate parameterized by H:
    "P holds of all atoms in H(x)." -/
def interpWithH (P : Atom → W → Bool) (H : HomParam Atom)
    (x : Finset Atom) (w : W) : Bool :=
  decide (∀ a ∈ H x, P a w = true)

/-- With H = id, interpretation reduces to allSatisfy. -/
theorem interpWithH_id (P : Atom → W → Bool) (x : Finset Atom) (w : W) :
    interpWithH P HomParam.id x w = allSatisfy P x w := by
  simp only [interpWithH, HomParam.id, allSatisfy, decide_eq_decide]

/-- `all` as universal quantification over admissible H:
    true iff for ALL admissible H, the predicate holds.
    @cite{kriz-spector-2021} eq. 71. -/
def allViaForallH (P : Atom → W → Bool) (x : Finset Atom) (w : W) : Prop :=
  ∀ H : HomParam Atom, isAdmissible H x → interpWithH P H x w = true

/-- `allViaForallH` ↔ `allSatisfy`: universal quantification over H reduces
    to the simple universal check on atoms.

    Proof: (→) For each atom a ∈ x, the singleton parameter H_a(x) = {a}
    is admissible, and interpWithH forces P(a). (←) If all atoms satisfy P,
    then any sub-plurality does too.

    This is the structural derivation of the `removeGap` effect: `all`
    doesn't stipulate gap removal — it universally quantifies over H,
    and the universal check is the only thing that survives. -/
theorem allViaForallH_iff_allSatisfy (P : Atom → W → Bool) (x : Finset Atom) (w : W) :
    allViaForallH P x w ↔ allSatisfy P x w = true := by
  constructor
  · -- (→): Use singleton parameters to extract each atom
    intro hall
    simp only [allSatisfy, decide_eq_true_eq]
    intro a ha
    have hAdm : isAdmissible (fun _ => ({a} : Finset Atom)) x :=
      ⟨Finset.singleton_subset_iff.mpr ha, ⟨a, Finset.mem_singleton.mpr rfl⟩⟩
    have := hall (fun _ => {a}) hAdm
    simp only [interpWithH, decide_eq_true_eq, Finset.mem_singleton, forall_eq] at this
    exact this
  · -- (←): If all atoms satisfy P, any sub-plurality does too
    intro hall H hAdm
    simp only [interpWithH, decide_eq_true_eq]
    simp only [allSatisfy, decide_eq_true_eq] at hall
    intro a ha
    exact hall a (hAdm.1 ha)

/-- The trivalent truth value via H quantification matches `pluralTruthValue`.

    TRUE iff ∀H (admissible), interpWithH = true, i.e., allSatisfy.
    FALSE iff ∀H (admissible), interpWithH = false, i.e., noneSatisfy.
    GAP otherwise.

    This shows that the H-parameterized semantics yields exactly the same
    trivalent output as the supervaluation-based `pluralTruthValue`. -/
theorem forallH_true_iff_pluralTrue (P : Atom → W → Bool) (x : Finset Atom) (w : W) :
    allViaForallH P x w ↔ pluralTruthValue P x w = .true := by
  rw [allViaForallH_iff_allSatisfy, pluralTruthValue_eq_true_iff]

/-- Derived: `allPluralTV` IS the ∀H quantification.

    This replaces the `removeGap`-based definition with a deeper derivation:
    `all` universally quantifies over homogeneity parameters, and the result
    is a bivalent sentence because ∀H agreement leaves no room for gaps. -/
theorem allPluralTV_from_forallH (P : Atom → W → Bool) (x : Finset Atom) (w : W) :
    allViaForallH P x w ↔ allSatisfy P x w = true := by
  exact allViaForallH_iff_allSatisfy P x w

end HomogeneityParameter

-- ════════════════════════════════════════════════════════════════════════════
-- Candidate Conjunction (@cite{kriz-spector-2021} §3.2)
-- ════════════════════════════════════════════════════════════════════════════

/-! K&S 2021's key departure from @cite{malamud-2012}: the overall meaning of a
    sentence is the CONJUNCTION of all strongly relevant candidate interpretations,
    not the disjunction. This yields homogeneity (true iff all true, false iff all
    false, gap iff mixed) and correct predictions in non-monotonic contexts. -/

section CandidateConjunction

variable {W : Type*}

/-- The truth-on-all-readings principle determines a trivalent truth value
    from a set of Boolean candidates: TRUE iff all true, FALSE iff all false,
    GAP iff mixed. @cite{kriz-spector-2021} §3.2.

    This is the Prop-level characterization (avoiding Decidable requirements
    on Set-quantified conditions). -/
theorem candidateConjunction_trichotomy (candidates : Set ((W → Bool))) (w : W) :
    trueOnAll candidates w ∨ falseOnAll candidates w ∨
    gapOnCandidates candidates w := by
  by_cases hall : trueOnAll candidates w
  · exact Or.inl hall
  · by_cases hnone : falseOnAll candidates w
    · exact Or.inr (Or.inl hnone)
    · right; right
      simp only [trueOnAll] at hall; push_neg at hall
      simp only [falseOnAll] at hnone; push_neg at hnone
      obtain ⟨p₁, hp₁, hne₁⟩ := hall
      obtain ⟨p₂, hp₂, hne₂⟩ := hnone
      have h₁ : p₁ w = false := by cases h : p₁ w <;> simp_all
      have h₂ : p₂ w = true := by cases h : p₂ w <;> simp_all
      exact ⟨⟨p₂, hp₂, h₂⟩, ⟨p₁, hp₁, h₁⟩⟩

/-- Conjunction of candidates yields exactly the same three-way partition
    as `pluralTruthValue` for the full candidate set. This IS the "truth
    on all readings" ↔ supervaluation correspondence. -/
theorem candidateConjunction_eq_plural (P : Atom → W → Bool)
    [DecidableEq Atom] (x : Finset Atom) (w : W) (hne : x.Nonempty) :
    (trueOnAll (fullCandidateSet P x) w ↔ pluralTruthValue P x w = .true) ∧
    (falseOnAll (fullCandidateSet P x) w ↔ pluralTruthValue P x w = .false) := by
  have h := pluralTruthValue_eq_candidateSemantics P x w hne
  exact ⟨h.1.symm, h.2.1.symm⟩

end CandidateConjunction

end Semantics.Plurality.Distributivity
