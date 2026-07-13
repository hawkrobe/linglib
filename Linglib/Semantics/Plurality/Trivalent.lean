import Linglib.Core.Logic.Duality
import Linglib.Core.Logic.Trivalent
import Linglib.Semantics.Plurality.Homogeneity.Basic
import Linglib.Semantics.Plurality.Basic
import Linglib.Semantics.Plurality.Cover
import Linglib.Semantics.Plurality.Implicature

/-!
# Candidate Interpretations for Plural Predication
[kriz-spector-2021]

Formalises a cover-cell **simplification** of [kriz-spector-2021]'s
candidate interpretation framework. The simplification treats each candidate
as a subset-universal proposition `λ w => ∀ a ∈ z, P a w` for some
sub-plurality `z ⊆ x`. This captures K&S's predictions in monotonic
contexts but is **not** their actual `Cand_x`: K&S build candidates from
convex closures of sub-plurality bundles (substrate at
`ordConnectedHull`), yielding generalised-quantifier candidates
that pattern with [schwarzschild-1996]-style covers and
[brisson-1998]'s ill-fitting covers but diverge in non-monotonic
contexts. For the cases formalised here the two predictions coincide; the
divergent non-monotonic cases are flagged in the Todo.

The contrast with [malamud-2012]'s earlier disjunctive aggregation is
made kernel-checked in `malamud_strictly_weaker_when_mixed`.

## Main declarations

* `pluralTruthValue` — trivalent K&S denotation via `Trivalent.dist`.
* `inGap`, `homogeneity_gap_symmetric`, `pluralTruthValue_neg` — the
  homogeneity theorem.
* `candidateProp`, `fullCandidateSet`, `candidateSet` — the (cover-cell)
  candidate-set machinery.
* `trueOnAll`, `falseOnAll`, `gapOnCandidates` — the truth-on-all-readings
  trichotomy.
* `pluralTruthValue_{true,false,indet}_iff_*` — correspondence between
  trivalent denotation and candidate semantics.
* `HomParam`, `isAdmissible`, `interpWithH`, `allViaForallH` — homogeneity
  parameter machinery (single-argument, sub-plurality-valued simplification
  of K&S's multi-argument GQ-valued `H`).
* `malamudDisjunction`, `malamud_strictly_weaker_when_mixed` — the
  [malamud-2012] contrast made kernel-checked.

## Implementation notes

Strong relevance (constancy on QUD cells) is defined at the substrate level
in `Semantics/Plurality/Homogeneity/Basic.lean` as
`Semantics.Homogeneity.isStronglyRelevantProp` and re-exported here.
The bivalent bridge to [kriz-2016]'s `addressesIssue` is proved in
`Studies/KrizSpector2021.lean`.

## Todo

* Replace `candidateProp` with K&S's faithful `Cand_x` (def. 21 in
  [kriz-spector-2021] — UNVERIFIED definition number) via
  `ordConnectedHull`. Current simplification matches K&S
  predictions only in monotonic contexts; non-monotonic cases (e.g. the
  "exactly one student read the books" example, see
  `Studies/KrizSpector2021.lean`) require the enriched generalised
  quantifiers.
* Re-type `HomParam` as `ArgIdx × Finset Atom → Cand_x` to support K&S's
  multi-argument candidate selection (their Desideratum B on co-referential
  plurals).
* Bridge to [bar-lev-2021]'s `Exh^{IE+II}` + ∃-PL rival implicature
  account.
-/

namespace Semantics.Plurality.Trivalent

open Semantics.Homogeneity (isStronglyRelevantProp stronglyRelevantSet
  exact_all_relevant)
open Semantics.Plurality
open Semantics.Plurality.Implicature (existPL)

variable {Atom W : Type*} [DecidableEq Atom]

/-! ### Trivalent truth values -/

/-- The trivalent truth value for plural predication "the Xs are P".

- TRUE: all atoms satisfy `P` (vacuously on `∅`)
- FALSE: nonempty plurality with no atoms satisfying `P`
- GAP: witnesses on both sides

This is the core of [kriz-spector-2021]: predication on a plurality
is super-true iff the predicate holds at every atom, super-false iff it
fails at every atom, gap otherwise. The [van-fraassen-1966]
supervaluation framing (each atom as a specification point) is
documented by `Semantics.Supervaluation.superTrue_eq_dist`. -/
@[reducible] def pluralTruthValue (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) : _root_.Trivalent :=
  Trivalent.dist x (fun a => P a w)

@[simp]
theorem pluralTruthValue_eq_true_iff (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    pluralTruthValue P x w = .true ↔ allSatisfy P x w :=
  Trivalent.dist_eq_true_iff x _

@[simp]
theorem pluralTruthValue_eq_false_iff (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    pluralTruthValue P x w = .false ↔ x.Nonempty ∧ noneSatisfy P x w :=
  Trivalent.dist_eq_false_iff x _

@[simp]
theorem pluralTruthValue_eq_gap_iff (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    pluralTruthValue P x w = .indet ↔
    (∃ a ∈ x, P a w) ∧ (∃ a ∈ x, ¬ P a w) :=
  Trivalent.dist_eq_indet_iff x _

theorem allSatisfy_imp_noneSatisfy_neg (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    allSatisfy P x w → noneSatisfy (fun a w => ¬ P a w) x w := by
  intro h a ha hPa; exact hPa (h a ha)

theorem noneSatisfy_imp_allSatisfy_neg (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    noneSatisfy P x w → allSatisfy (fun a w => ¬ P a w) x w := id

/-! ### The homogeneity theorem -/

/-- The gap condition: some but not all atoms satisfy `P`. -/
def inGap (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) : Prop :=
  (∃ a ∈ x, P a w) ∧ (∃ a ∈ x, ¬ P a w)

/-- **Homogeneity Theorem** ([kriz-spector-2021]). The gap is
    symmetric under negation: a world is in the gap for `P` iff it is
    in the gap for `¬P`. This explains why "the Xs are P" and "the Xs
    aren't P" are both undefined in exactly the same worlds. -/
theorem homogeneity_gap_symmetric (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    inGap P x w ↔ inGap (fun a w => ¬ P a w) x w := by
  unfold inGap
  refine ⟨fun ⟨⟨a, ha, hPa⟩, ⟨b, hb, hPb⟩⟩ => ?_,
          fun ⟨⟨a, ha, hnPa⟩, ⟨b, hb, hnnPb⟩⟩ => ?_⟩
  · exact ⟨⟨b, hb, hPb⟩, ⟨a, ha, fun hnPa => hnPa hPa⟩⟩
  · refine ⟨⟨b, hb, ?_⟩, ⟨a, ha, hnPa⟩⟩
    by_contra hPb; exact hnnPb hPb

/-- Corollary: `pluralTruthValue` is gap iff the negated version is gap. -/
theorem pluralTruthValue_gap_iff_neg_gap (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) (_hne : x.Nonempty) :
    pluralTruthValue P x w = .indet ↔
    pluralTruthValue (fun a w => ¬ P a w) x w = .indet := by
  rw [pluralTruthValue_eq_gap_iff, pluralTruthValue_eq_gap_iff]
  refine ⟨fun ⟨⟨a, ha, hPa⟩, ⟨b, hb, hnPb⟩⟩ => ?_,
          fun ⟨⟨a, ha, hnPa⟩, ⟨b, hb, hnnPb⟩⟩ => ?_⟩
  · exact ⟨⟨b, hb, hnPb⟩, ⟨a, ha, fun hnPa => hnPa hPa⟩⟩
  · refine ⟨⟨b, hb, ?_⟩, ⟨a, ha, hnPa⟩⟩
    by_contra hPb; exact hnnPb hPb

/-- **Homogeneity Polarity**: truth and falsity swap under negation
    on nonempty pluralities; the gap is preserved. Empty `x` makes both
    `allSatisfy P` and `allSatisfy ¬P` vacuously true, so the theorem
    requires `x.Nonempty`. -/
theorem pluralTruthValue_neg (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) (hne : x.Nonempty) :
    pluralTruthValue (fun a w => ¬ P a w) x w =
    match pluralTruthValue P x w with
    | .true => .false
    | .false => .true
    | .indet => .indet := by
  cases h : pluralTruthValue P x w
  · rw [pluralTruthValue_eq_true_iff] at h
    rw [pluralTruthValue_eq_false_iff]
    exact ⟨hne, fun a ha hnPa => hnPa (h a ha)⟩
  · rw [pluralTruthValue_eq_false_iff] at h
    rw [pluralTruthValue_eq_true_iff]
    intro a ha hPa; exact h.2 a ha hPa
  · rw [pluralTruthValue_eq_gap_iff] at h
    rw [pluralTruthValue_eq_gap_iff]
    obtain ⟨⟨a, ha, hPa⟩, ⟨b, hb, hnPb⟩⟩ := h
    exact ⟨⟨b, hb, hnPb⟩, ⟨a, ha, fun hnPa => hnPa hPa⟩⟩

/-! ### Candidate interpretations -/

/-- The candidate proposition for sub-plurality `z`: `P` holds of every atom
    in `z`. This is the **cover-cell simplification** of
    [kriz-spector-2021]'s candidate; see module-level Todo for the
    convex-closure-enriched faithful version. Definitionally equal to
    `distMaximal P z`. -/
def candidateProp (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (z : Finset Atom) : W → Prop :=
  distMaximal P z

instance (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (z : Finset Atom) (w : W) : Decidable (candidateProp P z w) :=
  inferInstanceAs (Decidable (distMaximal P z w))

/-- Full candidate set: all nonempty sub-plurality propositions. -/
def fullCandidateSet (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) : Set (W → Prop) :=
  { p | ∃ z ∈ x.powerset, z.Nonempty ∧ p = candidateProp P z }

/-- Candidate set filtered by a tolerance relation. With identity tolerance
    only the maximal candidate survives; with trivial tolerance every
    nonempty sub-plurality candidate is included. -/
def candidateSet (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (tol : Tolerance Atom) (x : Finset Atom) : Set (W → Prop) :=
  { p | ∃ z ∈ x.powerset, z.Nonempty ∧ tol.rel z x ∧ p = candidateProp P z }

/-! ### _root_.Trivalent-on-all-readings trichotomy -/

/-- All candidates in the set hold at `w`. -/
def trueOnAll (candidates : Set (W → Prop)) (w : W) : Prop :=
  ∀ p ∈ candidates, p w

/-- All candidates in the set fail at `w`. -/
def falseOnAll (candidates : Set (W → Prop)) (w : W) : Prop :=
  ∀ p ∈ candidates, ¬ p w

/-- Some candidates true, some false at `w` (the homogeneity gap). -/
def gapOnCandidates (candidates : Set (W → Prop)) (w : W) : Prop :=
  (∃ p ∈ candidates, p w) ∧ (∃ p ∈ candidates, ¬ p w)

/-! ### Identity- and trivial-tolerance reductions -/

theorem identity_candidateSet_eq_singleton (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (hne : x.Nonempty) :
    candidateSet P Tolerance.identity x = {candidateProp P x} := by
  ext p
  simp only [candidateSet, Set.mem_setOf_eq, Set.mem_singleton_iff,
             Finset.mem_powerset, Tolerance.identity]
  refine ⟨fun ⟨_, _, _, hz_eq, hp⟩ => ?_, fun hp => ?_⟩
  · rw [← hz_eq, hp]
  · exact ⟨x, Finset.Subset.refl x, hne, rfl, hp⟩

theorem fullCandidateSet_eq_candidateSet_trivial (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) :
    fullCandidateSet P x = candidateSet P Tolerance.trivial x := by
  ext p
  simp only [fullCandidateSet, candidateSet, Set.mem_setOf_eq]
  refine ⟨fun ⟨z, hz_mem, hne, hp⟩ => ?_, fun ⟨z, hz_mem, hne, _, hp⟩ => ?_⟩
  · exact ⟨z, hz_mem, hne, Finset.mem_powerset.mp hz_mem, hp⟩
  · exact ⟨z, hz_mem, hne, hp⟩

/-- Identity tolerance is just plurality equality. -/
theorem identity_tolerant_iff_eq (x z : Finset Atom) :
    Tolerance.identity.rel z x ↔ z = x := Iff.rfl

/-! ### _root_.Trivalent-on-all ↔ trivalent semantics

Three correspondence lemmas connecting `trueOnAll` / `falseOnAll` /
`gapOnCandidates` over the (cover-cell) candidate set to the trivalent
`pluralTruthValue`. -/

theorem trueOnAll_full_iff_allSatisfy (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    trueOnAll (fullCandidateSet P x) w ↔ allSatisfy P x w := by
  refine ⟨fun h a ha => ?_, fun h p hp => ?_⟩
  · have hsing : candidateProp P {a} ∈ fullCandidateSet P x :=
      ⟨{a}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr ha),
       ⟨a, Finset.mem_singleton.mpr rfl⟩, rfl⟩
    have := h (candidateProp P {a}) hsing
    simpa [candidateProp, distMaximal] using this
  · obtain ⟨z, hz_mem, _, rfl⟩ := hp
    intro a ha
    exact h a (Finset.mem_powerset.mp hz_mem ha)

theorem falseOnAll_full_iff_noneSatisfy (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) (_hne : x.Nonempty) :
    falseOnAll (fullCandidateSet P x) w ↔ noneSatisfy P x w := by
  refine ⟨fun h a ha hPa => ?_, fun h p hp => ?_⟩
  · have hsing : candidateProp P {a} ∈ fullCandidateSet P x :=
      ⟨{a}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr ha),
       ⟨a, Finset.mem_singleton.mpr rfl⟩, rfl⟩
    have hf := h (candidateProp P {a}) hsing
    apply hf
    intro b hb; rw [Finset.mem_singleton.mp hb]; exact hPa
  · obtain ⟨z, hz_mem, ⟨a, ha⟩, rfl⟩ := hp
    intro hall
    exact h a (Finset.mem_powerset.mp hz_mem ha) (hall a ha)

theorem pluralTruthValue_true_iff_trueOnAll (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    pluralTruthValue P x w = .true ↔ trueOnAll (fullCandidateSet P x) w := by
  rw [pluralTruthValue_eq_true_iff, trueOnAll_full_iff_allSatisfy]

theorem pluralTruthValue_false_iff_falseOnAll (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) (hne : x.Nonempty) :
    pluralTruthValue P x w = .false ↔ falseOnAll (fullCandidateSet P x) w := by
  rw [pluralTruthValue_eq_false_iff, falseOnAll_full_iff_noneSatisfy P x w hne]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hne, h⟩⟩

theorem pluralTruthValue_indet_iff_gapOnCandidates (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    pluralTruthValue P x w = .indet ↔
    gapOnCandidates (fullCandidateSet P x) w := by
  rw [pluralTruthValue_eq_gap_iff]
  refine ⟨fun ⟨⟨a, ha, hPa⟩, ⟨b, hb, hPb⟩⟩ => ?_,
          fun ⟨⟨pt, hpt_mem, hpt_true⟩, ⟨pf, hpf_mem, hpf_false⟩⟩ => ?_⟩
  · refine ⟨⟨candidateProp P {a}, ?_, ?_⟩, ⟨candidateProp P {b}, ?_, ?_⟩⟩
    · exact ⟨{a}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr ha),
             ⟨a, Finset.mem_singleton.mpr rfl⟩, rfl⟩
    · intro c hc; rw [Finset.mem_singleton.mp hc]; exact hPa
    · exact ⟨{b}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hb),
             ⟨b, Finset.mem_singleton.mpr rfl⟩, rfl⟩
    · intro hsing; exact hPb (hsing b (Finset.mem_singleton.mpr rfl))
  · obtain ⟨z, hz, ⟨b, hb⟩, rfl⟩ := hpt_mem
    obtain ⟨z', hz', _, rfl⟩ := hpf_mem
    refine ⟨⟨b, Finset.mem_powerset.mp hz hb, hpt_true b hb⟩, ?_⟩
    by_contra hc
    push Not at hc
    apply hpf_false
    intro a ha
    exact hc a (Finset.mem_powerset.mp hz' ha)

/-- Consolidated form bundling the three correspondence lemmas. -/
theorem pluralTruthValue_eq_candidateSemantics (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) (hne : x.Nonempty) :
    (pluralTruthValue P x w = .true ↔ trueOnAll (fullCandidateSet P x) w) ∧
    (pluralTruthValue P x w = .false ↔ falseOnAll (fullCandidateSet P x) w) ∧
    (pluralTruthValue P x w = .indet ↔
      gapOnCandidates (fullCandidateSet P x) w) :=
  ⟨pluralTruthValue_true_iff_trueOnAll P x w,
   pluralTruthValue_false_iff_falseOnAll P x w hne,
   pluralTruthValue_indet_iff_gapOnCandidates P x w⟩

/-! ### QUD relevance for K&S candidates

`isStronglyRelevantProp` lives in `Semantics.Homogeneity` (substrate);
these are the K&S-specific specialisations applied to `candidateProp`. -/

/-- The maximal candidate is always strongly relevant to the exact QUD. -/
theorem maximal_relevant_to_exact [BEq W] [LawfulBEq W] (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) :
    isStronglyRelevantProp (QUD.exact (M := W)) (candidateProp P x) :=
  exact_all_relevant _

/-- Non-Maximality from a coarse QUD: when the QUD groups an all-true world
    with a not-all-true world, the maximal candidate is not strongly
    relevant — opening the door to a non-maximal interpretation. -/
theorem nonMaximality_from_coarse_qud (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (q : QUD W)
    (w_all w_almost : W)
    (h_equiv : q.r w_all w_almost)
    (h_all : allSatisfy P x w_all)
    (h_not_all : ¬ allSatisfy P x w_almost) :
    ¬ isStronglyRelevantProp q (candidateProp P x) := by
  intro hsr
  exact h_not_all ((hsr w_all w_almost h_equiv).mp h_all)

/-! ### The homogeneity parameter H

K&S parameterise interpretation by `H`, mapping each argument position to a
candidate denotation. The formalisation here treats `H` as a
**single-argument** sub-plurality selector — a simplification of K&S's
multi-argument candidate-GQ-valued `H` (their H is morally
`ArgIdx × Plurality → Cand_x`, supporting their Desideratum B on
co-referential plural arguments). The reductive `allViaForallH_iff_allSatisfy`
below reflects this simplification: K&S's actual `H` does not collapse to
atom-universal in non-monotonic positions. -/

/-- A homogeneity parameter selects, for each plurality, a sub-plurality. -/
def HomParam (Atom : Type*) : Type _ := Finset Atom → Finset Atom

/-- An admissible homogeneity parameter maps `x` to a nonempty sub-plurality. -/
def isAdmissible (H : HomParam Atom) (x : Finset Atom) : Prop :=
  H x ⊆ x ∧ (H x).Nonempty

/-- The identity parameter `H(x) = x` (universal/maximal reading). -/
def HomParam.id : HomParam Atom := fun x => x

theorem isAdmissible_id (x : Finset Atom) (hne : x.Nonempty) :
    isAdmissible (HomParam.id (Atom := Atom)) x :=
  ⟨Finset.Subset.refl x, hne⟩

/-- Interpretation of a distributive predicate parameterised by `H`. -/
def interpWithH (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (H : HomParam Atom) (x : Finset Atom) (w : W) : Prop :=
  ∀ a ∈ H x, P a w

instance (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (H : HomParam Atom) (x : Finset Atom) (w : W) :
    Decidable (interpWithH P H x w) :=
  inferInstanceAs (Decidable (∀ a ∈ H x, P a w))

/-- Universal quantification over admissible `H`. -/
def allViaForallH (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) : Prop :=
  ∀ H : HomParam Atom, isAdmissible H x → interpWithH P H x w

/-- Universal `H`-quantification reduces to atom-wise universal, in the
    file's simplified `H` typing. K&S's actual `H`, valued in candidate
    GQs, does not collapse this way in non-monotonic positions. -/
theorem allViaForallH_iff_allSatisfy (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    allViaForallH P x w ↔ allSatisfy P x w := by
  refine ⟨fun hall a ha => ?_, fun hall H hAdm a ha => hall a (hAdm.1 ha)⟩
  have hAdm : isAdmissible (fun _ => ({a} : Finset Atom)) x :=
    ⟨Finset.singleton_subset_iff.mpr ha, ⟨a, Finset.mem_singleton.mpr rfl⟩⟩
  exact hall (fun _ => {a}) hAdm a (Finset.mem_singleton.mpr rfl)

/-- Trivalent truth via `H`-quantification matches `pluralTruthValue`. -/
theorem forallH_true_iff_pluralTrue (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    allViaForallH P x w ↔ pluralTruthValue P x w = .true := by
  rw [allViaForallH_iff_allSatisfy, pluralTruthValue_eq_true_iff]

/-! ### Candidate conjunction vs Malamud's disjunction

K&S compute sentence meaning as the **conjunction** of all strongly relevant
candidate interpretations. [malamud-2012]'s earlier proposal used
**disjunction**: a sentence is true iff some candidate is. The contrast is
empirically critical in non-monotonic contexts and was K&S's headline
departure from Malamud; the divergence theorem below makes the prose claim
kernel-checked. -/

/-- _root_.Trivalent-on-all trichotomy: a candidate set is true-on-all, false-on-all,
    or mixed (gap). Classical disjunction over decidable cases. -/
theorem candidateConjunction_trichotomy (candidates : Set (W → Prop)) (w : W)
    [Decidable (trueOnAll candidates w)]
    [Decidable (falseOnAll candidates w)] :
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
      exact ⟨⟨p₂, hp₂, hne₂⟩, ⟨p₁, hp₁, hne₁⟩⟩

/-- [malamud-2012]'s disjunctive aggregation: a sentence is true iff
    *some* candidate is. Contrasts with `trueOnAll`'s conjunctive
    aggregation. -/
def malamudDisjunction (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) : Prop :=
  ∃ p ∈ fullCandidateSet P x, p w

/-- K&S's conjunction entails Malamud's disjunction, given any atom witness
    to make the candidate set inhabited. -/
theorem trueOnAll_imp_malamud (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) (a : Atom) (ha : a ∈ x) :
    trueOnAll (fullCandidateSet P x) w → malamudDisjunction P x w := by
  intro hAll
  have hMem : candidateProp P {a} ∈ fullCandidateSet P x :=
    ⟨{a}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr ha),
     ⟨a, Finset.mem_singleton.mpr rfl⟩, rfl⟩
  exact ⟨candidateProp P {a}, hMem, hAll _ hMem⟩

/-- **Divergence theorem.** When `P` has mixed truth values on `x` at `w`
    — at least one atom satisfies `P` and at least one does not — Malamud's
    disjunction holds at `w` while K&S's conjunction fails. K&S's prose
    departure from [malamud-2012] made kernel-checked. -/
theorem malamud_strictly_weaker_when_mixed (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W)
    (h_some : ∃ a ∈ x, P a w) (h_other : ∃ b ∈ x, ¬ P b w) :
    malamudDisjunction P x w ∧ ¬ trueOnAll (fullCandidateSet P x) w := by
  obtain ⟨a, ha, hPa⟩ := h_some
  obtain ⟨b, hb, hPb⟩ := h_other
  refine ⟨⟨candidateProp P {a}, ?_, ?_⟩, ?_⟩
  · exact ⟨{a}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr ha),
           ⟨a, Finset.mem_singleton.mpr rfl⟩, rfl⟩
  · intro c hc; rw [Finset.mem_singleton.mp hc]; exact hPa
  · intro hAll
    have hSingB : candidateProp P {b} ∈ fullCandidateSet P x :=
      ⟨{b}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hb),
       ⟨b, Finset.mem_singleton.mpr rfl⟩, rfl⟩
    exact hPb (hAll _ hSingB b (Finset.mem_singleton.mpr rfl))

/-! ### Bridge to Bar-Lev's `existPL`

[malamud-2012]'s disjunctive aggregation collapses to
[bar-lev-2021]'s `existPL` with full domain: both express
"some atom satisfies `P`". This makes the prior Bar-Lev / K&S
silent-divergence connection kernel-checked. The K&S divergence
theorem (`malamud_strictly_weaker_when_mixed`) immediately yields
the polarity-asymmetric `existPL` divergence corollary below. -/

/-- Malamud's disjunctive aggregation IS Bar-Lev's `existPL` on the
    full domain. Establishes that the two prose-cited rival
    frameworks coincide on this primitive. -/
theorem malamudDisjunction_eq_existPL_full
    (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) :
    malamudDisjunction P x w ↔ existPL x P x w := by
  refine ⟨?_, ?_⟩
  · rintro ⟨p, ⟨z, hz_mem, ⟨a, ha⟩, rfl⟩, hp⟩
    exact ⟨a, Finset.mem_powerset.mp hz_mem ha, Finset.mem_powerset.mp hz_mem ha,
           hp a ha⟩
  · rintro ⟨a, ha, _, hPa⟩
    refine ⟨candidateProp P {a}, ?_, ?_⟩
    · exact ⟨{a}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr ha),
             ⟨a, Finset.mem_singleton.mpr rfl⟩, rfl⟩
    · intro b hb; rw [Finset.mem_singleton.mp hb]; exact hPa

/-- **Divergence theorem (Bar-Lev vs K&S).** On mixed-truth data,
    Bar-Lev's `existPL` (bivalent existential) holds while K&S's
    `pluralTruthValue` is not `.true`. This is the polarity-asymmetric
    contrast that distinguishes implicature-strengthening accounts from
    trivalent-gap accounts in non-monotonic contexts. -/
theorem existPL_not_eq_pluralTruthValue_true
    (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W)
    (h_some : ∃ a ∈ x, P a w) (h_other : ∃ b ∈ x, ¬ P b w) :
    existPL x P x w ∧ pluralTruthValue P x w ≠ .true := by
  obtain ⟨a, ha, hPa⟩ := h_some
  obtain ⟨b, hb, hPb⟩ := h_other
  refine ⟨⟨a, ha, ha, hPa⟩, fun h => ?_⟩
  have hAll : allSatisfy P x w := (pluralTruthValue_eq_true_iff P x w).mp h
  exact hPb (hAll b hb)

/-! ### Bridge to [schwarzschild-1996] covers

Cover and Trivalent operate at different conceptual levels — Cover is
a relation on `Set (Finset Atom) × Finset Atom` ("these parts cover
that whole"), Trivalent's candidate is a function `Finset Atom →
(W → Prop)` ("this sub-plurality produces this proposition"). They
share the substrate of "non-empty sub-pluralities of `x`" but the
operations remain distinct. The bridge below makes the forward
direction explicit: every cell of a finite cover produces a candidate
in `fullCandidateSet`. -/

/-- **Cover cells are candidates**: any non-empty cell of a finite
    cover of `x` (in the [schwarzschild-1996] sense) corresponds
    to a candidate in `fullCandidateSet P x`. The cover relation
    constrains how parts join to `x`; the candidate function lifts
    each part to its sub-plurality-universal proposition. -/
theorem mem_fullCandidateSet_of_cover_cell
    (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) {parts : Finset (Finset Atom)} {hne : parts.Nonempty}
    (hCover : Semantics.Plurality.Cover.IsFinCover parts hne x)
    {z : Finset Atom} (hz : z ∈ parts) (hzNe : z.Nonempty) :
    candidateProp P z ∈ fullCandidateSet P x := by
  refine ⟨z, Finset.mem_powerset.mpr ?_, hzNe, rfl⟩
  have h_le : z ≤ parts.sup' hne id := Finset.le_sup' id hz
  unfold Semantics.Plurality.Cover.IsFinCover at hCover
  rw [hCover] at h_le
  exact h_le

end Semantics.Plurality.Trivalent
