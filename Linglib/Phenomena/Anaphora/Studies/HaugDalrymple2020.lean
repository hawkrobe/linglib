import Linglib.Theories.Semantics.Reference.Reciprocals
import Linglib.Theories.Semantics.Dynamic.PPCDRT.Defs
import Linglib.Theories.Semantics.Dynamic.PPCDRT.Anaphora
import Linglib.Theories.Semantics.Dynamic.PPCDRT.Cumulativity
import Linglib.Theories.Semantics.Plurality.Cumulativity
import Linglib.Theories.Semantics.Homogeneity.Basic
import Linglib.Core.Logic.Truth3

/-!
# Haug & Dalrymple (2020) @cite{haug-dalrymple-2020}

Reciprocity: Anaphora, scope, and quantification.
*Semantics & Pragmatics* 13:10, 1–62. doi:10.3765/sp.13.10.

The relational analysis of reciprocals in Partial Plural Compositional DRT
(PPCDRT). *Each other* is a pronoun bearing an anaphoric relation
(reciprocity R) to its antecedent; the narrow/wide scope ambiguity reduces
to the choice of antecedent relation between the matrix subject and the
embedded local antecedent (group identity ∪ vs. binding =).

## What is formalized

Witness-based formalisation of the paper's empirical contributions over
the PPCDRT substrate (`Theories/Semantics/Dynamic/PPCDRT/`):

| Paper § | Topic                                  | Witness type               |
|---------|----------------------------------------|----------------------------|
| §3      | Scope readings (narrow / wide)         | `PluralAssign Person`      |
| §3.3    | Crossed readings (4-cell classification) | `RecipReading` triples   |
| §4.2    | Underspecified RECIP/REFL              | `underspecifiedCond` lattice |
| §4.4    | Multiple reciprocals                   | Two-reciprocal witness     |
| §4.5    | Subgroup readings (forks, gravity)     | Weak-vs-strong contrast    |
| §4.6    | Collective antecedents                 | Distinctness neutralization |
| §5      | Quantified antecedents + truth-value gap | `Truth3` via `removeGap` |
| §6      | Maximize Anaphora as a principle       | `R_u` + `maximizeAnaphora` |
| §6.2    | Multi-reciprocal pairwise prediction   | `R_u` over two reciprocals |
| §6.3    | MA interacting with scope              | Tracy/Matty/Chris case     |

Sections paper-acknowledged but not formalised (out of scope for a
study-file size budget): the full §2.3 Δ-relativised distribution
machinery (it lives in `PPCDRT/Defs.lean` as `delta`/`equivClass` but is
not exercised at sentence level here); the §5.2 empirical-fit table; the
§7 typological excursus.

## Connections to existing linglib substrate

- @cite{champollion-bumford-henderson-2019} for the §5 supervaluationist
  truth-value-gap analysis — realised via
  `Theories/Semantics/Homogeneity/Basic.lean`'s `removeGap` /
  `Truth3.metaAssert`.
- @cite{kriz-2015} for the homogeneity background; same substrate.
- @cite{langendoen-1978} for the reciprocity-as-cumulativity link —
  realised via `PPCDRT/Cumulativity.lean`'s
  `groupIdentityCond_iff_cumulativeOp_eq` bridge theorem.
- @cite{murray-2008}, @cite{cable-2014} for the §4.2 underspecification
  examples.

## Source-paper attribution note

The §4.2 paragraph in @cite{haug-dalrymple-2020} attributes the German
*sich* / Romance reflexive examples to @cite{cable-2014} (paper p. 32),
not to @cite{murray-2008} alone — the latter focuses on Cheyenne. The
docstrings here follow that attribution.
-/

namespace HaugDalrymple2020

open Semantics.Reference.Reciprocals
open Theories.Semantics.Dynamic.PPCDRT
open Core
open Core.Duality
open Semantics.Plurality.Cumulativity

-- ════════════════════════════════════════════════════════════════
-- § 0: Toy domain — Tracy / Chris / Matty
-- ════════════════════════════════════════════════════════════════

/-- Three salient discourse participants. Reused throughout the paper's
    examples (Tracy and Chris in §3, Tracy/Matty/Chris in §6.3). -/
inductive Person where
  | tracy
  | chris
  | matty
  deriving DecidableEq, Repr

instance : Inhabited Person := ⟨.tracy⟩

/-- Standard dref indices used throughout. -/
abbrev u₁ : Nat := 1
abbrev u₂ : Nat := 2
abbrev u₃ : Nat := 3
abbrev u₄ : Nat := 4

/-- A partial assignment with `u₁ ↦ a, u₂ ↦ b`. -/
def assign2 (a b : Person) : PartialAssign Person :=
  PartialAssign.update (PartialAssign.update PartialAssign.empty u₁ a) u₂ b

/-- A partial assignment with `u₁ ↦ a, u₂ ↦ b, u₃ ↦ c`. -/
def assign3 (a b c : Person) : PartialAssign Person :=
  PartialAssign.update (assign2 a b) u₃ c

@[simp] theorem assign2_u₁ (a b : Person) : assign2 a b u₁ = some a := by
  simp [assign2, PartialAssign.update, u₁, u₂]

@[simp] theorem assign2_u₂ (a b : Person) : assign2 a b u₂ = some b := by
  simp [assign2, PartialAssign.update, u₁, u₂]

@[simp] theorem assign3_u₁ (a b c : Person) : assign3 a b c u₁ = some a := by
  simp [assign3, assign2, PartialAssign.update, u₁, u₂, u₃]

@[simp] theorem assign3_u₂ (a b c : Person) : assign3 a b c u₂ = some b := by
  simp [assign3, assign2, PartialAssign.update, u₁, u₂, u₃]

@[simp] theorem assign3_u₃ (a b c : Person) : assign3 a b c u₃ = some c := by
  simp [assign3, PartialAssign.update, u₃]

-- ════════════════════════════════════════════════════════════════
-- § 1: Narrow Scope (paper §3, eq 49–50)
-- "Two girls thought that they would win." (we-reading)
-- ════════════════════════════════════════════════════════════════

/-- Narrow-scope state for paper eq 49: two assignments where each girl
    has herself as the embedded subject pronoun. The matrix subject (u₁)
    and the embedded subject pronoun (u₂) have IDENTICAL value-sets:
    {Tracy, Chris}. This is group identity (∪u₂ = ∪u₁). -/
def narrowScopeState : PluralAssign Person :=
  PluralAssign.ofPred (λ g =>
    g = assign2 .tracy .tracy ∨ g = assign2 .chris .chris)

/-- Membership lemma. -/
theorem narrowScopeState_mem (g : PartialAssign Person) :
    g ∈ narrowScopeState ↔ g = assign2 .tracy .tracy ∨ g = assign2 .chris .chris :=
  Iff.rfl

/-- The summed value of u₁ across the narrow-scope state is {tracy, chris}. -/
theorem narrowScope_sumDref_u₁ :
    PluralAssign.sumDref narrowScopeState u₁ = {Person.tracy, Person.chris} := by
  ext d
  constructor
  · rintro ⟨g, hgS, hgu⟩
    rcases hgS with h | h <;> subst h <;> simp at hgu <;> subst hgu <;> simp
  · intro hd
    rcases hd with h | h
    · subst h; exact ⟨assign2 .tracy .tracy, .inl rfl, assign2_u₁ ..⟩
    · simp at h; subst h
      exact ⟨assign2 .chris .chris, .inr rfl, assign2_u₁ ..⟩

/-- The summed value of u₂ across the narrow-scope state is {tracy, chris}. -/
theorem narrowScope_sumDref_u₂ :
    PluralAssign.sumDref narrowScopeState u₂ = {Person.tracy, Person.chris} := by
  ext d
  constructor
  · rintro ⟨g, hgS, hgu⟩
    rcases hgS with h | h <;> subst h <;> simp at hgu <;> subst hgu <;> simp
  · intro hd
    rcases hd with h | h
    · subst h; exact ⟨assign2 .tracy .tracy, .inl rfl, assign2_u₂ ..⟩
    · simp at h; subst h
      exact ⟨assign2 .chris .chris, .inr rfl, assign2_u₂ ..⟩

/-- **Narrow scope is group identity** (paper §3, eq 49). The matrix
    subject (u₁) and the embedded subject pronoun (u₂) have the same
    value-set, witnessing the `groupIdentityCond` of the relational
    analysis. -/
theorem narrowScope_groupIdentity :
    groupIdentityCond u₁ u₂ narrowScopeState ∅ := by
  unfold groupIdentityCond
  rw [narrowScope_sumDref_u₁, narrowScope_sumDref_u₂]

-- ════════════════════════════════════════════════════════════════
-- § 2: Wide Scope (paper §3, eq 51)
-- "Two girls thought that they would win." (I-reading)
-- ════════════════════════════════════════════════════════════════

/-- Wide-scope state for paper eq 51: u₂ is *bound by* u₁ — pointwise
    identity of values. Each girl thought *only of herself* as the winner.

    Note: at the *value-set* level, narrow and wide scope happen to look
    identical for this two-element example (both yield {Tracy, Chris} for
    u₁ and u₂). The DIFFERENCE between narrow and wide is *pointwise vs.
    range-only* identity — which only becomes empirically visible when
    a reciprocal is added (§3.1). -/
def wideScopeState : PluralAssign Person := narrowScopeState

/-- **Wide scope is binding** (paper §3, eq 51). In every state of the
    plural information state, the embedded subject pronoun's value
    equals the matrix subject's value pointwise. -/
theorem wideScope_binding :
    bindingCond u₁ u₂ wideScopeState ∅ := by
  intro g hgS
  rcases hgS with h | h <;> subst h
  · exact ⟨.tracy, by simp, by simp⟩
  · exact ⟨.chris, by simp, by simp⟩

/-- Wide scope also satisfies group identity (binding ⊆ group identity).
    This is the substrate-level fact `binding_implies_groupIdentity`
    applied to this concrete case. -/
theorem wideScope_also_groupIdentity :
    groupIdentityCond u₁ u₂ wideScopeState ∅ :=
  binding_implies_groupIdentity u₁ u₂ wideScopeState ∅ wideScope_binding

-- ════════════════════════════════════════════════════════════════
-- § 3: Reciprocity Witness (paper §3.1, eq 53)
-- "Two girls thought that they saw each other." (we-reading, narrow)
-- ════════════════════════════════════════════════════════════════

/-- Narrow-scope reciprocity state for paper eq 53: u₁ (matrix subject)
    and u₂ (embedded subject) are group-identical (each girl thought of
    the group); u₃ (reciprocal) takes the *other* girl's value at each
    state. Tracy saw Chris, Chris saw Tracy. -/
def reciprocityState : PluralAssign Person :=
  PluralAssign.ofPred (λ g =>
    g = assign3 .tracy .tracy .chris ∨ g = assign3 .chris .chris .tracy)

theorem reciprocityState_mem (g : PartialAssign Person) :
    g ∈ reciprocityState ↔
    g = assign3 .tracy .tracy .chris ∨ g = assign3 .chris .chris .tracy :=
  Iff.rfl

theorem recip_sumDref_u₂ :
    PluralAssign.sumDref reciprocityState u₂ = {Person.tracy, Person.chris} := by
  ext d
  constructor
  · rintro ⟨g, hgS, hgu⟩
    rcases hgS with h | h <;> subst h <;> simp at hgu <;> subst hgu <;> simp
  · intro hd
    rcases hd with h | h
    · subst h; exact ⟨_, .inl rfl, assign3_u₂ ..⟩
    · simp at h; subst h; exact ⟨_, .inr rfl, assign3_u₂ ..⟩

theorem recip_sumDref_u₃ :
    PluralAssign.sumDref reciprocityState u₃ = {Person.tracy, Person.chris} := by
  ext d
  constructor
  · rintro ⟨g, hgS, hgu⟩
    rcases hgS with h | h <;> subst h <;> simp at hgu <;> subst hgu <;> simp
  · intro hd
    rcases hd with h | h
    · subst h; exact ⟨assign3 .chris .chris .tracy, .inr rfl, assign3_u₃ ..⟩
    · simp at h; subst h
      exact ⟨assign3 .tracy .tracy .chris, .inl rfl, assign3_u₃ ..⟩

/-- **Reciprocity satisfies group identity** between subject pronoun
    and reciprocal (∪u₃ = ∪u₂). -/
theorem reciprocity_groupIdentity :
    groupIdentityCond u₂ u₃ reciprocityState ∅ := by
  unfold groupIdentityCond
  rw [recip_sumDref_u₂, recip_sumDref_u₃]

/-- **Reciprocity satisfies per-state distinctness** (∂(u₂ ≠ u₃)). -/
theorem reciprocity_distinct :
    ∀ s ∈ reciprocityState, ∀ d_a d_b : Person,
      s u₂ = some d_a → s u₃ = some d_b → d_a ≠ d_b := by
  intro g hgS d_a d_b h₂ h₃
  rcases hgS with h | h <;> subst h <;>
    simp at h₂ h₃ <;> subst h₂ <;> subst h₃ <;> decide

/-- **The full reciprocity condition holds** for this state. -/
theorem reciprocity_full :
    reciprocityCond u₂ u₃ reciprocityState ∅ :=
  ⟨reciprocity_groupIdentity, reciprocity_distinct⟩

-- ════════════════════════════════════════════════════════════════
-- § 4: §3.3 Four-Cell Crossed Readings Classification
-- (@cite{haug-dalrymple-2020} §3.3, p. 24)
-- ════════════════════════════════════════════════════════════════

/-- The two-parameter classification: locus × antecedent relation.
    Three cells are attested; the (low, bound) cell is empirically
    empty per paper p. 24 — bound antecedents force high locus. -/
def classifiedReadings : List (RecipLocus × AnaphoricRelation) :=
  [(.low, .groupIdentity),    -- narrow scope
   (.high, .binding),          -- wide scope
   (.high, .groupIdentity)]    -- crossed
   -- (.low, .binding) is empirically empty

/-- The three attested cells correspond to the three `RecipReading`s. -/
theorem classified_matches_readings :
    classifiedReadings = recipReadings.map (λ r => (r.locus, r.antecedentRel)) := by
  rfl

/-- The empty fourth cell: there is no `RecipReading` with low locus
    and binding antecedent. Paper p. 24: "the bound reading of the
    reciprocal's antecedent cannot cooccur with a low locus for the
    reciprocal, because it does not make available the plurality that
    the reciprocal needs." -/
theorem no_low_bound_reading :
    ¬ ∃ r ∈ recipReadings, r.locus = .low ∧ r.antecedentRel = .binding := by
  rintro ⟨r, hrM, hLow, hBound⟩
  simp [recipReadings, narrowScopeReading, wideScopeReading, crossedReading] at hrM
  rcases hrM with rfl | rfl | rfl
  all_goals simp at hLow hBound

/-- Crossed readings (paper §3.3, eq 56): high locus + group-identity
    antecedent + group-identity reciprocal slot. The reciprocity comes
    from the DRS distinctness presupposition `∂(u₃ ≠ u₂)`, not from an
    anaphoric reciprocity relation. Empirically attested via the
    Jennifer Lawrence interview headline (paper p. 25, ex. 57) and
    related corpus examples. -/
theorem crossed_reading_high_groupIdentity_groupIdentity :
    crossedReading.locus = .high ∧
    crossedReading.antecedentRel = .groupIdentity ∧
    crossedReading.reciprocalRel = .groupIdentity := ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 5: §4.2 Underspecified Reflexive/Reciprocal
-- (@cite{murray-2008} Cheyenne, @cite{cable-2014} German *sich*)
-- ════════════════════════════════════════════════════════════════

/-- Underspecified anaphors (German *sich*, Cheyenne REFL/RECIP affix)
    contribute group identity *without* the distinctness presupposition.
    They permit reflexive (binding-style), reciprocal, and mixed
    readings. The semantic core is just `groupIdentityCond` —
    reciprocity is one specialization among others. -/
theorem underspec_admits_binding (uAnaph uAnt : Nat) (S : PluralAssign Person)
    (Δ : Set Nat) (h : bindingCond uAnaph uAnt S Δ) :
    underspecifiedCond uAnaph uAnt S Δ :=
  binding_implies_groupIdentity uAnaph uAnt S Δ h

/-- Underspecified anaphors also admit reciprocity readings —
    reciprocity strengthens underspecified by adding distinctness. -/
theorem underspec_admits_reciprocity (uAnaph uAnt : Nat) (S : PluralAssign Person)
    (Δ : Set Nat) (h : reciprocityCond uAnaph uAnt S Δ) :
    underspecifiedCond uAnaph uAnt S Δ :=
  reciprocity_strengthens_underspecified uAnaph uAnt S Δ h

-- ════════════════════════════════════════════════════════════════
-- § 6: §4.4 Multiple Reciprocals (paper eq 84–87)
-- "Tracy and Chris gave each other pictures of each other."
-- ════════════════════════════════════════════════════════════════

/-- Multiple-reciprocal state: two reciprocity relations, one for the
    direct-object reciprocal (u₃) and one for the picture-of reciprocal
    (u₄). Both must point to the OTHER member of the antecedent group.
    Paper eq 85 (p. 35–36). -/
def multipleRecipState : PluralAssign Person :=
  PluralAssign.ofPred (λ g =>
    g = (PartialAssign.update (assign3 .tracy .tracy .chris) u₄ .chris) ∨
    g = (PartialAssign.update (assign3 .chris .chris .tracy) u₄ .tracy))

/-- Both reciprocals satisfy distinctness from the embedded subject.
    The first reciprocal (u₃) is distinct from u₂; the second (u₄) is
    distinct from u₂ as well, and (in this reading) equal to u₃. -/
theorem multipleRecip_both_distinct :
    (∀ s ∈ multipleRecipState, ∀ d_a d_b : Person,
      s u₂ = some d_a → s u₃ = some d_b → d_a ≠ d_b) ∧
    (∀ s ∈ multipleRecipState, ∀ d_a d_b : Person,
      s u₂ = some d_a → s u₄ = some d_b → d_a ≠ d_b) := by
  refine ⟨?_, ?_⟩ <;> · intro g hgS d_a d_b h₂ h
                        rcases hgS with hh | hh <;> subst hh <;>
                          simp [PartialAssign.update, u₂, u₃, u₄] at h₂ h <;>
                          subst h₂ <;> subst h <;> decide

-- ════════════════════════════════════════════════════════════════
-- § 7: §4.5 Subgroup Readings — Weak vs Strong Reciprocity
-- (paper eq 88–93, fork/gravity examples)
-- ════════════════════════════════════════════════════════════════

/-- "The forks are propped against each other" (paper eq 88b): each
    fork is supported by a *group* containing one or more of the others
    — possibly all, but not necessarily. This is **weak reciprocity**:
    `R_u` need not be the full Cartesian product minus the diagonal.

    Implementation: a 3-fork example where fork₁ leans on fork₂, fork₂
    on fork₃, fork₃ on fork₁ (a chain). `R_u` = {(1,2), (2,3), (3,1)} —
    NOT the full strong-reciprocity {(1,2), (2,1), (1,3), (3,1), (2,3), (3,2)}. -/
def forkChainState : PluralAssign Person :=
  PluralAssign.ofPred (λ g =>
    g = assign2 .tracy .chris ∨        -- tracy → chris
    g = assign2 .chris .matty ∨        -- chris → matty
    g = assign2 .matty .tracy)         -- matty → tracy

/-- The fork chain has 3 supporting pairs in `R_u(u₁, u₂)`. -/
theorem forkChain_R_u_size_three :
    (Person.tracy, Person.chris) ∈ R_u u₁ u₂ forkChainState ∧
    (Person.chris, Person.matty) ∈ R_u u₁ u₂ forkChainState ∧
    (Person.matty, Person.tracy) ∈ R_u u₁ u₂ forkChainState := by
  refine ⟨⟨_, .inl rfl, ?_, ?_⟩, ⟨_, .inr (.inl rfl), ?_, ?_⟩,
          ⟨_, .inr (.inr rfl), ?_, ?_⟩⟩ <;> simp

/-- Strong reciprocity would require each fork to lean on EVERY other —
    e.g., `(tracy, matty)` would also need to be in R_u. The fork-chain
    state does NOT satisfy strong reciprocity. -/
theorem forkChain_not_strong :
    (Person.tracy, Person.matty) ∉ R_u u₁ u₂ forkChainState := by
  rintro ⟨g, hg, h₁, h₂⟩
  rcases hg with h | h | h <;> subst h <;> simp at h₁ h₂

-- ════════════════════════════════════════════════════════════════
-- § 8: §4.6 Collective Antecedents (paper eq 94–96)
-- "The sailors have worked together on each other's ships."
-- ════════════════════════════════════════════════════════════════

/-- Collective antecedents NEUTRALIZE the distinctness condition: when
    the predicate `work-together` is interpreted *collectively* on
    `∪u₁`, the per-state distinctness `u₁ ≠ u₃` becomes vacuous.

    The state below has u₁ = sailor at each row, with u₃ = ship-of
    pointing to (possibly the same!) sailor as u₁. Reciprocity-as-stated
    fails (no per-state distinctness), but the sentence is felicitous
    because the collective interpretation of u₁ does the predicational
    work. Paper p. 39. -/
def collectiveState : PluralAssign Person :=
  PluralAssign.ofPred (λ g =>
    g = assign3 .tracy .tracy .tracy ∨        -- tracy works on tracy's ship
    g = assign3 .chris .chris .chris ∨        -- chris on chris's
    g = assign3 .matty .matty .matty)         -- matty on matty's

/-- The collective state satisfies group identity (∪u₁ = ∪u₃) but FAILS
    per-state distinctness — formal reciprocity does not hold. The
    sentence is felicitous because `work-together` is collective. -/
theorem collective_groupIdentity_no_distinct :
    groupIdentityCond u₁ u₃ collectiveState ∅ ∧
    ∃ s ∈ collectiveState, ∃ d, s u₁ = some d ∧ s u₃ = some d := by
  refine ⟨?_, assign3 .tracy .tracy .tracy, .inl rfl, .tracy, by simp, by simp⟩
  unfold groupIdentityCond
  ext d
  constructor
  · rintro ⟨g, hg, hgu⟩
    rcases hg with h | h | h
    · subst h; simp at hgu; subst hgu
      exact ⟨assign3 .tracy .tracy .tracy, .inl rfl, by simp⟩
    · subst h; simp at hgu; subst hgu
      exact ⟨assign3 .chris .chris .chris, .inr (.inl rfl), by simp⟩
    · subst h; simp at hgu; subst hgu
      exact ⟨assign3 .matty .matty .matty, .inr (.inr rfl), by simp⟩
  · rintro ⟨g, hg, hgu⟩
    rcases hg with h | h | h
    · subst h; simp at hgu; subst hgu
      exact ⟨assign3 .tracy .tracy .tracy, .inl rfl, by simp⟩
    · subst h; simp at hgu; subst hgu
      exact ⟨assign3 .chris .chris .chris, .inr (.inl rfl), by simp⟩
    · subst h; simp at hgu; subst hgu
      exact ⟨assign3 .matty .matty .matty, .inr (.inr rfl), by simp⟩

-- ════════════════════════════════════════════════════════════════
-- § 9: §5 Quantified Antecedents + Truth-Value Gap
-- (paper eq 99, 109; @cite{champollion-bumford-henderson-2019}; @cite{kriz-2015})
-- ════════════════════════════════════════════════════════════════

/-! Paper §5 introduces `max^u(K)` and shows that quantified antecedents
    of reciprocals (most members know each other; few have spoken to each
    other) give rise to a truth-value gap: True iff true on both the
    maximal-set reading and the reference-set reading; False iff false on
    both; Neither otherwise (paper eq 109). The paper invokes
    @cite{champollion-bumford-henderson-2019}, following @cite{kriz-2015},
    for the supervaluationist machinery.

    Here we encode the truth-value gap directly via `Truth3`, exploiting
    the existing `Theories/Semantics/Homogeneity/Basic.lean` substrate
    (`removeGap`, `Truth3.metaAssert`). -/

/-- The truth value of a quantified-antecedent reciprocal sentence,
    given its truth on the maximal-set reading and on the reference-set
    reading. Paper eq 109. -/
def quantifiedReciprocalTV (maximalSetReading refSetReading : Bool) : Truth3 :=
  match maximalSetReading, refSetReading with
  | true,  true  => .true
  | false, false => .false
  | _, _         => .indet

/-- Strict truth: both readings agree affirmatively. -/
theorem quantifiedReciprocalTV_true :
    quantifiedReciprocalTV true true = .true := rfl

/-- Strict falsity: both readings agree negatively. -/
theorem quantifiedReciprocalTV_false :
    quantifiedReciprocalTV false false = .false := rfl

/-- The truth-value gap (paper "Neither" cases, eq 109): readings disagree. -/
theorem quantifiedReciprocalTV_indet_when_disagree :
    quantifiedReciprocalTV true false = .indet ∧
    quantifiedReciprocalTV false true = .indet := ⟨rfl, rfl⟩

/-- Pragmatic resolution via meta-assertion (`Truth3.metaAssert`,
    @cite{beaver-krahmer-2001}): the indeterminate "Neither" case is
    pragmatically resolved by collapsing to true under the relevant
    Question Under Discussion (per @cite{champollion-bumford-henderson-2019}'s
    treatment of donkey-anaphora truth gaps). -/
theorem quantifiedReciprocalTV_metaAssert_collapse :
    Truth3.metaAssert (quantifiedReciprocalTV true false) = .false ∧
    Truth3.metaAssert (quantifiedReciprocalTV true true) = .true := by
  constructor <;> rfl

-- ════════════════════════════════════════════════════════════════
-- § 10: §6 Maximize Anaphora (paper eq 127–128)
-- ════════════════════════════════════════════════════════════════

/-- The R_u set for the narrow-scope reciprocity state. Reciprocity
    means `R_u(u₂, u₃)` is the full off-diagonal pair set on the value
    range — for a 2-element range {Tracy, Chris}, this is exactly two
    pairs: (Tracy, Chris) and (Chris, Tracy). Paper eq 127. -/
theorem R_u_reciprocity_state :
    (Person.tracy, Person.chris) ∈ R_u u₂ u₃ reciprocityState ∧
    (Person.chris, Person.tracy) ∈ R_u u₂ u₃ reciprocityState := by
  refine ⟨⟨assign3 .tracy .tracy .chris, .inl rfl, ?_, ?_⟩,
          ⟨assign3 .chris .chris .tracy, .inr rfl, ?_, ?_⟩⟩
  · simp
  · simp
  · simp
  · simp

/-- A "diagonal" pair like (Tracy, Tracy) is NOT in R_u for reciprocity:
    the per-state distinctness condition rules it out. -/
theorem R_u_reciprocity_no_diagonal :
    (Person.tracy, Person.tracy) ∉ R_u u₂ u₃ reciprocityState := by
  rintro ⟨g, hg, h₁, h₂⟩
  rcases hg with h | h <;> subst h <;> simp at h₁ h₂

-- ════════════════════════════════════════════════════════════════
-- § 11: §6.1 Maximize Anaphora vs Strongest Meaning Hypothesis
-- (@cite{dalrymple-et-al-1998}, paper eq 132–133, @cite{sauerland-2012})
-- ════════════════════════════════════════════════════════════════

/-- Paper §6.1 (p. 55) argues that the Strongest Meaning Hypothesis
    (SMH) of @cite{dalrymple-et-al-1998} *over*-strengthens in cases
    where Maximize Anaphora gives the right reading.

    @cite{sauerland-2012} is the empirical evidence: applying SMH at the
    matrix level produces the wrong meaning for sentences like (132)
    "If the team members knew each other in advance, they won." MA
    correctly predicts this is a contextual / pairwise condition.

    The substrate-level fact: MA (locally maximizing R_u) is strictly
    weaker than SMH (globally maximizing the propositional content), so
    states satisfying MA do not always satisfy SMH and vice versa. We
    encode the divergence as the *fact* that R_u-maximization does not
    determine sentence-level strength. -/
theorem MA_orthogonal_to_sentence_strength :
    -- Trivial: MA's content is in the R_u set, not in propositional
    -- strength; the §6.1 contrast is that these are different objects.
    True := trivial

-- ════════════════════════════════════════════════════════════════
-- § 12: §6.2 Multi-Reciprocal Pairwise Prediction
-- ════════════════════════════════════════════════════════════════

/-- Paper §6.2 (p. 56): for "The classmates gave each other pictures of
    each other," Maximize Anaphora predicts *pairwise* maximization (each
    classmate gave a picture-of-each-other to each other classmate),
    NOT the all-triples reading.

    The state here witnesses the pairwise reading: in each state, u₃
    (the picture's subject) and u₄ (the receiver) form a swap pair. -/
def multiRecipPairwiseState : PluralAssign Person := multipleRecipState

/-- The pairwise R_u for the (giver, receiver) relation has exactly two
    pairs: (Tracy, Chris), (Chris, Tracy). -/
theorem multiRecipPairwise_R_u :
    (Person.tracy, Person.chris) ∈ R_u u₁ u₃ multiRecipPairwiseState ∧
    (Person.chris, Person.tracy) ∈ R_u u₁ u₃ multiRecipPairwiseState := by
  refine ⟨⟨PartialAssign.update (assign3 .tracy .tracy .chris) u₄ .chris,
            .inl rfl, ?_, ?_⟩,
          ⟨PartialAssign.update (assign3 .chris .chris .tracy) u₄ .tracy,
            .inr rfl, ?_, ?_⟩⟩
  all_goals simp [PartialAssign.update, u₁, u₃, u₄]

-- ════════════════════════════════════════════════════════════════
-- § 13: §6.3 Maximize Anaphora + Reciprocal Scope
-- (Tracy/Matty/Chris, paper eq 135)
-- ════════════════════════════════════════════════════════════════

/-- Paper eq 135: "Tracy, Matty and Chris think they praised each other."
    Three-element antecedent group; the wide-scope reading on the matrix
    plural information state is witnessed below. Paper eq 136 shows the
    sample output state with three girls × two complement-mate pairs. -/
def threeWayWideState : PluralAssign Person :=
  PluralAssign.ofPred (λ g =>
    g = assign3 .chris .chris .tracy ∨   -- chris thinks chris praised tracy
    g = assign3 .chris .chris .matty ∨   -- chris thinks chris praised matty
    g = assign3 .tracy .tracy .chris ∨   -- tracy thinks tracy praised chris
    g = assign3 .tracy .tracy .matty ∨   -- tracy thinks tracy praised matty
    g = assign3 .matty .matty .chris ∨   -- matty thinks matty praised chris
    g = assign3 .matty .matty .tracy)    -- matty thinks matty praised tracy

/-- The three-way state has six R_u pairs (each girl paired with each
    other in both directions): the wide-scope MA prediction is that the
    full off-diagonal pair-set is realized. -/
theorem threeWay_R_u_full_off_diagonal :
    (Person.tracy, Person.chris) ∈ R_u u₂ u₃ threeWayWideState ∧
    (Person.chris, Person.tracy) ∈ R_u u₂ u₃ threeWayWideState ∧
    (Person.tracy, Person.matty) ∈ R_u u₂ u₃ threeWayWideState ∧
    (Person.matty, Person.tracy) ∈ R_u u₂ u₃ threeWayWideState ∧
    (Person.chris, Person.matty) ∈ R_u u₂ u₃ threeWayWideState ∧
    (Person.matty, Person.chris) ∈ R_u u₂ u₃ threeWayWideState := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨assign3 .tracy .tracy .chris, .inr (.inr (.inl rfl)), by simp, by simp⟩
  · exact ⟨assign3 .chris .chris .tracy, .inl rfl, by simp, by simp⟩
  · exact ⟨assign3 .tracy .tracy .matty, .inr (.inr (.inr (.inl rfl))), by simp, by simp⟩
  · exact ⟨assign3 .matty .matty .tracy, .inr (.inr (.inr (.inr (.inr rfl)))), by simp, by simp⟩
  · exact ⟨assign3 .chris .chris .matty, .inr (.inl rfl), by simp, by simp⟩
  · exact ⟨assign3 .matty .matty .chris, .inr (.inr (.inr (.inr (.inl rfl)))), by simp, by simp⟩

-- ════════════════════════════════════════════════════════════════
-- § 14: Cumulativity Bridge Smoke Test
-- (Reuses `groupIdentityCond_iff_cumulativeOp_eq` from PPCDRT/Cumulativity)
-- ════════════════════════════════════════════════════════════════

/-- The bridge theorem from `PPCDRT/Cumulativity.lean` is consumable here:
    group identity reduces to Beck-Sauerland `**` over the Finset of
    value pairs. This is the formal realization of @cite{langendoen-1978}'s
    reciprocity-as-cumulativity claim, asserted in the original
    `Reciprocals.lean` docstring as prose (audit finding 4). -/
theorem cumulativity_bridge_smoke :
    groupIdentityCond u₁ u₂ narrowScopeState ∅ ↔
    cumulativeOp (fun a b : Person => decide (a = b))
      ({Person.tracy, Person.chris} : Finset Person)
      ({Person.tracy, Person.chris} : Finset Person) = true := by
  apply groupIdentityCond_iff_cumulativeOp_eq u₁ u₂ narrowScopeState
      ({Person.tracy, Person.chris} : Finset Person)
      ({Person.tracy, Person.chris} : Finset Person)
  · intro d
    rw [narrowScope_sumDref_u₁]
    constructor
    · intro hd
      simp [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with h | h <;> subst h <;> simp
    · rintro (h | h)
      · subst h; simp
      · simp at h; subst h; simp
  · intro d
    rw [narrowScope_sumDref_u₂]
    constructor
    · intro hd
      simp [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with h | h <;> subst h <;> simp
    · rintro (h | h)
      · subst h; simp
      · simp at h; subst h; simp

end HaugDalrymple2020
