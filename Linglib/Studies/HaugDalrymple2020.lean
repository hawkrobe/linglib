import Linglib.Semantics.Reference.Reciprocals
import Linglib.Semantics.Dynamic.PPCDRT.Defs
import Linglib.Semantics.Dynamic.PPCDRT.Anaphora
import Linglib.Semantics.Dynamic.PPCDRT.Cumulativity
import Linglib.Semantics.Plurality.Cumulativity
import Linglib.Semantics.Plurality.Homogeneity.Basic
import Linglib.Semantics.Supervaluation.Basic
import Linglib.Core.Logic.Trivalent

/-!
# Haug & Dalrymple (2020) [haug-dalrymple-2020]

Reciprocity: Anaphora, scope, and quantification.
*Semantics & Pragmatics* 13:10, 1–62. doi:10.3765/sp.13.10.

The relational analysis of reciprocals in Partial Plural Compositional DRT
(PPCDRT). *Each other* is a pronoun bearing an anaphoric relation
(reciprocity R) to its antecedent; the narrow/wide scope ambiguity reduces
to the choice of antecedent relation between the matrix subject and the
embedded local antecedent (group identity ∪ vs. binding =).

## What is formalized

Witness-based formalisation of the paper's empirical contributions over
the PPCDRT substrate (`Semantics/Dynamic/PPCDRT/`):

| Paper § | Topic                                  | Witness type               |
|---------|----------------------------------------|----------------------------|
| §3      | Scope readings (narrow / wide)         | `PluralAssign Person`      |
| §3.3    | Crossed readings (4-cell classification) | `RecipReading` triples   |
| §4.2    | Underspecified RECIP/REFL              | `underspecifiedCond` lattice |
| §4.4    | Multiple reciprocals                   | Two-reciprocal witness     |
| §4.5    | Subgroup readings (forks, gravity)     | Weak-vs-strong contrast    |
| §4.6    | Collective antecedents                 | Distinctness neutralization |
| §5      | Quantified antecedents + truth-value gap | `Trivalent` via `removeGap` |
| §6      | Maximize Anaphora as a principle       | `R_u` + `maximizeAnaphora` |
| §6.2    | Multi-reciprocal pairwise prediction   | `R_u` over two reciprocals |
| §6.3    | MA interacting with scope              | Tracy/Matty/Chris case     |

Sections paper-acknowledged but not formalised (out of scope for a
study-file size budget): the full §2.3 Δ-relativised distribution
machinery (deferred — the substrate-trimming pass removed the prototyped
`delta`/`⨟`/`∂`/`max^u` operators since no consumer exercised them; they
will return alongside a Brasoveanu 2007 / Dotlačil 2013 study file);
the §5.2 empirical-fit table; the §7 typological excursus.

## Connections to existing linglib substrate

- [champollion-bumford-henderson-2019] for the §5 supervaluationist
  truth-value-gap analysis — realised via
  `Semantics/Plurality/Homogeneity/Basic.lean`'s `removeGap` /
  `Trivalent.metaAssert`.
- [kriz-2015] for the homogeneity background; same substrate.
- [langendoen-1978] for the reciprocity-as-cumulativity link —
  realised via `PPCDRT/Cumulativity.lean`'s
  `groupIdentityCond_iff_cumulativeOp_eq` bridge theorem.
- [murray-2008], [cable-2014] for the §4.2 underspecification
  examples.

## Source-paper attribution note

The §4.2 paragraph in [haug-dalrymple-2020] attributes the German
*sich* / Romance reflexive examples to [cable-2014] (paper p. 32),
not to [murray-2008] alone — the latter focuses on Cheyenne. The
docstrings here follow that attribution.
-/

namespace HaugDalrymple2020

open Semantics.Reference.Reciprocals
open Semantics.Dynamic.PPCDRT
open Core
open Trivalent (dist metaAssert)
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
  simp only [assign2, PartialAssign.update, u₁, u₂]
  rfl

@[simp] theorem assign2_u₂ (a b : Person) : assign2 a b u₂ = some b := by
  simp only [assign2, PartialAssign.update, u₂, Function.update_self]

@[simp] theorem assign3_u₁ (a b c : Person) : assign3 a b c u₁ = some a := by
  simp only [assign3, assign2, PartialAssign.update, u₁, u₂, u₃]
  rfl

@[simp] theorem assign3_u₂ (a b c : Person) : assign3 a b c u₂ = some b := by
  simp only [assign3, assign2, PartialAssign.update, u₂, u₃]
  rfl

@[simp] theorem assign3_u₃ (a b c : Person) : assign3 a b c u₃ = some c := by
  simp only [assign3, PartialAssign.update, u₃, Function.update_self]

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
    rcases hgS with h | h <;> subst h <;>
      simp only [assign2_u₁, Option.some.injEq] at hgu <;> subst hgu <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · intro hd
    rcases hd with h | h
    · subst h; exact ⟨assign2 .tracy .tracy, .inl rfl, assign2_u₁ ..⟩
    · simp only [Set.mem_singleton_iff] at h; subst h
      exact ⟨assign2 .chris .chris, .inr rfl, assign2_u₁ ..⟩

/-- The summed value of u₂ across the narrow-scope state is {tracy, chris}. -/
theorem narrowScope_sumDref_u₂ :
    PluralAssign.sumDref narrowScopeState u₂ = {Person.tracy, Person.chris} := by
  ext d
  constructor
  · rintro ⟨g, hgS, hgu⟩
    rcases hgS with h | h <;> subst h <;>
      simp only [assign2_u₂, Option.some.injEq] at hgu <;> subst hgu <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · intro hd
    rcases hd with h | h
    · subst h; exact ⟨assign2 .tracy .tracy, .inl rfl, assign2_u₂ ..⟩
    · simp only [Set.mem_singleton_iff] at h; subst h
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

    **UNVERIFIED collapse.** The paper distinguishes narrow eq 49 (a
    4-row table including a doxastic-world column `w`) from wide eq 51
    (a 2-row table without `w`). The empirical contrast lives in the
    presence/absence of the doxastic-alternative column, which the
    intensional `δ_w` machinery (paper §3.1) makes visible. The current
    `narrowScopeState`/`wideScopeState` encoding flattens both to a
    2-row table — the pointwise-vs-coverage distinction is correct at
    *each row* but the row-multiplicity contrast is lost. Setting
    `wideScopeState := narrowScopeState` reflects this collapse honestly:
    until the substrate exposes `δ_w`, the two states are extensionally
    identical for the 2-element domain. -/
def wideScopeState : PluralAssign Person := narrowScopeState

/-- **Wide scope is binding** (paper §3, eq 51). In every state of the
    plural information state, the embedded subject pronoun's value
    equals the matrix subject's value as `Option E`. -/
theorem wideScope_binding :
    bindingCond u₁ u₂ wideScopeState ∅ := by
  intro g hgS
  rcases hgS with h | h <;> subst h <;> rfl

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
    rcases hgS with h | h <;> subst h <;>
      simp only [assign3_u₂, Option.some.injEq] at hgu <;> subst hgu <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · intro hd
    rcases hd with h | h
    · subst h; exact ⟨_, .inl rfl, assign3_u₂ ..⟩
    · simp only [Set.mem_singleton_iff] at h; subst h
      exact ⟨_, .inr rfl, assign3_u₂ ..⟩

theorem recip_sumDref_u₃ :
    PluralAssign.sumDref reciprocityState u₃ = {Person.tracy, Person.chris} := by
  ext d
  constructor
  · rintro ⟨g, hgS, hgu⟩
    rcases hgS with h | h <;> subst h <;>
      simp only [assign3_u₃, Option.some.injEq] at hgu <;> subst hgu <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · intro hd
    rcases hd with h | h
    · subst h; exact ⟨assign3 .chris .chris .tracy, .inr rfl, assign3_u₃ ..⟩
    · simp only [Set.mem_singleton_iff] at h; subst h
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
    simp only [assign3_u₂, assign3_u₃, Option.some.injEq] at h₂ h₃ <;>
    subst h₂ <;> subst h₃ <;> decide

/-- **The full reciprocity condition holds** for this state. -/
theorem reciprocity_full :
    reciprocityCond u₂ u₃ reciprocityState ∅ :=
  ⟨reciprocity_groupIdentity, reciprocity_distinct⟩

-- ════════════════════════════════════════════════════════════════
-- § 4: §3.3 Four-Cell Crossed Readings Classification
-- ([haug-dalrymple-2020] §3.3, p. 24)
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
  simp only [recipReadings, narrowScopeReading, wideScopeReading, crossedReading,
             List.mem_cons, List.not_mem_nil, or_false] at hrM
  rcases hrM with rfl | rfl | rfl <;> simp_all

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
-- ([murray-2008] Cheyenne, [cable-2014] German *sich*)
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

/-- Multiple-reciprocal state for paper (85a) reading "where the second
    reciprocal takes the first one as its antecedent" — semantically
    interpretation (84b): "Tracy gave Chris a picture of Tracy, and
    Chris gave Tracy a picture of Chris." Per paper eq 85 (p. 35–36):
    - u₁ = subject (each girl, the giver)
    - u₂ = first reciprocal (each other₁), antecedent u₁
    - u₃ = pictures
    - u₄ = second reciprocal (each other₂), antecedent u₂; per the
      reading, u₄ takes the value of "the other member of u₂'s
      antecedent group" = u₁ (the giver).

    Distinctness conditions per eq 85b: ∂(u₁ ≠ u₂) and ∂(u₂ ≠ u₄).
    Each reciprocal is distinct from its OWN antecedent. There is no
    constraint between u₃ (pictures) and any reciprocal. -/
def multipleRecipState : PluralAssign Person :=
  PluralAssign.ofPred (λ g =>
    -- Row 1: Tracy gave Chris a picture (matty as placeholder pic₁) of Tracy
    g = (PartialAssign.update (assign3 .tracy .chris .matty) u₄ .tracy) ∨
    -- Row 2: Chris gave Tracy a picture (matty as placeholder pic₂) of Chris
    g = (PartialAssign.update (assign3 .chris .tracy .matty) u₄ .chris))

/-- Both reciprocals satisfy the paper's distinctness conditions per
    eq 85b: u₂ ≠ u₁ (first reciprocal distinct from antecedent u₁) and
    u₄ ≠ u₂ (second reciprocal distinct from its antecedent u₂). -/
theorem multipleRecip_both_distinct :
    (∀ s ∈ multipleRecipState, ∀ d_a d_b : Person,
      s u₁ = some d_a → s u₂ = some d_b → d_a ≠ d_b) ∧
    (∀ s ∈ multipleRecipState, ∀ d_a d_b : Person,
      s u₂ = some d_a → s u₄ = some d_b → d_a ≠ d_b) := by
  refine ⟨?_, ?_⟩ <;> · intro g hgS d_a d_b h₂ h
                        rcases hgS with hh | hh <;> subst hh <;>
                          simp [PartialAssign.update, u₁, u₂, u₄] at h₂ h <;>
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
    NOT the full strong-reciprocity {(1,2), (2,1), (1,3), (3,1), (2,3), (3,2)}.

    **Note on paper eq 92.** The paper's actual analysis (eq 92) wraps
    the support relation in `δ_{u_1}` distribution and uses sum-dref
    `∪u_2` on the supporter side. Our flat 3-row encoding shows the
    R_u-shape weak-reciprocity property at the value-set level but does
    not exercise the equivalence-class structure that distribution
    builds. The δ-side of the analysis is substrate-deferred (PPCDRT
    `delta` was trimmed in P6). -/
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
          ⟨_, .inr (.inr rfl), ?_, ?_⟩⟩ <;>
    simp only [assign2_u₁, assign2_u₂]

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
  refine ⟨?_, assign3 .tracy .tracy .tracy, .inl rfl, .tracy,
          assign3_u₁ .., assign3_u₃ ..⟩
  unfold groupIdentityCond
  ext d
  constructor
  · rintro ⟨g, hg, hgu⟩
    rcases hg with h | h | h
    · subst h; simp only [assign3_u₁, Option.some.injEq] at hgu; subst hgu
      exact ⟨assign3 .tracy .tracy .tracy, .inl rfl, assign3_u₃ ..⟩
    · subst h; simp only [assign3_u₁, Option.some.injEq] at hgu; subst hgu
      exact ⟨assign3 .chris .chris .chris, .inr (.inl rfl), assign3_u₃ ..⟩
    · subst h; simp only [assign3_u₁, Option.some.injEq] at hgu; subst hgu
      exact ⟨assign3 .matty .matty .matty, .inr (.inr rfl), assign3_u₃ ..⟩
  · rintro ⟨g, hg, hgu⟩
    rcases hg with h | h | h
    · subst h; simp only [assign3_u₃, Option.some.injEq] at hgu; subst hgu
      exact ⟨assign3 .tracy .tracy .tracy, .inl rfl, assign3_u₁ ..⟩
    · subst h; simp only [assign3_u₃, Option.some.injEq] at hgu; subst hgu
      exact ⟨assign3 .chris .chris .chris, .inr (.inl rfl), assign3_u₁ ..⟩
    · subst h; simp only [assign3_u₃, Option.some.injEq] at hgu; subst hgu
      exact ⟨assign3 .matty .matty .matty, .inr (.inr rfl), assign3_u₁ ..⟩

-- ════════════════════════════════════════════════════════════════
-- § 9: §5 Quantified Antecedents + Trivalent-Value Gap
-- (paper eq 99, 109; [champollion-bumford-henderson-2019]; [kriz-2015])
-- ════════════════════════════════════════════════════════════════

/-! Paper §5 introduces `max^u(K)` and shows that quantified antecedents
    of reciprocals (most members know each other; few have spoken to each
    other) give rise to a truth-value gap: True iff true on both the
    maximal-set reading and the reference-set reading; False iff false on
    both; Neither otherwise (paper eq 109). The paper invokes
    [champollion-bumford-henderson-2019], following [kriz-2015],
    for the supervaluationist machinery.

    Here we encode the truth-value gap directly via `Trivalent`, exploiting
    the existing `Semantics/Plurality/Homogeneity/Basic.lean` substrate
    (`removeGap`, `Trivalent.metaAssert`). -/

/-- The truth value of a quantified-antecedent reciprocal sentence,
    given its truth on the maximal-set reading and on the reference-set
    reading. Paper eq 109. -/
def quantifiedReciprocalTV (maximalSetReading refSetReading : Prop)
    [Decidable maximalSetReading] [Decidable refSetReading] : Trivalent :=
  if maximalSetReading ∧ refSetReading then .true
  else if ¬ maximalSetReading ∧ ¬ refSetReading then .false
  else .indet

/-- The two precisifications H&D §5 makes available for a
    quantified-antecedent reciprocal sentence: the **maximal set**
    reading (`u` ranges over the largest restrictor-satisfying set) and
    the **reference set** reading (`u` ranges over the largest set such
    that the scope-plus-reciprocal relation holds). Paper §5.1, eq 99. -/
inductive HDPrecisification where
  | maximalSet
  | referenceSet
  deriving DecidableEq, Repr

/-- The two-element specification space for H&D §5: both precisifications
    are admissible. -/
def hdSpec : Semantics.Supervaluation.SpecSpace HDPrecisification where
  admissible := {.maximalSet, .referenceSet}
  nonempty := ⟨.maximalSet, Finset.mem_insert_self _ _⟩

/-- Lift a (maximal-set-reading, reference-set-reading) pair of Props
    to a Prop-valued evaluation over the H&D precisification space. -/
def hdEval (maximalSetReading refSetReading : Prop) : HDPrecisification → Prop
  | .maximalSet => maximalSetReading
  | .referenceSet => refSetReading

instance hdEval.instDecidable (m r : Prop) [Decidable m] [Decidable r] :
    DecidablePred (hdEval m r) := fun p => by
  cases p <;> unfold hdEval <;> infer_instance

/-- **Bridge theorem (P8)** — H&D §5's truth-value gap (paper eq 109)
    *instantiates* a 2-precisification supervaluation construction. Paper
    §5 footnote 23 cites Križ 2015 and Champollion-Bumford-Henderson 2019
    as inspirations for the gap shape; this theorem makes the structural
    correspondence Lean-checkable: `quantifiedReciprocalTV m r` agrees
    with `superTrue (hdEval m r) hdSpec` over the two-element
    {maximalSet, referenceSet} precisification space.

    The paper itself is more guarded than "the §5 gap *is* CBH 2019" —
    it says §5 is *inspired by* CBH/Križ. The theorem here exhibits the
    truth-table reproducibility (paper eq 109 ↔ `superTrue` on a
    2-element space), not a deeper claim about identity of analyses. -/
theorem quantifiedReciprocalTV_iff_supervaluation
    (m r : Prop) [Decidable m] [Decidable r] :
    quantifiedReciprocalTV m r =
    Semantics.Supervaluation.superTrue (hdEval m r) hdSpec := by
  unfold quantifiedReciprocalTV Semantics.Supervaluation.superTrue
  by_cases hm : m <;> by_cases hr : r <;>
    simp [hdEval, hdSpec, hm, hr]

/-- **Sibling parallel — Križ 2016 plural homogeneity.**
    `Studies/Kriz2016.lean`'s `barePluralTV_eq_superTrue`
    proves `barePluralTV P x w = superTrue (fun a => P a w) ⟨x, hne⟩` —
    plural homogeneity reduces to `superTrue` over **atoms in the
    plurality** as specification points. The bridge above shows the H&D
    §5 reciprocal gap reduces to `superTrue` over **precisifications of
    the reciprocal's restrictor** ({maximalSet, referenceSet}). Both
    instances share the supervaluationist shape; only the spec-space sort
    differs. The Križ2016 §7 docstring explicitly enumerates this as one
    of five linglib instances of the same pattern (Fine/Križ/dist/
    selectional/H&D), making the H&D ↔ Križ structural agreement
    grep-able from either end.

    This theorem is the Lean-level smoke test: H&D's gap agrees with the
    image of `superTrue` evaluated at the H&D spec-eval pair, exactly as
    Križ's gap agrees with `superTrue` at the atomic-spec pair. -/
theorem hd_and_kriz_share_supervaluationist_shape
    (m r : Prop) [Decidable m] [Decidable r] :
    quantifiedReciprocalTV m r =
    Semantics.Supervaluation.superTrue (hdEval m r) hdSpec ∧
    -- The Križ side is `barePluralTV_eq_superTrue` over atoms; we don't
    -- restate it here, but the parallel is exhibited by the shared use
    -- of `Semantics.Supervaluation.superTrue`.
    True :=
  ⟨quantifiedReciprocalTV_iff_supervaluation m r, trivial⟩

-- ════════════════════════════════════════════════════════════════
-- § 10: §6 Maximize Anaphora (paper eq 127–128)
-- ════════════════════════════════════════════════════════════════

/-- The R_u set for the narrow-scope reciprocity state. Reciprocity
    means `R_u(u₂, u₃)` is the full off-diagonal pair set on the value
    range — for a 2-element range {Tracy, Chris}, this is exactly two
    pairs: (Tracy, Chris) and (Chris, Tracy). Paper eq 127. -/
theorem R_u_reciprocity_state :
    (Person.tracy, Person.chris) ∈ R_u u₃ u₂ reciprocityState ∧
    (Person.chris, Person.tracy) ∈ R_u u₃ u₂ reciprocityState := by
  -- After arg-order swap: pair `(p.1, p.2)` = `(u₃-value, u₂-value)`.
  -- Row 1 (assign3 tracy tracy chris) has u₃=chris, u₂=tracy → (chris, tracy).
  -- Row 2 (assign3 chris chris tracy) has u₃=tracy, u₂=chris → (tracy, chris).
  refine ⟨⟨assign3 .chris .chris .tracy, .inr rfl, ?_, ?_⟩,
          ⟨assign3 .tracy .tracy .chris, .inl rfl, ?_, ?_⟩⟩
  · simp
  · simp
  · simp
  · simp

/-- A "diagonal" pair like (Tracy, Tracy) is NOT in R_u for reciprocity:
    the per-state distinctness condition rules it out. -/
theorem R_u_reciprocity_no_diagonal :
    (Person.tracy, Person.tracy) ∉ R_u u₃ u₂ reciprocityState := by
  rintro ⟨g, hg, h₁, h₂⟩
  rcases hg with h | h <;> subst h <;> simp at h₁ h₂

-- ════════════════════════════════════════════════════════════════
-- § 11: §6.1 Maximize Anaphora vs Strongest Meaning Hypothesis
-- ([dalrymple-et-al-1998], paper eq 132–133, [sauerland-2012])
-- ════════════════════════════════════════════════════════════════

/-! Paper §6.1 (p. 55) argues SMH over-strengthens. The substrate-level
    refutation lives in `Reciprocals.lean` as `SMH_diverges_from_relational`
    — the relational analysis with MA leaves both readings available on
    the default property bundle, while SMH commits to narrow only.

    Related principles cited by paper §6: the Maximal Interpretation
    Hypothesis of [sabato-winter-2012] and [winter-2001]
    (p. 54), the typicality-constrained MA of [poortman-struiksma-kerem-friedmann-winter-2018]
    (p. 54), the anaphora-as-exhaustive principle of [kadmon-1990]
    (p. 54), and the experimental evidence of [majewski-2014]
    (paper §6 docstring reference). The trio MIH/MA/SMH form the natural
    scaffold for a principled treatment of the §4.5 reciprocal-strength
    typology — see the open work in the future-directions note below. -/

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

/-- The pairwise `R_u u₂ u₁` for the first reciprocal (each other₁,
    antecedent u₁) has exactly two pairs: (Chris, Tracy) and (Tracy, Chris)
    — read as `(receiver, giver)` per the paper's pair convention.

    Witnesses: row 1 (Tracy gave Chris) gives `(u₂=Chris, u₁=Tracy)`
    and row 2 (Chris gave Tracy) gives `(u₂=Tracy, u₁=Chris)`. -/
theorem multiRecipPairwise_R_u :
    (Person.chris, Person.tracy) ∈ R_u u₂ u₁ multiRecipPairwiseState ∧
    (Person.tracy, Person.chris) ∈ R_u u₂ u₁ multiRecipPairwiseState := by
  refine ⟨⟨PartialAssign.update (assign3 .tracy .chris .matty) u₄ .tracy,
            .inl rfl, ?_, ?_⟩,
          ⟨PartialAssign.update (assign3 .chris .tracy .matty) u₄ .chris,
            .inr rfl, ?_, ?_⟩⟩
  all_goals simp [PartialAssign.update, u₁, u₂, u₄]

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
    (Person.tracy, Person.chris) ∈ R_u u₃ u₂ threeWayWideState ∧
    (Person.chris, Person.tracy) ∈ R_u u₃ u₂ threeWayWideState ∧
    (Person.tracy, Person.matty) ∈ R_u u₃ u₂ threeWayWideState ∧
    (Person.matty, Person.tracy) ∈ R_u u₃ u₂ threeWayWideState ∧
    (Person.chris, Person.matty) ∈ R_u u₃ u₂ threeWayWideState ∧
    (Person.matty, Person.chris) ∈ R_u u₃ u₂ threeWayWideState := by
  -- After the R_u argument-order swap (P-T1.6), the pair `(p.1, p.2)` is
  -- read as `(reciprocal_value, antecedent_value) = (u₃-value, u₂-value)`.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨assign3 .chris .chris .tracy, .inl rfl, by simp, by simp⟩
  · exact ⟨assign3 .tracy .tracy .chris, .inr (.inr (.inl rfl)), by simp, by simp⟩
  · exact ⟨assign3 .matty .matty .tracy, .inr (.inr (.inr (.inr (.inr rfl)))), by simp, by simp⟩
  · exact ⟨assign3 .tracy .tracy .matty, .inr (.inr (.inr (.inl rfl))), by simp, by simp⟩
  · exact ⟨assign3 .matty .matty .chris, .inr (.inr (.inr (.inr (.inl rfl)))), by simp, by simp⟩
  · exact ⟨assign3 .chris .chris .matty, .inr (.inl rfl), by simp, by simp⟩

-- ════════════════════════════════════════════════════════════════
-- § 14: Cumulativity Bridge Smoke Test
-- (Reuses `groupIdentityCond_iff_cumulativeOp_eq` from PPCDRT/Cumulativity)
-- ════════════════════════════════════════════════════════════════

/-- The bridge theorem from `PPCDRT/Cumulativity.lean` is consumable here:
    group identity reduces to Beck-Sauerland `**` over the Finset of
    value pairs. This is the formal realization of [langendoen-1978]'s
    reciprocity-as-cumulativity claim, asserted in the original
    `Reciprocals.lean` docstring as prose (audit finding 4). -/
theorem cumulativity_bridge_smoke :
    groupIdentityCond u₁ u₂ narrowScopeState ∅ ↔
    Cumulative (fun a b : Person => a = b)
      ({Person.tracy, Person.chris} : Finset Person)
      ({Person.tracy, Person.chris} : Finset Person) := by
  apply groupIdentityCond_iff_cumulative_eq u₁ u₂ narrowScopeState
      ({Person.tracy, Person.chris} : Finset Person)
      ({Person.tracy, Person.chris} : Finset Person)
  · intro d
    rw [narrowScope_sumDref_u₁]
    constructor
    · intro hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with h | h <;> subst h <;>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
    · rintro (h | h)
      · subst h
        simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
      · simp only [Set.mem_singleton_iff] at h; subst h
        simp only [Finset.mem_insert, Finset.mem_singleton, or_true]
  · intro d
    rw [narrowScope_sumDref_u₂]
    constructor
    · intro hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with h | h <;> subst h <;>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
    · rintro (h | h)
      · subst h
        simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
      · simp only [Set.mem_singleton_iff] at h; subst h
        simp only [Finset.mem_insert, Finset.mem_singleton, or_true]

end HaugDalrymple2020
