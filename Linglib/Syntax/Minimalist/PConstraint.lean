import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Defs.PartialOrder
import Linglib.Features.Prominence
import Linglib.Syntax.Minimalist.Phi.Geometry

/-!
# The P-Constraint
[pancheva-zubizarreta-2018]

A parametric theory of person-sensitivity in clitic clusters, due to
[pancheva-zubizarreta-2018]. The P-Constraint is triggered by an
*interpretable* person feature on Appl, which marks the indirect object as a
**point-of-view center** (a logophoric pivot/self/source in the sense of
[sells-1987]).

## Architecture

Empirical predictions for the eight named grammar instances, and the
correspondence P&Z draw between P-Prominence settings and Sells's
logophoric roles (§6.2), live in the study file
`Studies/PanchevaZubizarreta2018.lean`. This file holds
only the framework-neutral parametric API — no commitment to any particular
theory of logophoric roles:

- `PProminence` — what the IO must satisfy (proximate, participant, author)
- `PCCGrammar` — a `Fintype` parameter space (24 grammars total)
- The four parametric clauses as named `Prop` predicates with `Decidable`
  instances: `DomainExempt`, `IOSatisfiesProminence`, `UniquenessSatisfied`,
  `PrimacyRescues`
- `IsLicit` — the main predicate, defined as the disjunction implementing
  the algorithm of (12)
- `licitFinset`, `licitCount` — empirical-prediction enumeration via
  `Finset.filter`
- `ApplDomain` and `PConstraintSatisfied` — a minimal semantic model in
  which `IsLicit` is *derived* from selecting the IO as POV center
- `Preorder PCCGrammar` — entailment by licit-set containment

## Convention deviation

`IsLicit` is the canonical `Prop`-valued predicate. The earlier
`pccLicit : ... → Bool` API has been removed. Use `IsLicit g io do_` and
its `Decidable` instance directly; for proofs about specific cells, prefer
`by decide`.
-/

namespace Minimalist.PConstraint

open Minimalist (DecomposedPerson decomposePerson)

-- ============================================================================
-- § 1: P-Prominence
-- ============================================================================

/-- P-Prominence settings. The interpretable person feature on Appl requires
    a DP at the phase edge to bear one of these positive specifications.
    The settings are framework-neutral feature specifications;
    [pancheva-zubizarreta-2018] §6.2 give them a logophoric reading
    (proximate↔pivot, participant↔self, author↔source) that lives in the
    study file. -/
inductive PProminence : Type where
  | proximate    -- default: requires [+PROXIMATE]
  | participant  -- restricted: requires [+PARTICIPANT]
  | author       -- most restricted: requires [+AUTHOR]
  deriving DecidableEq, Repr, Fintype

-- ============================================================================
-- § 2: PCC Grammar — Parameter Space
-- ============================================================================

/-- A PCC grammar, parameterized by the four binary settings of the
    P-Constraint ([pancheva-zubizarreta-2018] (12)).

    The 24-element parameter space (3 prominence values × 2³ Bool flags) is
    enumerated by the `Fintype` instance below. -/
structure PCCGrammar where
  /-- P-Prominence: what feature value the IO must inherit at the phase edge.
      Default: `.proximate`. -/
  prominence : PProminence := .proximate
  /-- P-Uniqueness: at most one DP can agree with the interpretable person
      feature on Appl. Default: `true` (active). -/
  uniqueness : Bool := true
  /-- P-Primacy: when both DPs satisfy P-Prominence, the [+author] DP takes
      priority. Conditional on P-Uniqueness. Default: `false`. -/
  primacy : Bool := false
  /-- Domain: whether the interpretable person feature is present on ALL
      Appl heads (`false` = default), or only when a [+author] DP is present
      (`true` = restricted). -/
  restrictedDomain : Bool := false
  deriving DecidableEq, Repr

/-- `PCCGrammar` is in bijection with `PProminence × Bool × Bool × Bool`. -/
def PCCGrammar.equivQuadruple :
    PCCGrammar ≃ PProminence × Bool × Bool × Bool where
  toFun g := (g.prominence, g.uniqueness, g.primacy, g.restrictedDomain)
  invFun := fun ⟨p, u, pr, rd⟩ =>
    { prominence := p, uniqueness := u, primacy := pr, restrictedDomain := rd }
  left_inv _ := rfl
  right_inv := fun ⟨_, _, _, _⟩ => rfl

instance : Fintype PCCGrammar := Fintype.ofEquiv _ PCCGrammar.equivQuadruple.symm

-- ============================================================================
-- § 3: Named Grammar Instances
-- ============================================================================

/-- **Strong PCC** — all defaults. DO must be 3P. -/
def strongGrammar : PCCGrammar := {}

/-- **Ultra-strong PCC** — adds P-Primacy. Allows ⟨1,2⟩ but not ⟨2,1⟩. -/
def ultraStrongGrammar : PCCGrammar := { primacy := true }

/-- **Weak PCC** — drops P-Uniqueness. Allows SAP co-occurrence. -/
def weakGrammar : PCCGrammar := { uniqueness := false }

/-- **Super-strong PCC** — [+participant] prominence. IO must be SAP. -/
def superStrongGrammar : PCCGrammar := { prominence := .participant }

/-- **Me-first PCC** — [+author] prominence, restricted domain. -/
def meFirstGrammar : PCCGrammar :=
  { prominence := .author, restrictedDomain := true }

/-- **PG1** (predicted): [+participant] + P-Primacy. -/
def pg1Grammar : PCCGrammar :=
  { prominence := .participant, primacy := true }

/-- **PG2** (predicted): [+participant], no P-Uniqueness. -/
def pg2Grammar : PCCGrammar :=
  { prominence := .participant, uniqueness := false }

/-- **PG3** (predicted): [+author], unrestricted domain. -/
def pg3Grammar : PCCGrammar := { prominence := .author }

-- ============================================================================
-- § 4: Subpredicate Decomposition (the four clauses of (12))
-- ============================================================================

/-- A DP is *inherently* [+PROXIMATE] iff it is a SAP ([pancheva-zubizarreta-2018]
    (11)). Third person can only be [+PROXIMATE] contextually. -/
def IsInherentlyProximate (p : Person) : Prop :=
  (decomposePerson p).hasProximate = true

instance (p : Person) : Decidable (IsInherentlyProximate p) :=
  inferInstanceAs (Decidable (_ = true))

/-- A DP inherently satisfies a P-Prominence setting. -/
def SatisfiesProminence (s : PProminence) (p : Person) : Prop :=
  match s with
  | .proximate   => (decomposePerson p).hasProximate = true
  | .participant => (decomposePerson p).hasParticipant = true
  | .author      => (decomposePerson p).hasAuthor = true

instance (s : PProminence) (p : Person) :
    Decidable (SatisfiesProminence s p) := by
  cases s <;> exact inferInstanceAs (Decidable (_ = true))

/-- **Clause (12a) — Domain.** When the domain is restricted and no [+author]
    DP is present, the P-Constraint does not apply. -/
def DomainExempt (g : PCCGrammar) (io do_ : Person) : Prop :=
  g.restrictedDomain = true ∧
    (decomposePerson io).hasAuthor = false ∧
    (decomposePerson do_).hasAuthor = false

instance (g : PCCGrammar) (io do_ : Person) :
    Decidable (DomainExempt g io do_) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **Clause (12b) — P-Prominence.** The IO satisfies the prominence
    requirement, either inherently or — for `.proximate` only — by
    contextual marking when paired with another non-proximate 3P
    ([pancheva-zubizarreta-2018] §4.1.4). -/
def IOSatisfiesProminence (g : PCCGrammar) (io do_ : Person) : Prop :=
  SatisfiesProminence g.prominence io ∨
    (g.prominence = .proximate ∧
     ¬ SatisfiesProminence g.prominence io ∧
     ¬ SatisfiesProminence g.prominence do_)

instance (g : PCCGrammar) (io do_ : Person) :
    Decidable (IOSatisfiesProminence g io do_) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- **Clause (12c) — P-Uniqueness.** The DO does not also inherently satisfy
    the prominence requirement. (Contextual proximate-marking on the IO
    does not propagate to the DO.) -/
def UniquenessSatisfied (g : PCCGrammar) (do_ : Person) : Prop :=
  ¬ SatisfiesProminence g.prominence do_

instance (g : PCCGrammar) (do_ : Person) :
    Decidable (UniquenessSatisfied g do_) :=
  inferInstanceAs (Decidable (¬ _))

/-- **Clause (12d) — P-Primacy.** When P-Uniqueness would block, a [+author]
    IO rescues. -/
def PrimacyRescues (g : PCCGrammar) (io : Person) : Prop :=
  g.primacy = true ∧ (decomposePerson io).hasAuthor = true

instance (g : PCCGrammar) (io : Person) : Decidable (PrimacyRescues g io) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- ============================================================================
-- § 5: Licit Person Combinations
-- ============================================================================

/-- The PCC verdict on a ⟨IO, DO⟩ person combination under grammar `g`.

    Implements (12) compositionally:
    - Domain-exempt configurations are vacuously licit.
    - Otherwise, the IO must satisfy P-Prominence; and either
      P-Uniqueness is inactive, or it is satisfied, or P-Primacy rescues. -/
def IsLicit (g : PCCGrammar) (io do_ : Person) : Prop :=
  DomainExempt g io do_ ∨
    (IOSatisfiesProminence g io do_ ∧
      (g.uniqueness = false ∨
       UniquenessSatisfied g do_ ∨
       PrimacyRescues g io))

instance (g : PCCGrammar) (io do_ : Person) :
    Decidable (IsLicit g io do_) :=
  inferInstanceAs (Decidable (_ ∨ _))

-- ============================================================================
-- § 6: Enumeration via `Finset`
-- ============================================================================

/-- The prediction domain: PCC varieties are stated over 1/2/3 clitic
    combinations (the tripartition; clusivity-marked and impersonal
    clitics are outside the paper's typology). -/
def cliticPairs : Finset (Person × Person) :=
  ({.first, .second, .third} ×ˢ {.first, .second, .third})

/-- The set of person combinations the grammar predicts to be licit
    (within the paper's domain). -/
def licitFinset (g : PCCGrammar) : Finset (Person × Person) :=
  cliticPairs.filter fun p => IsLicit g p.1 p.2

/-- Cardinality of the licit set (out of 9 total combinations). -/
def licitCount (g : PCCGrammar) : ℕ := (licitFinset g).card

@[simp]
theorem mem_licitFinset (g : PCCGrammar) (p : Person × Person) :
    p ∈ licitFinset g ↔ p ∈ cliticPairs ∧ IsLicit g p.1 p.2 := by
  simp [licitFinset]

-- ============================================================================
-- § 7: Markedness
-- ============================================================================

/-- Number of parametric departures from the default (strong PCC).
    This is the markedness rank — strong = 0, ultra/weak/super/pg3 = 1,
    me-first/pg1/pg2 = 2 ([pancheva-zubizarreta-2018] §4.5 (31)). -/
def parameterDepartures (g : PCCGrammar) : ℕ :=
  (if g.prominence = .proximate then 0 else 1) +
  (if g.uniqueness then 0 else 1) +
  (if g.primacy then 1 else 0) +
  (if g.restrictedDomain then 1 else 0)

-- ============================================================================
-- § 8: Entailment Preorder
-- ============================================================================

instance : LE PCCGrammar where
  le g₁ g₂ := licitFinset g₁ ⊆ licitFinset g₂

instance : Preorder PCCGrammar where
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ h₁₂ h₂₃ := Finset.Subset.trans h₁₂ h₂₃

instance (g₁ g₂ : PCCGrammar) : Decidable (g₁ ≤ g₂) :=
  inferInstanceAs (Decidable (_ ⊆ _))

/-- Entailment in unfolded form: every licit cell of `g₁` is licit in `g₂`. -/
theorem le_iff_isLicit_imp (g₁ g₂ : PCCGrammar) :
    g₁ ≤ g₂ ↔ ∀ io do_ : Person, (io, do_) ∈ cliticPairs →
      IsLicit g₁ io do_ → IsLicit g₂ io do_ := by
  constructor
  · intro h io do_ hmem hlic
    have h1 : (io, do_) ∈ licitFinset g₁ :=
      (mem_licitFinset _ _).mpr ⟨hmem, hlic⟩
    exact ((mem_licitFinset _ _).mp (h h1)).2
  · intro h p hp
    rcases p with ⟨io, do_⟩
    rw [mem_licitFinset] at hp ⊢
    exact ⟨hp.1, h io do_ hp.1 hp.2⟩

-- ============================================================================
-- § 9: Semantic Grounding — the P-Constraint over Appl Domains
-- ============================================================================

/-- A minimal model of the Appl phase: the two arguments and the chosen
    point-of-view center. The interpretable person feature on Appl
    ([pancheva-zubizarreta-2018] (10)) marks one DP as the perspectival
    center; in the unmarked case this is the IO at the phase edge. -/
structure ApplDomain where
  /-- The indirect-object argument introduced by Appl. -/
  io : Person
  /-- The direct-object argument inside VP. -/
  do_ : Person
  /-- The DP selected as point-of-view center within the phase. -/
  povCenter : Person
  deriving DecidableEq, Repr

/-- The IO is the canonical POV-center candidate ([pancheva-zubizarreta-2018]
    page 1320). -/
def ApplDomain.povIsIO (a : ApplDomain) : Prop := a.povCenter = a.io

instance (a : ApplDomain) : Decidable a.povIsIO :=
  inferInstanceAs (Decidable (a.povCenter = a.io))

/-- The P-Constraint as a semantic predicate over an Appl domain.
    A domain satisfies the P-Constraint iff either it is exempt, or the
    POV center is the IO and the IO inherits the prominence value with
    uniqueness/primacy as required. -/
def PConstraintSatisfied (g : PCCGrammar) (a : ApplDomain) : Prop :=
  DomainExempt g a.io a.do_ ∨
    (a.povIsIO ∧
     IOSatisfiesProminence g a.io a.do_ ∧
     (g.uniqueness = false ∨
      UniquenessSatisfied g a.do_ ∨
      PrimacyRescues g a.io))

instance (g : PCCGrammar) (a : ApplDomain) :
    Decidable (PConstraintSatisfied g a) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- **Central derivation.** A ⟨IO, DO⟩ combination is licit iff there
    exists an Appl domain over those arguments — with the IO chosen as
    POV center — that satisfies the P-Constraint. The four parametric
    clauses are not stipulated verdicts; they are the conditions under
    which IO-as-POV-center is consistent with the interpretable person
    feature on Appl. -/
theorem isLicit_iff_exists_appl_satisfying
    (g : PCCGrammar) (io do_ : Person) :
    IsLicit g io do_ ↔
      ∃ a : ApplDomain, a.io = io ∧ a.do_ = do_ ∧ PConstraintSatisfied g a := by
  constructor
  · intro h
    refine ⟨⟨io, do_, io⟩, rfl, rfl, ?_⟩
    rcases h with hexempt | ⟨hprom, hrest⟩
    · exact Or.inl hexempt
    · exact Or.inr ⟨rfl, hprom, hrest⟩
  · rintro ⟨a, hio, hdo, hsat⟩
    rcases hsat with hexempt | ⟨_, hprom, hrest⟩
    · subst hio; subst hdo; exact Or.inl hexempt
    · subst hio; subst hdo; exact Or.inr ⟨hprom, hrest⟩

end Minimalist.PConstraint
