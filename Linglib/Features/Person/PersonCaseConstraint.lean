import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Linglib.Features.Person.Decomposition

/-!
# The Person Case Constraint (theory-neutral)

[pancheva-zubizarreta-2018] [nevins-2007] [bonet-1991]

The PCC restricts which ⟨IO-person, DO-person⟩ combinations a single probe can license
in a clitic cluster. It is **person-feature combinatorics**, not a syntactic primitive:
the licit region of each grammar is determined order-theoretically by the
[author] ⟹ [participant] ⟹ [proximate] entailment chain (Nevins 2007's feature calculus,
adopted by [pancheva-zubizarreta-2018] (11)), and the variants (strong/weak/ultra-strong/
…) are points in a parameter lattice. So it lives on the person feature, not in the
syntax. The Minimalist application — the interpretable p-feature on Appl, the phase edge —
is the consumer (`PConstraintSatisfied`), kept separately.

Formerly `Syntax/Minimalist/PConstraint.lean`.

## Person prominence, derived from feature containment

`Person.Features` (`Features/Person/Decomposition.lean`) already carries the
[±participant, ±author] decomposition with its containment order (author ⊏ participant).
A person's prominence is read off it. **Inherently** `[+proximate] = [+participant]` (1P/2P
are proximate, 3P is not); the proximate/participant *grammars* differ only in the
contextual clause ([pancheva-zubizarreta-2018]: a 3P IO may count as proximate when paired
with another 3P), encoded in `IOSatisfiesProminence`.
-/

namespace PCC

open Person (Features)

/-! ### Theory-neutral person-feature accessors -/

/-- `[+author]` of a person, via the theory-neutral decomposition. -/
def hasAuthor (p : Person) : Bool := (Person.toFeatures p).elim false (·.hasAuthor)

/-- `[+participant]` of a person, via the theory-neutral decomposition. -/
def hasParticipant (p : Person) : Bool := (Person.toFeatures p).elim false (·.hasParticipant)

/-! ### P-Prominence: a cut on the [author] ⟹ [participant] ⟹ [proximate] chain -/

/-- The value the interpretable p-feature on the head requires of the IO
    ([pancheva-zubizarreta-2018] (12b)). `proximate` is the default (least restrictive);
    `participant` and `author` are the marked, more restrictive thresholds. -/
inductive PProminence where
  | proximate | participant | author
  deriving DecidableEq, Repr, Fintype

/-- A person *inherently* satisfies a prominence threshold. The sets nest by feature
    containment (`prominence_inherent_nested`): author ⊆ participant = proximate. -/
def PProminence.satisfiedInherentlyBy : PProminence → Person → Bool
  | .proximate   => hasParticipant   -- inherent proximate = participant ([pz-2018] (11))
  | .participant => hasParticipant
  | .author      => hasAuthor

/-- **Prominence is an order-ideal on the person prominence chain** ([nevins-2007]'s
    [author] ⟹ [participant] ⟹ [proximate]): the author-satisfiers are contained in the
    participant-satisfiers, which equal the (inherent) proximate-satisfiers. The person
    hierarchy is thus a theorem of feature containment, not a stipulated primitive. -/
theorem prominence_inherent_nested (p : Person) :
    (PProminence.author.satisfiedInherentlyBy p → PProminence.participant.satisfiedInherentlyBy p)
    ∧ (PProminence.participant.satisfiedInherentlyBy p
        ↔ PProminence.proximate.satisfiedInherentlyBy p) := by
  refine ⟨?_, Iff.rfl⟩
  cases p <;> decide

/-! ### The PCC grammar — a constrained parameter lattice

A grammar is the four parameters of [pancheva-zubizarreta-2018] (12), with the
**dependency P-Primacy ⟹ P-Uniqueness** (Primacy presupposes active Uniqueness) carried as
a well-formedness invariant, so the impossible corner does not exist. -/

/-- The raw four-parameter grammar ([pancheva-zubizarreta-2018] (12)). -/
structure RawGrammar where
  /-- P-Prominence: the threshold the IO must meet (always active; default `.proximate`). -/
  prominence : PProminence := .proximate
  /-- P-Uniqueness: at most one DP agrees with the p-feature (default active). -/
  uniqueness : Bool := true
  /-- P-Primacy: a [+author] DP wins a tie; presupposes P-Uniqueness (default off). -/
  primacy : Bool := false
  /-- Domain: p-feature on all Appl heads (default), or only with a relevant DP. -/
  restrictedDomain : Bool := false
  deriving DecidableEq, Repr, Fintype

/-- Well-formedness: P-Primacy presupposes active P-Uniqueness. -/
def RawGrammar.WellFormed (g : RawGrammar) : Prop := g.primacy = true → g.uniqueness = true

instance (g : RawGrammar) : Decidable g.WellFormed := inferInstanceAs (Decidable (_ → _))

/-- A **PCC grammar**: the four parameters subject to `primacy ⟹ uniqueness`. The
    impossible (Primacy-on, Uniqueness-off) corner is excluded by construction. -/
def PCCGrammar : Type := { g : RawGrammar // g.WellFormed }

instance : DecidableEq PCCGrammar := Subtype.instDecidableEq
instance : Fintype PCCGrammar := Subtype.fintype _

/-- Build a `PCCGrammar`, discharging well-formedness by `decide`. -/
def mkGrammar (prominence : PProminence := .proximate) (uniqueness : Bool := true)
    (primacy : Bool := false) (restrictedDomain : Bool := false)
    (h : RawGrammar.WellFormed ⟨prominence, uniqueness, primacy, restrictedDomain⟩ := by decide) :
    PCCGrammar :=
  ⟨⟨prominence, uniqueness, primacy, restrictedDomain⟩, h⟩

namespace PCCGrammar
/-- Accessor: the prominence threshold. -/
def prominence (g : PCCGrammar) : PProminence := g.val.prominence
/-- Accessor: P-Uniqueness. -/
def uniqueness (g : PCCGrammar) : Bool := g.val.uniqueness
/-- Accessor: P-Primacy. -/
def primacy (g : PCCGrammar) : Bool := g.val.primacy
/-- Accessor: restricted domain. -/
def restrictedDomain (g : PCCGrammar) : Bool := g.val.restrictedDomain
end PCCGrammar

/-! ### Named grammars ([pancheva-zubizarreta-2018] (31)–(34)) -/

/-- **Strong PCC** — all defaults. DO must be 3P. -/
def strongGrammar : PCCGrammar := mkGrammar
/-- **Ultra-strong PCC** — adds P-Primacy (allows ⟨1,2⟩, not ⟨2,1⟩). -/
def ultraStrongGrammar : PCCGrammar := mkGrammar (primacy := true)
/-- **Weak PCC** — drops P-Uniqueness (allows SAP co-occurrence). -/
def weakGrammar : PCCGrammar := mkGrammar (uniqueness := false)
/-- **Super-strong PCC** — [+participant] prominence (IO must be SAP, bans ⟨3,3⟩). -/
def superStrongGrammar : PCCGrammar := mkGrammar (prominence := .participant)
/-- **Me-first PCC** — [+author] prominence, restricted domain. -/
def meFirstGrammar : PCCGrammar := mkGrammar (prominence := .author) (restrictedDomain := true)
/-- **PG1** (predicted): [+participant] + P-Primacy. -/
def pg1Grammar : PCCGrammar := mkGrammar (prominence := .participant) (primacy := true)
/-- **PG2** (predicted): [+participant], no P-Uniqueness. -/
def pg2Grammar : PCCGrammar := mkGrammar (prominence := .participant) (uniqueness := false)
/-- **PG3** (predicted): [+author], unrestricted domain. -/
def pg3Grammar : PCCGrammar := mkGrammar (prominence := .author)

/-! ### Subpredicates — the four clauses of (12) -/

/-- (12b) The IO satisfies P-Prominence, inherently or — for `.proximate` only — by
    contextual marking when paired with another non-proximate 3P. -/
def IOSatisfiesProminence (g : PCCGrammar) (io do_ : Person) : Prop :=
  g.prominence.satisfiedInherentlyBy io ∨
    (g.prominence = .proximate ∧
     ¬ g.prominence.satisfiedInherentlyBy io ∧
     ¬ g.prominence.satisfiedInherentlyBy do_)

instance (g : PCCGrammar) (io do_ : Person) : Decidable (IOSatisfiesProminence g io do_) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- (12c) The DO does not also inherently satisfy P-Prominence. -/
def UniquenessSatisfied (g : PCCGrammar) (do_ : Person) : Prop :=
  ¬ g.prominence.satisfiedInherentlyBy do_

instance (g : PCCGrammar) (do_ : Person) : Decidable (UniquenessSatisfied g do_) :=
  inferInstanceAs (Decidable (¬ _))

/-- (12d) A [+author] IO rescues an otherwise-blocking configuration when P-Primacy is on. -/
def PrimacyRescues (g : PCCGrammar) (io : Person) : Prop :=
  g.primacy = true ∧ hasAuthor io = true

instance (g : PCCGrammar) (io : Person) : Decidable (PrimacyRescues g io) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A person is *inherently* `[+proximate]` iff it is a speech-act participant
    ([pancheva-zubizarreta-2018] (11)); a 3P is proximate only contextually. -/
def IsInherentlyProximate (p : Person) : Prop := hasParticipant p = true

instance (p : Person) : Decidable (IsInherentlyProximate p) :=
  inferInstanceAs (Decidable (_ = true))

/-- (12a) Domain-exempt: restricted domain with no [+author] DP present. -/
def DomainExempt (g : PCCGrammar) (io do_ : Person) : Prop :=
  g.restrictedDomain = true ∧ hasAuthor io = false ∧ hasAuthor do_ = false

instance (g : PCCGrammar) (io do_ : Person) : Decidable (DomainExempt g io do_) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ### Licit person combinations -/

/-- The PCC verdict on ⟨IO, DO⟩ under `g`, composing the four clauses of (12). -/
def IsLicit (g : PCCGrammar) (io do_ : Person) : Prop :=
  DomainExempt g io do_ ∨
    (IOSatisfiesProminence g io do_ ∧
      (g.uniqueness = false ∨ UniquenessSatisfied g do_ ∨ PrimacyRescues g io))

instance (g : PCCGrammar) (io do_ : Person) : Decidable (IsLicit g io do_) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The prediction domain: the 1/2/3 person tripartition. -/
def cliticPairs : Finset (Person × Person) :=
  ({.first, .second, .third} ×ˢ {.first, .second, .third})

/-- The person combinations `g` predicts licit. -/
def licitFinset (g : PCCGrammar) : Finset (Person × Person) :=
  cliticPairs.filter fun p => IsLicit g p.1 p.2

/-- Cardinality of the licit set (out of 9). -/
def licitCount (g : PCCGrammar) : ℕ := (licitFinset g).card

/-- Markedness rank: parametric departures from the default (strong PCC)
    ([pancheva-zubizarreta-2018] §4.5 (31)) — strong = 0. -/
def parameterDepartures (g : PCCGrammar) : ℕ :=
  (if g.prominence = .proximate then 0 else 1) +
  (if g.uniqueness then 0 else 1) +
  (if g.primacy then 1 else 0) +
  (if g.restrictedDomain then 1 else 0)

@[simp] theorem mem_licitFinset (g : PCCGrammar) (p : Person × Person) :
    p ∈ licitFinset g ↔ p ∈ cliticPairs ∧ IsLicit g p.1 p.2 := by simp [licitFinset]

/-! ### The typology as a partial order (entailment by licit-set inclusion) -/

instance : LE PCCGrammar where le g₁ g₂ := licitFinset g₁ ⊆ licitFinset g₂

instance : Preorder PCCGrammar where
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ h₁₂ h₂₃ := Finset.Subset.trans h₁₂ h₂₃

instance (g₁ g₂ : PCCGrammar) : Decidable (g₁ ≤ g₂) := inferInstanceAs (Decidable (_ ⊆ _))

/-- Entailment unfolded: every licit cell of `g₁` is licit in `g₂`. -/
theorem le_iff_isLicit_imp (g₁ g₂ : PCCGrammar) :
    g₁ ≤ g₂ ↔ ∀ io do_ : Person, (io, do_) ∈ cliticPairs → IsLicit g₁ io do_ → IsLicit g₂ io do_ := by
  constructor
  · intro h io do_ hmem hlic
    exact ((mem_licitFinset _ _).mp (h ((mem_licitFinset _ _).mpr ⟨hmem, hlic⟩))).2
  · intro h p hp
    rcases p with ⟨io, do_⟩
    rw [mem_licitFinset] at hp ⊢
    exact ⟨hp.1, h io do_ hp.1 hp.2⟩

/-- **Within the proximate family the licit sets form a chain**
    ([pancheva-zubizarreta-2018]): strong ⊆ ultra-strong ⊆ weak — monotone removal of
    P-Primacy then P-Uniqueness only enlarges the licit region. (Cross-family the
    typology is a lattice, not a chain: me-first/super-strong are incomparable.) -/
theorem proximate_family_chain :
    strongGrammar ≤ ultraStrongGrammar ∧ ultraStrongGrammar ≤ weakGrammar := by
  constructor <;> decide

end PCC
