import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Linglib.Features.Person.Basic

/-!
# The Person Case Constraint

The PCC restricts which ⟨IO-person, DO-person⟩ combinations a clitic cluster can
realize — the classic ban of French *me lui*. This file defines the descriptive
typology of PCC varieties (strong, ultra-strong, weak, super-strong, me-first, and the
predicted PG1–PG3). Prominence thresholds are cuts on the entailment chain
[author] ⟹ [participant] ⟹ [proximate], denoting the person predicates
`Person.IncludesSpeaker` and `Person.IsSAP`, so the person hierarchy enters as a
theorem (`inherentlyMetBy_antitone`) rather than a stipulation. Grammars are
preordered by inclusion of their licit regions (`licitFinset`).

Which mechanism enforces the constraint is left open here: a morphological filter,
φ-Agree, and perspectival semantics have all been proposed. The rival accounts are
formalized in their study files and compared cell-by-cell against this typology
(`Deal2024.strong_matches_pz`,
`PanchevaZubizarreta2018.isLicit_iff_exists_appl_satisfying`).

## References

* [bonet-1991]: the original formulation, as a morphological filter
* [nevins-2007]: the strong/weak/ultra-strong/me-first taxonomy and the feature calculus
* [pancheva-zubizarreta-2018]: the four-parameter grammar (their (11)–(12)) formalized here
* [bejar-rezac-2009], [coon-keine-2021], [deal-2024]: φ-Agree rivals, compared in `Studies/`
-/

namespace PCC

/-! ### Prominence thresholds: cuts on the [author] ⟹ [participant] ⟹ [proximate] chain -/

/-- The prominence a grammar requires of its IO: `proximate` (the default),
    `participant`, or `author`. -/
inductive ProminenceThreshold where
  | proximate | participant | author
  deriving DecidableEq, Repr, Fintype

/-- The restrictiveness chain `proximate < participant < author`. -/
instance : LinearOrder ProminenceThreshold :=
  LinearOrder.lift' (·.ctorIdx) (by decide)

/-- A person meets a prominence threshold by its own features: speech-act participants
    meet `proximate` and `participant`, the speaker meets `author`. A 3P meets
    `proximate` only contextually (`IOSatisfiesProminence`). -/
def ProminenceThreshold.InherentlyMetBy : ProminenceThreshold → Person → Prop
  | .proximate | .participant => Person.IsSAP
  | .author => Person.IncludesSpeaker

instance : (t : ProminenceThreshold) → DecidablePred t.InherentlyMetBy
  | .proximate | .participant => inferInstanceAs (DecidablePred Person.IsSAP)
  | .author => inferInstanceAs (DecidablePred Person.IncludesSpeaker)

/-- Prominence is an order-ideal on the person prominence chain: raising the
    threshold only shrinks the set of persons that inherently meet it. -/
theorem ProminenceThreshold.inherentlyMetBy_antitone (p : Person) :
    Antitone (InherentlyMetBy · p) := fun t₁ t₂ ht hm => by
  revert ht hm
  cases p <;> cases t₁ <;> cases t₂ <;> decide

/-! ### The PCC grammar -/

/-- A PCC grammar is a setting of the four P-Constraint parameters: the prominence
    threshold, P-Uniqueness, P-Primacy, and the domain restriction. P-Primacy
    presupposes P-Uniqueness (`primacy_le_uniqueness`); field defaults are the paper's
    defaults, so `{}` is the strong PCC. -/
structure Grammar where
  /-- P-Prominence: the threshold the IO must meet (always active). -/
  prominence : ProminenceThreshold := .proximate
  /-- P-Uniqueness: at most one DP may bear the required prominence. -/
  uniqueness : Bool := true
  /-- P-Primacy: a [+author] IO wins a tie. -/
  primacy : Bool := false
  /-- Restricted domain: the constraint applies only where a prominence-bearing DP
      is present. -/
  restrictedDomain : Bool := false
  /-- P-Primacy presupposes active P-Uniqueness. -/
  primacy_le_uniqueness : primacy ≤ uniqueness := by decide

/-! ### Named grammars ([pancheva-zubizarreta-2018] (31)–(34)) -/

/-- Strong PCC: all defaults; the DO must be 3P. -/
def strongGrammar : Grammar := {}
/-- Ultra-strong PCC: adds P-Primacy; ⟨1,2⟩ licit, ⟨2,1⟩ not. -/
def ultraStrongGrammar : Grammar := { primacy := true }
/-- Weak PCC: drops P-Uniqueness; SAPs may co-occur. -/
def weakGrammar : Grammar := { uniqueness := false }
/-- Super-strong PCC: `participant` prominence; the IO must be a SAP, ⟨3,3⟩ banned. -/
def superStrongGrammar : Grammar := { prominence := .participant }
/-- Me-first PCC: `author` prominence on a restricted domain. -/
def meFirstGrammar : Grammar := { prominence := .author, restrictedDomain := true }
/-- PG1 (predicted): `participant` prominence with P-Primacy. -/
def pg1Grammar : Grammar := { prominence := .participant, primacy := true }
/-- PG2 (predicted): `participant` prominence without P-Uniqueness. -/
def pg2Grammar : Grammar := { prominence := .participant, uniqueness := false }
/-- PG3 (predicted): `author` prominence on the unrestricted domain. -/
def pg3Grammar : Grammar := { prominence := .author }

/-! ### Subpredicates — the four clauses of (12) -/

/-- (12b) The IO meets P-Prominence: inherently, or — under a `proximate` threshold
    only — by contextual marking when paired with another non-proximate 3P. -/
def IOSatisfiesProminence (g : Grammar) (io do_ : Person) : Prop :=
  g.prominence.InherentlyMetBy io ∨
    (g.prominence = .proximate ∧
     ¬ g.prominence.InherentlyMetBy io ∧ ¬ g.prominence.InherentlyMetBy do_)

instance (g : Grammar) (io do_ : Person) : Decidable (IOSatisfiesProminence g io do_) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- (12c) The DO does not also inherently meet P-Prominence. -/
def UniquenessSatisfied (g : Grammar) (do_ : Person) : Prop :=
  ¬ g.prominence.InherentlyMetBy do_

instance (g : Grammar) (do_ : Person) : Decidable (UniquenessSatisfied g do_) :=
  inferInstanceAs (Decidable (¬ _))

/-- (12d) A [+author] IO rescues an otherwise-blocking configuration when P-Primacy is on.

    The rescue checks only the IO, so primacy-active grammars license ⟨1,1⟩, where the
    paper's descriptive statement (14d) — the DO must be 2P or 3P — would forbid it (the
    paper never walks the mechanism through ⟨1,1⟩ for the [+proximate] family). The
    permissive reading is deliberate: rival probe-based accounts part ways with the
    P-Constraint at exactly this cell (`Deal2024.sd_ultra_discrepancy_1_1`). -/
def PrimacyRescues (g : Grammar) (io : Person) : Prop :=
  g.primacy ∧ io.IncludesSpeaker

instance (g : Grammar) (io : Person) : Decidable (PrimacyRescues g io) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A person is inherently proximate iff it is a speech-act participant; a 3P is
    proximate only contextually. -/
def IsInherentlyProximate (p : Person) : Prop :=
  ProminenceThreshold.proximate.InherentlyMetBy p

instance : DecidablePred IsInherentlyProximate := fun p =>
  inferInstanceAs (Decidable (ProminenceThreshold.proximate.InherentlyMetBy p))

/-- (12a) Domain-exempt: restricted domain with no DP bearing the prominence feature. The
    restriction presupposes an argument matching the P-Prominence value
    ([pancheva-zubizarreta-2018] §4.5: the restricted application "matches the feature
    value set in P-Prominence"; for me-first, ApplPs with a [+author] argument). -/
def DomainExempt (g : Grammar) (io do_ : Person) : Prop :=
  g.restrictedDomain ∧
    ¬ g.prominence.InherentlyMetBy io ∧ ¬ g.prominence.InherentlyMetBy do_

instance (g : Grammar) (io do_ : Person) : Decidable (DomainExempt g io do_) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ### Licit person combinations -/

/-- ⟨IO, DO⟩ is licit under `g`: the domain restriction exempts the pair, or the IO
    meets P-Prominence and — when P-Uniqueness is active — the DO does not compete or
    P-Primacy rescues the tie. -/
def IsLicit (g : Grammar) (io do_ : Person) : Prop :=
  DomainExempt g io do_ ∨
    (IOSatisfiesProminence g io do_ ∧
      (g.uniqueness → UniquenessSatisfied g do_ ∨ PrimacyRescues g io))

instance (g : Grammar) (io do_ : Person) : Decidable (IsLicit g io do_) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The prediction domain: the 1/2/3 person tripartition. -/
def cliticPairs : Finset (Person × Person) :=
  ({.first, .second, .third} ×ˢ {.first, .second, .third})

/-- The person combinations `g` predicts licit. -/
def licitFinset (g : Grammar) : Finset (Person × Person) :=
  {p ∈ cliticPairs | IsLicit g p.1 p.2}

@[simp] theorem mem_licitFinset (g : Grammar) (p : Person × Person) :
    p ∈ licitFinset g ↔ p ∈ cliticPairs ∧ IsLicit g p.1 p.2 := by simp [licitFinset]

/-! ### The typology as a preorder (entailment by licit-set inclusion)

Only a preorder: distinct parameter settings can share a licit set (e.g. the
restricted-domain [+participant] grammar surfaces as the strong PCC,
`PanchevaZubizarreta2018.restricted_participant_surfaces_as_strong`), so antisymmetry
fails. -/

instance : Preorder Grammar := Preorder.lift licitFinset

instance (g₁ g₂ : Grammar) : Decidable (g₁ ≤ g₂) :=
  inferInstanceAs (Decidable (licitFinset g₁ ⊆ licitFinset g₂))

/-- Entailment unfolded: every licit cell of `g₁` is licit in `g₂`. -/
theorem le_iff_isLicit_imp (g₁ g₂ : Grammar) :
    g₁ ≤ g₂ ↔ ∀ io do_ : Person, (io, do_) ∈ cliticPairs → IsLicit g₁ io do_ → IsLicit g₂ io do_ := by
  show licitFinset g₁ ⊆ licitFinset g₂ ↔ _
  simp +contextual [Finset.subset_iff, Prod.forall, and_imp]

end PCC
