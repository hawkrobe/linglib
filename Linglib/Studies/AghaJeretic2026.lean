import Linglib.Semantics.Modality.Directive
import Linglib.Semantics.Homogeneity.Decided
import Linglib.Semantics.Exhaustification.Finite
import Linglib.Studies.Rubinstein2014
import Linglib.Data.Examples.AghaJeretic2026

/-!
# Modal force and its realization across languages

Necessity and possibility modals are universal and existential quantifiers over the best worlds,
but two classes of modals fall outside the binary. Weak necessity modals such as *should* are
weaker than *must*: a strong necessity modal conjoined with the negation of another over the
same domain is contradictory, and the conjunction of two is trivial, while *should φ but you
don't have to* is consistent and *should φ, and in fact you must* is informative
(`sameDomain_contradiction`, `restricted_consistent`). The chapter surveys three analyses:
domain restriction by a secondary ordering source, comparative meaning with a negotiable
ordering source, and non-quantificational plural predication over worlds. Under domain
restriction the modal neg-raises only over a subsingleton domain (`vfiWeak_negRaises_iff`),
whereas the scope facts of the chapter's rows show *should* never below negation, *must* below
it only when the negation is in a higher clause, and *have to* always below it
(`weak_never_narrow`, `must_narrow_iff_higher`, `haveTo_always_narrow`); on *must* under higher
negation the chapter's judgment contradicts the one Rubinstein reports (`must_higherNeg_conflict`).

Polarity-sensitive variable force modals are possibility modals whose necessity readings arise
from what they project: Nez Perce *o'qa* projects no alternatives, so necessity is a special case
of possibility in upward-entailing contexts only; Siona *ba'iji* projects subdomain alternatives
with no scalemate, so obligatory exhaustification yields necessity unembedded; Swedish *får* has
a prunable scalemate, so both readings are available; Kinande *anga*'s domain carries a secondary
ordering source and its scalemate *paswa* blocks strong necessity, so exhaustification yields
weak necessity. `Projection` records these four settings and `available` states the readings
each licenses in each environment, matching the chapter's table row by row
(`projection_matches_table`); every profile leaves only possibility under clausemate negation,
where no clause boundary hosts the exhaustifier (`clausemateNegation_possibility`). The
exhaustification step itself is Bar-Lev and Fox's operator: over the subdomain alternatives of a
possibility modal on a two-world domain, `exhIEII` entails the prejacent at both worlds
(`exh_subdomain_necessity`). The determiner–modal generalization for infinitival relatives is
stated over its rows (`strong_determiner_should`); the discourse-sensitive modals, the overt
exhaustifiers, collapse variable force, and the covert modals of the final section are surveyed
without a formal counterpart here.

## References

* [agha-jeretic-2026]
* [agha-jeretic-2022]
* [von-fintel-iatridou-2008]
* [rubinstein-2014]
* [deal-2011]
* [bar-lev-fox-2020]
* [vander-klok-hohaus-2020]
-/

namespace AghaJeretic2026

open Modality.Kratzer Modality.Directive Data.Examples
open Semantics.Homogeneity (negRaising_iff_subsingleton)
open Exhaustification

/-! ### Weak and strong necessity -/

variable {W : Type*}

/-- Two universal modals over one domain cannot be affirmed and denied together. -/
theorem sameDomain_contradiction (D : Set W) (p : W → Prop) :
    ¬ ((∀ w ∈ D, p w) ∧ ¬ ∀ w ∈ D, p w) := fun h => h.2 h.1

/-- A universal modal over a proper subdomain can be affirmed while the one over the full
domain is denied. -/
theorem restricted_consistent {D' D : Finset W} (h : D' ⊂ D) :
    ∃ p : W → Prop, (∀ w ∈ D', p w) ∧ ¬ ∀ w ∈ D, p w :=
  let ⟨w, hw, hw'⟩ := Finset.exists_of_ssubset h
  ⟨(· ∈ D'), fun _ hw => hw, fun hall => hw' (hall w hw)⟩

/-- Domain-restriction weak necessity neg-raises at a world exactly when its nested best-world
domain is a subsingleton. -/
theorem vfiWeak_negRaises_iff (f : ModalBase W) (g g' : OrderingSource W) (w : W) :
    (∀ p : W → Prop, ¬ weakNecessity f g g' p w → weakNecessity f g g' (fun w' => ¬ p w') w) ↔
      (bestAmong (bestWorlds f g w) (g' w)).Subsingleton := by
  simp only [weakNecessity]
  exact negRaising_iff_subsingleton _

/-! ### Scope under negation -/

/-- A weak necessity modal never takes scope below negation. -/
theorem weak_never_narrow :
    ∀ e ∈ Examples.all, e.feature? "force" = some "weak" → (e.feature? "negation").isSome →
      e.readings.lookup "wide" = some .acceptable ∧
        e.readings.lookup "narrow" = some .unacceptable := by
  decide

/-- *Must* takes scope below negation exactly when the negation is in a higher clause. -/
theorem must_narrow_iff_higher :
    ∀ e ∈ Examples.all, e.feature? "modal" = some "must" →
      (e.readings.lookup "narrow" = some .acceptable ↔ e.feature? "negation" = some "higher") := by
  decide

/-- *Have to* takes scope below negation wherever the negation is. -/
theorem haveTo_always_narrow :
    ∀ e ∈ Examples.all, e.feature? "modal" = some "have to" →
      e.readings.lookup "narrow" = some .acceptable ∧
        e.readings.lookup "wide" = some .unacceptable := by
  decide

/-- The chapter reads *must* below a higher-clause negation, where Rubinstein's row records the
lower-negation reading as unacceptable. -/
theorem must_higherNeg_conflict :
    Examples.ex_19b.readings.lookup "narrow" = some .acceptable ∧
      Rubinstein2014.Examples.nr_must.readings.lookup "lowerNeg" = some .unacceptable := by
  decide

/-! ### Polarity-sensitive variable force -/

/-- The environments the typology distinguishes. -/
inductive Environment
  | unembedded
  | clausemateNegation
  | otherDE
  deriving DecidableEq, Repr

/-- The readings a variable force modal may have. -/
inductive Reading
  | possibility
  | necessity
  | weakNecessity
  deriving DecidableEq, Repr, Fintype

/-- What a possibility modal projects: subdomain alternatives, a strong-necessity scalemate,
whether that scalemate can be pruned, and whether its domain is restricted by a secondary
ordering source. -/
structure Projection where
  subdomain : Bool
  scalemate : Bool
  prunable : Bool
  secondaryOrdering : Bool
  deriving DecidableEq, Repr

/-- The readings a projection licenses in an environment: unembedded, obligatory
exhaustification of subdomain alternatives removes the possibility reading unless a scalemate
supplies it, and strengthens to strong or weak necessity according to the domain; under
clausemate negation there is no clause boundary for the exhaustifier and the necessity reading
is no special case of possibility; in other downward-entailing contexts exhaustification is
optional. -/
def available (π : Projection) : Environment → Reading → Prop
  | .unembedded, .possibility => ¬ π.subdomain ∨ π.scalemate
  | .unembedded, .necessity =>
      (¬ π.subdomain ∧ ¬ π.scalemate) ∨
        (π.subdomain ∧ (¬ π.scalemate ∨ π.prunable) ∧ ¬ π.secondaryOrdering)
  | .unembedded, .weakNecessity => π.subdomain ∧ π.secondaryOrdering
  | .clausemateNegation, r => r = .possibility
  | .otherDE, .possibility => True
  | .otherDE, .necessity => π.subdomain ∧ ¬ π.secondaryOrdering
  | .otherDE, .weakNecessity => π.subdomain ∧ π.secondaryOrdering

instance (π : Projection) (env : Environment) (r : Reading) : Decidable (available π env r) := by
  unfold available; cases env <;> cases r <;> infer_instance

/-- Nez Perce *o'qa* projects nothing. -/
def oqa : Projection := ⟨false, false, false, false⟩

/-- Siona *ba'iji* projects subdomain alternatives and has no scalemate. -/
def baiji : Projection := ⟨true, false, false, false⟩

/-- Swedish *får* projects subdomain alternatives and a prunable scalemate, *behöva*. -/
def far : Projection := ⟨true, true, true, false⟩

/-- Kinande *anga* projects subdomain alternatives, has the scalemate *paswa*, and quantifies
over a doubly restricted domain. -/
def anga : Projection := ⟨true, true, false, true⟩

/-- Under clausemate negation every projection leaves only the possibility reading. -/
theorem clausemateNegation_possibility (π : Projection) (r : Reading) :
    available π .clausemateNegation r ↔ r = .possibility := Iff.rfl

/-- The projection a table row concerns. -/
def projection? (e : LinguisticExample) : Option Projection :=
  match e.feature? "modal" with
  | some "o'qa" => some oqa
  | some "ba'iji" => some baiji
  | some "får" => some far
  | some "anga" => some anga
  | _ => none

/-- The environment a table row concerns. -/
def environment? (e : LinguisticExample) : Option Environment :=
  match e.feature? "environment" with
  | some "unembedded" => some .unembedded
  | some "clausemate negation" => some .clausemateNegation
  | some "other DE" => some .otherDE
  | _ => none

/-- The reading a row names. -/
def readingName : Reading → String
  | .possibility => "possibility"
  | .necessity => "necessity"
  | .weakNecessity => "weak necessity"

/-- The projections license exactly the readings the chapter's table records. -/
theorem projection_matches_table :
    ∀ e ∈ Examples.all, e.feature? "modal" ≠ none → ∀ π ∈ projection? e, ∀ env ∈ environment? e,
      ∀ r, (e.readings.lookup (readingName r)).getD .unacceptable = .acceptable ↔
        available π env r := by
  decide

/-! ### Exhaustification of subdomain alternatives -/

/-- A state of a two-world modal domain: whether the prejacent holds at each world. -/
abbrev Domain := Bool × Bool

/-- The prejacent holds at the first world. -/
def atFirst : Finset Domain := Finset.univ.filter (·.1 = true)

/-- The prejacent holds at the second world. -/
def atSecond : Finset Domain := Finset.univ.filter (·.2 = true)

/-- The possibility modal: the prejacent holds somewhere in the domain. -/
def somewhere : Finset Domain := Finset.univ.filter fun s => s.1 = true ∨ s.2 = true

/-- The subdomain alternatives of the possibility modal, with no scalemate. -/
def subdomainAlts : Finset (Finset Domain) := {atFirst, atSecond, somewhere}

/-- Exhaustifying the possibility modal over its subdomain alternatives yields necessity: the
prejacent holds at both worlds. -/
theorem exh_subdomain_necessity (s : Domain)
    (h : exhIEII (asSetOfSets subdomainAlts) ↑somewhere s) :
    s ∈ atFirst ∧ s ∈ atSecond := by
  have hcell : cell (asSetOfSets subdomainAlts) ↑somewhere (true, true) :=
    (mem_cellFinset_iff subdomainAlts somewhere _).1 (by decide)
  exact ⟨exhIEII_implies_cell_witnessed_alt _ _ (mem_asSetOfSets.2 ⟨atFirst, by decide, rfl⟩)
      (true, true) hcell (Finset.mem_coe.2 (by decide : (true, true) ∈ atFirst)) s h,
    exhIEII_implies_cell_witnessed_alt _ _ (mem_asSetOfSets.2 ⟨atSecond, by decide, rfl⟩)
      (true, true) hcell (Finset.mem_coe.2 (by decide : (true, true) ∈ atSecond)) s h⟩

/-! ### Covert modality -/

/-- In infinitival relatives a strong determiner forces the *should* reading and excludes the
*could* reading, where a weak determiner allows both. -/
theorem strong_determiner_should :
    ∀ e ∈ Examples.all, e.feature? "construction" = some "infinitival relative" →
      e.readings.lookup "should" = some .acceptable ∧
        (e.readings.lookup "could" = some .acceptable ↔ e.feature? "determiner" = some "weak") := by
  decide

end AghaJeretic2026
