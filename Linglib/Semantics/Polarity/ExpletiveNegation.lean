import Linglib.Semantics.Polarity.Item
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Basic

/-!
# Expletive Negation Typology

Pre-Fragment typological substrate for expletive negation (EN):
framework-agnostic classification types that Fragments and Studies
import to type their per-language EN data. The trigger-class /
licensing apparatus traces to [espinal-1992]'s logical-absorption
account, on which the [greco-2020] / [rett-2026] refinements build.

Two orthogonal classifications:

- `ENType` (high/low) — [rett-2026]'s position-based classification
- `ENStrength` (weak/strong) — [greco-2020]'s polarity-based classification
- `PolarityClass` / `PolarityLicensing` — polarity-sensitive element classes
  and their licensing profiles

These types classify EN constructions by their empirical properties
without committing to a syntactic analysis. The syntactic derivation
(from merge position in the extended projection) lives in
`Studies/Greco2020.lean` under `namespace Minimalist.NegScope`.
-/

namespace Semantics.Negation


/-! ### EN blocking reasons -/

/-- Cross-linguistic reasons why a trigger class may not license
    expletive negation in a particular language ([jin-koenig-2021] §7). -/
inductive ENBlockingReason where
  /-- Language disprefers modal operators in complement clauses -/
  | modalRestriction
  /-- Comparative complements only allow NPs, not clauses -/
  | npOnlyComplement
  /-- Concept expressed analytically with necessary (non-expletive) negation -/
  | analyticNegation
  deriving DecidableEq, Repr

/-! ### EN type classification -/

/-- Two syntactic types of expletive negation ([rett-2026]).

    **High EN** appears above TP, targets non-truth-conditional content
    (exclamatives, surprise negation). It is obligatory where licensed.

    **Low EN** appears below TP (VP-level), targets truth-conditional
    content in ambidirectional environments. It is optional and triggers
    a manner implicature (evaluativity). -/
inductive ENType where
  | high   -- Non-truth-conditional; obligatory (exclamatives, surprise)
  | low    -- Truth-conditional; optional (before, than, fear)
  deriving DecidableEq, Repr

-- ── ENType: Equiv, Fintype, LinearOrder ──

/-- ENType ≃ Bool: low ↦ false, high ↦ true. -/
def ENType.equivBool : ENType ≃ Bool where
  toFun | .low => false | .high => true
  invFun | false => .low | true => .high
  left_inv t := by cases t <;> rfl
  right_inv b := by cases b <;> rfl

instance : Fintype ENType := Fintype.ofEquiv _ ENType.equivBool.symm

/-- Numeric embedding: low ↦ 0, high ↦ 1.
    Ordering: low < high (truth-conditional before non-truth-conditional). -/
def ENType.toNat : ENType → Nat
  | .low => 0 | .high => 1

instance : LinearOrder ENType :=
  LinearOrder.lift' ENType.toNat
    (fun a b h => by cases a <;> cases b <;> simp_all [ENType.toNat])

/-! ### EN strength classification -/

/-- [greco-2020] §2.1: EN constructions divide into two classes
    based on co-occurrence with polarity-sensitive elements.

    **Weak EN** retains some polarity properties of standard negation:
    licenses weak NPIs and N-words (e.g. *finché*-clauses, *unless*-clauses).

    **Strong EN** loses all polarity properties: rejects weak NPIs,
    strong NPIs, not-also conjunctions, and N-words (e.g. negative
    exclamatives, rhetorical questions, surprise negation). -/
inductive ENStrength where
  | weak    -- Retains some SN properties (weak NPIs, N-words)
  | strong  -- Loses all SN polarity properties
  deriving DecidableEq, Repr

-- ── ENStrength: Equiv, Fintype, LinearOrder ──

/-- ENStrength ≃ Bool: weak ↦ false, strong ↦ true. -/
def ENStrength.equivBool : ENStrength ≃ Bool where
  toFun | .weak => false | .strong => true
  invFun | false => .weak | true => .strong
  left_inv s := by cases s <;> rfl
  right_inv b := by cases b <;> rfl

instance : Fintype ENStrength := Fintype.ofEquiv _ ENStrength.equivBool.symm

/-- Numeric embedding: weak ↦ 0, strong ↦ 1.
    Ordering: weak < strong (retains-polarity before loses-polarity). -/
def ENStrength.toNat : ENStrength → Nat
  | .weak => 0 | .strong => 1

instance : LinearOrder ENStrength :=
  LinearOrder.lift' ENStrength.toNat
    (fun a b h => by cases a <;> cases b <;> simp_all [ENStrength.toNat])

/-! ### Polarity classes and licensing profiles -/

/-- The four classes of polarity-sensitive elements tested by
    [greco-2020] Table 1. Each EN environment either licenses
    or rejects each class, giving a four-bit fingerprint. -/
inductive PolarityClass where
  | weakNPI      -- weak NPIs: *alzare un dito* 'lift a finger', *mai* 'ever'
  | strongNPI    -- strong NPIs: *affatto* 'at all'
  | notAlsoConj  -- *e neanche* / *not ... also* conjunctions
  | nWord        -- N-words: *nessuno* 'nobody'
  deriving DecidableEq, Repr

-- ── PolarityClass: Fintype ──

/-- PolarityClass ≃ Fin 4: weakNPI ↦ 0, strongNPI ↦ 1, notAlsoConj ↦ 2, nWord ↦ 3. -/
def PolarityClass.equivFin : PolarityClass ≃ Fin 4 where
  toFun | .weakNPI => 0 | .strongNPI => 1 | .notAlsoConj => 2 | .nWord => 3
  invFun | ⟨0, _⟩ => .weakNPI | ⟨1, _⟩ => .strongNPI | ⟨2, _⟩ => .notAlsoConj | ⟨3, _⟩ => .nWord
         | ⟨n + 4, h⟩ => absurd h (by omega)
  left_inv c := by cases c <;> rfl
  right_inv i := by
    match i with
    | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl | ⟨3, _⟩ => rfl
    | ⟨n + 4, h⟩ => exact absurd h (by omega)

instance : Fintype PolarityClass := Fintype.ofEquiv _ PolarityClass.equivFin.symm

/-- Polarity licensing profile for an EN environment ([greco-2020] Table 1).
    Each field records whether that class of polarity-sensitive element
    is grammatical in the construction. -/
structure PolarityLicensing where
  weakNPIs : Bool
  strongNPIs : Bool
  notAlsoConj : Bool
  nWords : Bool
  deriving DecidableEq, Repr

/-- Accessor: look up a polarity class in the licensing profile. -/
def PolarityLicensing.licenses (p : PolarityLicensing) : PolarityClass → Bool
  | .weakNPI     => p.weakNPIs
  | .strongNPI   => p.strongNPIs
  | .notAlsoConj => p.notAlsoConj
  | .nWord       => p.nWords

/-- Weak EN environments license weak NPIs and N-words but NOT
    strong NPIs or not-also conjunctions. -/
def weakENProfile : PolarityLicensing :=
  { weakNPIs := true, strongNPIs := false, notAlsoConj := false, nWords := true }

/-- Strong EN environments license NONE of the four polarity classes. -/
def strongENProfile : PolarityLicensing :=
  { weakNPIs := false, strongNPIs := false, notAlsoConj := false, nWords := false }

/-- The licensing profile determined by an EN strength class
    ([greco-2020] Table 1: rows are uniform within each class). -/
def ENStrength.profile : ENStrength → PolarityLicensing
  | .weak => weakENProfile
  | .strong => strongENProfile

/-- Strong EN rejects ALL polarity classes (universally quantified). -/
theorem strongEN_rejects_all (c : PolarityClass) :
    strongENProfile.licenses c = false := by cases c <;> rfl

/-- Weak EN licenses exactly the weak NPIs and N-words. -/
theorem weakEN_licenses_weakNPI : weakENProfile.licenses .weakNPI = true := rfl
theorem weakEN_licenses_nWord : weakENProfile.licenses .nWord = true := rfl
theorem weakEN_rejects_strongNPI : weakENProfile.licenses .strongNPI = false := rfl
theorem weakEN_rejects_notAlso : weakENProfile.licenses .notAlsoConj = false := rfl

-- ── PolarityLicensing: Equiv, Fintype, Lattice, BoundedOrder ──

/-- Equivalence with `Bool⁴` for `Fintype` derivation. -/
def PolarityLicensing.equiv : PolarityLicensing ≃ (Bool × Bool × Bool × Bool) where
  toFun p := (p.weakNPIs, p.strongNPIs, p.notAlsoConj, p.nWords)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
  left_inv p := by cases p; rfl
  right_inv t := by obtain ⟨_, _, _, _⟩ := t; rfl

instance : Fintype PolarityLicensing := Fintype.ofEquiv _ PolarityLicensing.equiv.symm

/-- Componentwise implication ordering: `a ≤ b` iff every class that `a`
    licenses, `b` also licenses. -/
private def PolarityLicensing.leBool (a b : PolarityLicensing) : Bool :=
  (!a.weakNPIs || b.weakNPIs) && (!a.strongNPIs || b.strongNPIs) &&
  (!a.notAlsoConj || b.notAlsoConj) && (!a.nWords || b.nWords)

instance : PartialOrder PolarityLicensing where
  le a b := a.leBool b = true
  le_refl a := by simp [PolarityLicensing.leBool]
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableRel (α := PolarityLicensing) (· ≤ ·) := fun a b =>
  inferInstanceAs (Decidable (a.leBool b = true))

instance : Lattice PolarityLicensing where
  sup a b := ⟨a.weakNPIs || b.weakNPIs, a.strongNPIs || b.strongNPIs,
              a.notAlsoConj || b.notAlsoConj, a.nWords || b.nWords⟩
  inf a b := ⟨a.weakNPIs && b.weakNPIs, a.strongNPIs && b.strongNPIs,
              a.notAlsoConj && b.notAlsoConj, a.nWords && b.nWords⟩
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

/-- Standard negation profile: licenses all polarity-sensitive elements. -/
def standardNegProfile : PolarityLicensing :=
  { weakNPIs := true, strongNPIs := true, notAlsoConj := true, nWords := true }

instance : OrderBot PolarityLicensing where
  bot := strongENProfile
  bot_le := by decide

instance : OrderTop PolarityLicensing where
  top := standardNegProfile
  le_top := by decide

/-- Strong EN (⊥) ≤ weak EN in the licensing lattice. -/
theorem strongEN_le_weakEN : strongENProfile ≤ weakENProfile := by decide

end Semantics.Negation
