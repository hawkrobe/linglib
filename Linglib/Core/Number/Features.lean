import Linglib.Core.Number.Value

/-!
# Number Feature Decomposition
@cite{harbour-2014}

Framework-neutral decomposition of number into binary features following
@cite{harbour-2014}'s lattice-theoretic account:

- **[±atomic]**: whether the referent is an atom (singleton) or a non-atom
  (plurality). Singular is [+atomic]; dual and plural are [−atomic].
- **[±minimal]**: whether the referent is a minimal element of the relevant
  lattice region. Singular and dual are [+minimal]; plural is [−minimal].

These features form a containment hierarchy: [+atomic] → [+minimal].
An atom is necessarily a minimal element of any lattice region it belongs to.

This containment parallels person features: [+author] → [+participant].

The three well-formed combinations yield the three basic number values:
- **singular**: [+atomic, +minimal] — atoms (singletons)
- **dual**: [−atomic, +minimal] — minimal non-atoms (pairs)
- **plural**: [−atomic, −minimal] — non-minimal non-atoms (triads and up)

Trial, unit augmented, and augmented arise from **feature recursion**
(reapplying [±minimal] to subregions), which is theory-layer material handled
in `Theories/`. The approximative numbers (paucal, greater paucal, greater
plural) require the additional feature [±additive], also theory-layer.

-/

namespace Core.Number

-- ============================================================================
-- § 1: Number Features
-- ============================================================================

/-- Binary number features: [±atomic, ±minimal].

    These two features suffice for the three basic number distinctions:
    - singular: [+atomic, +minimal]
    - dual:     [−atomic, +minimal]
    - plural:   [−atomic, −minimal]

    The fourth combination [+atomic, −minimal] is ill-formed:
    an atom is necessarily a minimal element of any lattice region. -/
structure Features where
  /-- [+atomic]: referent is an atom (singleton individual). -/
  isAtomic : Bool
  /-- [+minimal]: referent is a minimal element of the relevant lattice region. -/
  isMinimal : Bool
  deriving DecidableEq, BEq, Repr

/-- Well-formedness: [+atomic] → [+minimal].
    An atom (singleton) is necessarily a minimal element. -/
def Features.wellFormed (nf : Features) : Bool :=
  !nf.isAtomic || nf.isMinimal

-- ============================================================================
-- § 2: Canonical Number Feature Bundles
-- ============================================================================

/-- Singular features: [+atomic, +minimal]. -/
def singular : Features := ⟨true, true⟩

/-- Dual features: [−atomic, +minimal]. -/
def dual : Features := ⟨false, true⟩

/-- Plural features: [−atomic, −minimal]. -/
def plural : Features := ⟨false, false⟩

-- ============================================================================
-- § 3: Value Bridge
-- ============================================================================

/-- Map number features to Corbett's analytical number values.

    The three well-formed base feature bundles map to three of
    @cite{corbett-2000}'s eight values. The remaining values (trial,
    paucal, etc.) arise from feature recursion and [±additive], which
    require compositional machinery beyond the base feature pair. -/
def Features.toValue : Features → Option Value
  | ⟨true, true⟩   => some .singular
  | ⟨false, true⟩  => some .dual
  | ⟨false, false⟩ => some .plural
  | ⟨true, false⟩  => none  -- ill-formed

/-- Map Corbett's number values to base features (partial).

    Only the three values derivable from the base [±atomic, ±minimal]
    system have feature equivalents. Trial, paucal, and the rest require
    feature recursion or [±additive]. -/
def Features.fromValue : Value → Option Features
  | .singular => some singular
  | .dual     => some dual
  | .plural   => some plural
  | _         => none

-- ============================================================================
-- § 4: Verification
-- ============================================================================

theorem singular_wellFormed : singular.wellFormed = true := rfl
theorem dual_wellFormed : dual.wellFormed = true := rfl
theorem plural_wellFormed : plural.wellFormed = true := rfl

/-- The ill-formed combination [+atomic, −minimal] is the only
    combination that violates well-formedness. -/
theorem illFormed_only : (⟨true, false⟩ : Features).wellFormed = false := rfl

/-- There are exactly 3 well-formed feature combinations (= 3 base numbers). -/
theorem exactly_three_wellFormed :
    ([⟨true, true⟩, ⟨true, false⟩, ⟨false, true⟩, ⟨false, false⟩].filter
      Features.wellFormed).length = 3 := by native_decide

/-- Round-trip: fromValue ∘ toValue = some for all well-formed features. -/
theorem roundtrip_fromValue_toValue :
    [singular, dual, plural].all
      (λ f => f.toValue.bind Features.fromValue == some f) = true := by native_decide

/-- toValue returns none for the ill-formed bundle. -/
theorem illFormed_toValue_none :
    (⟨true, false⟩ : Features).toValue = none := rfl

/-- Containment: [+atomic] → [+minimal] for all well-formed features. -/
theorem atomic_implies_minimal (f : Features) (hw : f.wellFormed = true) :
    f.isAtomic = true → f.isMinimal = true := by
  intro ha
  simp [Features.wellFormed] at hw
  simp [ha] at hw
  exact hw

end Core.Number
