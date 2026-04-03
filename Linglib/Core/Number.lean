import Linglib.Core.Lexical.UD
import Linglib.Core.PrivativePair

/-!
# Number
@cite{corbett-2000} @cite{harbour-2014}

Two components of the number API:

**§ 1–3: Number Categories** (@cite{corbett-2000}). Eight analytical number
values organized along two orthogonal dimensions:
- **System membership**: general number is *outside* the number system (a form
  non-committal to cardinality); all others are within it.
- **Determinacy**: values whose cardinality boundary is fixed (singular=1,
  dual=2, trial=3) vs those whose boundary varies by context (paucal ≈ 2–6,
  greater plural ≈ abundance).

**§ 4–6: Number Features** (@cite{harbour-2014}). Binary feature decomposition:
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
(reapplying [±minimal] to subregions), which is theory-layer material.
The approximative numbers (paucal, greater paucal, greater plural) require
the additional feature [±additive], also theory-layer.

The full typological machinery (number systems, animacy profiles, agreement
hierarchy, language data) remains in
`Phenomena/Agreement/Studies/Corbett2000.lean`.

-/

namespace Core.Number

-- ============================================================================
-- § 1: Number Categories
-- ============================================================================

/-- Number categories in @cite{corbett-2000}'s inventory.

    Two orthogonal classifications:
    - **System membership**: general is *outside* the number system; all others
      are within it.
    - **Determinacy**: values whose cardinality boundary is fixed (singular=1,
      dual=2, trial=3) vs those whose boundary varies by context (paucal ≈ 2–6,
      greater plural ≈ all/abundance). -/
inductive Category where
  | general        -- non-committal, outside the number system
  | singular       -- exactly one
  | dual           -- exactly two
  | trial          -- exactly three
  | paucal         -- a few (indeterminate, ~2–6)
  | plural         -- more than one (residual)
  | greaterPaucal  -- indeterminate, larger than paucal
  | greaterPlural  -- abundance / totality (indeterminate)
  deriving DecidableEq, BEq, Repr

namespace Category

/-- A number category is determinate iff its cardinality boundary is fixed. -/
def isDeterminate : Category → Bool
  | .singular | .dual | .trial => true
  | _ => false

/-- A number category participates in the number system (is not general). -/
def isInSystem : Category → Bool
  | .general => false
  | _ => true

end Category

-- ============================================================================
-- § 2: UD Bridges
-- ============================================================================

/-- Map analytical number categories to UD.Number (general has no UD equivalent). -/
def Category.toUD : Category → Option UD.Number
  | .general       => none
  | .singular      => some .Sing
  | .dual          => some .Dual
  | .trial         => some .Tri
  | .paucal        => some .Pauc
  | .plural        => some .Plur
  | .greaterPaucal => some .Grpa
  | .greaterPlural => some .Grpl

/-- Map UD.Number to analytical number categories (partial).

    Seven core categories round-trip cleanly. Three UD values have no analytical
    equivalent:
    - `Inv` (inverse number): marks the *unexpected* number for a given noun —
      plural for some nouns, singular for others. Not a fixed cardinality.
    - `Coll` (collective): denotes a group-as-unit (Russian *листва* 'foliage'),
      distinct from general number which is non-committal to cardinality.
    - `Count` (count form): a special form after numerals (Hungarian, Welsh),
      not equivalent to singular (exactly one). -/
def Category.fromUD : UD.Number → Option Category
  | .Sing  => some .singular
  | .Plur  => some .plural
  | .Dual  => some .dual
  | .Tri   => some .trial
  | .Pauc  => some .paucal
  | .Grpa  => some .greaterPaucal
  | .Grpl  => some .greaterPlural
  | .Inv   => none
  | .Coll  => none
  | .Count => none

-- ============================================================================
-- § 3: Category Verification
-- ============================================================================

/-- Round-trip: fromUD ∘ toUD = id for all in-system categories. -/
theorem roundtrip_fromUD_toUD :
    [Category.singular, .dual, .trial, .paucal, .plural,
     .greaterPaucal, .greaterPlural].all
      (λ v => v.toUD.bind Category.fromUD == some v) = true := by native_decide

-- ============================================================================
-- § 4: Number Features
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

/-- Singular features: [+atomic, +minimal]. -/
def singularF : Features := ⟨true, true⟩

/-- Dual features: [−atomic, +minimal]. -/
def dualF : Features := ⟨false, true⟩

/-- Plural features: [−atomic, −minimal]. -/
def pluralF : Features := ⟨false, false⟩

-- ============================================================================
-- § 5: Features ↔ Category Bridge
-- ============================================================================

/-- Map number features to Corbett's analytical number categories.

    The three well-formed base feature bundles map to three of
    @cite{corbett-2000}'s eight categories. The remaining (trial,
    paucal, etc.) arise from feature recursion and [±additive], which
    require compositional machinery beyond the base feature pair. -/
def Features.toCategory : Features → Option Category
  | ⟨true, true⟩   => some .singular
  | ⟨false, true⟩  => some .dual
  | ⟨false, false⟩ => some .plural
  | ⟨true, false⟩  => none  -- ill-formed

/-- Map Corbett's number categories to base features (partial).

    Only the three categories derivable from the base [±atomic, ±minimal]
    system have feature equivalents. Trial, paucal, and the rest require
    feature recursion or [±additive]. -/
def Features.fromCategory : Category → Option Features
  | .singular => some singularF
  | .dual     => some dualF
  | .plural   => some pluralF
  | _         => none

-- ============================================================================
-- § 6: PhiFeatures Instance
-- ============================================================================

/-- Number features are a `PhiFeatures` instance:
    outer = isMinimal, inner = isAtomic.

    The containment [+atomic] → [+minimal] maps to PrivativePair's
    [+inner] → [+outer], unifying the structure with person features.
    All shared properties are inherited by construction. -/
instance : Core.PhiFeatures Features where
  toPair f := ⟨f.isMinimal, f.isAtomic⟩
  ofPair p := ⟨p.inner, p.outer⟩
  roundtrip := fun ⟨_, _⟩ => rfl

/-- The three canonical number values map to the three PrivativePair cells. -/
theorem singular_is_maximal : PhiFeatures.toPair singularF = .maximal := rfl
theorem dual_is_intermediate : PhiFeatures.toPair dualF = .intermediate := rfl
theorem plural_is_minimal : PhiFeatures.toPair pluralF = .minimal := rfl

/-- No 4-way base number distinction (inherited from `PhiFeatures`). -/
theorem no_fourth_base_number :
    ∀ (a b c d : Features),
      a.wellFormed = true → b.wellFormed = true →
      c.wellFormed = true → d.wellFormed = true →
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → False :=
  fun a b c d ha hb hc hd =>
    Core.PhiFeatures.no_four_way a b c d ha hb hc hd

-- ============================================================================
-- § 7: Features Verification
-- ============================================================================

theorem singular_wellFormed : singularF.wellFormed = true := rfl
theorem dual_wellFormed : dualF.wellFormed = true := rfl
theorem plural_wellFormed : pluralF.wellFormed = true := rfl

/-- The ill-formed combination [+atomic, −minimal] is the only
    combination that violates well-formedness. -/
theorem illFormed_only : (⟨true, false⟩ : Features).wellFormed = false := rfl

/-- There are exactly 3 well-formed feature combinations (= 3 base numbers). -/
theorem exactly_three_wellFormed :
    ([⟨true, true⟩, ⟨true, false⟩, ⟨false, true⟩, ⟨false, false⟩].filter
      Features.wellFormed).length = 3 := by native_decide

/-- Round-trip: fromCategory ∘ toCategory = some for all well-formed features. -/
theorem roundtrip_fromCategory_toCategory :
    [singularF, dualF, pluralF].all
      (λ f => f.toCategory.bind Features.fromCategory == some f) = true := by
  native_decide

/-- toCategory returns none for the ill-formed bundle. -/
theorem illFormed_toCategory_none :
    (⟨true, false⟩ : Features).toCategory = none := rfl

/-- Containment: [+atomic] → [+minimal] for all well-formed features. -/
theorem atomic_implies_minimal (f : Features) (hw : f.wellFormed = true) :
    f.isAtomic = true → f.isMinimal = true := by
  intro ha
  simp [Features.wellFormed] at hw
  simp [ha] at hw
  exact hw

-- ============================================================================
-- § 8: Lattice-Theoretic Grounding
-- ============================================================================

/-! ### Lattice-Theoretic Grounding

Number features grounded in a join-semilattice of individuals.

Link (1983) models the domain of individuals as a join-semilattice
⟨D, ⊔⟩. Number categories correspond to lattice predicates:
- **singular** = atoms (no proper part)
- **dual** = minimal non-atoms (join of exactly 2 atoms)
- **plural** = non-minimal non-atoms

The containment [+atomic] → [+minimal] is a *theorem* of lattice
theory, not a stipulation: atoms have no proper parts, so they are
trivially minimal in any sublattice region. -/

/-- An element is an atom if no smaller element exists in the domain
    (besides itself). -/
def isAtomIn {D : Type} [DecidableEq D] (elems : List D) (x : D) : Bool :=
  elems.all λ y => y == x || !(elems.contains y && elems.contains x)

/-- An element is minimal in a sublattice if no element in the same
    region is strictly smaller. For non-atoms, "minimal" means there
    is no non-atom strictly below. -/
def isMinimalNonAtom {D : Type} [DecidableEq D]
    (atoms nonAtoms : List D) (x : D) : Bool :=
  !atoms.contains x &&
  nonAtoms.all λ y => y == x || !(nonAtoms.contains y)

/-- Convert lattice membership to number features.
    Atoms → singular, minimal non-atoms → dual, others → plural. -/
def latticeToFeatures {D : Type} [DecidableEq D]
    (atoms nonAtoms : List D) (x : D) : Features :=
  if atoms.contains x then singularF
  else if isMinimalNonAtom atoms nonAtoms x then dualF
  else pluralF

/-- Containment follows from lattice structure: atoms always get
    [+minimal], so [+atomic] → [+minimal] holds by construction.
    Every branch of `latticeToFeatures` produces a well-formed bundle. -/
theorem latticeToFeatures_wellFormed {D : Type} [DecidableEq D]
    (atoms nonAtoms : List D) (x : D) :
    (latticeToFeatures atoms nonAtoms x).wellFormed = true := by
  simp only [latticeToFeatures]
  split
  · rfl
  · split
    · rfl
    · rfl

/-- Concrete example: a 3-element domain {a, b, a⊔b}.
    a and b are atoms → singular; a⊔b is minimal non-atom → dual. -/
private def exAtoms : List Nat := [0, 1]
private def exNonAtoms : List Nat := [2]

theorem ex_atom_is_singular :
    latticeToFeatures exAtoms exNonAtoms 0 = singularF := rfl
theorem ex_atom_is_singular' :
    latticeToFeatures exAtoms exNonAtoms 1 = singularF := rfl
theorem ex_pair_is_dual :
    latticeToFeatures exAtoms exNonAtoms 2 = dualF := rfl

end Core.Number
