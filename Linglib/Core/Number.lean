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
  | singular       -- exactly one ([+atomic, +minimal])
  | dual           -- exactly two ([−atomic, +minimal])
  | trial          -- exactly three (recursive [+minimal] on plural region)
  | paucal         -- a few (indeterminate, [−additive])
  | plural         -- more than one (residual, [−atomic] or [+additive])
  | greaterPaucal  -- indeterminate, larger than paucal ([−additive]*)
  | greaterPlural  -- abundance / totality (recursive [−minimal] on plural)
  | minimal        -- [+minimal] without [±atomic] — includes atoms AND
                    -- minimal non-atoms; distinct from singular
  | augmented      -- [−minimal] without [±atomic] — complement of minimal
  | unitAugmented  -- recursive [+minimal] on augmented region — minimal
                    -- non-minimal; distinct from dual
  | globalPlural   -- recursive [+additive] on [+additive] region (tentative)
  deriving DecidableEq, BEq, Repr

namespace Category

/-- A number category is determinate iff its cardinality boundary is fixed.
    Minimal and unit augmented are indeterminate: they depend on the
    composition of the group, not a fixed cardinality. -/
def isDeterminate : Category → Bool
  | .singular | .dual | .trial => true
  | _ => false

/-- A number category participates in the number system (is not general). -/
def isInSystem : Category → Bool
  | .general => false
  | _ => true

/-- Exact referent-set cardinality for determinate number categories.

    Singular denotes exactly 1 individual (atom), dual exactly 2 (pair),
    trial exactly 3 (triple). All other categories — plural, paucal,
    greaterPlural, minimal, augmented — have indeterminate or
    context-dependent cardinality and return `none`.

    Used by `CoordinateResolution.canonicalResolve` to derive resolution
    from cardinality addition: |A ⊔ B| = |A| + |B| for disjoint sets. -/
def exactCard : Category → Option Nat
  | .singular => some 1
  | .dual     => some 2
  | .trial    => some 3
  | _         => none

/-- Whether a category belongs to the [±minimal] number system (without
    [±atomic]). In such systems, minimal = atoms ∪ minimal non-atoms,
    and augmented = everything else. Returns `none` for categories
    outside the MIN/AUG system. -/
def isMinAug : Category → Bool
  | .minimal | .augmented => true
  | _ => false

/-- Map a referent-set cardinality back to the finest determinate category.
    1 → singular, 2 → dual, 3 → trial, 4+ → greaterPlural. -/
def fromCard : Nat → Category
  | 1 => .singular
  | 2 => .dual
  | 3 => .trial
  | _ => .greaterPlural

/-- `fromCard` inverts `exactCard` for determinate categories. -/
theorem fromCard_singular : fromCard 1 = .singular := rfl
theorem fromCard_dual : fromCard 2 = .dual := rfl
theorem fromCard_trial : fromCard 3 = .trial := rfl

end Category

-- ============================================================================
-- § 2: UD Bridges
-- ============================================================================

/-- Map analytical number categories to UD.Number (general has no UD equivalent).
    Minimal, augmented, unit augmented, and global plural have no UD representation. -/
def Category.toUD : Category → Option UD.Number
  | .general        => none
  | .singular       => some .Sing
  | .dual           => some .Dual
  | .trial          => some .Tri
  | .paucal         => some .Pauc
  | .plural         => some .Plur
  | .greaterPaucal  => some .Grpa
  | .greaterPlural  => some .Grpl
  | .minimal        => none
  | .augmented      => none
  | .unitAugmented  => none
  | .globalPlural   => none

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
    system have feature equivalents. Trial, paucal, minimal, augmented,
    and the rest require feature recursion, [±additive], or different
    feature activation patterns. -/
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

@cite{link-1983} models the domain of individuals as a join-semilattice
⟨D, ⊔⟩. Number categories correspond to lattice predicates:
- **singular** = atoms (no proper part)
- **dual** = minimal non-atoms (join of exactly 2 atoms)
- **plural** = non-minimal non-atoms

The containment [+atomic] → [+minimal] is a *theorem* of lattice
theory, not a stipulation: atoms have no proper parts, so they are
trivially minimal in any sublattice region (`Mereology.Atom`).

The decidable functions `isAtom` and `isMinimalNonAtom` are parameterized
by a join operation and a finite domain, making the lattice-theoretic
grounding computationally verifiable. They are the `Bool` counterparts
of `Mereology.Atom` and minimality-in-region. -/

/-- Powerset lattice join (bitwise OR). Atoms are powers of 2;
    sums are bitwise OR of their atoms. Used across §§8–10 and
    by `CoordinateResolution` for lattice verification. -/
def bitmaskJoin (a b : Nat) : Nat := Nat.lor a b

/-- Ordering induced by join: a ≤ b iff a ⊔ b = b.
    In a join-semilattice, this is the canonical partial order. -/
private def joinLE {D : Type} [DecidableEq D]
    (join : D → D → D) (a b : D) : Bool :=
  join a b == b

/-- An element is an atom in a domain under the join-induced ordering:
    x ∈ domain and no element other than x is below it.
    Decidable counterpart of `Mereology.Atom` (∀ y, y ≤ x → y = x),
    parameterized by a concrete join operation and finite domain. -/
def isAtom {D : Type} [DecidableEq D]
    (join : D → D → D) (domain : List D) (x : D) : Bool :=
  domain.contains x &&
  domain.all fun y => y == x || !(joinLE join y x)

/-- An element is a minimal non-atom: not an atom, and no non-atom in
    the domain is strictly below it in the join-induced ordering.
    For number: minimal non-atoms are duals (pairs of exactly 2 atoms).
    Non-minimal non-atoms are plurals (groups of 3+). -/
def isMinimalNonAtom {D : Type} [DecidableEq D]
    (join : D → D → D) (domain : List D) (x : D) : Bool :=
  let nonAtoms := domain.filter (! isAtom join domain ·)
  nonAtoms.contains x &&
  nonAtoms.all fun y => y == x || !(joinLE join y x)

/-- Convert lattice membership to number features using join structure.
    Atoms → singular, minimal non-atoms → dual, others → plural. -/
def latticeToFeatures {D : Type} [DecidableEq D]
    (join : D → D → D) (domain : List D) (x : D) : Features :=
  if isAtom join domain x then singularF
  else if isMinimalNonAtom join domain x then dualF
  else pluralF

/-- Containment follows from lattice structure: atoms always get
    [+minimal], so [+atomic] → [+minimal] holds by construction.
    Every branch of `latticeToFeatures` produces a well-formed bundle. -/
theorem latticeToFeatures_wellFormed {D : Type} [DecidableEq D]
    (join : D → D → D) (domain : List D) (x : D) :
    (latticeToFeatures join domain x).wellFormed = true := by
  simp only [latticeToFeatures]
  split
  · rfl
  · split
    · rfl
    · rfl

/-- Powerset lattice with 2 atoms: {0}=1, {1}=2, {0,1}=3. -/
private def ps2Domain : List Nat := [1, 2, 3]

theorem ex_atom_is_singular :
    latticeToFeatures bitmaskJoin ps2Domain 1 = singularF := by native_decide
theorem ex_atom_is_singular' :
    latticeToFeatures bitmaskJoin ps2Domain 2 = singularF := by native_decide
theorem ex_pair_is_dual :
    latticeToFeatures bitmaskJoin ps2Domain 3 = dualF := by native_decide

/-- Powerset lattice with 3 atoms: {0}=1, {1}=2, {2}=4.
    Pairs (3,5,6) are minimal non-atoms → dual.
    Triple (7) is non-minimal non-atom → plural.
    This demonstrates that `isMinimalNonAtom` correctly distinguishes
    duals from plurals in a non-trivial lattice (the 2-atom domain
    above has only one non-atom and cannot show this). -/
def ps3Domain : List Nat := [1, 2, 4, 3, 5, 6, 7]

theorem ps3_atom_is_singular :
    latticeToFeatures bitmaskJoin ps3Domain 1 = singularF := by native_decide
theorem ps3_pair_is_dual :
    latticeToFeatures bitmaskJoin ps3Domain 3 = dualF := by native_decide
theorem ps3_pair_is_dual' :
    latticeToFeatures bitmaskJoin ps3Domain 5 = dualF := by native_decide
theorem ps3_triple_is_plural :
    latticeToFeatures bitmaskJoin ps3Domain 7 = pluralF := by native_decide

-- ============================================================================
-- § 9: The Additive Feature
-- ============================================================================

/-! ### The Additive Feature
@cite{harbour-2014}

[±additive] is the third number feature, characterizing
join-completeness within a lattice region. Applied to the non-atomic
region, it separates:
- [+additive] = "abundance" (plural/greater plural) — join-complete
- [−additive] = "paucity" (paucal/greater paucal) — not join-complete

The boundary is fixed by sociosemantic convention, subject to:
- **Complement completeness** ((11)): the [+additive] subregion must
  be join-complete.
- **Fungibility** ((12)): the boundary must be permutation-invariant
  (horizontal cuts by cardinality, not identity of atoms).

**Connection to CUM**: [+additive] IS cumulativity restricted to a
subregion. The link between number and aspect/telicity
(@cite{harbour-2014} §4.4) runs through exactly this connection:
mass nouns satisfy [+additive] (cumulative), count nouns satisfy
[−additive] (quantized). -/

/-- An element is join-complete in a region under a given join operation.
    @cite{harbour-2014} (10): [+additive](x) ⟺ x ∈ Q ∧ ∀y ∈ Q, x ⊔ y ∈ Q. -/
def isJoinCompleteIn {D : Type} [DecidableEq D]
    (join : D → D → D) (region : List D) (x : D) : Bool :=
  region.contains x &&
  region.all fun y => region.contains (join x y)

/-- A region is globally join-complete: every element is [+additive].
    Decidable counterpart of `Mereology.CUM` restricted to the region:
    CUM(Q) ⇔ ∀x,y ∈ Q, x ⊔ y ∈ Q. -/
def isRegionJoinComplete {D : Type} [DecidableEq D]
    (join : D → D → D) (region : List D) : Bool :=
  region.all fun x => isJoinCompleteIn join region x

-- ============================================================================
-- § 10: Additive Feature — Powerset Lattice Examples
-- ============================================================================

/-! ### Powerset Lattice Examples

Paucal vs plural on a powerset lattice (join = bitwise OR). Atoms
encoded as powers of 2; sums as bitwise OR of their atoms.

With 3 atoms, the non-atomic region is entirely join-complete, so
[±additive] draws no distinction — paucal requires a richer lattice.

With 5 atoms, the "paucal" region (2–3 atoms) is NOT join-complete:
two small sums can join to exceed "a few." The "plural" region
(≥ 4 atoms) IS join-complete, satisfying complement completeness. -/

/-- Non-atoms in the 3-atom powerset. Atoms: {0}=1, {1}=2, {2}=4.
    Non-atoms: {0,1}=3, {0,2}=5, {1,2}=6, {0,1,2}=7. -/
private def ps3NonAtoms : List Nat := [3, 5, 6, 7]

/-- With 3 atoms, the entire non-atomic region is join-complete.
    [±additive] is vacuous — no paucal/plural split possible. -/
theorem ps3_nonAtoms_joinComplete :
    isRegionJoinComplete bitmaskJoin ps3NonAtoms = true := by native_decide

/-- "Paucal" region in a 5-atom powerset: elements with 2–3 atoms.
    Atoms: 1, 2, 4, 8, 16.
    Dyads (C(5,2)=10): 3, 5, 6, 9, 10, 12, 17, 18, 20, 24.
    Triads (C(5,3)=10): 7, 11, 13, 14, 19, 21, 22, 25, 26, 28. -/
private def ps5Paucal : List Nat :=
  [3, 5, 6, 9, 10, 12, 17, 18, 20, 24,
   7, 11, 13, 14, 19, 21, 22, 25, 26, 28]

/-- "Plural" region in a 5-atom powerset: elements with ≥ 4 atoms.
    Tetrads (C(5,4)=5): 15, 23, 27, 29, 30. Pentad: 31. -/
private def ps5Plural : List Nat := [15, 23, 27, 29, 30, 31]

/-- The paucal region is NOT join-complete: {0,1}=3 ⊔ {2,3}=12 =
    {0,1,2,3}=15 has 4 atoms and escapes the region. -/
theorem ps5_paucal_not_joinComplete :
    isRegionJoinComplete bitmaskJoin ps5Paucal = false := by native_decide

/-- The plural region IS join-complete: joining two large sums stays
    large. Satisfies complement completeness (@cite{harbour-2014} (11)). -/
theorem ps5_plural_joinComplete :
    isRegionJoinComplete bitmaskJoin ps5Plural = true := by native_decide

/-- The paucal/plural asymmetry: the [+additive] region is join-complete,
    the [−additive] region is not. This is the formal content of the
    approximative number distinction (@cite{harbour-2014} §3). -/
theorem ps5_additive_asymmetry :
    isRegionJoinComplete bitmaskJoin ps5Plural = true ∧
    isRegionJoinComplete bitmaskJoin ps5Paucal = false :=
  ⟨ps5_plural_joinComplete, ps5_paucal_not_joinComplete⟩

end Core.Number
