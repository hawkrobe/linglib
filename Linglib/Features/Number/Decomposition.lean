import Linglib.Features.Number.Basic
import Linglib.Features.Number.Interp
import Linglib.Features.ContainmentPair

/-!
# Number — the Harbour feature decomposition and its lattice grounding
[harbour-2014] [link-1983]

Binary feature decomposition of the number values ([harbour-2014]):

- **[±atomic]**: whether the referent is an atom (singleton) or a non-atom
  (plurality). Singular is [+atomic]; dual and plural are [−atomic].
- **[±minimal]**: whether the referent is a minimal element of the relevant
  lattice region. Singular and dual are [+minimal]; plural is [−minimal].

These features form a containment hierarchy: [+atomic] → [+minimal].
An atom is necessarily a minimal element of any lattice region it belongs to.

This containment parallels person features ([+author] → [+participant]),
but with an asymmetry worth marking: number's filter is a *theorem* of the
lattice semantics (the grounding sections below — atoms are minimal;
[harbour-2016] ch. 9.5 notes the odd cooccurrence is contradictory for
`±atomic` "by the logic of the system"), whereas person's filter is a
descriptive convention the same chapter rejects. See
`Features/ContainmentPair.lean`.

The three well-formed combinations yield the three basic number values:
- **singular**: [+atomic, +minimal] — atoms (singletons)
- **dual**: [−atomic, +minimal] — minimal non-atoms (pairs)
- **plural**: [−atomic, −minimal] — non-minimal non-atoms (triads and up)

Trial, unit augmented, and augmented arise from **feature recursion**
(reapplying [±minimal] to subregions; `Syntax/Minimalist/Phi/Recursion.lean`).
The approximative numbers require the additional feature [±additive] (§ on
the additive feature below).

## Main declarations

* `Number.Features` — the [±atomic, ±minimal] bundle, with the containment
  filter `Features.WellFormed` and the `ContainmentPairLike` presentation
  unifying it with the person skeleton
  (`featuresEquiv : Features ≃ ContainmentPair`).
* `Number.latticeToFeatures` — classify a lattice element as
  singular/dual/plural by its position.
* `Number.isJoinCompleteIn` / `Number.isRegionJoinComplete` — the
  [±additive] feature ([harbour-2014]): join-completeness within a region.
* `Number.dualPredOnLattice` — ⟦DUAL⟧ as a predicate modifier
  ([jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025]), grounded in
  the feature decomposition by `dualPredOnLattice_eq_via_features`.
-/

set_option autoImplicit false

namespace Number

open _root_.Features (ContainmentPair ContainmentPairLike)

/-! ### The feature bundle -/

/-- Bivalent number features: [±atomic, ±minimal].

    These two features suffice for the three basic number distinctions:
    - singular: [+atomic, +minimal]
    - dual:     [−atomic, +minimal]
    - plural:   [−atomic, −minimal]

    The fourth combination [+atomic, −minimal] is cut by the containment
    filter (`WellFormed`): an atom is necessarily a minimal element of any
    lattice region (a theorem of the semantics — §8). -/
structure Features where
  /-- [+atomic]: referent is an atom (singleton individual). -/
  isAtomic : Bool
  /-- [+minimal]: referent is a minimal element of the relevant lattice region. -/
  isMinimal : Bool
  deriving DecidableEq, Repr, Fintype

/-- Singular features: [+atomic, +minimal]. -/
def singularF : Features := ⟨true, true⟩

/-- Dual features: [−atomic, +minimal]. -/
def dualF : Features := ⟨false, true⟩

/-- Plural features: [−atomic, −minimal]. -/
def pluralF : Features := ⟨false, false⟩

/-! ### Features ↔ value bridge -/

/-- Map a feature bundle to the number value it realizes.

    The three well-formed base bundles map to three of
    [corbett-2000]'s values. The remaining (trial,
    paucal, etc.) arise from feature recursion and [±additive], which
    require compositional machinery beyond the base feature pair. -/
def Features.toNumber : Features → Option Number
  | ⟨true, true⟩   => some .singular
  | ⟨false, true⟩  => some .dual
  | ⟨false, false⟩ => some .plural
  | ⟨true, false⟩  => none  -- ill-formed

/-- Map a number value to its base feature bundle (partial).

    Only the three values derivable from the base [±atomic, ±minimal]
    system have feature equivalents. Trial, paucal, minimal, augmented,
    and the rest require feature recursion, [±additive], or different
    feature activation patterns. -/
def Features.ofNumber : Number → Option Features
  | .singular => some singularF
  | .dual     => some dualF
  | .plural   => some pluralF
  | _         => none

/-! ### The `ContainmentPairLike` presentation -/

/-- The `[±atomic, ±minimal]` decomposition is carrier-equivalent to the
containment pair: `outer` = minimal, `inner` = atomic. The containment
[+atomic] → [+minimal] maps to [+inner] → [+outer], unifying the structure
with person features — one edge of the φ-feature iso-web
(`Features/PhiKernel.lean`). -/
def featuresEquiv : Features ≃ ContainmentPair where
  toFun f := ⟨f.isMinimal, f.isAtomic⟩
  invFun p := ⟨p.inner, p.outer⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

instance : ContainmentPairLike Features := .ofEquiv featuresEquiv

/-- The three canonical number values land on the three well-formed cells. -/
@[simp] theorem singular_is_maximal :
    ContainmentPairLike.toPair singularF = .maximal := rfl
@[simp] theorem dual_is_intermediate :
    ContainmentPairLike.toPair dualF = .intermediate := rfl
@[simp] theorem plural_is_minimal :
    ContainmentPairLike.toPair pluralF = .minimal := rfl

/-- Well-formedness: [+atomic] → [+minimal] — an atom is necessarily a
    minimal element. Inherited from `ContainmentPair.WellFormed` through
    the presentation; for number this filter is a theorem of the lattice
    semantics (§8), not a stipulation. -/
abbrev Features.WellFormed (nf : Features) : Prop :=
  ContainmentPairLike.WellFormed nf

/-- No 4-way base number distinction (inherited from
    `ContainmentPairLike.no_four_way`). -/
theorem no_fourth_base_number :
    ∀ (a b c d : Features),
      a.WellFormed → b.WellFormed → c.WellFormed → d.WellFormed →
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → False :=
  fun a b c d ha hb hc hd =>
    ContainmentPairLike.no_four_way a b c d ha hb hc hd

/-! ### Verification -/

@[simp] theorem singular_wellFormed : singularF.WellFormed := by decide
@[simp] theorem dual_wellFormed : dualF.WellFormed := by decide
@[simp] theorem plural_wellFormed : pluralF.WellFormed := by decide

/-- The filtered combination [+atomic, −minimal] is the only one that
    violates containment. -/
theorem illFormed_only : ¬ (⟨true, false⟩ : Features).WellFormed := by decide

/-- Exactly 3 well-formed feature combinations (= 3 base numbers) — the
    carrier count of the containment chain
    (`ContainmentPair.card_wellFormed`). -/
theorem card_wellFormed :
    Fintype.card {nf : Features // nf.WellFormed} = 3 := by decide

/-- Round-trip: `ofNumber ∘ toNumber = some` for all well-formed features. -/
theorem roundtrip_ofNumber_toNumber :
    [singularF, dualF, pluralF].all
      (λ f => f.toNumber.bind Features.ofNumber == some f) = true := by
  decide

/-- `toNumber` returns none for the filtered bundle. -/
theorem illFormed_toNumber_none :
    (⟨true, false⟩ : Features).toNumber = none := rfl

/-- Containment: [+atomic] → [+minimal] for all well-formed features. -/
theorem atomic_implies_minimal :
    ∀ f : Features, f.WellFormed → f.isAtomic = true → f.isMinimal = true := by
  decide

/-! ### Lattice-theoretic grounding

Number features grounded in a join-semilattice of individuals.

[link-1983] models the domain of individuals as a join-semilattice
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

/-! The decidable layer below mirrors the general lattice semantics of
`Features/Number/Interp.lean` on finite, list-enumerated domains: the
`Bool`-valued `isAtom` is domain-relative minimality (`Number.minimalIn
(· ∈ domain)` — `isAtom_iff_minimalIn`), `isMinimalNonAtom` mirrors
minimality over the non-atoms (`isMinimalNonAtom_iff_minimalIn`), and
`isJoinCompleteIn` mirrors `Number.additiveIn`
(`isJoinCompleteIn_iff_additiveIn`). `Interp`'s `Mereology.Atom` is
global minimality; the two agree when the domain enumerates a
downward-closed region of `D⁺`. -/

/-- Powerset lattice join (bitwise OR). Atoms are powers of 2;
    sums are bitwise OR of their atoms. Used across the lattice
    sections below and by `Number.resolve` for lattice verification. -/
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

/-- The `Bool` atom test is domain-relative minimality: the decidable
    mirror of `Number.minimalIn (· ∈ domain)` for the lattice join. -/
theorem isAtom_iff_minimalIn {D : Type} [SemilatticeSup D] [DecidableEq D]
    (domain : List D) (x : D) :
    isAtom (· ⊔ ·) domain x = true ↔ minimalIn (· ∈ domain) x := by
  simp only [isAtom, joinLE, minimalIn, Bool.and_eq_true, List.contains_iff,
    List.all_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h y hy hyx
    rcases h y hy with rfl | hn
    · rfl
    · exact absurd (sup_eq_right.mpr hyx) hn
  · intro h y hy
    by_cases hyx : y ≤ x
    · exact Or.inl (h y hy hyx)
    · exact Or.inr fun he => hyx (sup_eq_right.mp he)

/-- The `Bool` minimal-non-atom test mirrors `Number.minimalIn` over the
    domain's non-atoms — the region `interp` assigns to the dual. -/
theorem isMinimalNonAtom_iff_minimalIn {D : Type} [SemilatticeSup D]
    [DecidableEq D] (domain : List D) (x : D) :
    isMinimalNonAtom (· ⊔ ·) domain x = true ↔
      minimalIn (fun y => y ∈ domain ∧ ¬minimalIn (· ∈ domain) y) x := by
  have hmem : ∀ y : D,
      (y ∈ domain.filter (! isAtom (· ⊔ ·) domain ·)) ↔
        (y ∈ domain ∧ ¬minimalIn (· ∈ domain) y) := by
    intro y
    rw [List.mem_filter, Bool.not_eq_true', ← isAtom_iff_minimalIn,
      Bool.not_eq_true]
  simp only [isMinimalNonAtom, joinLE, minimalIn, Bool.and_eq_true,
    List.contains_iff, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
  rw [and_congr_left fun _ => hmem x]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h y hy hyx
    rcases h y ((hmem y).mpr hy) with rfl | hn
    · rfl
    · exact absurd (sup_eq_right.mpr hyx) hn
  · intro h y hy
    by_cases hyx : y ≤ x
    · exact Or.inl (h y ((hmem y).mp hy) hyx)
    · exact Or.inr fun he => hyx (sup_eq_right.mp he)


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
    (latticeToFeatures join domain x).WellFormed := by
  simp only [latticeToFeatures]
  split
  · exact singular_wellFormed
  · split
    · exact dual_wellFormed
    · exact plural_wellFormed

/-- Powerset lattice with 2 atoms: {0}=1, {1}=2, {0,1}=3. -/
private def ps2Domain : List Nat := [1, 2, 3]

theorem ex_atom_is_singular :
    latticeToFeatures bitmaskJoin ps2Domain 1 = singularF := by decide
theorem ex_atom_is_singular' :
    latticeToFeatures bitmaskJoin ps2Domain 2 = singularF := by decide
theorem ex_pair_is_dual :
    latticeToFeatures bitmaskJoin ps2Domain 3 = dualF := by decide

/-- Powerset lattice with 3 atoms: {0}=1, {1}=2, {2}=4.
    Pairs (3,5,6) are minimal non-atoms → dual.
    Triple (7) is non-minimal non-atom → plural.
    This demonstrates that `isMinimalNonAtom` correctly distinguishes
    duals from plurals in a non-trivial lattice (the 2-atom domain
    above has only one non-atom and cannot show this). -/
def ps3Domain : List Nat := [1, 2, 4, 3, 5, 6, 7]

theorem ps3_atom_is_singular :
    latticeToFeatures bitmaskJoin ps3Domain 1 = singularF := by decide
theorem ps3_pair_is_dual :
    latticeToFeatures bitmaskJoin ps3Domain 3 = dualF := by decide
theorem ps3_pair_is_dual' :
    latticeToFeatures bitmaskJoin ps3Domain 5 = dualF := by decide
theorem ps3_triple_is_plural :
    latticeToFeatures bitmaskJoin ps3Domain 7 = pluralF := by decide

/-! ### The additive feature
[harbour-2014]

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
([harbour-2014] §4.4) runs through exactly this connection:
mass nouns satisfy [+additive] (cumulative), count nouns satisfy
[−additive] (quantized). -/

/-- An element is join-complete in a region under a given join operation.
    [harbour-2014] (10): [+additive](x) ⟺ x ∈ Q ∧ ∀y ∈ Q, x ⊔ y ∈ Q. -/
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

/-- The `Bool` join-completeness test mirrors `Number.additiveIn` on the
    enumerated region. -/
theorem isJoinCompleteIn_iff_additiveIn {D : Type} [SemilatticeSup D]
    [DecidableEq D] (region : List D) (x : D) :
    isJoinCompleteIn (· ⊔ ·) region x = true ↔
      additiveIn (· ∈ region) x := by
  simp only [isJoinCompleteIn, additiveIn, Bool.and_eq_true,
    List.contains_iff, List.all_eq_true]


/-! ### Additive feature — powerset lattice examples

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
    isRegionJoinComplete bitmaskJoin ps3NonAtoms = true := by decide

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
    isRegionJoinComplete bitmaskJoin ps5Paucal = false := by decide

/-- The plural region IS join-complete: joining two large sums stays
    large. Satisfies complement completeness ([harbour-2014] (11)). -/
theorem ps5_plural_joinComplete :
    isRegionJoinComplete bitmaskJoin ps5Plural = true := by decide

/-- The paucal/plural asymmetry: the [+additive] region is join-complete,
    the [−additive] region is not. This is the formal content of the
    approximative number distinction ([harbour-2014] §3). -/
theorem ps5_additive_asymmetry :
    isRegionJoinComplete bitmaskJoin ps5Plural = true ∧
    isRegionJoinComplete bitmaskJoin ps5Paucal = false :=
  ⟨ps5_plural_joinComplete, ps5_paucal_not_joinComplete⟩

/-! ### DUAL as predicate modifier
[jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025]

The paper proposes (eq 39 in §4.2.1, derived from Harbour features
in §8 eq 98b) that the core concept DUAL has a predicate-modification
semantics:

  ⟦DUAL⟧ = λP.λx. P(x) ∧ |{y : atom(y) ∧ y ⊑ x}| = 2

In a join-semilattice, "exactly 2 atomic parts below x" coincides with
"x is a minimal non-atom" — already formalized as `isMinimalNonAtom`.
The bridge is therefore a one-line composition: filter P by the dual
lattice predicate.

This connects the Harbour feature bundle `dualF = ⟨isAtomic := false,
isMinimal := true⟩` to the predicate modifier required by the paper's
Indirect Alternative analysis: *les deux* lexicalizes the predicate
modifier `dualPredOnLattice _ _ verres` ('cup'), which is what blocks
*tous les NP.dual*. See `Studies/JereticEtAl2025.lean`. -/

/-- ⟦DUAL⟧ as a predicate modifier on a join-semilattice domain
([jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025] eq 39).

Given a property `P` over individuals and an element `x`, `dualPredOnLattice`
holds of `x` iff `P x` and `x` has exactly 2 atomic parts. The latter is
witnessed by `isMinimalNonAtom`, since in a join-semilattice the minimal
non-atoms are precisely the joins of two atoms. -/
def dualPredOnLattice {D : Type} [DecidableEq D]
    (join : D → D → D) (domain : List D)
    (P : D → Bool) (x : D) : Bool :=
  P x && isMinimalNonAtom join domain x

/-- `dualPredOnLattice P` strictly refines `P`: the dual reading
of `P` is a subset of `P`. -/
theorem dualPredOnLattice_refines {D : Type} [DecidableEq D]
    (join : D → D → D) (domain : List D)
    (P : D → Bool) (x : D) :
    dualPredOnLattice join domain P x = true → P x = true := by
  simp only [dualPredOnLattice, Bool.and_eq_true]
  exact And.left

/-- The dual reading of a property holds of `x` iff `P x` and `x` is a
minimal non-atom in the domain. -/
theorem dualPredOnLattice_iff {D : Type} [DecidableEq D]
    (join : D → D → D) (domain : List D)
    (P : D → Bool) (x : D) :
    dualPredOnLattice join domain P x = true ↔
    P x = true ∧ isMinimalNonAtom join domain x = true := by
  simp only [dualPredOnLattice, Bool.and_eq_true]

/-- An element classified as a minimal non-atom is, by construction, not
an atom. This is a structural fact about `isMinimalNonAtom`: it filters
to the non-atom region of the domain before testing minimality. -/
theorem not_atom_of_isMinimalNonAtom {D : Type} [DecidableEq D]
    (join : D → D → D) (domain : List D) (x : D)
    (h : isMinimalNonAtom join domain x = true) :
    isAtom join domain x = false := by
  unfold isMinimalNonAtom at h
  rw [Bool.and_eq_true] at h
  have hMem : x ∈ domain.filter (! isAtom join domain ·) := by
    have := h.1
    simp only [List.contains_iff_exists_mem_beq, beq_iff_eq] at this
    obtain ⟨y, hy, rfl⟩ := this
    exact hy
  rw [List.mem_filter] at hMem
  simpa using hMem.2

/-- **Bridge**: the lattice predicate `isMinimalNonAtom` IS the condition
`latticeToFeatures` uses to assign `dualF`. So `dualPredOnLattice`
factors as `P x ∧ latticeToFeatures … x = dualF`.

This grounds the paper's predicate-modifier semantics
([jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025] eq 39)
in the existing Harbour feature decomposition (the feature bundle above):
DUAL is *not* a separate primitive but the same conditions used to
classify a lattice element as `[−atomic, +minimal]`. -/
theorem dualPredOnLattice_eq_via_features {D : Type} [DecidableEq D]
    (join : D → D → D) (domain : List D)
    (P : D → Bool) (x : D) :
    dualPredOnLattice join domain P x = true ↔
    P x = true ∧ latticeToFeatures join domain x = dualF := by
  rw [dualPredOnLattice_iff]
  refine and_congr_right (fun _ => ?_)
  constructor
  · -- isMinimalNonAtom → latticeToFeatures = dualF
    intro hMin
    have hNotAtom : isAtom join domain x = false :=
      not_atom_of_isMinimalNonAtom join domain x hMin
    unfold latticeToFeatures
    simp [hNotAtom, hMin]
  · -- latticeToFeatures = dualF → isMinimalNonAtom
    intro hF
    unfold latticeToFeatures at hF
    by_cases ha : isAtom join domain x = true
    · simp [ha, singularF, dualF] at hF
    · simp only [ha] at hF
      by_cases hm : isMinimalNonAtom join domain x = true
      · exact hm
      · simp only [hm] at hF
        simp [pluralF, dualF] at hF

/-- On the 3-atom powerset, the dual reading of "is a non-atom"
selects the three pairs (3, 5, 6) and excludes the triple (7). -/
theorem ps3_dual_pairs_satisfy :
    dualPredOnLattice bitmaskJoin ps3Domain (fun _ => true) 3 = true ∧
    dualPredOnLattice bitmaskJoin ps3Domain (fun _ => true) 5 = true ∧
    dualPredOnLattice bitmaskJoin ps3Domain (fun _ => true) 6 = true := by
  decide

/-- Triples (≥3 atomic parts) fail the dual predicate. -/
theorem ps3_dual_triple_excluded :
    dualPredOnLattice bitmaskJoin ps3Domain (fun _ => true) 7 = false := by
  decide

end Number
