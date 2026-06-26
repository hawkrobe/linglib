import Mathlib.Data.Fintype.Powerset
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
(`phiKernelEquiv`, `Studies/Harbour2016.lean`). -/
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
⟨D, ⊔⟩. Number categories correspond to the lattice predicates of
`Features/Number/Interp.lean`:
- **singular** = domain-minimal elements (the atoms),
- **dual** = minimal non-atoms (`minimalNonAtomIn`),
- **plural** = the rest.

The containment `[+atomic] → [+minimal]` is a *theorem* of lattice
theory (`Number.singular_subset_minimal`), not a stipulation. On finite
carriers the predicates are decidable (instances in `Interp.lean`), so
every concrete classification below is kernel-checked by `decide`:
domains are `Finset (Fin n)` powerset lattices with join = union.
Minimality is domain-relative (`minimalIn (· ∈ domain)`), agreeing with
the global `Mereology.Atom` when the domain is downward closed
in `D⁺`. -/

section Lattice

variable {D : Type*} [SemilatticeSup D]

/-- The minimal non-atoms of `domain`: minimal among its non-minimal
    elements — the dual's region ([harbour-2014] `[−atomic, +minimal]`). -/
def minimalNonAtomIn (domain : D → Prop) : D → Prop :=
  minimalIn fun y => domain y ∧ ¬minimalIn domain y

/-- A minimal non-atom is not domain-minimal. -/
theorem not_minimalIn_of_minimalNonAtomIn {domain : D → Prop} {x : D}
    (h : minimalNonAtomIn domain x) : ¬minimalIn domain x := h.1.2

/-- A region is join-complete: every element is `[+additive]` in it —
    `Mereology.CUM` restricted to the region ([harbour-2014] (11),
    complement completeness). -/
def RegionAdditive (Q : D → Prop) : Prop := ∀ x, Q x → additiveIn Q x

variable [Fintype D] [DecidableEq D] [DecidableLE D]

instance {domain : D → Prop} [DecidablePred domain] (x : D) :
    Decidable (minimalNonAtomIn domain x) := by
  unfold minimalNonAtomIn
  infer_instance

instance {Q : D → Prop} [DecidablePred Q] :
    Decidable (RegionAdditive Q) := by
  unfold RegionAdditive
  infer_instance

/-- Classify a lattice element by position: domain-minimal → singular,
    minimal non-atom → dual, otherwise → plural. -/
def latticeToFeatures (domain : D → Prop) [DecidablePred domain]
    (x : D) : Features :=
  if minimalIn domain x then singularF
  else if minimalNonAtomIn domain x then dualF
  else pluralF

/-- Every branch of `latticeToFeatures` produces a well-formed bundle:
    `[+atomic] → [+minimal]` holds by construction. -/
theorem latticeToFeatures_wellFormed (domain : D → Prop)
    [DecidablePred domain] (x : D) :
    (latticeToFeatures domain x).WellFormed := by
  unfold latticeToFeatures
  split
  · exact singular_wellFormed
  · split
    · exact dual_wellFormed
    · exact plural_wellFormed

end Lattice

/-! ### Powerset lattice examples -/

/-- The 2-atom powerset domain: nonempty subsets of `Fin 2`. -/
private def ps2 (s : Finset (Fin 2)) : Prop := s.Nonempty

private instance : DecidablePred ps2 := fun s =>
  inferInstanceAs (Decidable s.Nonempty)

theorem ex_atom_is_singular :
    latticeToFeatures ps2 {0} = singularF := by decide
theorem ex_atom_is_singular' :
    latticeToFeatures ps2 {1} = singularF := by decide
theorem ex_pair_is_dual :
    latticeToFeatures ps2 {0, 1} = dualF := by decide

/-- The 3-atom powerset domain: nonempty subsets of `Fin 3`. Pairs are
    minimal non-atoms → dual; the triple is non-minimal → plural (the
    2-atom domain has a single non-atom and cannot show the split). -/
def ps3 (s : Finset (Fin 3)) : Prop := s.Nonempty

instance : DecidablePred ps3 := fun s =>
  inferInstanceAs (Decidable s.Nonempty)

theorem ps3_atom_is_singular :
    latticeToFeatures ps3 {0} = singularF := by decide
theorem ps3_pair_is_dual :
    latticeToFeatures ps3 {0, 1} = dualF := by decide
theorem ps3_pair_is_dual' :
    latticeToFeatures ps3 {0, 2} = dualF := by decide
theorem ps3_triple_is_plural :
    latticeToFeatures ps3 {0, 1, 2} = pluralF := by decide

/-! ### The additive feature
[harbour-2014]

`[±additive]` is the third number feature, characterizing
join-completeness within a lattice region (`Number.additiveIn`).
Applied to the non-atomic region, it separates:
- `[+additive]` = "abundance" (plural/greater plural) — join-complete
- `[−additive]` = "paucity" (paucal/greater paucal) — not join-complete

The boundary is fixed by sociosemantic convention, subject to:
- **Complement completeness** ((11)): the `[+additive]` subregion must
  be join-complete (`RegionAdditive`).
- **Fungibility** ((12)): the boundary must be permutation-invariant
  (horizontal cuts by cardinality, not identity of atoms) — which is why
  the regions below are defined by `Finset.card`.

**Connection to CUM**: `[+additive]` IS cumulativity restricted to a
subregion (`Number.additive_subregion_is_cum`). The link between number
and aspect/telicity ([harbour-2014] §4.4) runs through exactly this
connection: mass nouns satisfy `[+additive]` (cumulative), count nouns
`[−additive]` (quantized). -/

/-- With 3 atoms the entire non-atomic region is join-complete:
    `[±additive]` is vacuous — a paucal/plural split needs a richer
    lattice. -/
theorem ps3_nonAtoms_joinComplete :
    RegionAdditive (fun s : Finset (Fin 3) => 2 ≤ s.card) := by decide

/-- The "paucal" region of the 5-atom powerset (2–3 atoms) is NOT
    join-complete: {0,1} ⊔ {2,3} has four atoms and escapes the
    region. -/
theorem ps5_paucal_not_joinComplete :
    ¬ RegionAdditive
      (fun s : Finset (Fin 5) => 2 ≤ s.card ∧ s.card ≤ 3) := by decide

/-- The "plural" region (≥ 4 atoms) IS join-complete: joining two large
    sums stays large. Satisfies complement completeness
    ([harbour-2014] (11)). -/
theorem ps5_plural_joinComplete :
    RegionAdditive (fun s : Finset (Fin 5) => 4 ≤ s.card) := by decide

/-- The paucal/plural asymmetry: the `[+additive]` region is
    join-complete, the `[−additive]` region is not — the formal content
    of the approximative number distinction ([harbour-2014] §3). -/
theorem ps5_additive_asymmetry :
    RegionAdditive (fun s : Finset (Fin 5) => 4 ≤ s.card) ∧
    ¬ RegionAdditive
      (fun s : Finset (Fin 5) => 2 ≤ s.card ∧ s.card ≤ 3) :=
  ⟨ps5_plural_joinComplete, ps5_paucal_not_joinComplete⟩

/-! ### DUAL as predicate modifier
[jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025]

The paper proposes (eq 39 in §4.2.1, derived from Harbour features in §8
eq 98b) that the core concept DUAL has a predicate-modification
semantics:

  ⟦DUAL⟧ = λP.λx. P(x) ∧ |{y : atom(y) ∧ y ⊑ x}| = 2

In a join-semilattice, "exactly 2 atomic parts below x" coincides with
"x is a minimal non-atom" (`minimalNonAtomIn`). The bridge is therefore
a one-line composition: restrict P by the dual lattice predicate.

This connects the Harbour feature bundle `dualF = ⟨isAtomic := false,
isMinimal := true⟩` to the predicate modifier required by the paper's
Indirect Alternative analysis: *les deux* lexicalizes the predicate
modifier `dualPredOnLattice _ verres` ('cup'), which is what blocks
*tous les NP.dual*. See `Studies/JereticEtAl2025.lean`. -/

section DualPred

variable {D : Type*} [SemilatticeSup D]

/-- ⟦DUAL⟧ as a predicate modifier on a join-semilattice domain
    ([jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025] eq 39):
    `P x`, and `x` has exactly two atomic parts — i.e. is a minimal
    non-atom of the domain. -/
def dualPredOnLattice (domain P : D → Prop) (x : D) : Prop :=
  P x ∧ minimalNonAtomIn domain x

instance {domain P : D → Prop} [Fintype D] [DecidableEq D]
    [DecidableLE D] [DecidablePred domain] [DecidablePred P] (x : D) :
    Decidable (dualPredOnLattice domain P x) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `dualPredOnLattice P` refines `P`: the dual reading of `P` is a
    subset of `P`. -/
theorem dualPredOnLattice_refines {domain P : D → Prop} {x : D}
    (h : dualPredOnLattice domain P x) : P x := h.1

/-- **Bridge**: the dual lattice predicate IS the condition
    `latticeToFeatures` uses to assign `dualF`, so `dualPredOnLattice`
    factors as `P x ∧ latticeToFeatures … x = dualF`. DUAL is *not* a
    separate primitive but the same condition that classifies a lattice
    element as `[−atomic, +minimal]`
    ([jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025] eq 39). -/
theorem dualPredOnLattice_eq_via_features [Fintype D] [DecidableEq D]
    [DecidableLE D] (domain : D → Prop) [DecidablePred domain]
    (P : D → Prop) (x : D) :
    dualPredOnLattice domain P x ↔
      P x ∧ latticeToFeatures domain x = dualF := by
  unfold dualPredOnLattice latticeToFeatures
  refine and_congr_right fun _ => ?_
  constructor
  · intro hMin
    rw [if_neg (not_minimalIn_of_minimalNonAtomIn hMin), if_pos hMin]
  · intro hF
    by_cases hm : minimalNonAtomIn domain x
    · exact hm
    · exfalso
      by_cases ha : minimalIn domain x
      · rw [if_pos ha] at hF
        exact absurd hF (by decide)
      · rw [if_neg ha, if_neg hm] at hF
        exact absurd hF (by decide)

end DualPred

/-- On the 3-atom powerset, the dual reading of the trivial property
    selects the three pairs and excludes the triple. -/
theorem ps3_dual_pairs_satisfy :
    dualPredOnLattice ps3 (fun _ => True) {0, 1} ∧
    dualPredOnLattice ps3 (fun _ => True) {0, 2} ∧
    dualPredOnLattice ps3 (fun _ => True) {1, 2} := by decide

/-- Triples (≥ 3 atomic parts) fail the dual predicate. -/
theorem ps3_dual_triple_excluded :
    ¬ dualPredOnLattice ps3 (fun _ => True) ({0, 1, 2} : Finset (Fin 3))
    := by decide

end Number
