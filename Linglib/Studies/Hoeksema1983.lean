import Mathlib.Order.Hom.BoundedLattice
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Order.Heyting.Hom
import Linglib.Core.Order.SetPreimage
import Linglib.Logic.Natural.Additivity
import Linglib.Semantics.Degree.Quantifier

/-!
# Hoeksema (1983): Negative Polarity and the Comparative

This file formalizes the Boolean-algebraic account of [hoeksema-1983] of the two comparatives.
The NP-comparative *Adj-er than NP* takes a generalized quantifier and is the Boolean
homomorphism of (22), here the preimage hom `npComparativeGQ` of the threshold function
`npThreshold`; as a homomorphism it is monotone increasing (Fact 3), so it is not a negative
polarity environment, and it is the only ordering-preserving homomorphism in the sense of
Definition 4 (`npComparativeGQ_uniqueness`, Facts 1 and 2). The S-comparative *Adj-er than S*
takes a set of degrees, `Degree.Comparison.gt.overSet` of Definition 7, and is anti-additive
(Fact 4, in the substrate) without being a homomorphism, which makes it a negative polarity
environment. On a proper name and the singleton of its degree the two coincide
(`npComparativeGQ_principal_eq_gtOverSet_singleton`, §3.9).

## Implementation notes

* The homomorphism preserves arbitrary suprema and infima, `CompleteLatticeHom`, where the
  paper states finite preservation; Fact 2 is proved for complete lattice homomorphisms from
  the atom decomposition of a set of sets.

## References

* [hoeksema-1983]
* [ladusaw-1979]
* [zwarts-1998]
-/

namespace Hoeksema1983

open Degree

variable {Entity : Type*} {D : Type*} [Preorder D]

/-! ## NP-comparative as Boolean homomorphism (§3.6, Eq 22) -/

/-- The threshold function underlying the NP-comparative: `npThreshold μ y`
    is the set of individuals `y` is taller than under measure `μ`. The
    NP-comparative GQ is the set-preimage operator induced by this
    function (`npComparativeGQ`); Hoeksema Fact 1 (uniqueness) is the
    injectivity of this assignment, supplied by
    `Core.Order.setPreimage_injective`. -/
def npThreshold (μ : Entity → D) (y : Entity) : Set Entity :=
  {x | μ x < μ y}

/-- [hoeksema-1983] Eq (22): the NP-comparative as a function on
    generalized quantifiers, packaged as the bundled mathlib
    `CompleteLatticeHom.setPreimage (npThreshold μ)`.

    `npComparativeGQ μ Q y` holds iff the property "is shorter than y"
    (`npThreshold μ y`) is one of the properties picked out by the GQ
    `Q`. All Boolean-algebra preservation properties — finite
    `∩`/`∪`/`ᶜ`/`⊤`/`⊥` and arbitrary `sSup`/`sInf` (stronger than
    Hoeksema's finitary statement) — are inherited from the bundled
    hom via the standard mathlib `map_*` API. -/
def npComparativeGQ (μ : Entity → D) :
    CompleteLatticeHom (Set (Set Entity)) (Set Entity) :=
  CompleteLatticeHom.setPreimage (npThreshold μ)

/-! ## Hoeksema Fact 3: monotonicity, and the §3.6 corollary -/

/-- [hoeksema-1983] Fact 3: the GQ NP-comparative is monotone
    *increasing* in its GQ argument. Inherited from the bundled hom's
    `OrderHomClass`. -/
theorem npComparativeGQ_monotone (μ : Entity → D) :
    Monotone (npComparativeGQ μ) :=
  OrderHomClass.mono _

/-- [hoeksema-1983] Eq (22), complement clause: complement
    preservation on the NP-comparative GQ, via mathlib's automatic
    `BiheytingHomClass` instance for `BooleanAlgebra → BooleanAlgebra`
    `BoundedLatticeHom`s. -/
theorem npComparativeGQ_map_compl (μ : Entity → D) (Q : Set (Set Entity)) :
    npComparativeGQ μ Qᶜ = (npComparativeGQ μ Q)ᶜ :=
  map_compl (npComparativeGQ μ) Q

/-- [hoeksema-1983] §3.6: the NP-comparative is *not* downward-
    entailing on any nontrivial domain. We state the contrapositive: if
    the GQ NP-comparative were antitone, then for `Q ⊆ Q'` it would map
    to `npComparativeGQ μ Q' ⊆ npComparativeGQ μ Q` — combined with the
    Fact 3 monotonicity going the other way, it would force equality on
    every comparable pair. This is the formal content of "monotone
    increasing ≠ downward-entailing", which is what disqualifies
    NP-comparative as an NPI environment under Ladusaw monotonicity. -/
theorem npComparativeGQ_antitone_iff_constant_on_chains (μ : Entity → D) :
    Antitone (npComparativeGQ μ) ↔
      ∀ Q₁ Q₂ : Set (Set Entity), Q₁ ⊆ Q₂ →
        npComparativeGQ μ Q₁ = npComparativeGQ μ Q₂ := by
  constructor
  · intro hAnti Q₁ Q₂ hsub
    exact le_antisymm (npComparativeGQ_monotone μ hsub) (hAnti hsub)
  · intro hConst Q₁ Q₂ hsub
    exact (hConst Q₁ Q₂ hsub).ge

/-! ## Threshold uniqueness for the NP-comparative GQ

    A specialization of the Hoeksema atom-uniqueness story to the
    `npComparativeGQ` family: distinct measures induce distinct GQs.
    Adjacent to but not literally [hoeksema-1983] Fact 1 (which is
    stated for arbitrary `>`-preserving functions; see below). -/

/-- The NP-comparative GQ uniquely determines its underlying threshold
    function. Two scales `μ₁`, `μ₂` produce the same NP-comparative GQ
    iff they induce the same "things-y-is-taller-than" set for every
    `y`. Proof by atom-decomposition (probe at singletons), packaged
    as `Core.Order.setPreimage_injective`. -/
theorem npComparativeGQ_injective_in_threshold {μ₁ μ₂ : Entity → D} :
    npComparativeGQ μ₁ = npComparativeGQ μ₂ ↔ npThreshold μ₁ = npThreshold μ₂ := by
  constructor
  · intro h
    unfold npComparativeGQ at h
    exact Core.Order.setPreimage_injective h
  · intro h
    unfold npComparativeGQ
    rw [h]

/-! ## Definition 4: `>`-preserving functions on quantifiers

    [hoeksema-1983] Definition 4 isolates the abstract property
    that distinguishes a comparative GQ-to-predicate operator from an
    arbitrary one. The principal ultrafilter `Q_b = {X | b ∈ X}` is the
    GQ denotation of the proper name `b`; `f` *preserves* `>` iff for
    every pair `a, b`, `μ b < μ a` is equivalent to `a ∈ f Q_b`
    (`f Q_b ∈ Q_a` in Hoeksema's exact phrasing). -/

/-- The principal ultrafilter at an individual: the GQ denotation of a
    proper name `b`. Hoeksema's `Q_b`. -/
def principalUltrafilter (b : Entity) : Set (Set Entity) := {X | b ∈ X}

/-- [hoeksema-1983] Definition 4: `f` *preserves* `>` iff for every
    pair `a, b`, `μ b < μ a ↔ a ∈ f Q_b`. -/
def IsOrderingPreserving (μ : Entity → D)
    (f : Set (Set Entity) → Set Entity) : Prop :=
  ∀ a b : Entity, μ b < μ a ↔ a ∈ f (principalUltrafilter b)

/-- The NP-comparative GQ preserves `>` in the sense of [hoeksema-1983]
    Definition 4. Combined with `npComparativeGQ_monotone` (Fact 3), this
    is the precise sense in which `[[Adj-er than]]` is *the* GQ-level
    comparative operator. -/
theorem npComparativeGQ_preserves_ordering (μ : Entity → D) :
    IsOrderingPreserving μ (npComparativeGQ μ) := by
  intro a b
  show μ b < μ a ↔ a ∈ (npComparativeGQ μ) (principalUltrafilter b)
  unfold npComparativeGQ principalUltrafilter npThreshold
  simp only [CompleteLatticeHom.coe_setPreimage, Set.mem_preimage, Set.mem_ofPred_eq]

/-! ## Fact 1: any two `>`-preserving functions agree on every atom -/

/-- [hoeksema-1983] Fact 1: any two functions on quantifiers that
    both preserve `>` (Definition 4) coincide on every principal
    ultrafilter `Q_b`. The proof is a direct chain of the two
    `IsOrderingPreserving` biconditionals — both sides reduce to
    `μ b < μ a`. -/
theorem fact1_agree_on_atoms {μ : Entity → D}
    {f g : Set (Set Entity) → Set Entity}
    (hf : IsOrderingPreserving μ f) (hg : IsOrderingPreserving μ g) :
    ∀ b : Entity, f (principalUltrafilter b) = g (principalUltrafilter b) := by
  intro b
  ext a
  exact (hf a b).symm.trans (hg a b)

/-! ## Fact 2: Boolean-hom uniqueness from agreement on principal ultrafilters

    Hoeksema's Fact 2 strengthens Fact 1: two complete-lattice Boolean
    homomorphisms on `Set (Set Entity) → Set Entity` that agree on every
    principal ultrafilter `Q_b` are equal. The proof reduces every
    `Q : Set (Set Entity)` to the `iSup` of its singleton members, each of
    which is the `iInf` of `Q_a` for `a ∈ Y` and `Q_aᶜ` for `a ∉ Y`.
    The hom commutes with `iSup`, `iInf`, `inf`, and `compl`.

    The two bridge lemmas (`singleton_eq_iInf_principalUltrafilter`,
    `eq_iSup_singletons`) state the atom representation directly with
    `⨅`/`⨆` so the consumer (`fact2_unique_from_atoms`) chains with
    `map_iInf₂` / `map_iSup₂` without any `⋂ → ⨅` bridging step. -/

/-- Atom representation of a singleton in `Set (Set Entity)`:
    `{X} = (⨅_{a ∈ X} Q_a) ⊓ (⨅_{a ∉ X} Q_aᶜ)`. Stated with `⨅`/`⊓`
    rather than `⋂`/`∩` so that consumers chain directly with
    `map_iInf₂` / `map_inf`. -/
theorem singleton_eq_iInf_principalUltrafilter (X : Set Entity) :
    ({X} : Set (Set Entity)) =
      (⨅ a ∈ X, principalUltrafilter a) ⊓ (⨅ a ∉ X, (principalUltrafilter a)ᶜ) := by
  ext Y
  simp only [Set.mem_singleton_iff, Set.inf_eq_inter, Set.mem_inter_iff,
             Set.iInf_eq_iInter, Set.mem_iInter,
             Set.mem_compl_iff, principalUltrafilter, Set.mem_ofPred_eq]
  refine ⟨?_, ?_⟩
  · rintro rfl; exact ⟨λ _ ha => ha, λ _ ha => ha⟩
  · rintro ⟨h1, h2⟩
    ext a
    exact ⟨λ hY => by_contra λ hX => h2 a hX hY, λ hX => h1 a hX⟩

/-- Any `Q : Set (Set Entity)` is the `⨆` of its singleton members.
    Stated with `⨆` rather than `⋃` so that the consumer
    (`fact2_unique_from_atoms`) chains directly with `map_iSup₂`. -/
theorem eq_iSup_singletons (Q : Set (Set Entity)) :
    Q = ⨆ Y ∈ Q, ({Y} : Set (Set Entity)) := by
  ext Y
  simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, Set.mem_singleton_iff,
             exists_prop, exists_eq_right']

/-- [hoeksema-1983] Fact 2: a `CompleteLatticeHom` on
    `Set (Set Entity) → Set Entity` is determined by its values on the
    principal-ultrafilter generators `Q_b`. The proof composes
    `eq_iSup_singletons` (every `Q` is a `⨆` of singletons),
    `singleton_eq_iInf_principalUltrafilter` (every singleton is an
    atomic `⨅` of `Q_a`'s and `Q_aᶜ`'s), and the standard mathlib hom
    API (`map_iSup₂`, `map_iInf₂`, `map_inf`, `map_compl`).

    The mathematical content — "a `CompleteLatticeHom` on
    `Set (Set α) → Set α` is determined by its values on principal-set
    generators" — is generic and would PR cleanly to
    `Mathlib/Order/Hom/CompleteLattice.lean` as a strengthening of the
    existing pointwise `@[ext]` lemma. -/
theorem fact2_unique_from_atoms
    (f g : CompleteLatticeHom (Set (Set Entity)) (Set Entity))
    (hagree : ∀ b : Entity, f (principalUltrafilter b) = g (principalUltrafilter b)) :
    f = g := by
  suffices h_singletons : ∀ Y : Set Entity, f {Y} = g {Y} by
    apply DFunLike.ext
    intro Q
    rw [eq_iSup_singletons Q, map_iSup₂ f, map_iSup₂ g]
    exact iSup_congr λ Y => iSup_congr λ _ => h_singletons Y
  intro Y
  rw [singleton_eq_iInf_principalUltrafilter, map_inf f, map_inf g,
      map_iInf₂ f, map_iInf₂ g, map_iInf₂ f, map_iInf₂ g]
  congr 1
  · exact iInf_congr λ a => iInf_congr λ _ => hagree a
  · refine iInf_congr λ a => iInf_congr λ _ => ?_
    rw [map_compl, map_compl, hagree a]

/-- Combining Fact 1 and Fact 2: two `>`-preserving complete-lattice
    homomorphisms (Definition 4) on `Set (Set Entity) → Set Entity` are
    equal. Hoeksema's strongest uniqueness statement: the threshold
    function determines the comparative GQ entirely. -/
theorem npComparativeGQ_uniqueness {μ : Entity → D}
    (f g : CompleteLatticeHom (Set (Set Entity)) (Set Entity))
    (hf : IsOrderingPreserving μ f) (hg : IsOrderingPreserving μ g) :
    f = g :=
  fact2_unique_from_atoms f g (fact1_agree_on_atoms hf hg)

/-! ## §3.9: NP-comparative on principal ultrafilter ≡ S-comparative on singleton -/

/-- [hoeksema-1983] §3.9 (Eq. 44): the NP-comparative applied to a
    principal ultrafilter `Q_b` (the GQ denotation of a proper name)
    coincides with the S-comparative applied to the singleton degree
    set `{μ b}`. Both reduce to "is taller than `b`" — explaining the
    empirical equivalence of "I am bigger than you" (NP-form) and
    "I am bigger than you are" (S-form), Hoeksema's Eq. 44a–b. -/
theorem npComparativeGQ_principal_eq_gtOverSet_singleton
    (μ : Entity → D) (b : Entity) :
    npComparativeGQ μ (principalUltrafilter b) = Comparison.gt.overSet μ {μ b} := by
  ext a
  unfold npComparativeGQ principalUltrafilter npThreshold
  simp only [CompleteLatticeHom.coe_setPreimage, Set.mem_preimage, Set.mem_ofPred_eq,
             Comparison.overSet_singleton, Comparison.mem_over, Comparison.rel, gt_iff_lt]

end Hoeksema1983
