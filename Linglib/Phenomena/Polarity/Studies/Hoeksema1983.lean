import Mathlib.Order.Hom.BoundedLattice
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Order.Heyting.Hom
import Linglib.Core.Order.SetPreimage
import Linglib.Theories.Semantics.Entailment.AntiAdditivity
import Linglib.Theories.Semantics.Degree.Comparative
import Linglib.Core.Lexical.PolarityItem

/-!
# Hoeksema (1983): Negative Polarity and the Comparative
@cite{hoeksema-1983}

## The asymmetry

@cite{hoeksema-1983} (NLLT 1: 403–434) advances a Boolean-algebraic
account of comparatives that distinguishes two distinctly typed
*than*-arguments, each with a different polarity-environment signature.
The empirical hook is that English / Dutch comparatives sometimes
license NPIs and sometimes do not — the type distinction predicts which.

- **NP-comparative** `[Adj-er than NP]` (§3.6, Eq 22): the than-argument
  is a generalized quantifier; ⟦than NP⟧ : Set (Set U) → Set U is a
  *Boolean homomorphism*. By Fact 3 it is monotone *increasing* in its
  GQ argument, and (§3.6) **not a negative polarity environment**.
  Surface NPIs in "than NP" arise (by hypothesis) from a covert
  clausal source.

- **S-comparative** `[Adj-er than S]` (§3.8, Def 7): the than-clause
  ranges over degrees; ⟦than S⟧ : Set D → Set U is anti-additive but
  *not* a Boolean homomorphism, hence an NPI environment by Zwarts.

## Formalization

`npComparativeGQ` is mathlib's `CompleteLatticeHom.setPreimage` applied
to a *threshold function* `npThreshold μ y = {x | μ x < μ y}`. All
Boolean-algebra preservation properties — finite `∩`/`∪`/`ᶜ`/`⊤`/`⊥`
and arbitrary `sSup`/`sInf` (strengthening Hoeksema's finitary claim)
— are inherited from the bundled hom via the standard mathlib
`map_inf` / `map_sup` / `map_compl` / `map_top` / `map_bot` /
`OrderHomClass.mono` API. `BoundedLatticeHomClass.toBiheytingHomClass`
gives complement preservation for free on `BooleanAlgebra → BooleanAlgebra`
homs.

For the S-comparative we use `IsAntiAdditive` from
`Theories/Semantics/Entailment/AntiAdditivity.lean`, instantiated via
the generic `isAntiAdditive_forall_mem` lemma.

## Hoeksema's algebraic spine: Definitions 4–8 and Facts 1–4

The §3 algebraic content is formalized in five layers:
- **Definition 4** (`IsOrderingPreserving`): the abstract property
  `μ b < μ a ↔ a ∈ f Q_b`, where `Q_b = {X | b ∈ X}` is the principal
  ultrafilter at `b` (`principalUltrafilter`).
- **Definition 7/8** (`sComparative`): the S-comparative as a
  set-of-degrees operator (already covered above).
- **Fact 1** (`fact1_agree_on_atoms`): two `>`-preserving functions
  coincide on every principal ultrafilter — a one-line chain of the
  Definition 4 biconditionals.
- **Fact 2** (`fact2_unique_from_atoms`): a `CompleteLatticeHom` on
  `Set (Set Entity) → Set Entity` is determined by its values on the
  principal-ultrafilter generators `Q_b`. Combined with Fact 1, this
  gives `npComparativeGQ_uniqueness`: two `>`-preserving complete
  Boolean homs are equal.
- **Fact 3** (`npComparativeGQ_monotone`): every Boolean hom is
  monotone increasing — disqualifies the NP-comparative as a Ladusaw
  NPI environment.
- **Fact 4** (cited from `IsAntiAdditive.antitone` in
  `Theories/Semantics/Entailment/AntiAdditivity.lean`): every
  anti-additive function is antitone — hence the S-comparative
  qualifies as an NPI environment.
- **§3.9 NP↔S equivalence** (`npComparativeGQ_principal_eq_sComparative_singleton`):
  on principal ultrafilters / singleton degree sets, the two
  constructions deliver the same predicate.

## Registry connection

The licensing-context registry `Core/Lexical/PolarityItem.lean` records
this paper's central asymmetry as a structural invariant:
- `.comparativeNP` has signature `.mono` (Boolean hom is monotone, not DE)
- `.comparativeS` has signature `.antiAdd`

The `comparativeNP_signature_monotone` and
`comparativeS_signature_anti_additive` theorems below witness the
agreement between this study file's mathematical statements and the
registry's classification, by `rfl`.
-/

namespace Hoeksema1983

open Semantics.Entailment.AntiAdditivity
open Core.Lexical.PolarityItem (LicensingContext contextProperties)

variable {Entity : Type*} {D : Type*} [Preorder D]

/-! ## S-comparative as set-of-degrees (§3.8, Def 7) -/

/-- S-comparative on a set of degrees: `y ∈ sComparative μ Δ` iff `μ y`
    strictly exceeds every degree in `Δ`. The than-clause supplies a
    set of degrees `Δ` (typically existentially closed). -/
def sComparative (μ : Entity → D) (Δ : Set D) : Set Entity :=
  fun y => ∀ d ∈ Δ, d < μ y

/-- The S-comparative is anti-additive in its set-of-degrees argument:
    `sComparative μ (A ∪ B) = sComparative μ A ∩ sComparative μ B`.
    Source of NPI licensing in clausal *than*-comparatives. -/
theorem sComparative_isAntiAdditive (μ : Entity → D) :
    IsAntiAdditive (sComparative μ) :=
  isAntiAdditive_forall_mem (fun d y => d < μ y)

/-- Atomic specialization of the S-comparative: at the singleton
    `{μ b}`, membership reduces to the binary "taller than b" relation.
    This is the bridge between the Hoeksema set-theoretic schema and
    the everyday `μ b < μ a` reading. -/
theorem sComparative_atomic (μ : Entity → D) (a b : Entity) :
    a ∈ sComparative μ {μ b} ↔ μ b < μ a := by
  refine ⟨fun h => h (μ b) rfl, ?_⟩
  intro h d hd
  rw [Set.mem_singleton_iff] at hd
  rw [hd]
  exact h

/-! ## NP-comparative as Boolean homomorphism (§3.6, Eq 22) -/

/-- The threshold function underlying the NP-comparative: `npThreshold μ y`
    is the set of individuals `y` is taller than under measure `μ`. The
    NP-comparative GQ is the set-preimage operator induced by this
    function (`npComparativeGQ`); Hoeksema Fact 1 (uniqueness) is the
    injectivity of this assignment, supplied by
    `Core.Order.setPreimage_injective`. -/
def npThreshold (μ : Entity → D) (y : Entity) : Set Entity :=
  {x | μ x < μ y}

/-- @cite{hoeksema-1983} Eq (22): the NP-comparative as a function on
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

/-- @cite{hoeksema-1983} Fact 3: the GQ NP-comparative is monotone
    *increasing* in its GQ argument. Inherited from the bundled hom's
    `OrderHomClass`. -/
theorem npComparativeGQ_monotone (μ : Entity → D) :
    Monotone (npComparativeGQ μ) :=
  OrderHomClass.mono _

/-- @cite{hoeksema-1983} Eq (22), complement clause: complement
    preservation on the NP-comparative GQ, via mathlib's automatic
    `BiheytingHomClass` instance for `BooleanAlgebra → BooleanAlgebra`
    `BoundedLatticeHom`s. -/
theorem npComparativeGQ_map_compl (μ : Entity → D) (Q : Set (Set Entity)) :
    npComparativeGQ μ Qᶜ = (npComparativeGQ μ Q)ᶜ :=
  map_compl (npComparativeGQ μ) Q

/-- @cite{hoeksema-1983} §3.6: the NP-comparative is *not* downward-
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
    Adjacent to but not literally @cite{hoeksema-1983} Fact 1 (which is
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

    @cite{hoeksema-1983} Definition 4 isolates the abstract property
    that distinguishes a comparative GQ-to-predicate operator from an
    arbitrary one. The principal ultrafilter `Q_b = {X | b ∈ X}` is the
    GQ denotation of the proper name `b`; `f` *preserves* `>` iff for
    every pair `a, b`, `μ b < μ a` is equivalent to `a ∈ f Q_b`
    (`f Q_b ∈ Q_a` in Hoeksema's exact phrasing). -/

/-- The principal ultrafilter at an individual: the GQ denotation of a
    proper name `b`. Hoeksema's `Q_b`. -/
def principalUltrafilter (b : Entity) : Set (Set Entity) := {X | b ∈ X}

/-- @cite{hoeksema-1983} Definition 4: `f` *preserves* `>` iff for every
    pair `a, b`, `μ b < μ a ↔ a ∈ f Q_b`. -/
def IsOrderingPreserving (μ : Entity → D)
    (f : Set (Set Entity) → Set Entity) : Prop :=
  ∀ a b : Entity, μ b < μ a ↔ a ∈ f (principalUltrafilter b)

/-- The NP-comparative GQ preserves `>` in the sense of @cite{hoeksema-1983}
    Definition 4. Combined with `npComparativeGQ_monotone` (Fact 3), this
    is the precise sense in which `[[Adj-er than]]` is *the* GQ-level
    comparative operator. -/
theorem npComparativeGQ_preserves_ordering (μ : Entity → D) :
    IsOrderingPreserving μ (npComparativeGQ μ) := by
  intro a b
  show μ b < μ a ↔ a ∈ (npComparativeGQ μ) (principalUltrafilter b)
  unfold npComparativeGQ principalUltrafilter npThreshold
  simp only [CompleteLatticeHom.coe_setPreimage, Set.mem_preimage, Set.mem_setOf_eq]

/-! ## Fact 1: any two `>`-preserving functions agree on every atom -/

/-- @cite{hoeksema-1983} Fact 1: any two functions on quantifiers that
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
    which is the intersection of `Q_a` for `a ∈ Y` and `Q_aᶜ` for `a ∉ Y`.
    The hom commutes with `iSup`, `iInf`, `inf`, and `compl`. -/

/-- Atom representation of a singleton in `Set (Set Entity)`:
    `{X} = (⋂_{a ∈ X} Q_a) ∩ (⋂_{a ∉ X} Q_aᶜ)`. -/
theorem singleton_eq_atomic_intersection (X : Set Entity) :
    ({X} : Set (Set Entity)) =
      (⋂ a ∈ X, principalUltrafilter a) ∩ (⋂ a ∉ X, (principalUltrafilter a)ᶜ) := by
  ext Y
  simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
             Set.mem_compl_iff, principalUltrafilter, Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rintro rfl; exact ⟨fun _ ha => ha, fun _ ha => ha⟩
  · rintro ⟨h1, h2⟩
    ext a
    exact ⟨fun hY => by_contra fun hX => h2 a hX hY, fun hX => h1 a hX⟩

/-- Any `Q : Set (Set Entity)` is the union of its singleton members. -/
theorem set_eq_iUnion_singletons (Q : Set (Set Entity)) :
    Q = ⋃ Y ∈ Q, ({Y} : Set (Set Entity)) := by
  ext; simp

/-- @cite{hoeksema-1983} Fact 2: a `CompleteLatticeHom` on
    `Set (Set Entity) → Set Entity` is determined by its values on the
    principal-ultrafilter generators `Q_b`. The proof composes
    `set_eq_iUnion_singletons` (every `Q` is a sup of singletons),
    `singleton_eq_atomic_intersection` (every singleton is an atomic
    inf of `Q_a`'s and `Q_aᶜ`'s), and the standard mathlib hom
    morphism API (`map_iSup₂`, `map_iInf₂`, `map_inf`, `map_compl`). -/
theorem fact2_unique_from_atoms
    (f g : CompleteLatticeHom (Set (Set Entity)) (Set Entity))
    (hagree : ∀ b : Entity, f (principalUltrafilter b) = g (principalUltrafilter b)) :
    f = g := by
  suffices h_singletons : ∀ Y : Set Entity, f {Y} = g {Y} by
    apply DFunLike.ext
    intro Q
    rw [set_eq_iUnion_singletons Q]
    rw [show (⋃ Y ∈ Q, ({Y} : Set (Set Entity))) = ⨆ Y ∈ Q, ({Y} : Set (Set Entity)) from rfl]
    rw [map_iSup₂ f, map_iSup₂ g]
    exact iSup_congr (fun Y => iSup_congr (fun _ => h_singletons Y))
  intro Y
  rw [singleton_eq_atomic_intersection]
  rw [show ((⋂ a ∈ Y, principalUltrafilter a) ∩ (⋂ a ∉ Y, (principalUltrafilter a)ᶜ))
        = ((⨅ a ∈ Y, principalUltrafilter a) ⊓ (⨅ a ∉ Y, (principalUltrafilter a)ᶜ)) from rfl]
  rw [map_inf f, map_inf g]
  rw [map_iInf₂ f, map_iInf₂ g, map_iInf₂ f, map_iInf₂ g]
  congr 1
  · exact iInf_congr (fun a => iInf_congr (fun _ => hagree a))
  · refine iInf_congr (fun a => iInf_congr (fun _ => ?_))
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

/-- @cite{hoeksema-1983} §3.9 (Eq. 44): the NP-comparative applied to a
    principal ultrafilter `Q_b` (the GQ denotation of a proper name)
    coincides with the S-comparative applied to the singleton degree
    set `{μ b}`. Both reduce to "is taller than `b`" — explaining the
    empirical equivalence of "I am bigger than you" (NP-form) and
    "I am bigger than you are" (S-form), Hoeksema's Eq. 44a–b. -/
theorem npComparativeGQ_principal_eq_sComparative_singleton
    (μ : Entity → D) (b : Entity) :
    npComparativeGQ μ (principalUltrafilter b) = sComparative μ {μ b} := by
  ext a
  unfold npComparativeGQ principalUltrafilter sComparative npThreshold
  simp only [CompleteLatticeHom.coe_setPreimage, Set.mem_preimage,
             Set.mem_setOf_eq, Set.mem_singleton_iff]
  refine ⟨fun h d hd => hd ▸ h, fun h => h (μ b) rfl⟩

/-! ## Bridge to the framework-independent comparative

    `Theories/Semantics/Degree/Comparative.lean` defines the binary
    `comparativeSem μ a b .positive ↔ μ a > μ b` for a `LinearOrder D`.
    The atomic S-comparative agrees with this binary form pointwise —
    the Hoeksema set-theoretic schema is a strict generalization. -/

/-- The atomic S-comparative coincides with the framework-independent
    binary comparative on a `LinearOrder`. The bridge is stated outside
    the `[Preorder D]` block to avoid an instance clash with the
    `LinearOrder → Preorder` derivation. -/
theorem sComparative_atomic_eq_comparativeSem
    {Entity D : Type*} [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    a ∈ sComparative μ {μ b} ↔
      Semantics.Degree.Comparative.comparativeSem μ a b .positive :=
  sComparative_atomic μ a b

/-! ## Connection to the licensing-context registry -/

/-- The `.comparativeNP` registry slot is monotone, matching
    `npComparativeGQ_monotone`. This is the registry-level encoding of
    Hoeksema's central asymmetry: the NP-comparative is monotone
    *increasing* and therefore not an NPI environment. -/
theorem comparativeNP_signature_monotone :
    (contextProperties .comparativeNP).signature = .mono := rfl

/-- The `.comparativeS` registry slot is anti-additive, matching
    `sComparative_isAntiAdditive`. -/
theorem comparativeS_signature_anti_additive :
    (contextProperties .comparativeS).signature = .antiAdd := rfl

/-- Both registry slots cite Hoeksema 1983, anchoring the registry's
    classification to this study file. -/
theorem both_comparatives_cite_hoeksema :
    "hoeksema-1983" ∈ (contextProperties .comparativeNP).citations ∧
    "hoeksema-1983" ∈ (contextProperties .comparativeS).citations := by
  refine ⟨?_, ?_⟩ <;> decide

end Hoeksema1983
