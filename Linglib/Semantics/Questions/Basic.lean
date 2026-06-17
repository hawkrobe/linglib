import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.SetLike.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.UpperLower.Basic
import Linglib.Semantics.Questions.Support

/-!
# Question — core type, lattice, Heyting derivatives
[ciardelli-groenendijk-roelofsen-2018] [puncochar-2016]
[puncochar-2019] [theiler-etal-2018]

A bundled `Question W` — a non-empty downward-closed family of information
states over `W` (where an information state is a subset of `W`). This is
mathematically a non-empty `LowerSet (Set W)`; in linguistic terms it is
the umbrella structure for question-flavored content: it subsumes
Hamblin alternative sets (`polar`, `which`), partition-style questions
(via `Semantics/Mood/PartitionAsInquiry.lean`), and the inquisitive
propositions of [ciardelli-groenendijk-roelofsen-2018]. The name
"Question" follows the decision-theoretic / discourse-semantic tradition
(van Rooij, Westera) — neutral as to whether the consumer is doing
inquisitive theorizing.

This `Basic` file carries the structural core: the type definition with
its `SetLike` instance, the `info`/`alt`/`isInformative`/`isInquisitive`/
`isDeclarative` predicates, the `declarative` constructor, the algebraic
operations (`conj`, `inqDisj`, `top`, `bot`) packaged into the
`CompleteDistribLattice` instance, the basic `info`-on-lattice-operations
API, the `alt`-as-maximal characterization, the existence of alternatives
under finiteness, the **Resolutions Theorem** (DNF), the
**principal-ideal characterization** of declaratives, the Heyting
derivatives (`compl_eq`, `proj`, `nonInfo`, the division law), and the
LEM-fails witness.

For Hamblin constructions (`polar`, `which`), see
`Core/Question/Hamblin.lean`. For partial-answerhood and Roberts
QUD-relevance predicates, see `Core/Question/Relevance.lean`. For
the `Setoid → Question` embedding (used by `POSWQ`), see
`Semantics/Mood/PartitionAsInquiry.lean`.

## Mathlib alignment

- `props : Set (Set W)` — sets of subsets of `W`, mathlib-native
- `contains_empty` is logically equivalent to `Nonempty props` together
  with downward closure — we expose it as the field directly because
  it's the only constraint that matters once downward closure holds
- `info` returns `Set W` (mathlib-native), not `W → Bool`
- `SetLike (Question W) (Set W)` — auto-derives `Membership`,
  `CoeSort`, and the `ext` machinery. `mem_props` is the canonical
  simp normalization (`q ∈ P.props → q ∈ P`).
- `CompleteDistribLattice (Question W)` — registered via
  `CompleteDistribLattice.ofMinimalAxioms` from two pointwise
  inequalities, giving `Frame`, `Coframe`, `HeytingAlgebra`, and
  `BiheytingAlgebra` for free. Mirrors `Filter`'s registration pattern.

### Why a bundled structure rather than `LowerSet (Set W)`?

A downward-closed family of propositions on `W` is, abstractly, a
`LowerSet (Set W)`. We considered registering `Question`
as a `LowerSet` synonym, but rejected it because the `⊥` elements
disagree: `LowerSet.⊥ = ∅` (no resolving propositions), while ours is
`{∅}` (only the inconsistent state resolves). The non-emptiness
constraint (`contains_empty`) is essential to inquisitive semantics
and is lost in `LowerSet`. We use `SetLike` instead, which gives the
membership/coercion API without forcing `LowerSet`'s `⊥`.
-/


universe u

/-- An inquisitive proposition in the sense of
    [ciardelli-groenendijk-roelofsen-2018]: a non-empty
    downward-closed family of information states over `W`. The states in
    `props` are the ones that *resolve* the issue raised by the sentence. -/
structure Question (W : Type u) where
  /-- The set of propositions resolving the issue. -/
  props : Set (Set W)
  /-- Contains the empty proposition (= the inconsistent information
      state). Equivalent to non-emptiness given downward closure. -/
  contains_empty : ∅ ∈ props
  /-- Downward closed: if `p` resolves the issue and `q ⊆ p`, then `q`
      also resolves it (any sufficient evidence is also sufficient when
      strengthened). -/
  downward_closed : ∀ p ∈ props, ∀ q : Set W, q ⊆ p → q ∈ props

namespace Question

variable {W : Type u}

/-- `SetLike` instance: an `Question W` coerces to its underlying
    `Set (Set W)` of resolving propositions. Auto-derives `Membership`
    (`q ∈ P` means `q ∈ P.props`), `CoeSort`, and the standard `ext`
    machinery. Mirrors mathlib's pattern for `Submonoid`, `Subgroup`,
    `LowerSet`, etc. -/
instance : SetLike (Question W) (Set W) where
  coe := props
  coe_injective P Q h := by cases P; cases Q; congr

/-- Membership normalization: `q ∈ P.props` rewrites to `q ∈ P`. Mirrors
    mathlib's `mem_carrier` pattern (`SetLike.Basic` line 92). -/
@[simp] theorem mem_props {P : Question W} {q : Set W} :
    q ∈ P.props ↔ q ∈ P := Iff.rfl

@[simp, norm_cast] theorem coe_mk (s : Set (Set W)) (h₁ h₂) :
    ((⟨s, h₁, h₂⟩ : Question W) : Set (Set W)) = s := rfl

/-- Two `Question`s are equal when their `props` agree. -/
@[ext]
theorem ext {P Q : Question W} (h : ∀ q, q ∈ P ↔ q ∈ Q) : P = Q :=
  SetLike.ext h

/-- The **alternatives** of an inquisitive content
    ([ciardelli-groenendijk-roelofsen-2018]): the maximal
    propositions in `props`. These are the "answers" — the strongest
    information states that resolve the issue. -/
def alt (P : Question W) : Set (Set W) :=
  {p ∈ P.props | ∀ q ∈ P.props, p ⊆ q → p = q}

/-- The **informative content** of an inquisitive content
    ([ciardelli-groenendijk-roelofsen-2018]): the union of all
    propositions in `props`. The information any utterance with this
    meaning provides — the actual world must lie in `info P`. -/
def info (P : Question W) : Set W :=
  ⋃₀ P.props

/-- A sentence is **informative** iff its informative content excludes
    at least one possible world. -/
def isInformative (P : Question W) : Prop :=
  info P ≠ Set.univ

/-- A sentence is **inquisitive** iff resolving the issue it raises
    requires more than the information it provides — equivalently, iff
    `info P` itself is not in `props` (so no single proposition in
    `props` covers all of `info P`). -/
def isInquisitive (P : Question W) : Prop :=
  info P ∉ P.props

/-- A sentence is **declarative** iff it is not inquisitive —
    equivalently, iff `info P ∈ props`. Algebraic characterization
    ([puncochar-2019]): `props` is a principal ideal in the algebra
    of information states; see `isDeclarative_iff_eq_declarative_info`. -/
def isDeclarative (P : Question W) : Prop :=
  info P ∈ P.props

/-- Declarative and inquisitive are exact negations of each other. -/
theorem isDeclarative_iff_not_isInquisitive (P : Question W) :
    P.isDeclarative ↔ ¬ P.isInquisitive :=
  not_not.symm

/-! ### Constructors -/

/-- Smart constructor from a lower (downward-closed) family of
    information states containing `∅`. Packages the two `Question`
    obligations in mathlib's `IsLowerSet` vocabulary, so a caller holding
    a persistence proof (`IsLowerSet`) and an empty-state witness builds
    the `Question` directly instead of re-deriving `downward_closed`
    inline. -/
def ofLowerSet (s : Set (Set W)) (empty_mem : ∅ ∈ s) (lower : IsLowerSet s) :
    Question W where
  props := s
  contains_empty := empty_mem
  downward_closed := fun _p hp _q hq => lower hq hp

@[simp] theorem props_ofLowerSet (s : Set (Set W)) (empty_mem : ∅ ∈ s)
    (lower : IsLowerSet s) : (ofLowerSet s empty_mem lower).props = s := rfl

@[simp] theorem mem_ofLowerSet {s : Set (Set W)} {empty_mem : ∅ ∈ s}
    {lower : IsLowerSet s} {q : Set W} :
    q ∈ ofLowerSet s empty_mem lower ↔ q ∈ s := Iff.rfl

/-- The **declarative** content of a proposition `p`: the principal
    ideal `{q | q ⊆ p}`. Single alternative `p`; non-inquisitive;
    informative iff `p ≠ univ`. -/
def declarative (p : Set W) : Question W where
  props := {q | q ⊆ p}
  contains_empty := Set.empty_subset p
  downward_closed := fun _ hq _ hr => hr.trans hq

/-! ### Basic theorems on declarative -/

@[simp] theorem mem_declarative {p q : Set W} :
    q ∈ declarative p ↔ q ⊆ p := Iff.rfl

@[simp] theorem info_declarative (p : Set W) : (declarative p).info = p := by
  ext w
  simp only [info, declarative, Set.mem_sUnion, Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨q, hq, hwq⟩; exact hq hwq
  · intro hw; exact ⟨p, Set.Subset.refl p, hw⟩

theorem isDeclarative_declarative (p : Set W) :
    (declarative p).isDeclarative := by
  show (declarative p).info ∈ declarative p
  rw [info_declarative]
  exact Set.Subset.refl p

theorem not_isInquisitive_declarative (p : Set W) :
    ¬ (declarative p).isInquisitive :=
  fun h => h (isDeclarative_declarative p)

/-! ### Algebraic operations ([puncochar-2019] §2)

Following the support-clause definitions in [puncochar-2019] §2:
conjunction is `||α ∧ β|| = ||α|| ∩ ||β||` (state supports `α ∧ β` iff
it supports both); inquisitive disjunction is `||α ⩒ β|| = ||α|| ∪ ||β||`
(state supports `α ⩒ β` iff it supports either).

Implication `→` and negation `¬` arise as the Heyting `⇨` and `ᶜ` of
the `CompleteDistribLattice` structure registered below; see the
"Heyting derivatives" section for the structural identity
`Pᶜ = declarative (info P)ᶜ` and the derivatives it grounds. -/

/-- **Inquisitive conjunction** `P ∧ Q` ([puncochar-2019] §2 ∧
    clause): `props` is the pointwise intersection. A state resolves
    `P ∧ Q` iff it resolves both `P` and `Q`. -/
def conj (P Q : Question W) : Question W where
  props := P.props ∩ Q.props
  contains_empty := ⟨P.contains_empty, Q.contains_empty⟩
  downward_closed := fun p hp q hq =>
    ⟨P.downward_closed p hp.1 q hq, Q.downward_closed p hp.2 q hq⟩

/-- **Inquisitive disjunction** `P ⩒ Q` ([puncochar-2019] §2 ⩒
    clause): `props` is the pointwise union. A state resolves
    `P ⩒ Q` iff it resolves `P` or `Q`. Distinct from classical
    disjunction `∨`, whose support clause involves splitting the state
    across two substates. -/
def inqDisj (P Q : Question W) : Question W where
  props := P.props ∪ Q.props
  contains_empty := Or.inl P.contains_empty
  downward_closed := fun p hp q hq => by
    rcases hp with hp | hp
    · exact Or.inl (P.downward_closed p hp q hq)
    · exact Or.inr (Q.downward_closed p hp q hq)

/-- The **top** inquisitive content: every set of worlds resolves the
    issue. The trivial inquiry that demands nothing. -/
def top : Question W where
  props := Set.univ
  contains_empty := Set.mem_univ _
  downward_closed := fun _ _ _ _ => Set.mem_univ _

/-- The **bottom** inquisitive content: only the inconsistent state
    (`∅`) resolves the issue. The unsatisfiable inquiry. -/
def bot : Question W where
  props := {∅}
  contains_empty := rfl
  downward_closed := fun p hp q hq => by
    rw [Set.mem_singleton_iff] at hp
    rw [hp] at hq
    rw [Set.mem_singleton_iff]
    exact Set.subset_empty_iff.mp hq

/-! ### Complete lattice structure

We package the algebraic operations into mathlib's order/lattice
typeclasses: the entailment order `P ≤ Q := P.props ⊆ Q.props` makes
`Question W` into a **bounded distributive complete lattice**
with `⊓ = conj`, `⊔ = inqDisj`, `⊥ = bot`, `⊤ = top`, plus arbitrary
suprema and infima.

`sSup S` is the union of all `props` fields (with `∅` adjoined so
`contains_empty` holds vacuously when `S = ∅`); `sInf S` is the
intersection (`= univ`, vacuously, when `S = ∅`, which gives `⊤`).
This gives access to the entire mathlib order/lattice API
(`inf_le_left`, `le_sup_right`, `inf_sup_right`, `iSup`, `iInf`,
`sSup_le_iff`, intervals, lattice homomorphisms, …).

Distributivity (binary) is free: it reduces to the standard set
distributivity on the underlying `Set (Set W)`, and falls out of the
`CompleteDistribLattice` registration below (no separate
`DistribLattice` instance needed). -/

/-- The arbitrary supremum: a state resolves `sSup S` iff it resolves
    some `P ∈ S` (or is the empty state, which always resolves). -/
def sSupContent (S : Set (Question W)) : Question W where
  props := {q | q = ∅ ∨ ∃ P ∈ S, q ∈ P.props}
  contains_empty := Or.inl rfl
  downward_closed := fun p hp q hq => by
    rcases hp with hempty | ⟨P, hPS, hpP⟩
    · left; rw [hempty] at hq; exact Set.subset_empty_iff.mp hq
    · exact Or.inr ⟨P, hPS, P.downward_closed p hpP q hq⟩

/-- The arbitrary infimum: a state resolves `sInf S` iff it resolves
    every `P ∈ S`. (When `S = ∅`, this is `Set.univ`, recovering `⊤`.) -/
def sInfContent (S : Set (Question W)) : Question W where
  props := {q | ∀ P ∈ S, q ∈ P.props}
  contains_empty := fun P _ => P.contains_empty
  downward_closed := fun p hp q hq P hPS => P.downward_closed p (hp P hPS) q hq

instance : SupSet (Question W) := ⟨sSupContent⟩
instance : InfSet (Question W) := ⟨sInfContent⟩

/-- The complete lattice structure on `Question W`. Provides
    `Lattice`, `BoundedOrder`, `SupSet`, `InfSet`, plus `iSup`/`iInf`
    for the entire mathlib API. -/
instance : CompleteLattice (Question W) where
  le P Q := P.props ⊆ Q.props
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm _ _ hpq hqp := SetLike.coe_injective (Set.Subset.antisymm hpq hqp)
  inf := conj
  sup := inqDisj
  top := top
  bot := bot
  inf_le_left _ _ _ hp := hp.1
  inf_le_right _ _ _ hp := hp.2
  le_inf _ _ _ hPQ hPR _ hp := ⟨hPQ hp, hPR hp⟩
  le_sup_left _ _ _ hp := Or.inl hp
  le_sup_right _ _ _ hp := Or.inr hp
  sup_le _ _ _ hPR hQR _ hp := by
    rcases hp with h | h
    · exact hPR h
    · exact hQR h
  le_top _ _ _ := Set.mem_univ _
  bot_le P q hq := by
    change q ∈ ({∅} : Set (Set W)) at hq
    rw [Set.mem_singleton_iff] at hq
    rw [hq]
    exact P.contains_empty
  isLUB_sSup S :=
    ⟨fun _ hPS _ hp => Or.inr ⟨_, hPS, hp⟩,
     fun Q hub _ hp => by
       rcases hp with hempty | ⟨P, hPS, hpP⟩
       · rw [hempty]; exact Q.contains_empty
       · exact hub hPS hpP⟩
  isGLB_sInf S :=
    ⟨fun _ hPS _ hp => hp _ hPS,
     fun _ hlb _ hp P hPS => hlb hPS hp⟩

/-! ### Distributivity

`Question W` is a complete distributive lattice (in mathlib's
sense: both a `Frame` and a `Coframe`). This subsumes finite
distributivity, gives a `HeytingAlgebra` (and `BiheytingAlgebra`)
structure for free, and follows from a single fact about the underlying
`Set (Set W)`: pointwise `∩` distributes over arbitrary `∪`, and
pointwise `∪` distributes over arbitrary `∩`.

We register it via `CompleteDistribLattice.ofMinimalAxioms`, which
needs only the two inequalities `inf_sSup ≤ iSup_inf` and
`iInf_sup ≤ sup_sInf`. -/

/-- Frame inequality: `P ⊓ sSup S ≤ ⨆ R ∈ S, P ⊓ R`. -/
private theorem inf_sSup_le_iSup_inf_aux (P : Question W)
    (S : Set (Question W)) :
    P ⊓ sSup S ≤ ⨆ R ∈ S, P ⊓ R := by
  intro q hq
  obtain ⟨hqP, hqS⟩ := hq
  rcases hqS with hempty | ⟨R, hRS, hqR⟩
  · -- q = ∅: lies in every Question
    have h0 : ∅ ∈ (⨆ R ∈ S, P ⊓ R : Question W).props :=
      (⨆ R ∈ S, P ⊓ R).contains_empty
    rw [hempty]; exact h0
  · -- q ∈ P ⊓ R for some R ∈ S; use le_iSup₂ to embed in the iSup
    have hPR : q ∈ (P ⊓ R).props := ⟨hqP, hqR⟩
    exact (le_iSup₂ (f := fun R (_ : R ∈ S) => P ⊓ R) R hRS) hPR

/-- Coframe inequality: `⨅ R ∈ S, P ⊔ R ≤ P ⊔ sInf S`. -/
private theorem iInf_sup_le_sup_sInf_aux (P : Question W)
    (S : Set (Question W)) :
    ⨅ R ∈ S, P ⊔ R ≤ P ⊔ sInf S := by
  intro q hq
  -- q ∈ ⨅ R ∈ S, P ⊔ R means: for every R ∈ S, q ∈ P.props ∨ q ∈ R.props
  have hAll : ∀ R ∈ S, q ∈ P.props ∨ q ∈ R.props := by
    intro R hRS
    have h1 : (⨅ R ∈ S, P ⊔ R) ≤ (P ⊔ R) :=
      iInf₂_le (f := fun R (_ : R ∈ S) => P ⊔ R) R hRS
    exact h1 hq
  by_cases hqP : q ∈ P.props
  · exact Or.inl hqP
  · -- q ∉ P.props, so for every R ∈ S, q ∈ R.props; hence q ∈ sInf S
    right
    intro R hRS
    rcases hAll R hRS with hp | hr
    · exact (hqP hp).elim
    · exact hr

/-- The `CompleteDistribLattice` structure: `⊓` distributes over `⨆` and
    `⊔` distributes over `⨅`. Subsumes binary distributivity and
    auto-provides `HeytingAlgebra`, `CoheytingAlgebra`, and
    `BiheytingAlgebra` instances via `ofMinimalAxioms`. -/
instance : CompleteDistribLattice (Question W) :=
  CompleteDistribLattice.ofMinimalAxioms
    { __ := (inferInstance : CompleteLattice (Question W))
      inf_sSup_le_iSup_inf := inf_sSup_le_iSup_inf_aux
      iInf_sup_le_sup_sInf := iInf_sup_le_sup_sInf_aux }

theorem le_def {P Q : Question W} : P ≤ Q ↔ P.props ⊆ Q.props :=
  Iff.rfl

theorem inf_eq_conj (P Q : Question W) : P ⊓ Q = conj P Q := rfl

theorem sup_eq_inqDisj (P Q : Question W) : P ⊔ Q = inqDisj P Q := rfl

theorem sSup_eq (S : Set (Question W)) : sSup S = sSupContent S := rfl

theorem sInf_eq (S : Set (Question W)) : sInf S = sInfContent S := rfl

theorem top_eq : (⊤ : Question W) = top := rfl
theorem bot_eq : (⊥ : Question W) = bot := rfl

@[simp] theorem mem_sSup_props {S : Set (Question W)} {q : Set W} :
    q ∈ (sSup S).props ↔ q = ∅ ∨ ∃ P ∈ S, q ∈ P.props := Iff.rfl

@[simp] theorem mem_sInf_props {S : Set (Question W)} {q : Set W} :
    q ∈ (sInf S).props ↔ ∀ P ∈ S, q ∈ P.props := Iff.rfl

/-- Membership in an indexed `iSup` of inquisitive contents. The `q = ∅`
    disjunct is structural: `∅` lies in every content's `props`. -/
theorem mem_iSup_iff {ι : Sort*} {f : ι → Question W} {q : Set W} :
    q ∈ (⨆ i, f i) ↔ q = ∅ ∨ ∃ i, q ∈ f i := by
  change q ∈ (sSup (Set.range f)).props ↔ _
  rw [mem_sSup_props]
  refine or_congr_right ?_
  constructor
  · rintro ⟨P, ⟨i, hPi⟩, hqP⟩; exact ⟨i, hPi ▸ hqP⟩
  · rintro ⟨i, hi⟩; exact ⟨f i, ⟨i, rfl⟩, hi⟩

/-- Membership in a bounded indexed `iSup`. Used pervasively for
    Hamblin-style wh-question alternatives (`which`) and for any
    `⨆ i ∈ I, declarative (P i)` construction. -/
theorem mem_biSup_iff {ι : Type*} {I : Set ι} {f : ι → Question W}
    {q : Set W} :
    q ∈ (⨆ i ∈ I, f i) ↔ q = ∅ ∨ ∃ i ∈ I, q ∈ f i := by
  constructor
  · intro h
    rw [mem_iSup_iff] at h
    rcases h with hempty | ⟨i, hi⟩
    · exact Or.inl hempty
    · rw [mem_iSup_iff] at hi
      rcases hi with hempty | ⟨hiI, hq⟩
      · exact Or.inl hempty
      · exact Or.inr ⟨i, hiI, hq⟩
  · rintro (hempty | ⟨i, hiI, hq⟩)
    · exact hempty ▸ (⨆ i ∈ I, f i).contains_empty
    · rw [mem_iSup_iff]
      refine Or.inr ⟨i, ?_⟩
      rw [mem_iSup_iff]
      exact Or.inr ⟨hiI, hq⟩

instance : Inhabited (Question W) := ⟨⊤⟩

/-! ### Basic API for `info` on the lattice operations

`info` is a monotone map from `(Question W, ≤)` to
`(Set W, ⊆)` and commutes with `⊔` (and `⊥`/`⊤`). The story for `⊓`
is one-sided: `info` distributes over union but only sub-distributes
over intersection (the same asymmetry as `⋃₀` over `Set` operations). -/

/-- `info` is monotone in the entailment order: a stronger inquiry has
    no more informative content than a weaker one. -/
theorem info_mono {P Q : Question W} (h : P ≤ Q) :
    P.info ⊆ Q.info := fun _ ⟨q, hq, hwq⟩ => ⟨q, h hq, hwq⟩

@[simp] theorem info_top : info (⊤ : Question W) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  exact fun w => ⟨Set.univ, Set.mem_univ _, Set.mem_univ w⟩

@[simp] theorem info_bot : info (⊥ : Question W) = ∅ :=
  Set.sUnion_singleton _

@[simp] theorem info_sup (P Q : Question W) :
    info (P ⊔ Q) = info P ∪ info Q :=
  Set.sUnion_union P.props Q.props

theorem info_inf_subset (P Q : Question W) :
    info (P ⊓ Q) ⊆ info P ∩ info Q := by
  rintro _ ⟨q, ⟨hpP, hpQ⟩, hwq⟩
  exact ⟨⟨q, hpP, hwq⟩, ⟨q, hpQ, hwq⟩⟩

/-! ### `alt` API and inquisitivity from alternatives

The `alt` (alternatives) selector picks out maximal propositions in
`P.props`. Two basic facts: alternatives are propositions, and the
union of alternatives is contained in `info P` (equality requires
finite-`W` or other guarantees that maximals exist —
[ciardelli-groenendijk-roelofsen-2018] discusses the limit case
where no maximal element exists). The two-alternatives criterion
gives a sufficient condition for inquisitivity that does not depend
on finiteness. -/

/-- Unfolded membership in `alt`. *Not* the simp normal form —
    `mem_alt_iff_maximal` is preferred because it connects to mathlib's
    `Maximal` API. Use this lemma when destructuring is more convenient
    than going through `Maximal`. -/
theorem mem_alt {P : Question W} {p : Set W} :
    p ∈ alt P ↔ p ∈ P.props ∧ ∀ q ∈ P.props, p ⊆ q → p = q := Iff.rfl

theorem alt_subset_props (P : Question W) : alt P ⊆ P.props :=
  fun _ hp => hp.1

theorem sUnion_alt_subset_info (P : Question W) :
    ⋃₀ alt P ⊆ info P := by
  rintro w ⟨q, hq, hwq⟩
  exact ⟨q, alt_subset_props P hq, hwq⟩

/-- **Simp normal form for alternatives**: the alternatives of `alt P`
    are exactly the `Maximal` elements of `P.props` under the subset
    order. Bridges the linguistic `alt`-definition to mathlib's
    order-theoretic `Maximal`, so that mathlib's `Maximal` API
    (`maximal_iff`, `Maximal.eq_of_ge`, etc.) applies directly to
    inquisitive alternatives. -/
@[simp] theorem mem_alt_iff_maximal {P : Question W} {p : Set W} :
    p ∈ alt P ↔ Maximal (· ∈ P.props) p := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hp, hmax⟩
    refine ⟨hp, ?_⟩
    intro q hq hpq
    exact (hmax q hq hpq).symm.le
  · rintro ⟨hp, hmax⟩
    refine ⟨hp, ?_⟩
    intro q hq hpq
    exact Set.Subset.antisymm hpq (hmax hq hpq)

/-- **Membership in `alt (P ⊓ Q)`**: the alternatives of the
    inquisitive conjunction are exactly the maximal elements of
    `P.props ∩ Q.props`. Direct corollary of `mem_alt_iff_maximal` and
    the pointwise definition of `⊓` on `props`. -/
theorem mem_alt_inf_iff {P Q : Question W} {q : Set W} :
    q ∈ alt (P ⊓ Q) ↔ Maximal (fun p => p ∈ P.props ∧ p ∈ Q.props) q := by
  rw [mem_alt_iff_maximal]
  rfl

/-- **Membership in `alt (P ⊔ Q)`**: the alternatives of the
    inquisitive disjunction are exactly the maximal elements of
    `P.props ∪ Q.props`. Direct corollary of `mem_alt_iff_maximal` and
    the pointwise definition of `⊔` on `props`. The asymmetry with
    `inf`: `inf`'s alts are sub-states satisfying both, `sup`'s alts
    are super-states maximal across either. -/
theorem mem_alt_sup_iff {P Q : Question W} {q : Set W} :
    q ∈ alt (P ⊔ Q) ↔ Maximal (fun p => p ∈ P.props ∨ p ∈ Q.props) q := by
  rw [mem_alt_iff_maximal]
  rfl

/-- An alt of `P` that is not contained in any *strictly larger* alt of
    `Q` survives in `alt (P ⊔ Q)`. The convenient direction for
    constructing alts of an inquisitive disjunction. -/
theorem mem_alt_sup_of_alt_left {P Q : Question W} {p : Set W}
    (hP : p ∈ alt P) (hQ : ∀ q ∈ Q.props, p ⊆ q → p = q) :
    p ∈ alt (P ⊔ Q) := by
  refine ⟨Or.inl hP.1, ?_⟩
  intro r hr hpr
  rcases hr with hrP | hrQ
  · exact hP.2 r hrP hpr
  · exact hQ r hrQ hpr

/-- An alt of `Q` that is not contained in any *strictly larger* alt of
    `P` survives in `alt (P ⊔ Q)`. Mirror of `mem_alt_sup_of_alt_left`. -/
theorem mem_alt_sup_of_alt_right {P Q : Question W} {q : Set W}
    (hQ : q ∈ alt Q) (hP : ∀ p ∈ P.props, q ⊆ p → q = p) :
    q ∈ alt (P ⊔ Q) := by
  refine ⟨Or.inr hQ.1, ?_⟩
  intro r hr hqr
  rcases hr with hrP | hrQ
  · exact hP r hrP hqr
  · exact hQ.2 r hrQ hqr

/-- An alt of `P ⊔ Q` is necessarily an alt of one of the summands —
    when restricted to that summand's `props`. -/
theorem alt_sup_subset_union (P Q : Question W) :
    alt (P ⊔ Q) ⊆ alt P ∪ alt Q := by
  intro q hq
  obtain ⟨hqPQ, hmax⟩ := hq
  rcases hqPQ with hqP | hqQ
  · left
    exact ⟨hqP, fun r hrP hqr => hmax r (Or.inl hrP) hqr⟩
  · right
    exact ⟨hqQ, fun r hrQ hqr => hmax r (Or.inr hrQ) hqr⟩

/-- The meet of two declaratives is the declarative of the intersection:
    `↓{A} ⊓ ↓{B} = ↓{A ∩ B}`. State `q` resolves both `declarative A` and
    `declarative B` iff `q ⊆ A ∩ B`. Direct corollary of
    `Set.subset_inter_iff`. -/
@[simp] theorem declarative_inf (A B : Set W) :
    declarative A ⊓ declarative B = declarative (A ∩ B) := by
  ext q
  show q ⊆ A ∧ q ⊆ B ↔ q ⊆ A ∩ B
  rw [Set.subset_inter_iff]

/-- A `declarative p` content has exactly one alternative — `p`
    itself, the unique maximal subset of `p`. -/
@[simp] theorem alt_declarative (p : Set W) : alt (declarative p) = {p} := by
  ext q
  refine ⟨?_, ?_⟩
  · rintro ⟨hq, hmax⟩
    exact Set.mem_singleton_iff.mpr (hmax p (Set.Subset.refl p) hq)
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    refine ⟨Set.Subset.refl q, ?_⟩
    intro r hr hpr
    exact Set.Subset.antisymm hpr hr

/-- The unique alternative of `⊤` is `Set.univ`. -/
@[simp] theorem alt_top : alt (⊤ : Question W) = {Set.univ} := by
  ext q
  simp only [mem_alt_iff_maximal, Set.mem_singleton_iff]
  constructor
  · intro hmax
    have huniv : (Set.univ : Set W) ∈ (⊤ : Question W).props :=
      Set.mem_univ _
    exact (hmax.eq_of_ge huniv (fun _ _ => Set.mem_univ _)).symm
  · rintro rfl
    refine ⟨Set.mem_univ _, ?_⟩
    intro q _ _
    exact fun _ _ => Set.mem_univ _

/-- The unique alternative of `⊥` is `∅`. -/
@[simp] theorem alt_bot : alt (⊥ : Question W) = {∅} := by
  ext q
  simp only [mem_alt_iff_maximal, Set.mem_singleton_iff]
  constructor
  · intro hmax
    have hq : q ∈ (⊥ : Question W).props := hmax.1
    change q ∈ ({∅} : Set (Set W)) at hq
    rwa [Set.mem_singleton_iff] at hq
  · rintro rfl
    refine ⟨rfl, ?_⟩
    intro r hr _
    change r ∈ ({∅} : Set (Set W)) at hr
    rw [Set.mem_singleton_iff] at hr
    exact hr.le

/-- If `P` has two distinct alternatives, then `P` is inquisitive: no
    single proposition (in particular, not `info P`) can equal both. -/
theorem isInquisitive_of_two_alternatives (P : Question W)
    {p₁ p₂ : Set W} (h₁ : p₁ ∈ alt P) (h₂ : p₂ ∈ alt P) (hne : p₁ ≠ p₂) :
    P.isInquisitive := by
  intro hinfo
  have hp₁ : p₁ ⊆ info P := fun w hwp₁ => ⟨p₁, h₁.1, hwp₁⟩
  have hp₂ : p₂ ⊆ info P := fun w hwp₂ => ⟨p₂, h₂.1, hwp₂⟩
  have hsub₁ : p₁ = info P := h₁.2 _ hinfo hp₁
  have hsub₂ : p₂ = info P := h₂.2 _ hinfo hp₂
  exact hne (hsub₁.trans hsub₂.symm)

/-! ### Existence of alternatives under finiteness

When `W` is finite, `P.props ⊆ Set W` is finite, so every
proposition extends to a maximal one. This gives the dual half of
`sUnion_alt_subset_info`: `info P ⊆ ⋃₀ alt P`, hence equality.

Without finiteness, alternatives need not exist — a downward-closed
family with no maximal element (e.g. `{q ⊊ Set.univ | q.Finite}`
on infinite `W`) is a valid `Question` with `alt P = ∅`
even though `info P ≠ ∅`. -/

/-- **Existence of alternatives** under finiteness: every proposition
    in `P.props` extends to a maximal one (i.e., to an alternative).

    Hypothesis is the *minimal* one: `P.props.Finite` (not `Finite W`).
    The latter implies the former (since `Set.instFinite` gives
    `Finite (Set W)` and `P.props ⊆ Set W`), but `P.props.Finite` can
    hold even on infinite worlds (e.g., a content with finitely many
    alternatives over an infinite world space). -/
theorem exists_alt_above (P : Question W) (hP : P.props.Finite)
    {p : Set W} (hp : p ∈ P.props) : ∃ q ∈ alt P, p ⊆ q := by
  obtain ⟨q, hpq, hmax⟩ := hP.exists_le_maximal hp
  exact ⟨q, mem_alt_iff_maximal.mpr hmax, hpq⟩

/-- Under finiteness of `P.props`, `info P` is exactly the union of
    alternatives: every world in some resolving proposition lies in some
    maximal resolving proposition. -/
theorem info_eq_sUnion_alt (P : Question W) (hP : P.props.Finite) :
    info P = ⋃₀ alt P := by
  apply Set.Subset.antisymm _ (sUnion_alt_subset_info P)
  rintro w ⟨p, hp, hwp⟩
  obtain ⟨q, hq, hpq⟩ := exists_alt_above P hP hp
  exact ⟨q, hq, hpq hwp⟩

/-! ### The Resolutions Theorem (DNF for inquisitive content)

The deepest theorem about `Question`: under finiteness, every
inquisitive content equals the inquisitive disjunction of the
declaratives generated by its alternatives. This is the
inquisitive-semantics analogue of disjunctive normal form, justifying
the slogan "an inquisitive content is its alternatives" — once
alternatives exist (finiteness), they fully determine the content.

This subsumes:
- Single-alternative case: `P = declarative p` iff `alt P = {p}`
  (the principal-ideal characterization for declaratives).
- The polar case: `polar p = declarative p ⊔ declarative pᶜ` (in
  `Hamblin.lean`) is literally `⨆ q ∈ {p, pᶜ}, declarative q`.
- Setoid-derived inquiries: `fromSetoid r` resolves to the iSup over
  equivalence classes (each class is an alternative).

Without finiteness the theorem fails (alternatives may not exist),
but the **inequality** `⨆ p ∈ alt P, declarative p ≤ P` holds always. -/

/-- The lower bound (always holds): the inquisitive disjunction of the
    declarative principal ideals of `P`'s alternatives is contained in
    `P` itself. -/
theorem iSup_declarative_alt_le (P : Question W) :
    ⨆ p ∈ alt P, declarative p ≤ P := by
  rw [← sSup_image]
  rw [le_def]
  intro q hq
  rcases hq with hempty | ⟨R, ⟨p, hp, hRp⟩, hqR⟩
  · rw [hempty]; exact P.contains_empty
  · subst hRp
    exact P.downward_closed p hp.1 q hqR

/-- **Resolutions Theorem under "alternatives-cover" hypothesis**: when
    every resolving proposition extends to an alternative, `P` equals the
    inquisitive disjunction of the declaratives generated by its
    alternatives. The hypothesis `hExt` is **strictly weaker** than
    `P.props.Finite`: atoms have `props = {q | q ⊆ V}` (potentially
    infinite if `V` infinite) but `alt = {V}`, so `hExt` discharges by
    `q ⊆ V → q ⊆ V` while finiteness fails.

    This is **Booth 2022's Compactness of Alternatives** for atomic and
    decomposable bilateral inquisitive propositions, captured at the
    `Question` substrate level. -/
theorem eq_iSup_declarative_alt_of_exists_alt (P : Question W)
    (hExt : ∀ p ∈ P.props, ∃ q ∈ alt P, p ⊆ q) :
    P = ⨆ p ∈ alt P, declarative p := by
  apply le_antisymm _ (iSup_declarative_alt_le P)
  rw [← sSup_image, le_def]
  intro q hq
  by_cases hqe : q = ∅
  · exact Or.inl hqe
  · right
    obtain ⟨p, hp, hqp⟩ := hExt q hq
    exact ⟨declarative p, ⟨p, hp, rfl⟩, hqp⟩

/-- **Resolutions Theorem**: under finiteness of `P.props`, every
    inquisitive content is the inquisitive disjunction of the
    declaratives generated by its alternatives. Corollary of the
    "alternatives-cover" version: finiteness gives existence of a
    maximal extension via `exists_alt_above`. -/
theorem eq_iSup_declarative_alt (P : Question W)
    (hP : P.props.Finite) : P = ⨆ p ∈ alt P, declarative p :=
  eq_iSup_declarative_alt_of_exists_alt P (fun _ hp => exists_alt_above P hP hp)

/-! ### Principal-ideal characterization of declaratives

[puncochar-2019]: declarative propositions are, algebraically
speaking, principal ideals in the algebra of information states. We
make this characterization explicit: `P` is declarative iff `P` is the
principal ideal generated by `info P`. We also prove the equivalent
characterization via alternatives: `P` is declarative iff
`alt P = {info P}`. -/

/-- **Principal-ideal characterization** ([puncochar-2019]): an
    inquisitive content is declarative iff it equals the principal ideal
    generated by its informative content. -/
theorem isDeclarative_iff_eq_declarative_info (P : Question W) :
    P.isDeclarative ↔ P = declarative P.info := by
  constructor
  · intro h
    ext q
    simp only [← mem_props, declarative, Set.mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · intro hq w hwq
      exact ⟨q, hq, hwq⟩
    · intro hq
      exact P.downward_closed P.info h q hq
  · intro h
    show P.info ∈ P
    rw [h]
    exact isDeclarative_declarative P.info

/-- **Alternative-set characterization**: an inquisitive content is
    declarative iff its alternatives are exactly `{info P}` — i.e., iff
    its informative content is itself the unique maximal resolving
    state. -/
theorem isDeclarative_iff_alt_eq_singleton (P : Question W) :
    P.isDeclarative ↔ alt P = {P.info} := by
  constructor
  · intro h
    ext q
    simp only [mem_alt_iff_maximal, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hqP, hmax⟩
      have h1 : q ⊆ P.info := fun w hw => ⟨q, hqP, hw⟩
      have h2 : P.info ⊆ q := hmax h h1
      exact Set.Subset.antisymm h1 h2
    · rintro rfl
      refine ⟨h, ?_⟩
      intro r hr hr_le w hw
      exact ⟨r, hr, hw⟩
  · intro halt
    show P.info ∈ P
    have hinfo : P.info ∈ alt P := by rw [halt]; rfl
    exact hinfo.1

/-! ### Heyting derivatives: complement, projection, division law

The `CompleteDistribLattice` structure registered above gives us a
`HeytingAlgebra` for free, so `Pᶜ` (pseudo-complement) and `P ⇨ Q`
(Heyting implication) come pre-installed with their universal
properties. The structural fact that drives the inquisitive-specific
theory is the explicit formula for `Pᶜ`:

    `Pᶜ = declarative (info P)ᶜ`

i.e., complementing `P` is the same as complementing its informative
content and taking the principal ideal. This single identity
(`compl_eq`) lets us derive the standard inquisitive operators
([ciardelli-groenendijk-roelofsen-2018]; [puncochar-2019]):

- the **non-inquisitive projection** `!P = Pᶜᶜ = declarative (info P)`
  (`proj_eq_compl_compl`),
- the **non-informative projection** `?P = P ⊔ Pᶜ`,
- and the **division law** `!P ⊓ ?P = P` decomposing every content into
  its informative and inquisitive components (`proj_inf_nonInfo`).

The lattice is **Heyting but not Boolean**: LEM `P ⊔ Pᶜ = ⊤` fails in
general — see `not_lem_inquisitive_content` below. -/

/-- **Pseudo-complement formula**: the Heyting complement `Pᶜ` is the
    declarative principal ideal of the complemented informative content.
    This is the structural identity that grounds all subsequent Heyting
    derivatives. -/
theorem compl_eq (P : Question W) :
    Pᶜ = declarative (P.info)ᶜ := by
  apply le_antisymm
  · intro q hq
    show q ⊆ (info P)ᶜ
    intro w hwq hw_info
    have h1 : ({w} : Set W) ∈ Pᶜ := by
      apply (Pᶜ).downward_closed q hq
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hwq
    obtain ⟨p, hpP, hwp⟩ := hw_info
    have h2 : ({w} : Set W) ∈ P := by
      apply P.downward_closed p hpP
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hwp
    have h3 : ({w} : Set W) ∈ P ⊓ Pᶜ := ⟨h2, h1⟩
    have h4 : ({w} : Set W) ∈ (⊥ : Question W) := by
      rw [← inf_compl_self P]; exact h3
    have h5 : ({w} : Set W) = ∅ := by
      change ({w} : Set W) ∈ ({∅} : Set (Set W)) at h4
      rwa [Set.mem_singleton_iff] at h4
    exact (h5 ▸ Set.mem_singleton w : w ∈ (∅ : Set W)).elim
  · rw [← himp_bot]
    apply le_himp_iff.mpr
    intro q hq
    obtain ⟨hq_decl, hq_P⟩ := hq
    show q ∈ ({∅} : Set (Set W))
    rw [Set.mem_singleton_iff]
    have hq_info : q ⊆ P.info := fun w hwq => ⟨q, hq_P, hwq⟩
    have hsub : q ⊆ ∅ := fun w hw => hq_decl hw (hq_info hw)
    exact Set.subset_empty_iff.mp hsub

/-- **`info` commutes with complement**: even though the lattice of
    contents is only Heyting, the underlying informative content is a
    Boolean Set, and `info` respects complementation. -/
@[simp] theorem info_compl (P : Question W) :
    info Pᶜ = (info P)ᶜ := by
  rw [compl_eq, info_declarative]

/-- **Non-inquisitive projection** `!P`: the declarative content with
    the same informative content as `P` ([ciardelli-groenendijk-roelofsen-2018]).
    Removes any inquisitivity by collapsing all alternatives into a
    single principal ideal. Always declarative; equal to `P` iff `P`
    is declarative.

    Used to define classical (non-inquisitive) operators in inquisitive
    semantics: classical disjunction is `!(P ⩒ Q) = !P ⊔ !Q`, etc. -/
def proj (P : Question W) : Question W :=
  declarative P.info

/-- `!P = Pᶜᶜ`: the non-inquisitive projection coincides with the
    Heyting double-complement ([ciardelli-groenendijk-roelofsen-2018]).
    Together with `compl_eq`, this means every inquisitive operator
    derivable from the Heyting structure is, at the level of `info`, a
    Boolean operator on `Set W`. -/
theorem proj_eq_compl_compl (P : Question W) : proj P = Pᶜᶜ := by
  rw [compl_eq Pᶜ, info_compl, compl_compl]
  rfl

@[simp] theorem info_proj (P : Question W) : P.proj.info = P.info :=
  info_declarative P.info

theorem isDeclarative_proj (P : Question W) : P.proj.isDeclarative :=
  isDeclarative_declarative P.info

/-- `proj` is idempotent: projecting twice = projecting once. -/
@[simp] theorem proj_proj (P : Question W) : P.proj.proj = P.proj := by
  unfold proj
  rw [info_declarative]

/-- Projection fixes declarative contents (`!P = P` iff `P` is declarative). -/
theorem proj_eq_self_iff (P : Question W) :
    P.proj = P ↔ P.isDeclarative := by
  refine ⟨?_, ?_⟩
  · intro h
    have := isDeclarative_proj P
    rw [h] at this
    exact this
  · intro h
    exact ((isDeclarative_iff_eq_declarative_info P).mp h).symm

/-- **Non-informative projection** `?P := P ⊔ Pᶜ`
    ([ciardelli-groenendijk-roelofsen-2018]). The "inquisitive
    question" operator: takes any content and returns its non-informative
    counterpart with the same inquisitive structure. -/
def nonInfo (P : Question W) : Question W := P ⊔ Pᶜ

theorem nonInfo_eq_sup_compl (P : Question W) :
    nonInfo P = P ⊔ Pᶜ := rfl

/-- **Division law** ([ciardelli-groenendijk-roelofsen-2018]):
    every inquisitive content decomposes uniquely as the meet of its
    non-inquisitive projection and its non-informative projection. This
    is the fundamental decomposition theorem of inquisitive semantics —
    it says the lattice "factors through" `(info, alternatives)`. -/
theorem proj_inf_nonInfo (P : Question W) :
    proj P ⊓ nonInfo P = P := by
  unfold nonInfo
  rw [inf_sup_left]
  have h1 : proj P ⊓ Pᶜ = ⊥ := by
    rw [compl_eq P]
    apply le_antisymm _ bot_le
    intro q ⟨hq1, hq2⟩
    show q ∈ ({∅} : Set (Set W))
    rw [Set.mem_singleton_iff]
    have : q ⊆ info P ∩ (info P)ᶜ := fun w hw => ⟨hq1 hw, hq2 hw⟩
    rw [Set.inter_compl_self] at this
    exact Set.subset_empty_iff.mp this
  rw [h1, sup_bot_eq]
  apply le_antisymm
  · exact inf_le_right
  · refine le_inf ?_ le_rfl
    intro q hq
    show q ⊆ info P
    intro w hwq
    exact ⟨q, hq, hwq⟩

/-! ### LEM fails: the lattice is Heyting but not Boolean

A central feature of inquisitive semantics is that the standard logical
laws of a Boolean algebra do not all hold. In particular, the law of
excluded middle `P ⊔ Pᶜ = ⊤` fails: an inquisitive content `P` and its
pseudo-complement `Pᶜ` are both *declarative*, so their join is
declarative too, while `⊤` is the trivially-resolved content (every
state in `props`). The witness below uses the polar-question shape
`declarative {true} ⊔ declarative {true}ᶜ` over `Bool`. -/

/-- **LEM fails for inquisitive content**: there exists `W` and `P`
    with `P ⊔ Pᶜ ≠ ⊤`. This is what makes the lattice Heyting rather
    than Boolean. -/
theorem not_lem_inquisitive_content :
    ∃ (W : Type) (P : Question W), P ⊔ Pᶜ ≠ ⊤ := by
  refine ⟨Bool, declarative {true}, ?_⟩
  intro h
  rw [compl_eq, info_declarative] at h
  have huniv : (Set.univ : Set Bool) ∈ (⊤ : Question Bool) :=
    Set.mem_univ _
  rw [← h] at huniv
  rcases huniv with h1 | h1
  · have : false ∈ ({true} : Set Bool) := h1 (Set.mem_univ false)
    simp at this
  · have : true ∈ ({true} : Set Bool)ᶜ := h1 (Set.mem_univ true)
    simp at this

/-! ### `Question.Support` instance

The cross-tradition `s ⊨ Q` interface (`Question.Support`) is satisfied
by `Question` in the standard inquisitive way: an information state `s : Set W`
supports / resolves the issue `P` iff `s` is one of the resolving propositions
(`s ∈ P.props`). This is the inquisitive notion of support
([ciardelli-groenendijk-roelofsen-2018]). -/

/-- Inquisitive support: `s ⊨ P` iff the state `s` resolves the issue `P`. -/
instance instSupport : Question.Support (Set W) (Question W) where
  supports s P := s ∈ P

theorem supports_iff (s : Set W) (P : Question W) :
    Question.Support.supports s P ↔ s ∈ P := Iff.rfl

end Question

