import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.SetLike.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.Preorder.Finite

/-!
# Inquisitive Content
@cite{ciardelli-groenendijk-roelofsen-2018} @cite{puncochar-2016}
@cite{puncochar-2019} @cite{theiler-etal-2018}

A bundled `InquisitiveContent W` representing an inquisitive proposition
in the sense of @cite{ciardelli-groenendijk-roelofsen-2018}: a non-empty
downward-closed family of information states over `W` (where an
information state is a subset of `W`).

This is the linglib **sibling structure** to `Setoid W` for the inquiry
component of a discourse context. Where `Setoid W` (used in
`Core/Mood/POSWQ.lean`) represents partition-based questions, this type
represents the full @cite{ciardelli-groenendijk-roelofsen-2018}
inquisitive proposition: a downward-closed family of information states
with possibly non-disjoint, possibly non-exhaustive alternatives.
Mention-some, intermediate-exhaustive, and conditional question
phenomena live here (none representable as a Setoid partition).

Algebraically (per @cite{puncochar-2019}): declarative propositions are
the **principal ideals** in the algebra of information states. We expose
this characterization as `isDeclarative` and prove it equivalent to the
defining condition `info P ∈ P` via `isDeclarative_iff_eq_declarative_info`.

## Mathlib alignment

- `props : Set (Set W)` — sets of subsets of `W`, mathlib-native
- `contains_empty` is logically equivalent to `Nonempty props` together
  with downward closure — we expose it as the field directly because
  it's the only constraint that matters once downward closure holds
- `info` returns `Set W` (mathlib-native), not `W → Bool` — for the
  Bool/List computational variants of inquisitive operations, see
  `Core/Inquisitive.lean`
- `SetLike (InquisitiveContent W) (Set W)` — auto-derives `Membership`,
  `CoeSort`, and the `ext` machinery. `mem_props` is the canonical
  simp normalization (`q ∈ P.props → q ∈ P`).
- `CompleteDistribLattice (InquisitiveContent W)` — registered via
  `CompleteDistribLattice.ofMinimalAxioms` from two pointwise
  inequalities, giving `Frame`, `Coframe`, `HeytingAlgebra`, and
  `BiheytingAlgebra` for free. Mirrors `Filter`'s registration pattern.

### Why a bundled structure rather than `LowerSet (Set W)`?

A downward-closed family of propositions on `W` is, abstractly, a
`LowerSet (Set W)`. We considered registering `InquisitiveContent`
as a `LowerSet` synonym, but rejected it because the `⊥` elements
disagree: `LowerSet.⊥ = ∅` (no resolving propositions), while ours is
`{∅}` (only the inconsistent state resolves). The non-emptiness
constraint (`contains_empty`) is essential to inquisitive semantics
and is lost in `LowerSet`. We use `SetLike` instead, which gives the
membership/coercion API without forcing `LowerSet`'s `⊥`.

## Architectural placement

This file sits in `Core/Mood/` next to `POSW.lean` and `POSWQ.lean` as
the **sibling type** to `Setoid W` for the inquiry component, following
the prescription in the `POSWQ.lean` "Architectural note" docstring. It
does *not* replace `POSWQ.inquiry : Setoid W`; the embedding goes the
other way (`Setoid → InquisitiveContent` in
`Core/Mood/PartitionAsInquiry.lean`). Mirrors mathlib's `Set`/`Finset`
and `Filter`/`Ultrafilter` parallel-structures pattern rather than
collapsing the two types.
-/

namespace Core.Mood

universe u v

/-- An inquisitive proposition in the sense of
    @cite{ciardelli-groenendijk-roelofsen-2018}: a non-empty
    downward-closed family of information states over `W`. The states in
    `props` are the ones that *resolve* the issue raised by the sentence. -/
structure InquisitiveContent (W : Type u) where
  /-- The set of propositions resolving the issue. -/
  props : Set (Set W)
  /-- Contains the empty proposition (= the inconsistent information
      state). Equivalent to non-emptiness given downward closure. -/
  contains_empty : ∅ ∈ props
  /-- Downward closed: if `p` resolves the issue and `q ⊆ p`, then `q`
      also resolves it (any sufficient evidence is also sufficient when
      strengthened). -/
  downward_closed : ∀ p ∈ props, ∀ q : Set W, q ⊆ p → q ∈ props

namespace InquisitiveContent

variable {W : Type u}

/-- `SetLike` instance: an `InquisitiveContent W` coerces to its underlying
    `Set (Set W)` of resolving propositions. Auto-derives `Membership`
    (`q ∈ P` means `q ∈ P.props`), `CoeSort`, and the standard `ext`
    machinery. Mirrors mathlib's pattern for `Submonoid`, `Subgroup`,
    `LowerSet`, etc. -/
instance : SetLike (InquisitiveContent W) (Set W) where
  coe := props
  coe_injective' P Q h := by cases P; cases Q; congr

/-- Membership normalization: `q ∈ P.props` rewrites to `q ∈ P`. Mirrors
    mathlib's `mem_carrier` pattern (`SetLike.Basic` line 92). -/
@[simp] theorem mem_props {P : InquisitiveContent W} {q : Set W} :
    q ∈ P.props ↔ q ∈ P := Iff.rfl

@[simp, norm_cast] theorem coe_mk (s : Set (Set W)) (h₁ h₂) :
    ((⟨s, h₁, h₂⟩ : InquisitiveContent W) : Set (Set W)) = s := rfl

/-- Two `InquisitiveContent`s are equal when their `props` agree. -/
@[ext]
theorem ext {P Q : InquisitiveContent W} (h : ∀ q, q ∈ P ↔ q ∈ Q) : P = Q :=
  SetLike.ext h

/-- The **alternatives** of an inquisitive content
    (@cite{ciardelli-groenendijk-roelofsen-2018}): the maximal
    propositions in `props`. These are the "answers" — the strongest
    information states that resolve the issue. -/
def alt (P : InquisitiveContent W) : Set (Set W) :=
  {p ∈ P.props | ∀ q ∈ P.props, p ⊆ q → p = q}

/-- The **informative content** of an inquisitive content
    (@cite{ciardelli-groenendijk-roelofsen-2018}): the union of all
    propositions in `props`. The information any utterance with this
    meaning provides — the actual world must lie in `info P`. -/
def info (P : InquisitiveContent W) : Set W :=
  ⋃₀ P.props

/-- A sentence is **informative** iff its informative content excludes
    at least one possible world. -/
def isInformative (P : InquisitiveContent W) : Prop :=
  info P ≠ Set.univ

/-- A sentence is **inquisitive** iff resolving the issue it raises
    requires more than the information it provides — equivalently, iff
    `info P` itself is not in `props` (so no single proposition in
    `props` covers all of `info P`). -/
def isInquisitive (P : InquisitiveContent W) : Prop :=
  info P ∉ P.props

/-- A sentence is **declarative** iff it is not inquisitive —
    equivalently, iff `info P ∈ props`. Algebraic characterization
    (@cite{puncochar-2019}): `props` is a principal ideal in the algebra
    of information states; see `isDeclarative_iff_eq_declarative_info`. -/
def isDeclarative (P : InquisitiveContent W) : Prop :=
  info P ∈ P.props

/-- Declarative and inquisitive are exact negations of each other. -/
theorem isDeclarative_iff_not_isInquisitive (P : InquisitiveContent W) :
    P.isDeclarative ↔ ¬ P.isInquisitive :=
  not_not.symm

/-! ### Constructors -/

/-- The **declarative** content of a proposition `p`: the principal
    ideal `{q | q ⊆ p}`. Single alternative `p`; non-inquisitive;
    informative iff `p ≠ univ`. -/
def declarative (p : Set W) : InquisitiveContent W where
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

/-! ### Algebraic operations (@cite{puncochar-2019} §2)

Following the support-clause definitions in @cite{puncochar-2019} §2:
conjunction is `||α ∧ β|| = ||α|| ∩ ||β||` (state supports `α ∧ β` iff
it supports both); inquisitive disjunction is `||α ⩒ β|| = ||α|| ∪ ||β||`
(state supports `α ⩒ β` iff it supports either).

Implication `→` and negation `¬` arise as the Heyting `⇨` and `ᶜ` of
the `CompleteDistribLattice` structure registered below; the
`InquisitiveContent.imp` and `InquisitiveContent.not` aliases (in the
"Non-inquisitive projection" section) expose them under their
linguistic names. The non-inquisitive projection `!P` (collapsing
inquisitivity) is `proj P`; classical operators are derived via
projection: `!(P ⩒ Q) = !P ⊔ !Q` etc. -/

/-- **Inquisitive conjunction** `P ∧ Q` (@cite{puncochar-2019} §2 ∧
    clause): `props` is the pointwise intersection. A state resolves
    `P ∧ Q` iff it resolves both `P` and `Q`. -/
def conj (P Q : InquisitiveContent W) : InquisitiveContent W where
  props := P.props ∩ Q.props
  contains_empty := ⟨P.contains_empty, Q.contains_empty⟩
  downward_closed := fun p hp q hq =>
    ⟨P.downward_closed p hp.1 q hq, Q.downward_closed p hp.2 q hq⟩

/-- **Inquisitive disjunction** `P ⩒ Q` (@cite{puncochar-2019} §2 ⩒
    clause): `props` is the pointwise union. A state resolves
    `P ⩒ Q` iff it resolves `P` or `Q`. Distinct from classical
    disjunction `∨`, whose support clause involves splitting the state
    across two substates. -/
def inqDisj (P Q : InquisitiveContent W) : InquisitiveContent W where
  props := P.props ∪ Q.props
  contains_empty := Or.inl P.contains_empty
  downward_closed := fun p hp q hq => by
    rcases hp with hp | hp
    · exact Or.inl (P.downward_closed p hp q hq)
    · exact Or.inr (Q.downward_closed p hp q hq)

/-- The **top** inquisitive content: every set of worlds resolves the
    issue. The trivial inquiry that demands nothing. -/
def top : InquisitiveContent W where
  props := Set.univ
  contains_empty := Set.mem_univ _
  downward_closed := fun _ _ _ _ => Set.mem_univ _

/-- The **bottom** inquisitive content: only the inconsistent state
    (`∅`) resolves the issue. The unsatisfiable inquiry. -/
def bot : InquisitiveContent W where
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
`InquisitiveContent W` into a **bounded distributive complete lattice**
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
def sSupContent (S : Set (InquisitiveContent W)) : InquisitiveContent W where
  props := {q | q = ∅ ∨ ∃ P ∈ S, q ∈ P.props}
  contains_empty := Or.inl rfl
  downward_closed := fun p hp q hq => by
    rcases hp with hempty | ⟨P, hPS, hpP⟩
    · left; rw [hempty] at hq; exact Set.subset_empty_iff.mp hq
    · exact Or.inr ⟨P, hPS, P.downward_closed p hpP q hq⟩

/-- The arbitrary infimum: a state resolves `sInf S` iff it resolves
    every `P ∈ S`. (When `S = ∅`, this is `Set.univ`, recovering `⊤`.) -/
def sInfContent (S : Set (InquisitiveContent W)) : InquisitiveContent W where
  props := {q | ∀ P ∈ S, q ∈ P.props}
  contains_empty := fun P _ => P.contains_empty
  downward_closed := fun p hp q hq P hPS => P.downward_closed p (hp P hPS) q hq

instance : SupSet (InquisitiveContent W) := ⟨sSupContent⟩
instance : InfSet (InquisitiveContent W) := ⟨sInfContent⟩

/-- The complete lattice structure on `InquisitiveContent W`. Provides
    `Lattice`, `BoundedOrder`, `SupSet`, `InfSet`, plus `iSup`/`iInf`
    for the entire mathlib API. -/
instance : CompleteLattice (InquisitiveContent W) where
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

`InquisitiveContent W` is a complete distributive lattice (in mathlib's
sense: both a `Frame` and a `Coframe`). This subsumes finite
distributivity, gives a `HeytingAlgebra` (and `BiheytingAlgebra`)
structure for free, and follows from a single fact about the underlying
`Set (Set W)`: pointwise `∩` distributes over arbitrary `∪`, and
pointwise `∪` distributes over arbitrary `∩`.

We register it via `CompleteDistribLattice.ofMinimalAxioms`, which
needs only the two inequalities `inf_sSup ≤ iSup_inf` and
`iInf_sup ≤ sup_sInf`. -/

/-- Frame inequality: `P ⊓ sSup S ≤ ⨆ R ∈ S, P ⊓ R`. -/
private theorem inf_sSup_le_iSup_inf_aux (P : InquisitiveContent W)
    (S : Set (InquisitiveContent W)) :
    P ⊓ sSup S ≤ ⨆ R ∈ S, P ⊓ R := by
  intro q hq
  obtain ⟨hqP, hqS⟩ := hq
  rcases hqS with hempty | ⟨R, hRS, hqR⟩
  · -- q = ∅: lies in every InquisitiveContent
    have h0 : ∅ ∈ (⨆ R ∈ S, P ⊓ R : InquisitiveContent W).props :=
      (⨆ R ∈ S, P ⊓ R).contains_empty
    rw [hempty]; exact h0
  · -- q ∈ P ⊓ R for some R ∈ S; use le_iSup₂ to embed in the iSup
    have hPR : q ∈ (P ⊓ R).props := ⟨hqP, hqR⟩
    exact (le_iSup₂ (f := fun R (_ : R ∈ S) => P ⊓ R) R hRS) hPR

/-- Coframe inequality: `⨅ R ∈ S, P ⊔ R ≤ P ⊔ sInf S`. -/
private theorem iInf_sup_le_sup_sInf_aux (P : InquisitiveContent W)
    (S : Set (InquisitiveContent W)) :
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
instance : CompleteDistribLattice (InquisitiveContent W) :=
  CompleteDistribLattice.ofMinimalAxioms
    { __ := (inferInstance : CompleteLattice (InquisitiveContent W))
      inf_sSup_le_iSup_inf := inf_sSup_le_iSup_inf_aux
      iInf_sup_le_sup_sInf := iInf_sup_le_sup_sInf_aux }

theorem le_def {P Q : InquisitiveContent W} : P ≤ Q ↔ P.props ⊆ Q.props :=
  Iff.rfl

theorem inf_eq_conj (P Q : InquisitiveContent W) : P ⊓ Q = conj P Q := rfl

theorem sup_eq_inqDisj (P Q : InquisitiveContent W) : P ⊔ Q = inqDisj P Q := rfl

theorem sSup_eq (S : Set (InquisitiveContent W)) : sSup S = sSupContent S := rfl

theorem sInf_eq (S : Set (InquisitiveContent W)) : sInf S = sInfContent S := rfl

theorem top_eq : (⊤ : InquisitiveContent W) = top := rfl
theorem bot_eq : (⊥ : InquisitiveContent W) = bot := rfl

@[simp] theorem mem_sSup_props {S : Set (InquisitiveContent W)} {q : Set W} :
    q ∈ (sSup S).props ↔ q = ∅ ∨ ∃ P ∈ S, q ∈ P.props := Iff.rfl

@[simp] theorem mem_sInf_props {S : Set (InquisitiveContent W)} {q : Set W} :
    q ∈ (sInf S).props ↔ ∀ P ∈ S, q ∈ P.props := Iff.rfl

/-- Membership in an indexed `iSup` of inquisitive contents. The `q = ∅`
    disjunct is structural: `∅` lies in every content's `props`. -/
theorem mem_iSup_iff {ι : Sort*} {f : ι → InquisitiveContent W} {q : Set W} :
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
theorem mem_biSup_iff {ι : Type*} {I : Set ι} {f : ι → InquisitiveContent W}
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

instance : Inhabited (InquisitiveContent W) := ⟨⊤⟩

/-! ### Basic API for `info` on the lattice operations

`info` is a monotone map from `(InquisitiveContent W, ≤)` to
`(Set W, ⊆)` and commutes with `⊔` (and `⊥`/`⊤`). The story for `⊓`
is one-sided: `info` distributes over union but only sub-distributes
over intersection (the same asymmetry as `⋃₀` over `Set` operations). -/

/-- `info` is monotone in the entailment order: a stronger inquiry has
    no more informative content than a weaker one. -/
theorem info_mono {P Q : InquisitiveContent W} (h : P ≤ Q) :
    P.info ⊆ Q.info := fun _ ⟨q, hq, hwq⟩ => ⟨q, h hq, hwq⟩

@[simp] theorem info_top : info (⊤ : InquisitiveContent W) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  exact fun w => ⟨Set.univ, Set.mem_univ _, Set.mem_univ w⟩

@[simp] theorem info_bot : info (⊥ : InquisitiveContent W) = ∅ :=
  Set.sUnion_singleton _

@[simp] theorem info_sup (P Q : InquisitiveContent W) :
    info (P ⊔ Q) = info P ∪ info Q :=
  Set.sUnion_union P.props Q.props

theorem info_inf_subset (P Q : InquisitiveContent W) :
    info (P ⊓ Q) ⊆ info P ∩ info Q := by
  rintro _ ⟨q, ⟨hpP, hpQ⟩, hwq⟩
  exact ⟨⟨q, hpP, hwq⟩, ⟨q, hpQ, hwq⟩⟩

/-! ### Polar question via inquisitive disjunction

@cite{puncochar-2019} §2 defines the polar question as
`?α := α ⩒ ¬α`. For atomic `α` with truth set `p`, the support
clause for `¬α` reduces to `a ⊆ pᶜ` (= `declarative pᶜ`), so
`?p` is the inquisitive disjunction of `declarative p` and
`declarative pᶜ`. We take this as the **definition** of `polar`
rather than stipulating an independent `props` set and proving
equivalence after the fact. The basic theorems (`info_polar`,
`isInquisitive_polar_iff`) then derive from `info_sup`,
`info_declarative`, and properties of complementation. -/

/-- The **polar interrogative** content of a proposition `p`, defined
    via @cite{puncochar-2019}'s `?α := α ⩒ ¬α`. Alternatives are `p`
    and `pᶜ`; non-informative (`info = univ`); inquisitive iff `p` is
    non-trivial. -/
def polar (p : Set W) : InquisitiveContent W :=
  declarative p ⊔ declarative pᶜ

/-- `polar` is, by definition, the inquisitive disjunction of the two
    declaratives. *Not* `@[simp]`: `polar p` is a meaningful surface
    primitive (it's the polar interrogative), and unfolding it to its
    lattice definition disrupts simp lemmas like `info_polar`. Use
    explicitly when reasoning about the lattice structure. -/
theorem polar_eq_sup (p : Set W) :
    polar p = declarative p ⊔ declarative pᶜ := rfl

@[simp] theorem info_polar (p : Set W) : (polar p).info = Set.univ := by
  rw [polar_eq_sup, info_sup, info_declarative, info_declarative,
      Set.union_compl_self]

theorem not_isInformative_polar (p : Set W) :
    ¬ (polar p).isInformative :=
  fun h => h (info_polar p)

/-- A polar question is **inquisitive** iff its proposition is
    non-trivial (neither `∅` nor `univ`). The trivial cases collapse to
    declaratives because `univ ⊆ p` requires `p = univ`. -/
theorem isInquisitive_polar_iff (p : Set W) :
    (polar p).isInquisitive ↔ p ≠ ∅ ∧ p ≠ Set.univ := by
  show (polar p).info ∉ (polar p).props ↔ _
  rw [info_polar]
  show (Set.univ : Set W) ∉ (declarative p).props ∪ (declarative pᶜ).props ↔ _
  simp only [declarative, Set.mem_union, Set.mem_setOf_eq, Set.univ_subset_iff,
             not_or]
  refine ⟨?_, ?_⟩
  · rintro ⟨hnp, hnpc⟩
    refine ⟨?_, hnp⟩
    intro he
    apply hnpc
    rw [he, Set.compl_empty]
  · rintro ⟨hne, hnu⟩
    refine ⟨hnu, ?_⟩
    intro hpc
    apply hne
    rw [← compl_compl p, hpc, Set.compl_univ]

/-! ### Wh-question content via Hamblin alternatives

A wh-question `Which x ∈ D satisfies P x?` (Hamblin) has one alternative
per element of `D`, given by the proposition `P e` for each `e ∈ D`.
We define this as the inquisitive disjunction of the principal ideals
generated by the per-element predicates. -/

/-- The **wh-question** content for "Which x ∈ D satisfies P x?". One
    alternative per element of `D` (modulo non-maximality of overlapping
    predicates). The Hamblin construction: `which D P = ⨆ e ∈ D,
    declarative (P e)`. -/
def which {E : Type v} (D : Set E) (P : E → Set W) : InquisitiveContent W :=
  ⨆ e ∈ D, declarative (P e)

/-- A state resolves `which D P` iff it is empty or contained in some
    `P e` for an `e ∈ D`. -/
theorem mem_which {E : Type v} {D : Set E} {P : E → Set W} {q : Set W} :
    q ∈ which D P ↔ q = ∅ ∨ ∃ e ∈ D, q ⊆ P e := by
  rw [which, mem_biSup_iff]
  simp only [mem_declarative]

/-- The informative content of `which D P` is the union of the per-element
    predicates: a world is settled by the question iff it satisfies
    `P e` for some `e ∈ D`. -/
@[simp] theorem info_which {E : Type v} (D : Set E) (P : E → Set W) :
    info (which D P) = ⋃ e ∈ D, P e := by
  ext w
  simp only [info, Set.mem_sUnion, Set.mem_iUnion]
  constructor
  · rintro ⟨q, hq, hwq⟩
    rw [show (q ∈ (which D P).props) = (q ∈ which D P) from rfl, mem_which] at hq
    rcases hq with hempty | ⟨e, heD, hqP⟩
    · exact (hempty ▸ hwq).elim
    · exact ⟨e, heD, hqP hwq⟩
  · rintro ⟨e, heD, hwe⟩
    refine ⟨P e, ?_, hwe⟩
    rw [show (P e ∈ (which D P).props) = (P e ∈ which D P) from rfl, mem_which]
    exact Or.inr ⟨e, heD, Set.Subset.refl _⟩

/-! ### `alt` API and inquisitivity from alternatives

The `alt` (alternatives) selector picks out maximal propositions in
`P.props`. Two basic facts: alternatives are propositions, and the
union of alternatives is contained in `info P` (equality requires
finite-`W` or other guarantees that maximals exist —
@cite{ciardelli-groenendijk-roelofsen-2018} discusses the limit case
where no maximal element exists). The two-alternatives criterion
gives a sufficient condition for inquisitivity that does not depend
on finiteness. -/

/-- Unfolded membership in `alt`. *Not* the simp normal form —
    `mem_alt_iff_maximal` is preferred because it connects to mathlib's
    `Maximal` API. Use this lemma when destructuring is more convenient
    than going through `Maximal`. -/
theorem mem_alt {P : InquisitiveContent W} {p : Set W} :
    p ∈ alt P ↔ p ∈ P.props ∧ ∀ q ∈ P.props, p ⊆ q → p = q := Iff.rfl

theorem alt_subset_props (P : InquisitiveContent W) : alt P ⊆ P.props :=
  fun _ hp => hp.1

theorem sUnion_alt_subset_info (P : InquisitiveContent W) :
    ⋃₀ alt P ⊆ info P := by
  rintro w ⟨q, hq, hwq⟩
  exact ⟨q, alt_subset_props P hq, hwq⟩

/-- **Simp normal form for alternatives**: the alternatives of `alt P`
    are exactly the `Maximal` elements of `P.props` under the subset
    order. Bridges the linguistic `alt`-definition to mathlib's
    order-theoretic `Maximal`, so that mathlib's `Maximal` API
    (`maximal_iff`, `Maximal.eq_of_ge`, etc.) applies directly to
    inquisitive alternatives. -/
@[simp] theorem mem_alt_iff_maximal {P : InquisitiveContent W} {p : Set W} :
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
@[simp] theorem alt_top : alt (⊤ : InquisitiveContent W) = {Set.univ} := by
  ext q
  simp only [mem_alt_iff_maximal, Set.mem_singleton_iff]
  constructor
  · intro hmax
    have huniv : (Set.univ : Set W) ∈ (⊤ : InquisitiveContent W).props :=
      Set.mem_univ _
    exact (hmax.eq_of_ge huniv (fun _ _ => Set.mem_univ _)).symm
  · rintro rfl
    refine ⟨Set.mem_univ _, ?_⟩
    intro q _ _
    exact fun _ _ => Set.mem_univ _

/-- The unique alternative of `⊥` is `∅`. -/
@[simp] theorem alt_bot : alt (⊥ : InquisitiveContent W) = {∅} := by
  ext q
  simp only [mem_alt_iff_maximal, Set.mem_singleton_iff]
  constructor
  · intro hmax
    have hq : q ∈ (⊥ : InquisitiveContent W).props := hmax.1
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
theorem isInquisitive_of_two_alternatives (P : InquisitiveContent W)
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
on infinite `W`) is a valid `InquisitiveContent` with `alt P = ∅`
even though `info P ≠ ∅`. -/

/-- **Existence of alternatives** under finiteness: every proposition
    in `P.props` extends to a maximal one (i.e., to an alternative).

    Hypothesis is the *minimal* one: `P.props.Finite` (not `Finite W`).
    The latter implies the former (since `Set.instFinite` gives
    `Finite (Set W)` and `P.props ⊆ Set W`), but `P.props.Finite` can
    hold even on infinite worlds (e.g., a content with finitely many
    alternatives over an infinite world space). -/
theorem exists_alt_above (P : InquisitiveContent W) (hP : P.props.Finite)
    {p : Set W} (hp : p ∈ P.props) : ∃ q ∈ alt P, p ⊆ q := by
  obtain ⟨q, hpq, hmax⟩ := hP.exists_le_maximal hp
  exact ⟨q, mem_alt_iff_maximal.mpr hmax, hpq⟩

/-- Under finiteness of `P.props`, `info P` is exactly the union of
    alternatives: every world in some resolving proposition lies in some
    maximal resolving proposition. -/
theorem info_eq_sUnion_alt (P : InquisitiveContent W) (hP : P.props.Finite) :
    info P = ⋃₀ alt P := by
  apply Set.Subset.antisymm _ (sUnion_alt_subset_info P)
  rintro w ⟨p, hp, hwp⟩
  obtain ⟨q, hq, hpq⟩ := exists_alt_above P hP hp
  exact ⟨q, hq, hpq hwp⟩

/-! ### The Resolutions Theorem (DNF for inquisitive content)

The deepest theorem about `InquisitiveContent`: under finiteness, every
inquisitive content equals the inquisitive disjunction of the
declaratives generated by its alternatives. This is the
inquisitive-semantics analogue of disjunctive normal form, justifying
the slogan "an inquisitive content is its alternatives" — once
alternatives exist (finiteness), they fully determine the content.

This subsumes:
- Single-alternative case: `P = declarative p` iff `alt P = {p}`
  (the principal-ideal characterization for declaratives).
- The polar case: `polar p = declarative p ⊔ declarative pᶜ` is
  literally `⨆ q ∈ {p, pᶜ}, declarative q`.
- Setoid-derived inquiries: `fromSetoid r` resolves to the iSup over
  equivalence classes (each class is an alternative).

Without finiteness the theorem fails (alternatives may not exist),
but the **inequality** `⨆ p ∈ alt P, declarative p ≤ P` holds always. -/

/-- The lower bound (always holds): the inquisitive disjunction of the
    declarative principal ideals of `P`'s alternatives is contained in
    `P` itself. -/
theorem iSup_declarative_alt_le (P : InquisitiveContent W) :
    ⨆ p ∈ alt P, declarative p ≤ P := by
  rw [← sSup_image]
  rw [le_def]
  intro q hq
  rcases hq with hempty | ⟨R, ⟨p, hp, hRp⟩, hqR⟩
  · rw [hempty]; exact P.contains_empty
  · subst hRp
    exact P.downward_closed p hp.1 q hqR

/-- **Resolutions Theorem**: under finiteness of `P.props`, every
    inquisitive content is the inquisitive disjunction of the
    declaratives generated by its alternatives. The DNF analogue for
    inquisitive semantics. -/
theorem eq_iSup_declarative_alt (P : InquisitiveContent W)
    (hP : P.props.Finite) : P = ⨆ p ∈ alt P, declarative p := by
  apply le_antisymm _ (iSup_declarative_alt_le P)
  rw [← sSup_image, le_def]
  intro q hq
  by_cases hqe : q = ∅
  · exact Or.inl hqe
  · right
    obtain ⟨p, hp, hqp⟩ := exists_alt_above P hP hq
    exact ⟨declarative p, ⟨p, hp, rfl⟩, hqp⟩

/-! ### Principal-ideal characterization of declaratives

@cite{puncochar-2019}: declarative propositions are, algebraically
speaking, principal ideals in the algebra of information states. We
make this characterization explicit: `P` is declarative iff `P` is the
principal ideal generated by `info P`. We also prove the equivalent
characterization via alternatives: `P` is declarative iff
`alt P = {info P}`. -/

/-- **Principal-ideal characterization** (@cite{puncochar-2019}): an
    inquisitive content is declarative iff it equals the principal ideal
    generated by its informative content. -/
theorem isDeclarative_iff_eq_declarative_info (P : InquisitiveContent W) :
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
theorem isDeclarative_iff_alt_eq_singleton (P : InquisitiveContent W) :
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
(@cite{ciardelli-groenendijk-roelofsen-2018}; @cite{puncochar-2019}):

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
theorem compl_eq (P : InquisitiveContent W) :
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
    have h4 : ({w} : Set W) ∈ (⊥ : InquisitiveContent W) := by
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
@[simp] theorem info_compl (P : InquisitiveContent W) :
    info Pᶜ = (info P)ᶜ := by
  rw [compl_eq, info_declarative]

/-- **Non-inquisitive projection** `!P`: the declarative content with
    the same informative content as `P` (@cite{ciardelli-groenendijk-roelofsen-2018}).
    Removes any inquisitivity by collapsing all alternatives into a
    single principal ideal. Always declarative; equal to `P` iff `P`
    is declarative.

    Used to define classical (non-inquisitive) operators in inquisitive
    semantics: classical disjunction is `!(P ⩒ Q) = !P ⊔ !Q`, etc. -/
def proj (P : InquisitiveContent W) : InquisitiveContent W :=
  declarative P.info

/-- `!P = Pᶜᶜ`: the non-inquisitive projection coincides with the
    Heyting double-complement (@cite{ciardelli-groenendijk-roelofsen-2018}).
    Together with `compl_eq`, this means every inquisitive operator
    derivable from the Heyting structure is, at the level of `info`, a
    Boolean operator on `Set W`. -/
theorem proj_eq_compl_compl (P : InquisitiveContent W) : proj P = Pᶜᶜ := by
  rw [compl_eq Pᶜ, info_compl, compl_compl]
  rfl

@[simp] theorem info_proj (P : InquisitiveContent W) : P.proj.info = P.info :=
  info_declarative P.info

theorem isDeclarative_proj (P : InquisitiveContent W) : P.proj.isDeclarative :=
  isDeclarative_declarative P.info

/-- `proj` is idempotent: projecting twice = projecting once. -/
@[simp] theorem proj_proj (P : InquisitiveContent W) : P.proj.proj = P.proj := by
  unfold proj
  rw [info_declarative]

/-- Projection fixes declarative contents (`!P = P` iff `P` is declarative). -/
theorem proj_eq_self_iff (P : InquisitiveContent W) :
    P.proj = P ↔ P.isDeclarative := by
  refine ⟨?_, ?_⟩
  · intro h
    have := isDeclarative_proj P
    rw [h] at this
    exact this
  · intro h
    exact ((isDeclarative_iff_eq_declarative_info P).mp h).symm

/-- **Non-informative projection** `?P := P ⊔ Pᶜ`
    (@cite{ciardelli-groenendijk-roelofsen-2018}). The "inquisitive
    question" operator: takes any content and returns its non-informative
    counterpart with the same inquisitive structure. -/
def nonInfo (P : InquisitiveContent W) : InquisitiveContent W := P ⊔ Pᶜ

theorem nonInfo_eq_sup_compl (P : InquisitiveContent W) :
    nonInfo P = P ⊔ Pᶜ := rfl

/-- **Division law** (@cite{ciardelli-groenendijk-roelofsen-2018}):
    every inquisitive content decomposes uniquely as the meet of its
    non-inquisitive projection and its non-informative projection. This
    is the fundamental decomposition theorem of inquisitive semantics —
    it says the lattice "factors through" `(info, alternatives)`. -/
theorem proj_inf_nonInfo (P : InquisitiveContent W) :
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

/-! ### Answerhood: mention-some and mention-all

The two basic notions of answerhood from the inquisitive-semantics
tradition (@cite{ciardelli-groenendijk-roelofsen-2018};
@cite{theiler-etal-2018}). A **mention-all** answer settles every
alternative; a **mention-some** answer settles at least one without
settling all. These are the structural Set-valued analogues of the
`Discourse.Issue.isMentionSomeAnswer` / `isMentionAllAnswer` predicates
that the Bool/List shadow exposes — the same definitions, lifted from
`List`-enumeration to `∀ p ∈ alt P, …`. -/

/-- A state `σ` is a **mention-some** answer to `P`: it settles at least
    one alternative (`σ ⊆ p` for some `p ∈ alt P`) without settling all
    of them (some alternative is not contained in `σ`). -/
def isMentionSomeAnswer (P : InquisitiveContent W) (σ : Set W) : Prop :=
  (∃ p ∈ alt P, σ ⊆ p) ∧ (∃ p ∈ alt P, ¬ σ ⊆ p)

/-- A state `σ` is a **mention-all** answer to `P`: it settles every
    alternative. -/
def isMentionAllAnswer (P : InquisitiveContent W) (σ : Set W) : Prop :=
  ∀ p ∈ alt P, σ ⊆ p

/-- The only mention-all answer to `⊥` is the empty state. -/
@[simp] theorem isMentionAllAnswer_bot_iff {σ : Set W} :
    isMentionAllAnswer (⊥ : InquisitiveContent W) σ ↔ σ = ∅ := by
  unfold isMentionAllAnswer
  simp only [alt_bot, Set.mem_singleton_iff, forall_eq, Set.subset_empty_iff]

/-- A mention-all answer to a declarative is precisely a substate of its
    informative content. -/
@[simp] theorem isMentionAllAnswer_declarative_iff {p σ : Set W} :
    isMentionAllAnswer (declarative p) σ ↔ σ ⊆ p := by
  unfold isMentionAllAnswer
  simp only [alt_declarative, Set.mem_singleton_iff, forall_eq]

/-! ### Granularity ordering (@cite{deo-thomas-2025})

Two questions on the same informative content can differ in *granularity*:
how finely they slice the world space into alternatives. The `widerThan`
relation captures the asymmetric "more granular" ordering used in
@cite{deo-thomas-2025} for granularity-based question construals. It is
strictly weaker than question entailment: a wider question's alternatives
are individually more specific, but no entailment relation generally
holds between answers. -/

/-- `q'` is **properly contained** in `q`: `q' ⊆ q` and `q' ≠ q`. -/
def properlyContains (q q' : Set W) : Prop := q' ⊆ q ∧ q' ≠ q

/-- `widerThan P P'` (@cite{deo-thomas-2025}): `P` is a wider, more
    granular inquiry than `P'` over the same informative content. Three
    conditions: (a) same `info`; (b) no `P'`-alternative properly
    contains any `P`-alternative; (c) some `P`-alternative is properly
    contained in some `P'`-alternative. -/
def widerThan (P P' : InquisitiveContent W) : Prop :=
  P.info = P'.info ∧
  (∀ p₂ ∈ alt P', ∀ p₁ ∈ alt P, ¬ properlyContains p₁ p₂) ∧
  (∃ p₁ ∈ alt P, ∃ p₂ ∈ alt P', properlyContains p₂ p₁)

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
    ∃ (W : Type) (P : InquisitiveContent W), P ⊔ Pᶜ ≠ ⊤ := by
  refine ⟨Bool, declarative {true}, ?_⟩
  intro h
  rw [compl_eq, info_declarative] at h
  have huniv : (Set.univ : Set Bool) ∈ (⊤ : InquisitiveContent Bool) :=
    Set.mem_univ _
  rw [← h] at huniv
  rcases huniv with h1 | h1
  · have : false ∈ ({true} : Set Bool) := h1 (Set.mem_univ false)
    simp at this
  · have : true ∈ ({true} : Set Bool)ᶜ := h1 (Set.mem_univ true)
    simp at this

end InquisitiveContent

end Core.Mood
