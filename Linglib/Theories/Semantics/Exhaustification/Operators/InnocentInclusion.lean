import Linglib.Theories.Semantics.Exhaustification.Operators.Basic

/-!
# Innocent Inclusion @cite{bar-lev-fox-2020}

From @cite{bar-lev-fox-2020}, Definition (51):

> `II(p, C) = ∩{C'' ⊆ C : C''` is maximal s.t.
> `{r : r ∈ C''} ∪ {p} ∪ {¬q : q ∈ IE(p,C)}` is consistent`}`

After computing IE, find all maximal subsets of alternatives that can
consistently be assigned TRUE (given that IE alternatives are false). An
alternative is innocently includable iff it appears in ALL such maximal
sets.

## Cell identification

@cite{bar-lev-fox-2020} eq. (20) + (27) + footnote 21. The *cell* of
`Partition(ALT)` containing prejacent `φ` is the strongest proposition
that assigns a definite truth value to every alternative in `ALT`: the
prejacent, the negation of every IE-excludable alternative, and the truth
of every non-excludable alternative. When the cell is consistent (=
satisfiable at some world), `exhIEII` collapses onto it. When inconsistent
(the simple-disjunction case `{a∨b, a, b, a∧b}`), `exhIEII` does no
enrichment beyond `exhIE`.
-/

namespace Exhaustification

variable {World : Type*}
variable (ALT : Set (Set World))
variable (φ : Set World)

/-- **Definition (II-compatible set)**: A set of propositions `R` is
    `(ALT, φ, IE)`-compatible for inclusion if:
    - `R ⊆ ALT`
    - `{r : r ∈ R} ∪ {φ} ∪ {¬q : q ∈ IE(ALT, φ)}` is consistent. -/
def IsIICompatible (R : Set (Set World)) : Prop :=
  R ⊆ ALT ∧
  SetConsistent ({φ} ∪ {ψ | ∃ q, IsInnocentlyExcludable ALT φ q ∧ ψ = qᶜ} ∪ R)

/-- **Definition (MI-set)**: Maximal II-compatible set. -/
def IsMISet (R : Set (Set World)) : Prop :=
  IsIICompatible ALT φ R ∧
  ∀ R', IsIICompatible ALT φ R' → R ⊆ R' → R' ⊆ R

/-- **Definition (II)**: `II(ALT, φ) = {r ∈ ALT : r belongs to every MI-set}`. -/
def II : Set (Set World) :=
  {r ∈ ALT | ∀ R, IsMISet ALT φ R → r ∈ R}

/-- An alternative `a` is innocently includable given `ALT` and `φ` iff
    `a ∈ II(ALT, φ)`. -/
def IsInnocentlyIncludable (a : Set World) : Prop :=
  a ∈ II ALT φ

/-- **Definition (Exh^{IE+II})**: The exhaustivity operator with both IE
    and II.

    `⟦Exh^{IE+II}⟧(ALT)(φ)(w) ⇔ φ(w) ∧ ∀q ∈ IE(ALT,φ)[¬q(w)] ∧ ∀r ∈ II(ALT,φ)[r(w)]`.

    Bar-Lev & Fox's key operator that derives free choice. -/
def exhIEII : Set World := λ w =>
  φ w ∧
  (∀ q, IsInnocentlyExcludable ALT φ q → ¬q w) ∧
  (∀ r, IsInnocentlyIncludable ALT φ r → r w)

/-- The non-IE alternatives: members of `ALT` not innocently excludable.
    @cite{bar-lev-fox-2020} (the `C \ IE(p,C)` of paper eq. 20). -/
def nonExcludable : Set (Set World) :=
  {r ∈ ALT | ¬ IsInnocentlyExcludable ALT φ r}

/-- The cell of `Partition(ALT)` containing prejacent `φ`.
    @cite{bar-lev-fox-2020} eq. (20):
    `Cell(p, C) = p ∧ ⋂₀ {¬q : q ∈ IE(p, C)} ∧ ⋂₀ (C \ IE(p, C))`. -/
def cell : Set World := λ w =>
  φ w ∧
  (∀ q, IsInnocentlyExcludable ALT φ q → ¬ q w) ∧
  (∀ r ∈ nonExcludable ALT φ, r w)

/-- Membership in `nonExcludable` unfolds to `r ∈ ALT` plus
    non-excludability. -/
@[simp] lemma mem_nonExcludable {r : Set World} :
    r ∈ nonExcludable ALT φ ↔ r ∈ ALT ∧ ¬ IsInnocentlyExcludable ALT φ r := Iff.rfl

/-- Every II-compatible set consists of non-excludable alternatives. -/
lemma isIICompatible_subset_nonExcludable
    {R : Set (Set World)} (hR : IsIICompatible ALT φ R) :
    R ⊆ nonExcludable ALT φ := by
  intro r hr
  refine ⟨hR.1 hr, fun hexc => ?_⟩
  obtain ⟨u, hu⟩ := hR.2
  exact hu (rᶜ) (Set.mem_union_left _ (Set.mem_union_right _ ⟨r, hexc, rfl⟩))
    (hu r (Set.mem_union_right _ hr))

/-- When the cell is consistent (nonempty as a set of worlds),
    `nonExcludable` is itself II-compatible. -/
lemma isIICompatible_nonExcludable_of_cell_nonempty
    (h : (cell ALT φ).Nonempty) :
    IsIICompatible ALT φ (nonExcludable ALT φ) := by
  obtain ⟨u, hφ, hexcl, hne⟩ := h
  refine ⟨fun _ hr => hr.1, u, ?_⟩
  rintro ψ ((hφψ | ⟨q, hq, rfl⟩) | hr)
  · rw [Set.mem_singleton_iff.mp hφψ]; exact hφ
  · exact hexcl q hq
  · exact hne ψ hr

/-- **Cell identification (@cite{bar-lev-fox-2020} footnote 21)**: when the
    cell is consistent, the unique MI-set is `nonExcludable`, hence
    `II = nonExcludable`. -/
theorem II_eq_nonExcludable_of_cell_nonempty
    (h : (cell ALT φ).Nonempty) :
    II ALT φ = nonExcludable ALT φ := by
  have hD_compat := isIICompatible_nonExcludable_of_cell_nonempty ALT φ h
  ext r
  refine ⟨fun ⟨hrALT, hrMI⟩ => ?_, fun hr => ⟨hr.1, ?_⟩⟩
  · have hD_MI : IsMISet ALT φ (nonExcludable ALT φ) :=
      ⟨hD_compat, fun R' hR' _ => isIICompatible_subset_nonExcludable ALT φ hR'⟩
    exact hrMI _ hD_MI
  · intro R hR
    have hR_sub := isIICompatible_subset_nonExcludable ALT φ hR.1
    have hRr_compat : IsIICompatible ALT φ (R ∪ {r}) := by
      refine ⟨?_, ?_⟩
      · rintro s (hsR | hsr)
        · exact hR.1.1 hsR
        · rw [Set.mem_singleton_iff.mp hsr]; exact hr.1
      · obtain ⟨u, hu⟩ := hD_compat.2
        refine ⟨u, ?_⟩
        rintro ψ ((hφψ | hneg) | hRr)
        · exact hu ψ (Set.mem_union_left _ (Set.mem_union_left _ hφψ))
        · exact hu ψ (Set.mem_union_left _ (Set.mem_union_right _ hneg))
        · rcases hRr with hsR | hsr
          · exact hu ψ (Set.mem_union_right _ (hR_sub hsR))
          · rw [Set.mem_singleton_iff.mp hsr]
            exact hu r (Set.mem_union_right _ hr)
    exact hR.2 _ hRr_compat Set.subset_union_left (Set.mem_union_right _ rfl)

/-- **Cell identification (@cite{bar-lev-fox-2020} eq. 27)**: when the cell
    is consistent, `exhIEII` coincides with `cell`. -/
theorem exhIEII_eq_cell_of_cell_nonempty
    (h : (cell ALT φ).Nonempty) :
    exhIEII ALT φ = cell ALT φ := by
  have hII := II_eq_nonExcludable_of_cell_nonempty ALT φ h
  ext w
  refine ⟨fun ⟨hφ, hexcl, hII_w⟩ => ⟨hφ, hexcl, fun r hr => ?_⟩,
          fun ⟨hφ, hexcl, hne⟩ => ⟨hφ, hexcl, fun r hr_II => ?_⟩⟩
  · exact hII_w r (show r ∈ II ALT φ by rw [hII]; exact hr)
  · have : r ∈ nonExcludable ALT φ := by rw [← hII]; exact hr_II
    exact hne r this

/-- **Sufficient condition for II membership via a cell witness world.**

    Given any world `w` that witnesses cell consistency (satisfies the
    prejacent, falsifies all IE-excludable alternatives, and verifies all
    non-excludable alternatives), every alternative true at `w` is
    innocently includable.

    The abstract content of @cite{bar-lev-fox-2020}'s free-choice
    derivation: each disjunct is true at the "separately-A-B" world, which
    is the cell witness for `Alt(◇(a∨b))`. -/
theorem mem_II_of_cell_witness {target : Set World}
    (htarget_alt : target ∈ ALT) (w : World)
    (hwitness : cell ALT φ w) (htarget : target w) :
    target ∈ II ALT φ := by
  rw [II_eq_nonExcludable_of_cell_nonempty ALT φ ⟨w, hwitness⟩]
  exact ⟨htarget_alt, fun hexc => hwitness.2.1 target hexc htarget⟩

end Exhaustification
