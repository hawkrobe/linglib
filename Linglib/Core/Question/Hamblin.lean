import Linglib.Core.Question.Basic

/-!
# Question — Hamblin constructions
@cite{ciardelli-groenendijk-roelofsen-2018} @cite{puncochar-2019}

Two basic question-content constructions, both built from `declarative`
+ inquisitive disjunction:

- `polar p` — the polar interrogative `?p` for proposition `p`. Defined
  as `declarative p ⊔ declarative pᶜ`, matching @cite{puncochar-2019}'s
  `?α := α ⩒ ¬α` (since the support clause for `¬α` over an atom with
  truth set `p` reduces to `q ⊆ pᶜ`).
- `which D P` — the wh-question content "which `e ∈ D` satisfies `P e`?",
  built as a Hamblin disjunction `⨆ e ∈ D, declarative (P e)`. One
  alternative per element of `D` (modulo non-maximality of overlapping
  predicates).

Both constructions are *defined* in terms of the lattice operations
rather than stipulated by a fresh `props` set with bridge theorems —
informativity/inquisitivity facts then derive from `info_sup`,
`info_declarative`, and properties of the underlying `Set` operations.
-/

namespace Core

namespace Question

universe u v
variable {W : Type u}

/-! ### Polar question via inquisitive disjunction -/

/-- The **polar interrogative** content of a proposition `p`, defined
    via @cite{puncochar-2019}'s `?α := α ⩒ ¬α`. Alternatives are `p`
    and `pᶜ`; non-informative (`info = univ`); inquisitive iff `p` is
    non-trivial. -/
def polar (p : Set W) : Question W :=
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

/-! ### `alt`-characterization of `polar` -/

/-- **Membership in a polar question's alternatives** when `p` is
    non-trivial: the alternative set is exactly `{p, pᶜ}`. The two
    alternatives are the maximal subsets of `polar p`, with no
    intermediate maximal element. The non-triviality hypotheses rule
    out the degenerate cases (`polar ∅ = polar univ = ⊤`) where the
    two summands collapse and `alt = {univ}`. -/
theorem alt_polar_of_nontrivial {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    alt (polar p) = {p, pᶜ} := by
  have hppc : ¬ p ⊆ pᶜ := by
    intro h
    apply hne
    ext w
    refine ⟨?_, fun he => he.elim⟩
    intro hw
    exact (h hw hw).elim
  have hpcp : ¬ pᶜ ⊆ p := by
    intro h
    apply hnu
    ext w
    refine ⟨fun _ => Set.mem_univ _, ?_⟩
    intro _
    by_contra hwp
    exact hwp (h hwp)
  -- Membership in `polar p` reduces to "subset of p or subset of pᶜ".
  have hmem : ∀ q : Set W, q ∈ polar p ↔ q ⊆ p ∨ q ⊆ pᶜ := by
    intro q
    rw [polar_eq_sup]
    constructor
    · intro h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr h
  ext q
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨hq, hmax⟩
    rcases (hmem q).mp hq with hqp | hqpc
    · have hpmem : p ∈ polar p := (hmem p).mpr (Or.inl (Set.Subset.refl p))
      exact Or.inl (hmax p hpmem hqp)
    · have hpcmem : pᶜ ∈ polar p := (hmem pᶜ).mpr (Or.inr (Set.Subset.refl pᶜ))
      exact Or.inr (hmax pᶜ hpcmem hqpc)
  · rintro (rfl | rfl)
    · refine ⟨(hmem q).mpr (Or.inl (Set.Subset.refl q)), ?_⟩
      intro r hr hqr
      rcases (hmem r).mp hr with hrp | hrpc
      · exact Set.Subset.antisymm hqr hrp
      · exact (hppc (hqr.trans hrpc)).elim
    · refine ⟨(hmem pᶜ).mpr (Or.inr (Set.Subset.refl pᶜ)), ?_⟩
      intro r hr hqr
      rcases (hmem r).mp hr with hrp | hrpc
      · exact (hpcp (hqr.trans hrp)).elim
      · exact Set.Subset.antisymm hqr hrpc

/-! ### Polar degenerate-case identities -/

/-- `declarative univ = ⊤`: the principal ideal of `univ` is the
    whole `LowerSet`. -/
theorem declarative_univ : (declarative (Set.univ : Set W)) = ⊤ := by
  ext q
  show q ⊆ Set.univ ↔ True
  simp [Set.subset_univ]

/-- `polar ∅ = ⊤`: a polar question with vacuous proposition collapses
    to the trivial issue. -/
theorem polar_empty : (polar (∅ : Set W)) = ⊤ := by
  rw [polar_eq_sup, Set.compl_empty, declarative_univ, sup_top_eq]

/-- `polar univ = ⊤`: dual of `polar_empty`. -/
theorem polar_univ : (polar (Set.univ : Set W)) = ⊤ := by
  rw [polar_eq_sup, declarative_univ, top_sup_eq]

/-! ### `alt`-characterization of `polar` (full) -/

/-- **Membership in a polar question's alternatives** — full
    characterization covering both the inquisitive case (`p` non-trivial)
    and the degenerate cases (`p = ∅` or `p = univ`, which collapse the
    polar question to `⊤`). -/
theorem alt_polar_iff (p : Set W) (q : Set W) :
    q ∈ alt (polar p) ↔
      ((p = ∅ ∨ p = Set.univ) ∧ q = Set.univ) ∨
      (p ≠ ∅ ∧ p ≠ Set.univ ∧ (q = p ∨ q = pᶜ)) := by
  by_cases he : p = ∅
  · subst he
    rw [polar_empty, alt_top]
    simp
  · by_cases hu : p = Set.univ
    · subst hu
      rw [polar_univ, alt_top]
      simp
    · rw [alt_polar_of_nontrivial he hu]
      simp [he, hu]

/-- Membership in `alt (polar p)` under the standard non-degenerate
    assumption — the convenient form for empirical study files. -/
theorem mem_alt_polar_of_nontrivial {p : Set W}
    (hne : p ≠ ∅) (hnu : p ≠ Set.univ) (q : Set W) :
    q ∈ alt (polar p) ↔ q = p ∨ q = pᶜ := by
  rw [alt_polar_of_nontrivial hne hnu]; simp

/-! ### Wh-question content via Hamblin alternatives

A wh-question `Which x ∈ D satisfies P x?` (Hamblin) has one alternative
per element of `D`, given by the proposition `P e` for each `e ∈ D`.
We define this as the inquisitive disjunction of the principal ideals
generated by the per-element predicates. -/

/-- The **wh-question** content for "Which x ∈ D satisfies P x?". One
    alternative per element of `D` (modulo non-maximality of overlapping
    predicates). The Hamblin construction: `which D P = ⨆ e ∈ D,
    declarative (P e)`. -/
def which {E : Type v} (D : Set E) (P : E → Set W) : Question W :=
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

/-! ### `alt`-characterization of `which` -/

/-- A `Q`-alternative of `which D P` is necessarily either the empty
    set (in the degenerate "no inhabited witness" case) or some
    maximal `P e` for `e ∈ D` — i.e., a `P e` not properly contained
    in any other `P e'`. -/
theorem alt_which_iff_left {E : Type v} {D : Set E} {P : E → Set W} {q : Set W} :
    q ∈ alt (which D P) →
      (q = ∅ ∨
       ∃ e ∈ D, q = P e ∧ ∀ e' ∈ D, P e ⊆ P e' → P e' = P e) := by
  rintro ⟨hq, hmax⟩
  -- q ∈ which D P, so q = ∅ or q ⊆ P e for some e ∈ D.
  rcases mem_which.mp hq with hempty | ⟨e, heD, hqe⟩
  · exact Or.inl hempty
  · -- q ⊆ P e. Maximality: P e ∈ which D P, so q = P e.
    have hPe_mem : P e ∈ which D P := mem_which.mpr (Or.inr ⟨e, heD, Set.Subset.refl _⟩)
    have hqPe : q = P e := hmax (P e) hPe_mem hqe
    refine Or.inr ⟨e, heD, hqPe, ?_⟩
    intro e' he'D hsub
    have hPe'_mem : P e' ∈ which D P :=
      mem_which.mpr (Or.inr ⟨e', he'D, Set.Subset.refl _⟩)
    -- From q = P e and q ⊆ P e' (by hsub), maximality of q gives q = P e'.
    have : q = P e' := hmax (P e') hPe'_mem (hqPe ▸ hsub)
    rw [← hqPe, ← this]

/-- The convenient direction: a maximal `P e` (in the antichain sense
    over `D`) that is nonempty is in `alt (which D P)`. -/
theorem mem_alt_which_of_maximal {E : Type v} {D : Set E} {P : E → Set W}
    (e : E) (heD : e ∈ D) (hne : (P e).Nonempty)
    (hmax : ∀ e' ∈ D, P e ⊆ P e' → P e' = P e) :
    P e ∈ alt (which D P) := by
  refine ⟨mem_which.mpr (Or.inr ⟨e, heD, Set.Subset.refl _⟩), ?_⟩
  intro r hr hPer
  rcases mem_which.mp hr with hrempty | ⟨e', he'D, hre'⟩
  · -- r = ∅, but P e ⊆ r = ∅ contradicts hne.
    obtain ⟨w, hw⟩ := hne
    exact absurd (hPer hw) (hrempty ▸ Set.notMem_empty w)
  · -- r ⊆ P e'. So P e ⊆ r ⊆ P e'. By maximality of P e among D, P e' = P e.
    have hPePe' : P e ⊆ P e' := hPer.trans hre'
    have : P e' = P e := hmax e' he'D hPePe'
    -- Now r ⊆ P e' = P e ⊆ r, so r = P e.
    exact Set.Subset.antisymm hPer (this ▸ hre')

/-! ### Hamblin construction from a finite alternative list

Bridge primitive: `ofList L` packages a `List (Set W)` of alternatives
into a `Core.Question W`, mediating between abstract Set-based issues and
finite-presentation consumers (Roberts QUD relevance, Hamblin focus
alternatives, etc.). -/

/-- The Hamblin issue with alternatives drawn from a finite list `L`:
    `ofList L = ⨆ p ∈ L, declarative p`. The underlying-set view of `L`
    is taken so the standard `mem_biSup_iff` API applies directly. -/
def ofList (L : List (Set W)) : Question W :=
  ⨆ p ∈ {p : Set W | p ∈ L}, declarative p

/-- A state resolves `ofList L` iff it is empty or contained in some
    listed alternative. -/
theorem mem_ofList {L : List (Set W)} {q : Set W} :
    q ∈ ofList L ↔ q = ∅ ∨ ∃ p ∈ L, q ⊆ p := by
  unfold ofList
  rw [mem_biSup_iff]
  simp only [Set.mem_setOf_eq, mem_declarative]

/-- The informative content of `ofList L` is the union of its
    alternatives. -/
@[simp] theorem info_ofList (L : List (Set W)) :
    info (ofList L) = ⋃ p ∈ L, p := by
  ext w
  simp only [info, Set.mem_sUnion, Set.mem_iUnion]
  refine ⟨?_, ?_⟩
  · rintro ⟨q, hq, hwq⟩
    rw [show (q ∈ (ofList L).props) = (q ∈ ofList L) from rfl, mem_ofList] at hq
    rcases hq with hempty | ⟨p, hpL, hqp⟩
    · exact (hempty ▸ hwq).elim
    · exact ⟨p, hpL, hqp hwq⟩
  · rintro ⟨p, hpL, hwp⟩
    refine ⟨p, ?_, hwp⟩
    rw [show (p ∈ (ofList L).props) = (p ∈ ofList L) from rfl, mem_ofList]
    exact Or.inr ⟨p, hpL, Set.Subset.refl _⟩

/-! ### `alt`-characterization for `ofList`

Under pairwise disjointness, nonemptiness, and a nonempty list,
the alternatives of `ofList L` are exactly the listed elements. -/

/-- **Alternatives of `ofList`** under pairwise disjoint + nonempty
    cells (and a nonempty list): `alt (ofList L) = {p | p ∈ L}`. The
    `L ≠ []` hypothesis rules out the degenerate `ofList [] = ⊥`,
    where `alt = {∅}` rather than `∅`. -/
theorem alt_ofList_of_pairwise_disjoint_nonempty
    (L : List (Set W)) (hL : L ≠ [])
    (hdisj : ∀ p₁ ∈ L, ∀ p₂ ∈ L, p₁ ≠ p₂ → Disjoint p₁ p₂)
    (hne : ∀ p ∈ L, p ≠ ∅) :
    alt (ofList L) = {p | p ∈ L} := by
  ext q
  rw [Set.mem_setOf_eq, mem_alt]
  constructor
  · rintro ⟨hq, hmax⟩
    rcases mem_ofList.mp hq with rfl | ⟨p, hpL, hqp⟩
    · -- q = ∅: extends to any p ∈ L by ∅ ⊆ p, so maximality forces ∅ = p,
      -- contradicting hne.
      obtain ⟨p, hpL⟩ : ∃ p, p ∈ L := List.exists_mem_of_ne_nil L hL
      have hp_in : p ∈ (ofList L).props :=
        mem_ofList.mpr (Or.inr ⟨p, hpL, Set.Subset.refl p⟩)
      have heq : (∅ : Set W) = p := hmax p hp_in (Set.empty_subset p)
      exact (hne p hpL heq.symm).elim
    · have hp_in : p ∈ (ofList L).props :=
        mem_ofList.mpr (Or.inr ⟨p, hpL, Set.Subset.refl p⟩)
      have hqeq : q = p := hmax p hp_in hqp
      exact hqeq ▸ hpL
  · intro hqL
    refine ⟨mem_ofList.mpr (Or.inr ⟨q, hqL, Set.Subset.refl q⟩), ?_⟩
    intro r hr hqr
    rcases mem_ofList.mp hr with rfl | ⟨p', hp'L, hrp'⟩
    · -- r = ∅ but q ⊆ r ⇒ q = ∅, contradicting hne q hqL
      have : q = ∅ := Set.subset_empty_iff.mp hqr
      exact (hne q hqL this).elim
    · -- r ⊆ p' ∈ L. q ⊆ r ⊆ p'. By disjointness + q nonempty, p' = q.
      have hqp' : q ⊆ p' := hqr.trans hrp'
      by_cases heq : q = p'
      · subst heq; exact Set.Subset.antisymm hqr hrp'
      · have hdj : Disjoint q p' := hdisj q hqL p' hp'L heq
        have hqne : q ≠ ∅ := hne q hqL
        exfalso; apply hqne
        ext w
        refine ⟨fun hw => ?_, fun he => he.elim⟩
        exact (Set.disjoint_left.mp hdj hw (hqp' hw)).elim

/-- **Alternatives of `ofList`** under the antichain condition (no cell
    is contained in another) plus nonemptiness: `alt (ofList L) = {p | p
    ∈ L}`. Weaker than `alt_ofList_of_pairwise_disjoint_nonempty` —
    cells may overlap as long as no cell is a (proper or improper)
    subset of any other distinct cell.

    Use case: question alternatives like "Does shop A sell Italian?",
    "Does shop B sell Italian?" with truth-sets `{A_only, both}` and
    `{B_only, both}`. The two cells overlap on `both` but neither is a
    subset of the other, so they are still maximal alternatives in the
    Hamblin issue. -/
theorem alt_ofList_of_antichain_nonempty
    (L : List (Set W)) (hL : L ≠ [])
    (hac : ∀ p₁ ∈ L, ∀ p₂ ∈ L, p₁ ≠ p₂ → ¬ p₁ ⊆ p₂)
    (hne : ∀ p ∈ L, p ≠ ∅) :
    alt (ofList L) = {p | p ∈ L} := by
  ext q
  rw [Set.mem_setOf_eq, mem_alt]
  constructor
  · rintro ⟨hq, hmax⟩
    rcases mem_ofList.mp hq with rfl | ⟨p, hpL, hqp⟩
    · -- q = ∅: extends to any p ∈ L by ∅ ⊆ p, so maximality forces ∅ = p,
      -- contradicting hne.
      obtain ⟨p, hpL⟩ : ∃ p, p ∈ L := List.exists_mem_of_ne_nil L hL
      have hp_in : p ∈ (ofList L).props :=
        mem_ofList.mpr (Or.inr ⟨p, hpL, Set.Subset.refl p⟩)
      have heq : (∅ : Set W) = p := hmax p hp_in (Set.empty_subset p)
      exact (hne p hpL heq.symm).elim
    · have hp_in : p ∈ (ofList L).props :=
        mem_ofList.mpr (Or.inr ⟨p, hpL, Set.Subset.refl p⟩)
      have hqeq : q = p := hmax p hp_in hqp
      exact hqeq ▸ hpL
  · intro hqL
    refine ⟨mem_ofList.mpr (Or.inr ⟨q, hqL, Set.Subset.refl q⟩), ?_⟩
    intro r hr hqr
    rcases mem_ofList.mp hr with rfl | ⟨p', hp'L, hrp'⟩
    · -- r = ∅ but q ⊆ r ⇒ q = ∅, contradicting hne q hqL
      have : q = ∅ := Set.subset_empty_iff.mp hqr
      exact (hne q hqL this).elim
    · -- r ⊆ p' ∈ L. q ⊆ r ⊆ p'. By antichain: either p' = q (squeeze) or
      -- ¬ q ⊆ p', contradicting q ⊆ p'.
      have hqp' : q ⊆ p' := hqr.trans hrp'
      by_cases heq : q = p'
      · subst heq; exact Set.Subset.antisymm hqr hrp'
      · exact (hac q hqL p' hp'L heq hqp').elim

/-- **Membership in `alt (ofList L)` from per-cell disjointness**: a
    nonempty cell `p ∈ L` is an alternative as long as it is disjoint
    from every *other* cell in `L`. Weaker than full pairwise
    disjointness — useful when only one cell's status is needed. -/
theorem mem_alt_ofList_of_disjoint_others
    {L : List (Set W)} {p : Set W}
    (hp : p ∈ L) (hne : p ≠ ∅)
    (hdisj : ∀ p' ∈ L, p' ≠ p → Disjoint p p') :
    p ∈ alt (ofList L) := by
  rw [mem_alt]
  refine ⟨mem_ofList.mpr (Or.inr ⟨p, hp, Set.Subset.refl p⟩), ?_⟩
  intro q hq hpq
  rcases mem_ofList.mp hq with rfl | ⟨c, hcL, hqc⟩
  · -- q = ∅, contradicts p ⊆ q (since p nonempty)
    have : p ⊆ ∅ := hpq
    exact (hne (Set.subset_empty_iff.mp this)).elim
  · -- q ⊆ c ∈ L. Either c = p (then q = p by squeeze) or c ≠ p
    -- (then p disjoint from c, but p ⊆ q ⊆ c, contradicting p nonempty).
    by_cases heq : c = p
    · subst heq
      exact Set.Subset.antisymm hpq hqc
    · exfalso
      have hpc : p ⊆ c := hpq.trans hqc
      have hdj : Disjoint p c := hdisj c hcL heq
      apply hne
      ext w
      refine ⟨fun hw => ?_, fun he => he.elim⟩
      exact (Set.disjoint_left.mp hdj hw (hpc hw)).elim

/-! ### Lattice-entailment of `polar` from a classified `ofList`

When every cell of `L` is *classified* by `p` (each cell either lies
in `p` or in `pᶜ`), the partition issue `ofList L` lattice-entails
the polar question `polar p`. This subsumes both the partition-cell
case (`p ∈ L`, classification by pairwise disjointness) and the
finer-than-`p` case (`p` is a union of cells of `L`). -/

/-- **Lattice entailment from cell classification**: if every cell of
    `L` lies entirely in `p` or entirely in `pᶜ`, then `ofList L ≤
    polar p`. Captures the Roberts subquestion relation in the
    common case where the wh-question's cells refine the polar
    question's cell.

    Subsumes the older "p ∈ L + pairwise disjoint" formulation:
    pairwise disjointness lets the cell `p ∈ L` itself sit in `p`
    while every other cell is disjoint from `p`, hence in `pᶜ`. -/
theorem ofList_le_polar_of_classified
    (L : List (Set W)) {p : Set W}
    (hclass : ∀ p' ∈ L, p' ⊆ p ∨ p' ⊆ pᶜ) :
    ofList L ≤ polar p := by
  rw [le_def]
  intro q hq
  have hqL : q ∈ ofList L := hq
  rcases mem_ofList.mp hqL with rfl | ⟨p', hp'L, hqp'⟩
  · exact (polar p).contains_empty
  · rw [polar_eq_sup]
    rcases hclass p' hp'L with hp'p | hp'pc
    · exact Or.inl (hqp'.trans hp'p)
    · exact Or.inr (hqp'.trans hp'pc)

/-! ### Inf of two polar questions classified by a partition

When two polar questions `polar p ⊓ polar q` are answered together,
the joint resolution carves the world space into the four "corners"
`p ∩ q`, `p ∩ qᶜ`, `pᶜ ∩ q`, `pᶜ ∩ qᶜ`. Every state resolving both
polars lies in some corner. A wh-question whose cells contain these
corners therefore satisfies `polar p ⊓ polar q ≤ ofList L`. -/

/-- **Membership in `polar p ⊓ polar q`**: a state resolves both
    polar questions iff it is contained in one of the four corners
    `p ∩ q`, `p ∩ qᶜ`, `pᶜ ∩ q`, `pᶜ ∩ qᶜ`. -/
theorem mem_polar_inf_polar_iff {p q σ : Set W} :
    σ ∈ polar p ⊓ polar q ↔
      σ ⊆ p ∩ q ∨ σ ⊆ p ∩ qᶜ ∨ σ ⊆ pᶜ ∩ q ∨ σ ⊆ pᶜ ∩ qᶜ := by
  constructor
  · rintro ⟨hp, hq⟩
    rw [show (polar p) = declarative p ⊔ declarative pᶜ from rfl] at hp
    rw [show (polar q) = declarative q ⊔ declarative qᶜ from rfl] at hq
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact Or.inl (Set.subset_inter hp hq)
    · exact Or.inr (Or.inl (Set.subset_inter hp hq))
    · exact Or.inr (Or.inr (Or.inl (Set.subset_inter hp hq)))
    · exact Or.inr (Or.inr (Or.inr (Set.subset_inter hp hq)))
  · intro h
    refine ⟨?_, ?_⟩ <;> rw [polar_eq_sup]
    · rcases h with h | h | h | h
      · exact Or.inl (h.trans (Set.inter_subset_left))
      · exact Or.inl (h.trans (Set.inter_subset_left))
      · exact Or.inr (h.trans (Set.inter_subset_left))
      · exact Or.inr (h.trans (Set.inter_subset_left))
    · rcases h with h | h | h | h
      · exact Or.inl (h.trans (Set.inter_subset_right))
      · exact Or.inr (h.trans (Set.inter_subset_right))
      · exact Or.inl (h.trans (Set.inter_subset_right))
      · exact Or.inr (h.trans (Set.inter_subset_right))

/-- **Two polar questions ≤ a covering `ofList`**: if all four
    corners of `polar p ⊓ polar q` are contained in cells of `L`,
    then `polar p ⊓ polar q ≤ ofList L`. The Roberts completeness
    fact: pursuing both polar subquestions resolves the wh-question
    they jointly partition. -/
theorem polar_inf_polar_le_ofList_of_corners
    (L : List (Set W)) {p q : Set W}
    (h1 : ∃ c ∈ L, p ∩ q ⊆ c) (h2 : ∃ c ∈ L, p ∩ qᶜ ⊆ c)
    (h3 : ∃ c ∈ L, pᶜ ∩ q ⊆ c) (h4 : ∃ c ∈ L, pᶜ ∩ qᶜ ⊆ c) :
    polar p ⊓ polar q ≤ ofList L := by
  rw [le_def]
  intro σ hσ
  have hσ' := mem_polar_inf_polar_iff.mp hσ
  rw [show (σ ∈ (ofList L).props) = (σ ∈ ofList L) from rfl, mem_ofList]
  rcases hσ' with h | h | h | h
  · obtain ⟨c, hcL, hcle⟩ := h1
    exact Or.inr ⟨c, hcL, h.trans hcle⟩
  · obtain ⟨c, hcL, hcle⟩ := h2
    exact Or.inr ⟨c, hcL, h.trans hcle⟩
  · obtain ⟨c, hcL, hcle⟩ := h3
    exact Or.inr ⟨c, hcL, h.trans hcle⟩
  · obtain ⟨c, hcL, hcle⟩ := h4
    exact Or.inr ⟨c, hcL, h.trans hcle⟩

end Question

end Core
