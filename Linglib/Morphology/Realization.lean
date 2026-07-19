/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

/-!
# Root realizations: indices realized in context

Every realizational/separationist framework that adopts late insertion or a
separate lexemic index factors a root into an opaque individuator plus
context-sensitive form and (optionally) meaning maps: DM's √ individuated by
arbitrary indices, form at Vocabulary Insertion ([harley-2014],
[marantz-1997], [embick-2021]); [borer-2013]'s phonological indices (her form
individuation `R ↪ F` is her instance's axiom, not the interface's); PFM's
opaque lexeme realized at a cell ([stump-2001], [bonami-stump-2016]);
[spencer-2013]'s lexemic index. [beard-1995]'s Separation Hypothesis grounds
the form-side separation; the meaning-side separation is DM's List-3 move.
`Realization` fixes that object; sign-based lexicalism, Construction
Morphology, and [haspelmath-2025-root]'s morph-based comparative root are
rival ontologies its parameters measure, not instances of it (survey:
[lohndal-2020]). The interface is agnostic about whether indices are listed
or constructed ([blevins-2016]).

`realize` is `Finset`-valued: the empty fiber is non-licensing, a
non-singleton an overabundant cell, matching `Paradigm/Linkage.lean`; the
univalent and total strata are `IsUnivalent` and `IsTotal`. Frameworks
diverge along parameters — what `R` individuates (√, lexeme, morph), what
`Ctx` is (categorizer configuration vs paradigm cell — vs [borer-2013]'s
headless categorial frames, a Ctx-instantiation contrast; [lohndal-2020]),
what `F` is (`ConsonantalRoot α` is a choice of `F`), whether interpretation
is present (`Realization.Interpreted`) — never along the core.

`Hom` merges indices with a context translation that may consult the source
index; `Realization.Interpreted.Hom` is the strict tier — root-independent context
translation, interpretation-preserving — on which individuation disputes are
stated: merged indices must share their whole profile
(`Hom.profileEq_of_onRoot_eq`), so strict mergers collapse only exact
profile-duplicates and `Interpreted.reduce` is terminal among them. The
individuation rivalries live at the lax tier, where fat-root and sister-root
presentations subsume each other's data: extensional profiles underdetermine
individuation, and the discriminators the literature actually uses —
first-categorization locality ([arad-2005]), the denial that indices are
linguistic objects, processing evidence — are extra structure on admissible
mergers that studies supply. The interface localizes the dispute precisely
because it cannot resolve it. One mild theory-ladenness to note: the strict
tier's root-independent context translation forces categorial information
into `Ctx`, quietly encoding the Categorization Assumption.

## Main declarations

* `Realization` — indices with contextual realization; `IsLicensed`, `Realizes`,
  `exponents`, `IsTotal`, `IsUnivalent`.
* `IsConstantIn` / `IsVariantIn` — the constancy pair over any
  contextual map; instantiated as `IsInvariant`/`IsSuppletive` (form) and
  `IsIntrinsic`/`IsAllosemous` (meaning).
* `Realization.RealizeEq`, `Realization.IsHomophonous` — form identity vs index
  identity.
* `Realization.Hom` — index mergers with realization tracking; `Interpreted.Hom` —
  the strict, interpretation-preserving tier;
  `Realization.Interpreted.Hom.interp_eq_of_onRoot_eq`.
* `Realization.Interpreted` — the two-map extension ([marantz-1997]'s List 2 / List 3).
* `Realization.comp` — Kleisli pipelining; `Interpreted.ProfileEq`,
  `Interpreted.reduce`, `Hom.profileEq_of_onRoot_eq` — the reduced
  presentation and the strict-merger bound.
-/

namespace Morphology

variable {R Ctx F M X : Type*}

/-- Constancy of a contextual map at an index: all values, across all
contexts, coincide. -/
def IsConstantIn (g : R → Ctx → Finset X) (r : R) : Prop :=
  ∀ ⦃c c' : Ctx⦄, ∀ x ∈ g r c, ∀ x' ∈ g r c', x = x'

/-- Variance of a contextual map at an index: two distinct values arise. -/
def IsVariantIn (g : R → Ctx → Finset X) (r : R) : Prop :=
  ∃ c c', ∃ x ∈ g r c, ∃ x' ∈ g r c', x ≠ x'

theorem not_isConstantIn_of_isVariantIn {g : R → Ctx → Finset X} {r : R}
    (h : IsVariantIn g r) : ¬ IsConstantIn g r := by
  obtain ⟨c, c', x, hx, x', hx', hne⟩ := h
  exact fun hc => hne (hc x hx x' hx')

/-- Constancy at an index is subsingletonhood of the index's total image —
the bridge to mathlib's `Set.Subsingleton` ecosystem. -/
theorem isConstantIn_iff_subsingleton {g : R → Ctx → Finset X} {r : R} :
    IsConstantIn g r ↔ {x | ∃ c, x ∈ g r c}.Subsingleton := by
  constructor
  · rintro h x ⟨c, hx⟩ x' ⟨c', hx'⟩
    exact h x hx x' hx'
  · intro h c c' x hx x' hx'
    exact h ⟨c, hx⟩ ⟨c', hx'⟩

/-- A **root realization**: an opaque index type realized in context. The
fiber `realize r c` is empty where `r` is unlicensed, non-singleton at an
overabundant cell. -/
structure Realization (R Ctx F : Type*) where
  /-- The realization of an index in a context: Vocabulary Insertion (DM),
  the paradigm function (PFM), spellout (nanosyntax). -/
  realize : R → Ctx → Finset F

namespace Realization

variable (S : Realization R Ctx F)

/-- `r` is licensed in `c`: some realization exists. -/
def IsLicensed (r : R) (c : Ctx) : Prop := (S.realize r c).Nonempty

/-- `f` realizes `r` in some context. -/
def Realizes (r : R) (f : F) : Prop := ∃ c, f ∈ S.realize r c

/-- The allomorph set of a root. -/
def exponents (r : R) : Set F := {f | S.Realizes r f}

@[simp] theorem mem_exponents {r : R} {f : F} :
    f ∈ S.exponents r ↔ S.Realizes r f := Iff.rfl

/-- Every index is licensed everywhere — PFM's stratum. -/
def IsTotal : Prop := ∀ r c, (S.realize r c).Nonempty

/-- At most one form per cell — the stratum of `Option`-shaped engine
outputs. -/
def IsUnivalent : Prop := ∀ r c, (S.realize r c).card ≤ 1

/-- One form wherever licensed: the classical context-free morpheme, as the
degenerate case. -/
def IsInvariant (r : R) : Prop := IsConstantIn S.realize r

/-- Distinct forms in distinct contexts — √GO as *go* and *went*,
[harley-2014]'s argument that indices, not forms, individuate. -/
def IsSuppletive (r : R) : Prop := IsVariantIn S.realize r

/-- A suppletive root is not invariant. -/
theorem not_isInvariant_of_isSuppletive {r : R} (h : S.IsSuppletive r) :
    ¬ S.IsInvariant r :=
  not_isConstantIn_of_isVariantIn h

/-- Invariance is subsingletonhood of the allomorph set. -/
theorem isInvariant_iff_subsingleton_exponents {r : R} :
    S.IsInvariant r ↔ (S.exponents r).Subsingleton :=
  isConstantIn_iff_subsingleton

/-- Overabundance at an index: some cell offers two forms (*dived*/*dove* in
one cell, [thornton-2011]-style — cf. `Linkage.HasCellMates`). Cell-internal
variance, disjoint in kind from suppletion. -/
def IsOverabundant (r : R) : Prop := ∃ c, 1 < (S.realize r c).card

/-- Suppletion proper: two licensed contexts realized by different fibers
(√GO: *go*/*went*). An unlicensed cell never witnesses it. -/
def IsProperlySuppletive (r : R) : Prop :=
  ∃ c c', (S.realize r c).Nonempty ∧ (S.realize r c').Nonempty ∧
    S.realize r c ≠ S.realize r c'

/-- The variance decomposition: form variance at an index is overabundance
or suppletion proper. -/
theorem isSuppletive_iff {r : R} :
    S.IsSuppletive r ↔ S.IsOverabundant r ∨ S.IsProperlySuppletive r := by
  constructor
  · rintro ⟨c, c', x, hx, x', hx', hne⟩
    by_cases hfib : S.realize r c = S.realize r c'
    · exact Or.inl ⟨c, Finset.one_lt_card.mpr ⟨x, hx, x', hfib ▸ hx', hne⟩⟩
    · exact Or.inr ⟨c, c', ⟨x, hx⟩, ⟨x', hx'⟩, hfib⟩
  · rintro (⟨c, hc⟩ | ⟨c, c', ⟨x, hx⟩, ⟨x', hx'⟩, hne⟩)
    · obtain ⟨y, hy, y', hy', hne⟩ := Finset.one_lt_card.mp hc
      exact ⟨c, c, y, hy, y', hy', hne⟩
    · by_cases hsub : S.realize r c ⊆ S.realize r c'
      · have hns : ¬ S.realize r c' ⊆ S.realize r c :=
          fun h => hne (Finset.Subset.antisymm hsub h)
        obtain ⟨y, hy, hy'⟩ := Finset.not_subset.mp hns
        exact ⟨c', c, y, hy, x, hx, fun h => hy' (h ▸ hx)⟩
      · obtain ⟨y, hy, hy'⟩ := Finset.not_subset.mp hsub
        exact ⟨c, c', y, hy, x', hx', fun h => hy' (h ▸ hx')⟩

/-- Contextwise identity of realization. -/
def RealizeEq (r r' : R) : Prop := ∀ c, S.realize r c = S.realize r' c

theorem RealizeEq.symm {r r' : R} (h : S.RealizeEq r r') :
    S.RealizeEq r' r := fun c => (h c).symm

/-- Distinct indices sharing every realization (*bank₁*/*bank₂*): spellout is
nowhere required to be injective. -/
def IsHomophonous (r r' : R) : Prop := r ≠ r' ∧ S.RealizeEq r r'

theorem IsHomophonous.symm {r r' : R} (h : S.IsHomophonous r r') :
    S.IsHomophonous r' r :=
  ⟨h.1.symm, fun c => (h.2 c).symm⟩

section Decidable

variable [Fintype Ctx] [DecidableEq F]

instance (r : R) (c : Ctx) : Decidable (S.IsLicensed r c) :=
  inferInstanceAs (Decidable (S.realize r c).Nonempty)

instance (r : R) (f : F) : Decidable (S.Realizes r f) :=
  inferInstanceAs (Decidable (∃ c, f ∈ S.realize r c))

instance (r : R) : Decidable (S.IsInvariant r) :=
  inferInstanceAs (Decidable (∀ c c' : Ctx,
    ∀ x ∈ S.realize r c, ∀ x' ∈ S.realize r c', x = x'))

instance (r : R) : Decidable (S.IsSuppletive r) :=
  inferInstanceAs (Decidable (∃ c c',
    ∃ x ∈ S.realize r c, ∃ x' ∈ S.realize r c', x ≠ x'))

instance (r : R) : Decidable (S.IsOverabundant r) :=
  inferInstanceAs (Decidable (∃ c, 1 < (S.realize r c).card))

instance (r : R) : Decidable (S.IsProperlySuppletive r) :=
  inferInstanceAs (Decidable (∃ c c', (S.realize r c).Nonempty ∧
    (S.realize r c').Nonempty ∧ S.realize r c ≠ S.realize r c'))

instance (r r' : R) : Decidable (S.RealizeEq r r') :=
  inferInstanceAs (Decidable (∀ c : Ctx, S.realize r c = S.realize r' c))

instance [DecidableEq R] (r r' : R) : Decidable (S.IsHomophonous r r') :=
  inferInstanceAs (Decidable (_ ∧ _))

variable [Fintype R]

instance : Decidable S.IsTotal :=
  inferInstanceAs (Decidable (∀ r c, (S.realize r c).Nonempty))

instance : Decidable S.IsUnivalent :=
  inferInstanceAs (Decidable (∀ r c, (S.realize r c).card ≤ 1))

end Decidable

/-- Pipeline composition — Kleisli of `Finset` over a shared context:
realize through an intermediate inventory. Late-insertion architectures
factor the grammar's realization as such a composite; PFM's
stem-choice-then-blocks cascade is another. -/
def comp {G : Type*} [DecidableEq G] (S : Realization R Ctx F)
    (T : Realization F Ctx G) : Realization R Ctx G :=
  ⟨fun r c => (S.realize r c).biUnion (fun f => T.realize f c)⟩

/-- Totality is closed under pipelining. -/
theorem comp_isTotal {G : Type*} [DecidableEq G] {S : Realization R Ctx F}
    {T : Realization F Ctx G} (hS : S.IsTotal) (hT : T.IsTotal) :
    (S.comp T).IsTotal := by
  intro r c
  obtain ⟨f, hf⟩ := hS r c
  obtain ⟨g, hg⟩ := hT f c
  exact ⟨g, Finset.mem_biUnion.mpr ⟨f, hf, hg⟩⟩

section Hom

variable {R₁ C₁ R₂ C₂ R₃ C₃ : Type*}

/-- An index merger with spellout tracking: `onRoot` may merge indices,
`onCtx` translates contexts and may consult the source index. The transport
tier — for adjudicating individuation disputes use `Realization.Interpreted.Hom`, whose
root-independent context translation blocks re-encoding the source index in
the target context. -/
structure Hom (S : Realization R₁ C₁ F) (T : Realization R₂ C₂ F) where
  /-- The index translation; non-injectivity is individuation coarsening. -/
  onRoot : R₁ → R₂
  /-- The context translation. -/
  onCtx : R₁ → C₁ → C₂
  /-- Realization is preserved. -/
  realize_eq : ∀ r c, S.realize r c = T.realize (onRoot r) (onCtx r c)

/-- The identity hom. -/
def Hom.id (S : Realization R Ctx F) : Hom S S :=
  ⟨fun r => r, fun _ c => c, fun _ _ => rfl⟩

/-- Homs compose: coarsenings chain (morph-level to lexeme-level to
√-level). -/
def Hom.comp {S₁ : Realization R₁ C₁ F} {S₂ : Realization R₂ C₂ F}
    {S₃ : Realization R₃ C₃ F} (g : Hom S₂ S₃) (f : Hom S₁ S₂) : Hom S₁ S₃ :=
  ⟨fun r => g.onRoot (f.onRoot r),
   fun r c => g.onCtx (f.onRoot r) (f.onCtx r c),
   fun r c => (f.realize_eq r c).trans
     (g.realize_eq (f.onRoot r) (f.onCtx r c))⟩

/-- Homs preserve licensing. -/
theorem Hom.isLicensed {S : Realization R₁ C₁ F} {T : Realization R₂ C₂ F}
    (φ : Hom S T) {r : R₁} {c : C₁} (h : S.IsLicensed r c) :
    T.IsLicensed (φ.onRoot r) (φ.onCtx r c) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, φ.realize_eq r c ▸ hf⟩

/-- Homs preserve realization: merging indices can only grow allomorph
sets. -/
theorem Hom.realizes {S : Realization R₁ C₁ F} {T : Realization R₂ C₂ F}
    (φ : Hom S T) {r : R₁} {f : F} (h : S.Realizes r f) :
    T.Realizes (φ.onRoot r) f := by
  obtain ⟨c, hc⟩ := h
  exact ⟨φ.onCtx r c, φ.realize_eq r c ▸ hc⟩

end Hom

end Realization

/-- The two-map extension ([marantz-1997]: spellout is List 2, `interp` List
3 — allosemy, `DM/Allosemy.lean`). A [borer-2013]-style system stays a bare
`System`; a lexicalist lexeme is an `Interpreted` system whose interpretation
is `IsIntrinsic`. -/
structure Realization.Interpreted (R Ctx F M : Type*) extends
    Realization R Ctx F where
  /-- Contextual interpretation: Encyclopedia access. -/
  interp : R → Ctx → Finset M

namespace Realization.Interpreted

variable (S : Interpreted R Ctx F M)

/-- One meaning in every context: the lexicalist degenerate case. -/
def IsIntrinsic (r : R) : Prop := IsConstantIn S.interp r

/-- Context-dependent interpretation: DM allosemy, its failure. -/
def IsAllosemous (r : R) : Prop := IsVariantIn S.interp r

/-- An allosemous root has no intrinsic meaning. -/
theorem not_isIntrinsic_of_isAllosemous {r : R} (h : S.IsAllosemous r) :
    ¬ S.IsIntrinsic r :=
  not_isConstantIn_of_isVariantIn h

instance [Fintype Ctx] [DecidableEq M] (r : R) : Decidable (S.IsIntrinsic r) :=
  inferInstanceAs (Decidable (∀ c c' : Ctx,
    ∀ x ∈ S.interp r c, ∀ x' ∈ S.interp r c', x = x'))

instance [Fintype Ctx] [DecidableEq M] (r : R) :
    Decidable (S.IsAllosemous r) :=
  inferInstanceAs (Decidable (∃ c c',
    ∃ x ∈ S.interp r c, ∃ x' ∈ S.interp r c', x ≠ x'))

section Hom

variable {R₁ C₁ R₂ C₂ : Type*}

/-- The strict tier of hom, on which individuation disputes are stated: the
context translation is root-independent — so the target context cannot
re-encode the source index — and interpretation is preserved alongside
spellout. -/
structure Hom (S : Interpreted R₁ C₁ F M) (T : Interpreted R₂ C₂ F M) where
  /-- The index translation. -/
  onRoot : R₁ → R₂
  /-- The root-independent context translation. -/
  onCtx : C₁ → C₂
  /-- Realization is preserved. -/
  realize_eq : ∀ r c, S.realize r c = T.realize (onRoot r) (onCtx c)
  /-- Interpretation is preserved. -/
  interp_eq : ∀ r c, S.interp r c = T.interp (onRoot r) (onCtx c)

/-- A strict hom is in particular a realization hom. -/
def Hom.toRealizationHom {S : Interpreted R₁ C₁ F M} {T : Interpreted R₂ C₂ F M}
    (φ : Hom S T) : Realization.Hom S.toRealization T.toRealization :=
  ⟨φ.onRoot, fun _ c => φ.onCtx c, φ.realize_eq⟩

/-- **Merged roots agree contextwise in interpretation** — the keystone
separating identity from accidental homophony: a strict hom identifying two
indices forces their interpretations to coincide in every context, so
*bank₁*/*bank₂* never merge. -/
theorem Hom.interp_eq_of_onRoot_eq {S : Interpreted R₁ C₁ F M}
    {T : Interpreted R₂ C₂ F M} (φ : Hom S T) {r r' : R₁}
    (h : φ.onRoot r = φ.onRoot r') (c : C₁) :
    S.interp r c = S.interp r' c := by
  rw [φ.interp_eq r c, φ.interp_eq r' c, h]

/-- The realization analog of `interp_eq_of_onRoot_eq`: merged roots agree
contextwise in realization. Unavailable for the transport tier
`Realization.Hom`, whose index-dependent context translation can separate the
merged roots' contexts. -/
theorem Hom.realize_eq_of_onRoot_eq {S : Interpreted R₁ C₁ F M}
    {T : Interpreted R₂ C₂ F M} (φ : Hom S T) {r r' : R₁}
    (h : φ.onRoot r = φ.onRoot r') (c : C₁) :
    S.realize r c = S.realize r' c := by
  rw [φ.realize_eq r c, φ.realize_eq r' c, h]

/-- The lax tier: realization and interpretation are *included* rather than
matched. Where a strict `Hom` merger asserts identity, a lax merger asserts
subsumption — each source index's forms and readings are among its image's,
as when a lexeme's listed properties are among its root's Encyclopedia entry
([arad-2005]). Pattern-bound lexemes lax-merge into a total root without
ever strict-merging. -/
structure LaxHom (S : Interpreted R₁ C₁ F M) (T : Interpreted R₂ C₂ F M) where
  /-- The index translation. -/
  onRoot : R₁ → R₂
  /-- The root-independent context translation. -/
  onCtx : C₁ → C₂
  /-- Realizations are included. -/
  realize_sub : ∀ r c, S.realize r c ⊆ T.realize (onRoot r) (onCtx c)
  /-- Interpretations are included. -/
  interp_sub : ∀ r c, S.interp r c ⊆ T.interp (onRoot r) (onCtx c)

/-- A strict hom is in particular lax. -/
def Hom.toLaxHom {S : Interpreted R₁ C₁ F M} {T : Interpreted R₂ C₂ F M}
    (φ : Hom S T) : LaxHom S T :=
  ⟨φ.onRoot, φ.onCtx, fun r c => (φ.realize_eq r c).le,
   fun r c => (φ.interp_eq r c).le⟩

/-- Lax homs compose. -/
def LaxHom.comp {R₃ C₃ : Type*} {S₁ : Interpreted R₁ C₁ F M}
    {S₂ : Interpreted R₂ C₂ F M} {S₃ : Interpreted R₃ C₃ F M}
    (g : LaxHom S₂ S₃) (f : LaxHom S₁ S₂) : LaxHom S₁ S₃ :=
  ⟨fun r => g.onRoot (f.onRoot r), fun c => g.onCtx (f.onCtx c),
   fun r c =>
     (f.realize_sub r c).trans (g.realize_sub (f.onRoot r) (f.onCtx c)),
   fun r c =>
     (f.interp_sub r c).trans (g.interp_sub (f.onRoot r) (f.onCtx c))⟩

end Hom

/-- Contextwise indistinguishability of indices: equal realization and
interpretation profiles. -/
def ProfileEq (r r' : R) : Prop :=
  (∀ c, S.realize r c = S.realize r' c) ∧ (∀ c, S.interp r c = S.interp r' c)

/-- Profile equality as a setoid. -/
def profileSetoid : Setoid R where
  r := S.ProfileEq
  iseqv :=
    ⟨fun _ => ⟨fun _ => rfl, fun _ => rfl⟩,
     fun h => ⟨fun c => (h.1 c).symm, fun c => (h.2 c).symm⟩,
     fun h h' => ⟨fun c => (h.1 c).trans (h'.1 c),
                  fun c => (h.2 c).trans (h'.2 c)⟩⟩

/-- The reduced presentation: indices are realization-and-interpretation
profiles. Every system presents its reduction; the strict hom tier is
change of presentation, and only the lax tier merges beyond profiles. -/
def reduce : Interpreted (Quotient S.profileSetoid) Ctx F M where
  realize := Quotient.lift S.realize (fun _ _ h => funext h.1)
  interp := Quotient.lift S.interp (fun _ _ h => funext h.2)

/-- Reduction is a strict hom: passing to profiles loses nothing. -/
def reduceHom : Hom S S.reduce :=
  ⟨Quotient.mk S.profileSetoid, id, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Mergers along any strict hom refine profile equality: `reduce` merges
as much as the strict tier ever can. Mergers beyond profiles — the *hammer*
carvings, pattern-bound lexemes into an [arad-2005] root — are necessarily
lax. -/
theorem Hom.profileEq_of_onRoot_eq {R₂ C₂ : Type*}
    {T : Interpreted R₂ C₂ F M} (φ : Hom S T) {r r' : R}
    (h : φ.onRoot r = φ.onRoot r') : S.ProfileEq r r' :=
  ⟨fun c => φ.realize_eq_of_onRoot_eq h c,
   fun c => φ.interp_eq_of_onRoot_eq h c⟩

end Realization.Interpreted

end Morphology
