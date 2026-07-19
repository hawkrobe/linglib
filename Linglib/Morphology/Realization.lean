/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Finset.Card

/-!
# Root systems: indices with contextual realization

Every realizational/separationist framework that adopts late insertion or a
separate lexemic index factors a root into an opaque individuator plus
context-sensitive form and (optionally) meaning maps: DM's √ individuated by
arbitrary indices, form at Vocabulary Insertion ([harley-2014],
[marantz-1997], [embick-2021]); [borer-2013]'s phonological indices (her form
individuation `R ↪ F` is her instance's axiom, not the interface's); PFM's
opaque lexeme realized at a cell ([stump-2001], [bonami-stump-2016]);
[spencer-2013]'s lexemic index. [beard-1995]'s Separation Hypothesis grounds
the form-side separation; the meaning-side separation is DM's List-3 move.
`Root.System` fixes that object; sign-based lexicalism, Construction
Morphology, and [haspelmath-2025-root]'s morph-based comparative root are
rival ontologies its parameters measure, not instances of it (survey:
[lohndal-2020]). The interface is agnostic about whether indices are listed
or constructed ([blevins-2016]).

`spellout` is `Finset`-valued: the empty fiber is non-licensing, a
non-singleton an overabundant cell, matching `Paradigm/Linkage.lean`; the
univalent and total strata are `IsUnivalent` and `IsTotal`. Frameworks
diverge along parameters — what `R` individuates (√, lexeme, morph), what
`Ctx` is (categorizer configuration vs paradigm cell — vs [borer-2013]'s
headless categorial frames, a Ctx-instantiation contrast; [lohndal-2020]),
what `F` is (`ConsonantalRoot α` is a choice of `F`), whether interpretation
is present (`Interpreted`) — never along the core.

`Hom` merges indices with a context translation that may consult the source
index; `Interpreted.Hom` is the strict tier — root-independent context
translation, interpretation-preserving — on which individuation disputes are
stated: merged roots must agree contextwise in interpretation
(`interp_eq_of_onRoot_eq`), so accidental homophones never merge, and
heterosemy-vs-single-√ rivalries become hom-(non)existence theorems in
studies.

## Main declarations

* `Root.System` — indices with contextual spellout; `IsLicensed`, `Realizes`,
  `exponents`, `IsTotal`, `IsUnivalent`.
* `Root.IsConstantIn` / `Root.IsVariantIn` — the constancy pair over any
  contextual map; instantiated as `IsInvariant`/`IsSuppletive` (form) and
  `IsIntrinsic`/`IsAllosemous` (meaning).
* `System.SpelloutEq`, `System.IsHomophonous` — form identity vs index
  identity.
* `System.Hom` — index mergers with spellout tracking; `Interpreted.Hom` —
  the strict, interpretation-preserving tier;
  `Interpreted.Hom.interp_eq_of_onRoot_eq`.
* `Interpreted` — the two-map extension ([marantz-1997]'s List 2 / List 3).
-/

namespace Morphology.Root

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

/-- A **root system**: an opaque index type realized in context. The fiber
`spellout r c` is empty where `r` is unlicensed, non-singleton at an
overabundant cell. -/
structure System (R Ctx F : Type*) where
  /-- The realization of an index in a context: Vocabulary Insertion (DM),
  the paradigm function (PFM), spellout (nanosyntax). -/
  spellout : R → Ctx → Finset F

namespace System

variable (S : System R Ctx F)

/-- `r` is licensed in `c`: some realization exists. -/
def IsLicensed (r : R) (c : Ctx) : Prop := (S.spellout r c).Nonempty

/-- `f` realizes `r` in some context. -/
def Realizes (r : R) (f : F) : Prop := ∃ c, f ∈ S.spellout r c

/-- The allomorph set of a root. -/
def exponents (r : R) : Set F := {f | S.Realizes r f}

@[simp] theorem mem_exponents {r : R} {f : F} :
    f ∈ S.exponents r ↔ S.Realizes r f := Iff.rfl

/-- Every index is licensed everywhere — PFM's stratum. -/
def IsTotal : Prop := ∀ r c, (S.spellout r c).Nonempty

/-- At most one form per cell — the stratum of `Option`-shaped engine
outputs. -/
def IsUnivalent : Prop := ∀ r c, (S.spellout r c).card ≤ 1

/-- One form wherever licensed: the classical context-free morpheme, as the
degenerate case. -/
def IsInvariant (r : R) : Prop := IsConstantIn S.spellout r

/-- Distinct forms in distinct contexts — √GO as *go* and *went*,
[harley-2014]'s argument that indices, not forms, individuate. -/
def IsSuppletive (r : R) : Prop := IsVariantIn S.spellout r

/-- A suppletive root is not invariant. -/
theorem not_isInvariant_of_isSuppletive {r : R} (h : S.IsSuppletive r) :
    ¬ S.IsInvariant r :=
  not_isConstantIn_of_isVariantIn h

/-- Contextwise identity of realization. -/
def SpelloutEq (r r' : R) : Prop := ∀ c, S.spellout r c = S.spellout r' c

theorem SpelloutEq.symm {r r' : R} (h : S.SpelloutEq r r') :
    S.SpelloutEq r' r := fun c => (h c).symm

/-- Distinct indices sharing every realization (*bank₁*/*bank₂*): spellout is
nowhere required to be injective. -/
def IsHomophonous (r r' : R) : Prop := r ≠ r' ∧ S.SpelloutEq r r'

theorem IsHomophonous.symm {r r' : R} (h : S.IsHomophonous r r') :
    S.IsHomophonous r' r :=
  ⟨h.1.symm, fun c => (h.2 c).symm⟩

section Decidable

variable [Fintype Ctx] [DecidableEq F]

instance (r : R) (c : Ctx) : Decidable (S.IsLicensed r c) :=
  inferInstanceAs (Decidable (S.spellout r c).Nonempty)

instance (r : R) (f : F) : Decidable (S.Realizes r f) :=
  inferInstanceAs (Decidable (∃ c, f ∈ S.spellout r c))

instance (r : R) : Decidable (S.IsInvariant r) :=
  inferInstanceAs (Decidable (∀ c c' : Ctx,
    ∀ x ∈ S.spellout r c, ∀ x' ∈ S.spellout r c', x = x'))

instance (r : R) : Decidable (S.IsSuppletive r) :=
  inferInstanceAs (Decidable (∃ c c',
    ∃ x ∈ S.spellout r c, ∃ x' ∈ S.spellout r c', x ≠ x'))

instance (r r' : R) : Decidable (S.SpelloutEq r r') :=
  inferInstanceAs (Decidable (∀ c : Ctx, S.spellout r c = S.spellout r' c))

instance [DecidableEq R] (r r' : R) : Decidable (S.IsHomophonous r r') :=
  inferInstanceAs (Decidable (_ ∧ _))

variable [Fintype R]

instance : Decidable S.IsTotal :=
  inferInstanceAs (Decidable (∀ r c, (S.spellout r c).Nonempty))

instance : Decidable S.IsUnivalent :=
  inferInstanceAs (Decidable (∀ r c, (S.spellout r c).card ≤ 1))

end Decidable

section Hom

variable {R₁ C₁ R₂ C₂ R₃ C₃ : Type*}

/-- An index merger with spellout tracking: `onRoot` may merge indices,
`onCtx` translates contexts and may consult the source index. The transport
tier — for adjudicating individuation disputes use `Interpreted.Hom`, whose
root-independent context translation blocks re-encoding the source index in
the target context. -/
structure Hom (S : System R₁ C₁ F) (T : System R₂ C₂ F) where
  /-- The index translation; non-injectivity is individuation coarsening. -/
  onRoot : R₁ → R₂
  /-- The context translation. -/
  onCtx : R₁ → C₁ → C₂
  /-- Realization is preserved. -/
  spellout_eq : ∀ r c, S.spellout r c = T.spellout (onRoot r) (onCtx r c)

/-- The identity hom. -/
def Hom.id (S : System R Ctx F) : Hom S S :=
  ⟨fun r => r, fun _ c => c, fun _ _ => rfl⟩

/-- Homs compose: coarsenings chain (morph-level to lexeme-level to
√-level). -/
def Hom.comp {S₁ : System R₁ C₁ F} {S₂ : System R₂ C₂ F}
    {S₃ : System R₃ C₃ F} (g : Hom S₂ S₃) (f : Hom S₁ S₂) : Hom S₁ S₃ :=
  ⟨fun r => g.onRoot (f.onRoot r),
   fun r c => g.onCtx (f.onRoot r) (f.onCtx r c),
   fun r c => (f.spellout_eq r c).trans
     (g.spellout_eq (f.onRoot r) (f.onCtx r c))⟩

/-- Homs preserve licensing. -/
theorem Hom.isLicensed {S : System R₁ C₁ F} {T : System R₂ C₂ F}
    (φ : Hom S T) {r : R₁} {c : C₁} (h : S.IsLicensed r c) :
    T.IsLicensed (φ.onRoot r) (φ.onCtx r c) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, φ.spellout_eq r c ▸ hf⟩

/-- Homs preserve realization: merging indices can only grow allomorph
sets. -/
theorem Hom.realizes {S : System R₁ C₁ F} {T : System R₂ C₂ F}
    (φ : Hom S T) {r : R₁} {f : F} (h : S.Realizes r f) :
    T.Realizes (φ.onRoot r) f := by
  obtain ⟨c, hc⟩ := h
  exact ⟨φ.onCtx r c, φ.spellout_eq r c ▸ hc⟩

end Hom

end System

/-- The two-map extension ([marantz-1997]: spellout is List 2, `interp` List
3 — allosemy, `DM/Allosemy.lean`). A [borer-2013]-style system stays a bare
`System`; a lexicalist lexeme is an `Interpreted` system whose interpretation
is `IsIntrinsic`. -/
structure Interpreted (R Ctx F M : Type*) extends System R Ctx F where
  /-- Contextual interpretation: Encyclopedia access. -/
  interp : R → Ctx → Finset M

namespace Interpreted

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
  spellout_eq : ∀ r c, S.spellout r c = T.spellout (onRoot r) (onCtx c)
  /-- Interpretation is preserved. -/
  interp_eq : ∀ r c, S.interp r c = T.interp (onRoot r) (onCtx c)

/-- A strict hom is in particular a system hom. -/
def Hom.toSystemHom {S : Interpreted R₁ C₁ F M} {T : Interpreted R₂ C₂ F M}
    (φ : Hom S T) : System.Hom S.toSystem T.toSystem :=
  ⟨φ.onRoot, fun _ c => φ.onCtx c, φ.spellout_eq⟩

/-- **Merged roots agree contextwise in interpretation** — the keystone
separating identity from accidental homophony: a strict hom identifying two
indices forces their interpretations to coincide in every context, so
*bank₁*/*bank₂* never merge. -/
theorem Hom.interp_eq_of_onRoot_eq {S : Interpreted R₁ C₁ F M}
    {T : Interpreted R₂ C₂ F M} (φ : Hom S T) {r r' : R₁}
    (h : φ.onRoot r = φ.onRoot r') (c : C₁) :
    S.interp r c = S.interp r' c := by
  rw [φ.interp_eq r c, φ.interp_eq r' c, h]

/-- The spellout analog of `interp_eq_of_onRoot_eq`: merged roots agree
contextwise in realization. Unavailable for the transport tier
`System.Hom`, whose index-dependent context translation can separate the
merged roots' contexts. -/
theorem Hom.spellout_eq_of_onRoot_eq {S : Interpreted R₁ C₁ F M}
    {T : Interpreted R₂ C₂ F M} (φ : Hom S T) {r r' : R₁}
    (h : φ.onRoot r = φ.onRoot r') (c : C₁) :
    S.spellout r c = S.spellout r' c := by
  rw [φ.spellout_eq r c, φ.spellout_eq r' c, h]

end Hom

end Interpreted

end Morphology.Root
