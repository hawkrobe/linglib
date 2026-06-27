import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Real.Basic

/-!
# Discriminative Lexicon Model — substrate
[baayen-2019] [heitmeier-chuang-baayen-2026]
[chuang-bell-tseng-baayen-2026] [lu-chuang-baayen-2026]

The **Discriminative Lexicon Model** (DLM) is a theory of *lexical
processing* in which form ↔ meaning relations are mediated by error-
driven networks rather than by stored lexical entries
([baayen-2019]). This file lifts the DLM substrate out of the
two paper-anchored Studies files that introduced it
(`Studies/ChuangEtAl2026.lean`,
`Studies/LuChuangBaayen2026.lean`) into a shared
location. The substrate has graduated to `Theories/` per `CLAUDE.md`'s
≥ 2-consumer rule.

## Architectural placement: Processing/Lexical, not Lexicon

The DLM is housed under `Processing/Lexical/` rather than
under a hypothetical `Theories/Lexicon/` for a substantive reason:
the DLM **denies** that there is a separable lexicon to theorize
about — its central architectural commitment is that the lexicon-as-
stored-inventory does not exist; only the connection weights of
comprehension and production networks do ([baayen-2019],
abstract; see also the discussion in [lu-chuang-baayen-2026] §5
on word-and-paradigm processing). Filing the DLM under "Lexicon"
would commit linglib to the very architecture the model rejects. By
contrast, the DLM is unambiguously a *processing* theory in the sense
of `Processing/`: it specifies how form vectors map to
meaning vectors and back, with the network weights as the operative
computational object.

The `Lexical/` parent groups DLM with future lexical-processing
sibling theories (e.g. WEAVER++ lexical-access models, Dell-style
spreading-activation, race / dual-route models, exemplar-based
lexical access). All such theories share the architectural concern
of how form ↔ meaning links are *processed*; they may disagree on
whether items are stored.

This means frequency-channel theories of a stored lexicon ([zuraw-2000],
[pater-2010], [coetzee-pater-2008], [moore-cantwell-2021]; see
`Studies/BreissKatsudaKawahara2026.lean`) and
`Morphology/UsageBased/Network.lean` (Bybee 1985 dynamic
network: [bybee-1985]) intentionally do **not** sit alongside
DLM here — they make positive lexicon-architecture commitments and
belong with the linguistic level whose generalisations they primarily
explain.

## What is in this file

- `LinearDiscriminativeLexicon R F M` — a pair of `LinearMap`s between
  form and meaning vector spaces; carrier-typed (mathlib-canonical),
  applies to any `[Module R F]`/`[Module R M]` pair.
- `FormVec`/`MeaningVec` — convenience `Fin n → ℝ` abbrevs for the
  Studies-file specialisation.
- `linear_dlm_distinguishes_meanings`, `dlm_neutralizes_meanings_in_kernel`
  — sister structural theorems derived from `map_sub` + `sub_ne_zero` /
  `sub_eq_zero`. The kernel of the production map is the locus of
  pairs the DLM cannot distinguish in form — load-bearing for both
  consumer studies (Chuang's discrimination claim, Lu's tone-sandhi
  neutralization claim).
- `broadcastFirstCoord` — a non-trivial `LinearMap` witness for the
  architectural-capacity existence theorem; reusable by consumers.
- `linear_dlm_admits_meaning_specific_contours` — for any positive
  form/meaning dimensions, the substrate admits a DLM that
  distinguishes some meaning pair.

## Out of scope here

- **ResLDL** (linear + nonlinear residual): the [heitmeier-chuang-baayen-2026]
  extension of the DLM. A separate sibling file
  (`ResidualDiscriminative.lean`) would extend `LinearDiscriminativeLexicon`
  with a residual nonlinear component once a Studies file consumes it.
- **EuclideanSpace adoption / Lipschitz / inner-product theorems**: the
  carriers here are bare `Fin n → ℝ` for minimal mathlib-import
  footprint. A future sibling `Normed.lean` will host
  `EuclideanSpace ℝ (Fin n)`-typed wrappers and the Lipschitz/norm-
  preservation theorems that go with the paper's "centroid neighbours
  → contour neighbours" finding.
- **No-stored-representations** as a Lean theorem: the architectural
  commitment lives at the level of the structure definition (only two
  `LinearMap` fields, no `entries`-typed projection). Any "the DLM
  has no entries" theorem would need to negate an entries projection
  the substrate deliberately doesn't have.
-/

namespace Processing.Lexical.Discriminative

universe u

-- ============================================================================
-- §1: Substrate — the Linear Discriminative Lexicon Model
-- ============================================================================

/-- The **Linear Discriminative Lexicon Model** (LDL) — a pair of
    linear maps between form and meaning vector spaces.

    The "L" in LDL stands for *Linear*; we bake that into the type
    by using mathlib's `LinearMap`. Carrier-typed: applies to any
    `[Module R F]`/`[Module R M]` pair, not just `Fin n → ℝ`.

    There are exactly **two fields, both linear maps**. There is no
    `entries : List ...` field, no `frequency : ... → ℝ` field. The
    "lexicon" of an `LDL` is its two maps; nothing else is stored.
    See the module docstring's "Architectural placement" note for the
    substantive reason this is housed under `Processing/`. -/
structure LinearDiscriminativeLexicon (R : Type*) (F M : Type*)
    [Semiring R] [AddCommMonoid F] [AddCommMonoid M]
    [Module R F] [Module R M] where
  comprehension : F →ₗ[R] M
  production    : M →ₗ[R] F

-- ============================================================================
-- §2: Convenience: ℝ-typed Fin-indexed carriers
-- ============================================================================

/-- A `formDim`-dimensional **form vector** over ℝ, indexed by `Fin formDim`.
    Used by both consumer studies (Chuang 2026: `formDim = 50`;
    Lu 2026: `formDim = 100`) for pitch contours sampled at uniform
    points on a normalised time axis. The substrate is dimension-
    polymorphic; the specific dimension is paper-specific. -/
abbrev FormVec (formDim : ℕ) : Type := Fin formDim → ℝ

/-- A `meaningDim`-dimensional **meaning vector** over ℝ. Used by both
    consumer studies for context-specific contextualised embeddings
    (768-dim CKIP GPT-2 in both papers). -/
abbrev MeaningVec (meaningDim : ℕ) : Type := Fin meaningDim → ℝ

-- ============================================================================
-- §3: Structural theorems — the kernel = neutralization locus
-- ============================================================================

section Structural

variable {R : Type*} {F M : Type*}
  [Semiring R] [AddCommGroup F] [AddCommGroup M] [Module R F] [Module R M]

/-- **Structural meaning-discrimination lemma.** For any
    `LinearDiscriminativeLexicon`, if the production map sends the
    difference of two meanings to a non-zero vector, then the meanings
    map to distinct forms.

    Derived from `map_sub` + `sub_ne_zero` — no DLM-specific reasoning;
    the linearity of the production map does all the work. -/
theorem linear_dlm_distinguishes_meanings
    (D : LinearDiscriminativeLexicon R F M) {e₁ e₂ : M}
    (h : D.production (e₁ - e₂) ≠ 0) :
    D.production e₁ ≠ D.production e₂ := by
  rw [← sub_ne_zero, ← map_sub]
  exact h

/-- **Structural meaning-neutralization lemma** (sister of
    `linear_dlm_distinguishes_meanings`). For any
    `LinearDiscriminativeLexicon`, if the production map sends the
    difference of two meanings to zero, then the meanings map to
    **identical** forms.

    Architectural significance: the kernel of the production map is
    the **neutralization locus** — meaning-pairs the DLM cannot
    distinguish in form. When two empirically-distinct meanings have
    form identity, that identity follows from their meaning-difference
    landing in `ker production`, not from a stipulated rule. The
    Lu, Chuang & Baayen 2026 study applies this to Taiwan Mandarin T3
    tone sandhi (`Studies/LuChuangBaayen2026.lean`):
    T3-T3 and T2-T3 word centroids in CE space differ only by a
    kernel-element of the DLM's trained production map, so their
    surface contours coincide — no phonological sandhi rule invoked.

    Derived from `map_sub` + `sub_eq_zero`, dual to the discrimination
    lemma. -/
theorem dlm_neutralizes_meanings_in_kernel
    (D : LinearDiscriminativeLexicon R F M) {e₁ e₂ : M}
    (h : D.production (e₁ - e₂) = 0) :
    D.production e₁ = D.production e₂ := by
  rw [← sub_eq_zero, ← map_sub]
  exact h

end Structural

-- ============================================================================
-- §4: Concrete witness — `broadcastFirstCoord`
-- ============================================================================

/-- The "broadcast first coordinate" linear map: `e ↦ (i ↦ e[0])`.
    The simplest non-trivial `LinearMap` from `MeaningVec d` to
    `FormVec n` for `d, n ≥ 1`. Used as a witness for the
    architectural-capacity existence theorem and re-used by consumer
    studies (e.g. `LuChuangBaayen2026.dlm_dialect_flexibility`) to
    construct concrete non-degenerate DLMs without re-implementing it. -/
def broadcastFirstCoord {n d : ℕ} (hd : 0 < d) :
    MeaningVec d →ₗ[ℝ] FormVec n where
  toFun e _      := e ⟨0, hd⟩
  map_add' _ _   := funext fun _ => rfl
  map_smul' _ _  := funext fun _ => rfl

/-- Evaluation of `broadcastFirstCoord` at any sample index returns
    the input's coordinate-0 value. `@[simp]` so consumer simp-only
    calls can drop the `LinearMap.coe_mk, AddHom.coe_mk` litany. -/
@[simp] theorem broadcastFirstCoord_apply
    {n d : ℕ} (hd : 0 < d) (e : MeaningVec d) (i : Fin n) :
    broadcastFirstCoord hd e i = e ⟨0, hd⟩ := rfl

-- ============================================================================
-- §5: Architectural capacity
-- ============================================================================

/-- **Architectural capacity theorem.** For any positive form and
    meaning dimensions, the `LinearDiscriminativeLexicon` substrate
    admits a DLM and two distinct meanings whose production-map images
    differ. The substrate is non-vacuously capable of meaning
    discrimination.

    The empirical claim of the consumer papers (that the *trained*
    network distinguishes empirically *most* meaning pairs in the
    corpus) is paper-supplied; this theorem establishes only that the
    architecture has the structural *capacity* for such discrimination. -/
theorem linear_dlm_admits_meaning_specific_contours
    {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    ∃ (D : LinearDiscriminativeLexicon ℝ (FormVec n) (MeaningVec d))
      (e₁ e₂ : MeaningVec d),
      e₁ ≠ e₂ ∧ D.production e₁ ≠ D.production e₂ := by
  refine ⟨⟨0, broadcastFirstCoord hd⟩,
          0, Function.update (0 : MeaningVec d) ⟨0, hd⟩ 1, ?_, ?_⟩
  · -- e₁ ≠ e₂: evaluate at coordinate 0; LHS gives 0, RHS gives 1.
    intro h
    have h0 := congrFun h ⟨0, hd⟩
    simp only [Pi.zero_apply, Function.update_self] at h0
    exact zero_ne_one h0
  · -- production maps differ: evaluate at sample 0; LHS gives 0, RHS gives 1.
    intro h
    have h0 := congrFun h ⟨0, hn⟩
    simp only [broadcastFirstCoord_apply, Pi.zero_apply,
               Function.update_self] at h0
    exact zero_ne_one h0

end Processing.Lexical.Discriminative
