import Linglib.Theories.Semantics.Exhaustification.Innocent

/-!
# Excluder Combinators
@cite{fox-2007} @cite{magri-2009} @cite{fox-katzir-2011} @cite{trinh-haida-2015}

Two combinators on `Excluder W`, modelling the two ways a base excluder
can be modified by linguistic constraints:

- `Excluder.restrict E R` filters the **output** of `E.excluded`. Only
  alternatives the base excluder already chose AND that satisfy `R`
  remain. This is @cite{magri-2009}'s relevance modifier and the natural
  home for any post-exclusion filter.

- `Excluder.preFilter E P` filters the **input** alternative set before
  `E` runs. The base excluder sees a smaller `ALT`, which can change
  which alternatives become innocently excludable. This is the natural
  home for restrictions on **what counts as a formal alternative** —
  e.g. @cite{trinh-haida-2015}'s Atomicity constraint, @cite{katzir-2007}'s
  structural-complexity bound on `F(S)`.

## The Fox–Katzir asymmetry

@cite{fox-katzir-2011}'s central thesis distinguishes the contextual
restriction `C` (what is contextually relevant) from the formal
alternative source `F` (what counts as an alternative at all). They
argue that `C` cannot break symmetry — only `F` can. As an algebraic
theorem about excluder combinators:

- `restrict` is **monotone in `R`**: dropping exclusions only **weakens**
  the exhaustified meaning (`exh_subset_restrict_exh`). Therefore
  `restrict` cannot **create** an implicature that the base excluder
  fails to license (`restrict_preserves_no_implicature`).
- `preFilter` is **not monotone in `P`**: removing a symmetric partner
  from `ALT` can promote the surviving alternative from non-IE to IE,
  **strengthening** the exhaustified meaning. The two-world
  `preFilter_can_create_implicature` witness shows this strengthening
  for the canonical symmetric pair `{{w₀}, {w₁}}`.

So the structural asymmetry that @cite{fox-katzir-2011} state as a
constraint on theories of alternatives falls out, in this library, as
an algebraic fact about which combinator one chose: post-filter
(`restrict`) is conservative; pre-filter (`preFilter`) is not.

## Linguistic instantiations

| Combinator         | Use site                                                         |
| ------------------ | ---------------------------------------------------------------- |
| `magri R`          | `Relevance.lean` — `innocent.restrict R`                         |
| `_ .preFilter P`   | `Alternatives/AtomicConstraint.lean` — Trinh–Haida F_AT ⊊ F      |

-/

namespace Exhaustification

variable {W : Type*} [Fintype W] [DecidableEq W]

namespace Excluder

-- ════════════════════════════════════════════════════════════════════
-- §1  restrict — filter the EXCLUDED output
-- ════════════════════════════════════════════════════════════════════

/-- Restrict an excluder to alternatives satisfying `R`. The exh result
    grows: dropping exclusions can only let more worlds through. -/
def restrict (E : Excluder W) (R : Finset W → Bool) : Excluder W where
  excluded ALT φ := (E.excluded ALT φ).filter (fun a => R a)
  excluded_subset ALT φ :=
    (Finset.filter_subset _ _).trans (E.excluded_subset ALT φ)

@[simp] theorem restrict_excluded (E : Excluder W) (R : Finset W → Bool)
    (ALT : Finset (Finset W)) (φ : Finset W) :
    (E.restrict R).excluded ALT φ
      = (E.excluded ALT φ).filter (fun a => R a) := rfl

/-- A constantly-true relevance predicate leaves the excluder unchanged. -/
theorem restrict_const_true (E : Excluder W) :
    E.restrict (fun _ => true) = E := by
  cases E with
  | mk excluded excluded_subset =>
    simp [restrict]

/-- Restricting an excluder enlarges (or preserves) its `exh`: fewer
    exclusions means a weaker conjunction. -/
theorem exh_subset_restrict_exh (E : Excluder W) (R : Finset W → Bool)
    (ALT : Finset (Finset W)) (φ : Finset W) :
    E.exh ALT φ ⊆ (E.restrict R).exh ALT φ := by
  intro w hw
  rw [mem_exh_iff] at hw ⊢
  refine ⟨hw.1, ?_⟩
  intro a ha
  rw [restrict_excluded, Finset.mem_filter] at ha
  exact hw.2 a ha.1

/-- **Fox–Katzir positive half (algebraic form)**: `restrict` cannot
    create an implicature. If the base excluder's exhaustified meaning
    is not contained in `ψ`, neither is the restricted excluder's.

    Contrapositively: an implicature licensed under `E.restrict R` was
    already licensed under `E`. The contextual modifier can drop
    implicatures, never add them. This is the algebraic statement of
    @cite{fox-katzir-2011}'s claim that contextual restriction `C`
    cannot break symmetry. -/
theorem restrict_preserves_no_implicature (E : Excluder W)
    (R : Finset W → Bool) (ALT : Finset (Finset W)) (φ ψ : Finset W)
    (h : ¬ E.exh ALT φ ⊆ ψ) :
    ¬ (E.restrict R).exh ALT φ ⊆ ψ :=
  fun hres => h ((exh_subset_restrict_exh E R ALT φ).trans hres)

-- ════════════════════════════════════════════════════════════════════
-- §2  preFilter — filter the INPUT alternative set
-- ════════════════════════════════════════════════════════════════════

/-- Pre-filter the alternative set before the excluder sees it. The
    base excluder runs on `ALT.filter P`, not `ALT`. Removing
    alternatives can change which of the survivors are innocently
    excludable, so the resulting `exh` is **not** monotone in `P`. -/
def preFilter (E : Excluder W) (P : Finset W → Bool) : Excluder W where
  excluded ALT φ := E.excluded (ALT.filter (fun a => P a)) φ
  excluded_subset _ _ :=
    (E.excluded_subset _ _).trans (Finset.filter_subset _ _)

@[simp] theorem preFilter_excluded (E : Excluder W) (P : Finset W → Bool)
    (ALT : Finset (Finset W)) (φ : Finset W) :
    (E.preFilter P).excluded ALT φ
      = E.excluded (ALT.filter (fun a => P a)) φ := rfl

/-- A constantly-true pre-filter leaves the excluder unchanged. -/
theorem preFilter_const_true (E : Excluder W) :
    E.preFilter (fun _ => true) = E := by
  cases E with
  | mk excluded excluded_subset =>
    simp [preFilter]

end Excluder

-- ════════════════════════════════════════════════════════════════════
-- §3  Asymmetry witness — preFilter can strengthen `exh`
-- ════════════════════════════════════════════════════════════════════

/-!
The two-world canonical symmetric pair: `ALT = {{true}, {false}}`,
`φ = univ`. Both alternatives partition the prejacent, so neither is
innocently excludable, and `innocent.exh ALT φ = φ`. Pre-filtering to
keep only `{true}` removes the symmetric partner; the surviving
alternative becomes excludable, and `(innocent.preFilter P).exh = {false}`.

This is the smallest possible witness that **`preFilter` is non-monotone**:
strict pre-filtering produced a strictly smaller `exh`.
-/

private def cAlt : Finset (Finset Bool) := {{true}, {false}}
private def cPhi : Finset Bool := Finset.univ
private def cPsi : Finset Bool := {false}
private def cPred : Finset Bool → Bool := fun a => decide (a = ({true} : Finset Bool))

private theorem innocent_exh_at_symmetric_pair :
    innocent.exh cAlt cPhi = cPhi := by decide

private theorem preFilter_innocent_exh_at_symmetric_pair :
    (innocent.preFilter cPred).exh cAlt cPhi = cPsi := by decide

/-- **Fox–Katzir negative half (algebraic form)**: there exist a
    base excluder, alternative set, prejacent, conclusion, and pre-filter
    such that the base excluder fails to license the implicature `ψ`,
    but the pre-filtered excluder does.

    Witness: the canonical symmetric pair on `Bool`. `innocent` over
    `{{true}, {false}}` is vacuous (both alternatives are symmetric, so
    neither is innocently excludable). Removing `{false}` via `preFilter`
    leaves `{true}` as a non-symmetric singleton alternative, which then
    becomes excludable, strengthening `exh` from `univ` to `{false}`.

    Compare `restrict_preserves_no_implicature` (positive half): this
    strengthening is impossible for `restrict`, because its monotonicity
    is structural. The asymmetry between `restrict` and `preFilter` is
    exactly @cite{fox-katzir-2011}'s thesis that `C` cannot break
    symmetry but `F` can. -/
theorem preFilter_can_create_implicature :
    ∃ (E : Excluder Bool) (ALT : Finset (Finset Bool)) (φ ψ : Finset Bool)
      (P : Finset Bool → Bool),
      ¬ E.exh ALT φ ⊆ ψ ∧ (E.preFilter P).exh ALT φ ⊆ ψ := by
  refine ⟨innocent, cAlt, cPhi, cPsi, cPred, ?_, ?_⟩
  · rw [innocent_exh_at_symmetric_pair]; decide
  · rw [preFilter_innocent_exh_at_symmetric_pair]

end Exhaustification
