import Linglib.Core.Order.Flat

/-!
# Lifting a per-slot compatibility clause to flat-slot `Compat`

`UD.MorphFeatures.compatible` checks φ-agreement slot by slot, each clause
having the shape `(a.isNone || b.isNone || a == b)` — equal-or-absent on the
raw UD values. These lemmas turn one such clause into `Compat` in the
analytical `Flat F` slot, after the raw value is ingested through an analytical
map (`ι : U → Option F`, or a total `g : U → F` — the `fromUD` ingests).

The order-theoretic core is `Flat.compat_iff` (`Core.Order.Flat`); this file
is the linglib-specific adapter on top of it, shared by the per-feature
agreement-faithfulness theorems (`HasX.compatible_hasX` in
`Features/{Person,Number,Gender,Case}/Capabilities.lean`). It is the
slot-level face of subsumption-based agreement ([shieber-1986];
[carpenter-1992]).

## Main declarations

* `Features.compat_of_clause` — clause ⟹ `Compat` after a partial ingest `ι`
* `Features.compat_of_clause_map` — the same for a total ingest `g`
-/

namespace Features

/-- A per-slot compatibility clause lifts to `Compat` in `Flat F`. If two raw
    values `a b : Option U` are equal-or-absent — `(a.isNone || b.isNone ||
    a == b)`, one clause of `UD.MorphFeatures.compatible` — then their images
    under any ingest `ι : U → Option F` are `Compat` in `Flat F`. -/
theorem compat_of_clause {U F : Type*} [DecidableEq U] [DecidableEq F]
    (ι : U → Option F) {a b : Option U}
    (h : (a.isNone || b.isNone || a == b) = true) :
    Compat (α := Flat F) (a.bind ι) (b.bind ι) := by
  rw [Flat.compat_iff]
  intro x hx y hy
  cases a with
  | none => exact absurd hx.symm (Option.some_ne_none x)
  | some u =>
    cases b with
    | none => exact absurd hy.symm (Option.some_ne_none y)
    | some v =>
      simp only [Option.isNone_some, Bool.false_or, beq_iff_eq,
        Option.some.injEq] at h
      subst h
      exact Option.some.inj (hx.symm.trans hy)

/-- `compat_of_clause` for a total ingest `g : U → F` (lifted via
    `Option.map`). The `Compat` conclusion is in `.map` form so it unifies
    with `.map`-shaped carrier projections. -/
theorem compat_of_clause_map {U F : Type*} [DecidableEq U] [DecidableEq F]
    (g : U → F) {a b : Option U}
    (h : (a.isNone || b.isNone || a == b) = true) :
    Compat (α := Flat F) (a.map g) (b.map g) := by
  have e : ∀ o : Option U, o.map g = o.bind (λ u => some (g u)) :=
    λ o => by cases o <;> rfl
  simp only [e]
  exact compat_of_clause (λ u => some (g u)) h

end Features
