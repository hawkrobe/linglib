import Linglib.Features.Number.Basic
import Linglib.Semantics.Mereology

/-!
# Number — lattice semantics for the values

The denotation of a number value as a region of a join-semilattice of
individuals: `Number.interp P n` is the part of the region `P` that the
value `n` picks out, composed from Harbour's three binary features.
`[±atomic]` is mereological atomicity (`Mereology.Atom`); `[±minimal]` in a
region is minimality under parthood within it — Krifka's atomization of the
region, `Mereology.atomize`; `[±additive]` in a region is join-completeness
within it (`additiveIn`), which is cumulativity restricted to the region
(`additive_subregion_is_cum`), the number–aspect–telicity nexus.

The exact values (singular … unit augmented) compose the first two features
over `P` alone. The approximative values (paucal, greater paucal, greater
plural, global plural) additionally need a conventionalized cut — a
contextually supplied subregion — so `interp` returns `none` for them: their
semantics is `additiveIn` relative to a cut the lexicon does not fix. Because
the carrier is any `SemilatticeSup`, the same operator interprets verbal
number: pluractionality is `interp` at the event lattice. The
inclusive/exclusive plural is a separate pragmatic layer and is not encoded
here.

## References

* [harbour-2014], (10), (20), (21), §4.2, §4.4
* [link-1983]
* [corbett-2000], ch. 7–8
-/

namespace Number

open Mereology (Atom CUM Null atomize null)

variable {D : Type*} [SemilatticeSup D]

/-! ### Feature semantics -/

/-- `[+additive]` in region `Q`: `x` is join-complete in `Q`, `∀ y ∈ Q, x ⊔ y ∈ Q`
([harbour-2014] (10)). -/
def additiveIn (Q : D → Prop) (x : D) : Prop :=
  Q x ∧ ∀ y, Q y → Q (x ⊔ y)

theorem additiveIn_sup {Q : D → Prop} {x y : D} (hx : additiveIn Q x) (hy : additiveIn Q y) :
    additiveIn Q (x ⊔ y) := by
  refine ⟨hx.2 y hy.1, fun z hz => ?_⟩
  rw [sup_assoc]
  exact hx.2 (y ⊔ z) (hy.2 z hz)

/-- The `[+additive]` subregion is cumulative: one feature governs mass nouns
(`[+additive]`, cumulative) and telic predicates (`[−additive]`, quantized)
([harbour-2014] §4.4). -/
theorem additive_subregion_is_cum (Q : D → Prop) : CUM (additiveIn Q) :=
  fun _ hx _ hy => additiveIn_sup hx hy

instance {Q : D → Prop} [Fintype D] [DecidablePred Q] (x : D) : Decidable (additiveIn Q x) :=
  decidable_of_iff (Q x ∧ ∀ y, Q y → Q (x ⊔ y)) Iff.rfl

variable [Null D]

/-- The atoms of a region that excludes the null individual are minimal in it:
`[+atomic] → [+minimal]` ([harbour-2014] §4.2), derived rather than
stipulated — the semantic ground of `Number.Features.WellFormed`. -/
theorem singular_subset_minimal {P : D → Prop} (hP : ∀ y, P y → ¬ null y) {x : D}
    (hPx : P x) (hx : Atom x) : atomize P x :=
  ⟨hPx, fun _ hy hle => hx.2 (hP _ hy) hle⟩

/-- Over an all-atom region `[+minimal]` selects everything, which is why
`[±atomic]` cannot undergo feature recursion ([harbour-2014] §4.2). -/
theorem atomize_eq_of_atoms {P : D → Prop} (hAll : ∀ x, P x → Atom x) :
    atomize P = P :=
  funext fun x => propext ⟨fun h => h.1, fun hPx =>
    singular_subset_minimal (fun y hy => (hAll y hy).not_null) hPx (hAll x hPx)⟩

/-! ### Value denotations -/

/-- The non-atoms of `P`: `[−atomic]` restricted to `P`. -/
def nonAtomsOf (P : D → Prop) : D → Prop :=
  fun x => P x ∧ ¬ Atom x

/-- The denotation of a number value over the region `P` ([harbour-2014] (20),
(21)): `general` is `P`; `singular` its atoms; `dual` the minimal non-atoms;
`plural` the non-minimal non-atoms (the featural exclusive plural); `trial`
the minimal elements of the plural region; `minimal`, `augmented` and
`unitAugmented` the `[±minimal]`-only system and its recursion; the
approximative values `none`, being `additiveIn` relative to a cut the lexicon
does not supply. -/
def interp (P : D → Prop) : Number → Option (D → Prop)
  | .general => some P
  | .singular => some fun x => P x ∧ Atom x
  | .dual => some (atomize (nonAtomsOf P))
  | .trial => some (atomize fun x => nonAtomsOf P x ∧ ¬ atomize (nonAtomsOf P) x)
  | .plural => some fun x => nonAtomsOf P x ∧ ¬ atomize (nonAtomsOf P) x
  | .minimal => some (atomize P)
  | .augmented => some fun x => P x ∧ ¬ atomize P x
  | .unitAugmented => some (atomize fun x => P x ∧ ¬ atomize P x)
  | _ => none

/-- `interp` is defined exactly on the non-approximative values. -/
theorem interp_isSome_iff (P : D → Prop) (n : Number) :
    (interp P n).isSome ↔
      n ∉ ([.paucal, .greaterPaucal, .greaterPlural, .globalPlural] : List Number) := by
  cases n <;> simp [interp]

end Number
