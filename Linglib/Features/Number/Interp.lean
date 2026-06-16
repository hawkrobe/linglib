import Linglib.Features.Number.Basic
import Linglib.Core.Order.Mereology

/-!
# Number — lattice semantics for the values
[harbour-2014] [link-1983]

The denotation of a number value as a predicate restrictor over a
join-semilattice of individuals ([link-1983]): `Number.interp P n` is the
region of `P`'s lattice the value `n` picks out, composed from the
feature semantics of [harbour-2014] —

- **(20)** `[±atomic]` = λx. (¬)atom(x) — `Mereology.Atom`;
- **(21)** `[±minimal]` = minimality in a region — `Number.minimalIn`;
- **(10)** `[±additive]` = join-completeness in a region —
  `Number.additiveIn`.

The exact values (singular … unit augmented) are compositions of (20)
and (21) over `P` alone; the approximative values (paucal, greater
paucal, greater plural, global plural) additionally require a
conventionalized cut — a contextually supplied subregion ([harbour-2014]
(14), the sociosemantic convention) — so `interp` returns `none` for
them: their semantics is `additiveIn` relative to a cut the lexicon does
not fix.

This is the *featural* characterization of the values (the regions
`latticeToFeatures` classifies, `Features/Number/Decomposition.lean`,
which hosts the decidable mirrors and the equivalence lemmas). The
inclusive/exclusive interpretation of the plural in assertion is a
separate, pragmatic layer ([corbett-2000] Ch 7; Sauerland-style
competition) and is deliberately not encoded here.

Because the domain is any `SemilatticeSup`, the same operator interprets
*verbal* number: pluractionality is `interp` at the event lattice
([corbett-2000] ch. 8), and `[+additive]`'s identity
with cumulativity (`additive_subregion_is_cum`, `Mereology.CUM`) is the
number–aspect–telicity nexus of [harbour-2014] §4.4.

The `[±minimal]`/`[±additive]` predicates were first stated in
`Syntax/Minimalist/Phi/Recursion.lean` and graduate here as the general
substrate; Recursion consumes them for the feature-recursion theory.
-/

set_option autoImplicit false

namespace Number

variable {D : Type*} [SemilatticeSup D]

/-! ### The feature semantics ([harbour-2014] (20), (21), (10)) -/

/-- `[+minimal]` in region `P`: `x` is a minimal element of `P` under `≤`
    ([harbour-2014] (21): `x` has no proper `P`-part below it). -/
def minimalIn (P : D → Prop) (x : D) : Prop :=
  P x ∧ ∀ y, P y → y ≤ x → y = x

/-- `[+additive]` in region `Q`: `x` is join-complete in `Q`
    ([harbour-2014] (10): ∀ y ∈ Q, x ⊔ y ∈ Q). -/
def additiveIn (Q : D → Prop) (x : D) : Prop :=
  Q x ∧ ∀ y, Q y → Q (x ⊔ y)

/-- The `[+additive]` region is closed under join: joining two
    `[+additive]` elements gives another. -/
theorem additiveIn_sup {Q : D → Prop}
    {x y : D} (hx : additiveIn Q x) (hy : additiveIn Q y) :
    additiveIn Q (x ⊔ y) := by
  refine ⟨hx.2 y hy.1, fun z hz => ?_⟩
  rw [sup_assoc]
  exact hx.2 (y ⊔ z) (hy.2 z hz)

/-- Atoms are minimal in any region containing them: the lattice-theoretic
    grounding of the containment `[+atomic] → [+minimal]`, and the reason
    `[±atomic]` cannot undergo feature recursion ([harbour-2014] §4.2):
    `[±minimal]` over an all-atom region selects all of it or nothing. -/
theorem minimalIn_of_atom {P : D → Prop}
    (hAllAtoms : ∀ x, P x → Mereology.Atom x)
    {x : D} (hPx : P x) : minimalIn P x :=
  ⟨hPx, fun y _ hle => Mereology.Atom.eq (hAllAtoms x hPx) hle⟩

/-- The `[−minimal]` complement of an all-atom region is empty
    ([harbour-2014] §4.2). -/
theorem not_nonminimal_of_atoms {P : D → Prop}
    (hAllAtoms : ∀ x, P x → Mereology.Atom x) (x : D) :
    ¬(P x ∧ ¬minimalIn P x) :=
  fun ⟨hPx, hNonMin⟩ => hNonMin (minimalIn_of_atom hAllAtoms hPx)

/-- The `[+additive]` subregion is cumulative (`Mereology.CUM`): the
    number–aspect–telicity nexus of [harbour-2014] §4.4 — mass nouns are
    `[+additive]` (cumulative), telic predicates `[−additive]`
    (quantized), with one feature governing both. -/
theorem additive_subregion_is_cum (Q : D → Prop) :
    Mereology.CUM (fun x => additiveIn Q x) :=
  Mereology.cum_iff.mpr fun x y hx hy => additiveIn_sup hx hy

/-! ### The value denotations -/

/-- The non-atoms of `P`: `[−atomic]` restricted to `P`. -/
def nonAtomsOf (P : D → Prop) : D → Prop :=
  fun x => P x ∧ ¬Mereology.Atom x

/-- The denotation of a number value over the region `P`, composed from
    (20)/(21):

    * `general` — non-committal: `P` itself;
    * `singular` — the atoms of `P`;
    * `dual` — the minimal non-atoms (`[−atomic +minimal]`);
    * `plural` — the non-minimal non-atoms (`[−atomic −minimal]`, the
      featural exclusive plural);
    * `trial` — `[±minimal]` recursion: the minimal elements of the
      plural region;
    * `minimal` / `augmented` / `unitAugmented` — the `[±minimal]`-only
      system and its recursion;
    * approximative values — `none`: they are `additiveIn` relative to a
      conventionalized cut the lexicon does not supply. -/
def interp (P : D → Prop) : Number → Option (D → Prop)
  | .general => some P
  | .singular => some fun x => P x ∧ Mereology.Atom x
  | .dual => some (minimalIn (nonAtomsOf P))
  | .trial => some (minimalIn fun x => nonAtomsOf P x ∧ ¬minimalIn (nonAtomsOf P) x)
  | .plural => some fun x => nonAtomsOf P x ∧ ¬minimalIn (nonAtomsOf P) x
  | .minimal => some (minimalIn P)
  | .augmented => some fun x => P x ∧ ¬minimalIn P x
  | .unitAugmented => some (minimalIn fun x => P x ∧ ¬minimalIn P x)
  | _ => none

/-- The values `interp` defines are exactly the non-approximative,
    in-system values together with `general`: the approximatives are the
    cut-dependent ones. -/
theorem interp_isSome_iff (P : D → Prop) (n : Number) :
    (interp P n).isSome ↔
      n ∉ ([.paucal, .greaterPaucal, .greaterPlural, .globalPlural] :
        List Number) := by
  cases n <;> simp [interp]

/-- Singular entails minimal over any region: the value-level containment
    `[+atomic] → [+minimal]`, derived from `minimalIn_of_atom` rather than
    stipulated — the semantic ground of `Number.Features.WellFormed`
    (`Features/Number/Decomposition.lean`). -/
theorem singular_subset_minimal (P : D → Prop) {x : D}
    (h : P x ∧ Mereology.Atom x) : minimalIn P x :=
  ⟨h.1, fun y _ hle => Mereology.Atom.eq h.2 hle⟩

/-- Dual and plural partition the non-atoms: every non-atom of `P` is
    dual or plural, never both — the `[±minimal]` split of the
    `[−atomic]` region. -/
theorem dual_plural_partition (P : D → Prop) (x : D)
    (hx : nonAtomsOf P x) :
    (minimalIn (nonAtomsOf P) x ∨
      (nonAtomsOf P x ∧ ¬minimalIn (nonAtomsOf P) x)) ∧
    ¬(minimalIn (nonAtomsOf P) x ∧
      (nonAtomsOf P x ∧ ¬minimalIn (nonAtomsOf P) x)) := by
  constructor
  · by_cases h : minimalIn (nonAtomsOf P) x
    · exact Or.inl h
    · exact Or.inr ⟨hx, h⟩
  · rintro ⟨hmin, -, hnmin⟩
    exact hnmin hmin

/-! ### Decidability

On finite carriers the feature predicates are decidable, so concrete
classifications (`Features/Number/Decomposition.lean`) are kernel-checked
by `decide`. -/

instance {P : D → Prop} [Fintype D] [DecidableEq D] [DecidableLE D]
    [DecidablePred P] (x : D) : Decidable (minimalIn P x) :=
  decidable_of_iff (P x ∧ ∀ y, P y → y ≤ x → y = x) Iff.rfl

instance {Q : D → Prop} [Fintype D] [DecidablePred Q] (x : D) :
    Decidable (additiveIn Q x) :=
  decidable_of_iff (Q x ∧ ∀ y, Q y → Q (x ⊔ y)) Iff.rfl

end Number
