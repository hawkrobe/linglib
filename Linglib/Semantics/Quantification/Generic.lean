import Linglib.Semantics.Quantification.Counting

/-!
# Generic quantifiers as generalized-quantifier schemas

Rival semantics for the silent generic operator `Gen`, expressed as instances of
the existing `Quantification.GQ α` generalized-quantifier interface
([barwise-cooper-1981]) rather than as bespoke per-paper types. The competing
theories then differ by a **property of the `GQ`**, not by an incompatible
signature: all are `Conservative`; only the majority schema is `Proportional`.

* `genNormalcy` — the traditional normalcy-restricted universal
  ([krifka-etal-1995]): the kind's NORMAL members satisfy the scope.
* `genWays` — [nickel-2009]'s ways-of-normality: SOME way of being normal makes
  all of its normal members satisfy the scope.

The third schema, the majority/absolute-reading operator ([cohen-1999a]), is the
existing `Quantification.most_sem`; `most_proportional` records that it — alone
among the three — is `Proportional` (its truth is a function of the
|R ∩ S| : |R ∖ S| ratio). That is the precise "generics as majority
quantification" characterization the genericity literature ([nickel-2009],
[leslie-2008]) rejects as a *theory of generics*; it is true of this operator,
not of generics in general.

The per-paper operators are shown EQUAL to these schemas in the study files
(`Cohen1999.cohenGEN_univ_eq_most_sem`, `Nickel2009.nickelGEN_univ_eq_genWays`),
so the unification subsumes them rather than paralleling them. Those bridges are
to the operators *as linglib formalizes them*, inheriting their documented
simplifications (Cohen's `cohenGEN` is the absolute reading only; `genWays` takes
Nickel's modal "ways" at their actual extension).

## Main definitions

* `genNormalcy normal : GQ α` — normalcy-restricted universal generic.
* `genWays normalIn ways : GQ α` — ways-of-normality generic.

## Main results

* `genNormalcy_conservative`, `genWays_conservative` — the generic schemas are
  conservative.
* `genWays_singleton` — one way of normality reduces `genWays` to `genNormalcy`
  (Nickel generalizes the traditional account).
* `genNormalcy_not_ratio_determined` — the normalcy schema is not ratio-determined,
  so (unlike the majority schema, `Counting.most_proportional`) it is not
  `Proportional`: equal cardinality ratio, opposite generic verdict.

## Implementation notes

`GQ α` is whole-carrier (`Fintype`); the study operators take an explicit
`Finset` domain and bridge at `Finset.univ`. `most_sem`/`Proportional` are stated
over the noncomputable classical `count`, so the proportionality contrast is
witnessed by a decidable cardinality example rather than a `Proportional`
counterexample.
-/

namespace Quantification

variable {α : Type*} [Fintype α]

/-! ### The generic schemas as generalized quantifiers -/

/-- **Traditional `Gen`** ([krifka-etal-1995]) as a generalized quantifier: the
    restrictor's NORMAL members all satisfy the scope — a normalcy-restricted
    universal, i.e. `Gen` with a hidden normalcy parameter. -/
def genNormalcy (normal : α → Prop) : GQ α :=
  fun R S => everyOn Finset.univ (fun x => normal x ∧ R x) S

/-- **[nickel-2009]'s ways-of-normality `Gen`** as a generalized quantifier:
    SOME way of being normal makes all of its normal members satisfy the scope.
    The actual-extension proxy of Nickel's modal "ways" (his own simplification). -/
def genWays {ι : Type*} (normalIn : α → ι → Prop) (ways : Finset ι) : GQ α :=
  fun R S => ∃ w ∈ ways, everyOn Finset.univ (fun x => normalIn x w ∧ R x) S

/-! ### Conservativity -/

/-- The normalcy-restricted generic is conservative ([barwise-cooper-1981]). -/
theorem genNormalcy_conservative (normal : α → Prop) :
    Conservative (genNormalcy normal) := by
  intro R S
  simp only [genNormalcy, everyOn]
  exact ⟨fun h x hx hpre => ⟨hpre.2, h x hx hpre⟩, fun h x hx hpre => (h x hx hpre).2⟩

/-- The ways-of-normality generic is conservative ([barwise-cooper-1981]). -/
theorem genWays_conservative {ι : Type*} (normalIn : α → ι → Prop) (ways : Finset ι) :
    Conservative (genWays normalIn ways) := by
  intro R S
  simp only [genWays, everyOn]
  constructor
  · rintro ⟨w, hw, h⟩; exact ⟨w, hw, fun x hx hpre => ⟨hpre.2, h x hx hpre⟩⟩
  · rintro ⟨w, hw, h⟩; exact ⟨w, hw, fun x hx hpre => (h x hx hpre).2⟩

/-- A single way of being normal reduces `genWays` to `genNormalcy`: [nickel-2009]'s
    account is the traditional one when there is only one respect of normality. -/
theorem genWays_singleton {ι : Type*} (normalIn : α → ι → Prop) (w : ι) :
    genWays normalIn {w} = genNormalcy (fun x => normalIn x w) := by
  funext R S
  simp only [genWays, genNormalcy, Finset.mem_singleton, exists_eq_left]

/-! ### Proportionality separates majority from normalcy

The majority operator is already `Proportional` (`most_proportional`, in
`Counting`): the formal content of "generics as majority quantification" — true
of *this operator* ([cohen-1999a]'s absolute reading), which his homogeneity and
relative reading, and the later literature ([nickel-2009], [leslie-2008]), reject
as a theory of generics. The normalcy schema is not proportional. -/

/-- The normalcy generic is NOT ratio-determined (hence not `Proportional`,
    unlike `most_sem` / `most_proportional`): over
    `Fin 2` with only `0` normal, `{0}`-in-scope is generic-true while
    `{1}`-in-scope is generic-false, yet both have |R ∩ S| : |R ∖ S| = 1 : 1. -/
theorem genNormalcy_not_ratio_determined :
    genNormalcy (α := Fin 2) (· = 0) (fun _ => True) (· = 0) ∧
    ¬ genNormalcy (α := Fin 2) (· = 0) (fun _ => True) (· = 1) := by
  refine ⟨?_, ?_⟩ <;> simp only [genNormalcy, everyOn] <;> decide

end Quantification
