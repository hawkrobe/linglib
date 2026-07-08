import Linglib.Semantics.Dynamic.DiscourseRef

/-!
# Anaphoric accessibility over dref-carrying contexts
[hofmann-2025]

Typeclass interface for contexts carrying individual and propositional
discourse referents, and the accessibility predicates and blocking theorem
of [hofmann-2025] stated at that interface: `HasPropDrefs` (propositional
drefs as sets of worlds, with the update law), `HasIndivDrefs`
(Entity-valued individual drefs), the accessibility predicates
(`localEntailment`, `subsetReq`, `consistentAt`, `accessible`), and
`counterfactual_blocks_veridical` — the abstract form of the
bathroom-sentence theorem, which any `HasPropDrefs` instance inherits.

`HasFiberedLookup` is the thin shared lookup signature
`iLookup : Ctx → V → W → M E`, instantiated at `M = Entity` (ICDRT, via
`HasIndivDrefs`), `M = Set` ([charlow-2019]'s marginal at a world), and
`M = Id` (the extensional DPL/CDRT/DRT baseline below). No theorem yet
quantifies over an abstract `M`; the signature exists so that per-family
lookups are comparable (`Reference/PronounDenotation.lean`'s
`interpPronoun_eq_iLookup`) and awaits a genuinely abstract consumer.

Frameworks diverge on what the lookup *returns* when a variable has no
referent (Hofmann's `.star`, Charlow's `∅`, Heim's partiality) and on how
states update; those commitments live in each family's file, and the
comparisons live in the studies that draw them (`Studies/Hofmann2025.lean`,
`Studies/Dekker2012.lean`, `Studies/Cooper2023/`).
-/

namespace Semantics.Dynamic.Context

open Semantics.Dynamic.Core

universe u v w x w₁ w₂

/-! ### Fibered lookup signature -/

/-- Fibered lookup: `iLookup i v w : M E` returns the `M`-family of values
for variable `v` at world `w` — `M = Entity` (ICDRT), `M = Set` (Charlow's
marginal), `M = Id` (extensional baseline). `M` is `outParam`: each `Ctx`
carries exactly one effect functor. -/
class HasFiberedLookup (M : outParam (Type u → Type u))
    (Ctx : Type v) (V : outParam (Type w))
    (W : outParam (Type x)) (E : outParam (Type u)) where
  /-- Look up the M-family of values for variable `v` at world `w`. -/
  iLookup : Ctx → V → W → M E

/-- Assignments as the *extensional* dynamic-semantic context, with
`M = Id` (no effect) and `W = PUnit` (no world parameter) — the baseline
shared by [groenendijk-stokhof-1991] DPL, [muskens-1996] CDRT, and
[kamp-reyle-1993] DRT, whose state types are all definitionally
`Nat → E = Assignment E`. Lookup is function application. -/
instance instAssignmentHasFiberedLookup (E : Type u) :
    HasFiberedLookup Id (Assignment E) Nat PUnit.{u + 1} E where
  iLookup g v _ := g v

/-! ### Individual and propositional drefs -/

/-- Hofmann-style deterministic context: `HasFiberedLookup Entity` plus
the `iVarUp` update relation — two contexts that "differ at most in `v`"
agree on every other variable. -/
class HasIndivDrefs (Ctx : Type v) (V : outParam (Type w))
    (W : outParam (Type x)) (E : outParam (Type u))
    extends HasFiberedLookup Entity Ctx V W E where
  /-- "j differs from i at most in v" — relation form. -/
  iVarUp : V → Ctx → Ctx → Prop
  /-- Equality of lookups outside the updated variable. -/
  iVarUp_other : ∀ v i j (u : V),
    iVarUp v i j → u ≠ v → iLookup j u = iLookup i u

/-- Contexts carrying propositional drefs (sets of worlds). -/
class HasPropDrefs (Ctx : Type v) (P : outParam (Type w)) (W : outParam (Type x)) where
  /-- Look up the worlds-set associated with propositional variable `p`. -/
  pLookup : Ctx → P → Set W
  /-- "j differs from i at most in p" — relation form. -/
  pVarUp : P → Ctx → Ctx → Prop
  /-- Equality of lookups outside the updated variable. -/
  pVarUp_other : ∀ p i j (q : P), pVarUp p i j → q ≠ p → pLookup j q = pLookup i q

/-! ### Accessibility predicates -/

section Predicates
variable {Ctx : Type v} {V : Type w₁} {P : Type w₂} {W : Type x} {E : Type u}
variable [HasIndivDrefs Ctx V W E] [HasPropDrefs Ctx P W]

/-- Local contextual entailment: `v` defined throughout `φ(i)`.
A precondition for anaphora to `v` resolved in local context `φ`; applied
to a commitment-set variable this is [hofmann-2025]'s veridicality of an
individual dref. -/
def localEntailment (φ : P) (v : V) (i : Ctx) : Prop :=
  ∀ w ∈ HasPropDrefs.pLookup (W := W) i φ,
    HasFiberedLookup.iLookup i v w ≠ Entity.star

/-- Counterfactuality: `v` maps to ⋆ in all `φ_DC`-worlds. -/
def counterfactualIndiv (φ_DC : P) (v : V) (i : Ctx) : Prop :=
  ∀ w ∈ HasPropDrefs.pLookup (W := W) i φ_DC,
    HasFiberedLookup.iLookup i v w = Entity.star

/-- Propositional-dref inclusion `φ(i) ⊆ ψ(i)`: the anaphor's subset
requirement when read as `φ_anaphor ⊆ φ_antecedent`, and [hofmann-2025]'s
DEC condition when read as `φ_DC ⊆ φ`. -/
def subsetReq (φ ψ : P) (i : Ctx) : Prop :=
  HasPropDrefs.pLookup (W := W) i φ ⊆ HasPropDrefs.pLookup i ψ

/-- Discourse consistency: commitment set is nonempty. -/
def consistentAt (φ_DC : P) (i : Ctx) : Prop :=
  (HasPropDrefs.pLookup (W := W) i φ_DC).Nonempty

/-- Accessibility = local entailment ∧ consistency. -/
def accessible (φ_anaphor : P) (v : V) (φ_DC : P) (i : Ctx) : Prop :=
  localEntailment (W := W) φ_anaphor v i ∧ consistentAt (W := W) φ_DC i

/-- Worlds where `v` has a non-⋆ referent in context `i`. -/
def definedAt (v : V) (i : Ctx) : Set W :=
  { w | HasFiberedLookup.iLookup i v w ≠ Entity.star }

/-- Generic relative-variable update: differ at most in `v`, and the
propositional dref `φ(j)` tracks exactly `v`'s definedness pattern in
`j`. This is Hofmann's cross-field operation expressed without a new
typeclass — pure combination of `iVarUp` and `pLookup`. -/
def relVarUp (φ : P) (v : V) (i j : Ctx) : Prop :=
  HasIndivDrefs.iVarUp v i j ∧
  HasPropDrefs.pLookup (W := W) j φ = definedAt (E := E) v j

end Predicates

/-! ### The blocking theorem -/

/-- **Counterfactual antecedent blocks veridical anaphor** (abstract).

In any `Ctx` with prop drefs, if we extend `i` to `j` keeping `φ_DC` and
`φ_neg` lookups fixed, and the antecedent provides counterfactuality
(`φ_DC(i) ∩ φ_neg(i) = ∅`), then satisfying both the DEC condition
(`φ_DC(j) ⊆ φ_anaphor(j)`) and the subset requirement
(`φ_anaphor(j) ⊆ φ_neg(j)`) forces `φ_DC(j) = ∅`, i.e. discourse
inconsistency.

This is the typeclass-only version of [hofmann-2025]'s bathroom-
sentence theorem ("There isn't a bathroom. #It is upstairs."), needing
only `HasPropDrefs`. It does not transfer to frameworks without
propositional-dref structure (e.g. [charlow-2019]'s `State W E`), which
handle the same phenomenon by alternative-set filtering — see
`Studies/Charlow2019.lean`. -/
theorem counterfactual_blocks_veridical
    {Ctx : Type v} {P : Type w} {W : Type x}
    [HasPropDrefs Ctx P W]
    (i j : Ctx) (φ_DC φ_anaphor φ_neg : P)
    (h_extends_DC :
      HasPropDrefs.pLookup (W := W) j φ_DC = HasPropDrefs.pLookup i φ_DC)
    (h_extends_neg :
      HasPropDrefs.pLookup (W := W) j φ_neg = HasPropDrefs.pLookup i φ_neg)
    (h_DC_disjoint_neg :
      HasPropDrefs.pLookup (W := W) i φ_DC ∩
        HasPropDrefs.pLookup (W := W) i φ_neg = ∅)
    (h_dec : subsetReq (W := W) φ_DC φ_anaphor j)
    (h_subset : subsetReq (W := W) φ_anaphor φ_neg j) :
    ¬ consistentAt (W := W) φ_DC j := by
  intro ⟨w, hw⟩
  have hw' : w ∈ HasPropDrefs.pLookup (W := W) i φ_DC := by
    rw [← h_extends_DC]; exact hw
  have hw_neg' : w ∈ HasPropDrefs.pLookup (W := W) i φ_neg := by
    rw [← h_extends_neg]; exact h_subset (h_dec hw)
  have hmem :
      w ∈ HasPropDrefs.pLookup (W := W) i φ_DC ∩
            HasPropDrefs.pLookup (W := W) i φ_neg := ⟨hw', hw_neg'⟩
  rw [h_DC_disjoint_neg] at hmem; exact hmem

end Semantics.Dynamic.Context
