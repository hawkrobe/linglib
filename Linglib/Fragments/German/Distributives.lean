import Linglib.Theories.Semantics.Lexical.Plural.Distributivity
import Linglib.Theories.Semantics.Lexical.Plural.CandidateInterpretation

/-!
# German Distributive Expressions

Fragment entries for German distributive items grounded in the theory-layer
operators from `Theories/Semantics/Lexical/Plural/Distributivity.lean`.

## Inventory

| Form     | Gloss          | Syntactic use   | Semantics       | ±dist | ±max |
|----------|----------------|-----------------|-----------------|-------|------|
| *jeder*  | every/each     | DP + distance   | `distMaximal`   | +     | +    |
| *jeweils*| each/resp.     | distance only   | `distTolerant`  | +     | -    |
| *alle*   | all            | DP only         | `allViaForallH` | -     | +    |

The key contrast: *jeder* and *jeweils* are both obligatorily distributive,
but differ in maximality. *jeder* uses identity tolerance (forces maximality);
*jeweils* uses a contextually provided tolerance (permits non-maximality for
some speakers). @cite{haslinger-etal-2025}.

## Grounding

Each entry's semantics is defined by direct reference to theory-layer operators,
following the compositional grounding principle: Fragment entries import and use
Theory definitions, never stipulating their own meaning functions.
-/

namespace Fragments.German.Distributives

open Semantics.Lexical.Plural.Distributivity

variable {Atom W : Type*} [DecidableEq Atom]

-- Semantic Entries

/--
⟦jeder⟧ = `distMaximal`: distribute P to every atom, no exceptions.

Equivalent to `distTolerant` with identity tolerance
(`distMaximal_eq_identity`). On atoms, reduces to P itself
(`distMaximal_singleton`).

@cite{haslinger-etal-2025} examples (1), (22b-c).
-/
def jederSem (P : Atom → W → Bool) : Finset Atom → W → Bool :=
  distMaximal P

/--
⟦jeweils⟧ = `distTolerant`: distribute P to atoms within a tolerant
sub-plurality. The tolerance relation ≤ is contextually provided.

For speakers who accept *jeweils* in non-maximal contexts, the tolerance
parameter allows exceptions irrelevant to the QUD.

@cite{haslinger-etal-2025} eq. (25), examples (22a), (23b), (24b).
-/
def jeweilsSem (P : Atom → W → Bool) (tol : Tolerance Atom) :
    Finset Atom → W → Bool :=
  distTolerant P tol

/--
⟦alle⟧ = universal quantification over the tolerance parameter.

`alle` does not itself force distributivity — it removes the tolerance
parameter that would otherwise permit non-maximal readings. The predicate's
own dist/non-dist nature is preserved.

Formally: ⟦alle P⟧ = λw.λx.∀≤'[≤' tolerance → ⟦P⟧^≤'(x)]
This is equivalent to `allSatisfy` by `allViaForallH_iff_allSatisfy`.

@cite{haslinger-etal-2025} eq. (20b); @cite{kriz-spector-2021} §5.3.
-/
def alleSem [Fintype Atom] (P : Atom → W → Bool) (x : Finset Atom) (w : W) : Prop :=
  allViaForallH P x w

-- Lexical Properties

/--
German distributive expression with grounded semantics.
-/
structure DistributiveEntry where
  /-- Surface form -/
  form : String
  /-- English gloss -/
  gloss : String
  /-- Has a DP-internal (determiner) use? -/
  hasDPUse : Bool
  /-- Has a distance-distributive (adverbial) use? -/
  hasDistanceUse : Bool
  /-- Classification -/
  distMaxClass : DistMaxClass
  deriving Repr

def jederEntry : DistributiveEntry :=
  { form := "jeder"
  , gloss := "every/each"
  , hasDPUse := true
  , hasDistanceUse := true
  , distMaxClass := .distMax }

def jeweilsEntry : DistributiveEntry :=
  { form := "jeweils"
  , gloss := "each/respectively"
  , hasDPUse := false        -- No DP-internal use!
  , hasDistanceUse := true
  , distMaxClass := .distNonMax }

def alleEntry : DistributiveEntry :=
  { form := "alle"
  , gloss := "all"
  , hasDPUse := true
  , hasDistanceUse := false
  , distMaxClass := .nonDistMax }

-- Grounding Theorems

/-- jeder's semantics IS distMaximal -/
theorem jeder_eq_distMaximal (P : Atom → W → Bool) :
    jederSem P = distMaximal P := rfl

/-- jeder = distTolerant with identity tolerance (on nonempty pluralities) -/
theorem jeder_eq_identity_tolerant (P : Atom → W → Bool)
    (x : Finset Atom) (w : W) (hne : x.Nonempty) :
    jederSem P x w = distTolerant P Tolerance.identity x w :=
  distMaximal_eq_identity P x w hne

/-- jeweils with identity tolerance = jeder (on nonempty pluralities) -/
theorem jeweils_identity_eq_jeder (P : Atom → W → Bool)
    (x : Finset Atom) (w : W) (hne : x.Nonempty) :
    jeweilsSem P Tolerance.identity x w = jederSem P x w :=
  (distMaximal_eq_identity P x w hne).symm

/-- alle reduces to simple universal check on atoms -/
theorem alle_eq_allSatisfy [Fintype Atom] (P : Atom → W → Bool)
    (x : Finset Atom) (w : W) :
    alleSem P x w ↔ allSatisfy P x w = true :=
  allViaForallH_iff_allSatisfy P x w

-- Typological Correlation

/-- The DP-use / maximality correlation from @cite{haslinger-etal-2025} §4:
    items with a DP-internal use (*jeder*, *alle*) enforce maximality;
    items without one (*jeweils*) permit non-maximality.

    This is a descriptive correlation, not a theorem — the paper notes
    that `jeder*` (eq. 27) would be a counterexample if attested. -/
theorem dp_use_implies_maximal_for_attested :
    jederEntry.hasDPUse = true ∧ jederEntry.distMaxClass.isMaximal = true ∧
    alleEntry.hasDPUse = true ∧ alleEntry.distMaxClass.isMaximal = true ∧
    jeweilsEntry.hasDPUse = false ∧ jeweilsEntry.distMaxClass.isMaximal = false := by
  decide

end Fragments.German.Distributives
