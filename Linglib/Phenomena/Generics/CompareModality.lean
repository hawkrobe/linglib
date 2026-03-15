import Linglib.Theories.Semantics.Lexical.Noun.Kind.Generics
import Linglib.Theories.Semantics.Attitudes.Intensional
import Linglib.Theories.Semantics.Lexical.CovertQuantifier

/-!
# Generic Quantification as Modal Necessity

@cite{krifka-etal-1995} @cite{cohen-2013} @cite{asher-pelletier-2013}

This module makes explicit the structural parallel between the GEN operator
and Kratzer's modal necessity.

## The Parallel

| GEN                           | Modal necessity (Kratzer)           |
|-------------------------------|-------------------------------------|
| Domain: situations            | Domain: possible worlds             |
| Restriction: normal ∧ kind    | Restriction: modal base f(w)        |
| Scope: predicated property    | Scope: prejacent proposition p      |
| Hidden: normalcy predicate    | Hidden: ordering source g(w)        |
| Force: quasi-universal (∀)    | Force: necessity (∀ over best)      |

Both are restricted universal quantifiers over a contextually determined
domain. The normalcy predicate in GEN plays the same structural role as
the ordering source in Kratzer's semantics: it selects the "best" or
"most normal" elements from the accessible domain.

## Cohen's Argument (@cite{cohen-2013})

Ariel Cohen (ch. 13 of the Genericity book) argues that GEN is not a
phonologically null version of an overt quantifier — it is introduced
by the hearer through reinterpretation. Cohen identifies two devices:
Predicate Transfer (pragmatic, for generics — yields scope ambiguities
except in opaque contexts) and type-shifting (semantic, for habituals —
yields narrow scope only). See `Theories/Semantics/Composition/PredicateTransfer.lean`
for the formal definitions (T_g, γ, `QuantifierSource`) and
`Phenomena/Generics/Studies/Cohen2013.lean` for the scope predictions
verified on finite models. The present module draws a further connection
not made by Cohen: the resulting generic quantifier has the structure
of modal quantification (restricted universal over a contextually
filtered domain).

## Asher & Pelletier (@cite{asher-pelletier-2013})

Asher & Pelletier (ch. 12) analyze generics as modal quantification over
circumstances, with the restrictor providing the modal base and normalcy
providing the ordering source.
-/
-- UNVERIFIED: Asher & Pelletier chapter number ("ch. 12") and specific claim about modal base/ordering source mapping

namespace Phenomena.Generics.CompareModality

open Semantics.Lexical.Noun.Kind.Generics
open Semantics.Attitudes.Intensional (World allWorlds)

-- Structural Correspondence

/-- GEN and modal necessity share the same logical form:
    ∀x ∈ BEST(domain, ordering). scope(x)

    This structure captures the parallel at the type level. -/
structure RestrictedUniversal (D : Type) where
  /-- The domain of quantification -/
  domain : List D
  /-- The restriction (selects relevant elements) -/
  restriction : D → Bool
  /-- The scope (what must hold of restricted elements) -/
  scope : D → Bool

/-- Evaluate a restricted universal: ∀d ∈ domain. restriction(d) → scope(d) -/
def RestrictedUniversal.eval {D : Type} (ru : RestrictedUniversal D) : Bool :=
  ru.domain.all λ d => !ru.restriction d || ru.scope d

/-- GEN as a restricted universal over situations. -/
def genAsRU
    (situations : List Situation)
    (normal : NormalcyPredicate)
    (restrictor : Restrictor)
    (scope : Scope)
    : RestrictedUniversal Situation :=
  { domain := situations
  , restriction := λ s => normal s && restrictor s
  , scope := scope }

/-- GEN evaluation matches the restricted universal evaluation. -/
theorem gen_matches_ru
    (situations : List Situation)
    (normal : NormalcyPredicate)
    (restrictor : Restrictor)
    (scope : Scope)
    : traditionalGEN situations normal restrictor scope =
      (genAsRU situations normal restrictor scope).eval := rfl

/-- Modal necessity as a restricted universal over worlds.
    With empty ordering source, this is simple necessity over accessible worlds. -/
def modalAsRU
    (accessible : List World)
    (p : World → Bool)
    : RestrictedUniversal World :=
  { domain := accessible
  , restriction := λ _ => true  -- all accessible worlds are "restricted"
  , scope := p }

/-- Modal necessity matches the restricted universal.
    (With the trivial restriction, the RU reduces to ∀w ∈ accessible. p(w).) -/
theorem modal_matches_ru
    (accessible : List World)
    (p : World → Bool)
    : accessible.all p = (modalAsRU accessible p).eval := by
  unfold modalAsRU RestrictedUniversal.eval
  simp only [Bool.not_true, Bool.false_or]

-- The normalcy–ordering-source correspondence

/-- The normalcy predicate in GEN plays the same role as the ordering source
    in Kratzer semantics. Both filter the domain down to "best" elements.

    This is a structural observation, not a definitional identity: GEN uses
    a binary normal/abnormal distinction while Kratzer uses a preorder. The
    binary case is the degenerate case where the ordering has exactly two
    equivalence classes. -/
inductive DomainFilterStrategy where
  | binaryNormalcy    -- GEN: normal(s) is Bool
  | preorderBest      -- Kratzer: bestWorlds uses ≤_A ranking
  deriving DecidableEq, Repr

-- GenericTheory ↔ ModalTheory correspondence table

/-- Summary of the structural correspondence between generic and modal theories. -/
structure Correspondence where
  genericComponent : String
  modalComponent : String
  notes : String := ""
  deriving Repr

def correspondenceTable : List Correspondence :=
  [ { genericComponent := "situations (domain)"
    , modalComponent := "possible worlds (domain)"
    , notes := "Both quantify over abstract indices" }
  , { genericComponent := "normal ∧ restrictor (restriction)"
    , modalComponent := "modal base f(w) (accessible worlds)"
    , notes := "Both select relevant elements from domain" }
  , { genericComponent := "normalcy predicate"
    , modalComponent := "ordering source g(w)"
    , notes := "Both rank/filter the restricted domain" }
  , { genericComponent := "scope (predicated property)"
    , modalComponent := "prejacent proposition p"
    , notes := "What must hold of all best/normal elements" }
  , { genericComponent := "GEN force (quasi-universal)"
    , modalComponent := "necessity force (∀ over best worlds)"
    , notes := "Both are universal, not existential" }
  ]

end Phenomena.Generics.CompareModality
