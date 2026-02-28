import Linglib.Core.Mereology
import Linglib.Core.Lexical.NounCategorization
import Linglib.Theories.Syntax.Minimalism.Formal.ExtendedProjection.Basic

/-!
# Nominal Syntax-Semantics Mapping (Borer 2005)

Compositional interpretation of the nominal extended projection
via mereological predicates. Bridges the syntactic spine
N(F0) → n(F1) → Num(F2) → Q(F3) → D(F4) from `ExtendedProjection`
to the CUM/QUA distinction from `Core/Mereology`.

## Core Thesis

Roots denote cumulative (mass-like) predicates. The mass/count
distinction is not a lexical property of nouns but emerges from
functional structure:

- **CL# / Div** (at Q, F3): individuates a cumulative predicate
  by restricting to atoms → quantized (count) denotation
- **# / Num** (at Num, F2): enables counting/measuring over
  the individuated domain

## Sections

1. Individuation Operator (Div/CL#)
2. Structural Mass/Count Distinction
3. Nominal EP Interpretation
4. The Great Divide
5. Bridges

## References

- Borer, H. (2005). *Structuring Sense, Vol I: In Name Only*. OUP.
- Grimshaw, J. (2005). *Words and Structure*. CSLI.
- Champollion, L. (2017). *Parts of a Whole*. OUP.
- Chierchia, G. (1998). Reference to Kinds Across Languages.
- Krifka, M. (1998). The origins of telicity.
-/

namespace Interfaces.SyntaxSemantics.Borer2005

open Mereology

-- ════════════════════════════════════════════════════
-- § 1. Individuation Operator
-- ════════════════════════════════════════════════════

variable {α : Type*} [SemilatticeSup α]

/-- The individuation operator (Borer's CL#/Div).

    Restricts a predicate to its atomic elements — the semantic
    content of the Q head in the nominal EP spine.

      Div(P) = {x ∈ P | Atom(x)}

    "beer" (mass, CUM) → Div → "a beer" (count, one unit)
    "stone" (mass, CUM) → Div → "a stone" (count, one piece)

    In classifier languages the classifier morpheme fills this head
    and may further constrain which atoms qualify (by shape, animacy,
    etc.); the present formalization captures the core: individuation
    restricts to entities without proper parts. -/
def Div (P : α → Prop) : α → Prop :=
  fun x => P x ∧ Atom x

/-- Div restricts: Div(P) ⊆ P. -/
theorem div_sub {P : α → Prop} {x : α} (h : Div P x) : P x :=
  h.1

/-- Every element of Div(P) is an atom. -/
theorem div_atom {P : α → Prop} {x : α} (h : Div P x) : Atom x :=
  h.2

-- ════════════════════════════════════════════════════
-- § 2. Structural Mass/Count Distinction
-- ════════════════════════════════════════════════════

/-- **Core theorem**: Individuated predicates are quantized.

    Atoms have no proper parts, so no proper part of a Div(P)-element
    can also be in Div(P). This is why count nouns are quantized:
    "three beers" is telic because the individuated predicate is QUA.

    The proof is structural: it holds for ANY root predicate P,
    regardless of whether P is lexically "mass" or "count." -/
theorem div_qua (P : α → Prop) : QUA (Div P) := by
  intro x y ⟨_, hAtom⟩ hlt _
  exact absurd (hAtom y (le_of_lt hlt)) (ne_of_lt hlt)

/-- **The anti-lexicalist theorem**: the same root yields both
    mass (CUM) and count (QUA) readings via functional structure.

    This is the formal refutation of `countable : Bool` as a lexical
    feature on nouns. The root √BEER has a cumulative denotation;
    functional structure alone determines whether it surfaces as
    mass "beer" or count "a beer."

    Borer (2005 §3.1): "there are no count nouns or mass nouns.
    There is, rather, a mass functional projection and a count
    functional projection." -/
theorem same_root_mass_and_count (P : α → Prop) (hCum : CUM P) :
    CUM P ∧ QUA (Div P) :=
  ⟨hCum, div_qua P⟩

/-- Sums of individuated elements remain in the original cumulative
    predicate: AlgClosure(Div(P)) ⊆ P when CUM(P).

    Linguistically: any plurality of beer-units is still beer (mass).
    "Three beers" denotes an entity that is also "beer."
    Pluralization does not escape the mass extension. -/
theorem algClosure_div_sub_cum (P : α → Prop) (hCum : CUM P) :
    ∀ x, AlgClosure (Div P) x → P x := by
  intro x hx
  induction hx with
  | base h => exact h.1
  | sum _ _ ih₁ ih₂ => exact hCum _ _ ih₁ ih₂

/-- Counting requires prior individuation.

    "Three beers" = QMOD(Div(√BEER), μ, 3): beer-atom sums
    whose measure is exactly 3. Inherits QUA from Div. -/
def countIndividuated (P : α → Prop) (μ : α → ℚ) (n : ℚ) : α → Prop :=
  QMOD (Div P) μ n

-- ════════════════════════════════════════════════════
-- § 3. Nominal EP Interpretation
-- ════════════════════════════════════════════════════

/-- Whether an EP spine projects individuation (Q head present).

    The Q head (Borer's CL#/Div, F3 in Grimshaw's hierarchy) is
    the locus of the mass/count distinction. Its presence in the
    spine determines count; its absence determines mass. -/
def spineHasQ (spine : List Minimalism.Cat) : Bool :=
  spine.any (· == Minimalism.Cat.Q)

/-- Whether an EP spine projects number (Num head present).

    The Num head (F2) hosts numeral/quantifier syntax. It is
    typically projected only when Q is also present, since
    counting presupposes individuation. -/
def spineHasNum (spine : List Minimalism.Cat) : Bool :=
  spine.any (· == Minimalism.Cat.Num)

/-- The full count spine includes both Q and Num. -/
theorem full_nominal_has_q :
    spineHasQ [.N, .n, .Num, .Q, .D] = true := by decide

/-- A truncated mass spine lacks Q. -/
theorem mass_spine_no_q :
    spineHasQ [.N, .n, .D] = false := by decide

-- ════════════════════════════════════════════════════
-- § 4. The Great Divide
-- ════════════════════════════════════════════════════

/-- The Great Divide (Borer 2005, Ch. 7): cross-linguistic variation
    in nominal systems reduces to how individuation is realized.

    This is NOT a lexical parameter on nouns or a typological
    parameter on languages (cf. Chierchia's NominalMapping), but a
    property of the functional inventory. -/
inductive IndividuationStrategy where
  /-- Classifier languages (Chinese, Japanese, Thai): CL# is an
      overt functional head filled by a classifier morpheme.
      Enumeration requires an overt classifier: 三只猫 (sān zhī māo). -/
  | overtClassifier
  /-- Non-classifier languages (English, Romance, Slavic): Div is
      a covert functional head. Plural morphology (-s, -en) is
      its morphological reflex. Enumeration is direct: "three cats." -/
  | covertDiv
  deriving DecidableEq, Repr, BEq

/-- Both individuation strategies produce the same semantic result.
    The Great Divide is morphosyntactic, not semantic: overt
    classifiers and covert Div both yield QUA via individuation. -/
theorem great_divide_semantic_invariance
    (P : α → Prop) : ∀ (_s : IndividuationStrategy), QUA (Div P) :=
  fun _ => div_qua P

/-- In classifier languages, a ClassifierEntry spells out the Q head.
    This bridges Aikhenvald's (2000) typological ClassifierEntry to
    Borer's syntactic CL# at Q(F3) in the nominal EP.

    The classifier's semantic parameters (shape, animacy, etc.)
    constrain which atoms Div selects — a refinement beyond the
    core `Div` formalization here. -/
structure ClassifierAsQ where
  /-- The classifier morpheme (from Aikhenvald's typology) -/
  classifier : Core.NounCategorization.ClassifierEntry
  /-- The syntactic position is Q (F3 in the nominal EP) -/
  position : Minimalism.Cat := .Q

-- ════════════════════════════════════════════════════
-- § 5. Bridges
-- ════════════════════════════════════════════════════

/-! ### Bridge to Chierchia (1998)

Borer and Chierchia offer competing accounts of the mass/count
distinction and cross-linguistic variation:

| Dimension        | Chierchia 1998            | Borer 2005              |
|------------------|--------------------------|-------------------------|
| Mass/count       | Lexical (`NounType`)      | Structural (`Div`)      |
| Cross-ling.      | Parameter (`NominalMapping`)| Functional inventory  |
| "beer" → count   | Not predicted             | `Div(√BEER)`            |
| Classifier langs | `[+arg, -pred]` parameter | Overt CL# at Q         |

Both predict CUM for mass and QUA for count. They disagree on
WHERE the distinction is encoded — lexicon vs. functional spine.
A full formal comparison belongs in `Theories/Comparisons/`.
-/

/-! ### Bridge to Krifka (1998) / Mereology

Borer's individuation connects directly to Krifka's event mereology
already formalized in `Core/Mereology`:

- `Div` on the nominal domain produces QUA predicates
- QUA nominal arguments create telic (QUA) VPs via `qua_pullback`
  along an incremental theme relation (Krifka's SINC)
- "eat three beers" is telic because `countIndividuated √BEER μ 3`
  is QUA, and QUA pulls back through the eat-theme homomorphism

The composition `qua_pullback (θ : Event → Entity) (div_qua P)` is
already supported by `Core/Mereology` §8.
-/

end Interfaces.SyntaxSemantics.Borer2005
