import Linglib.Core.Mereology
import Linglib.Core.Lexical.NounCategorization
import Linglib.Theories.Syntax.Minimalism.Formal.ExtendedProjection.Basic

/-!
# Nominal Syntax-Semantics Mapping
@cite{borer-2005} @cite{champollion-2017} @cite{chierchia-1998} @cite{grimshaw-2005} @cite{krifka-1998}

Compositional interpretation of the nominal extended projection
via mereological predicates. Bridges the syntactic spine
N(F0) → n(F1) → Q(F2) → Num(F3) → D(F4) from `ExtendedProjection`
to the CUM/QUA distinction from `Core/Mereology`.

## Core Thesis

Roots denote cumulative (mass-like) predicates. The mass/count
distinction is not a lexical property of nouns but emerges from
functional structure:

- **CL# / Div** (at Q, F2): individuates a cumulative predicate
  by restricting to atoms → quantized (count) denotation
- **# / Num** (at Num, F3): enables counting/measuring over
  the individuated domain

## Why Q Below Num (§6)

The F-value ordering Q(F2) < Num(F3) — individuation below counting —
is not arbitrary. Section 6 proves it is the *unique* ordering
consistent with compositional semantics:

1. **Selectional typing**: Q takes CUM input (from roots) and produces
   QUA output. Num takes QUA input (from Q) and measures it. The
   chain root → Q → Num is well-typed; root → Num → Q is not, because
   Num on CUM input has no canonical measure.
2. **Asymmetric dependency**: `countIndividuated` calls `Div` but
   `Div` never calls counting. Dependents must be above dependencies.
3. **Truncation coherence**: every prefix of [N, n, Q, Num, D] has
   coherent semantics. The prefix [N, n, Num] (counting without
   individuation) is incoherent.
4. **Typological prediction**: Q without Num is attested (individuated
   but uncounted); Num without Q requires covert Q.

## Sections

1. Individuation Operator (Div/CL#)
2. Structural Mass/Count Distinction
3. Nominal EP Interpretation
4. The Great Divide
5. Parametric Individuation (DivCL)
6. Ordering Argument: Why Q Below Num
7. Bridges

-/

namespace Interfaces.SyntaxSemantics.Borer2005

open Mereology

-- ════════════════════════════════════════════════════
-- § 1. Individuation Operator
-- ════════════════════════════════════════════════════

variable {α : Type*} [SemilatticeSup α]

/-- The individuation operator (Borer's CL#/Div).

    Restricts a predicate to its atomic elements — the semantic
    content of the Q head (F2) in the nominal EP spine.

      Div(P) = {x ∈ P | Atom(x)}

    "beer" (mass, CUM) → Div → "a beer" (count, one unit)
    "stone" (mass, CUM) → Div → "a stone" (count, one piece)

    In classifier languages the classifier morpheme fills Q and may
    further constrain which atoms qualify (see `DivCL` in § 5). -/
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

    The Q head (Borer's CL#/Div, F2 in the EP hierarchy) is
    the locus of the mass/count distinction. Its presence in the
    spine determines count; its absence determines mass. -/
def spineHasQ (spine : List Minimalism.Cat) : Bool :=
  spine.any (· == Minimalism.Cat.Q)

/-- Whether an EP spine projects number (Num head present).

    The Num head (F3) hosts numeral/quantifier syntax. It is
    typically projected only when Q is also present, since
    counting presupposes individuation (see `num_presupposes_q`). -/
def spineHasNum (spine : List Minimalism.Cat) : Bool :=
  spine.any (· == Minimalism.Cat.Num)

/-- The full count spine includes both Q and Num. -/
theorem full_nominal_has_q :
    spineHasQ [.N, .n, .Q, .Num, .D] = true := by decide

/-- A truncated mass spine lacks Q. -/
theorem mass_spine_no_q :
    spineHasQ [.N, .n, .D] = false := by decide

/-- **Borer's prediction about `countable`**: the `countable` field
    on fragment noun entries is derivable from the EP spine. Under
    Borer's theory, a noun surfaces as count iff its nominal EP
    projects Q (individuation). The fragment records `countable` as
    an observable fact; this theorem shows it equals `spineHasQ`.

    Un@cite{chierchia-1998}, `countable` is a lexical primitive and
    this theorem is an accidental correlation rather than an
    explanation. The two theories agree on the data but disagree on
    direction of explanation.

    This is a definitional schema — instances for specific nouns
    appear in bridge files where fragment entries are paired with
    specific EP spines. -/
def countableFromSpine (spine : List Minimalism.Cat) : Bool :=
  spineHasQ spine

/-- Count spine → countable = true. -/
theorem count_spine_countable :
    countableFromSpine [.N, .n, .Q, .Num, .D] = true := by decide

/-- Mass spine → countable = false. -/
theorem mass_spine_not_countable :
    countableFromSpine [.N, .n, .D] = false := by decide

-- ════════════════════════════════════════════════════
-- § 4. The Great Divide
-- ════════════════════════════════════════════════════

/-- The Great Divide: cross-linguistic variation
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
    This bridges @cite{aikhenvald-2000}'s typological ClassifierEntry to
    Borer's syntactic CL# at Q(F2) in the nominal EP. -/
structure ClassifierAsQ where
  /-- The classifier morpheme (from Aikhenvald's typology) -/
  classifier : Core.NounCategorization.ClassifierEntry
  /-- The syntactic position is Q (F2 in the nominal EP) -/
  position : Minimalism.Cat := .Q

-- ════════════════════════════════════════════════════
-- § 5. Parametric Individuation (DivCL)
-- ════════════════════════════════════════════════════

/-- A classifier predicate: a constraint on which atoms qualify
    for individuation. In classifier languages, the classifier
    morpheme contributes this predicate; in non-classifier languages,
    it is trivially `fun _ => True` (covert Div). -/
abbrev ClassifierPred (α : Type*) := α → Prop

/-- Parametric individuation: like `Div` but further constrained
    by a classifier predicate.

    `DivCL P cl` = {x ∈ P | Atom(x) ∧ cl(x)}

    Examples:
    - 只 (zhī, small animal): `cl = fun x => x.animacy ∧ x.isSmall`
    - 本 (běn, bound volume): `cl = fun x => x.shape ==.boundVolume`
    - Covert Div (English): `cl = fun _ => True`

    This connects the semantic parameters from classifier fragment
    entries (`ClassifierEntry.semantics`) to the Div operator. -/
def DivCL (P : α → Prop) (cl : ClassifierPred α) : α → Prop :=
  fun x => P x ∧ Atom x ∧ cl x

/-- DivCL refines Div: DivCL(P, cl) ⊆ Div(P). -/
theorem divCL_sub_div {P : α → Prop} {cl : ClassifierPred α}
    {x : α} (h : DivCL P cl x) : Div P x :=
  ⟨h.1, h.2.1⟩

/-- Parametric individuation is still quantized.
    The classifier predicate only narrows *which* atoms qualify;
    it doesn't change the fundamental property that atoms have
    no proper parts. -/
theorem divCL_qua (P : α → Prop) (cl : ClassifierPred α) :
    QUA (DivCL P cl) := by
  intro x y ⟨_, hAtom, _⟩ hlt _
  exact absurd (hAtom y (le_of_lt hlt)) (ne_of_lt hlt)

/-- Div is DivCL with the trivial classifier.
    Non-classifier languages (English) have covert Div, which is
    parametric individuation with no classifier restriction. -/
theorem div_eq_divCL_trivial (P : α → Prop) :
    ∀ x, Div P x ↔ DivCL P (fun _ => True) x := by
  intro x
  simp [Div, DivCL]

/-- Counting with a classifier: QMOD(DivCL(P, cl), μ, n).
    "三只猫" = countCL(√CAT, isSmallAnimal, μ, 3). -/
def countCL (P : α → Prop) (cl : ClassifierPred α) (μ : α → ℚ) (n : ℚ) :
    α → Prop :=
  QMOD (DivCL P cl) μ n

-- ════════════════════════════════════════════════════
-- § 6. Ordering Argument: Why Q Below Num
-- ════════════════════════════════════════════════════

/-! ### The selectional typing argument

The semantic operations at each EP level form a typed pipeline:

```
root (CUM) →[Q/CL]→ individuated (QUA) →[Num/#]→ measured →[D]→ referential
```

Q's input type is CUM (roots denote cumulative predicates), and its
output type is QUA (individuated predicates are quantized, by `div_qua`).
Num's input type is QUA (counting presupposes individuated units).

If the ordering were reversed (Num below Q), Num would receive CUM
input and attempt to count a mass predicate — but counting mass
without prior individuation has no canonical measure. The selectional
chain would be ill-typed.

We formalize this as three properties that the Borer ordering satisfies
and the reverse ordering violates.
-/

/-- The mereological status of a predicate: cumulative (mass-like),
    quantized (count-like), or measured (counted). This tracks the
    semantic type through the nominal EP pipeline. -/
inductive MereoStatus where
  | cum       -- cumulative: closed under join (root denotation)
  | qua       -- quantized: no proper-part membership (after individuation)
  | measured  -- quantized + fixed measure value (after counting)
  deriving DecidableEq, Repr, BEq

/-- The semantic effect of each nominal functional head on the
    mereological status of its complement.

    - **Q (individuation)**: CUM → QUA (by `div_qua`)
    - **Num (counting)**: QUA → measured (by `QMOD` on QUA)
    - **n (categorizer)**: CUM → CUM (categorization preserves mass)
    - **D (determination)**: any → referential (not tracked here)

    The key insight: Q's transition CUM → QUA is well-defined
    (proved by `div_qua`), and Num's transition QUA → measured
    is well-defined (QMOD on a quantized predicate gives a
    quantized subpredicate). But Num on CUM input — counting
    mass — has no canonical semantics. -/
def headEffect : Minimalism.Cat → Option (MereoStatus × MereoStatus)
  | .Q   => some (.cum, .qua)        -- individuation: CUM → QUA
  | .Num => some (.qua, .measured)    -- counting: QUA → measured
  | .n   => some (.cum, .cum)         -- categorization preserves CUM
  | _    => none                      -- other heads: not part of this pipeline

/-- A nominal EP spine is **selectively well-typed** if each head's
    input status matches its predecessor's output status.

    This is the compositional coherence condition: the semantic
    pipeline must be type-correct at every step. -/
def selectionallyWellTyped : List (Minimalism.Cat × MereoStatus) → Bool
  | [] => true
  | [_] => true
  | (_, s₁) :: rest@((c₂, _) :: _) =>
    match headEffect c₂ with
    | some (input, _) => (s₁ == input) && selectionallyWellTyped rest
    | none => selectionallyWellTyped rest

/-- The Borer ordering [N(CUM), n(CUM), Q(QUA), Num(measured)] is
    selectively well-typed: each head receives the correct input.

    - N starts CUM (root predicate)
    - n expects CUM, outputs CUM ✓
    - Q expects CUM, outputs QUA ✓ (by `div_qua`)
    - Num expects QUA, outputs measured ✓ -/
theorem borer_ordering_well_typed :
    selectionallyWellTyped
      [(.N, .cum), (.n, .cum), (.Q, .qua), (.Num, .measured)] = true := by
  native_decide

/-- The reverse ordering [N(CUM), n(CUM), Num(?), Q(QUA)] is
    selectively ILL-typed: Num receives CUM input but expects QUA.

    Counting mass (CUM) without prior individuation is undefined:
    there is no canonical unit to count. "Three beer" (without a
    classifier or plural morphology) is not a well-formed count
    expression in any language — it requires covert individuation. -/
theorem reverse_ordering_ill_typed :
    selectionallyWellTyped
      [(.N, .cum), (.n, .cum), (.Num, .measured), (.Q, .qua)] = false := by
  native_decide

/-- **The Borer ordering is the unique well-typed ordering of Q and Num.**

    Among the two possible orderings of Q and Num in the nominal
    spine (with N at F0 and n at F1 fixed), only the Borer ordering
    (Q below Num) produces a selectively well-typed pipeline. -/
theorem borer_ordering_unique :
    -- Borer ordering: well-typed
    selectionallyWellTyped
      [(.N, .cum), (.n, .cum), (.Q, .qua), (.Num, .measured)] = true ∧
    -- Reverse ordering: ill-typed
    selectionallyWellTyped
      [(.N, .cum), (.n, .cum), (.Num, .measured), (.Q, .qua)] = false := by
  exact ⟨by native_decide, by native_decide⟩

/-! ### The asymmetric dependency argument

`countIndividuated` is defined as `QMOD (Div P) μ n` — it calls `Div`
internally. But `Div` is defined as `fun x => P x ∧ Atom x` — no
reference to counting, measurement, or `QMOD`. The dependency is
one-directional: counting depends on individuation, not vice versa.

In a bottom-up compositional EP, a head that depends on another's
output must be structurally above it (higher F-value). Since Num
depends on Q's output but Q does not depend on Num's, we get
fValue Q < fValue Num. -/

/-- Q's individuation operator (`Div`) is self-contained: it depends
    only on the root predicate and the mereological atom concept.
    It does not reference counting, measurement, or Num. -/
theorem div_independent_of_counting (P : α → Prop) :
    Div P = fun x => P x ∧ Atom x := rfl

/-- Num's counting operator (`countIndividuated`) depends on Q's
    output: it calls `Div` as a subcomputation. -/
theorem counting_depends_on_div (P : α → Prop) (μ : α → ℚ) (n : ℚ) :
    countIndividuated P μ n = QMOD (Div P) μ n := rfl

/-- The F-value ordering reflects the dependency: Q (F2) is below
    Num (F3), so Q's output is available as Num's input in bottom-up
    composition. -/
theorem fvalue_reflects_dependency :
    Minimalism.fValue .Q < Minimalism.fValue .Num := by decide

/-! ### The truncation coherence argument

Every prefix of the Borer-ordered spine [N, n, Q, Num, D] yields a
coherent nominal structure:

| Prefix          | Spine       | Interpretation                    |
|-----------------|-------------|-----------------------------------|
| bare root       | [N, n]      | CUM: mass predicate               |
| individuated    | [N, n, Q]   | QUA: one atomic unit ("a beer")   |
| counted         | [N, n, Q, Num] | measured: fixed count ("3 beers")|
| determined      | [N, n, Q, Num, D] | referential ("the 3 beers") |

Under the reverse ordering, the prefix [N, n, Num] would be
"counted but not individuated" — semantically incoherent. We
capture this via the truncation coherence check below. -/

/-- The mereological status after projecting a spine prefix.
    Returns `none` if the pipeline is ill-typed at any step. -/
def spinePrefixStatus : List Minimalism.Cat → Option MereoStatus
  | [] => some .cum
  | c :: rest =>
    match spinePrefixStatus rest with
    | none => none
    | some status =>
      match headEffect c with
      | some (input, output) => if status == input then some output else none
      | none => some status   -- head doesn't change mereological status

/-- Every prefix of the Borer-ordered spine has a well-defined
    mereological status: the pipeline is coherent at every truncation. -/
theorem borer_truncation_coherent :
    -- bare root: CUM
    spinePrefixStatus [.n, .N] = some .cum ∧
    -- individuated: QUA
    spinePrefixStatus [.Q, .n, .N] = some .qua ∧
    -- counted: measured
    spinePrefixStatus [.Num, .Q, .n, .N] = some .measured := by
  decide

/-- The reverse-ordered prefix [Num, n, N] is ill-typed:
    Num expects QUA input but n provides CUM. -/
theorem reverse_truncation_incoherent :
    spinePrefixStatus [.Num, .n, .N] = none := by
  decide

/-! ### Typological prediction

Q without Num should be attested (individuated but uncounted:
"a beer" projects Q but not Num). Num without Q should require
covert Q (you can't count without individuation, so [N, n, Num]
is ill-typed by `reverse_truncation_incoherent`). This predicts:

- Classifier languages CAN lack obligatory number marking
  (project Q without Num) — attested in Chinese, Japanese, Thai.
- Languages with obligatory number marking MUST have (overt or
  covert) individuation — universally attested: English has covert
  Div, producing the same QUA output. -/

/-- Q without Num: well-typed. Individuated but uncounted.
    Attested: Chinese bare classifiers, English "a beer." -/
theorem q_without_num_coherent :
    spinePrefixStatus [.Q, .n, .N] = some .qua := by decide

/-- Num without Q: ill-typed. Counted but not individuated. -/
theorem num_without_q_incoherent :
    spinePrefixStatus [.Num, .n, .N] = none := by decide

-- ════════════════════════════════════════════════════
-- § 7. Bridges
-- ════════════════════════════════════════════════════

/-! ### Bridge to @cite{chierchia-1998}

Borer and Chierchia offer competing accounts of the mass/count
distinction and cross-linguistic variation:

| Dimension        | @cite{chierchia-1998}            | @cite{borer-2005}              |
|------------------|--------------------------|-------------------------|
| Mass/count       | Lexical (`NounType`)      | Structural (`Div`)      |
| Cross-ling.      | Parameter (`NominalMapping`)| Functional inventory  |
| "beer" → count   | Not predicted             | `Div(√BEER)`            |
| Classifier langs | `[+arg, -pred]` parameter | Overt CL# at Q         |

Both predict CUM for mass and QUA for count. They disagree on
WHERE the distinction is encoded — lexicon vs. functional spine.
A full formal comparison belongs in `Theories/Comparisons/`.
-/

/-! ### Bridge to @cite{krifka-1998} / Mereology

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
