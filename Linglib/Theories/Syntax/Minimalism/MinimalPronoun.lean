import Linglib.Theories.Morphology.DM.VocabularyInsertion
import Linglib.Core.NullSubject.Universals

/-!
# Minimal Pronoun Theory
@cite{kratzer-1998} @cite{kratzer-2009} @cite{safir-2014} @cite{landau-2015}

All instances of bound variable anaphora — reflexives, PRO, bound variable
pronouns — are syntactically identical: bare D heads with unvalued φ-features
("minimal pronouns"). Cross-linguistic variation in their surface form
(null, reflexive, pronoun) reduces entirely to variation in **vocabulary items**,
language-specific contextual allomorphs applied postsyntactically.

Definition (28) of @cite{landau-2015}: X is a minimal pronoun iff X = [D,uφ].
Within different derivations, X can become a reflexive, a bound lexical pronoun,
a resumptive pronoun, a *pro* element, a relative pronoun, or controlled PRO.
The choice is determined by the syntactic context and the language's vocabulary
item inventory.

## Key Definitions

- `BVAContext`: The four licensing contexts for bound variable anaphora
- `VocabItem`: A context-sensitive realization rule (D[uφ] → Form / context)
- `MinPronInventory`: A language's vocabulary item inventory + elsewhere default
- `PronForm`: Standard surface form categories (null, pronoun, reflexive)
- `OCSignature`: @cite{landau-2013}'s Obligatory Control diagnostic package

## Core Claims

1. Minimal pronouns are D heads with unvalued φ-features (28)
2. φ-values are transmitted from the antecedent (via Agree or variable binding)
3. Vocabulary items map valued feature bundles to surface forms, conditioned
   by syntactic context (locally bound, controlled subject, etc.)
4. The **Elsewhere Condition** (DM; Halle & Marantz 1993): if no
   context-specific item matches, the default (pronoun) applies
5. Cross-linguistic variation in anaphoric form is morphological, not
   syntactic (@cite{safir-2014}: "all anaphoric diversity is morphological").
   The DM vocabulary-item implementation used here follows @cite{landau-2015}
   and @cite{ostrove-2026}; Safir's own mechanism is morphological shape
   conditions at Spell-Out, not Vocabulary Insertion per se.

Landau-specific theory (the Two-Tiered Theory of Control, predicate
classification, clause classes) is in `Phenomena/Control/Studies/Landau2015.lean`.
-/

namespace Syntax.Minimalism.MinimalPronoun

-- ════════════════════════════════════════════════════════════════
-- § 1: Licensing Contexts
-- ════════════════════════════════════════════════════════════════

/-- The four syntactic contexts in which a minimal pronoun can occur.
    Each context may trigger a different vocabulary item (surface form).

    These correspond to the traditional binding domains:
    - `controlledSubject`: PRO position (subject of controlled clause)
    - `locallyBound`: Condition A domain (reflexives)
    - `boundVariable`: Condition B domain (bound pronoun, non-local)
    - `free`: Condition C / referential (unbound) -/
inductive BVAContext where
  /-- Subject of a controlled clause — PRO in English -/
  | controlledSubject
  /-- Locally bound — reflexive in English (Condition A domain) -/
  | locallyBound
  /-- Bound by a non-local c-commanding antecedent -/
  | boundVariable
  /-- Free / referential (unbound) -/
  | free
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 2: Vocabulary Items and the Elsewhere Condition
-- ════════════════════════════════════════════════════════════════

/-- A vocabulary item: a context-specific realization rule for a minimal pronoun.

    In DM terms: D[uφ] → `form` / `context` ...

    Vocabulary items are ordered by specificity. When multiple items could
    apply, the most specific (first in the list) wins.

    This is a specialization of the general DM `Morphology.DM.VI.VocabItem`
    in `Theories/Morphology/DM/VocabularyInsertion.lean`, restricted to
    `BVAContext` matching with a parameterized `Form` type. -/
structure VocabItem (Form : Type) where
  /-- The syntactic context this item is restricted to -/
  context : BVAContext
  /-- The surface form this item realizes -/
  form : Form

/-- A language's inventory of vocabulary items for minimal pronouns.

    The `items` list is ordered by specificity (most specific first).
    The `elsewhere` form applies when no context-specific item matches.

    @cite{safir-2014}: "from this single element, all anaphoric diversity
    is morphological" -/
structure MinPronInventory (Form : Type) where
  /-- Context-specific vocabulary items, ordered by specificity -/
  items : List (VocabItem Form)
  /-- Default exponence: applies when no specific item matches.
      Crosslinguistically, this is the pronoun form (@cite{safir-2014}). -/
  elsewhere : Form

/-- The Elsewhere Condition: find the first vocabulary item whose context
    matches; if none does, use the elsewhere (default pronoun) form. -/
def MinPronInventory.realize {Form : Type}
    (inv : MinPronInventory Form) (ctx : BVAContext) : Form :=
  match inv.items.find? (·.context == ctx) with
  | some item => item.form
  | none => inv.elsewhere

/-- A language's realized form for controlled subjects specifically.
    This is the function that distinguishes null-PRO from overt-PRO languages. -/
def MinPronInventory.controlForm {Form : Type}
    (inv : MinPronInventory Form) : Form :=
  inv.realize .controlledSubject

-- ════════════════════════════════════════════════════════════════
-- § 3: Standard Surface Forms
-- ════════════════════════════════════════════════════════════════

/-- Standard surface form categories for bound variable anaphora.

    These are the cross-linguistically attested exponence options for
    minimal pronouns. Each vocabulary item maps a BVA context to one
    of these forms. -/
inductive PronForm where
  /-- Silent (null PRO) -/
  | null
  /-- Overt pronoun (φ-matching clitic or full form) -/
  | pronoun
  /-- Reflexive anaphor (English *-self*, SMPM *mí* + pronoun) -/
  | reflexive
  deriving DecidableEq, Repr

/-- Whether a language's minimal-pronoun inventory realizes the
    controlled-subject context with an overt form. This is the
    Minimalism-side bridge to `Core.NullSubject.ProDropProfile.hasOvertPRO`.
    The typological criterion is non-nullness, not specifically `.pronoun`:
    @cite{ostrove-2026}'s universal is about overt-vs-null PRO, so an
    inventory whose controlled-subject form is `.reflexive` would also
    count as overt PRO. -/
def MinPronInventory.hasOvertPRO (inv : MinPronInventory PronForm) : Bool :=
  inv.controlForm != .null

-- ════════════════════════════════════════════════════════════════
-- § 3.5: Bridge to `Core.NullSubject.SubjectAssignment`
-- ════════════════════════════════════════════════════════════════

open Core.NullSubject in
/-- Project a `PronForm` to the framework-agnostic `Exponent` (null vs
    overt). Both `.pronoun` and `.reflexive` count as overt — the
    typological criterion in `Core.NullSubject` is non-nullness. -/
def PronForm.toExponent : PronForm → Core.NullSubject.Exponent
  | .null      => .null
  | .pronoun   => .overt
  | .reflexive => .overt

open Core.NullSubject in
/-- Project a Minimalist `MinPronInventory` to the framework-agnostic
    `SubjectAssignment`. The `BVAContext` axis maps `controlled
    SubjectContext`s to `controlledSubject`; all other contexts get
    the elsewhere/free realization, since the minimal-pronoun
    inventory does not directly track person, finiteness, or
    Ā-status. Refinements (per-person inventories, anti-agreement
    inventories) extend this projection. -/
def MinPronInventory.toSubjectAssignment
    (inv : MinPronInventory PronForm) : SubjectAssignment :=
  fun ctx =>
    let bva : BVAContext := match ctx.clauseRole with
      | .controlSubject => .controlledSubject
      | _               => .free
    (inv.realize bva).toExponent

open Core.NullSubject in
/-- Bridge theorem: the abstract `hasOvertPRO` over the projected
    assignment agrees with the inventory's own `hasOvertPRO`. This is
    the Minimalism→Core grounding: changing the inventory propagates
    to the abstract universal by construction. -/
theorem MinPronInventory.subjectAssignment_overtPRO_iff
    (inv : MinPronInventory PronForm) :
    inv.toSubjectAssignment.hasOvertPRO = inv.hasOvertPRO := by
  unfold SubjectAssignment.hasOvertPRO MinPronInventory.toSubjectAssignment
    MinPronInventory.hasOvertPRO MinPronInventory.controlForm
    SubjectAssignment.hasOvertPROAt
  simp [thematicPersons, SubjectContext.controlled, PronForm.toExponent]
  cases h : inv.realize .controlledSubject <;> simp

-- ════════════════════════════════════════════════════════════════
-- § 4: Obligatory Control Signature
-- ════════════════════════════════════════════════════════════════

/-- @cite{landau-2013}'s Obligatory Control signature (simplified).

    A clause S exhibits OC iff its subject satisfies two core conditions:
    (a) the controller(s) must be codependent(s) of S
    (b) PRO (or part of it) must be interpreted as a bound variable

    Two additional diagnostics are **derived** from (a):
    - Sloppy-only under VPE (from (a): controller must be local codependent
      of the elided clause, forcing sloppy construal; Morgan 1970)
    - Local c-commanding antecedent required (from (a): codependency
      excludes arbitrary, long-distance, and non-c-commanding control)

    Note: partial control IS a subspecies of OC per @cite{landau-2013} —
    (74b) says "PRO (or part of it)", explicitly accommodating it. -/
structure OCSignature where
  /-- (a): Controller must be argument of the matrix predicate -/
  controllerCodependent : Bool
  /-- (b): Embedded subject interpreted as bound variable -/
  boundVariable : Bool
  deriving DecidableEq, Repr

/-- Derived: VPE allows only sloppy, not strict readings (from codependency:
    controller must be local codependent of elided clause). -/
def OCSignature.sloppyOnly (sig : OCSignature) : Bool := sig.controllerCodependent

/-- Derived: Antecedent must locally c-command (from codependency). -/
def OCSignature.localCCommand (sig : OCSignature) : Bool := sig.controllerCodependent

/-- The full OC signature: both core diagnostics positive. -/
def ocFull : OCSignature where
  controllerCodependent := true
  boundVariable := true

/-- No OC: neither core diagnostic holds. -/
def ocNone : OCSignature where
  controllerCodependent := false
  boundVariable := false

/-- Does a clause type show obligatory control? -/
def OCSignature.isOC (sig : OCSignature) : Bool :=
  sig.controllerCodependent && sig.boundVariable

-- ════════════════════════════════════════════════════════════════
-- § 5: DM Vocabulary Insertion Bridge
-- ════════════════════════════════════════════════════════════════

/-- Convert a `MinPronInventory` to a list of DM `VocabItem`s.

    Each context-specific item becomes a DM rule with `specificity = 1`,
    and the elsewhere form becomes a DM rule with `specificity = 0`.
    This preserves the Elsewhere Condition: DM's specificity-sorted
    insertion will select the context-specific rule when it matches,
    falling back to the elsewhere rule otherwise.

    The `Form` type is rendered to `String` via the supplied function. -/
def MinPronInventory.toDMRules {Form : Type}
    (inv : MinPronInventory Form) (render : Form → String)
    : List (Morphology.DM.VI.VocabItem BVAContext Unit) :=
  let contextRules := inv.items.map fun item =>
    { exponent := render item.form
      contextMatch := fun ctx => ctx == item.context
      specificity := 1 }
  let elsewhereRule : Morphology.DM.VI.VocabItem BVAContext Unit :=
    { exponent := render inv.elsewhere
      contextMatch := fun _ => true
      specificity := 0 }
  contextRules ++ [elsewhereRule]

end Syntax.Minimalism.MinimalPronoun
