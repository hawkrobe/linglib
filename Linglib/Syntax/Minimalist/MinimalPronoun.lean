/-!
# Minimal Pronoun Theory
[kratzer-1998] [kratzer-2009] [safir-2014] [landau-2015]

All instances of bound variable anaphora — reflexives, PRO, bound variable
pronouns — are syntactically identical: bare D heads with unvalued φ-features
("minimal pronouns"). Cross-linguistic variation in their surface form
(null, reflexive, pronoun) reduces entirely to variation in **vocabulary items**,
language-specific contextual allomorphs applied postsyntactically.

Definition (28) of [landau-2015]: X is a minimal pronoun iff X = [D,uφ].
Within different derivations, X can become a reflexive, a bound lexical pronoun,
a resumptive pronoun, a *pro* element, a relative pronoun, or controlled PRO.
The choice is determined by the syntactic context and the language's vocabulary
item inventory.

## Key Definitions

- `BVAContext`: The four licensing contexts for bound variable anaphora
- `VocabItem`: A context-sensitive realization rule (D[uφ] → Form / context)
- `MinPronInventory`: A language's vocabulary item inventory + elsewhere default
- `PronForm`: Standard surface form categories (null, pronoun, reflexive)
- `OCSignature`: [landau-2013]'s Obligatory Control diagnostic package

## Core Claims

1. Minimal pronouns are D heads with unvalued φ-features (28)
2. φ-values are transmitted from the antecedent (via Agree or variable binding)
3. Vocabulary items map valued feature bundles to surface forms, conditioned
   by syntactic context (locally bound, controlled subject, etc.)
4. The **Elsewhere Condition** (DM; Halle & Marantz 1993): if no
   context-specific item matches, the default (pronoun) applies
5. Cross-linguistic variation in anaphoric form is morphological, not
   syntactic ([safir-2014]: "all anaphoric diversity is morphological").
   The DM vocabulary-item implementation used here follows [landau-2015]
   and [ostrove-2026]; Safir's own mechanism is morphological shape
   conditions at Spell-Out, not Vocabulary Insertion per se.

Landau-specific theory (the Two-Tiered Theory of Control, predicate
classification, clause classes) is in `Studies/Landau2015.lean`.
-/

namespace Minimalist.MinimalPronoun

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
    in `Morphology/DM/VocabularyInsertion.lean`, restricted to
    `BVAContext` matching with a parameterized `Form` type. -/
structure VocabItem (Form : Type) where
  /-- The syntactic context this item is restricted to -/
  context : BVAContext
  /-- The surface form this item realizes -/
  form : Form

/-- A language's inventory of vocabulary items for minimal pronouns.

    The `items` list is ordered by specificity (most specific first).
    The `elsewhere` form applies when no context-specific item matches.

    [safir-2014]: "from this single element, all anaphoric diversity
    is morphological" -/
structure MinPronInventory (Form : Type) where
  /-- Context-specific vocabulary items, ordered by specificity -/
  items : List (VocabItem Form)
  /-- Default exponence: applies when no specific item matches.
      Crosslinguistically, this is the pronoun form ([safir-2014]). -/
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
    controlled-subject context with an overt form. The criterion is
    non-nullness, not specifically `.pronoun`: [ostrove-2026]'s universal
    is about overt-vs-null PRO, so an inventory whose controlled-subject
    form is `.reflexive` also counts as overt PRO. -/
def MinPronInventory.hasOvertPRO (inv : MinPronInventory PronForm) : Prop :=
  inv.controlForm ≠ .null

instance (inv : MinPronInventory PronForm) : Decidable inv.hasOvertPRO :=
  inferInstanceAs (Decidable (_ ≠ _))

-- ════════════════════════════════════════════════════════════════
-- § 4: Obligatory Control Signature
-- ════════════════════════════════════════════════════════════════

/-- [landau-2013]'s Obligatory Control signature (simplified).

    A clause S exhibits OC iff its subject satisfies two core conditions:
    (a) the controller(s) must be codependent(s) of S
    (b) PRO (or part of it) must be interpreted as a bound variable

    Partial control is a subspecies of OC per [landau-2013] — "PRO (or part
    of it)" explicitly accommodates it. -/
structure OCSignature where
  /-- (a): Controller must be argument of the matrix predicate -/
  controllerCodependent : Bool
  /-- (b): Embedded subject interpreted as bound variable -/
  boundVariable : Bool
  deriving DecidableEq, Repr

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

end Minimalist.MinimalPronoun
