module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic

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
- `MinPronInventory`: A language's Vocabulary Items (D[uφ] → Form / context) + elsewhere default
- `MinPronInventory.syncretic`: the contexts whose form is the elsewhere pronoun's
- `PronForm`: Standard surface form categories (null, pronoun, reflexive)

## Core Claims

1. Minimal pronouns are D heads with unvalued φ-features (28)
2. φ-values are transmitted from the antecedent (via Agree or variable binding)
3. Vocabulary items map valued feature bundles to surface forms, conditioned
   by syntactic context (locally bound, controlled subject, etc.)
4. The **Elsewhere Condition** of [halle-marantz-1993]: if no
   context-specific item matches, the default (pronoun) applies
5. Cross-linguistic variation in anaphoric form is morphological, not
   syntactic ([safir-2014]: "all anaphoric diversity is morphological").
   The DM vocabulary-item implementation used here follows [landau-2015]
   and [ostrove-2026]; Safir's own mechanism is morphological shape
   conditions at Spell-Out, not Vocabulary Insertion per se.

Landau-specific theory (the Two-Tiered Theory of Control, predicate
classification, clause classes) is in `Studies/Landau2015.lean`.
-/

@[expose] public section

namespace Minimalist.MinimalPronoun

/-! ### Licensing Contexts -/

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
  deriving DecidableEq, Repr, Fintype

/-! ### Vocabulary Items and the Elsewhere Condition -/

/-- A language's inventory of Vocabulary Items for minimal pronouns: each
    item realizes D[uφ] as a form in one `BVAContext` — D[uφ] → `form` /
    `context` — and the `elsewhere` form applies when no item matches.

    [safir-2014]: "from this single element, all anaphoric diversity
    is morphological" -/
structure MinPronInventory (Form : Type) where
  /-- Context-specific Vocabulary Items. -/
  items : List (DistributedMorphology.VocabularyItem BVAContext Form)
  /-- Default exponence: applies when no specific item matches.
      Crosslinguistically, this is the pronoun form ([safir-2014]). -/
  elsewhere : Form

/-- The Elsewhere Condition: the Subset Principle over the items at the
    context, falling back to the elsewhere (default pronoun) form. -/
def MinPronInventory.realize {Form : Type}
    (inv : MinPronInventory Form) (ctx : BVAContext) : Form :=
  (DistributedMorphology.subsetPrinciple inv.items [ctx]).getD inv.elsewhere

/-- A language's realized form for controlled subjects specifically.
    This is the function that distinguishes null-PRO from overt-PRO languages. -/
def MinPronInventory.controlForm {Form : Type}
    (inv : MinPronInventory Form) : Form :=
  inv.realize .controlledSubject

/-! ### Standard Surface Forms -/

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

/-! ### Syncretism with the referential pronoun -/

/-- The contexts in which an inventory's minimal pronoun is syncretic with the referential
pronoun are those that no context-specific item overrides, so that the elsewhere form surfaces
([kratzer-2009], [safir-2014]). -/
def MinPronInventory.syncretic {Form : Type} [DecidableEq Form]
    (inv : MinPronInventory Form) : Finset BVAContext :=
  {c | inv.realize c = inv.elsewhere}

end Minimalist.MinimalPronoun
