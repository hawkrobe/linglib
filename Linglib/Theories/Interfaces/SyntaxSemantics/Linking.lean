import Linglib.Theories.Semantics.Events.ThematicRoles

/-!
# Linking Theory Interface

General interface for theories of argument realization — how verbs'
arguments get their thematic roles.

Theories in the literature differ along three dimensions:

1. **What the verb contributes** (lexical semantics, meaning components,
   event structure templates, root meaning, entailment profiles)
2. **What the structure contributes** (Voice flavor, applicative type,
   sub-event decomposition, construction type, causal chain position)
3. **Which direction the mapping goes** (verb → role, structure → role,
   or both jointly)

The `LinkingTheory` structure captures this variation by parameterizing
over BOTH the verb representation type (`Verb`) and the structural
context type (`Ctx`). Theories that ignore structure use `Unit` for
`Ctx`; theories that care about Voice use `VoiceFlavor`; theories
with richer decompositions bring their own types.

The role output is always `ThetaRole` — the shared vocabulary that
makes theories comparable against fragment data.

The `compatible` field captures gradient verb–construction pairing
(Levin 2004): a verb may be compatible with multiple structural
contexts (causative alternation verbs appear with both agentive and
non-thematic Voice). Singleton lists express categorical predictions;
multi-element lists express gradient compatibility.

## Coverage

Accounts expressible via this interface (non-exhaustive):

| Account | Ctx | compatible | predict uses verb? |
|---------|-----|------------|-------------------|
| Severing (Kratzer 1996) | VoiceFlavor | verb-constrained | no |
| Lexicalist (Levin & RH 1998) | Unit | always [()] | yes |
| Zero morphology (Pesetsky 1995) | (custom) | verb-constrained | yes |
| First Phase Syntax (Ramchand 2008) | (custom) | verb-constrained | yes |
| CxG (Goldberg 1995) | (custom) | broad | no |
| Proto-roles (Dowty 1991) | Unit | always [()] | yes (via ASP) |
| Applicatives (Pylkkänen 2008) | (custom) | verb-constrained | no |

## References

- Kratzer, A. (1996). Severing the external argument from its verb.
- Levin, B. & M. Rappaport Hovav (1995). *Unaccusativity*.
- Rappaport Hovav, M. & B. Levin (1998). Building verb meanings.
- Pesetsky, D. (1995). *Zero Syntax*.
- Dowty, D. (1991). Thematic proto-roles and argument selection.
- Ramchand, G. (2008). *Verb Meaning and the Lexicon*.
- Goldberg, A. (1995). *Constructions*.
- Pylkkänen, L. (2008). *Introducing Arguments*.
- Levin, B. (2004). Verbs and constructions: Where next?
- Beavers, J. & A. Koontz-Garboden (2020). *The Roots of Verbal Meaning*.
-/

namespace Interfaces.SyntaxSemantics

-- ════════════════════════════════════════════════════════════════════════
-- § 1. Argument position
-- ════════════════════════════════════════════════════════════════════════

/-- Which argument position in the clause we're asking about.
    Theory-neutral: expressed as grammatical functions, not structural
    positions (Spec-vP, Comp-VP, etc.), so that theories with different
    structural vocabularies can all target the same output. -/
inductive ArgPosition where
  | subject         -- Grammatical subject (external or raised)
  | directObject    -- Direct object
  | indirectObject  -- Indirect object / dative
  | oblique         -- Oblique / PP complement
  | applied         -- Applied argument (Pylkkänen 2008)
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════════════════════════
-- § 2. LinkingTheory
-- ════════════════════════════════════════════════════════════════════════

/-- A linking theory, parameterized by verb representation and structural
    context type.

    - `Verb`: what the theory needs to know about the verb. Typically
      `VerbCore`, but could be `EntailmentProfile` (Dowty) or
      `EventTemplate` (Rappaport Hovav & Levin).
    - `Ctx`: what the theory considers relevant about the syntactic
      structure beyond the verb itself:
      - `Unit` for theories that derive everything from the verb
      - `VoiceFlavor` for the severing account (Kratzer 1996)
      - A richer type for Ramchand, Goldberg, Pylkkänen, etc.

    The theory provides two functions:
    - `compatible`: which structural contexts can this verb appear in?
    - `predict`: in a given context, what theta role does each position get?

    This separation captures the key theoretical distinction:
    - **Pure constructional** (Borer, strong Goldberg): `compatible` is
      broad — the verb is promiscuous; structure determines roles
    - **Pure lexicalist** (Levin): `compatible` always returns `[()]` —
      there is nothing structural to vary
    - **Hybrid** (Pesetsky, Levin 2004): `compatible` returns a
      verb-constrained subset — gradient compatibility -/
structure LinkingTheory (Verb Ctx : Type) where
  /-- Which structural contexts this verb is compatible with.
      Singleton = categorical. Multiple = gradient (alternation). -/
  compatible : Verb → List Ctx
  /-- Predict each argument's theta role in a given context.
      Returns `none` for positions the theory is silent about. -/
  predict : Verb → Ctx → ArgPosition → Option ThetaRole

-- ════════════════════════════════════════════════════════════════════════
-- § 3. Testing predictions against fragment data
-- ════════════════════════════════════════════════════════════════════════

/-- Does the theory's prediction match the observed role at a given
    position, for at least one compatible structural context?

    For alternation verbs (multiple compatible contexts), the test passes
    if ANY context produces the correct prediction — the fragment entry
    records one use of the verb, not all possible uses. -/
def LinkingTheory.matchesAt {Verb Ctx : Type} [BEq Ctx]
    (th : LinkingTheory Verb Ctx) (v : Verb) (pos : ArgPosition)
    (actual : Option ThetaRole) : Bool :=
  (th.compatible v).any fun ctx => th.predict v ctx pos == actual

end Interfaces.SyntaxSemantics
