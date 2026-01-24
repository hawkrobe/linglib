# Milestone: End-to-End Scalar Implicature

**Goal**: Derive "not all" from "some" through the full pipeline, using both NeoGricean and RSA, and prove they agree.

## Current State

| Layer | Status | Key File |
|-------|--------|----------|
| CCG Syntax | ✓ Complete | `Theories/CCG/Basic.lean` |
| Syntax→Semantics | ✓ Types align | `Theories/CCG/Semantics.lean` |
| Montague Semantics | ✓ Complete | `Theories/Montague/*.lean` |
| Semantic Derivation | ✓ Interface | `Theories/Montague/SemDerivation.lean` |
| CCG→SemDeriv | ✓ Bridge | `Theories/CCG/Interpret.lean` |
| NeoGricean | ✓ Derives SI | `Theories/NeoGricean/ScalarImplicatures.lean` |
| RSA | ✓ Derives SI | `Theories/RSA/ScalarImplicatures.lean` |
| **Connected pipeline** | ✓ Complete | `Theories/RSA/Comparison.lean` |

## Architecture: Layered Dependencies

Montague defines what it needs from syntax; specific syntax theories implement that interface:

```
                    Montague
                   (defines SemDerivation interface,
                    lexicon, alternatives)
                        ↑
          ┌─────────────┼─────────────┐
          │             │             │
         CCG          HPSG      Minimalism
      (implements   (could      (could
       interface)   implement)  implement)
          │
          ▼
      Pragmatics layer
      (consumes SemDerivation,
       agnostic to syntax source)
          │
    ┌─────┴─────┐
    │           │
NeoGricean     RSA
    │           │
    └─────┬─────┘
          ▼
    Comparison
```

**Key principle**: Pragmatics imports from Montague, not from CCG. CCG is just one way to produce the semantic derivations that pragmatics consumes.

## The Pipeline

```
"Some students passed"
        │
        ▼
┌───────────────────┐
│   CCG Derivation  │  NP/N    N       VP
│                   │  some  students  passed
└─────────┬─────────┘
          │ interpret
          ▼
┌───────────────────┐
│ Montague Meaning  │  ∃x. student(x) ∧ passed(x)
│                   │  + alternatives: {∀x. student(x) → passed(x)}
└─────────┬─────────┘
          │
    ┌─────┴─────┐
    ▼           ▼
┌────────┐  ┌────────┐
│NeoGric.│  │  RSA   │
│        │  │        │
│¬Bel(∀) │  │P(¬∀|u) │
│  +comp │  │  high  │
│ =Bel¬∀ │  │        │
└────┬───┘  └────┬───┘
     │           │
     ▼           ▼
   "not all"   "not all"
```

## Files to Create/Modify

### Phase 1: Semantic Foundation (Montague layer)

**`Montague/Lexicon.lean`** (NEW)

Lexical entries with semantic values AND Horn set membership:

```lean
/-- A lexical entry bundles form, type, denotation, and scalar alternatives -/
structure LexEntry (m : Model) where
  form : String
  ty : Ty
  denot : m.interpTy ty
  hornSet : Option HornSet  -- None for non-scalar items

def some_lex : LexEntry toyModel := {
  form := "some"
  ty := Ty.det
  denot := some_sem toyModel
  hornSet := some quantifierSet
}
```

**`Montague/SemDerivation.lean`** (NEW)

The interface that any syntax theory must produce:

```lean
/-- A semantic derivation — what Montague needs from syntax -/
structure SemDerivation (m : Model) where
  surface : List String              -- the words
  ty : Ty                            -- result type
  meaning : m.interpTy ty            -- denotation
  scalarItems : List (Nat × LexEntry m)  -- positions with scalar items

/-- Generate sentential alternatives by replacing scalar items -/
def sententialAlternatives (d : SemDerivation m) (ctx : ContextPolarity)
    : List (SemDerivation m) := ...
```

### Phase 2: CCG Implements the Interface

**`CCG/Interpret.lean`** (NEW)

CCG produces Montague's `SemDerivation`:

```lean
import Linglib.Theories.Montague.SemDerivation

/-- Convert a CCG derivation to a SemDerivation -/
def toSemDerivation (deriv : DerivStep) (lex : CCGLexicon m) : SemDerivation m := ...

/-- Example: "some students passed" via CCG -/
def someStudentsPassed_ccg : DerivStep := ...
def someStudentsPassed : SemDerivation toyModel :=
  toSemDerivation someStudentsPassed_ccg toyLexicon
```

*(HPSG/Interpret.lean and Minimalism/Interpret.lean could do the same)*

### Phase 3: NeoGricean Consumes SemDerivation

**`NeoGricean/ScalarImplicatures.lean`** (EXTEND)

Imports from Montague, NOT from CCG:

```lean
import Linglib.Theories.Montague.SemDerivation  -- syntax-agnostic!

/-- Derive scalar implicatures from a semantic derivation -/
def deriveFromDerivation (d : SemDerivation m) (ctx : ContextPolarity)
    : ScalarImplicatureResult :=
  let alts := sententialAlternatives d ctx
  deriveScalarImplicatures d.meaning (alts.map (·.meaning)) ctx

/-- "Some students passed" → "not all students passed" -/
theorem some_students_not_all :
    let result := deriveFromDerivation someStudentsPassed .upward
    result.implicatures.contains (negation allStudentsPassed.meaning) := ...
```

### Phase 4: RSA Consumes SemDerivation

**`RSA/ScalarImplicatures.lean`** (NEW)

Also imports from Montague, NOT from CCG:

```lean
import Linglib.Theories.Montague.SemDerivation  -- syntax-agnostic!

/-- World type for scalar implicature scenarios -/
inductive ScalarWorld where
  | none | some | all

/-- Build RSA setup from a semantic derivation -/
def rsaFromDerivation (d : SemDerivation m) : FiniteSemanticBackend := ...

/-- RSA derives "not all" (higher probability for .some than .all) -/
theorem rsa_some_not_all :
    l1_some_students .some > l1_some_students .all := ...
```

### Phase 5: Agreement Theorem

**`RSA/Comparison.lean`** (NEW)

```lean
import Linglib.Theories.NeoGricean.ScalarImplicatures
import Linglib.Theories.RSA.ScalarImplicatures

/-- Both theories derive "not all" from "some" -/
theorem scalar_implicature_agreement :
    (deriveFromDerivation someStudentsPassed .upward).hasImplicature (¬all)
    ∧
    l1_some_students .some > l1_some_students .all := ...
```

## Dependency Graph

```
Montague/Lexicon.lean ◄─── Montague/SemDerivation.lean
        │                           │
        └───────────┬───────────────┘
                    │
        ┌───────────┼───────────────┐
        ▼           ▼               ▼
   CCG/Interpret  HPSG/Interpret  Minimalism/Interpret
   (produces      (could produce  (could produce
    SemDerivation) SemDerivation)  SemDerivation)
        │
        │ (example derivations)
        ▼
┌───────────────────────────────────────┐
│     Montague/SemDerivation            │
│  (pragmatics imports THIS, not CCG)   │
└───────────────────┬───────────────────┘
                    │
          ┌─────────┴─────────┐
          ▼                   ▼
  NeoGricean/              RSA/
  ScalarImplicatures    ScalarImplicatures
          │                   │
          └─────────┬─────────┘
                    ▼
            RSA/Comparison.lean
```

## Implementation Order

| Step | File | What it provides | Status |
|------|------|------------------|--------|
| 1 | `Montague/Lexicon.lean` | `SemLexEntry` with scale membership | ✅ Done |
| 2 | `Montague/SemDerivation.lean` | `SemDeriv.Derivation` interface | ✅ Done |
| 3 | `CCG/Interpret.lean` | `toDerivation`, example derivations | ✅ Done |
| 4 | `NeoGricean/ScalarImplicatures.lean` | `deriveFromDerivation`, proof of SI | ✅ Done |
| 5 | `RSA/ScalarImplicatures.lean` | `rsaFromDerivation`, proof of SI | ✅ Done |
| 6 | `PragmaticComparison.lean` | Agreement theorem | ✅ Done |

**Key insight**: Steps 1-2 are the semantic interface. Step 3 is CCG implementing it. Steps 4-6 are pragmatics consuming it (syntax-agnostic).

## Success Criteria

1. **Compiles**: `lake build` succeeds
2. **Computable**: `#eval` on example derivations
3. **Proven**:
   - `some_students_not_all` (NeoGricean)
   - `rsa_some_not_all` (RSA)
   - `scalar_implicature_agreement`
4. **Clean imports**: Each layer only imports what it needs

## Stretch Goals

- [ ] DE blocking: Both theories predict no SI in "No student ate some cookies"
- [ ] Embedded implicatures: "John believes some students passed"
- [ ] Characterize divergence: When do NeoGricean and RSA make different predictions?

## Future Refactoring

- [ ] **Parameterized Lexicon**: Restructure Montague lexicon to support competing analyses:
  ```
  Montague/Lexicon/
  ├── Numerals/{LowerBound,Exact}.lean
  ├── Modals/{Kratzer,Simple}.lean
  └── Quantifiers/...
  ```
  Current `Numbers.lean` → `Lexicon/Numerals/{LowerBound,Exact}.lean`
  Each variant defines denotations + empirical predictions
