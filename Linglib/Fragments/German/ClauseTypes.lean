import Linglib.Syntax.Clause.Form

/-!
# German Clause Types

German clause-type taxonomy: five clause types distinguished by verb
position (V2 vs verb-last) and complementizer presence (dass vs not),
encoded as an indexed refinement of the framework-agnostic
`Clause.Form`. Descriptive German syntax; the sentence-mood
analysis built on this taxonomy ([gutzmann-2015], Ch 5: which mood
operators each clause type composes) lives in
`Studies/Gutzmann2015.lean`.

| Clause type       | Example                |
|-------------------|------------------------|
| dass-VL           | "Dass du kommst!"      |
| V2-declarative    | "Jim wohnt in Berlin." |
| VL-interrogative  | "Wann Peter kommt?"    |
| V2-interrogative  | "Kommt Peter?"         |
| Imperative        | "Tritt zurück!"        |
-/

namespace German.ClauseTypes

open Clause (Form)

/-! ### `GermanClauseType` as `Form`-indexed inductive

`GermanClauseType` distinguishes clauses by both verb position (V2 vs
VL) and complementizer presence (dass vs not), where `Form` only
records the matrix-vs-embedded question / declarative word-order
distinction. We encode the refinement *structurally* as an indexed
inductive `GermanClauseType : Form → Type`:

| `GermanClauseType` | `Form`        |
|--------------------|---------------------|
| `dassVL`           | `declarative`       |
| `v2Declarative`    | `declarative`       |
| `v2Interrogative`  | `matrixQuestion`    |
| `vlInterrogative`  | `embeddedQuestion`  |
| `imperative`       | `declarative`       |

Two consequences fall out of the indexing rather than requiring
separate proof:

1. **No bridge function.** The "projection to `Form`" is the
   type-level index — `(ct : GermanClauseType f)` witnesses both the
   refined value *and* its `Form` projection `f` simultaneously.
2. **`(ct : GermanClauseType .matrixQuestion)` is *exactly* the
   v2Interrogative case.** `cases ct` on this type produces a single
   branch, capturing the structural fact that "matrix-question German
   clause" picks out v2Interrogative without auxiliary filtering. -/

/-- German clause types distinguished by verb position and complementizer,
indexed by their `Clause.Form` projection. -/
inductive GermanClauseType : Form → Type where
  /-- dass-VL: complementizer clause, verb-last.
      Form-level: declarative. -/
  | dassVL : GermanClauseType .declarative
  /-- V2-declarative: finite verb in C⁰.
      Form-level: declarative. -/
  | v2Declarative : GermanClauseType .declarative
  /-- V2-interrogative: verb-second.
      Form-level: matrix question. -/
  | v2Interrogative : GermanClauseType .matrixQuestion
  /-- VL-interrogative: verb-last.
      Form-level: embedded question. -/
  | vlInterrogative : GermanClauseType .embeddedQuestion
  /-- Imperative.
      Form-level: declarative (no SAI inversion). -/
  | imperative : GermanClauseType .declarative
  deriving DecidableEq, Repr

/-! ### Structural consequences of the indexing -/

/-- A matrix-question German clause type is *exactly* `v2Interrogative`.
Pattern matching on `GermanClauseType .matrixQuestion` produces a single
constructor by the indexing. -/
theorem matrix_question_is_v2_interrog (ct : GermanClauseType .matrixQuestion) :
    ct = .v2Interrogative := by
  cases ct; rfl

/-- An embedded-question German clause type is *exactly* `vlInterrogative`. -/
theorem embedded_question_is_vl_interrog (ct : GermanClauseType .embeddedQuestion) :
    ct = .vlInterrogative := by
  cases ct; rfl

end German.ClauseTypes
