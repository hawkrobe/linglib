import Lab.Colinguistics.QuantifiedLimitedSymmetry

/-!
# Export the projection verdicts

Writes the verdicts that `Eval` and `Lab` prove for the theories of presupposition projection as
JSON, for `scripts/gen_eval_page.py`. A verdict is the right-hand side of a proved equation,
instantiated at a theory and a cell and reduced to a constructor by Lean, so the page shows what
the theorems say and nothing typed by hand; a theorem that rests on `sorry` stops the export. Run
from the repository root, after building `Lab`:

```
lake env lean scripts/eval_page/Export.lean
```

The output path is `$EVAL_PAGE_JSON`, by default `.lake/build/eval-page/verdicts.json`.
-/

open Lean Meta

namespace EvalPage

/-- The constructors of an inductive type. -/
def ctors (ty : Name) : MetaM (List Name) := do
  let .inductInfo info ← getConstInfo ty | throwError "{ty} is not an inductive type"
  return info.ctors

/-- The `i`-th conjunct (from 1) of a right-nested conjunction with `n` conjuncts. -/
partial def conjunct (e : Expr) (i n : Nat) : MetaM Expr := do
  if n ≤ 1 then return e
  let some (a, b) := (← whnfR e).and? | throwError "not a conjunction: {e}"
  if i = 1 then return a else conjunct b (i - 1) (n - 1)

/-- The right-hand side of the equation that a proof proves, or of one conjunct of it. -/
def rhs (proof : Expr) (i n : Nat := 1) : MetaM Expr := do
  let stmt ← conjunct (← instantiateMVars (← inferType proof)) i n
  let some (_, _, r) := (← whnfR stmt).eq? | throwError "not an equation: {stmt}"
  return r

/-- A closed term reduced to its tree of constructors: a constructor without fields is its name, a
constructor with fields is its name and theirs. -/
partial def ctorTree (e : Expr) : MetaM Json := do
  let e ← whnf e
  let .const c _ := e.getAppFn | throwError "does not reduce to a constructor: {e}"
  let .ctorInfo info ← getConstInfo c | throwError "does not reduce to a constructor: {e}"
  let fields := e.getAppArgs.extract info.numParams e.getAppNumArgs
  if fields.isEmpty then return toJson c.getString!
  return Json.mkObj [("ctor", toJson c.getString!), ("args", toJson (← fields.mapM ctorTree))]

/-- The elements of a finite set written as a literal, `∅`, `{a}` or `{a, b, …}`. -/
partial def literalElems (e : Expr) : MetaM (List Expr) := do
  let e := e.consumeMData
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``EmptyCollection.emptyCollection, _ => return []
  | some ``Singleton.singleton, args => return [args[3]!]
  | some ``Insert.insert, args => return args[3]! :: (← literalElems args[4]!)
  | _, _ => throwError "not a finite set literal: {e}"

/-- The module that declares a constant. -/
def moduleOf (n : Name) : MetaM Name := do
  let env ← getEnv
  let some i := env.getModuleIdxFor? n | throwError "{n} is not imported"
  return env.header.moduleNames[i.toNat]!

/-- A constant with the module that declares it and its docstring. -/
def declJson (n : Name) : MetaM Json := do
  return Json.mkObj [("name", toJson n.toString), ("module", toJson (← moduleOf n).toString),
    ("doc", toJson ((← findDocString? (← getEnv) n).getD ""))]

/-- A theorem, refused if it rests on `sorry`: a mark the page shows is a proof. -/
def theoremJson (n : Name) : MetaM Json := do
  if (← collectAxioms n).contains ``sorryAx then throwError "{n} depends on sorry"
  declJson n

/-- A verdict, with the theorem whose equation gives it. -/
def verdictRow (dataset theory cell : String) (thm : Name) (value : Expr) : MetaM Json := do
  return Json.mkObj [("dataset", toJson dataset), ("theory", toJson theory), ("cell", toJson cell),
    ("verdict", ← ctorTree value), ("theorem", ← theoremJson thm)]

open Eval.Projection

def chemlaSchlenker2012 (accounts constructions orders : List Name) : MetaM (Array Json) := do
  let mut rows := #[]
  for k in constructions do
    for o in orders do
      let cell := s!"{k.getString!}.{o.getString!}"
      let obs ← mkAppM ``ChemlaSchlenker2012.observed_eq #[mkConst k, mkConst o]
      rows := rows.push <| Json.mkObj [("dataset", "chemla-schlenker-2012"), ("cell", toJson cell),
        ("observed", ← ctorTree (← rhs obs 2 2)),
        ("theorem", ← theoremJson ``ChemlaSchlenker2012.observed_eq)]
      for a in accounts do
        let pf ← mkAppM ``ChemlaSchlenker2012.verdict_eq #[mkConst a, mkConst k, mkConst o]
        rows := rows.push (← verdictRow "chemla-schlenker-2012" a.toString cell
          ``ChemlaSchlenker2012.verdict_eq (← rhs pf 2 2))
      let pf ← mkAppM ``Lab.Colinguistics.verdict_chemlaSchlenker2012 #[mkConst k, mkConst o]
      rows := rows.push (← verdictRow "chemla-schlenker-2012"
        (``Lab.Colinguistics.limitedSymmetry).toString cell
        ``Lab.Colinguistics.verdict_chemlaSchlenker2012 (← rhs pf))
  return rows

def chemla2009a (accounts : List Name) : MetaM (Array Json) := do
  let parsers := [(``Chemla2009a.global, ``Chemla2009a.stipulations_global,
      ``Chemla2009a.verdict_global),
    (``Chemla2009a.stipulated, ``Chemla2009a.stipulations_stipulated,
      ``Chemla2009a.verdict_stipulated),
    (``Chemla2009a.oneStep, ``Chemla2009a.stipulations_oneStep, ``Chemla2009a.verdict_oneStep)]
  let mut rows := #[Json.mkObj [("dataset", "chemla-2009a"), ("cell", "experiment1"),
    ("observed", ← ctorTree (← rhs (mkConst ``Chemla2009a.observed_eq))),
    ("theorem", ← theoremJson ``Chemla2009a.observed_eq)],
    Json.mkObj [("dataset", "chemla-2009a"),
      ("graduation", ← theoremJson ``Chemla2009a.parse_oneStep)]]
  for (i, parser, stipulations, verdict) in (List.range 3).zip parsers do
    let elems ← literalElems (← rhs (mkConst stipulations))
    rows := rows.push <| Json.mkObj [("dataset", "chemla-2009a"), ("parser", ← declJson parser),
      ("stipulations", toJson (← elems.mapM ctorTree)), ("theorem", ← theoremJson stipulations)]
    for a in accounts do
      let pf ← mkAppM verdict #[mkConst a]
      rows := rows.push (← verdictRow "chemla-2009a" a.toString parser.getString! verdict
        (← rhs pf))
    rows := rows.push (← verdictRow "chemla-2009a" (``Lab.Colinguistics.limitedSymmetry).toString
      parser.getString! ``Lab.Colinguistics.verdict_chemla2009a
      (← rhs (mkConst ``Lab.Colinguistics.verdict_chemla2009a) (i + 1) 3))
  return rows

def exportAll : MetaM Json := do
  let accounts ← ctors ``Account
  let theories := (← accounts.mapM fun a ↦ return Json.mkObj [("id", toJson a.toString),
      ("source", "registered"), ("decl", ← declJson a)]) ++
    [Json.mkObj [("id", toJson (``Lab.Colinguistics.limitedSymmetry).toString), ("source", "lab"),
      ("decl", ← declJson ``Lab.Colinguistics.limitedSymmetry)]]
  let rows := (← chemlaSchlenker2012 accounts (← ctors ``_root_.ChemlaSchlenker2012.Construction)
    (← ctors ``_root_.ChemlaSchlenker2012.Order)) ++ (← chemla2009a accounts)
  return Json.mkObj [("theories", toJson theories), ("rows", toJson rows)]

end EvalPage

#eval show MetaM Unit from do
  let path := (← IO.getEnv "EVAL_PAGE_JSON").getD ".lake/build/eval-page/verdicts.json"
  if let some dir := (System.FilePath.mk path).parent then IO.FS.createDirAll dir
  IO.FS.writeFile path (← EvalPage.exportAll).pretty
