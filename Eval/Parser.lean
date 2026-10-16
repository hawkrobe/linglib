module

public import Mathlib.Data.Finmap

/-!
# Parsers

A theory assigns its own parses to the sentences of a dataset in two ways. By a rule, it parses a
sentence from its parse in a fragment that the theories share, so that it parses alike every
sentence of the same shared parse, including sentences no dataset holds yet. By a table, it
stipulates the parse of a single sentence. A parser has both, and the table overrides the rule on
the sentences it lists (`Eval.Parser`). A verdict that rests on a listed sentence rests on a
stipulation, so the listed sentences are what a parser costs beyond its rule
(`Parser.stipulations`). A rule that reproduces every stipulated parse replaces the table without
changing a parse (`Parser.parse_ofRule_eq`).
-/

@[expose] public section

namespace Eval

/-- How a theory parses the sentences `S` of a dataset into its parses `P`: by a rule on the parse
of a sentence in a shared fragment `F`, defined on the shared parses the theory covers, and by a
table of parses stipulated for single sentences, which overrides the rule. -/
structure Parser (S F P : Type*) where
  /-- The theory's parse of the sentences of each shared parse it covers. -/
  rule : F → Option P
  /-- The parses stipulated for single sentences. -/
  table : Finmap fun _ : S ↦ P

namespace Parser

variable {S F P : Type*} (π : Parser S F P)

/-- The sentences whose parses are stipulated. -/
def stipulations : Finset S := π.table.keys

/-- The parser of a rule alone. -/
def ofRule (r : F → Option P) : Parser S F P := ⟨r, ∅⟩

@[simp] theorem stipulations_ofRule (r : F → Option P) :
    (ofRule r : Parser S F P).stipulations = ∅ :=
  Finmap.keys_empty

variable [DecidableEq S] (shared : S → F)

/-- The parse of a sentence, given its shared parse: the stipulated one if the table lists the
sentence, and the rule's otherwise. -/
def parse (s : S) : Option P := (π.table.lookup s).or (π.rule (shared s))

@[simp] theorem parse_ofRule (r : F → Option P) (s : S) :
    (ofRule r).parse shared s = r (shared s) := by
  simp [parse, ofRule]

theorem parse_of_notMem {s : S} (hs : s ∉ π.stipulations) :
    π.parse shared s = π.rule (shared s) := by
  rw [parse, Finmap.lookup_eq_none.2 (Finmap.mem_keys.not.1 hs), Option.none_or]

/-- A rule that reproduces every stipulated parse, and agrees with the parser's rule on the other
sentences, parses every sentence as the parser does. -/
theorem parse_ofRule_eq {r : F → Option P}
    (hstip : ∀ s p, π.table.lookup s = some p → r (shared s) = some p)
    (hrule : ∀ s ∉ π.stipulations, r (shared s) = π.rule (shared s)) :
    (ofRule r).parse shared = π.parse shared := by
  funext s
  rw [parse_ofRule]
  by_cases hs : s ∈ π.stipulations
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1
      (Finmap.lookup_isSome.2 (Finmap.mem_keys.1 hs))
    rw [hstip s p hp, parse, hp, Option.some_or]
  · rw [hrule s hs, parse_of_notMem π shared hs]

end Parser

end Eval
