/-!
# Shared Slavic Verbal-Prefix Parameters
@cite{svenonius-2004} @cite{istratkova-2004} @cite{jablonska-2004}

Types and parameters shared across Slavic verbal-prefix fragments
(Russian, Polish, Bulgarian) following @cite{svenonius-2004}'s
**lexical / superlexical** distinction. Mirrors the
`Fragments/Mayan/Params.lean` pattern: shared cluster-level types
factored out so per-language fragments don't triplicate them.

Aspect is reused from `Linglib.Core.Lexical.UD` (UD-tag canonical
`Aspect.Imp` / `Aspect.Perf`) rather than redefined per Slavic
fragment.

## Main definitions

* `Aspect` — perfective vs imperfective (binary distinction sufficient
  for Slavic; the richer UD-tagset Aspect enum lives in
  `Linglib.Core.Lexical.UD`).
* `SuperlexicalSubtype` — six aspectual subtypes (paper §3).
* `PrefixClass` — `lexical` or `superlexical _` ADT.
* `PrefixClass.IsSuperlexical` predicate with `DecidablePred` instance.

## Cross-references

- `Fragments/Slavic/Russian/VerbalPrefixes.lean`
- `Fragments/Slavic/Polish/VerbalPrefixes.lean`
- `Fragments/Slavic/Bulgarian/VerbalPrefixes.lean`

-/

namespace Fragments.Slavic

/-- Slavic grammatical aspect — the binary perfective / imperfective
    contrast. -/
inductive Aspect
  | perfective
  | imperfective
  deriving DecidableEq

/-- Aspectual subtypes for the superlexical class
    (@cite{svenonius-2004} §3). The same six categories used across
    Russian, Polish, and Bulgarian VPC fragments. -/
inductive SuperlexicalSubtype
  | delimitative
  | cumulative
  | completive
  | repetitive
  | inceptive
  | distributive
  deriving DecidableEq

/-- @cite{svenonius-2004}'s lexical / superlexical split as a single
    ADT — the superlexical case carries its subtype, eliminating the
    need for an `Option`-typed companion field plus a consistency
    lemma. -/
inductive PrefixClass
  | lexical
  | superlexical (subtype : SuperlexicalSubtype)
  deriving DecidableEq

namespace PrefixClass

/-- A `PrefixClass` is *superlexical* iff it is the `superlexical _` case. -/
def IsSuperlexical : PrefixClass → Prop
  | .lexical          => False
  | .superlexical _   => True

instance : DecidablePred IsSuperlexical
  | .lexical        => isFalse id
  | .superlexical _ => isTrue trivial

end PrefixClass

end Fragments.Slavic
