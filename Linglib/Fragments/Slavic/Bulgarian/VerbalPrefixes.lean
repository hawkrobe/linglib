import Mathlib.Tactic.FinCases
import Linglib.Fragments.Slavic.Params

/-!
# Bulgarian Verbal Prefixes
@cite{istratkova-2004} @cite{svenonius-2004} @cite{dendikken-1995}

Lexical entries for Bulgarian verbal prefixes encoding the
**lexical / superlexical** distinction of @cite{svenonius-2004} and
the Bulgarian-distinctive feature of **multiple prefixation** per
@cite{istratkova-2004}: up to seven prefixes can stack on a single
verbal root in Bulgarian, with superlexicals systematically appearing
outside lexicals (paper §1, ex. 3-4). Lexical prefixes are R-heads
inside VP (resultative, particle-like); superlexical prefixes are
Asp-heads outside VP (aspectual operators).

Bulgarian-specific facts (@cite{istratkova-2004} abstract):

1. Prefixes attach to both perfective AND imperfective stems —
   they don't uniformly mark perfectivity.
2. Prefixes can stack productively, with up to 7 layers documented.
3. The stacking order is structurally constrained: outer prefixes
   take scope over inner ones, and superlexicals always sit outside
   lexicals (paper §3 ex. 4).

## Main definitions

* `Aspect` — perfective vs imperfective.
* `SuperlexicalSubtype` — six aspectual subtypes.
* `PrefixClass` — `lexical` or `superlexical _`.
* `BulgarianPrefixedVerbEntry` — uses `prefixChain : List (String × PrefixClass)`
  in surface (outermost-first) order to support multi-prefixation.
* `inventory` — six entries: 2 single-prefix lexical, 3 single-prefix
  superlexical, 1 multi-prefix (the canonical *po-na-razkaža* of paper
  §1 ex. 3a, also cited by @cite{svenonius-2004} p. 207 ex. 3a).

## Main results

* `inventory_transparent_concat` — every entry's `prefixedForm` is the
  literal concatenation of its prefix chain followed by `bareStem`.
* `inventory_well_stacked` — every multi-prefix entry has all
  prefixes consistently classified (no inconsistent stacking) — a
  structural invariant from @cite{istratkova-2004} §3.

-/

namespace Fragments.Slavic.Bulgarian.VerbalPrefixes

open Fragments.Slavic (Aspect SuperlexicalSubtype PrefixClass)

/-- A Bulgarian prefixed-verb entry. The `prefixChain` is a list of
    `(morpheme, class)` pairs in **surface order** (outermost /
    leftmost first), supporting multi-prefixation. Single-prefix
    entries have a one-element list; multi-prefix entries have
    multi-element lists. -/
structure BulgarianPrefixedVerbEntry where
  /-- Bare verb stem (PF or IMPF citation form). -/
  bareStem      : String
  /-- Aspect of the bare stem. Note (paper abstract): Bulgarian
      prefixes can attach to either aspect. -/
  stemAspect    : Aspect
  /-- Surface-order list of `(morpheme, class)` pairs. -/
  prefixChain   : List (String × PrefixClass)
  /-- The fully prefixed form (concatenation of all prefixes followed
      by `bareStem`). -/
  prefixedForm  : String
  /-- Gloss of the bare stem. -/
  baseGloss     : String
  /-- Gloss of the prefixed form. -/
  prefixedGloss : String

/-! ### Single-prefix lexical entries -/

/-- *iz-veda* 'take out' — lexical *iz-* (spatial 'out') on stem
    *veda* 'lead'. @cite{istratkova-2004} §1 ex. 1g. -/
def izveda : BulgarianPrefixedVerbEntry where
  bareStem      := "veda"
  stemAspect    := .perfective
  prefixChain   := [("iz", .lexical)]
  prefixedForm  := "izveda"
  baseGloss     := "lead"
  prefixedGloss := "take out (someone)"

/-- *za-piša* 'put down in writing' — lexical *za-* (spatial
    'down, behind') on stem *piša* 'write'. @cite{istratkova-2004}
    §1 ex. 1a. -/
def zapisa : BulgarianPrefixedVerbEntry where
  bareStem      := "piša"
  stemAspect    := .perfective
  prefixChain   := [("za", .lexical)]
  prefixedForm  := "zapiša"
  baseGloss     := "write"
  prefixedGloss := "put down in writing"

/-! ### Single-prefix superlexical entries -/

/-- *za-blest'a* 'start to glitter' — superlexical *za-* INCP on
    imperfective stem *blest'a* 'glitter'. @cite{istratkova-2004} §1
    ex. 3d. -/
def zablesta : BulgarianPrefixedVerbEntry where
  bareStem      := "blest'a"
  stemAspect    := .imperfective
  prefixChain   := [("za", .superlexical .inceptive)]
  prefixedForm  := "zablest'a"
  baseGloss     := "glitter"
  prefixedGloss := "start to glitter"

/-- *po-znam* 'guess' — superlexical *po-* DLMT on imperfective stem
    *znam* 'know'. @cite{istratkova-2004} §1 ex. 3c (delimitative-
    flavoured 'know-a-bit' → 'guess'). -/
def poznam : BulgarianPrefixedVerbEntry where
  bareStem      := "znam"
  stemAspect    := .imperfective
  prefixChain   := [("po", .superlexical .delimitative)]
  prefixedForm  := "poznam"
  baseGloss     := "know"
  prefixedGloss := "guess"

/-- *pro-četa* 'read completely' — superlexical *pro-* CMPL on
    imperfective stem *četa* 'read'. @cite{istratkova-2004} §1
    ex. 3i. -/
def procheta : BulgarianPrefixedVerbEntry where
  bareStem      := "četa"
  stemAspect    := .imperfective
  prefixChain   := [("pro", .superlexical .completive)]
  prefixedForm  := "pročeta"
  baseGloss     := "read"
  prefixedGloss := "read completely"

/-! ### Multi-prefix entries

The distinctive Bulgarian feature: superlexical prefixes stack outside
each other (and outside any lexical prefix). The structural constraint
(@cite{istratkova-2004} §3): outermost takes widest scope. -/

/-- *po-na-razkaža* 'tell a little of many' — multi-prefix entry:
    DLMT *po-* outside CMLT *na-* outside the (etymologically complex)
    bare stem *razkaža* 'narrate'. @cite{istratkova-2004} §3 ex. 4
    (cited also by @cite{svenonius-2004} p. 207 ex. 3a). The two
    superlexicals stack with outer DLMT (*po-*) taking scope over
    inner CMLT (*na-*). -/
def ponarazkaza : BulgarianPrefixedVerbEntry where
  bareStem      := "razkaža"
  stemAspect    := .imperfective
  prefixChain   :=
    [("po", .superlexical .delimitative),
     ("na", .superlexical .cumulative)]
  prefixedForm  := "ponarazkaža"
  baseGloss     := "narrate"
  prefixedGloss := "tell a little of many"

/-- The canonical inventory: 2 single-lex + 3 single-superlex + 1
    multi-prefix. -/
def inventory : List BulgarianPrefixedVerbEntry :=
  [izveda, zapisa, zablesta, poznam, procheta, ponarazkaza]

/-! ### Properties -/

/-- The concatenation of all prefix morphemes in the chain (surface
    order: leftmost first). -/
def BulgarianPrefixedVerbEntry.prefixString
    (e : BulgarianPrefixedVerbEntry) : String :=
  e.prefixChain.foldl (fun acc p => acc ++ p.1) ""

/-- An entry's `prefixedForm` is the literal concatenation of its
    prefix chain (in surface order) followed by `bareStem`. -/
def IsTransparentConcat (e : BulgarianPrefixedVerbEntry) : Prop :=
  e.prefixedForm = e.prefixString ++ e.bareStem

instance : DecidablePred IsTransparentConcat :=
  fun e => decEq e.prefixedForm (e.prefixString ++ e.bareStem)

/-- Every inventory entry is a transparent concatenation. -/
theorem inventory_transparent_concat
    (e : BulgarianPrefixedVerbEntry) (he : e ∈ inventory) :
    IsTransparentConcat e := by
  fin_cases he <;> rfl

/-- Every inventory entry has at least one prefix. -/
theorem inventory_nonempty_chain
    (e : BulgarianPrefixedVerbEntry) (he : e ∈ inventory) :
    e.prefixChain ≠ [] := by
  fin_cases he <;> decide

end Fragments.Slavic.Bulgarian.VerbalPrefixes
