import Linglib.Data.UD.Basic
import Linglib.Syntax.Tree.Basic

/-!
# Default Category System (UD-grounded)

`Syntax.Cat` — the default instantiation of `Syntax.Tree`'s category
parameter `C`, grounded in Universal Dependencies UPOS
([de-marneffe-zeman-2021]). Word-level categories via `head : UPOS → Cat`,
phrasal via `proj : UPOS → Cat`, plus `S` and `CP`.

Split from `Syntax/Tree/Basic.lean` so that category-generic consumers
(e.g. the type-driven composition engine, which ignores categories) do
not carry the UD dataset in their transitive imports.
-/

namespace Syntax

/-- Default syntactic category system grounded in Universal Dependencies
UPOS ([de-marneffe-zeman-2021]).

- `head pos` — word-level (terminal): wraps a UPOS tag directly
- `proj pos` — maximal X-bar projection of a UPOS head
- `S` — sentence/clause (not a projection of a single lexical head)
- `CP` — complementizer phrase

Phrasal categories are derived systematically: NP = `proj .NOUN`,
VP = `proj .VERB`, DP = `proj .DET`, ConjP = `proj .CCONJ`, etc.

This is one possible instantiation of `Tree`'s `C` parameter.
Framework-specific category systems (CCG functors, Minimalist
feature bundles, etc.) can be used instead. -/
inductive Cat where
  | head : UD.UPOS → Cat
  | proj : UD.UPOS → Cat
  | S
  | CP
  deriving DecidableEq, Repr

instance : Inhabited Cat := ⟨.S⟩

instance : BEq Cat := ⟨λ a b => decide (a = b)⟩

instance : LawfulBEq Cat where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

-- ── Abbreviations ──────────────────────────────────────────────────
-- Short names matching traditional notation. Each abbreviation is
-- marked @[match_pattern] so it can be used in pattern position.

namespace Cat

-- Word-level (heads / terminals)
@[match_pattern] abbrev N     : Cat := .head .NOUN
@[match_pattern] abbrev V     : Cat := .head .VERB
@[match_pattern] abbrev Det   : Cat := .head .DET
@[match_pattern] abbrev Adj   : Cat := .head .ADJ
@[match_pattern] abbrev Adv   : Cat := .head .ADV
@[match_pattern] abbrev P     : Cat := .head .ADP
@[match_pattern] abbrev Conj  : Cat := .head .CCONJ
@[match_pattern] abbrev Neg   : Cat := .head .PART
@[match_pattern] abbrev C     : Cat := .head .SCONJ
@[match_pattern] abbrev Num   : Cat := .head .NUM
@[match_pattern] abbrev Pron  : Cat := .head .PRON
@[match_pattern] abbrev Aux   : Cat := .head .AUX

-- Phrasal (maximal projections)
@[match_pattern] abbrev NP    : Cat := .proj .NOUN
@[match_pattern] abbrev VP    : Cat := .proj .VERB
@[match_pattern] abbrev DP    : Cat := .proj .DET
@[match_pattern] abbrev PP    : Cat := .proj .ADP
@[match_pattern] abbrev AdjP  : Cat := .proj .ADJ
@[match_pattern] abbrev AdvP  : Cat := .proj .ADV
@[match_pattern] abbrev ConjP : Cat := .proj .CCONJ
@[match_pattern] abbrev NegP  : Cat := .proj .PART
@[match_pattern] abbrev NumP  : Cat := .proj .NUM

end Cat

end Syntax
