import Linglib.Semantics.Verb.Root.Basic

/-!
# Root attachment position

A verb root attaches in one of two structural positions
([beavers-koontz-garboden-2020] ch. 1; the Distributed-Morphology tradition,
Marantz): adjoined to a head, or as a head's complement. The distinction
conditions vVPE eligibility ([kalyakin-2026]), result-state modifier scope, and
the restitutive/repetitive *again* ambiguity ([merchant-2013]).

## Main declarations

* `Root.Position` — complement vs adjoined attachment
-/

namespace Verb

/-! ### Root position -/

/-- Structural attachment position of a verb root, following the
    Distributed-Morphology tradition (Marantz; systematized by
    [beavers-koontz-garboden-2020]):

    - **complement**: root merges as complement of v (inside VP),
      filling the result/state slot (√flat, √crack, √blossom, √drown);
    - **adjoined**: root merges as adjunct to v (outside VP), modifying
      the event (√jog, √toss, √hand).

    The distinction matters beyond root typology: it conditions vVPE
    eligibility ([kalyakin-2026]), result-state modifier scope, and the
    restitutive/repetitive *again* ambiguity
    ([beavers-koontz-garboden-2020], [merchant-2013]). -/
inductive Root.Position where
  | complement
  | adjoined
  deriving DecidableEq, Repr

end Verb
