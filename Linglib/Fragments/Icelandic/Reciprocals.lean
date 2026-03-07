import Linglib.Core.Lexical.Pronouns

/-!
# Icelandic Reciprocal Fragment
@cite{nordlinger-2023}

Icelandic uses a bipartite NP strategy: "hvor...annad" ('each...other'),
where each part independently inflects for case. The first element "hvor"
takes nominative (subject case), while "annad" takes the case assigned by
the verb.

This is a bivalent strategy: the bipartite NP fills the object position,
preserving transitivity. Formally distinct from the reflexive "sig".

@cite{nordlinger-2023} ex. 17 (citing Hurst & Nordlinger 2021).
-/

namespace Fragments.Icelandic.Reciprocals

open Core.Pronouns

/-- hvor...annad — bipartite reciprocal NP 'each other'.

    Each part inflects independently for case.  -/
def hvorAnnad : PronounEntry :=
  { form := "hvor...annad", person := some .third, number := some .pl }

/-- sig — reflexive pronoun (for contrast). -/
def sig : PronounEntry :=
  { form := "sig", person := some .third }

/-- Icelandic reciprocal is formally distinct from reflexive. -/
theorem recip_distinct_from_reflexive :
    hvorAnnad.form ≠ sig.form := by decide

end Fragments.Icelandic.Reciprocals
