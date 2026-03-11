import Linglib.Core.Case.Basic

/-!
# Swiss German Case and Verb Subcategorization @cite{shieber-1985}

Swiss German uses the same four-case inventory as Standard German (NOM, ACC,
GEN, DAT). The critical fact for @cite{shieber-1985}'s argument is that
different verbs in cross-serial constructions subcategorize for different
cases on their NP objects:

- *hälfe* ("help") requires **dative**
- *lönd* ("let") requires **accusative**
- *aastriiche* ("paint") requires **accusative**

This case-verb pairing is what makes Swiss German cross-serial dependencies
produce the pattern a^m b^n c^m d^n (DAT-NPs, ACC-NPs, DAT-Vs, ACC-Vs),
which is not context-free.
-/

namespace Fragments.SwissGerman.Case

/-- Swiss German uses the same 4-case inventory as Standard German. -/
def caseInventory : List Core.Case := [.nom, .acc, .gen, .dat]

/-- Verbs that participate in cross-serial subordinate clause constructions.

    These are the verbs from @cite{shieber-1985}'s Swiss German data. Each
    subcategorizes for a specific case on its NP object. -/
inductive CrossSerialVerb where
  /-- *hälfe* "help" — requires dative NP object -/
  | haelfe
  /-- *lönd* "let" — requires accusative NP object -/
  | loend
  /-- *aastriiche* "paint" — requires accusative NP object -/
  | aastriiche
  deriving DecidableEq, BEq, Repr

/-- Case required by each verb on its NP object.

    This is the empirical fact that drives @cite{shieber-1985}'s proof:
    verbs sort into dative-subcategorizing and accusative-subcategorizing
    classes, and in the cross-serial construction the case on each NP must
    match the requirement of its corresponding verb. -/
def verbObjectCase : CrossSerialVerb → Core.Case
  | .haelfe     => .dat
  | .loend      => .acc
  | .aastriiche => .acc

/-- The two case classes are genuinely distinct — *hälfe* requires dative
    while *lönd* requires accusative. This non-trivial case distinction is
    what produces the crossed agreement pattern a^m b^n c^m d^n. -/
theorem dat_acc_distinction :
    verbObjectCase .haelfe ≠ verbObjectCase .loend := by decide

/-- *lönd* and *aastriiche* belong to the same case class (accusative). -/
theorem loend_aastriiche_same_class :
    verbObjectCase .loend = verbObjectCase .aastriiche := by decide

end Fragments.SwissGerman.Case
