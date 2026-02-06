import Linglib.Theories.HPSG.Basic

/-!
# Head-Filler Schema and SLASH Feature

HPSG's third combination schema: the Head-Filler Schema handles long-distance
dependencies (extraction, wh-movement). A filler XP combines with a sentence
containing a gap (SLASH feature) of matching category.

Together with Head-Complement and Head-Subject (in Basic.lean), this completes
HPSG's three immediate dominance schemata.

## Key types

- `SlashValue` — the set of categories expected to fill gaps
- `SynsemSlash` — extends `Synsem` with SLASH
- `HeadFillerRule` — filler combines with `S[SLASH {XP}]`, discharging the gap
- `HPSGSchema` — unifies all three schemata

## Connection to Müller (2013)

Müller §2.3: "the formalization of internal Merge and that of the head-filler
schema are very similar" — both handle displacement by pairing a moved element
with its extraction site.

## References

- Pollard, C. & Sag, I. (1994). Head-Driven Phrase Structure Grammar. Ch. 9.
- Ginzburg, J. & Sag, I. (2000). Interrogative Investigations. §2.3.
- Müller, S. (2013). Unifying Everything. Language 89(4):920–950.
-/

namespace HPSG

/-! ## SLASH features -/

/-- The SLASH value: a set of categories for which gaps exist.

In HPSG, SLASH is a set-valued feature on phrases. A phrase with
`SLASH {NP}` contains an NP gap somewhere inside it. The Head-Filler
schema discharges one element from this set. -/
structure SlashValue where
  /-- Categories of gaps in this phrase -/
  gaps : List Cat
  deriving Repr, DecidableEq

/-- Empty SLASH value (no gaps). -/
def SlashValue.empty : SlashValue := ⟨[]⟩

/-- Check if SLASH contains a specific category. -/
def SlashValue.contains (sv : SlashValue) (c : Cat) : Bool :=
  sv.gaps.contains c

/-- Remove a category from SLASH (when a gap is filled). -/
def SlashValue.discharge (sv : SlashValue) (c : Cat) : SlashValue :=
  ⟨sv.gaps.erase c⟩

instance : BEq SlashValue where
  beq a b := a.gaps == b.gaps

/-! ## Extended SYNSEM with SLASH -/

/-- Extended SYNSEM value including the SLASH feature.

This extends the basic `Synsem` from HPSG.Basic with nonlocal features. -/
structure SynsemSlash where
  /-- Local syntax-semantics features -/
  local_ : Synsem
  /-- Nonlocal SLASH feature (gap set) -/
  slash : SlashValue := .empty
  deriving Repr

/-- Get the category from an extended synsem. -/
def SynsemSlash.cat (ss : SynsemSlash) : Cat := ss.local_.cat

/-! ## Head-Filler Schema -/

/-- Head-Filler Schema: filler XP combines with a clause containing a gap.

Schema 3 (Pollard & Sag 1994, Ch. 9):
```
       S
      / \
   XP    S[SLASH {XP}]
(filler)  (head)
```

The filler's category must match one of the gaps in the head's SLASH set.
The result has that gap discharged from SLASH. -/
structure HeadFillerRule where
  /-- The filler phrase (the extracted constituent) -/
  filler : Sign
  /-- The head phrase (sentence with a gap) -/
  headPhrase : Sign
  /-- The SLASH value on the head phrase before combination -/
  headSlash : SlashValue
  /-- The result phrase -/
  result : Sign
  /-- The filler's category matches a gap in the head -/
  slashMatch : headSlash.contains (filler.synsem.cat) = true
  /-- The result has the gap discharged -/
  resultSlash : SlashValue := headSlash.discharge (filler.synsem.cat)

/-! ## Unified schema type -/

/-- All three HPSG immediate dominance schemata, unified.

This inductive covers the complete set of phrase structure schemata
needed for HPSG phrase building. Müller (2013) argues these three
correspond to the three universal combination modes. -/
inductive HPSGSchema where
  /-- Head-Complement: head combines with complements (Schema 1) -/
  | headComp : HeadCompRule → HPSGSchema
  /-- Head-Subject: subject combines with head phrase (Schema 2) -/
  | headSubj : HeadSubjRule → HPSGSchema
  /-- Head-Filler: filler combines with gapped clause (Schema 3) -/
  | headFiller : HeadFillerRule → HPSGSchema

/-- Get the result sign from any schema application. -/
def HPSGSchema.result : HPSGSchema → Sign
  | .headComp r => r.result
  | .headSubj r => r.result
  | .headFiller r => r.result

/-- Get the head sign from any schema application. -/
def HPSGSchema.head : HPSGSchema → Sign
  | .headComp r => r.head
  | .headSubj r => r.headPhrase
  | .headFiller r => r.headPhrase

/-! ## Key properties -/

/-- The head's category propagates to the result (Head Feature Principle).

In all three schemata, the category of the result phrase equals the
category of the head daughter. This is the HPSG analogue of the
Minimalist labeling algorithm. -/
theorem head_determines_cat_headComp (r : HeadCompRule) :
    r.result.synsem.cat = r.head.synsem.cat :=
  r.hfp

/-- When constructing a HeadFillerRule with the default resultSlash,
the gap matching the filler is discharged. -/
theorem slash_discharged_default (filler headPhrase result : Sign) (headSlash : SlashValue)
    (slashMatch : headSlash.contains (filler.synsem.cat) = true) :
    ({ filler, headPhrase, headSlash, result, slashMatch : HeadFillerRule}).resultSlash
      = headSlash.discharge (filler.synsem.cat) := rfl

end HPSG
