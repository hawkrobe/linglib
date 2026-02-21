/-
# Verb Position Phenomena

Theory-neutral empirical data on verb position alternations.

## References

- Harizanov, B. "Syntactic Head Movement: Elements in Generative Syntax"
- Lambova (2004c:274, (15)): Bulgarian participle fronting
- Vikner (1995:32, (11d)): German V2
-/

import Linglib.Core.Word

namespace Phenomena.WordOrderAlternations.VerbPosition

-- Bulgarian Participle Fronting (Lambova 2004c, Harizanov 2019)

/-!
## Bulgarian: Participle Fronting

From Lambova (2004c:274, (15)), cited in Harizanov (2019) examples (29), (48), (52).

Both word orders are grammatical with the same meaning:

**Order A (participle before auxiliary):**
    Pročeli   bjaha      studentite     statijata.
    read      be.3p.pst  the.students   the.article
    'The students had read the article.'

**Order B (auxiliary before participle):**
    Studentite     bjaha      pročeli   statijata.
    the.students   be.3p.pst  read      the.article
    'The students had read the article.'
-/

/-- Bulgarian participle fronting alternation -/
structure BulgarianParticipleData where
  /-- Surface form with participle fronted -/
  fronted : String := "Pročeli bjaha studentite statijata"
  /-- Surface form without fronting -/
  unfronted : String := "Studentite bjaha pročeli statijata"
  /-- Both orders are grammatical -/
  bothGrammatical : Bool := true
  /-- Same meaning for both orders -/
  sameMeaning : Bool := true
  /-- Gloss -/
  gloss : String := "read be.3p.pst the.students the.article"
  /-- Translation -/
  translation : String := "The students had read the article."

def bulgarianExample : BulgarianParticipleData := {}

-- Germanic V2 (Vikner 1995, Harizanov 2019)

/-!
## German: V2 Word Order

From Vikner (1995:32, (11d)), cited in Harizanov (2019) example (35).

The finite verb appears in different positions depending on clause type:

**Root clause (verb second):**
    Diesen Film haben die Kinder gesehen.
    this   film have  the children seen
    'The children have seen this film.'

**Embedded clause (verb final):**
    ... dass die Kinder diesen Film gesehen haben.
    ... that the children this film seen have
    '... that the children have seen this film.'
-/

/-- German V2 alternation data -/
structure GermanV2Data where
  /-- Root clause with V2 order -/
  rootClause : String := "Diesen Film haben die Kinder gesehen"
  /-- Embedded clause with verb-final order -/
  embeddedClause : String := "dass die Kinder diesen Film gesehen haben"
  /-- Root clause gloss -/
  rootGloss : String := "this film have the children seen"
  /-- Embedded clause gloss -/
  embeddedGloss : String := "that the children this film seen have"
  /-- Translation -/
  translation : String := "The children have seen this film."
  /-- V2 required in root clauses -/
  v2InRoot : Bool := true
  /-- Verb-final in embedded clauses with overt complementizer -/
  verbFinalInEmbedded : Bool := true

def germanExample : GermanV2Data := {}

end Phenomena.WordOrderAlternations.VerbPosition
