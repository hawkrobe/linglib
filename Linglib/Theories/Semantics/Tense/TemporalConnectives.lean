import Linglib.Theories.Semantics.Tense.TemporalConnectives.Basic
import Linglib.Theories.Semantics.Tense.TemporalConnectives.Anscombe
import Linglib.Theories.Semantics.Tense.TemporalConnectives.Karttunen
import Linglib.Theories.Semantics.Tense.TemporalConnectives.Rett
import Linglib.Theories.Semantics.Tense.TemporalConnectives.EventBridge
import Linglib.Theories.Semantics.Tense.TemporalConnectives.OST
import Linglib.Theories.Semantics.Tense.TemporalConnectives.BeaverCondoravdi

/-!
# Temporal Connective Semantics
@cite{anscombe-1964} @cite{beaver-condoravdi-2003} @cite{karttunen-1974} @cite{krifka-2010b} @cite{ogihara-steinert-threlkeld-2024} @cite{rett-2020}

Hub module re-exporting all temporal connective theories. Five semantic
analyses operate at four distinct levels of abstraction:

```
Level 4: World–Time pairs + branching    (Beaver & Condoravdi 2003)
Level 3: Event predicates + τ-image      (Ogihara & Steinert-Threlkeld 2024)
Level 2: Interval sets + MAX on scales   (Rett 2020)
Level 1: Point sets + ∀/∃               (Anscombe 1964; Karttunen 1974)
```

The projection chain connects them:

```
EvPred Time  →[eventDenotation]→  SentDenotation Time  →[timeTrace]→  Set Time
  (Level 3)                          (Level 2)                        (Level 1)
```

Level 4 (B&C) is orthogonal: it adds a modal dimension (historical alternatives)
that the extensional levels lack. The `earliest` operator it uses is the same
as Rett's MAX₍<₎.

At Level 1, the eight English temporal connectives reduce to four primitives
plus two ≤-ordering variants:
*before* (∃∀ strict), *after* (∃∃ strict), *when* (∃ overlap),
*while* (∀ containment). *Until* is derived: durative ≡ *when*,
punctual ≡ ¬*before* (Karttunen 1974). *Till* ≡ durative *until*.
*Since* (∃∈B ∀∈A ≤) and *by* (∃∈A ∀∈B ≤) are the non-strict
counterparts of the Anscombe connectives (Heinämäki 1974).

## Submodules

- `Basic.lean`: Shared infrastructure (SentDenotation, timeTrace, denotation patterns)
- `Anscombe.lean`: Point-level under-specification semantics (*before*, *after*)
- `Karttunen.lean`: *When*, *while*, *until*, *till*, *since*, *by* at Level 1; two-*until* hypothesis
- `Rett.lean`: Interval-level antonymy + aspectual coercion + ambidirectionality
- `EventBridge.lean`: The eventDenotation projection (Level 3 → Level 2)
- `OST.lean`: Event-level quantificational asymmetry + veridicality
- `BeaverCondoravdi.lean`: Intensional uniform analysis with `earliest`

-/
