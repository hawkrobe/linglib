import Linglib.Theories.Semantics.Tense.TemporalConnectives.Basic
import Linglib.Theories.Semantics.Tense.TemporalConnectives.Anscombe
import Linglib.Theories.Semantics.Tense.TemporalConnectives.Rett
import Linglib.Theories.Semantics.Tense.TemporalConnectives.EventBridge
import Linglib.Theories.Semantics.Tense.TemporalConnectives.OST
import Linglib.Theories.Semantics.Tense.TemporalConnectives.BeaverCondoravdi

/-!
# Temporal Connective Semantics: *before* and *after*

Hub module re-exporting all temporal connective theories. Four semantic
analyses operate at four distinct levels of abstraction:

```
Level 4: World–Time pairs + branching    (Beaver & Condoravdi 2003)
Level 3: Event predicates + τ-image      (Ogihara & Steinert-Threlkeld 2024)
Level 2: Interval sets + MAX on scales   (Rett 2020)
Level 1: Point sets + ∀/∃               (Anscombe 1964)
```

The projection chain connects them:

```
EvPred Time  →[eventDenotation]→  SentDenotation Time  →[timeTrace]→  Set Time
  (Level 3)                          (Level 2)                        (Level 1)
```

Level 4 (B&C) is orthogonal: it adds a modal dimension (historical alternatives)
that the extensional levels lack. The `earliest` operator it uses is the same
as Rett's MAX₍<₎.

## Submodules

- `Basic.lean`: Shared infrastructure (SentDenotation, timeTrace, denotation patterns)
- `Anscombe.lean`: Point-level under-specification semantics
- `Rett.lean`: Interval-level antonymy + aspectual coercion + ambidirectionality
- `EventBridge.lean`: The eventDenotation projection (Level 3 → Level 2)
- `OST.lean`: Event-level quantificational asymmetry + veridicality
- `BeaverCondoravdi.lean`: Intensional uniform analysis with `earliest`

## References

- Anscombe, E. (1964). Before and after. *The Philosophical Review* 73, 3–24.
- Rett, J. (2020). Eliminating EARLIEST. *Sinn und Bedeutung* 24, 201–218.
- Ogihara, T. & Steinert-Threlkeld, S. (2024). An interval-based semantics
  for *before* and *after*.
- Beaver, D. & Condoravdi, C. (2003). A uniform analysis of *before* and *after*.
  *Proceedings of SALT* 13, 37–54.
- Krifka, M. (2010). *Before* and *after* without coercion. *NLLT* 28, 911–929.
-/
