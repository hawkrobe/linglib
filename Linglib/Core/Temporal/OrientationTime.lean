/-!
# Orientation Times: the universal role vocabulary for tense
@cite{klein-1994} @cite{kiparsky-2002} @cite{reichenbach-1947} @cite{declerck-2006}

The contemporary linguistic literature on tense has largely converged on a
four-element role vocabulary for the times that tense and aspect manipulate:

- **Utterance time** (`utterance`): when the utterance is made. Klein's TU,
  Reichenbach's S, Declerck's t₀.
- **Topic time** (`topic`): the time about which a claim is made. Klein's TT,
  Reichenbach's R. Sometimes called "reference time" in older Reichenbachian
  usage; "topic time" is now standard.
- **Situation time** (`situation`): when the described situation actually
  obtains. Klein's TSit, Reichenbach's E, Declerck's TS, Kratzer's "running
  time of the event" τ(e).
- **Perspective time** (`perspective`): the time tense locates the topic
  against. Kiparsky's P (= utterance in root clauses, but shifts under
  free indirect discourse, attitude embedding, narrative mode).
  Declerck's TO₁ (the binding TO of the domain) plays the same architectural
  role, even though Declerck does not use the "perspective" label.

The fifth case `sub (n : Nat)` covers framework-specific intermediate TOs:
Declerck's TO₂, TO₃, etc. in chained tenses (past perfect, conditional perfect).
The natural-number index counts outward from the perspective TO: Declerck's
TO₂ is `sub 0`, TO₃ is `sub 1`. This keeps the universal vocabulary closed
while admitting arbitrarily-long chains.

`OrientationTime` is the canonical `Role` type used by `Domain`, `TenseSystem`,
and `AspectSystem` in the rest of the temporal substrate. Framework-specific
role mappings (Reichenbach → {utterance, topic, situation, perspective};
Declerck → {utterance, situation, perspective, sub n}) live with the
respective framework files.
-/

namespace Core.Time

/-- The universal vocabulary of orientation times in modern tense theory.
    See the module docstring for the framework-mapping and citations. -/
inductive OrientationTime where
  /-- Utterance time (TU / S / t₀). When the utterance is made. -/
  | utterance
  /-- Topic time (TT / R). The time about which a claim is made. -/
  | topic
  /-- Situation time (TSit / E / TS / τ(e)). When the situation obtains. -/
  | situation
  /-- Perspective time (P). What tense locates topic time against — equal
      to the utterance time in root clauses, shifted in FID and embedded
      contexts. Also covers Declerck's TO₁ (the binding TO of a domain). -/
  | perspective
  /-- An intermediate TO in a chain. `sub 0` = Declerck's TO₂, `sub 1` = TO₃,
      and so on; the index counts outward from `perspective`. -/
  | sub (n : Nat)
  deriving DecidableEq, Repr, Inhabited

end Core.Time
