module

public import Linglib.Syntax.Category.Particle.Basic

/-!
# Czech particles

This file gives the Czech discourse particles of polar questions as `Particle` values: *náhodou*,
*ještě*, *fakt* and *vůbec*, which [stankova-2026] uses to diagnose the position of negation, and
the question particles *snad* and *copak* ([nekula-1996], [simik-2024]). The diagnostics are in
`Studies/Stankova2026.lean` and the bias experiments in `Studies/StankovaSimik2025.lean`.

## References

* [stankova-2025]
* [stankova-2026]
* [simik-2024]
* [nekula-1996]
-/

@[expose] public section

namespace Czech.Particles

/-- *náhodou* 'by (any) chance' — in its particle use restricted to
negative polar questions ([stankova-2026] §2.2.1; the adverbial reading
'accidentally' is a separate item, her fn. 3). Diagnoses outer negation
(`Stankova2026`); FALSUM experiments in `StankovaSimik2025`. -/
def nahodou : Particle where
  form := "náhodou"
  distribution := fun c e => match c, e with
    | .declarative, .matrix => some .excluded
    | .polar, .matrix => some .optional
    | _, _ => none

/-- *ještě* 'yet, still' — aspectual particle of declaratives and polar
questions ([stankova-2026] (13)-(14)); inner-negation diagnostic in
`Stankova2026`. -/
def jeste : Particle where
  form := "ještě"
  distribution := fun c e => match c, e with
    | .declarative, .matrix => some .optional
    | .polar, .matrix => some .optional
    | _, _ => none

/-- *fakt* 'really' — emphatic particle of declaratives and polar
questions ([stankova-2026] (15)); inner/medial-negation diagnostic in
`Stankova2026`. -/
def fakt : Particle where
  form := "fakt"
  distribution := fun c e => match c, e with
    | .declarative, .matrix => some .optional
    | .polar, .matrix => some .optional
    | _, _ => none

/-- *vůbec* 'at all' — NPI particle of assertions and polar questions
([stankova-2026] (9)); parallels English *at all*. -/
def vubec : Particle where
  form := "vůbec"
  distribution := fun c e => match c, e with
    | .declarative, .matrix => some .optional
    | .polar, .matrix => some .optional
    | _, _ => none

/-- *snad* 'perhaps, surely not' — adversative/mirative PQ particle
([nekula-1996], [stankova-2023]); optionally supports rhetorical
readings of polar questions ([simik-2024] ex. 8). -/
def snad : Particle where
  form := "snad"
  distribution := fun c e => match c, e with
    | .polar, .matrix => some .optional
    | _, _ => none

/-- *copak* 'what then' — RAZVE-family particle ([simik-2024] §4.2.4) of positive and
negative polar questions ([stankova-2025] exs. 19a-b, [nekula-1996]);
evidential-bias experiments in `StankovaSimik2025`. -/
def copak : Particle where
  form := "copak"
  distribution := fun c e => match c, e with
    | .polar, .matrix => some .optional
    | _, _ => none

end Czech.Particles
