import Linglib.Syntax.Category.Particle.Basic

/-!
# Czech Particles
[stankova-2025] [stankova-2026] [simik-2024] [nekula-1996]

Czech discourse particles of polar questions as `Particle` values.
The negation-position diagnostics and Table 1 licensing live in
`Stankova2026`; the bias experiments in `StankovaSimik2025`.
-/

namespace Czech.Particles

/-- *náhodou* 'by (any) chance' — in its particle use restricted to
negative polar questions ([stankova-2026] §2.2.1; the adverbial reading
'accidentally' is a separate item, her fn. 3). Diagnoses outer negation
(`Stankova2026`); FALSUM experiments in `StankovaSimik2025`. -/
def nahodou : Particle where
  form := "náhodou"
  distribution := some
    { declarative := some .excluded
      polarInterrogative := some .optional }

/-- *ještě* 'yet, still' — aspectual particle of declaratives and polar
questions ([stankova-2026] (13)-(14)); inner-negation diagnostic in
`Stankova2026`. -/
def jeste : Particle where
  form := "ještě"
  distribution := some
    { declarative := some .optional
      polarInterrogative := some .optional }

/-- *fakt* 'really' — emphatic particle of declaratives and polar
questions ([stankova-2026] (15)); inner/medial-negation diagnostic in
`Stankova2026`. -/
def fakt : Particle where
  form := "fakt"
  distribution := some
    { declarative := some .optional
      polarInterrogative := some .optional }

/-- *vůbec* 'at all' — NPI particle of assertions and polar questions
([stankova-2026] (9)); parallels English *at all*. -/
def vubec : Particle where
  form := "vůbec"
  distribution := some
    { declarative := some .optional
      polarInterrogative := some .optional }

/-- *snad* 'perhaps, surely not' — adversative/mirative PQ particle of
the cross-Slavic RAZVE family ([simik-2024] §4.2.4, [nekula-1996],
[stankova-2023]). -/
def snad : Particle where
  form := "snad"
  distribution := some { polarInterrogative := some .optional }

/-- *copak* 'what then' — RAZVE-family particle of positive and
negative polar questions ([stankova-2025] exs. 19a-b, [nekula-1996]);
evidential-bias experiments in `StankovaSimik2025`. -/
def copak : Particle where
  form := "copak"
  distribution := some { polarInterrogative := some .optional }

/-- All Czech PQ particles indexed in this file. -/
def allParticles : List Particle :=
  [nahodou, jeste, fakt, vubec, snad, copak]

end Czech.Particles
