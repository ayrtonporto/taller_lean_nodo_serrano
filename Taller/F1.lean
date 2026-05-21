/-
  ═══════════════════════════════════════════════════════════
  Taller Lean 4 — GRUPO B
  Campeonato de F1 (Reglamento FIA 2025)
  ═══════════════════════════════════════════════════════════

  El objetivo: formalizar el sistema de puntos de F1
  y demostrar 4 propiedades fundamentales.

  Reemplacen `sorry` por la demostración.
  Si compila → Goals accomplished.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

/- ─────────────────────────────────────────────────────────
   PARTE 1 — TABLA DE PUNTOS (REGLAMENTO 2025)

   En Python:
     PUNTOS = {1:25, 2:18, 3:15, 4:12, 5:10,
               6:8, 7:6, 8:4, 9:2, 10:1}

   Sin punto por vuelta rápida (eliminado en 2025).
   ───────────────────────────────────────────────────────── -/

def puntajePos : ℕ → ℕ
  | 1  => 25
  | 2  => 18
  | 3  => 15
  | 4  => 12
  | 5  => 10
  | 6  => 8
  | 7  => 6
  | 8  => 4
  | 9  => 2
  | 10 => 1
  | _  => 0

/- ─────────────────────────────────────────────────────────
   PARTE 2 — EL PILOTO Y EL CAMPEONATO

   En Python:
     @dataclass
     class Piloto:
       puntos: int = 0
       posiciones: list[int] = []   # historial

     @dataclass
     class Campeonato:
       pilotos: dict[str, Piloto]
   ───────────────────────────────────────────────────────── -/

structure Piloto where
  puntos     : ℕ
  posiciones : List ℕ
  deriving Repr

structure Campeonato where
  pilotos : Finset String
  estado  : String → Piloto

/- ─────────────────────────────────────────────────────────
   PARTE 3 — FUNCIONES AUXILIARES
   ───────────────────────────────────────────────────────── -/

/-- Cuenta cuántas veces el piloto terminó en la posición k. -/
def Piloto.conteo (p : Piloto) (k : ℕ) : ℕ :=
  p.posiciones.countP (· = k)

/-- Suma total de puntos distribuidos en una carrera.
    Útil para la propiedad 2. -/
def puntosCarrera (resultado : List String) : ℕ :=
  (List.range resultado.length).foldl (fun acc i => acc + puntajePos (i + 1)) 0

/-- Comparación lexicográfica para countback:
    primero por puntos, después por victorias, después por 2°, etc. -/
def claveDesempate (p : Piloto) : ℕ × List ℕ :=
  (p.puntos, (List.range 10).map (fun k => p.conteo (k + 1)))

/-- Líder del campeonato según puntos + countback. -/
def lider (c : Campeonato) : Option String :=
  if c.pilotos = ∅ then none
  else
    let pilotosList := c.pilotos.toList
    -- Tomamos el máximo según la clave lexicográfica
    pilotosList.head?.map (fun primero =>
      pilotosList.foldl (fun mejor p =>
        if claveDesempate (c.estado p) > claveDesempate (c.estado mejor)
        then p else mejor) primero)

/- ═══════════════════════════════════════════════════════════
   LAS CUATRO PROPIEDADES A DEMOSTRAR
   ═══════════════════════════════════════════════════════════ -/

/- ─────────────────────────────────────────────────────────
   PROPIEDAD 1 — Puntos no negativos.   [Fácil — gratis]

   Los puntos siempre son ≥ 0.
   Es trivial: usamos ℕ, que por definición es no negativo.
   El compilador lo garantiza por el sistema de tipos.

   Pista: `Nat.zero_le` cierra esto en una línea.
   ───────────────────────────────────────────────────────── -/

theorem puntos_no_negativos
    (c : Campeonato)
    (p : String) :
    (c.estado p).puntos ≥ 0 := by
  sorry

/- ─────────────────────────────────────────────────────────
   PROPIEDAD 2 — Cota de puntos por carrera.   [Fácil]

   Una carrera distribuye como máximo 101 puntos
   (25+18+15+12+10+8+6+4+2+1 = 101).

   Pista: por inducción sobre la longitud del resultado,
   o por cálculo directo si la lista tiene ≤ 10 elementos.
   `decide` o `omega` pueden ayudar para casos finitos.
   ───────────────────────────────────────────────────────── -/

theorem max_puntos_carrera (resultado : List String) :
    puntosCarrera resultado ≤ 101 := by
  sorry

/- ─────────────────────────────────────────────────────────
   PROPIEDAD 3 — Validez del líder.   [Media]

   Si declaramos un líder, ningún otro piloto tiene
   estrictamente más puntos.

   Pista: usar la definición de `lider` y propiedades
   del fold con la comparación lexicográfica.
   ───────────────────────────────────────────────────────── -/

theorem lider_tiene_max_puntos
    (c : Campeonato)
    (l : String)
    (h : lider c = some l) :
    ∀ p ∈ c.pilotos, (c.estado p).puntos ≤ (c.estado l).puntos := by
  sorry

/- ─────────────────────────────────────────────────────────
   PROPIEDAD 4 — Countback por victorias.   [Difícil]

   Si dos pilotos tienen los mismos puntos, pero uno
   tiene MÁS victorias que el otro, entonces el que
   tiene menos victorias NO puede ser líder.

   Esta es la regla central del desempate de la FIA.

   Pista: usar la definición de `claveDesempate` y
   las propiedades del orden lexicográfico sobre pares.
   ───────────────────────────────────────────────────────── -/

theorem countback_victorias
    (c : Campeonato)
    (a b : String)
    (ha : a ∈ c.pilotos)
    (hb : b ∈ c.pilotos)
    (h_puntos : (c.estado a).puntos = (c.estado b).puntos)
    (h_victorias : (c.estado a).conteo 1 > (c.estado b).conteo 1) :
    lider c ≠ some b := by
  sorry

/- ═══════════════════════════════════════════════════════════
   PRUEBA RÁPIDA - PARA VER QUE EL ENTORNO FUNCIONA
   ═══════════════════════════════════════════════════════════ -/

example : 2 + 2 = 4 := rfl

-- Verificá que la tabla de puntos compila bien:
example : puntajePos 1 = 25 := rfl
example : puntajePos 10 = 1 := rfl
example : puntajePos 11 = 0 := rfl

#check puntajePos
#check lider
