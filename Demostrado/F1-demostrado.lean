/-
  ═══════════════════════════════════════════════════════════
  Taller Lean 4 — GRUPO B
  Campeonato de F1 (Reglamento FIA 2025)
  VERSIÓN DEMOSTRADA (referencia para el presentador)
  ═══════════════════════════════════════════════════════════

  Nota: las propiedades 1 (verde) están verificadas.
  Las propiedades 2, 3 y 4 son esqueletos plausibles —
  algunos lemmas concretos pueden requerir ajuste según
  Mathlib v4.24.0. Si una falla, marcala con sorry y seguí.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic

open Finset

/- ─────────────────────────────────────────────────────────
   PARTE 1 — TABLA DE PUNTOS (REGLAMENTO 2025)
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

def Piloto.conteo (p : Piloto) (k : ℕ) : ℕ :=
  p.posiciones.countP (· = k)

def puntosCarrera (resultado : List String) : ℕ :=
  (List.range resultado.length).foldl (fun acc i => acc + puntajePos (i + 1)) 0

def claveDesempate (p : Piloto) : ℕ × List ℕ :=
  (p.puntos, (List.range 10).map (fun k => p.conteo (k + 1)))

def lexListNatLt : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ => false
  | _, [] => true
  | a :: as, b :: bs =>
    if a < b then true
    else if b < a then false
    else lexListNatLt as bs

def claveMenor (a b : ℕ × List ℕ) : Bool :=
  if a.1 < b.1 then true
  else if b.1 < a.1 then false
  else lexListNatLt a.2 b.2

noncomputable def lider (c : Campeonato) : Option String :=
  if c.pilotos = ∅ then none
  else
    let pilotosList := c.pilotos.toList
    pilotosList.head?.map (fun primero =>
      pilotosList.foldl (fun mejor p =>
        if claveMenor (claveDesempate (c.estado mejor))
            (claveDesempate (c.estado p))
        then p else mejor) primero)

/- ═══════════════════════════════════════════════════════════
   LAS CUATRO PROPIEDADES — DEMOSTRACIONES
   ═══════════════════════════════════════════════════════════ -/

/- ─────────────────────────────────────────────────────────
   PROPIEDAD 1 — Puntos no negativos.   [Fácil — VERIFICADA]

   Gratis porque usamos ℕ, que nunca es negativo.
   ───────────────────────────────────────────────────────── -/

theorem puntos_no_negativos
    (c : Campeonato)
    (p : String) :
    (c.estado p).puntos ≥ 0 := by
  exact Nat.zero_le _

/- ─────────────────────────────────────────────────────────
   PROPIEDAD 2 — Cota de puntos por carrera.   [Media — esqueleto]

   Una carrera distribuye como máximo 101 puntos.
   ───────────────────────────────────────────────────────── -/

/-- Lema auxiliar: la suma parcial de puntajes hasta el índice n
    está acotada por la suma total de los 10 primeros. -/
theorem max_puntos_carrera (resultado : List String) :
    puntosCarrera resultado ≤ 101 := by
  unfold puntosCarrera
  -- Estrategia: como puntajePos k = 0 para k > 10,
  -- el fold solo acumula valores no nulos para las primeras 10 posiciones.
  -- La suma de las primeras 10: 25+18+15+12+10+8+6+4+2+1 = 101.
  --
  -- Inducción sobre la longitud de la lista resultado.
  -- Caso base: lista vacía → 0 ≤ 101.
  -- Caso inductivo: agregar un elemento agrega puntajePos (n+1).
  --   Si n+1 ≤ 10, el total acumulado se mantiene ≤ 101 porque
  --   los puntajes son decrecientes.
  --   Si n+1 > 10, puntajePos (n+1) = 0, total no cambia.
  --
  -- ATENCIÓN: la prueba formal de esto requiere lemmas sobre foldl
  -- que pueden ser técnicos. Estrategia más directa:
  -- usar `interval_cases` sobre resultado.length o un lema sobre
  -- la suma de los primeros n términos de puntajePos.
  sorry

/- ─────────────────────────────────────────────────────────
   PROPIEDAD 3 — Validez del líder.   [Media — esqueleto]

   Si declaramos un líder, ningún otro piloto tiene
   estrictamente más puntos.
   ───────────────────────────────────────────────────────── -/

theorem lider_tiene_max_puntos
    (c : Campeonato)
    (l : String)
    (h : lider c = some l) :
    ∀ p ∈ c.pilotos, (c.estado p).puntos ≤ (c.estado l).puntos := by
  intro p hp
  unfold lider at h
  split_ifs at h with hvac
  · -- Caso 1: pilotos = ∅, no puede haber p ∈ pilotos
    rw [hvac] at hp
    simp at hp
  · -- Caso 2: pilotos no vacío, l surge del fold con claveMenor
    -- Invariante del fold: en cada paso, mejor es ≥ todos los pilotos vistos.
    -- Al final del fold, l ≥ todos los pilotos.
    --
    -- Propiedad: si claveMenor (clave p) (clave l) ⇒ p.puntos ≤ l.puntos.
    -- Esto es porque claveMenor compara primero por puntos.
    --
    -- ATENCIÓN: razonar sobre fold con claveMenor es técnico.
    -- Lemma útil: List.foldl_eq_of_comm, o por inducción sobre la lista.
    sorry

/- ─────────────────────────────────────────────────────────
   PROPIEDAD 4 — Countback por victorias.   [Difícil — esqueleto]

   Si dos pilotos tienen los mismos puntos pero uno tiene
   MÁS victorias, el de menos victorias NO es líder.
   ───────────────────────────────────────────────────────── -/

theorem countback_victorias
    (c : Campeonato)
    (a b : String)
    (ha : a ∈ c.pilotos)
    (hb : b ∈ c.pilotos)
    (h_puntos : (c.estado a).puntos = (c.estado b).puntos)
    (h_victorias : (c.estado a).conteo 1 > (c.estado b).conteo 1) :
    lider c ≠ some b := by
  intro hlider
  -- Por contradicción: si b fuera líder, entonces para todo p,
  -- claveMenor (clave p) (clave b) ∨ clave p = clave b.
  -- En particular para a: claveMenor (clave a) (clave b).
  --
  -- claveMenor compara: primero puntos, después conteo[1].
  -- Por h_puntos las primeras componentes son iguales,
  -- así el desempate va a la lista de conteos.
  -- conteo a 1 > conteo b 1 implica que clave a > clave b en lexicográfico,
  -- contradiciendo claveMenor (clave a) (clave b).
  --
  -- ATENCIÓN: esta es la propiedad más técnica. Requiere:
  -- 1) probar la propiedad invariante del fold (que es similar a Prop 3)
  -- 2) razonar sobre el orden lexicográfico de lexListNatLt
  --
  -- Sugerencia: empezar por el caso particular de claveMenor cuando
  -- los puntos son iguales, mostrando que se reduce a lexListNatLt
  -- sobre las listas de conteos.
  sorry

/- ═══════════════════════════════════════════════════════════
   PRUEBA RÁPIDA
   ═══════════════════════════════════════════════════════════ -/

example : 2 + 2 = 4 := rfl

example : puntajePos 1 = 25 := rfl
example : puntajePos 10 = 1 := rfl
example : puntajePos 11 = 0 := rfl

#check puntajePos
#check lider
