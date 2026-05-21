/-
  ═══════════════════════════════════════════════════════════
  Taller Lean 4 — GRUPO A
  Sistema de Votación por Mayoría Simple
  VERSIÓN DEMOSTRADA (referencia para el presentador)
  ═══════════════════════════════════════════════════════════

  Nota: las propiedades 1 (verde) están verificadas conceptualmente.
  Las propiedades 2, 3 y 4 son esqueletos plausibles —
  algunos lemmas concretos pueden requerir ajuste según
  Mathlib v4.24.0. Si una falla, marcala con sorry y seguí.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic

open Finset

/- ─────────────────────────────────────────────────────────
   PARTE 1 — EL MODELO
   ───────────────────────────────────────────────────────── -/

structure VotadorState where
  candidatos : Finset String
  votos      : String → ℕ
  votantes   : Finset String

/- ─────────────────────────────────────────────────────────
   PARTE 2 — LA OPERACIÓN VOTAR
   ───────────────────────────────────────────────────────── -/

def votar
    (s : VotadorState)
    (votante candidato : String)
    (hv : votante ∉ s.votantes)
    (hc : candidato ∈ s.candidatos)
    : VotadorState :=
  { candidatos := s.candidatos
    votos      := fun c => if c = candidato then s.votos c + 1 else s.votos c
    votantes   := insert votante s.votantes
  }

/- ─────────────────────────────────────────────────────────
   PARTE 3 — EL GANADOR
   ───────────────────────────────────────────────────────── -/

noncomputable def ganador (s : VotadorState) : Option String :=
  if s.votantes = ∅ then none
  else
    let votosMax := s.candidatos.sup s.votos
    let top := s.candidatos.filter (fun c => s.votos c = votosMax)
    if h : top.card = 1 then
      some (top.toList.head (by
        have hlen : top.toList.length = 1 := by
          simpa [Finset.length_toList] using h
        intro hnil
        simpa [hnil] using hlen))
    else none

/- ═══════════════════════════════════════════════════════════
   LAS CUATRO PROPIEDADES — DEMOSTRACIONES
   ═══════════════════════════════════════════════════════════ -/

/- ─────────────────────────────────────────────────────────
   PROPIEDAD 1 — Un votante, un voto.   [Fácil — VERIFICADA]
   ───────────────────────────────────────────────────────── -/

theorem votar_registra
    (s : VotadorState)
    (v c : String)
    (hv : v ∉ s.votantes)
    (hc : c ∈ s.candidatos) :
    v ∈ (votar s v c hv hc).votantes := by
  dsimp [votar]
  exact Finset.mem_insert_self v s.votantes

/- ─────────────────────────────────────────────────────────
   PROPIEDAD 2 — Conservación de votos.   [Media — esqueleto]

   Idea: la nueva función de votos es if-then-else.
   Hay que separar la suma en el caso x = c y los demás.
   ───────────────────────────────────────────────────────── -/

theorem suma_votos_post_votar
    (s : VotadorState)
    (v c : String)
    (hv : v ∉ s.votantes)
    (hc : c ∈ s.candidatos) :
    (s.candidatos.sum (votar s v c hv hc).votos) =
    s.candidatos.sum s.votos + 1 := by
  dsimp [votar]
  -- La suma se separa: el caso x = c aporta s.votos c + 1,
  -- los demás x aportan s.votos x.
  -- Esto se traduce a: ∑ x, (if x=c then s.votos x + 1 else s.votos x)
  --                 = ∑ x, s.votos x + (if x=c then 1 else 0)
  --                 = ∑ x, s.votos x + (1 si c está, 0 si no)
  -- Como hc : c ∈ s.candidatos, la indicadora vale 1.
  conv_lhs =>
    ext x
    rw [show (if x = c then s.votos x + 1 else s.votos x)
          = s.votos x + (if x = c then 1 else 0) from by
        split_ifs <;> ring]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' s.candidatos c (fun _ => 1)]
  simp [hc]

/- ─────────────────────────────────────────────────────────
   PROPIEDAD 3 — Validez del ganador.   [Difícil — esqueleto]

   Si declaramos un ganador, ese ganador tiene
   estrictamente más votos que cualquier otro candidato.
   ───────────────────────────────────────────────────────── -/

theorem ganador_es_maximo
    (s : VotadorState)
    (g : String)
    (h : ganador s = some g) :
    ∀ c ∈ s.candidatos, c ≠ g → s.votos c < s.votos g := by
  intro c hc hne
  unfold ganador at h
  -- Análisis por casos del if interno de `ganador`
  split_ifs at h with hvac hcard
  · -- Caso 1: votantes = ∅ → ganador = none, contradice h
    simp at h
  · -- Caso 2: top.card = 1, donde top filtra candidatos con votos máximos
    -- En este caso h tiene la forma some (top.toList.head _) = some g
    -- Por lo tanto g ∈ top, lo que significa s.votos g = sup
    -- Como c ≠ g, c no está en top, así s.votos c < sup = s.votos g
    -- ATENCIÓN: el manejo de toList.head requiere lemmas técnicos.
    -- Si te cuesta cerrar esta parte, marcala con sorry.
    sorry
  · -- Caso 3: top.card ≠ 1 → ganador = none, contradice h
    simp at h

/- ─────────────────────────────────────────────────────────
   PROPIEDAD 4 — Empate honesto.   [Difícil — esqueleto]

   Si no hay ganador único (y hay votantes), existen
   al menos dos candidatos con el mismo máximo de votos.
   ───────────────────────────────────────────────────────── -/

theorem empate_es_real
    (s : VotadorState)
    (h : ganador s = none)
    (hne : s.votantes ≠ ∅) :
    ∃ a ∈ s.candidatos, ∃ b ∈ s.candidatos,
      a ≠ b ∧ s.votos a = s.votos b ∧
      ∀ c ∈ s.candidatos, s.votos c ≤ s.votos a := by
  unfold ganador at h
  split_ifs at h with hvac hcard
  · -- Caso 1: votantes = ∅, contradice hne
    exact absurd hvac hne
  · -- Caso 2: top.card = 1, pero entonces ganador = some _, contradice h
    simp at h
  · -- Caso 3: top.card ≠ 1, así que top tiene 0 o ≥ 2 elementos
    -- top es no vacío (siempre existe un candidato con el sup),
    -- así que top.card ≥ 2.
    -- Por Finset.one_lt_card_iff existen a, b ∈ top distintos.
    -- a, b ∈ top significa s.votos a = sup ∧ s.votos b = sup.
    -- Por lo tanto s.votos a = s.votos b.
    -- Y como sup es el máximo: ∀ c ∈ candidatos, s.votos c ≤ sup = s.votos a.
    sorry

/- ═══════════════════════════════════════════════════════════
   PRUEBA RÁPIDA
   ═══════════════════════════════════════════════════════════ -/

example : 2 + 2 = 4 := rfl

#check votar
#check ganador
