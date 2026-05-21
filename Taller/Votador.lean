/-
  ═══════════════════════════════════════════════════════════
  Taller Lean 4 — GRUPO A
  Sistema de Votación por Mayoría Simple
  ═══════════════════════════════════════════════════════════

  El objetivo: formalizar el votador en Python y demostrar
  4 propiedades fundamentales como teoremas.

  Las propiedades están enunciadas. Reemplacen `sorry` por
  la demostración. Si compila → Goals accomplished.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Basic

open Finset

/- ─────────────────────────────────────────────────────────
   PARTE 1 — EL MODELO

   En Python:
     class Votador:
         candidatos : list[str]
         votos      : dict[str, int]
         votantes   : set[str]
   ───────────────────────────────────────────────────────── -/

/-- Estado del votador.
    `votos` es una función total: candidatos válidos pueden tener > 0,
    cualquier otro string tiene 0. -/
structure VotadorState where
  candidatos : Finset String
  votos      : String → ℕ
  votantes   : Finset String

/- ─────────────────────────────────────────────────────────
   PARTE 2 — LA OPERACIÓN VOTAR

   En Python:
     def votar(self, votante, candidato):
       if votante in self.votantes: raise ValueError(...)
       if candidato not in self.votos: raise ValueError(...)
       self.votos[candidato] += 1
       self.votantes.add(votante)

   En Lean las guardas son PARÁMETROS DEL TIPO:
   hv y hc son pruebas que el caller debe proveer.
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

   En Python:
     def ganador(self) -> str | None:
       if not self.votantes: return None
       max_v = max(self.votos.values())
       top = [c for c,v in self.votos.items() if v == max_v]
       return top[0] if len(top)==1 else None
   ───────────────────────────────────────────────────────── -/

/-- Devuelve el ganador único si existe, `none` si hay empate o no hay votantes. -/
def ganador (s : VotadorState) : Option String :=
  if s.votantes = ∅ then none
  else
    let votosMax := s.candidatos.sup s.votos
    let top := s.candidatos.filter (fun c => s.votos c = votosMax)
    if h : top.card = 1 then
      some (top.toList.head (by
        simp only [← Finset.length_toList]
        omega))
    else none

/- ═══════════════════════════════════════════════════════════
   LAS CUATRO PROPIEDADES A DEMOSTRAR
   ═══════════════════════════════════════════════════════════ -/

/- ─────────────────────────────────────────────────────────
   PROPIEDAD 1 — Un votante, un voto.   [Fácil]

   Después de que un votante vote, queda registrado.
   No puede votar dos veces — la guarda `hv` lo impide
   por construcción.

   Pista: `simp [votar]` debería cerrarlo.
   ───────────────────────────────────────────────────────── -/

theorem votar_registra
    (s : VotadorState)
    (v c : String)
    (hv : v ∉ s.votantes)
    (hc : c ∈ s.candidatos) :
    v ∈ (votar s v c hv hc).votantes := by
  sorry

/- ─────────────────────────────────────────────────────────
   PROPIEDAD 2 — Conservación de votos.   [Media]

   La suma total de votos sobre todos los candidatos
   coincide con el número de votantes.

   Acá la dificultad está en que `s.votos` es una función,
   no un Finset, y hay que sumar sobre los candidatos.

   Pista: usar `Finset.sum_ite` y la hipótesis del estado
   inicial. Esta propiedad NO se demuestra solo sobre
   un estado arbitrario — necesita inducción sobre cómo
   se construyó.
   ───────────────────────────────────────────────────────── -/

/-- Lema auxiliar: después de votar, la suma aumenta en 1. -/
theorem suma_votos_post_votar
    (s : VotadorState)
    (v c : String)
    (hv : v ∉ s.votantes)
    (hc : c ∈ s.candidatos) :
    (s.candidatos.sum (votar s v c hv hc).votos) =
    s.candidatos.sum s.votos + 1 := by
  sorry

/- ─────────────────────────────────────────────────────────
   PROPIEDAD 3 — Validez del ganador.   [Difícil]

   Si declaramos un ganador, ese ganador tiene
   estrictamente más votos que cualquier otro candidato.

   Pista: usar la definición de `ganador` y el hecho
   de que viene de un filter sobre el sup.
   ───────────────────────────────────────────────────────── -/

theorem ganador_es_maximo
    (s : VotadorState)
    (g : String)
    (h : ganador s = some g) :
    ∀ c ∈ s.candidatos, c ≠ g → s.votos c < s.votos g := by
  sorry

/- ─────────────────────────────────────────────────────────
   PROPIEDAD 4 — Empate honesto.   [Difícil]

   Si no hay ganador único (y hay votantes), entonces
   existen al menos dos candidatos con el mismo
   máximo de votos.

   Pista: por contradicción. Si todos tienen votos
   distintos, el top filter tiene cardinal 1.
   ───────────────────────────────────────────────────────── -/

theorem empate_es_real
    (s : VotadorState)
    (h : ganador s = none)
    (hne : s.votantes ≠ ∅) :
    ∃ a ∈ s.candidatos, ∃ b ∈ s.candidatos,
      a ≠ b ∧ s.votos a = s.votos b ∧
      ∀ c ∈ s.candidatos, s.votos c ≤ s.votos a := by
  sorry

/- ═══════════════════════════════════════════════════════════
   PRUEBA RÁPIDA - PARA VER QUE EL ENTORNO FUNCIONA

   Cuando todo lo de arriba esté bien, este teorema
   debería compilar sin sorry:
   ═══════════════════════════════════════════════════════════ -/

example : 2 + 2 = 4 := rfl

#check votar
#check ganador
