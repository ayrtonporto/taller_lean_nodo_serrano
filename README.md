# Taller Lean 4 — Las reglas tienen tipos

Repositorio del taller de formalización en Lean 4.
**No necesitás instalar nada.** Trabajamos en el browser.

---

## Cómo empezar (3 pasos)

### 1. Abrí este repo en Codespaces

Click en el botón verde **`<> Code`** arriba a la derecha →
pestaña **`Codespaces`** → **`Create codespace on main`**.

Si no tenés cuenta de GitHub, hacela ahora (gratis, 30 segundos).

### 2. Esperá que se prepare el entorno

La primera vez tarda **2-4 minutos** porque baja Lean 4 y Mathlib.
Vas a ver mensajes en la terminal inferior. Cuando aparezca
`Setup completo!`, está listo.

### 3. Abrí el archivo de tu grupo

- **Grupo A — Votador**: `Taller/Votador.lean`
- **Grupo B — F1**: `Taller/F1.lean`

A la derecha vas a ver el **InfoView**: te muestra el goal
actual en cada paso de la demostración. Si no lo ves, abrilo con
`Ctrl+Shift+Enter` (o `Cmd+Shift+Enter` en Mac).

---

## Cómo trabajar

Cada propiedad tiene la forma:

```lean
theorem nombre (...) : ... := by
  sorry   -- ← reemplazá esto por la demostración
```

Reemplazá `sorry` por las tácticas que demuestren la propiedad.
Cuando el archivo compila sin `sorry`, **Goals accomplished** —
la propiedad vale para todos los casos posibles.

### Tácticas útiles

| Táctica | Cuándo usarla |
|---------|---------------|
| `rfl` | Ambos lados de una igualdad son iguales por definición |
| `simp` | Simplifica usando lemmas conocidos de Mathlib |
| `simp [foo, bar]` | Lo mismo, pero incluyendo `foo` y `bar` |
| `exact h` | La prueba es exactamente la hipótesis `h` |
| `omega` | Aritmética automática sobre `ℕ` y `ℤ` |
| `ring` | Identidades algebraicas en anillos |
| `intro h` | Introduce una hipótesis del antecedente |
| `obtain ⟨a, b⟩ := h` | Desempaqueta un `∃` o un `∧` |
| `constructor` | Divide un `∧` o un `↔` en dos goals |
| `decide` | Decide propiedades sobre tipos finitos |

### Si te trabás

1. Mirá el **InfoView** — te dice exactamente qué falta probar.
2. Probá `exact?` o `apply?` (Lean busca lemmas que cierren el goal).
3. Pegale el goal completo a Claude o GPT y pedile sugerencias.
4. **Las propiedades fáciles se cierran en 1-2 líneas.** Si llevás 20
   minutos en una "fácil", probablemente te estás complicando.

---

## Estructura del repositorio

```
.
├── .devcontainer/         # Configuración de Codespaces (no tocar)
├── Taller/
│   ├── Votador.lean       # ← Grupo A trabaja acá
│   └── F1.lean            # ← Grupo B trabaja acá
├── lakefile.lean          # Define el proyecto y Mathlib
└── lean-toolchain         # Versión de Lean 4
```

---

## Recursos

- [Documentación Mathlib4](https://leanprover-community.github.io/mathlib4_docs/)
- [Búsqueda semántica Moogle](https://loogle.lean-lang.org/)
- [Mathematics in Lean (libro gratuito)](https://leanprover-community.github.io/mathematics_in_lean/)

---

Ayrton Porto · UNICEN, Tandil
