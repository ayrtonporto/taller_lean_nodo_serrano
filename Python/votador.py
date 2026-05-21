"""
═══════════════════════════════════════════════════════════
  GRUPO A — Sistema de Votación por Mayoría Simple
  Versión Python (la referencia que vamos a formalizar)
═══════════════════════════════════════════════════════════

Este archivo tiene el sistema funcionando en Python.
Compará con Taller/Votador.lean — son el mismo modelo
en dos lenguajes distintos.

Para correrlo:
    python Python/votador.py
"""


class Votador:
    def __init__(self, candidatos: list[str]):
        assert len(candidatos) >= 2, "Se necesitan al menos 2 candidatos"
        self.candidatos = candidatos
        self.votos = {c: 0 for c in candidatos}
        self.votantes: set[str] = set()

    def votar(self, votante: str, candidato: str) -> None:
        # Guardas: en Python son if/raise (runtime)
        # En Lean serán parámetros del tipo (compile time)
        if votante in self.votantes:
            raise ValueError(f"{votante} ya votó")
        if candidato not in self.votos:
            raise ValueError(f"{candidato} no es un candidato válido")

        self.votos[candidato] += 1
        self.votantes.add(votante)

    def ganador(self) -> str | None:
        if not self.votantes:
            return None

        max_votos = max(self.votos.values())
        ganadores = [c for c, v in self.votos.items() if v == max_votos]

        # Si hay un único ganador, lo retornamos. Si hay empate, None.
        return ganadores[0] if len(ganadores) == 1 else None

    def total_votos(self) -> int:
        return len(self.votantes)


# ═══════════════════════════════════════════════════════════
#   TESTS — verifican las 4 propiedades empíricamente
#   (en Lean las vamos a demostrar formalmente)
# ═══════════════════════════════════════════════════════════

def test_un_votante_un_voto():
    """Propiedad 1: nadie puede votar dos veces."""
    v = Votador(["A", "B"])
    v.votar("alice", "A")
    try:
        v.votar("alice", "B")
        assert False, "alice no debería poder votar dos veces"
    except ValueError:
        pass
    print("✓ Propiedad 1: un votante, un voto")


def test_conservacion_votos():
    """Propiedad 2: suma de votos = número de votantes."""
    v = Votador(["A", "B", "C"])
    v.votar("alice", "A")
    v.votar("bob", "B")
    v.votar("carol", "A")

    assert sum(v.votos.values()) == v.total_votos() == 3
    print("✓ Propiedad 2: conservación de votos")


def test_validez_ganador():
    """Propiedad 3: si hay ganador, tiene estrictamente más votos."""
    v = Votador(["A", "B", "C"])
    v.votar("alice", "A")
    v.votar("bob", "A")
    v.votar("carol", "B")

    g = v.ganador()
    assert g == "A"
    for c in v.candidatos:
        if c != g:
            assert v.votos[c] < v.votos[g]
    print("✓ Propiedad 3: validez del ganador")


def test_empate_honesto():
    """Propiedad 4: si no hay ganador, hay empate real."""
    v = Votador(["A", "B"])
    v.votar("alice", "A")
    v.votar("bob", "B")

    assert v.ganador() is None
    assert v.votos["A"] == v.votos["B"]
    print("✓ Propiedad 4: empate honesto")


# ═══════════════════════════════════════════════════════════
#   DEMO INTERACTIVA
# ═══════════════════════════════════════════════════════════

def demo():
    print("\n─── DEMO ───")
    elecciones = Votador(["Alice", "Bob", "Carol"])

    votos_simulados = [
        ("v1", "Alice"), ("v2", "Bob"), ("v3", "Alice"),
        ("v4", "Carol"), ("v5", "Alice"), ("v6", "Bob"),
    ]

    for votante, candidato in votos_simulados:
        elecciones.votar(votante, candidato)
        print(f"  {votante:4s} votó a {candidato}")

    print(f"\n  Votos: {dict(elecciones.votos)}")
    print(f"  Ganador: {elecciones.ganador()}")


if __name__ == "__main__":
    print("Tests de propiedades:")
    test_un_votante_un_voto()
    test_conservacion_votos()
    test_validez_ganador()
    test_empate_honesto()

    demo()

    print("\n→ Estas propiedades pasaron los tests.")
    print("→ En Lean 4 vamos a *demostrarlas* para todos los casos posibles.")
