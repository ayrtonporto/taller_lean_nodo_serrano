"""
═══════════════════════════════════════════════════════════
  GRUPO B — Campeonato F1 (Reglamento FIA 2025)
  Versión Python (la referencia que vamos a formalizar)
═══════════════════════════════════════════════════════════

Este archivo tiene el sistema de puntos funcionando en Python.
Compará con Taller/F1.lean — son el mismo modelo en dos lenguajes.

Para correrlo:
    python Python/f1.py
"""

from dataclasses import dataclass, field


# ───────────────────────────────────────────────────────────
# Tabla de puntos por posición (Reglamento FIA 2025)
# Sin punto por vuelta rápida (eliminado en 2025)
# ───────────────────────────────────────────────────────────
PUNTOS = {
    1: 25, 2: 18, 3: 15, 4: 12, 5: 10,
    6: 8,  7: 6,  8: 4,  9: 2,  10: 1,
}


@dataclass
class Piloto:
    nombre: str
    puntos: int = 0
    posiciones: list[int] = field(default_factory=list)  # historial


@dataclass
class Campeonato:
    pilotos: dict[str, Piloto] = field(default_factory=dict)

    def agregar_piloto(self, nombre: str) -> None:
        if nombre not in self.pilotos:
            self.pilotos[nombre] = Piloto(nombre=nombre)

    def registrar_carrera(self, resultado: list[str]) -> None:
        """Registra los resultados de una carrera.

        `resultado` es una lista ordenada: el primero ganó, el último
        terminó último.
        """
        for nombre in resultado:
            if nombre not in self.pilotos:
                self.agregar_piloto(nombre)

        for pos, nombre in enumerate(resultado, start=1):
            self.pilotos[nombre].puntos += PUNTOS.get(pos, 0)
            self.pilotos[nombre].posiciones.append(pos)

    def conteo(self, p: Piloto, k: int) -> int:
        """Cuántas veces el piloto terminó en la posición k."""
        return sum(1 for pos in p.posiciones if pos == k)

    def lider(self) -> str | None:
        """Líder del campeonato según puntos + countback.

        Comparación lexicográfica:
            (puntos, victorias, 2° lugares, 3°, ..., 10°)
        """
        if not self.pilotos:
            return None

        def clave(p: Piloto) -> tuple:
            return (p.puntos, *[self.conteo(p, k) for k in range(1, 11)])

        return max(self.pilotos.values(), key=clave).nombre


# ═══════════════════════════════════════════════════════════
#   TESTS — verifican las 4 propiedades empíricamente
# ═══════════════════════════════════════════════════════════

def test_puntos_no_negativos():
    """Propiedad 1: puntos siempre ≥ 0 (gratis: usamos int)."""
    c = Campeonato()
    c.agregar_piloto("Verstappen")
    assert c.pilotos["Verstappen"].puntos >= 0
    print("✓ Propiedad 1: puntos no negativos")


def test_max_puntos_por_carrera():
    """Propiedad 2: una carrera distribuye como máximo 101 puntos."""
    total_max = sum(PUNTOS.values())  # 25+18+15+12+10+8+6+4+2+1
    assert total_max == 101
    print(f"✓ Propiedad 2: máx por carrera = {total_max} puntos")


def test_validez_lider():
    """Propiedad 3: si hay líder, nadie tiene más puntos."""
    c = Campeonato()
    c.registrar_carrera(["Verstappen", "Norris", "Leclerc"])
    c.registrar_carrera(["Norris", "Verstappen", "Leclerc"])

    lider = c.lider()
    puntos_lider = c.pilotos[lider].puntos

    for nombre, piloto in c.pilotos.items():
        assert piloto.puntos <= puntos_lider, \
            f"{nombre} tiene {piloto.puntos} pero líder tiene {puntos_lider}"
    print(f"✓ Propiedad 3: validez del líder ({lider} con {puntos_lider} pts)")


def test_countback_victorias():
    """Propiedad 4: empate en puntos → decide victorias."""
    c = Campeonato()
    # Construimos un escenario de empate en puntos
    # Verstappen: 2 victorias + 1 segundo  = 25+25+18 = 68
    # Norris:     1 victoria + 2 segundos  = 25+18+18 = 61... no empate.

    # Mejor escenario: Verstappen 25+18+25 = 68 con 2 victorias
    #                  Hamilton   25+18+25 = 68 con 2 victorias - empate total
    # Hagámoslo simple: empate en puntos, diferencia en victorias
    c.registrar_carrera(["Verstappen", "Hamilton", "Bottas"])  # V:25, H:18, B:15
    c.registrar_carrera(["Hamilton", "Verstappen", "Bottas"])  # V:18, H:25, B:15

    # Ambos tienen 43 puntos y 1 victoria cada uno. Forzamos diferencia:
    c.registrar_carrera(["Verstappen", "Bottas", "Hamilton"])  # V:25, H:15, B:18

    # Ahora: V tiene 68 puntos y 2 victorias
    #        H tiene 58 puntos y 1 victoria
    # No es empate de puntos. Hagamos manualmente uno:

    c2 = Campeonato()
    c2.pilotos["A"] = Piloto(nombre="A", puntos=50, posiciones=[1, 1, 3])  # 2 vict
    c2.pilotos["B"] = Piloto(nombre="B", puntos=50, posiciones=[1, 2, 2])  # 1 vict

    lider = c2.lider()
    assert lider == "A", f"Esperaba A (más victorias), obtuve {lider}"
    print("✓ Propiedad 4: countback por victorias")


# ═══════════════════════════════════════════════════════════
#   DEMO INTERACTIVA
# ═══════════════════════════════════════════════════════════

def demo():
    print("\n─── DEMO: Temporada simulada ───")
    camp = Campeonato()

    # Calendario reducido
    carreras = [
        ("Bahrain",     ["Verstappen", "Norris", "Leclerc", "Hamilton"]),
        ("Saudi",       ["Norris", "Verstappen", "Hamilton", "Leclerc"]),
        ("Australia",   ["Verstappen", "Leclerc", "Norris", "Hamilton"]),
        ("Japan",       ["Leclerc", "Norris", "Verstappen", "Hamilton"]),
    ]

    for nombre, resultado in carreras:
        camp.registrar_carrera(resultado)
        print(f"  {nombre:10s} → {resultado[0]} ganó")

    print("\n  Clasificación:")
    pilotos_ord = sorted(
        camp.pilotos.values(),
        key=lambda p: (p.puntos, *[camp.conteo(p, k) for k in range(1, 11)]),
        reverse=True,
    )
    for i, p in enumerate(pilotos_ord, 1):
        vict = camp.conteo(p, 1)
        print(f"    {i}. {p.nombre:12s} {p.puntos:3d} pts  ({vict} victorias)")

    print(f"\n  Líder: {camp.lider()}")


if __name__ == "__main__":
    print("Tests de propiedades:")
    test_puntos_no_negativos()
    test_max_puntos_por_carrera()
    test_validez_lider()
    test_countback_victorias()

    demo()

    print("\n→ Estas propiedades pasaron los tests.")
    print("→ En Lean 4 vamos a *demostrarlas* para todos los casos posibles.")
