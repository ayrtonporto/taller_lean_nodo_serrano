#!/usr/bin/env bash
set -e

echo "═══════════════════════════════════════════════════════════"
echo "  Setup del entorno Lean 4 para el taller"
echo "═══════════════════════════════════════════════════════════"

# Instalar elan (el gestor de versiones de Lean)
echo ""
echo "[1/3] Instalando elan..."
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none

# Agregar elan al PATH
echo 'export PATH="$HOME/.elan/bin:$PATH"' >> ~/.bashrc
export PATH="$HOME/.elan/bin:$PATH"

# Descargar la versión de Lean del proyecto
echo ""
echo "[2/3] Descargando Lean 4 (esto puede tardar 1-2 min)..."
cd /workspaces/$(basename $(pwd))
elan toolchain install $(cat lean-toolchain)

# Descargar Mathlib precompilada
echo ""
echo "[3/3] Descargando Mathlib precompilada (esto puede tardar 3-5 min)..."
lake exe cache get || echo "Si falla, ejecutá manualmente: lake exe cache get"

echo ""
echo "═══════════════════════════════════════════════════════════"
echo "  Setup completo!"
echo ""
echo "  Abrí Taller/Votador.lean o Taller/F1.lean"
echo "  para empezar a trabajar."
echo "═══════════════════════════════════════════════════════════"
