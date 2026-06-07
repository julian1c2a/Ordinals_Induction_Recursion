# Workflow & Methodology

Basado en metodologías de desarrollo matemático de `AczelSetTheory` y `FOL`.

## Flujo de Trabajo Lean + IA
1. **Alineación:** Todo desarrollo comienza confirmando los objetivos en `PLANNING.md` y las tareas inmediatas en `NEXT-STEPS.md`.
2. **Implementación Estricta:** Escribir definiciones y teoremas en Lean 4. Las demostraciones deben ser robustas y preferentemente libres de `sorry`. Las convenciones de Mathlib (`NAMING-CONVENTIONS.md`) son obligatorias.
3. **Compilación Continua:** Se asume y exige la ejecución frecuente de `lake build` para comprobar consistencia.
4. **Sincronización de Documentación:** Aplicar el protocolo de proyección de `AI-GUIDE.md`. Tras cada sesión significativa, los hallazgos y avances deben fluir hacia `CHANGELOG.md`, `CURRENT-STATUS-PROJECT.md` y `NEXT-STEPS.md`.
5. **Modularidad y Bloqueo:** Los archivos maduros y verificados (✅) se tratan como inmutables para construir las capas superiores sin riesgo de regresiones.
