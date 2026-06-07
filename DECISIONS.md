# Architectural Decision Records (ADRs)

## ADR 001: Segmentación Ordinal/Conjuntista y Universos
**Fecha:** 2026-06-07
**Estado:** Aceptado
**Decisión:** El desarrollo formal se dividirá sistemáticamente en dos ejes paralelos:
1. `Ord` (E.g. `TarskiOrd`, `DybjerOrd`): La espina dorsal, enfocada en buen orden y recursión.
2. `Set` (E.g. `TarskiSet`, `DybjerSet`): Construcción extensional estilo Aczel, enfocada en la pertenencia y axiomas de ZF.
La transición desde Tarski hacia Dybjer obedece a la necesidad arquitectónica de contar con tipos dependientes (`Pi`, `Sigma`) en el meta-lenguaje para computar los conjuntos Potencia y Unión.
