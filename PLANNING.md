# Planificación de Desarrollo (PLANNING)

Este documento centraliza los objetivos macro del repositorio `Ordinals_Induction_Recursion` y su estado actual de consecución.

## Visión General
El objetivo maestro es estabilizar los esqueletos fundamentales de los árboles bien fundados (tanto para Ontología Ordinal como para la Extensionalidad de Aczel) para su inyección posterior en el proyecto mayor `AczelSetTheory`.

---

## Fases de Desarrollo

### 🟢 Fase 1: Fundaciones y Estabilización (Completado)
- [x] Ontología Ordinal base (`PreOrd`) y aritmética.
- [x] Equivalencia extensional y Teorema de Tricotomía sin `sorry`.
- [x] Mapeo e Isomorfismo de Mostowski.

### 🟢 Fase 2: Exploración Computacional vs Platónica (Completado)
- [x] Implementación de universos nativos abiertos (`UnivOrd`, `UnivSets`).
- [x] Implementación estricta de universos a la Tarski (`TarskiOrd`, `TarskiSet`).
- [x] Formalización axiomática de sub-conjuntos ZFC elementales en `TarskiSet`.
- [x] Identificación matemática del límite de Tarski: imposibilidad de Unión y Potencia por falta de tipos dependientes (`Sigma` y `Pi`).
- [x] Inyecciones estrictas hacia arriba (`Tarski ↪ Univ`) respetando el Teorema de Cantor.

### 🟡 Fase 3: La Familia de Dybjer y Completitud ZFC (En Progreso)
- [x] Construcción de `DybjerOrd` mediante familias inductivas indexadas (`UCodeFam`).
- [x] Aritmética transinfinita en `DybjerOrd` ($\aleph$, $\beth$, Universos de Grothendieck explícitos).
- [ ] **OBJETIVO ACTIVO:** Trasplantar y completar ZFC en `DybjerSet` (aprovechando `Sigma` y `Pi` para la Unión y el Conjunto Potencia).

### 🔴 Fase 4: La Jerarquía de Grandes Cardinales (Por Iniciar)
*(Consultar `LARGE_CARDINALS_ROADMAP.md` para los detalles exhaustivos).*
- [ ] **Teoría Descriptiva:** Filtros, Ideales y Conjuntos Estacionarios.
- [ ] **Cardinales de Mahlo:** Postulación de inalcanzabilidad estacionaria.
- [ ] **Teoría de Modelos y Medibilidad:** Ultrafiltros e Inmersiones Elementales ($j : V \to M$).
- [ ] **El Principio de Vopěnka:** Culminación teórica de los axiomas de tamaño estructural.

---

## Notas Arquitectónicas
- Siempre priorizaremos las pruebas **libres de `sorry`**.
- La ontología se mantendrá segmentada (Ord vs Set) para facilitar el trasplante modular futuro.
