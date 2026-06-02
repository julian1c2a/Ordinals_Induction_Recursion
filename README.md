# Ordinals, Induction, and Recursion

Este repositorio sirve como un **proyecto de investigación y esqueleto** (*sandbox/skeleton*) para el estudio y la formalización de conceptos avanzados de Teoría de Conjuntos en Lean 4. Su objetivo principal es diseñar, aislar y probar estructuras matemáticas que posteriormente serán integradas en otros proyectos principales.

## Propósito y Contexto

Actualmente, proyectos base como **`AczelSetTheory`** ya implementan fundaciones como los **Conjuntos Hereditariamente Finitos (`HFSet`)** y los **Números Naturales**. Para continuar expandiendo dicha teoría de conjuntos, el proyecto `Aczel` tendrá dos expansiones principales. Este repositorio funciona como el banco de pruebas para esas expansiones:

1.  **Conjuntos Infinitos Numerables (Countable Sets)**: Extender la teoría más allá de lo finito, introduciendo conjuntos numerables y desarrollando la aritmética y el orden de los ordinales correspondientes.
2.  **Conjuntos Generales (Universal/General Sets)**: Una generalización completa hacia conjuntos arbitrarios (no necesariamente numerables) y ordinales generales, construyendo un marco axiomático mucho más amplio.

Al desarrollar estas expansiones aquí de forma independiente, podemos iterar rápidamente sobre las definiciones, principios de inducción, recursión, y estructuras de retículos (Lattices) antes de hacer un *porting* a la arquitectura oficial de `AczelSetTheory`.

## Estructura del Repositorio

El código fuente (ubicado en `OrdinalsInductionRecursion/`) está estructurado lógicamente para reflejar las dos grandes expansiones:

### 1. Expansión Numerable
-   **`CountableSets/`**: Definiciones base, axiomas y propiedades fundamentales de los conjuntos infinitos numerables.
-   **`CountableOrd/`**: Desarrollo de los **Ordinales Numerables**. Incluye el estudio de pre-órdenes extendidos (`ExtPreOrd.lean`), aritmética básica (`Arith.lean`) y pruebas para demostrar que forman estructuras de retículo distributivo (`OrdinalsLattice.lean`).

### 2. Expansión General
-   **`UnivSets/`**: Marco axiomático y definiciones fundamentales para los conjuntos en general (universales).
-   **`UnivOrd/`**: Desarrollo de los **Ordinales Generales/Universales**. Incluye mecanismos de *lifting* (`Lift.lean`) y formalización de pre-órdenes sobre clases más amplias de ordinales (`ExtPreOrd.lean`).

### Directorios Auxiliares
-   **`scratch/`**: Directorio raíz destinado a pruebas aisladas, demostraciones experimentales y módulos temporales (como `test_lift.lean` o `scratch_axioms.lean`) que no forman parte estricta de la jerarquía principal del módulo. Ideal para bocetar ideas.

## Líneas de Investigación Actuales

-   **Relaciones de Orden**: Establecimiento de relaciones de orden (Pre-órdenes, Órdenes Parciales) y equivalencias sobre ordinales.
-   **Teoría de Retículos**: Pruebas de existencia de ínfimos (intersecciones) y supremos (uniones), así como propiedades de distributividad en las jerarquías de ordinales.
-   **Inducción y Recursión Transfinita**: Construcción de principios sólidos para razonar inductivamente y definir funciones recursivas sobre estos nuevos tipos de conjuntos y ordinales.

## Notas de Uso

Como este es un proyecto referencial y de desarrollo de *esqueletos*:
1.  El código puede evolucionar rápidamente y estar sujeto a refactorizaciones severas.
2.  Las definiciones que alcanzan madurez son extraídas e integradas a los repositorios de destino formales.
3.  Usa el directorio `scratch/` para experimentos que requieran romper cosas sin afectar la compilación del proyecto principal (`lake build`).