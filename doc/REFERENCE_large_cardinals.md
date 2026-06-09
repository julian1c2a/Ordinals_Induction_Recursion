# REFERENCE: Grandes Cardinales y Principio de Vopěnka

Este volumen documenta la jerarquía extendida de **Grandes Cardinales** implementada en la sublibrería `UnivCard`. A diferencia de otras aproximaciones formales basadas puramente en Types o lógica de primer orden aislada, nuestra construcción está firmemente cimentada en la jerarquía material del modelo extensional `USet`.

## Módulos Principales de `UnivCard`

### 1. Equipolencia y Cardinalidad Básica
- **`Equipollence.lean`**: Define inyecciones, biyecciones y la relación de equipotencia (`Equipollent`) puramente sobre los conjuntos materiales `USet`. Se demuestra que esta relación es de equivalencia (reflexiva, simétrica, transitiva) y que preserva subconjuntos lógicos.
- **`Cardinal.lean`**: Aborda la definición de cardinalidad (`IsCardinal`). Se establece un cardinal como el ordinal inicial de su clase de equipotencia.

### 2. Topología Ordinal y Conjuntos Cerrados No Acotados (CUB)
La ascensión a los cardinales superiores requiere infraestructura topológica sobre secuencias ordinales.
- **`Topology.lean`**: Introduce las nociones de Límite Topológico, Puntos de Acumulación (`LimitPoint`) y Conjuntos Cerrados (`IsClosed`) evaluando el supremo de las secuencias dentro del tipo material.
- **`CUB.lean`**: Expande la topología definiendo conjuntos No Acotados (`IsUnbounded`) y los conjuntos CUB (`IsCUB`). Se incluye la formalización de que la intersección de conjuntos CUB sigue siendo CUB.

### 3. La Torre de Inaccesibilidad
- **`Inaccessible.lean`**: Define formalmente la Regularidad (`IsRegular`) como aquellos cardinales cuya cofinalidad coincide con ellos mismos, el Límite Fuerte (`IsStrongLimit`), y conjuga ambas propiedades para definir el Cardinal Fuertemente Inaccesible (`IsInaccessible`).

### 4. El Puente Semántico: Universos de Grothendieck
- **`GrothendieckBridge.lean`**: Formaliza abstractamente un Universo de Grothendieck (`IsGrothendieckUniverse`) como un conjunto material clausurado bajo partes, pares, unión y transitividad. Postula el `grothendieck_bridge`: el axioma que equipara semánticamente a los cardinales fuertemente inaccesibles con la existencia de Universos de Grothendieck. Este axioma conecta la teoría de conjuntos y teoría de modelos con los universos funcionales de Lean (Dybjer).

### 5. Mahlo y Medibles
- **`Mahlo.lean`**: Define los Cardinales de Mahlo (`IsMahlo`) probando la estacionariedad del subconjunto de los cardinales regulares que viven por debajo del cardinal dado $\kappa$.
- **`Measurable.lean`**: Aborda la teoría de Ultrafiltros. Define filtros sobre conjuntos y su versión $\kappa$-completa (`IsKappaComplete`), para finalmente postular los Cardinales Medibles (`IsMeasurable`).

### 6. Estructuras y el Principio de Vopěnka
El hito definitivo de la teoría axiomática construida.
- **`Structure.lean`**: Construye el marco de Estructuras Relacionales (`RelStructure`) e Inmersiones (`IsEmbedding`) donde dominio y morfismos existen plenamente como elementos o propiedades de `USet`.
- **`Vopenka.lean`**: Define lo que es una "Clase Propia" (`IsProperClass`) desde la perspectiva de `USet` (clases cuyos dominios no se acotan bajo ningún $S \in \text{USet}$). Formaliza el supremo absoluto: el **Principio de Vopěnka (`vopenka_principle`)**, estableciendo que toda clase propia de estructuras alberga inmersiones entre al menos dos de sus miembros distintos.

---
Con este módulo, el proyecto `Ordinals_Induction_Recursion` se eleva desde la Aritmética de Peano básica hasta ser un marco equivalente a la **Teoría de Tarski-Grothendieck con el Principio de Vopěnka (TG + VP)**.
