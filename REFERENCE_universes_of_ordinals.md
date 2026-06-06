# Universo de Ordinales: Ramas y Esqueletos

A diferencia de los conjuntos ordinarios, nuestra concepción nativa de Ordinal en este repositorio trae codificada de fábrica la idea de "Transitividad" y "Buena Fundación". La pertenencia se define de forma estructural: si $x$ forma parte de las ramas que construyen a un árbol $y$, o es menor que alguna de esas ramas, entonces $x \in y$. 

Este volumen enumera las 4 jerarquías de ordinales exploradas, de menor a mayor complejidad teórica.

## 1. Ordinales Numerables (`CountableOrd`)
El modelo fundacional de "calentamiento".
- Las ramas están acotadas al índice `Nat` estándar de Lean.
- Implementa sin ambigüedades la tricotomía estricta de ordinales ($x < y \lor x = y \lor y < x$).
- Ideal para trabajar bajo axiomas sin infinito no-numerable o en topologías muy simples.

## 2. Ordinales de Grothendieck (`UnivOrd`)
El modelo para las altas matemáticas clásicas. Usa `Type u` directo para las ramas, lo que significa que el árbol en sí vive en `Type (u+1)`.
- **Aritmética y Cardinales:** Suma, Producto, Retículos Distributivos Completos (Lattice).
- **Mostowski y Hartogs:** Implementa la asignación cardinal de Von Neumann usando recursión de límite puro y mapeo isomórfico de clases bien ordenadas.
- **Inaccesibilidad:** Cuenta con el marco para postular la existencia de **Universos Inaccesibles de Grothendieck** internamente en el lenguaje, forzando cortes sobre la jerarquía $\aleph$ para estudiar consistencia relativa.

## 3. TarskiOrd y 4. DybjerOrd (La Vía Constructiva)
En Lean, iterar un modelo basado en `Type u` genera un rastro indeseado de parámetros universales a través de todo el código (infiernos de `.{u, v, w}`).
La vía constructiva re-empaqueta la noción ordinal:
- **TarskiOrd** usa `UCode` (Tipos simples).
- **DybjerOrd** usa `UCodeFam` (Tipos Dependientes nativos).
Ambos mantienen el árbol firmemente plantado en un solo universo tipológico, blindando el cálculo de fugas paramétricas.

### Matemáticas Avanzadas Implementadas
En los modelos constructivos de `TarskiOrd` y `DybjerOrd` hemos logrado asentar los hitos más complejos de la Teoría de Conjuntos de forma rigurosa:
1. **Inducción y Recursión Transfinita:** Haciendo uso del predicado de "Bien Fundado" nativo de Lean (`WellFounded.fix`), lo cual garantiza al kernel que nuestras operaciones sobre ramas hiperfinitas terminan algorítmicamente.
2. **Número de Hartogs:** Proceso de asignación que prueba constructivamente que para cualquier conjunto/ordinal, existe un ordinal estrictamente mayor en cardinalidad.
3. **Jerarquía $\aleph_\alpha$ (Alephs):** Evaluada estructuralmente sobre todos los ordinales límite y sucesor sin requerir del Axioma de Elección completo del metalenguaje.
4. **Colapso de Mostowski:** Colapso de cualquier relación bien fundada a un ordinal nativo (restringido a tipos `UCode` en Tarski, y genérico en Dybjer).
5. **Cofinalidad y Regularidad:** Maquinaria para determinar la cofinalidad de ordinales, clasificación de cardinales (regulares/singulares) y aritmética cardinal familiar (como base para el teorema de König).
