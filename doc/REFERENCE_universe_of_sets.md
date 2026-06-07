# Universo de Conjuntos: Bisimulación Extensional

Los ordinales son un caso muy particular en matemáticas: conjuntos asombrosamente ordenados donde todo elemento de un ordinal también es un subconjunto del mismo (transitividad). Sin embargo, la **Teoría de Conjuntos (Aczel Set Theory)** modela el universo $V$ completo, que aloja todo tipo de estructuras no ordenadas (como los Reales, Grafos, Topologías).

Este volumen documenta la arquitectura de los sub-directorios dedicados a Conjuntos: `CountableSets`, `UnivSets`, `TarskiSet` y `DybjerSet`.

## 1. Bisimulación de Aczel
La característica distintiva entre los "Ord" y los "Set" en este repositorio recae en las relaciones fundamentales de pertenencia (`Mem`) y subconjunto (`Subset`).
Dado que no asumimos transitividad, definimos la equivalencia de forma cruzada (Bisimulación):
- Un árbol $A$ es un **subconjunto** de $B$ si para cada rama (elemento) de $A$, podemos encontrar una rama **equivalente** en $B$.
- Un árbol $x$ **pertenece** a un árbol $A$, si $x$ es **equivalente** a alguna de las ramas formales de $A$.
- Dos árboles son **equivalentes** (extensionalmente el mismo conjunto matemático) si ambos son subconjuntos el uno del otro.

Todas las pruebas en los directorios de Set (en el archivo `Tree.lean`) se orientan exclusivamente a validar este triángulo lógico, probando que el Setoid final cumple perfectamente con el principio de Extensionalidad Clásica.

## 2. Los Cuatro Modelos Instanciados
Al igual que en los ordinales, poseemos cuatro niveles para los conjuntos:
1. **CountableSets ($HC$):** Modelan la familia de conjuntos Hereditariamente Numerables.
2. **UnivSets ($V_u$):** Los W-types universales tradicionales construidos en `Type (u+1)`.
3. **TarskiSet:** El modelo puro de conjuntos de Aczel con control predicativo total a través de `UCode`. 
4. **DybjerSet:** El clímax teórico: conjuntos plenamente expresivos pero acotados por familias inductivas `UCodeFam`.

## 3. Instanciación Axiomática de ZF
El éxito de un modelo de Teoría de Conjuntos descansa en validar los Axiomas ZF de forma interna en Lean (usualmente documentado en el archivo `Axioms.lean`). En cada de estos cuatro modelos implementamos computacionalmente:
- **Axioma de Extensionalidad:** Directamente resuelto por la definición de equivalencia en el cociente.
- **Axioma del Vacío:** Se codificó utilizando el constructor `.zero` nativo de nuestros árboles, probando lógicamente su vacuidad total.
- **Axioma de Adjunción (Unión Singleton):** La inserción explícita de un elemento en un árbol sin dañar sus ramas pre-existentes, valiéndonos de `.succ` y sumas disjuntas `.sum`.
- **Axiomas Estructurales Fuertes (Separación, Potencia, Reemplazo):** Operan filtrando, transformando y recolectando las ramas de un árbol a través de funciones mapeadas, garantizando explícitamente (usando `Quotient.lift`) que dichas operaciones respetan la Equivalencia de Bisimulación.
