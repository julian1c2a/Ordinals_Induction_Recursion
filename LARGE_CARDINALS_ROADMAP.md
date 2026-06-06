# ROADMAP: Hacia el Principio de Vopěnka en Lean 4

Este documento establece la hoja de ruta arquitectónica para extender el universo dependiente `Dybjer` hasta las cimas más altas de la Teoría de Conjuntos: **Los Grandes Cardinales y el Principio de Vopěnka**.

## 1. El Rol Dual: `DybjerOrd` y `DybjerSet`

Para alcanzar estos niveles de abstracción, no basta con los ordinales. Los ordinales (`DybjerOrd`) proporcionan la **columna vertebral** (el buen orden, la cardinalidad, la recursión transfinita), pero necesitamos los conjuntos extensionales de Aczel (`DybjerSet`) para proporcionar la **carne**:
- Los **Ultrafiltros** operan sobre el conjunto potencia $\mathcal{P}(\kappa)$, que se expresa mejor con conjuntos.
- Las **Inmersiones Elementales** ($j: V \to M$) operan sobre el Universo de Conjuntos $V$, mapeando estructuras y relaciones complejas.
- Las **Clases y Categorías** del Principio de Vopěnka contienen "grafos" y "estructuras", formadas por conjuntos extensionales.

Por lo tanto, el trabajo futuro se dividirá en asentar `DybjerSet` y luego construir la jerarquía en `LargeCardinals/`.

---

## 2. Esqueleto Arquitectónico (`OrdinalsInductionRecursion/LargeCardinals/`)

### Fase I: Fundamentos Estructurales y Topológicos
Antes de definir nuevos cardinales, necesitamos las herramientas topológicas y de teoría de la medida en el contexto ordinal/conjuntista.

1. **`Filters.lean`**
   - Definición de Filtro y Ultrafiltro sobre un cardinal $\kappa$.
   - Definición de la propiedad de ser "$\kappa$-completo" (cerrado bajo intersecciones de tamaño menor a $\kappa$).

2. **`Stationary.lean`**
   - Definición de **Conjuntos Club** (Cerrados y No Acotados) sobre un ordinal.
   - Definición de **Conjuntos Estacionarios** (aquellos que intersecan a todo conjunto Club).
   - Lema de Fodor (derivada fundamental para probar propiedades de Mahlo).

### Fase II: La Primera Muralla de Grandes Cardinales
Usando las herramientas de la Fase I, escalamos más allá de los Inaccesibles.

3. **`Mahlo.lean`**
   - **Definición:** Un cardinal $\kappa$ es Mahlo si es inaccesible y el conjunto de cardinales regulares menores que $\kappa$ es estacionario en $\kappa$.
   - **Cardinales débilmente compactos:** Generalización a través de la Propiedad del Árbol (ausencia de árboles de Aronszajn de altura $\kappa$).

### Fase III: Teoría de Modelos Interna e Inmersiones
Para ir más allá de los débilmente compactos, Lean necesita "entender" la Lógica de Primer Orden para poder hablar de Verdad y Preservación de Modelos.

4. **`ModelTheory/Syntax.lean` y `ModelTheory/Semantics.lean`**
   - Deep embedding de la sintaxis lógica: Fórmulas, Variables, Cuantificadores.
   - Relación de satisfacción ($M \models \phi$).

5. **`Embeddings.lean`**
   - **Inmersiones Elementales ($j: V \to M$):** Funciones inyectivas entre la clase universo $V$ (basada en `DybjerSet`) y una subclase $M$, tal que preservan toda la verdad lógica.
   - Definición del Punto Crítico (el menor ordinal $\alpha$ tal que $j(\alpha) > \alpha$).

### Fase IV: Cardinales Fuertes y Woodin
Con las inmersiones elementales, definimos los cardinales modernos.

6. **`Measurable.lean`**
   - Definición clásica: Existencia de un ultrafiltro no principal $\kappa$-completo.
   - Teorema de equivalencia: $\kappa$ es medible si y solo si es el punto crítico de alguna inmersión elemental $j: V \to M$.

7. **`Woodin.lean` y `Supercompact.lean`**
   - Definiciones basadas en inmersiones elementales $j$ cuyo objetivo $M$ captura una gran cantidad de conjuntos (clausura bajo sucesiones de tamaño $\lambda$).

### Fase V: El Principio de Vopěnka
El objetivo final de este repositorio.

8. **`CategoryTheory/Classes.lean`**
   - Formalización de Clases Propias parametrizadas sobre el universo de `DybjerSet`.
   - Definición de "Estructura de una misma firma" (por ejemplo, la Clase de todos los Grafos).

9. **`Vopenka.lean`**
   - **Axioma de Vopěnka:** "Ninguna clase propia de estructuras relacionales de la misma firma es discreta."
   - Equivalentemente: "Para toda clase propia $C$ de estructuras, existen $A, B \in C$ y una inmersión elemental $j: A \to B$."
   - Propiedades reflexivas de Vopěnka hacia abajo (cómo Vopěnka implica la existencia de cardinales supercompactos y extendibles debajo de él).

---

## 3. Metodología y Ejecución

La meta es que cada archivo dentro de `LargeCardinals/` compile sin advertencias, basándose íntegramente en las pruebas fundacionales de `DybjerOrd` y `DybjerSet`. Al completar este mapa, el repositorio se convertirá en una de las formalizaciones computacionales de Teoría de Conjuntos más profundas y extensas jamás escritas en Lean 4.
