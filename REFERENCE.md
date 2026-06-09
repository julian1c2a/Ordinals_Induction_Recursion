# REFERENCE: Estructura Central del Ecosistema

Bienvenido al directorio de referencias técnicas y metodológicas del proyecto **Ordinals, Induction & Recursion**. A diferencia de otros repositorios puramente matemáticos, este proyecto es un **Sandbox (Campo de pruebas y aprendizaje)**. Por lo tanto, la documentación está diseñada para enseñar, guiar e instruir sobre los pilares fundamentales tanto de la Inteligencia Artificial que te asiste, como de las matemáticas implementadas.

## 🤖 Guías Operativas y de Inteligencia Artificial

Al estar construyendo un sistema matemático riguroso, nuestra dinámica de colaboración sigue estrictas convenciones. Estas guías no solo dirigen a la IA, sino que sirven como una explicación pedagógica sobre cómo pensamos y estructuramos las soluciones:

- [**AI-GUIDE.md**](file:///e:/dropbox/github/lean4/Ordinals_Induction_Recursion/AI-GUIDE.md): El manifiesto de comportamiento de la IA. Explica la arquitectura de "Agente Supervisor / Agente Codificador", las reglas de verificación paso a paso, y la prohibición estricta de generar `sorry` o avanzar sin comprobar rigurosamente con `lake build`. Léelo si deseas entender el razonamiento detrás de los flujos de trabajo de la IA en este proyecto.
- [**NAMING-CONVENTIONS.md**](file:///e:/dropbox/github/lean4/Ordinals_Induction_Recursion/NAMING-CONVENTIONS.md): Nuestro manual de estilo. Explica detalladamente cómo y por qué nombramos las variables, teoremas y estructuras matemáticas (por qué usamos `DPreOrd` en lugar de `PreOrd`, por qué los Lemas llevan CamelCase, etc). Es indispensable para mantener el código base homogéneo y legible.

---

## 🧮 Referencia Matemática y Arquitectónica

El núcleo del proyecto formaliza las **Estructuras de Computación, Teoría Ordinal, y Teoría de Conjuntos**. Para facilitar la lectura, la referencia matemática se ha dividido en tres grandes volúmenes:

### 1. Estructuras de Computación (Cimientos)
> Enlace directo: [**doc/REFERENCE_computation_structs.md**](file:///e:/dropbox/github/lean4/Ordinals_Induction_Recursion/doc/REFERENCE_computation_structs.md)

Este documento detalla la fontanería computacional de Lean 4 subyacente. Si deseas entender **cómo** superamos los problemas sintácticos de constructibilidad en Type Theory, aquí encontrarás las explicaciones sobre los `W-types`, los **Universos de Tarski** (`UCode`), el asombroso truco de las **Familias Inductivas Indexadas de Dybjer** (`UCodeFam`), y la arquitectura general basada en cocientes (Setoides).

### 2. Universo de Ordinales
> Enlace directo: [**doc/REFERENCE_universes_of_ordinals.md**](file:///e:/dropbox/github/lean4/Ordinals_Induction_Recursion/doc/REFERENCE_universes_of_ordinals.md)

Este volumen documenta todo lo referido a los **Ordinales Transitivos Nativos** (`PreOrd`). Explora las diferencias entre los cuatro esqueletos implementados:
- **CountableOrd:** Ordinales construidos con supremos numerables (`Nat`).
- **UnivOrd:** Ordinales genéricos con universos de Grothendieck (Inaccesibles).
- **TarskiOrd / DybjerOrd:** Ordinales 100% constructivos y predicativos.
También cubre hitos matemáticos fundamentales como la *Inducción Transfinita*, la *Aritmética Cardinal*, la *Función de Hartogs*, la *Jerarquía de los Alephs ($\aleph_\alpha$)*, y el *Colapso de Mostowski*.

### 3. Universo de Conjuntos
> Enlace directo: [**doc/REFERENCE_universe_of_sets.md**](file:///e:/dropbox/github/lean4/Ordinals_Induction_Recursion/doc/REFERENCE_universe_of_sets.md)

A diferencia de los ordinales que asumen transitividad, los **Conjuntos** modelan el Universo Extensional ($V$) clásico. Aquí se explica en detalle la **Bisimulación de Aczel** (la verdadera clave computacional de la equivalencia extensional). Aborda los cuatro modelos equivalentes en el lado de la teoría de conjuntos: `CountableSets`, `UnivSets`, `TarskiSet` y `DybjerSet`, y detalla cómo se instancian los **Axiomas de ZF** (Vacío, Adjunción, Potencia, Reemplazo, Separación) en cada universo.

### 4. Grandes Cardinales y Principio de Vopěnka
> Enlace directo: [**doc/REFERENCE_large_cardinals.md**](file:///e:/dropbox/github/lean4/Ordinals_Induction_Recursion/doc/REFERENCE_large_cardinals.md)

Este volumen documenta la jerarquía de Grandes Cardinales construida sobre los conjuntos materiales (`UnivCard`). Detalla la formalización del Puente de Grothendieck que conecta inaccesibles con universos de Dybjer, la caracterización de Cardinales de Mahlo y Medibles mediante topología y filtros sobre conjuntos materiales, y la cristalización final de la teoría de conjuntos con el Principio de Vopěnka aplicado a clases de estructuras relacionales.

### 5. Arquitectura y Dependencias de Módulos
> Enlace directo: [**doc/MODULE_DEPENDENCIES.md**](file:///e:/dropbox/github/lean4/Ordinals_Induction_Recursion/doc/MODULE_DEPENDENCIES.md)

Mapa técnico completo con diagramas Mermaid sobre cómo los módulos de `OrdinalsInductionRecursion` se interconectan. Especialmente diseñado para extraer módulos y reutilizarlos en otros proyectos matemáticos como la construcción de un marco para **TG + CAC + VP**.
