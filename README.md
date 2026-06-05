# Ordinals, Induction & Recursion: Skeletons for Aczel Set Theory

Este proyecto sirve como un entorno "sandbox" o campo de pruebas para la exploración y estabilización de esqueletos estructurales fundacionales. El objetivo principal es pulir y purificar estas estructuras matemáticas (ordinales, inducción, recursión transfinita, universos) para que puedan ser directamente integradas en proyectos más grandes, como el proyecto **AczelSetTheory**.

Actualmente, el proyecto contiene el código base de cuatro pilares fundacionales, todos compilando en **Lean 4** sin ningún `sorry` (cero advertencias), cada uno dividido en dos vertientes (**Ord** para ordinales transitivos nativos y **Set** para conjuntos extensionales de Aczel):

## 1. Familias Numerables (`CountableOrd` / `CountableSets`)
- **Propósito**: Explorar los ordinales y conjuntos numerables usando árboles de Brouwer limitados.
- **Estructura**: El constructor de supremos (`sup`) está restringido al tipo índice `Nat` (es decir, cada nodo límite tiene una cantidad numerable de ramas).
- **Logros**: Contiene demostraciones purificadas de tricotomía, pertenencia y equivalencia extensional.

## 2. Familias Universales (`UnivOrd` / `UnivSets`)
- **Propósito**: Generalizar los árboles de Brouwer para soportar supremos sobre cualquier `Type u` del universo de Lean.
- **Estructura**: Representa los ordinales y conjuntos de Von Neumann de forma genérica usando W-types y el axioma de elección de Lean.
- **Logros**:
  - **Mostowski Collapse (`Isomorphism.lean`)**: Implementación del colapso de subconjuntos bien ordenados.
  - **Asignación Cardinal (`Cardinals.lean`)**: Implementación de la equipotencia, número de Hartogs y $\aleph$.
  - **Lifting (`Lift.lean`)**: Ascenso de ordinales entre niveles de universos de Lean (`Type u` → `Type (max u v)`).
  - **Universos Inaccesibles (`Inaccessible.lean`)**: Postulación formal de los **Universos de Grothendieck** internamente.

## 3. Universo de Tarski (`TarskiOrd` / `TarskiSet`)
- **Propósito**: Resolver de forma constructiva el problema de iterar universos de Grothendieck sin chocar con la jerarquía predicativa `Sort u` de Lean.
- **Estructura**: 
  - Define un Universo a la Tarski (`UCode`) con tipos simples (unit, nat, sum, arrow) y un decodificador (`El`).
  - Los árboles limitan sus supremos **únicamente a tipos decodificables** de este código interno.
- **Logros**:
  - Replicación exitosa de toda el álgebra extensional sobre los códigos de Tarski sin usar `sorry`.
  - Construcción de los tipos límite $\omega$ y del **Primer Universo de Grothendieck** explícito ($\Omega_0$) puramente computables.
  - Recursión e Inducción transfinita computable.

## 4. Universo de Dybjer (`DybjerOrd` / `DybjerSet`)
- **Propósito**: Expandir Tarski para incluir verdaderos **tipos dependientes** (Pi y Sigma) manteniendo la computabilidad estricta.
- **Estructura**: Usa el **Truco de Peter Dybjer** (Familias Inductivas Indexadas) `UCodeFam : Type → Type 1`.
- **Logros**:
  - Inducción y Recursión Transfinita basadas en Minimización y Fundamentación (`WellFounded.fix`).
  - Aritmética Cardinal completa (Hartogs).
  - Colapso de Mostowski constructivo sobre cualquier relación bien fundada parametrizada.
  - Jerarquía de los Alephs ($\aleph_\alpha$) construida estructuralmente.

---

## 🛠 Estado del Proyecto
* **Sorries / Axiomas pendientes**: 0 (Cero). Todas las demostraciones de equivalencia y colapso estructural han sido probadas satisfactoriamente.
* **Uso Futuro**: Estos módulos están diseñados para copiarse o integrarse como módulos satélite en los proyectos destino. Se recomienda usar la base semántica basada en cocientes (`Ordinal` o `TOrdinal`) para evitar los "infiernos de inducción" asociados a los índices crudos de los árboles.