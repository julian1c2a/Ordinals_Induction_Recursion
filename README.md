# Ordinals, Induction & Recursion: Skeletons for Aczel Set Theory

Este proyecto sirve como un entorno "sandbox" o campo de pruebas para la exploración y estabilización de esqueletos estructurales fundacionales. El objetivo principal es pulir y purificar estas estructuras matemáticas (ordinales, inducción, recursión transfinita, universos) para que puedan ser directamente integradas en proyectos más grandes, como el proyecto **AczelSetTheory**.

Actualmente, el proyecto contiene el código base para cuatro enfoques o "esqueletos" distintos, todos compilando en **Lean 4** sin ningún `sorry` (0 advertencias):

## 1. `CountableOrd` (Esqueleto Numerable)
- **Propósito**: Explorar los ordinales numerables usando árboles de Brouwer limitados.
- **Estructura**: El constructor de supremos (`sup`) está restringido al tipo índice `Nat` (es decir, cada nodo límite tiene una cantidad numerable de ramas).
- **Logros**: Contiene demostraciones purificadas de tricotomía, pertenencia y equivalencia extensional para ordinales numerables.

## 2. `UnivOrd` (Esqueleto Universal Clásico)
- **Propósito**: Generalizar los árboles de Brouwer para soportar supremos sobre cualquier `Type u` del universo de Lean.
- **Estructura**: Representa los ordinales de Von Neumann de forma genérica.
- **Logros**:
  - **Mostowski Collapse (`Isomorphism.lean`)**: Implementación libre de errores del colapso de subconjuntos bien ordenados usando el axioma de Mostowski.
  - **Asignación Cardinal (`Cardinals.lean`)**: Implementación extensional estricta de la equipotencia, número de Hartogs y la función límite $\aleph$ utilizando recursión transfinita explícita (`limitRecOn`).
  - **Lifting (`Lift.lean`)**: Ascenso de ordinales entre niveles de universos de Lean (`Type u` → `Type (max u v)`).
  - **Universos Inaccesibles (`Inaccessible.lean`)**: Postulación formal de los **Universos de Grothendieck** internamente, permitiendo iteraciones límite ($\Omega_\alpha$) vía axiomática fuerte.

## 3. `TarskiOrd` (Esqueleto Constructivo de Universos Internos)
- **Propósito**: Resolver de forma constructiva el problema de iterar universos de Grothendieck sin chocar con la jerarquía predicativa `Sort u` de Lean.
- **Estructura**: 
  - Define un Universo a la Tarski (`UCode`) con tipos simples y un decodificador (`El`).
  - El árbol de Brouwer (`TPreOrd`) limita sus supremos **únicamente a tipos decodificables** de este código interno.
- **Logros**:
  - Replicación exitosa de toda el álgebra extensional (`Subset`, `Mem`, `Equiv`, `Setoid`) sobre los códigos de Tarski sin usar `sorry`.
  - Construcción de los tipos límite $\omega$ y del **Primer Universo de Grothendieck** explícito ($\Omega_0$) puramente computables.

## 4. `UnivSets` (Esqueleto Aczel)
- **Propósito**: Implementación análoga para conjuntos en lugar de ordinales.
- **Estructura**: Usa `W-types` (tipos de ramificación general) para modelar conjuntos inductivos a la Aczel.
- **Logros**: Se cuenta con demostraciones básicas de pertenencia estructural e inmersión (`liftTree`).

---

## 🛠 Estado del Proyecto
* **Sorries / Axiomas pendientes**: 0 (Cero). Todas las demostraciones de equivalencia y colapso estructural han sido probadas satisfactoriamente.
* **Uso Futuro**: Estos módulos están diseñados para copiarse o integrarse como módulos satélite en los proyectos destino. Se recomienda usar la base semántica basada en cocientes (`Ordinal` o `TOrdinal`) para evitar los "infiernos de inducción" asociados a los índices crudos de `PreOrd`.