# Próximos Pasos (NEXT-STEPS)

Hoja de ruta táctica, focalizada en tareas atómicas e inmediatas para el desarrollo activo del repositorio.

## 🎯 Meta Actual: Completar ZFC en el Universo de Dybjer

Nuestra principal prioridad es utilizar el poder de los tipos dependientes (implementados mediante el truco de Peter Dybjer) para romper la barrera computacional en la que se atascó `TarskiSet`, logrando formular la Unión Universal y el Conjunto Potencia.

### Tareas Inmediatas

1. **Inicialización de `DybjerSet/Axioms.lean`**
   - [x] Crear el esqueleto inicial `DybjerSet/Axioms.lean`.
   - [x] Migrar/Re-implementar los axiomas elementales ya comprobados desde TarskiSet:
     - [x] Conjunto Vacío (`empty`)
     - [x] Adjunción (`insert`)
     - [x] Pares no ordenados (`pair`) y Singletons (`singleton`)
     - [x] Axioma del Infinito ($\omega$ computable)

2. **La Conquista de los Axiomas Complejos (ZFC Completo)**
   - [x] **Unión ($\bigcup$):** Aprovechar `UCodeFam.sigma` para proyectar familias de árboles en un único conjunto unificado. Demostrar pertenencia equivalente.
   - [x] **Conjunto Potencia ($\mathcal{P}$):** Aprovechar `UCodeFam.pi` y funciones en el meta-lenguaje para computar el árbol potencia.
   - [x] **Reemplazo:** Formalizar el mapeo de árboles bajo relaciones funcionales indexadas.
   - [x] **Separación:** Filtrar usando predicados decodificables del código interno.

3. **Inyecciones Finales (Embeddings)**
   - [x] Formalizar la inyección `TarskiSet ↪ DybjerSet` (usando el `Hack` de `tarski` en `UCodeFam` para evitar codificación Gödeliana).
   - [x] Formalizar la inyección `TarskiSet ↪ UnivSets`.

## 🚀 Fase 4: Grandes Cardinales (Large Cardinals)

Con ZFC firmemente asentado en DybjerSet, iniciamos la ascensión formal. Hemos decidido asentar los grandes cardinales analíticos sobre `UnivOrd` (la jerarquía de Grothendieck de Lean 4) debido a su amigabilidad con el polimorfismo y las lógicas de conjunto potencia sobre `Ordinal.{u}`.

1. **Infraestructura de Inaccesibilidad**
   - [x] Crear módulo `LargeCardinals/Inaccessible.lean` migrándolo desde `UnivOrd`.
   - [x] Formalizar la noción de Cardenal Inaccesible (`IsRegular`, `IsStrongLimit`, `IsUniverse`).
2. **Filtros y Cerrados No Acotados (CUBs)**
   - [x] Crear módulo `LargeCardinals/Filters.lean` (Estructura abstracta de Filtros).
   - [x] Crear módulo `LargeCardinals/CUB.lean` y formalizar `IsUnbounded`, `IsClosed`, e `IsCUB`.
   - [x] Construir la sucesión alternante explicita (`seq_bounded`) necesaria para la intersección de CUBs.
   - [ ] **TAREA ACTUAL:** Calcular analíticamente el supremo $\lambda = \sup_n s_n$, usar `IsRegular` para probar $\lambda < \kappa$ y deducir $\lambda \in C_1 \cap C_2$ (`CUB_inter_unbounded`).
3. **Cardinales de Mahlo**
   - [ ] Definir el filtro de Mahlo usando `IsCUB`.
   - [ ] Formalizar los cardinales de Mahlo.
