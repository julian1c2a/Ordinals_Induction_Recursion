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

### Fase III: Teoría de Modelos Interna e Inmersiones
Para ir más allá de los débilmente compactos, Lean necesita "entender" la Lógica de Primer Orden para poder hablar de Verdad y Preservación de Modelos.

4. **`ModelTheory/Syntax.lean` y `ModelTheory/Semantics.lean`**
   - [x] *Atajo:* Importar la dependencia `FOL` externa.
   - [x] Crear `ModelTheory/Universe.lean` instanciando el universo de Dybjer como modelo semántico de ZFC.

5. **`Embeddings.lean`**
   - [x] **Inmersiones Elementales ($j: V \to M$):** Funciones inyectivas entre la clase universo $V$ (basada en `DybjerSet`) y una subclase $M$, tal que preservan toda la verdad lógica.

## 🚀 Fase 4: Grandes Cardinales (Large Cardinals)

Con ZFC firmemente asentado en DybjerSet, iniciamos la ascensión formal. Hemos decidido asentar los grandes cardinales analíticos sobre `UnivOrd` (la jerarquía de Grothendieck de Lean 4) debido a su amigabilidad con el polimorfismo y las lógicas de conjunto potencia sobre `Ordinal.{u}`.

1. **Infraestructura de Inaccesibilidad**
   - [x] Crear módulo `LargeCardinals/Inaccessible.lean` migrándolo desde `UnivOrd`.
   - [x] Formalizar la noción de Cardenal Inaccesible (`IsRegular`, `IsStrongLimit`, `IsUniverse`).
2. **Filtros y Cerrados No Acotados (CUBs)**
   - [x] Crear módulo `LargeCardinals/Filters.lean` (Estructura abstracta de Filtros).
   - [x] Crear módulo `LargeCardinals/CUB.lean` y formalizar `IsUnbounded`, `IsClosed`, e `IsCUB`.
   - [x] Construir la sucesión alternante explicita (`seq_bounded`) necesaria para la intersección de CUBs.
   - [x] **TAREA ACTUAL:** Calcular analíticamente el supremo $\lambda = \sup_n s_n$, usar `IsRegular` para probar $\lambda < \kappa$ y deducir $\lambda \in C_1 \cap C_2$ (`CUB_inter_unbounded`).
3. **Cardinales de Mahlo**
   - [x] Definir el filtro CUB y el filtro de Mahlo usando `IsCUB`.
   - [x] Formalizar la noción de Conjuntos Estacionarios y Cardinales de Mahlo.

4. **Cardinales Fuertes y Medibles**
   - [x] Definición estructural: Existencia de un ultrafiltro no principal $\kappa$-completo.
   - [x] Definición del punto crítico `crit` de una inmersión $j$.
   - [x] Formalización (axiomatizada) del Teorema de Scott: Equivalencia entre Inmersiones Elementales y Medibilidad.

### Fase V: El Principio de Vopěnka

Llegamos a la cúspide de los grandes cardinales, en la cual el universo impone orden en el multiverso de las estructuras matemáticas.

5. **`Supercompact.lean`**
   - [x] Definir la clausura bajo sucesiones para universos $M$.
   - [x] Formalizar cardinales $\lambda$-supercompactos y Supercompactos.

6. **`ModelTheory/Structures.lean` y `Vopenka.lean`**
   - [x] Estructuras Relacionales e Inmersiones Estructurales.
   - [x] Concepto de Clase Propia.
   - [x] **El Principio de Vopěnka**: Ninguna clase propia de estructuras escapa a una inmersión elemental entre sus miembros.

### 🎉 ¡ROADMAP DE ZFC COMPLETADO! 🎉
El repositorio ahora alberga formalmente desde el constructivismo extensional de Aczel hasta la cima de la jerarquía de grandes cardinales.

---

### Fase VI: Fundamentación Constructiva de MK⁺ sobre `UnivSets` (COMPLETADA)

Hemos abandonado los axiomas huérfanos de MK⁺. El objetivo fue transformar la teoría de Morse-Kelley en un modelo constructivo probado sobre los universos extensionales puros de Aczel (`UnivSets.USet`).

7. **Transformación de MK⁺ (De Axiomas a Teoremas)**
   - [x] Redefinir ontológicamente `Class := UnivSets.USet → Prop`.
   - [x] Reformular el núcleo de `MKplusCACAxioms.lean` convirtiendo todos los axiomas `axiom` en `theorem` y demostrando sus postulados constructivamente sobre los árboles `W` de Aczel.
   - [x] Reestructurar Vopěnka (`Vopenka.lean`) y Tarski (`Tarski.lean`) para operar en este modelo constructivo impredicativo de Clases.

### Fase VII: La Gran Unificación (Tarski-Grothendieck Arquitectónico y Vopěnka en `UnivCard`) (COMPLETADA)

El momento cúspide donde los tres mundos convergen: Lean 4, Constructivismo Extensional (ZFC), Teoría de Clases (MK), y Grandes Cardinales. Todo unificado sobre la base material de `USet`.

8. **Universo de Grothendieck y El Principio de Vopěnka**
   - [x] Formalizar e implementar la inmersión computacional `DSet ↪ UnivSets.USet`. (Completado en `EmbedDybjer.lean`).
   - [x] **Puente de Grothendieck (`UnivCard/GrothendieckBridge.lean`)**: Caracterización axiomática del universo de Grothendieck y su equivalencia con los cardinales fuertemente inaccesibles.
   - [x] **Principio de Vopěnka (`UnivCard/Vopenka.lean`)**: Cristalización formal del Principio de Vopěnka sobre clases propias materiales de estructuras relacionales.
   - [x] **Teorema Supremo**: Todo el proyecto alcanza el nivel lógico de **TG + VP**, sirviendo como base teórica monolítica para el arranque de `ZfcSetTheory` y la futura Teoría de Categorías.
