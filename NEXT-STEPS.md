# Próximos Pasos (NEXT-STEPS)

Hoja de ruta táctica, focalizada en tareas atómicas e inmediatas para el desarrollo activo del repositorio.

## 🎯 Meta Actual: Completar ZFC en el Universo de Dybjer

Nuestra principal prioridad es utilizar el poder de los tipos dependientes (implementados mediante el truco de Peter Dybjer) para romper la barrera computacional en la que se atascó `TarskiSet`, logrando formular la Unión Universal y el Conjunto Potencia.

### Tareas Inmediatas

1. **Inicialización de `DybjerSet/Axioms.lean`**
   - [ ] Crear el esqueleto inicial `DybjerSet/Axioms.lean`.
   - [ ] Migrar/Re-implementar los axiomas elementales ya comprobados desde TarskiSet:
     - [ ] Conjunto Vacío (`empty`)
     - [ ] Adjunción (`insert`)
     - [ ] Pares no ordenados (`pair`) y Singletons (`singleton`)
     - [ ] Axioma del Infinito ($\omega$ computable)

2. **La Conquista de los Axiomas Complejos (ZFC Completo)**
   - [ ] **Unión ($\bigcup$):** Aprovechar `UCodeFam.sigma` para proyectar familias de árboles en un único conjunto unificado. Demostrar pertenencia equivalente.
   - [ ] **Conjunto Potencia ($\mathcal{P}$):** Aprovechar `UCodeFam.pi` y funciones en el meta-lenguaje para computar el árbol potencia.
   - [ ] **Reemplazo:** Formalizar el mapeo de árboles bajo relaciones funcionales indexadas.
   - [ ] **Separación:** Filtrar usando predicados decodificables del código interno.

3. **Inyecciones Finales (Embeddings)**
   - [ ] Formalizar la inyección `TarskiSet ↪ DybjerSet` (demostrando que Tarski es un submodelo estricto de Dybjer).
   - [ ] Formalizar la inyección `DybjerSet ↪ UnivSets`.

### Siguientes en Cola (Preparando Fase 4)
- **Directorio de Grandes Cardinales:** Una vez ZFC sea estable en Dybjer, crear el submódulo `OrdinalsInductionRecursion/LargeCardinals` e iniciar la formulación de cardinales regulares y el Filtro de los Cerrados No Acotados (CUBs).
