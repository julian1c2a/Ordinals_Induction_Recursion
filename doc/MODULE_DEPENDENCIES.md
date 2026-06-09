# Dependencias y Arquitectura de Módulos (OrdinalsInductionRecursion)

Este documento detalla la estructura del proyecto para que las partes relevantes puedan ser extraídas e integradas de forma independiente en otros repositorios, como el proyecto **TG + CAC + VP** o construcciones en Categorías.

## Resumen del Ecosistema

El proyecto se dividió históricamente en dos ramas paralelas ("Ord" para Ordinales puros y "Set" para extensiones tipo ZFC), multiplicadas por diferentes ontologías computacionales (Numerable, Universo, Tarski, Dybjer). 
El módulo fundamental para extraer toda la Lógica de Conjuntos Materiales (y sus Grandes Cardinales) es `UnivSets` y `UnivCard`.

## Diagrama de Dependencias Principal

El siguiente diagrama muestra el flujo de dependencias lógicas y de importación entre los paquetes de nivel superior. Las flechas (`-->`) indican que un módulo depende (o es una abstracción superior) de otro.

```mermaid
flowchart TD
    subgraph Core Computacional
    UCode[Universos de Tarski UCode]
    UCodeFam[Universos Dybjer UCodeFam]
    end

    subgraph Ordinales Básicos
    CountableOrd[CountableOrd<br>Supremos en Nat]
    UnivOrd[UnivOrd<br>Supremos genéricos en Type u]
    end

    subgraph Conjuntos Materiales Extensionales
    UnivSets[UnivSets<br>Conjuntos vía Aczel sobre Type u]
    TarskiSet[TarskiSet<br>Conjuntos sobre UCode]
    DybjerSet[DybjerSet<br>Conjuntos sobre UCodeFam]
    end

    subgraph Grandes Cardinales (El Techo ZFC+TG+VP)
    UnivCard[UnivCard<br>Teoría Superior sobre UnivSets]
    end

    %% Relaciones
    CountableOrd --> UnivOrd
    UCode --> TarskiSet
    UCodeFam --> DybjerSet
    
    %% Mapeos Constructivos (Embeddings)
    TarskiSet -.->|Embedding a| DybjerSet
    DybjerSet -.->|Embedding a| UnivSets
    
    %% Base de Grandes Cardinales
    UnivOrd --> UnivSets
    UnivSets --> UnivCard
    
    classDef core fill:#f9f,stroke:#333,stroke-width:2px;
    classDef card fill:#ff9,stroke:#333,stroke-width:2px;
    class UCode,UCodeFam core;
    class UnivCard card;
```

---

## Desglose por Paquetes para Reutilización

Si deseas instanciar un nuevo proyecto basado en **TG + CAC + VP**, no necesitas importar todos los experimentos constructivos (Tarski/Dybjer), sino únicamente las ramas universales:

### 1. `UnivSets` (La base extensional de Conjuntos)
- **`Tree.lean`**: Define los árboles de Brouwer universales.
- **`Axioms.lean`**: Implementa los fundamentos de Aczel: Equipotencia Estructural, Conjunto Vacío, Par, Unión, Partes. **(Aquí reside la base de USet)**.
- **Recomendación para Extracción**: Copiar `Tree.lean` y `Axioms.lean` es suficiente para tener un Universo Material $V$ funcional en Lean 4.

### 2. `UnivCard` (La corona de los Grandes Cardinales)
Para poder afirmar que el universo sobre el que operas en Categorías cumple **Tarski-Grothendieck** y **Vopěnka**, debes extraer la infraestructura desarrollada aquí:
- **`Equipollence.lean` & `Cardinal.lean`**: Funciones inyectivas/biyectivas materiales y asignación cardinal.
- **`Topology.lean` & `CUB.lean`**: Límites, puntos de acumulación, y estacionariedad.
- **`Inaccessible.lean` & `GrothendieckBridge.lean`**: El corazón de TG. El puente de Grothendieck equipara la Inaccesibilidad Fuerte con la noción categórica de Universo ($V_\kappa$).
- **`Mahlo.lean` & `Measurable.lean`**: Extensiones fuertes vía filtros.
- **`Structure.lean` & `Vopenka.lean`**: Definición material de estructuras y la aserción de que ninguna clase propia carece de inmersiones elementales.

### 3. Evitar el Equipaje Computacional (Opcional)
Los módulos de `TarskiOrd`, `TarskiSet`, `DybjerOrd` y `DybjerSet` fueron pruebas de concepto vitales para entender *cómo y por qué* ciertos axiomas (como Potencia) fallaban sin tipos dependientes. 
- En tu proyecto puro orientado a matemáticas ordinarias (Categorías), **puedes descartar por completo las ramas de Tarski y Dybjer**, ya que `UnivSets` asume el Axioma de Elección y Extensionalidad de Lean por defecto, brindándote la comodidad máxima para operar matemáticamente.

---

> **Resumen de Extracción para TG+CAC+VP:** 
> Migrar `UnivSets` y `UnivCard` a tu nuevo repositorio es exactamente lo que cimentará la Teoría de Conjuntos Materiales (con Universos de Grothendieck explícitos y Principio de Vopěnka), lista para alojar la jerarquía de `Obj` y `Hom` propia de la Teoría de Categorías.
