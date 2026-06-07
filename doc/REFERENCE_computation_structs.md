# Estructuras de Computación y Cimientos Constructivos

Esta sección documenta el sustrato lógico de Lean 4 sobre el que operan nuestros modelos. Dado que Lean 4 se basa en la Teoría de Tipos Intensional (Calculus of Inductive Constructions), no poseemos de manera nativa la "Extensionalidad" (donde dos conjuntos con los mismos elementos son iguales). Todo debe construirse manualmente a través de la magia del Setoid.

## 1. Árboles de Ramificación (W-Types)
En el corazón de todo nuestro ecosistema se encuentran los `W-types` (Well-founded trees). Ya sea para Ordinales o Conjuntos, los objetos se definen siempre mediante un tipo de datos inductivo genérico con la forma:
```lean
inductive Tree : Type u
  | sup {α : Type u} (f : α → Tree) : Tree
```
En esta concepción, `α` es la "anchura" o ramificación del árbol, y `f` es la función que asigna un sub-árbol a cada rama. Un objeto matemático, por tanto, es la recolección suprema de todas sus ramas (elementos).

## 2. El Universo Predicativo de Tarski (`UCode`)
A la hora de crear árboles gigantescos (como Ordinales Inaccesibles), Lean nos exige subir el universo tipológico (`Type u`, `Type (u+1)`, etc). Esta torre de universos puede ser catastrófica para pruebas genéricas.

Para resolver esto sin salir de `Type 0`, implementamos un **Universo de Tarski**:
- Definimos un tipo puramente sintáctico `UCode` con códigos para constructores simples: `.unit`, `.nat`, `.sum`, `.arrow`.
- Definimos un decodificador `El : UCode → Type`.
- Restringimos las ramas del árbol exclusivamente a los tipos que se pueden construir en `UCode`.
```lean
inductive TPreOrd : Type
  | sup (c : UCode) (f : El c → TPreOrd) : TPreOrd
```
Esto encapsula infinitos "universos pequeños" matemáticos dentro de un único tipo base de Lean estrictamente constructivo y computable.

## 3. Familias Inductivas Indexadas de Dybjer (`UCodeFam`)
El gran defecto de `UCode` de Tarski es que carece de la característica principal de la Teoría de Tipos Dependientes: los verdaderos tipos $\Pi$ y $\Sigma$, porque requeriría "Inducción-Recursión" simultánea (que Lean 4 no soporta nativamente de la misma manera que Agda).

La joya de la corona del repositorio es el **Truco de Peter Dybjer**. Reemplazamos la función de decodificación separada `El` por una familia inductiva que aloja su propia decodificación *en el índice*:
```lean
inductive UCodeFam : Type → Type 1
  | unit : UCodeFam PUnit
  | sigma {A : Type} {B : A → Type} (a : UCodeFam A) (b : (x : A) → UCodeFam (B x)) : UCodeFam (Σ x, B x)
  | pi    {A : Type} {B : A → Type} (a : UCodeFam A) (b : (x : A) → UCodeFam (B x)) : UCodeFam ((x : A) → B x)
```
Esto nos da lo mejor de todos los mundos: Computabilidad estricta dentro de Lean 4, pero con una expresividad dependiente absoluta que permite encodear lógicas formidables.

## 4. El Manejo de Setoides
Dado que el tipo base (`Tree` o `PreOrd`) diferencia entre $2+3$ y $3+2$ por su forma estructural (intensionalidad), para hacer matemáticas reales equipamos a los árboles de una noción de Equivalencia ($\equiv$).
Demostramos `Equiv_refl`, `Equiv_symm` y `Equiv_trans` para la relación, instanciamos un `Setoid` (la interfaz estándar de Lean para clases de equivalencia), y creamos los objetos finales usando `Quotient Setoid`.
Esto sella matemáticamente los agujeros y permite un puente transparente con la teoría clásica.
