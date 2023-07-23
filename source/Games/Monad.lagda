Martin Escardo, Paulo Oliva, 2023

(Strong, wild) monads on types.

TODO. We should also use this in FiniteHistoryDependentMonadic.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.Equiv
open import UF.FunExt

module Games.Monad where

record Monad : Type₁ where
 constructor
  monad
 field
  functor : Type → Type
  η       : {X : Type} → X → functor X
  ext     : {X Y : Type} → (X → functor Y) → functor X → functor Y
  ext-η   : {X : Set} → ext (η {X}) ∼ 𝑖𝑑 (functor X)
  unit    : {X Y : Type} (f : X → functor Y) (x : X) → ext f (η x) ＝ f x
  assoc   : {X Y Z : Type} (g : Y → functor Z) (f : X → functor Y) (t : functor X)
          → ext (λ x → ext g (f x)) t ＝ ext g (ext f t)

 map : {X Y : Type} → (X → Y) → functor X → functor Y
 map f = ext (η ∘ f)

 μ : {X : Type} → functor (functor X) → functor X
 μ = ext id

 _⊗_ : {X : Type} {Y : X → Type}
     → functor X
     → ((x : X) → functor (Y x))
     → functor (Σ x ꞉ X , Y x)
 t ⊗ f = ext (λ x → map (λ y → x , y) (f x)) t

open Monad public

tensor : (𝓣 : Monad) → {X : Type} {Y : X → Type}
       → functor 𝓣 X
       → ((x : X) → functor 𝓣 (Y x))
       → functor 𝓣 (Σ x ꞉ X , Y x)
tensor 𝓣 = _⊗_ 𝓣

syntax tensor 𝓣 t f = t ⊗[ 𝓣 ] f

𝕀𝕕 : Monad
𝕀𝕕 = record {
      functor = id ;
      η       = id ;
      ext     = id ;
      ext-η   = λ x → refl ;
      unit    = λ f x → refl ;
      assoc   = λ g f x → refl
     }

𝕀𝕕⊗ : {X : Type} {Y : X → Type}
      (x : X)
      (f : (x : X) → (Y x))
    → x ⊗[ 𝕀𝕕 ] f ＝ x , f x
𝕀𝕕⊗ x f = refl

\end{code}

We we want to call a monad (literally) T, then we can use the
following module:

\begin{code}

module T-definitions (𝓣 : Monad) where

 T : Type → Type
 T = functor 𝓣

 ηᵀ : {X : Type} → X → T X
 ηᵀ = η 𝓣

 extᵀ : {X Y : Type} → (X → T Y) → T X → T Y
 extᵀ = ext 𝓣

 extᵀ-η : {X : Type} → extᵀ (ηᵀ {X}) ∼ 𝑖𝑑 (T X)
 extᵀ-η = ext-η 𝓣

 unitᵀ : {X Y : Type} (f : X → T Y) → extᵀ f ∘ ηᵀ ∼ f
 unitᵀ = unit 𝓣

 assocᵀ : {X Y Z : Type} (g : Y → T Z) (f : X → T Y)
        → extᵀ (extᵀ g ∘ f) ∼ extᵀ g ∘ extᵀ f
 assocᵀ = assoc 𝓣

 mapᵀ : {X Y : Type} → (X → Y) → T X → T Y
 mapᵀ = map 𝓣

 μᵀ : {X : Type} → T (T X) → T X
 μᵀ = μ 𝓣

 _⊗ᵀ_ : {X : Type} {Y : X → Type}
      → T X
      → ((x : X) → T (Y x))
      → T (Σ x ꞉ X , Y x)
 _⊗ᵀ_ = _⊗_ 𝓣

\end{code}

For some results, we need our monad to satisfy the condition
extᵀ-const defined below. Ohad Kammar pointed out to us that this
condition is equivalent to the monad being affine. We include his
proof here.

References given by Ohad Kammar and Alex Simpson:

[1] Anders Kock, Bilinearity and Cartesian closed monads,
Math. Stand. 29 (1971) 161-174.
https://users-math.au.dk/kock/BCCM.pdf

[2]
https://www.denotational.co.uk/publications/kammar-plotkin-algebraic-foundations-for-effect-dependent-optimisations.pdf

[3] https://www.denotational.co.uk/publications/kammar-ohad-thesis.pdf

[4] Gavin Wraith mentions affine theories in his lecture notes form
1969 (Prop. 3.5 here:
https://www.denotational.co.uk/scans/wraith-algebraic-theories.pdf)

[5] Bart Jacobs' "Semantics of weakening and contraction".
https://doi.org/10.1016/0168-0072(94)90020-5

\begin{code}

module _ (T : Monad) where

 is-affine : Type
 is-affine = is-equiv (η T {𝟙})

 ext-const' : Type → Type₁
 ext-const' X = {Y : Type} (u : functor T Y)
              → ext T (λ (x : X) → u) ∼ λ (t : functor T X) → u

 ext-const : Type₁
 ext-const = {X : Type} → ext-const' X

 affine-gives-ext-const' : Fun-Ext → is-affine → ext-const' 𝟙
 affine-gives-ext-const' fe a {Y} u t = γ
  where
   f = λ (x : 𝟙) → u

   I : f ∘ inverse (η T {𝟙}) a ∼ ext T f
   I s = (f ∘ inverse (η T) a) s           ＝⟨ I₀ ⟩
         ext T f (η T (inverse (η T) a s)) ＝⟨ I₁ ⟩
         ext T f s                         ∎
    where
     I₀ = (unit T f (inverse (η T) a s))⁻¹
     I₁ = ap (ext T f) (inverses-are-sections (η T) a s)

   γ : ext T f t ＝ u
   γ = ext T f t                   ＝⟨ (ap (λ - → - t) (dfunext fe I))⁻¹ ⟩
       (f ∘ inverse (η T {𝟙}) a) t ＝⟨ refl ⟩
       u                           ∎

 affine-gives-ext-const : Fun-Ext → is-affine → ext-const
 affine-gives-ext-const fe a {X} {Y} u t = γ
  where
   g : X → functor T Y
   g _ = u

   f : functor T 𝟙 → functor T Y
   f _ = u

   h : 𝟙 → functor T Y
   h _ = u

   k : X → functor T 𝟙
   k = η T {𝟙} ∘ unique-to-𝟙

   I : ext T h ＝ f
   I = dfunext fe (affine-gives-ext-const' fe a u)

   γ = ext T g t             ＝⟨ refl ⟩
       ext T (f ∘ k) t       ＝⟨ ap (λ - → ext T (- ∘ k) t) (I ⁻¹) ⟩
       ext T (ext T h ∘ k) t ＝⟨ assoc T h k t ⟩
       ext T h (ext T k t)   ＝⟨ ap (λ - → - (ext T k t)) I ⟩
       f (ext T k t)         ＝⟨ refl ⟩
       u                     ∎

 ext-const-gives-affine : ext-const → is-affine
 ext-const-gives-affine ϕ = γ
  where
   η⁻¹ : functor T 𝟙 → 𝟙
   η⁻¹ t = ⋆

   I : η⁻¹ ∘ η T ∼ id
   I ⋆ = refl

   II : η T ∘ η⁻¹ ∼ id
   II t = (η T ∘ η⁻¹) t         ＝⟨ refl ⟩
          η T ⋆                 ＝⟨ (ϕ {𝟙} (η T ⋆) t)⁻¹ ⟩
          ext T (λ x → η T ⋆) t ＝⟨ refl ⟩
          ext T (η T) t         ＝⟨ ext-η T t ⟩
          t                     ∎

   γ : is-equiv (η T {𝟙})
   γ = qinvs-are-equivs (η T) (η⁻¹ , I , II)

\end{code}

Monad algebras.

\begin{code}

record Algebra (T : Monad) (A : Type) : Type₁ where
 field
  structure-map : functor T A → A
  unit          : structure-map ∘ η T ∼ id
  assoc         : structure-map ∘ ext T (η T ∘ structure-map) ∼ structure-map ∘ ext T id

open Algebra public

\end{code}

If we want to call an algebra (literally) α, we can used this module:

\begin{code}

module α-definitions
        (𝓣 : Monad)
        (R : Type)
        (𝓐 : Algebra 𝓣 R)
       where

 open T-definitions 𝓣

 α : T R → R
 α = structure-map 𝓐

 α-unitᵀ : α ∘ ηᵀ ∼ id
 α-unitᵀ = unit 𝓐

 α-assocᵀ : α ∘ extᵀ (ηᵀ ∘ α) ∼ α ∘ extᵀ id
 α-assocᵀ = assoc 𝓐

 α-extᵀ : {A : Type} → (A → R) → T A → R
 α-extᵀ q = α ∘ mapᵀ q

 α-curryᵀ : {X : Type} {Y : X → Type}
          → ((Σ x ꞉ X , Y x) → R)
          → (x : X) → T (Y x) → R
 α-curryᵀ q x = α-extᵀ (curry q x)

\end{code}

TODO. Define monad morphism (for example overline is a monad morphism
from J to K).
