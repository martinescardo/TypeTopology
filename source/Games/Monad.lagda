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

module _ (T : Monad) where

 is-affine : Type
 is-affine = is-equiv (η T {𝟙})

 ext-const' : Type → Type₁
 ext-const' X = {Y : Type} (u : functor T Y)
              → ext T (λ (x : X) → u) ∼ λ (t : functor T X) → u

 ext-const : Type₁
 ext-const = {X : Type} → ext-const' X

 Kammars-Lemma₁ : Fun-Ext → is-affine → ext-const' 𝟙
 Kammars-Lemma₁ fe a {Y} u t = γ
  where
   f = λ (x : 𝟙) → u

   I : f ∘ inverse (η T {𝟙}) a ∼ ext T f
   I s = (f ∘ inverse (η T) a) s           ＝⟨ (unit T f (inverse (η T) a s))⁻¹ ⟩
         ext T f (η T (inverse (η T) a s)) ＝⟨ ap (ext T f) (inverses-are-sections (η T) a s) ⟩
         ext T f s                         ∎

   γ : ext T f t ＝ u
   γ = ext T f t                   ＝⟨ (ap (λ - → - t) (dfunext fe I))⁻¹ ⟩
       (f ∘ inverse (η T {𝟙}) a) t ＝⟨ refl ⟩
       u                           ∎

 Kammars-Lemma₂ : Fun-Ext → is-affine → ext-const
 Kammars-Lemma₂ fe a {X} {Y} u t = γ
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
   I = dfunext fe (Kammars-Lemma₁ fe a u)

   γ = ext T g t             ＝⟨ refl ⟩
       ext T (f ∘ k) t       ＝⟨ ap (λ - → ext T (- ∘ k) t) (I ⁻¹) ⟩
       ext T (ext T h ∘ k) t ＝⟨ assoc T h k t ⟩
       ext T h (ext T k t)   ＝⟨ ap (λ - → - (ext T k t)) I ⟩
       f (ext T k t)         ＝⟨ refl ⟩
       u                     ∎

 Kammars-Lemma-converse : ext-const
                        → is-affine
 Kammars-Lemma-converse ϕ = γ
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

record Algebra (T : Monad) (A : Type) : Type₁ where
 field
  structure-map : functor T A → A
  unit          : structure-map ∘ η T ∼ id
  assoc         : structure-map ∘ ext T (η T ∘ structure-map) ∼ structure-map ∘ ext T id

open Algebra public

\end{code}

TODO. Define monad morphism.
