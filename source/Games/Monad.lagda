Martin Escardo, Paulo Oliva, 2023

(Strong, wild) monads on types.

TODO. We should also use this in FiniteHistoryDependentMonadic.

\begin{code}

{-# OPTIONS --safe --without-K #-}

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

tensor : (𝕋 : Monad) → {X : Type} {Y : X → Type}
       → functor 𝕋 X
       → ((x : X) → functor 𝕋 (Y x))
       → functor 𝕋 (Σ x ꞉ X , Y x)
tensor 𝕋 = _⊗_ 𝕋

syntax tensor 𝕋 t f = t ⊗[ 𝕋 ] f

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

If we want to call a monad T, then we can use the following module:

\begin{code}

module T-definitions (𝕋 : Monad) where

 T : Type → Type
 T = functor 𝕋

 ηᵀ : {X : Type} → X → T X
 ηᵀ = η 𝕋

 extᵀ : {X Y : Type} → (X → T Y) → T X → T Y
 extᵀ = ext 𝕋

 extᵀ-η : {X : Type} → extᵀ (ηᵀ {X}) ∼ 𝑖𝑑 (T X)
 extᵀ-η = ext-η 𝕋

 unitᵀ : {X Y : Type} (f : X → T Y) → extᵀ f ∘ ηᵀ ∼ f
 unitᵀ = unit 𝕋

 assocᵀ : {X Y Z : Type} (g : Y → T Z) (f : X → T Y)
        → extᵀ (extᵀ g ∘ f) ∼ extᵀ g ∘ extᵀ f
 assocᵀ = assoc 𝕋

 mapᵀ : {X Y : Type} → (X → Y) → T X → T Y
 mapᵀ = map 𝕋

 μᵀ : {X : Type} → T (T X) → T X
 μᵀ = μ 𝕋

 _⊗ᵀ_ : {X : Type} {Y : X → Type}
      → T X
      → ((x : X) → T (Y x))
      → T (Σ x ꞉ X , Y x)
 _⊗ᵀ_ = _⊗_ 𝕋

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

module _ (𝕋 : Monad) where

 open T-definitions 𝕋

 is-affine : Type
 is-affine = is-equiv (ηᵀ {𝟙})

 ext-const' : Type → Type₁
 ext-const' X = {Y : Type} (u : T Y)
              → extᵀ (λ (x : X) → u) ∼ λ (t : T X) → u

 ext-const : Type₁
 ext-const = {X : Type} → ext-const' X

 affine-gives-ext-const' : Fun-Ext → is-affine → ext-const' 𝟙
 affine-gives-ext-const' fe a {Y} u t = γ
  where
   f = λ (x : 𝟙) → u

   I : f ∘ inverse (ηᵀ {𝟙}) a ∼ extᵀ f
   I s = (f ∘ inverse ηᵀ a) s         ＝⟨ I₀ ⟩
         extᵀ f (ηᵀ (inverse ηᵀ a s)) ＝⟨ I₁ ⟩
         extᵀ f s                     ∎
    where
     I₀ = (unitᵀ f (inverse ηᵀ a s))⁻¹
     I₁ = ap (extᵀ f) (inverses-are-sections ηᵀ a s)

   γ : extᵀ f t ＝ u
   γ = extᵀ f t                   ＝⟨ (ap (λ - → - t) (dfunext fe I))⁻¹ ⟩
       (f ∘ inverse (ηᵀ {𝟙}) a) t ＝⟨ refl ⟩
       u                          ∎

 affine-gives-ext-const : Fun-Ext → is-affine → ext-const
 affine-gives-ext-const fe a {X} {Y} u t = γ
  where
   g : X → T Y
   g _ = u

   f : T 𝟙 → T Y
   f _ = u

   h : 𝟙 → T Y
   h _ = u

   k : X → T 𝟙
   k = ηᵀ {𝟙} ∘ unique-to-𝟙

   I : extᵀ h ＝ f
   I = dfunext fe (affine-gives-ext-const' fe a u)

   γ = extᵀ g t             ＝⟨ refl ⟩
       extᵀ (f ∘ k) t       ＝⟨ ap (λ - → extᵀ (- ∘ k) t) (I ⁻¹) ⟩
       extᵀ (extᵀ h ∘ k) t  ＝⟨ assocᵀ h k t ⟩
       extᵀ h (extᵀ k t)    ＝⟨ ap (λ - → - (extᵀ k t)) I ⟩
       f (extᵀ k t)         ＝⟨ refl ⟩
       u                    ∎

 ext-const-gives-affine : ext-const → is-affine
 ext-const-gives-affine ϕ = γ
  where
   η⁻¹ : T 𝟙 → 𝟙
   η⁻¹ t = ⋆

   I : η⁻¹ ∘ ηᵀ ∼ id
   I ⋆ = refl

   II : ηᵀ ∘ η⁻¹ ∼ id
   II t = (ηᵀ ∘ η⁻¹) t        ＝⟨ refl ⟩
          ηᵀ ⋆                ＝⟨ (ϕ {𝟙} (ηᵀ ⋆) t)⁻¹ ⟩
          extᵀ (λ x → ηᵀ ⋆) t ＝⟨ refl ⟩
          extᵀ ηᵀ t           ＝⟨ extᵀ-η t ⟩
          t                   ∎

   γ : is-equiv (ηᵀ {𝟙})
   γ = qinvs-are-equivs ηᵀ (η⁻¹ , I , II)

\end{code}

Monad algebras.

\begin{code}

record Algebra (𝕋 : Monad) (A : Type) : Type₁ where
 field
  structure-map : functor 𝕋 A → A
  unit          : structure-map ∘ η 𝕋 ∼ id
  assoc         : structure-map ∘ ext 𝕋 (η 𝕋 ∘ structure-map) ∼ structure-map ∘ ext 𝕋 id

open Algebra public

\end{code}

If we want to call an algebra (literally) α, we can used this module:

\begin{code}

module α-definitions
        (𝕋 : Monad)
        (R : Type)
        (𝓐 : Algebra 𝕋 R)
       where

 open T-definitions 𝕋

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
