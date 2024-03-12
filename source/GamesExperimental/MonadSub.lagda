Martin Escardo, Paulo Oliva, March 2024

(Strong, wild) universe-polymorphic monads on types equipped with data or properties.

We use ℓ : Universe → Universe to control the functor part. E.g. for
the powerset monad, as the powerset of a type in 𝓤 lands in the next
universe 𝓤⁺, we take ℓ 𝓤 = 𝓤⁺, but for the list monad we take
ℓ 𝓤 = 𝓤. For the J and K monads with answer type R : 𝓦,
we have ℓ 𝓤 = 𝓤 ⊔ 𝓦.

It is the use of ℓ below that requires the flag --no-level-universe.
Perhaps we will instead make ℓ into a parameter to avoid that.

\begin{code}

{-# OPTIONS --safe --without-K --no-level-universe #-}

open import MLTT.Spartan
open import UF.Equiv
open import UF.FunExt

module GamesExperimental.MonadSub
        (suitable : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇ )
        (𝟙-is-suitable : {𝓤 : Universe} → suitable (𝟙 {𝓤}))
        (Σ-is-suitable
           : {𝓤 𝓥 : Universe}
             (𝓧 : Σ X ꞉ 𝓤 ̇ , suitable X)
             (𝓨 : pr₁ 𝓧 → Σ Y ꞉ 𝓥 ̇ , suitable Y)
           → suitable (Σ x ꞉ pr₁ 𝓧 , pr₁ (𝓨 x)))
       where

𝕊 : (𝓤 : Universe) → 𝓤 ⁺ ̇
𝕊 𝓤 = Σ X ꞉ 𝓤 ̇ , suitable X

⟨_⟩ : {𝓤 : Universe} → 𝕊 𝓤 → 𝓤 ̇
⟨ X , s ⟩ = X

structure : {𝓤 : Universe} → (𝓧 : 𝕊 𝓤) → suitable ⟨ 𝓧 ⟩
structure (X , s) = s

𝟙ₛ : {𝓤 : Universe} → 𝕊 𝓤
𝟙ₛ = 𝟙 , 𝟙-is-suitable

Sigmaₛ : {𝓤 𝓥 : Universe} (𝓧 : 𝕊 𝓤) (𝓨 : ⟨ 𝓧 ⟩ → 𝕊 𝓥) → 𝕊 (𝓤 ⊔ 𝓥)
Sigmaₛ {𝓤} {𝓥} 𝓧 𝓨 = (Σ x ꞉ ⟨ 𝓧 ⟩ , ⟨ 𝓨 x ⟩) , Σ-is-suitable 𝓧 𝓨

syntax Sigmaₛ 𝓧 (λ x → 𝓨) = Σₛ x ꞉ 𝓧 , 𝓨

infixr -1 Sigmaₛ

record Monad : 𝓤ω where
 constructor
  monad
 field
  ℓ       : Universe → Universe
  functor : {𝓤 : Universe} → 𝕊 𝓤 → 𝕊 (ℓ 𝓤)
  η       : {𝓤 : Universe} {𝓧 : 𝕊 𝓤} → ⟨ 𝓧 ⟩ → ⟨ functor 𝓧 ⟩
  ext     : {𝓤 𝓥 : Universe} {𝓧 : 𝕊 𝓤} {𝓨 : 𝕊 𝓥} → (⟨ 𝓧 ⟩ → ⟨ functor 𝓨 ⟩) → ⟨ functor 𝓧 ⟩ → ⟨ functor 𝓨 ⟩
  ext-η   : {𝓤 : Universe} {𝓧 : 𝕊 𝓤} → ext (η {𝓤} {𝓧}) ∼ 𝑖𝑑 (⟨ functor 𝓧 ⟩)
  unit    : {𝓤 𝓥 : Universe} {𝓧 : 𝕊 𝓤} {𝓨 : 𝕊 𝓥} (f : ⟨ 𝓧 ⟩ → ⟨ functor 𝓨 ⟩) (x : ⟨ 𝓧 ⟩)
          → ext {𝓤} {𝓥} {𝓧} {𝓨} f (η x) ＝ f x
  assoc   : {𝓤 𝓥 𝓦 : Universe}
            {𝓧 : 𝕊 𝓤} {𝓨 : 𝕊 𝓥} {𝓩 : 𝕊 𝓦}
            (g : ⟨ 𝓨 ⟩ → ⟨ functor 𝓩 ⟩) (f : ⟨ 𝓧 ⟩ → ⟨ functor 𝓨 ⟩) (t : ⟨ functor 𝓧 ⟩)
          → ext (λ x → ext g (f x)) t ＝ ext g (ext f t)

 map : {𝓧 : 𝕊 𝓤} {𝓨 : 𝕊 𝓥} → (⟨ 𝓧 ⟩ → ⟨ 𝓨 ⟩) → ⟨ functor 𝓧 ⟩ → ⟨ functor 𝓨 ⟩
 map f = ext (η ∘ f)

 μ : {𝓧 : 𝕊 𝓤} →  ⟨ functor (functor 𝓧) ⟩ → ⟨ functor 𝓧 ⟩
 μ = ext id

 _⊗_ : {𝓧 : 𝕊 𝓤} {𝓨 : ⟨ 𝓧 ⟩ → 𝕊 𝓥}
     → ⟨ functor 𝓧 ⟩
     → ((x : ⟨ 𝓧 ⟩) → ⟨ functor (𝓨 x) ⟩)
     → ⟨ functor (Σₛ x ꞉ 𝓧 , 𝓨 x) ⟩
 t ⊗ f = ext (λ x → map (λ y → x , y) (f x)) t

open Monad public

tensor : (𝕋 : Monad)
         {𝓧 : 𝕊 𝓤} {𝓨 : ⟨ 𝓧 ⟩ → 𝕊 𝓥}
       → ⟨ functor 𝕋 𝓧 ⟩
       → ((x : ⟨ 𝓧 ⟩) → ⟨ functor 𝕋 (𝓨 x) ⟩)
       → ⟨ functor 𝕋 (Σₛ x ꞉ 𝓧 , 𝓨 x) ⟩
tensor 𝕋 = _⊗_ 𝕋

syntax tensor 𝕋 t f = t ⊗[ 𝕋 ] f

𝕀𝕕 : Monad
𝕀𝕕 = record {
      ℓ       = id ;
      functor = id ;
      η       = id ;
      ext     = id ;
      ext-η   = λ x → refl ;
      unit    = λ f x → refl ;
      assoc   = λ g f x → refl
     }

𝕀𝕕⊗ : {𝓧 : 𝕊 𝓤} {𝓨 : ⟨ 𝓧 ⟩ → 𝕊 𝓥}
      (x : ⟨ 𝓧 ⟩)
      (f : (x : ⟨ 𝓧 ⟩) → ⟨ 𝓨  x ⟩)
    → tensor 𝕀𝕕 {𝓧} {𝓨} x f ＝ (x , f x)
𝕀𝕕⊗ x f = refl

\end{code}

If we want to call a monad T, then we can use the following module:

\begin{code}

module T-definitions (𝕋 : Monad) where

 T : {𝓤 : Universe} → 𝕊 𝓤 → 𝕊 (ℓ 𝕋 𝓤)
 T {𝓤} = functor 𝕋

 ηᵀ : {𝓧 : 𝕊 𝓤} → ⟨ 𝓧 ⟩ → ⟨ T 𝓧 ⟩
 ηᵀ = η 𝕋

 extᵀ : {𝓧 : 𝕊 𝓤} {𝓨 : 𝕊 𝓥} → (⟨ 𝓧 ⟩ → ⟨ T 𝓨 ⟩) → ⟨ T 𝓧 ⟩ → ⟨ T 𝓨 ⟩
 extᵀ = ext 𝕋

 extᵀ-η : {𝓧 : 𝕊 𝓤} → extᵀ (ηᵀ {𝓤} {𝓧}) ∼ 𝑖𝑑 (⟨ T 𝓧 ⟩)
 extᵀ-η = ext-η 𝕋

 unitᵀ : {𝓧 : 𝕊 𝓤} {𝓨 : 𝕊 𝓥} (f : ⟨ 𝓧 ⟩ → ⟨ T 𝓨 ⟩) → extᵀ {𝓤} {𝓥} {𝓧} {𝓨} f ∘ ηᵀ ∼ f
 unitᵀ = unit 𝕋



 assocᵀ : {𝓧 : 𝕊 𝓤} {𝓨 : 𝕊 𝓥} {𝓩 : 𝕊 𝓦}
          (g : ⟨ 𝓨 ⟩ → ⟨ T 𝓩 ⟩) (f : ⟨ 𝓧 ⟩ → ⟨ T 𝓨 ⟩)
        → extᵀ {_} {_} {𝓧} {𝓩} (extᵀ g ∘ f) ∼ extᵀ g ∘ extᵀ f
 assocᵀ = assoc 𝕋

 mapᵀ : {𝓧 : 𝕊 𝓤} {𝓨 : 𝕊 𝓥} → (⟨ 𝓧 ⟩ → ⟨ 𝓨 ⟩) → ⟨ T 𝓧 ⟩ → ⟨ T 𝓨 ⟩
 mapᵀ = map 𝕋

 μᵀ : {𝓧 : 𝕊 𝓤} → ⟨ T (T 𝓧) ⟩ → ⟨ T 𝓧 ⟩ -- T (⟨ T 𝓧 ⟩) → ⟨ T 𝓧 ⟩
 μᵀ = μ 𝕋

 _⊗ᵀ_ : {𝓧 : 𝕊 𝓤} {𝓨 : ⟨ 𝓧 ⟩ → 𝕊 𝓥}
      → ⟨ T 𝓧 ⟩
      → ((x : ⟨ 𝓧 ⟩) → ⟨ T (𝓨 x) ⟩)
      → ⟨ T (Σₛ x ꞉ 𝓧 , 𝓨 x) ⟩
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

 is-affine : (𝓤 : Universe) → 𝓤 ⊔ ℓ 𝕋 𝓤 ̇
 is-affine 𝓤 = is-equiv (ηᵀ {𝓤} {𝟙ₛ})

 ext-const' : 𝕊 𝓤 → 𝓤ω
 ext-const' 𝓧 = {𝓥 : Universe} {𝓨 : 𝕊 𝓥} (u : ⟨ T 𝓨 ⟩)
              → extᵀ (λ (x : ⟨ 𝓧 ⟩) → u) ∼ λ (t : ⟨ T 𝓧 ⟩) → u

 ext-const : 𝓤ω
 ext-const = {𝓤 : Universe} {𝓧 : 𝕊 𝓤} → ext-const' 𝓧

 affine-gives-ext-const' : Fun-Ext → is-affine 𝓤 → ext-const' 𝟙ₛ
 affine-gives-ext-const' {𝓤} fe a {𝓨} u t = γ
  where
   f = λ (x : 𝟙) → u

   I : f ∘ inverse (ηᵀ {𝓤} {𝟙ₛ}) a ∼ extᵀ f
   I s = (f ∘ inverse ηᵀ a) s         ＝⟨ I₀ ⟩
         extᵀ f (ηᵀ (inverse ηᵀ a s)) ＝⟨ I₁ ⟩
         extᵀ f s                     ∎
    where
     I₀ = (unitᵀ f (inverse ηᵀ a s))⁻¹
     I₁ = ap (extᵀ f) (inverses-are-sections ηᵀ a s)

   γ : extᵀ f t ＝ u
   γ = extᵀ f t                   ＝⟨ (ap (λ - → - t) (dfunext fe I))⁻¹ ⟩
       (f ∘ inverse (ηᵀ {𝓤} {𝟙ₛ}) a) t ＝⟨ refl ⟩
       u                          ∎

 affine-gives-ext-const : Fun-Ext → ({𝓤 : Universe} → is-affine 𝓤) → ext-const
 affine-gives-ext-const fe a {𝓤} {𝓧} {𝓥} {𝓨} u t = γ
  where
   g : ⟨ 𝓧 ⟩ → ⟨ T 𝓨 ⟩
   g _ = u

   f : ⟨ T 𝟙ₛ ⟩ → ⟨ T 𝓨 ⟩
   f _ = u

   h : 𝟙 → ⟨ T 𝓨 ⟩
   h _ = u

   k : ⟨ 𝓧 ⟩ → ⟨ T 𝟙ₛ ⟩
   k = ηᵀ {𝓤} {𝟙ₛ} ∘ unique-to-𝟙

   I : extᵀ h ＝ f
   I = dfunext fe (affine-gives-ext-const' fe a u)

   γ = extᵀ g t             ＝⟨ refl ⟩
       extᵀ (f ∘ k) t       ＝⟨ ap (λ - → extᵀ (- ∘ k) t) (I ⁻¹) ⟩
       extᵀ (extᵀ h ∘ k) t  ＝⟨ assocᵀ h k t ⟩
       extᵀ h (extᵀ k t)    ＝⟨ ap (λ - → - (extᵀ k t)) I ⟩
       f (extᵀ k t)         ＝⟨ refl ⟩
       u                    ∎

 ext-const-gives-affine : ext-const → is-affine 𝓤
 ext-const-gives-affine {𝓤} ϕ = γ
  where
   η⁻¹ : ⟨ T 𝟙ₛ ⟩ → 𝟙
   η⁻¹ t = ⋆

   I : η⁻¹ ∘ ηᵀ ∼ id
   I ⋆ = refl

   II : ηᵀ ∘ η⁻¹ ∼ id
   II t = (ηᵀ ∘ η⁻¹) t        ＝⟨ refl ⟩
          ηᵀ ⋆                ＝⟨ (ϕ {𝓤} {𝟙ₛ} (ηᵀ ⋆) t)⁻¹ ⟩
          extᵀ (λ x → ηᵀ ⋆) t ＝⟨ refl ⟩
          extᵀ ηᵀ t           ＝⟨ extᵀ-η t ⟩
          t                   ∎

   γ : is-equiv (ηᵀ {𝓤} {𝟙ₛ})
   γ = qinvs-are-equivs ηᵀ (η⁻¹ , I , II)

\end{code}

Monad algebras.

\begin{code}

record Algebra (𝕋 : Monad) (A : 𝕊 𝓦) : 𝓤ω where
 field
  structure-map : ⟨ functor 𝕋 A ⟩ → ⟨ A ⟩
  unit          : structure-map ∘ η 𝕋 ∼ id
  assoc         : structure-map ∘ ext 𝕋 {ℓ 𝕋 𝓦} {𝓦} {functor 𝕋 A} {A} (η 𝕋 ∘ structure-map) ∼ structure-map ∘ ext 𝕋 id

open Algebra public

\end{code}

If we want to call an algebra (literally) α, we can used this module:

\begin{code}

module α-definitions
        (𝕋 : Monad)
        {𝓦₀ : Universe}
        (R : 𝕊 𝓦₀)
        (𝓐 : Algebra 𝕋 R)
       where

 open T-definitions 𝕋

 α : ⟨ T R ⟩ → ⟨ R ⟩
 α = structure-map 𝓐

 α-unitᵀ : α ∘ ηᵀ ∼ id
 α-unitᵀ = unit 𝓐

 α-assocᵀ : α ∘ extᵀ (ηᵀ ∘ α) ∼ α ∘ extᵀ id
 α-assocᵀ = assoc 𝓐

 α-extᵀ : {A : 𝕊 𝓤} → (⟨ A ⟩ → ⟨ R ⟩) → ⟨ T A ⟩ → ⟨ R ⟩
 α-extᵀ q = α ∘ mapᵀ q

 α-curryᵀ : {𝓧 : 𝕊 𝓤} {𝓨 : ⟨ 𝓧 ⟩ → 𝕊 𝓥}
          → (⟨ Σₛ x ꞉ 𝓧 , 𝓨 x ⟩ → ⟨ R ⟩)
          → (x : ⟨ 𝓧 ⟩) → ⟨ T (𝓨 x) ⟩ → ⟨ R ⟩
 α-curryᵀ q x = α-extᵀ (curry q x)

\end{code}

TODO. Define monad morphism (for example overline is a monad morphism
from J to K).
