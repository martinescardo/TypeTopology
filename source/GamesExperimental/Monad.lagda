Martin Escardo, Paulo Oliva, March 2024

(Strong, wild) universe-polymorphic monads on types.

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

module GamesExperimental.Monad where

record Monad : 𝓤ω where
 constructor
  monad
 field
  ℓ       : Universe → Universe
  functor : {𝓤 : Universe} → 𝓤 ̇ → ℓ 𝓤 ̇
  η       : {𝓤 : Universe} {X : 𝓤 ̇ } → X → functor X
  ext     : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → functor Y) → functor X → functor Y
  ext-η   : {𝓤 : Universe} {X : 𝓤 ̇ } → ext (η {𝓤} {X}) ∼ 𝑖𝑑 (functor X)
  unit    : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → functor Y) (x : X) → ext f (η x) ＝ f x
  assoc   : {𝓤 𝓥 𝓦 : Universe}
            {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
            (g : Y → functor Z) (f : X → functor Y) (t : functor X)
          → ext (λ x → ext g (f x)) t ＝ ext g (ext f t)

 map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → functor X → functor Y
 map f = ext (η ∘ f)

 μ : {X : 𝓤 ̇ } → functor (functor X) → functor X
 μ = ext id

 _⊗_ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
     → functor X
     → ((x : X) → functor (Y x))
     → functor (Σ x ꞉ X , Y x)
 t ⊗ f = ext (λ x → map (λ y → x , y) (f x)) t

open Monad public

tensor : (𝕋 : Monad) → {X : 𝓤 ̇ } {Y : X → 𝓥  ̇ }
       → functor 𝕋 X
       → ((x : X) → functor 𝕋 (Y x))
       → functor 𝕋 (Σ x ꞉ X , Y x)
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

𝕀𝕕⊗ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
      (x : X)
      (f : (x : X) → (Y x))
    → x ⊗[ 𝕀𝕕 ] f ＝ x , f x
𝕀𝕕⊗ x f = refl

\end{code}

If we want to call a monad T, then we can use the following module:

\begin{code}

module T-definitions (𝕋 : Monad) where

 T : 𝓤 ̇ → ℓ 𝕋 𝓤 ̇
 T {𝓤} = functor 𝕋

 ηᵀ : {X : 𝓤 ̇ } → X → T X
 ηᵀ = η 𝕋

 extᵀ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → T Y) → T X → T Y
 extᵀ = ext 𝕋

 extᵀ-η : {X : 𝓤 ̇ } → extᵀ (ηᵀ {𝓤} {X}) ∼ 𝑖𝑑 (T X)
 extᵀ-η = ext-η 𝕋

 unitᵀ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → T Y) → extᵀ f ∘ ηᵀ ∼ f
 unitᵀ = unit 𝕋

 assocᵀ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇}
          (g : Y → T Z) (f : X → T Y)
        → extᵀ (extᵀ g ∘ f) ∼ extᵀ g ∘ extᵀ f
 assocᵀ = assoc 𝕋

 mapᵀ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → T X → T Y
 mapᵀ = map 𝕋

 μᵀ : {X : 𝓤 ̇ } → T (T X) → T X
 μᵀ = μ 𝕋

 _⊗ᵀ_ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
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

 is-affine : (𝓤 : Universe) → ℓ 𝕋 𝓤 ⊔ 𝓤 ̇
 is-affine 𝓤 = is-equiv (ηᵀ {𝓤} {𝟙})

 ext-const' : 𝓤 ̇ → 𝓤ω
 ext-const' X = {𝓥 : Universe} {Y : 𝓥 ̇ } (u : T Y)
              → extᵀ (λ (x : X) → u) ∼ λ (t : T X) → u

 ext-const : 𝓤ω
 ext-const = {𝓤 : Universe} {X : 𝓤 ̇ } → ext-const' X

 affine-gives-ext-const' : Fun-Ext → is-affine 𝓤 → ext-const' 𝟙
 affine-gives-ext-const' {𝓤} fe a {Y} u t = γ
  where
   f = λ (x : 𝟙) → u

   I : f ∘ inverse (ηᵀ {𝓤} {𝟙}) a ∼ extᵀ f
   I s = (f ∘ inverse ηᵀ a) s         ＝⟨ I₀ ⟩
         extᵀ f (ηᵀ (inverse ηᵀ a s)) ＝⟨ I₁ ⟩
         extᵀ f s                     ∎
    where
     I₀ = (unitᵀ f (inverse ηᵀ a s))⁻¹
     I₁ = ap (extᵀ f) (inverses-are-sections ηᵀ a s)

   γ : extᵀ f t ＝ u
   γ = extᵀ f t                   ＝⟨ (ap (λ - → - t) (dfunext fe I))⁻¹ ⟩
       (f ∘ inverse (ηᵀ {𝓤} {𝟙}) a) t ＝⟨ refl ⟩
       u                          ∎

 affine-gives-ext-const : Fun-Ext → ({𝓤 : Universe} → is-affine 𝓤) → ext-const
 affine-gives-ext-const fe a {𝓤} {X} {𝓥} {Y} u t = γ
  where
   g : X → T Y
   g _ = u

   f : T 𝟙 → T Y
   f _ = u

   h : 𝟙 → T Y
   h _ = u

   k : X → T 𝟙
   k = ηᵀ {𝓤} {𝟙} ∘ unique-to-𝟙

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
   η⁻¹ : T 𝟙 → 𝟙
   η⁻¹ t = ⋆

   I : η⁻¹ ∘ ηᵀ ∼ id
   I ⋆ = refl

   II : ηᵀ ∘ η⁻¹ ∼ id
   II t = (ηᵀ ∘ η⁻¹) t        ＝⟨ refl ⟩
          ηᵀ ⋆                ＝⟨ (ϕ {𝓤} {𝟙} (ηᵀ ⋆) t)⁻¹ ⟩
          extᵀ (λ x → ηᵀ ⋆) t ＝⟨ refl ⟩
          extᵀ ηᵀ t           ＝⟨ extᵀ-η t ⟩
          t                   ∎

   γ : is-equiv (ηᵀ {𝓤} {𝟙})
   γ = qinvs-are-equivs ηᵀ (η⁻¹ , I , II)

\end{code}

Monad algebras.

\begin{code}

record Algebra (𝕋 : Monad) (A : 𝓦 ̇ ) : 𝓤ω where
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
        {𝓦₀ : Universe}
        (R : 𝓦₀  ̇ )
        (𝓐 : Algebra 𝕋 R)
       where

 open T-definitions 𝕋

 α : T R → R
 α = structure-map 𝓐

 α-unitᵀ : α ∘ ηᵀ ∼ id
 α-unitᵀ = unit 𝓐

 α-assocᵀ : α ∘ extᵀ (ηᵀ ∘ α) ∼ α ∘ extᵀ id
 α-assocᵀ = assoc 𝓐

 α-extᵀ : {A : 𝓤 ̇ } → (A → R) → T A → R
 α-extᵀ q = α ∘ mapᵀ q

 α-curryᵀ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
          → ((Σ x ꞉ X , Y x) → R)
          → (x : X) → T (Y x) → R
 α-curryᵀ q x = α-extᵀ (curry q x)

\end{code}

TODO. Define monad morphism (for example overline is a monad morphism
from J to K).
