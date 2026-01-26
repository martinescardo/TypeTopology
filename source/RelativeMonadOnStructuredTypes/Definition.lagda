Martin Escardo, Paulo Oliva, May 2024

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import Notation.General
open import MLTT.Spartan
open import UF.Equiv
open import UF.FunExt
open import RelativeMonadOnStructuredTypes.OneSigmaStructure

module RelativeMonadOnStructuredTypes.Definition
        {{ρ : 𝟙-Σ-structure}}
       where

open 𝟙-Σ-structure ρ

record Relative-Monad {ℓ : Universe → Universe} : 𝓤ω where
 field
  functor : {𝓤 : Universe} → 𝕊 𝓤 → ℓ 𝓤 ̇

 private
  T = functor

 field
  η       : {𝓤 : Universe} {𝓧 : 𝕊 𝓤}
          → ⟨ 𝓧 ⟩ → T 𝓧
  ext     : {𝓤 𝓥 : Universe} {𝓧 : 𝕊 𝓤} {𝓨 : 𝕊 𝓥}
          → (⟨ 𝓧 ⟩ → T 𝓨)
          → T 𝓧 → T 𝓨
  ext-η   : {𝓤 : Universe} {𝓧 : 𝕊 𝓤}
          → ext (η {𝓤} {𝓧}) ∼ 𝑖𝑑 (T 𝓧)
  unit    : {𝓤 𝓥 : Universe} {𝓧 : 𝕊 𝓤} {𝓨 : 𝕊 𝓥}
            (f : ⟨ 𝓧 ⟩ → T 𝓨)
            (x : ⟨ 𝓧 ⟩)
          → ext {𝓤} {𝓥} {𝓧} {𝓨} f (η x) ＝ f x
  assoc   : {𝓤 𝓥 𝓦 : Universe}
            {𝓧 : 𝕊 𝓤} {𝓨 : 𝕊 𝓥} {𝓩 : 𝕊 𝓦}
            (g : ⟨ 𝓨 ⟩ → T 𝓩)
            (f : ⟨ 𝓧 ⟩ → T 𝓨)
            (t : T 𝓧)
          → ext (λ x → ext g (f x)) t ＝ ext g (ext f t)

 map : {𝓧 : 𝕊 𝓤} {𝓨 : 𝕊 𝓥} → (⟨ 𝓧 ⟩ → ⟨ 𝓨 ⟩) → T 𝓧 → T 𝓨
 map f = ext (η ∘ f)

 _⊗ᵣ_ : {𝓧 : 𝕊 𝓤} {𝓨 : ⟨ 𝓧 ⟩ → 𝕊 𝓥}
      → T 𝓧
      → ((x : ⟨ 𝓧 ⟩) → T (𝓨 x))
      → T (Σₛ x ꞉ 𝓧 , 𝓨 x)
 t ⊗ᵣ f = ext (λ x → map (λ y → x , y) (f x)) t

open Relative-Monad public

\end{code}

TODO. Is "tensor" an appropriate terminology? Would (left)
convolution, in the sense of Day, be better?

    https://ncatlab.org/nlab/show/tensorial+strength
    https://ncatlab.org/nlab/show/Day+convolution

\begin{code}

tensorᵣ : {ℓ : Universe → Universe}
          (𝕋 : Relative-Monad {ℓ})
          {𝓧 : 𝕊 𝓤} {𝓨 : ⟨ 𝓧 ⟩ → 𝕊 𝓥}
        → functor 𝕋 𝓧
        → ((x : ⟨ 𝓧 ⟩) → functor 𝕋 (𝓨 x))
        → functor 𝕋 (Σₛ x ꞉ 𝓧 , 𝓨 x)
tensorᵣ 𝕋 = _⊗ᵣ_ 𝕋

syntax tensorᵣ 𝕋 t f = t ⊗ᵣ[ 𝕋 ] f

\end{code}

If we want to call a Relative-Monad T, then we can use the following
module:

\begin{code}

module relative-T-definitions
        {ℓ : Universe → Universe}
        (𝕋 : Relative-Monad {ℓ})
       where

 T : {𝓤 : Universe}
   → 𝕊 𝓤 → ℓ 𝓤 ̇
 T {𝓤} = functor 𝕋

 ηᵀ : {𝓧 : 𝕊 𝓤}
    → ⟨ 𝓧 ⟩ → T 𝓧
 ηᵀ = η 𝕋

 extᵀ : {𝓧 : 𝕊 𝓤} {𝓨 : 𝕊 𝓥}
      → (⟨ 𝓧 ⟩ → T 𝓨) → T 𝓧 → T 𝓨
 extᵀ = ext 𝕋

 extᵀ-η : {𝓧 : 𝕊 𝓤} → extᵀ (ηᵀ {𝓤} {𝓧}) ∼ 𝑖𝑑 (T 𝓧)
 extᵀ-η = ext-η 𝕋

 unitᵀ : {𝓧 : 𝕊 𝓤} {𝓨 : 𝕊 𝓥} (f : ⟨ 𝓧 ⟩ → T 𝓨)
       → extᵀ {𝓤} {𝓥} {𝓧} {𝓨} f ∘ ηᵀ ∼ f
 unitᵀ = unit 𝕋

 assocᵀ : {𝓧 : 𝕊 𝓤} {𝓨 : 𝕊 𝓥} {𝓩 : 𝕊 𝓦}
          (g : ⟨ 𝓨 ⟩ → T 𝓩) (f : ⟨ 𝓧 ⟩ → T 𝓨)
        → extᵀ {_} {_} {𝓧} {𝓩} (extᵀ g ∘ f) ∼ extᵀ g ∘ extᵀ f
 assocᵀ = assoc 𝕋

 mapᵀ : {𝓧 : 𝕊 𝓤} {𝓨 : 𝕊 𝓥} → (⟨ 𝓧 ⟩ → ⟨ 𝓨 ⟩) → T 𝓧 → T 𝓨
 mapᵀ = map 𝕋

 _⊗ᵀ_ : {𝓧 : 𝕊 𝓤} {𝓨 : ⟨ 𝓧 ⟩ → 𝕊 𝓥}
      → T 𝓧
      → ((x : ⟨ 𝓧 ⟩) → T (𝓨 x))
      → T (Σₛ x ꞉ 𝓧 , 𝓨 x)
 _⊗ᵀ_ = _⊗ᵣ_ 𝕋

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

module _ {ℓ : Universe → Universe}
         (𝕋 : Relative-Monad {ℓ})
       where

 open relative-T-definitions 𝕋

 is-affine : 𝓤ω
 is-affine = {𝓤 : Universe} → is-equiv (ηᵀ {𝓤} {𝟙ₛ})

 ext-const' : 𝕊 𝓤 → 𝓤ω
 ext-const' 𝓧 = {𝓥 : Universe} {𝓨 : 𝕊 𝓥} (u : T 𝓨)
                       → extᵀ (λ (x : ⟨ 𝓧 ⟩) → u) ∼ λ (t : T 𝓧) → u
  where
   remark : {𝓥 : Universe} {𝓨 : 𝕊 𝓥} (u : T 𝓨) → functor 𝕋 𝓧 → functor 𝕋 𝓨
   remark u = extᵀ (λ (x : ⟨ 𝓧 ⟩) → u)

 ext-const : 𝓤ω
 ext-const = {𝓤 : Universe} {𝓧 : 𝕊 𝓤} → ext-const' 𝓧

 affine-gives-ext-const' : Fun-Ext → is-affine → ext-const' (𝟙ₛ {𝓤})
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
   γ = extᵀ f t                        ＝⟨ (ap (λ - → - t) (dfunext fe I))⁻¹ ⟩
       (f ∘ inverse (ηᵀ {𝓤} {𝟙ₛ}) a) t ＝⟨refl⟩
       u                               ∎

 affine-gives-ext-const : Fun-Ext → is-affine → ext-const
 affine-gives-ext-const fe a {𝓤} {𝓧} {𝓥} {𝓨} u t = γ
  where
   g : ⟨ 𝓧 ⟩ → T 𝓨
   g _ = u

   f : T 𝟙ₛ → T 𝓨
   f _ = u

   h : 𝟙 → T 𝓨
   h _ = u

   k : ⟨ 𝓧 ⟩ → T 𝟙ₛ
   k = ηᵀ {𝓤} {𝟙ₛ} ∘ unique-to-𝟙

   I : extᵀ h ＝ f
   I = dfunext fe (affine-gives-ext-const' fe a u)

   γ = extᵀ g t             ＝⟨refl⟩
       extᵀ (f ∘ k) t       ＝⟨ ap (λ - → extᵀ (- ∘ k) t) (I ⁻¹) ⟩
       extᵀ (extᵀ h ∘ k) t  ＝⟨ assocᵀ h k t ⟩
       extᵀ h (extᵀ k t)    ＝⟨ ap (λ - → - (extᵀ k t)) I ⟩
       f (extᵀ k t)         ＝⟨refl⟩
       u                    ∎

 ext-const-gives-affine : ext-const → is-affine
 ext-const-gives-affine ϕ {𝓤} = γ
  where
   η⁻¹ : T 𝟙ₛ → 𝟙
   η⁻¹ t = ⋆

   I : η⁻¹ ∘ ηᵀ ∼ id
   I ⋆ = refl

   II : ηᵀ ∘ η⁻¹ ∼ id
   II t = (ηᵀ ∘ η⁻¹) t        ＝⟨refl⟩
          ηᵀ ⋆                ＝⟨ (ϕ {𝓤} {𝟙ₛ} (ηᵀ ⋆) t)⁻¹ ⟩
          extᵀ (λ x → ηᵀ ⋆) t ＝⟨refl⟩
          extᵀ ηᵀ t           ＝⟨ extᵀ-η t ⟩
          t                   ∎

   γ : is-equiv (ηᵀ {𝓤} {𝟙ₛ})
   γ = qinvs-are-equivs ηᵀ (η⁻¹ , I , II)

\end{code}

Relative-Monad algebras.

\begin{code}

record Relative-Algebra
        {𝓦₀ : Universe}
        {ℓ : Universe → Universe}
        (𝕋 : Relative-Monad {ℓ})
        (R : 𝓦₀ ̇ ) : 𝓤ω where
 field
  aext     : {𝓤 : Universe} {𝓧 : 𝕊 𝓤}
           → (⟨ 𝓧 ⟩ → R)
           → functor 𝕋 𝓧 → R
  aunit    : {𝓤 : Universe} {𝓧 : 𝕊 𝓤}
             (f : ⟨ 𝓧 ⟩ → R)
             (x : ⟨ 𝓧 ⟩)
           → aext {𝓤} {𝓧} f (η 𝕋 x) ＝ f x
  aassoc   : {𝓤 𝓥 : Universe}
             {𝓧 : 𝕊 𝓤} {𝓨 : 𝕊 𝓥}
             (g : ⟨ 𝓨 ⟩ → R)
             (f : ⟨ 𝓧 ⟩ → functor 𝕋 𝓨)
             (t : functor 𝕋 𝓧)
           → aext (λ x → aext g (f x)) t ＝ aext g (ext 𝕋 f t)

open Relative-Algebra public

\end{code}

If we want to call an algebra (literally) α, we can used this module:

\begin{code}

module relative-α-definitions
        {ℓ : Universe → Universe}
        (𝕋 : Relative-Monad {ℓ})
        {𝓦₀ : Universe}
        (𝓡 : 𝕊 𝓦₀)
        (𝓐 : Relative-Algebra {𝓦₀} {ℓ} 𝕋 ⟨ 𝓡 ⟩)
       where

 open relative-T-definitions 𝕋

 α : T 𝓡 → ⟨ 𝓡 ⟩
 α = aext 𝓐 id

 α-unitᵀ : α ∘ ηᵀ ∼ id
 α-unitᵀ = aunit 𝓐 id

 extᴬ : {𝓧 : 𝕊 𝓤} → (⟨ 𝓧 ⟩ → ⟨ 𝓡 ⟩) → T 𝓧 → ⟨ 𝓡 ⟩
 extᴬ = aext 𝓐

 extᴬ-alternative : {𝓧 : 𝕊 𝓤} → (⟨ 𝓧 ⟩ → ⟨ 𝓡 ⟩) → T 𝓧 → ⟨ 𝓡 ⟩
 extᴬ-alternative q = α ∘ mapᵀ q

 extᴬ-agreement
  : funext 𝓤 𝓦₀
  → {𝓧 : 𝕊 𝓤} (f : ⟨ 𝓧 ⟩ → ⟨ 𝓡 ⟩) (t : T 𝓧)
  → extᴬ f t ＝ extᴬ-alternative f t
 extᴬ-agreement {𝓤} fe {𝓧} f t =
  extᴬ f t                                     ＝⟨refl⟩
  aext 𝓐 f t                                   ＝⟨ I ⟩
  aext 𝓐 (λ x → aext 𝓐 id (ηᵀ (f x))) t        ＝⟨ II ⟩
  aext 𝓐 (λ x → x) (ext 𝕋 (λ x → η 𝕋 (f x)) t) ＝⟨refl⟩
  extᴬ-alternative f t                         ∎
   where
    I  = ap (λ - → aext 𝓐 - t) (dfunext fe (λ x → (aunit 𝓐 id (f x))⁻¹))
    II = aassoc 𝓐 id (ηᵀ ∘ f) t

 unitᴬ : {𝓧 : 𝕊 𝓤}
         (f : ⟨ 𝓧 ⟩ → ⟨ 𝓡 ⟩)
         (x : ⟨ 𝓧 ⟩)
       → aext 𝓐 {𝓤} {𝓧} f (ηᵀ x) ＝ f x
 unitᴬ = aunit 𝓐

\end{code}

Free algebras.

\begin{code}

module _ {𝓣₀ : Universe}
         {ℓ : Universe → Universe}
         (𝕋 : Relative-Monad {ℓ})
         (𝓐 : 𝕊 𝓣₀)
       where

 open relative-T-definitions 𝕋

 free-relative-algebra : Relative-Algebra 𝕋 (T 𝓐)
 free-relative-algebra =
  record {
    aext   = extᵀ
  ; aunit  = unitᵀ
  ; aassoc = assocᵀ
  }

\end{code}

TODO. Define Relative-Monad morphism (for example overline is a
Relative-Monad morphism from J to K).
