Tom de Jong, March 2021

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base

module CirclePreliminaries where

𝓛 : (X : 𝓤 ̇ ) → 𝓤 ̇
𝓛 X = Σ x ꞉ X , x ≡ x

𝓛-functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → 𝓛 X → 𝓛 Y
𝓛-functor f (x , p) = f x , ap f p

𝓛-functor-id : {X : 𝓤 ̇ } → 𝓛-functor id ∼ id {𝓤} {𝓛 X}
𝓛-functor-id {𝓤} {X} (x , p) = to-Σ-≡ (refl , γ p)
 where
  γ : {y z : X} (q : y ≡ z) → transport (λ - → y ≡ -) q refl ≡ q
  γ refl = refl

𝓛-functor-comp : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y) (g : Y → Z)
               → 𝓛-functor g ∘ 𝓛-functor f ∼ 𝓛-functor (g ∘ f)
𝓛-functor-comp f g (x , p) = to-Σ-≡ (refl , (ap-ap f g p))

ap-𝓛-functor-lemma : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f g : A → B)
                     {a : A} (p : a ≡ a) {b : B} (q : b ≡ b)
                     (u : 𝓛-functor f (a , p) ≡ (b , q))
                     (v : 𝓛-functor g (a , p) ≡ (b , q))
                     (w : (f , u) ≡ (g , v))
                   → ap (λ - → 𝓛-functor - (a , p)) (ap pr₁ w) ≡ u ∙ v ⁻¹
ap-𝓛-functor-lemma f g p q refl v refl = refl

happly-𝓛-functor-lemma : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f g : A → B)
                         {a : A} (p : a ≡ a) {b : B} (q : b ≡ b)
                         (u : 𝓛-functor f (a , p) ≡ (b , q))
                         (v : 𝓛-functor g (a , p) ≡ (b , q))
                         (w : (f , u) ≡ (g , v))
                       → happly (ap pr₁ w) a ≡ (ap pr₁ u) ∙ (ap pr₁ v) ⁻¹
happly-𝓛-functor-lemma f g p q refl v refl = refl

\end{code}
