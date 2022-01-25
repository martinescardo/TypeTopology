Tom de Jong, 25 January 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

open import UF-FunExt
open import UF-PropTrunc
open import UF-Subsingletons

module DcpoPowerset
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (pe : propext 𝓤)
        {X : 𝓤 ̇  }
        (X-is-set : is-set X)
       where

open PropositionalTruncation pt

{-
open import UF-Equiv

open import UF-Miscelanea
open import UF-Subsingletons-FunExt


-}

open import List

open import UF-ImageAndSurjection
open import UF-Powerset
open import UF-Powerset-Fin pt
open import UF-Subsingletons-FunExt

open import Dcpo pt fe 𝓤
open import DcpoMiscelanea pt fe 𝓤
open import DcpoWayBelow pt fe 𝓤

open import Poset fe

open binary-unions-of-subsets pt
open canonical-map-from-lists-to-subsets X-is-set
open ImageAndSurjection pt
open unions-of-small-families pt

𝓟-dcpo : DCPO {𝓤 ⁺} {𝓤}
𝓟-dcpo = 𝓟 X , _⊆_ ,
         ( powersets-are-sets fe pe
         , ⊆-is-prop fe
         , ⊆-refl
         , ⊆-trans
         , λ A B → subset-extensionality pe fe)
         , dir-compl
 where
  dir-compl : is-directed-complete _⊆_
  dir-compl I α δ = ⋃ α , ⋃-is-upperbound α , ⋃-is-lowerbound-of-upperbounds α

-- TODO: Add 𝓟-dcpo⊥ version

κ⁺ : (A : 𝓟 X) → (Σ l ꞉ List X , κ l ⊆ A) → 𝓟 X
κ⁺ A = κ ∘ pr₁

κ⁺-is-directed : (A : 𝓟 X) → is-Directed 𝓟-dcpo (κ⁺ A)
κ⁺-is-directed A = inh , semidir
 where
  inh : ∃ l ꞉ List X , κ l ⊆ A
  inh = ∣ [] , (∅-is-least A) ∣
  semidir : is-semidirected _⊆_ (κ⁺ A)
  semidir (l₁ , s₁) (l₂ , s₂) = ∣ ((l₁ ++ l₂) , s) , u₁ , u₂ ∣
   where
    e : κ (l₁ ++ l₂) ≡ κ l₁ ∪ κ l₂
    e = κ-of-concatenated-lists-is-union pe fe l₁ l₂
    u : (κ l₁ ∪ κ l₂) ⊆ κ (l₁ ++ l₂)
    u = ≡-to-⊑ 𝓟-dcpo (e ⁻¹)
    -- unfortunately, using the ⊑⟨ 𝓟-dcpo ⟩-syntax here gives
    -- implicit arguments problems, so we use ⊆-trans instead.
    u₁ : κ l₁ ⊆ κ (l₁ ++ l₂)
    u₁ = ⊆-trans (κ l₁) (κ l₁ ∪ κ l₂) (κ (l₁ ++ l₂))
          (∪-is-upperbound₁ (κ l₁) (κ l₂)) u
    u₂ = ⊆-trans (κ l₂) (κ l₁ ∪ κ l₂) (κ (l₁ ++ l₂))
          (∪-is-upperbound₂ (κ l₁) (κ l₂)) u
    s : κ (l₁ ++ l₂) ⊆ A
    s = ⊆-trans (κ (l₁ ++ l₂)) (κ l₁ ∪ κ l₂) A ⦅1⦆ ⦅2⦆
     where
      ⦅1⦆ : κ (l₁ ++ l₂) ⊆ (κ l₁ ∪ κ l₂)
      ⦅1⦆ = ≡-to-⊑ 𝓟-dcpo e
      ⦅2⦆ : (κ l₁ ∪ κ l₂) ⊆ A
      ⦅2⦆ = ∪-is-lowerbound-of-upperbounds (κ l₁) (κ l₂) A s₁ s₂

Kuratowski-finite-if-compact : (A : 𝓟 X)
                             → is-compact 𝓟-dcpo A
                             → is-Kuratowski-finite-subset A
Kuratowski-finite-if-compact A c =
 Kuratowski-finite-subset-if-in-image-of-κ A γ
  where
   claim : ∃ l⁺ ꞉ (Σ l ꞉ List X , κ l ⊆ A) , A ⊆ κ⁺ A l⁺
   claim = c (domain (κ⁺ A)) (κ⁺ A) (κ⁺-is-directed A) A-below-∐κ⁺
    where
     A-below-∐κ⁺ : A ⊆ ⋃ (κ⁺ A)
     A-below-∐κ⁺ x a = ⋃-is-upperbound (κ⁺ A) ([ x ] , s) x i
      where
       open singleton-subsets X-is-set
       s : (❴ x ❵ ∪ ∅) ⊆ A
       s = ∪-is-lowerbound-of-upperbounds ❴ x ❵ ∅ A t (∅-is-least A)
        where
         t : ❴ x ❵ ⊆ A
         t _ refl = a
       i : x ∈ (❴ x ❵ ∪ ∅)
       i = ∪-is-upperbound₁ ❴ x ❵ ∅ x ∈-❴❵
   γ : A ∈image κ
   γ = ∥∥-functor h claim
    where
     h : (Σ l⁺ ꞉ (Σ l ꞉ List X , κ l ⊆ A) , A ⊆ κ⁺ A l⁺)
       → Σ l ꞉ List X , κ l ≡ A
     h ((l , s) , t) = (l , subset-extensionality pe fe s t)

compact-if-Kuratowski-finite : (A : 𝓟 X)
                             → is-Kuratowski-finite-subset A
                             → is-compact 𝓟-dcpo A
compact-if-Kuratowski-finite A k =
 ∥∥-rec (being-compact-is-prop 𝓟-dcpo A) goal claim
  where
   lemma : (l : List X) (I : 𝓤 ̇  ) (𝓐 : I → 𝓟 X)
         → is-Directed 𝓟-dcpo 𝓐
         → κ l ⊆ ⋃ 𝓐
         → ∃ i ꞉ I , κ l ⊆ 𝓐 i
   lemma []      I 𝓐 δ u = ∥∥-functor h (inhabited-if-Directed 𝓟-dcpo 𝓐 δ)
    where
     h : I → (Σ i ꞉ I , ∅ ⊆ 𝓐 i)
     h i = i , (∅-is-least (𝓐 i))
   lemma (x ∷ l) I 𝓐 δ u = ∥∥-rec₂ ∃-is-prop ρ h IH
    where
     open singleton-subsets X-is-set
     ρ : (Σ i ꞉ I , ❴ x ❵ ⊆ 𝓐 i)
       → (Σ j ꞉ I , κ l ⊆ 𝓐 j)
       → (∃ k ꞉ I , κ (x ∷ l) ⊆ 𝓐 k)
     ρ (i , sₓ) (j , sₗ) = ∥∥-functor σ (semidirected-if-Directed 𝓟-dcpo 𝓐 δ i j)
      where
       σ : (Σ k ꞉ I , (𝓐 i ⊆ 𝓐 k) × (𝓐 j ⊆ 𝓐 k))
         → (Σ k ꞉ I , κ (x ∷ l) ⊆ 𝓐 k)
       σ (k , sᵢ , sⱼ) = k , s
        where
         s : κ (x ∷ l) ⊆ 𝓐 k
         s = ⊆-trans (κ (x ∷ l)) (𝓐 i ∪ 𝓐 j) (𝓐 k) ⦅1⦆ ⦅2⦆
          where
           ⦅1⦆ : (❴ x ❵ ∪ κ l) ⊆ (𝓐 i ∪ 𝓐 j)
           ⦅1⦆ = ∪-is-lowerbound-of-upperbounds ❴ x ❵ (κ l) (𝓐 i ∪ 𝓐 j)
                 (⊆-trans ❴ x ❵ (𝓐 i) (𝓐 i ∪ 𝓐 j)
                   sₓ (∪-is-upperbound₁ (𝓐 i) (𝓐 j)))
                 (⊆-trans (κ l) (𝓐 j) (𝓐 i ∪ 𝓐 j)
                   sₗ (∪-is-upperbound₂ (𝓐 i) (𝓐 j)))
           ⦅2⦆ : (𝓐 i ∪ 𝓐 j) ⊆ 𝓐 k
           ⦅2⦆ = ∪-is-lowerbound-of-upperbounds (𝓐 i) (𝓐 j) (𝓐 k) sᵢ sⱼ
     h : ∃ i ꞉ I , ❴ x ❵ ⊆ 𝓐 i
     h = ∥∥-functor r (u₁ x ∈-❴❵)
      where
       r : (Σ i ꞉ I , x ∈ 𝓐 i) → (Σ i ꞉ I , ❴ x ❵ ⊆ 𝓐 i)
       r (i , a) = (i , (λ y p → transport (_∈ 𝓐 i) p a))
       u₁ : ❴ x ❵ ⊆ ⋃ 𝓐
       u₁ = ⊆-trans ❴ x ❵ (❴ x ❵ ∪ κ l) (⋃ 𝓐)
             (∪-is-upperbound₁ ❴ x ❵ (κ l)) u
     IH : ∃ i ꞉ I , κ l ⊆ 𝓐 i
     IH = lemma l I 𝓐 δ u₂
      where
       u₂ : κ l ⊆ ⋃ 𝓐
       u₂ = (⊆-trans (κ l) (❴ x ❵ ∪ κ l) (⋃ 𝓐)
              (∪-is-upperbound₂ ❴ x ❵ (κ l)) u)

   claim : A ∈image κ
   claim = in-image-of-κ-if-Kuratowski-finite-subset pe fe A k

   goal : (Σ l ꞉ List X , κ l ≡ A) → is-compact 𝓟-dcpo A
   goal (l , refl) I 𝓐 δ A-below-∐𝓐 = lemma l I 𝓐 δ A-below-∐𝓐


\end{code}
