Tom de Jong, 27 May 2019.
Refactored 29 April 2020.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

open import UF-FunExt
open import UF-PropTrunc
open import UF-Subsingletons

module DcpoLifting
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓣 : Universe)
        (pe : propext 𝓣)
       where

open PropositionalTruncation pt

open import UF-Miscelanea
open import UF-Subsingletons-FunExt

open import UF-ImageAndSurjection
open ImageAndSurjection pt

open import Lifting 𝓣
open import LiftingMiscelanea 𝓣
open import LiftingMiscelanea-PropExt-FunExt 𝓣 pe fe
open import LiftingMonad 𝓣

open import Dcpo pt fe 𝓣 hiding (⊥)
open import DcpoBasics pt fe 𝓣

open import Poset fe

module _ {𝓤 : Universe}
         {X : 𝓤 ̇ }
         (s : is-set X)
       where

 family-value-map : {I : 𝓣 ̇}
                  → (α : I → 𝓛 X)
                  → (Σ i ꞉ I , is-defined (α i)) → X
 family-value-map α (i , d) = value (α i) d

 directed-family-value-map-is-wconstant : {I : 𝓣 ̇  }
                                        → (α : I → 𝓛 X)
                                        → (δ : is-directed _⊑'_ α )
                                        → wconstant (family-value-map α)
 directed-family-value-map-is-wconstant {I} α δ (i₀ , d₀) (i₁ , d₁) =
  γ (semidirected-if-directed _⊑'_ α δ i₀ i₁)
   where
    f : (Σ i ꞉ I , is-defined (α i)) → X
    f = family-value-map α
    γ : (∃ k ꞉ I , (α i₀ ⊑' α k) × (α i₁ ⊑' α k)) → f (i₀ , d₀) ≡ f (i₁ , d₁)
    γ = ∥∥-rec s g
     where
      g : (Σ k ꞉ I , (α i₀ ⊑' α k)
                   × (α i₁ ⊑' α k)) → f (i₀ , d₀) ≡ f (i₁ , d₁)
      g (k , l , m) =
       f (i₀ , d₀)                             ≡⟨ refl ⟩
       value (α i₀) d₀                         ≡⟨ ≡-of-values-from-≡ (l d₀) ⟩
       value (α k) (≡-to-is-defined (l d₀) d₀) ≡⟨ ≡-of-values-from-≡ ((m d₁) ⁻¹) ⟩
       value (α i₁) d₁                         ≡⟨ refl ⟩
       f (i₁ , d₁)                             ∎

 lifting-sup-value : {I : 𝓣 ̇}
                   → (α : I → 𝓛 X)
                   → (δ : is-directed _⊑'_ α )
                   → (∃ i ꞉ I , is-defined (α i)) → X
 lifting-sup-value {I} α δ =
  pr₁ (wconstant-map-to-set-factors-through-truncation-of-domain
        s (family-value-map α)
        (directed-family-value-map-is-wconstant α δ))

 lifting-sup : {I : 𝓣 ̇} → (α : I → 𝓛 X) → (δ : is-directed _⊑'_ α) → 𝓛 X
 lifting-sup {I} α δ =
  (∃ i ꞉ I , is-defined (α i)) , lifting-sup-value α δ , ∥∥-is-prop

 lifting-sup-is-upperbound : {I : 𝓣 ̇} → (α : I → 𝓛 X)
                             (δ : is-directed _⊑'_ α)
                           → (i : I) → α i ⊑' lifting-sup α δ
 lifting-sup-is-upperbound {I} α δ i = γ
  where
   γ : α i ⊑' lifting-sup α δ
   γ = ⊑-to-⊑' (f , v)
    where
     f : is-defined (α i) → is-defined (lifting-sup α δ)
     f d = ∣ i , d ∣
     v : (d : is-defined (α i)) → value (α i) d ≡ value (lifting-sup α δ) (f d)
     v d = value (α i) d                 ≡⟨ p    ⟩
           lifting-sup-value α δ (f d)   ≡⟨ refl ⟩
           value (lifting-sup α δ) (f d) ∎
      where
       p = (pr₂ (wconstant-map-to-set-factors-through-truncation-of-domain
                  s (family-value-map α)
                  (directed-family-value-map-is-wconstant α δ)))
           (i , d)

 family-defined-somewhere-sup-≡ : {I : 𝓣 ̇} {α : I → 𝓛 X}
                                → (δ : is-directed _⊑'_ α)
                                → (i : I)
                                → is-defined (α i)
                                → α i ≡ lifting-sup α δ
 family-defined-somewhere-sup-≡ {I} {α} δ i d =
  (lifting-sup-is-upperbound α δ i) d

 lifting-sup-is-lowerbound-of-upperbounds : {I : 𝓣 ̇}
                                          → {α : I → 𝓛 X}
                                          → (δ : is-directed _⊑'_ α)
                                          → (v : 𝓛 X)
                                          → ((i : I) → α i ⊑' v)
                                          → lifting-sup α δ ⊑' v
 lifting-sup-is-lowerbound-of-upperbounds {I} {α} δ v b = h
  where
   h : lifting-sup α δ ⊑' v
   h d = ∥∥-rec (lifting-of-set-is-set s) g d
    where
     g : (Σ i ꞉ I , is-defined (α i)) → lifting-sup α δ ≡ v
     g (i , dᵢ) = lifting-sup α δ ≡⟨ (family-defined-somewhere-sup-≡ δ i dᵢ) ⁻¹ ⟩
                  α i             ≡⟨ b i dᵢ ⟩
                  v               ∎

 𝓛-DCPO : DCPO {𝓣 ⁺ ⊔ 𝓤} {𝓣 ⁺ ⊔ 𝓤}
 𝓛-DCPO = 𝓛 X , _⊑'_ , pa , c
  where
   pa : PosetAxioms.poset-axioms _⊑'_
   pa = sl , p , r , t , a
    where
     open PosetAxioms {_} {_} {𝓛 X} _⊑'_
     sl : is-set (𝓛 X)
     sl = lifting-of-set-is-set s
     p : is-prop-valued
     p _ _ = ⊑'-prop-valued s
     r : is-reflexive
     r _ = ⊑'-is-reflexive
     a : is-antisymmetric
     a _ _ = ⊑'-is-antisymmetric
     t : is-transitive
     t _ _ _ = ⊑'-is-transitive
   c : (I : 𝓣 ̇ ) (α : I → 𝓛 X) → is-directed _⊑'_ α → has-sup _⊑'_ α
   c I α δ = lifting-sup α δ ,
             lifting-sup-is-upperbound α δ ,
             lifting-sup-is-lowerbound-of-upperbounds δ

 𝓛-DCPO⊥ : DCPO⊥ {𝓣 ⁺ ⊔ 𝓤} {𝓣 ⁺ ⊔ 𝓤}
 𝓛-DCPO⊥ = 𝓛-DCPO , ⊥ , λ _ → unique-from-𝟘

\end{code}

Now that we have the lifting as a dcpo, we prove that the lifting functor and
Kleisli extension yield continuous maps.

\begin{code}

module _ {𝓤 : Universe}
         {X : 𝓤 ̇ }
         (s₀ : is-set X)
         {𝓥 : Universe}
         {Y : 𝓥 ̇ }
         (s₁ : is-set Y)
       where

 ♯-is-monotone : (f : X → 𝓛 Y) → is-monotone (𝓛-DCPO s₀) (𝓛-DCPO s₁) (f ♯)
 ♯-is-monotone f l m ineq d = ap (f ♯) (ineq (♯-is-defined f l d))

 ♯-is-continuous : (f : X → 𝓛 Y) → is-continuous (𝓛-DCPO s₀) (𝓛-DCPO s₁) (f ♯)
 ♯-is-continuous f I α δ = u , v
  where
   u : (i : I) → (f ♯) (α i) ⊑⟨ (𝓛-DCPO s₁) ⟩ (f ♯) (∐ (𝓛-DCPO s₀) δ)
   u i = ♯-is-monotone f (α i) (∐ (𝓛-DCPO s₀) δ)
         (∐-is-upperbound (𝓛-DCPO s₀) δ i)
   v : (m : ⟨ 𝓛-DCPO s₁ ⟩)
     → ((i : I) → (f ♯) (α i) ⊑⟨ (𝓛-DCPO s₁) ⟩ m)
     → (f ♯) (∐ (𝓛-DCPO s₀) δ) ⊑⟨ (𝓛-DCPO s₁) ⟩ m
   v m ineqs d =
    ∥∥-rec (lifting-of-set-is-set s₁) g (♯-is-defined f (∐ (𝓛-DCPO s₀) δ) d)
     where
      g : (Σ i ꞉ I , is-defined (α i)) → (f ♯) (∐ (𝓛-DCPO s₀) δ) ≡ m
      g (i , dᵢ) = (f ♯) (∐ (𝓛-DCPO s₀) δ) ≡⟨ h i dᵢ ⟩
                   (f ♯) (α i)             ≡⟨ ineqs i (≡-to-is-defined (h i dᵢ) d) ⟩
                   m                       ∎
       where
        h : (i : I) → is-defined (α i) → (f ♯) (∐ (𝓛-DCPO s₀) δ) ≡ (f ♯) (α i)
        h i d = ap (f ♯) ((family-defined-somewhere-sup-≡ s₀ δ i d) ⁻¹)

 𝓛̇-continuous : (f : X → Y) → is-continuous (𝓛-DCPO s₀) (𝓛-DCPO s₁) (𝓛̇ f)
 𝓛̇-continuous f = transport
                   (is-continuous (𝓛-DCPO s₀) (𝓛-DCPO s₁))
                   (dfunext fe (𝓛̇-♯-∼ f))
                   (♯-is-continuous (η ∘ f))

\end{code}
