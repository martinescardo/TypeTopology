Ayberk Tosun, 1 March 2022.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import Universes
open import SpartanMLTT
open import UF-Base
open import UF-PropTrunc
open import UF-FunExt
open import Sigma

module AdjointFunctorTheoremForFrames
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
         where

open import Frame pt fe
open import GaloisConnection pt fe
open import UF-Subsingletons

open import UF-Subsingleton-Combinators

open AllCombinators pt fe
open PropositionalTruncation pt

\end{code}

\begin{code}

module AdjointFunctorTheorem (K : frame 𝓤  𝓥  𝓥)
                             (𝒷 : has-basis K holds)
                             (L : frame 𝓤' 𝓥 𝓥) where

\end{code}

\begin{code}

 private
  Kₚ = poset-of K
  Lₚ = poset-of L

 open GaloisConnectionBetween Kₚ Lₚ

 aft-forward : (f : Kₚ ─m→ Lₚ)
             → has-right-adjoint f
             → is-join-preserving K L (f .pr₁) holds
 aft-forward (f , μ) (ℊ@(g , _) , p) S =
  ⋁[ L ]-unique ⁅ f s ∣ s ε S ⁆ (f (⋁[ K ] S)) (β , γ)
   where
    open Joins (λ x y → x ≤[ poset-of L ] y)
    open Joins (λ x y → x ≤[ poset-of K ] y)
     using () renaming (_is-an-upper-bound-of_ to _is-a-ub-of_)

    β : (f (⋁[ K ] S) is-an-upper-bound-of ⁅ f s ∣ s ε S ⁆) holds
    β i = μ (S [ i ] , ⋁[ K ] S) (⋁[ K ]-upper S i)

    γ : (Ɐ (u , _) ∶ upper-bound ⁅ f s ∣ s ε S ⁆ , f (⋁[ K ] S) ≤[ Lₚ ] u) holds
    γ (u , q) = pr₂ (p (⋁[ K ] S) u) (⋁[ K ]-least S (g u , δ))
     where
      δ : (g u is-a-ub-of S) holds
      δ i = pr₁ (p (S [ i ]) u) (q i)

\end{code}

\begin{code}

 aft-backward : (𝒻 : Kₚ ─m→ Lₚ)
              → is-join-preserving K L (𝒻 .pr₁) holds
              → has-right-adjoint 𝒻
 aft-backward 𝒻@(f , μf) φ = ∥∥-rec (has-right-adjoint-is-prop 𝒻) γ 𝒷
  where
   open Joins (λ x y → x ≤[ poset-of K ] y)
   open Joins (λ x y → x ≤[ poset-of L ] y)
         using    ()
         renaming (_is-an-upper-bound-of_ to _is-an-ub-of_)

   γ : Σ ℬ ꞉ (Fam 𝓥 ⟨ K ⟩) , is-basis-for K ℬ → Σ ℊ ꞉ (Lₚ ─m→ Kₚ) , (𝒻 ⊣ ℊ) holds
   γ (ℬ , b) = (g , μ′) , β
    where
     𝒦 : ∣ Lₚ ∣ₚ → 𝓥 ̇
     𝒦 y = Σ i ꞉ index ℬ , (f (ℬ [ i ]) ≤[ Lₚ ] y) holds

     g : ∣ Lₚ ∣ₚ → ∣ Kₚ ∣ₚ
     g y = ⋁[ K ] ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 y ⁆

     μ′ : is-monotonic Lₚ Kₚ g holds
     μ′ (y₁ , y₂) p =
      ⋁[ K ]-least ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 y₁ ⁆ (g y₂ , ε)
        where
         open PosetReasoning Lₚ

         ε : (g y₂ is-an-upper-bound-of ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 y₁ ⁆) holds
         ε 𝒾@(i , q) = ⋁[ K ]-upper ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 y₂ ⁆ (i , †)
          where
           † : (f (ℬ [ i ]) ≤[ Lₚ ] y₂) holds
           † = f (ℬ [ i ]) ≤⟨ q ⟩ y₁ ≤⟨ p ⟩ y₂ ■

     ℊ = g , μ′

     β : (𝒻 ⊣ ℊ) holds
     β x y = β₁ , β₂
      where
       𝒥 : Fam 𝓥 (index ℬ)
       𝒥 = pr₁ (b x)

       c : x ≡ ⋁[ K ] ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆
       c = ⋁[ K ]-unique ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆ x (pr₂ (b x))

       β₁ : (f x ≤[ Lₚ ] y ⇒ x ≤[ Kₚ ] g y) holds
       β₁ p = x                           ≡⟨ c ⟩ₚ
              ⋁[ K ] ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆  ≤⟨ † ⟩
              g y                         ■
        where
         open PosetReasoning Kₚ
         open PosetReasoning Lₚ using () renaming (_■ to _■ₗ; _≤⟨_⟩_ to _≤⟨_⟩ₗ_)

         u = ⋁[ K ] ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 y ⁆

         ζ : (u is-an-upper-bound-of ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆) holds
         ζ j = ⋁[ K ]-upper ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 y ⁆ (𝒥 [ j ] , η)
                where
                 θ : ((ℬ [ 𝒥 [ j ] ]) ≤[ Kₚ ] x) holds
                 θ = ℬ [ 𝒥 [ j ] ]               ≤⟨ ⋁[ K ]-upper _ j ⟩
                     ⋁[ K ] ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆  ≡⟨ c ⁻¹             ⟩ₚ
                     x ■

                 η : (f (ℬ [ 𝒥 [ j ] ]) ≤[ Lₚ ] y) holds
                 η = f (ℬ [ 𝒥 [ j ] ])  ≤⟨ μf (ℬ [ 𝒥 [ j ] ] , x) θ ⟩ₗ
                     f x                ≤⟨ p ⟩ₗ
                     y                  ■ₗ

         † : ((⋁[ K ] ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆) ≤[ poset-of K ] g y) holds
         † = ⋁[ K ]-least ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆ (g y , ‡)
              where
               ‡ : (g y is-an-upper-bound-of ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆) holds
               ‡ i = ℬ [ 𝒥 [ i ] ]                       ≤⟨ 𝟏    ⟩
                     ⋁[ K ] ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆          ≤⟨ 𝟐    ⟩
                     ⋁[ K ] ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 y ⁆  ≡⟨ refl ⟩ₚ
                     g y                                 ■
                      where
                       𝟏 = ⋁[ K ]-upper ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆ i
                       𝟐 = ⋁[ K ]-least ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆ (u , ζ)

       † : ((⋁[ L ] ⁅ f (ℬ [ i ]) ∣ (i , _) ∶ 𝒦 y ⁆) ≤[ poset-of L ] y) holds
       † = ⋁[ L ]-least ⁅ f (ℬ [ i ]) ∣ (i , _) ∶ 𝒦 y ⁆ (y , pr₂)

       β₂ : (x ≤[ Kₚ ] g y ⇒ f x ≤[ Lₚ ] y) holds
       β₂ p =
        f x                                    ≤⟨ μf (x , g y) p                ⟩
        f (g y)                                ≡⟨ refl                          ⟩ₚ
        f (⋁[ K ] ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 y ⁆) ≡⟨ φ ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 y ⁆ ⟩ₚ
        ⋁[ L ] ⁅ f (ℬ [ i ]) ∣ (i , _) ∶ 𝒦 y ⁆ ≤⟨ †                             ⟩
        y                                      ■
         where
          open PosetReasoning Lₚ

\end{code}

\begin{code}

 aft : (𝒻 : Kₚ ─m→ Lₚ)
     → has-right-adjoint 𝒻 ⇔ is-join-preserving K L (𝒻 .pr₁) holds
 aft 𝒻 = aft-forward 𝒻 , aft-backward 𝒻

 right-adjoint-of : (K ─f→ L) → Lₚ ─m→ Kₚ
 right-adjoint-of 𝒽@(h , υ@(_ , _ , jp)) = pr₁ (aft-backward hₘ γ)
  where
   hₘ : Kₚ ─m→ Lₚ
   hₘ = h , frame-morphisms-are-monotonic K L h υ

   γ : is-join-preserving K L h holds
   γ S = ⋁[ L ]-unique ⁅ h s ∣ s ε S ⁆ (h (⋁[ K ] S)) (jp S)

 _^* : (K ─f→ L) → ⟨ L ⟩ → ⟨ K ⟩
 _^* = pr₁ ∘ right-adjoint-of

\end{code}
