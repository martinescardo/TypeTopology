Ayberk Tosun, 1 March 2022.

\begin{code}

{-# OPTIONS --without-K --safe --auto-inline #-}

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

open Locale

\end{code}

\begin{code}

module AdjointFunctorTheorem (X : Locale 𝓤' 𝓥 𝓥)
                             (Y : Locale 𝓤  𝓥  𝓥)
                             (𝒷 : has-basis (𝒪 Y) holds) where

\end{code}

\begin{code}

 private
  𝒪Xₚ = poset-of (𝒪 X)
  𝒪Yₚ = poset-of (𝒪 Y)

 open GaloisConnectionBetween 𝒪Yₚ 𝒪Xₚ

 aft-forward : (f : 𝒪Yₚ ─m→ 𝒪Xₚ)
             → has-right-adjoint f
             → is-join-preserving (𝒪 Y) (𝒪 X) (f .pr₁) holds
 aft-forward (f , μ) (ℊ@(g , _) , p) S =
  ⋁[ 𝒪 X ]-unique ⁅ f s ∣ s ε S ⁆ (f (⋁[ 𝒪 Y ] S)) (β , γ)
   where
    open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)
    open Joins (λ x y → x ≤[ poset-of (𝒪 Y) ] y)
     using () renaming (_is-an-upper-bound-of_ to _is-a-ub-of_)

    β : (f (⋁[ 𝒪 Y ] S) is-an-upper-bound-of ⁅ f s ∣ s ε S ⁆) holds
    β i = μ (S [ i ] , ⋁[ 𝒪 Y ] S) (⋁[ 𝒪 Y ]-upper S i)

    γ : (Ɐ (u , _) ∶ upper-bound ⁅ f s ∣ s ε S ⁆ , f (⋁[ 𝒪 Y ] S) ≤[ 𝒪Xₚ ] u) holds
    γ (u , q) = pr₂ (p (⋁[ 𝒪 Y ] S) u) (⋁[ 𝒪 Y ]-least S (g u , δ))
     where
      δ : (g u is-a-ub-of S) holds
      δ i = pr₁ (p (S [ i ]) u) (q i)

\end{code}

\begin{code}

 aft-backward : (𝒻 : 𝒪Yₚ ─m→ 𝒪Xₚ)
              → is-join-preserving (𝒪 Y) (𝒪 X) (𝒻 .pr₁) holds
              → has-right-adjoint 𝒻
 aft-backward 𝒻@(f , μf) φ = ∥∥-rec (has-right-adjoint-is-prop 𝒻) γ 𝒷
  where
   open Joins (λ x y → x ≤[ poset-of (𝒪 Y) ] y)
   open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)
         using    ()
         renaming (_is-an-upper-bound-of_ to _is-an-ub-of_)

   γ : Σ ℬ ꞉ Fam 𝓥 ⟨ 𝒪 Y ⟩ , is-basis-for (𝒪 Y) ℬ → Σ ℊ ꞉ 𝒪Xₚ ─m→ 𝒪Yₚ , (𝒻 ⊣ ℊ) holds
   γ (ℬ , b) = (g , μ′) , β
    where
     𝒦 : ∣ 𝒪Xₚ ∣ₚ → 𝓥 ̇
     𝒦 y = Σ i ꞉ index ℬ , (f (ℬ [ i ]) ≤[ 𝒪Xₚ ] y) holds

     g : ∣ 𝒪Xₚ ∣ₚ → ∣ 𝒪Yₚ ∣ₚ
     g y = ⋁[ 𝒪 Y ] ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 y ⁆

     μ′ : is-monotonic 𝒪Xₚ 𝒪Yₚ g holds
     μ′ (y₁ , y₂) p =
      ⋁[ 𝒪 Y ]-least ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 y₁ ⁆ (g y₂ , ε)
        where
         open PosetReasoning 𝒪Xₚ

         ε : (g y₂ is-an-upper-bound-of ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 y₁ ⁆) holds
         ε 𝒾@(i , q) = ⋁[ 𝒪 Y ]-upper ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 y₂ ⁆ (i , †)
          where
           † : (f (ℬ [ i ]) ≤[ 𝒪Xₚ ] y₂) holds
           † = f (ℬ [ i ]) ≤⟨ q ⟩ y₁ ≤⟨ p ⟩ y₂ ■

     ℊ = g , μ′

     β : (𝒻 ⊣ ℊ) holds
     β U V = β₁ , β₂
      where
       𝒥 : Fam 𝓥 (index ℬ)
       𝒥 = pr₁ (b U)

       c : U ≡ ⋁[ 𝒪 Y ] ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆
       c = ⋁[ 𝒪 Y ]-unique ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆ U (pr₂ (b U))

       β₁ : (f U ≤[ 𝒪Xₚ ] V ⇒ U ≤[ 𝒪Yₚ ] g V) holds
       β₁ p = U                             ≡⟨ c ⟩ₚ
              ⋁[ 𝒪 Y ] ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆  ≤⟨ † ⟩
              g V                           ■
        where
         open PosetReasoning 𝒪Yₚ
         open PosetReasoning 𝒪Xₚ using () renaming (_■ to _■ₗ; _≤⟨_⟩_ to _≤⟨_⟩ₗ_)

         u = ⋁[ 𝒪 Y ] ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 V ⁆

         ζ : (u is-an-upper-bound-of ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆) holds
         ζ j = ⋁[ 𝒪 Y ]-upper ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 V ⁆ (𝒥 [ j ] , η)
                where
                 θ : ((ℬ [ 𝒥 [ j ] ]) ≤[ 𝒪Yₚ ] U) holds
                 θ = ℬ [ 𝒥 [ j ] ]                ≤⟨ ⋁[ 𝒪 Y ]-upper _ j ⟩
                     ⋁[ 𝒪 Y ] ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆ ≡⟨ c ⁻¹             ⟩ₚ
                     U ■

                 η : (f (ℬ [ 𝒥 [ j ] ]) ≤[ 𝒪Xₚ ] V) holds
                 η = f (ℬ [ 𝒥 [ j ] ])  ≤⟨ μf (ℬ [ 𝒥 [ j ] ] , U) θ ⟩ₗ
                     f U                ≤⟨ p ⟩ₗ
                     V                  ■ₗ

         † : ((⋁[ 𝒪 Y ] ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆) ≤[ poset-of (𝒪 Y) ] g V) holds
         † = ⋁[ 𝒪 Y ]-least ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆ (g V , ‡)
              where
               ‡ : (g V is-an-upper-bound-of ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆) holds
               ‡ i = ℬ [ 𝒥 [ i ] ]                         ≤⟨ 𝟏    ⟩
                     ⋁[ 𝒪 Y ] ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆          ≤⟨ 𝟐    ⟩
                     ⋁[ 𝒪 Y ] ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 V ⁆  ≡⟨ refl ⟩ₚ
                     g V                                   ■
                      where
                       𝟏 = ⋁[ 𝒪 Y ]-upper ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆ i
                       𝟐 = ⋁[ 𝒪 Y ]-least ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆ (u , ζ)

       † : ((⋁[ 𝒪 X ] ⁅ f (ℬ [ i ]) ∣ (i , _) ∶ 𝒦 V ⁆) ≤[ poset-of (𝒪 X) ] V) holds
       † = ⋁[ 𝒪 X ]-least ⁅ f (ℬ [ i ]) ∣ (i , _) ∶ 𝒦 V ⁆ (V , pr₂)

       β₂ : (U ≤[ 𝒪Yₚ ] g V ⇒ f U ≤[ 𝒪Xₚ ] V) holds
       β₂ p =
        f U                                      ≤⟨ μf (U , g V) p                ⟩
        f (g V)                                  ≡⟨ refl                          ⟩ₚ
        f (⋁[ 𝒪 Y ] ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 V ⁆) ≡⟨ φ ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 V ⁆ ⟩ₚ
        ⋁[ 𝒪 X ] ⁅ f (ℬ [ i ]) ∣ (i , _) ∶ 𝒦 V ⁆ ≤⟨ †                             ⟩
        V                                        ■
         where
          open PosetReasoning 𝒪Xₚ

\end{code}

\begin{code}

 aft : (𝒻 : 𝒪Yₚ ─m→ 𝒪Xₚ)
     → has-right-adjoint 𝒻 ⇔ is-join-preserving (𝒪 Y) (𝒪 X) (𝒻 .pr₁) holds
 aft 𝒻 = aft-forward 𝒻 , aft-backward 𝒻

 right-adjoint-of : (X ─c→ Y) → 𝒪Xₚ ─m→ 𝒪Yₚ
 right-adjoint-of 𝒽@(h , υ@(_ , _ , jp)) = pr₁ (aft-backward hₘ γ)
  where
   hₘ : 𝒪Yₚ ─m→ 𝒪Xₚ
   hₘ = h , frame-morphisms-are-monotonic (𝒪 Y) (𝒪 X) h υ

   γ : is-join-preserving (𝒪 Y) (𝒪 X) h holds
   γ S = ⋁[ 𝒪 X ]-unique ⁅ h s ∣ s ε S ⁆ (h (⋁[ 𝒪 Y ] S)) (jp S)

 _^* : (X ─c→ Y) → ⟨ 𝒪 X ⟩ → ⟨ 𝒪 Y ⟩
 _^* = pr₁ ∘ right-adjoint-of

\end{code}
