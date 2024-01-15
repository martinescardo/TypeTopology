Andrew Sneap, April 2021 - January 2022

In this file, I prove that the Reals are arithmetically located.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Notation.Order
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Powerset
open import UF.Subsingletons
open import Naturals.Properties
open import Naturals.Order
open import Rationals.Type
open import Rationals.Abs
open import Rationals.Addition
open import Rationals.Multiplication
open import Rationals.Negation
open import Rationals.Order
open import Rationals.Positive hiding (_*_)

module DedekindReals.Properties
  (fe : Fun-Ext)
  (pe : Prop-Ext)
  (pt : propositional-truncations-exist)
 where
open import DedekindReals.Type fe pe pt
open import MetricSpaces.Rationals fe pe pt
open import Rationals.Limits fe pe pt

open PropositionalTruncation pt

trans→disjoint : (L R : 𝓟 ℚ) → disjoint L R → (q : ℚ) → ¬ (q ∈ L × q ∈ R)
trans→disjoint L R d q (q∈L , q∈R) = ℚ<-irrefl q γ
 where
  γ : q < q
  γ = d q q (q∈L , q∈R)

disjoint→trans : (L R : 𝓟 ℚ)
               → located L R → ((q : ℚ)
               → ¬ (q ∈ L × q ∈ R))
               → disjoint L R
disjoint→trans L R loc dis p q (p∈L , q∈R) = cases₃ γ₁ γ₂ γ₃ I
 where
  I : (p < q) ∔ (p ＝ q) ∔ (q < p)
  I = ℚ-trichotomous p q

  γ₁ : p < q → p < q
  γ₁ = id

  γ₂ : p ＝ q → p < q
  γ₂ e = 𝟘-elim (dis p (p∈L , p∈R))
   where
    p∈R : p ∈ R
    p∈R = transport (_∈ R) (e ⁻¹) q∈R

  γ₃ : q < p → p < q
  γ₃ l = 𝟘-elim (∥∥-rec 𝟘-is-prop γ II)
   where
    II : (q ∈ L) ∨ (p ∈ R)
    II = loc q p l

    γ : ¬ ((q ∈ L) ∔ (p ∈ R))
    γ (inl q∈L) = dis q (q∈L , q∈R)
    γ (inr p∈R) = dis p (p∈L , p∈R)

ℝ-arithmetically-located : (x : ℝ)
                         → (ε : ℚ₊)
                         → ∃ (u , v) ꞉ ℚ × ℚ , (u < x < v) × (v - u < ε)
ℝ-arithmetically-located x ε₊@(ε , 0<ε) = ∥∥-rec ∃-is-prop γ I
 where
  I : ∥ (Σ p ꞉ ℚ , p < x) × (Σ q ꞉ ℚ , x < q) ∥
  I = binary-choice (inhabited-from-real-L x) (inhabited-from-real-R x)

  γ : (Σ p ꞉ ℚ , p < x) × (Σ q ꞉ ℚ , x < q)
    → ∃ (u , v) ꞉ ℚ × ℚ , (u < x < v) × (v - u < ε)
  γ ((p , p<x) , (q , x<q)) = γ₁ n p q p<x x<q II l₂
   where
    p<q : p < q
    p<q = disjoint-from-real x p q (p<x , x<q)

    l₁ : 0ℚ < q - p
    l₁ = ℚ<-difference-positive p q p<q

    II : _
    II = trisect p q p<q

    III : Σ n ꞉ ℕ , (⟨2/3⟩^ n) * (q - p) < ε₊
    III = ⟨2/3⟩^n<ε-consequence (ε , 0<ε) (q - p , l₁)
    n = pr₁ III
    l₂ = pr₂ III

    γ₁ : (n : ℕ) → (p q : ℚ) → p < x → x < q
       → Σ (u , v) ꞉ ℚ × ℚ , (p < u) × (u < v) × (v < q)
                           × (q - u ＝ 2/3 * (q - p))
                           × (v - p ＝ 2/3 * (q - p))
       → (⟨2/3⟩^ n) * (q - p) < ε
       → ∃ (u , v) ꞉ ℚ × ℚ , (u < x < v) × (v - u < ε)
    γ₁ 0 p q p<x x<q ((u , v) , p<u , u<v , v<q , e₁ , e₂) l
     = ∣ (p , q) , (p<x , x<q) , (transport (_< ε) e₃ l) ∣
     where
      e₃ : 1ℚ * (q - p) ＝ q - p
      e₃ = ℚ-mult-left-id (q - p)
    γ₁ (succ n) p q p<x x<q ((u , v) , p<u , u<v , v<q , e₁ , e₂) l
     = ∨-elim ∃-is-prop γ₂ γ₃ IV
     where
      IV : (u < x) ∨ (x < v)
      IV = ℝ-locatedness x u v u<v

      γ₂ : (u < x) → ∃ (u , v) ꞉ ℚ × ℚ , (u < x < v) × (v - u < ε)
      γ₂ u<x = γ₁ n u q u<x x<q V (transport (_< ε) α l)
       where
        u<q : u < q
        u<q = disjoint-from-real x u q (u<x , x<q)

        V : _
        V = trisect u q u<q

        α : (⟨2/3⟩^ succ n) * (q - p) ＝ (⟨2/3⟩^ n) * (q - u)
        α = (⟨2/3⟩^ succ n) * (q - p)    ＝⟨ ap (_* (q - p)) (⟨2/3⟩-to-mult n) ⟩
            (⟨2/3⟩^ n) * 2/3 * (q - p)   ＝⟨ ℚ*-assoc (⟨2/3⟩^ n) 2/3 (q - p)   ⟩
            (⟨2/3⟩^ n) * (2/3 * (q - p)) ＝⟨ ap ((⟨2/3⟩^ n) *_) (e₁ ⁻¹)        ⟩
            (⟨2/3⟩^ n) * (q - u)         ∎

      γ₃ : (x < v) → ∃ (u , v) ꞉ ℚ × ℚ , (u < x < v) × (v - u < ε)
      γ₃ x<v = γ₁ n p v p<x x<v V (transport (_< ε) α l)
       where
        p<v : p < v
        p<v = disjoint-from-real x p v (p<x , x<v)

        V : _
        V = trisect p v p<v

        α : (⟨2/3⟩^ succ n) * (q - p) ＝ (⟨2/3⟩^ n) * (v - p)
        α = (⟨2/3⟩^ succ n) * (q - p)    ＝⟨ ap (_* (q - p)) (⟨2/3⟩-to-mult n) ⟩
            (⟨2/3⟩^ n) * 2/3 * (q - p)   ＝⟨ ℚ*-assoc (⟨2/3⟩^ n) 2/3 (q - p)   ⟩
            (⟨2/3⟩^ n) * (2/3 * (q - p)) ＝⟨ ap ((⟨2/3⟩^ n) *_) (e₂ ⁻¹)        ⟩
            (⟨2/3⟩^ n) * (v - p)         ∎

ℝ-arithmetically-located' : (x : ℝ)
                          → ((ε , _) : ℚ₊)
                          → ∃ (u , v) ꞉ ℚ × ℚ , (u < x < v) × (0ℚ < (v - u) < ε)
ℝ-arithmetically-located' x (ε , 0<ε) = ∥∥-functor γ₂ γ₁

 where
  γ₁ : ∃ (u , v) ꞉ ℚ × ℚ , (u < x < v) × (v - u < ε)
  γ₁ = ℝ-arithmetically-located x (ε , 0<ε)

  γ₂ : Σ (u , v) ꞉ ℚ × ℚ , (u < x < v) × (v - u < ε)
     → Σ (u , v) ꞉ ℚ × ℚ , (u < x < v) × (0ℚ < (v - u) < ε)
  γ₂ ((u , v) , u<x<v , l) = (u , v) , u<x<v , l' , l
   where
    u<v : u < v
    u<v = disjoint-from-real x u v u<x<v

    l' : 0ℚ < v - u
    l' = ℚ<-difference-positive u v u<v

\end{code}
