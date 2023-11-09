Andrew Sneap

\begin{code}
{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Notation.Order
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.FunExt
open import UF.Powerset

open import Rationals.Type
open import Rationals.Order

module DedekindReals.Multiplication
         (fe : Fun-Ext)
         (pe : Prop-Ext)
         (pt : propositional-truncations-exist)
       where

open import Rationals.Multiplication renaming (_*_ to _ℚ*_)
open import Rationals.MinMax
open import DedekindReals.Type fe pe pt
open PropositionalTruncation pt


\end{code}

Multiplication is defined as in the HoTT Book. It reminds of interval multiplication of rational numbers.

Inhabitedness: by inhabitedness of x and y, we find values
on both sides of each. Then using the property that rationals have no
least element, then using the relevant min/max calculation we
trivially find a p which inhabits each cut of the product.

Roundedness: roundedness in the left to right direction follows
directly from density of rationals, and transitivity of rationals
order. In the right to left, transivity alone completes the proof.

\begin{code}
{-
_*_ : ℝ → ℝ → ℝ
_*_ ((Lx , Rx) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x)
    ((Ly , Ry) , inhabited-left-y , inhabited-right-y , rounded-left-y , rounded-right-y , disjoint-y , located-y)
  = (L , R) , inhabited-L , {!!} , rounded-left-L , {!!} , is-disjoint , {!!}
 where
  L : 𝓟 ℚ
  L p = (∃ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a ∈ Lx × b ∈ Rx × c ∈ Ly × d ∈ Ry × p < min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)) , ∃-is-prop
  R : 𝓟 ℚ
  R q = (∃ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a ∈ Lx × b ∈ Rx × c ∈ Ly × d ∈ Ry × max₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d) < q) , ∃-is-prop

  x-values : ∥ (Σ a ꞉ ℚ , a ∈ Lx) × (Σ b ꞉ ℚ , b ∈ Rx) ∥
  x-values = binary-choice inhabited-left-x inhabited-right-x

  y-values : ∥ (Σ c ꞉ ℚ , c ∈ Ly) × (Σ d ꞉ ℚ , d ∈ Ry) ∥
  y-values = binary-choice inhabited-left-y inhabited-right-y

  xy-values : ∥ ((Σ a ꞉ ℚ , a ∈ Lx) × (Σ b ꞉ ℚ , b ∈ Rx)) × ((Σ c ꞉ ℚ , c ∈ Ly) × (Σ d ꞉ ℚ , d ∈ Ry)) ∥
  xy-values = binary-choice x-values y-values

  inhabited-L : inhabited-left L
  inhabited-L = ∥∥-rec ∃-is-prop I xy-values
   where
    I : ((Σ a ꞉ ℚ , a ∈ Lx) × (Σ b ꞉ ℚ , b ∈ Rx)) × ((Σ c ꞉ ℚ , c ∈ Ly) × (Σ d ꞉ ℚ , d ∈ Ry))
      → ∃ p ꞉ ℚ , ∃ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a ∈ Lx × b ∈ Rx × c ∈ Ly × d ∈ Ry × p < min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)
    I (((a , a<x) , (b , x<b)) , ((c , c<y) , (d , y<d))) = II (ℚ-no-least-element (min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)))
     where
      II : Σ p ꞉ ℚ , p < min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)
         → _
      II (p , p<MIN) = ∣ p , ∣ (a , b , c , d) , a<x , x<b , c<y , y<d , p<MIN ∣ ∣

  rounded-left-L : rounded-left L
  rounded-left-L p = ltr , rtl
   where
    ltr : p ∈ L → ∃ p' ꞉ ℚ , (p < p') × p' ∈ L
    ltr p<xy = ∥∥-functor I p<xy
     where
      I : (Σ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a ∈ Lx × b ∈ Rx × c ∈ Ly × d ∈ Ry × p < min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d))
        → Σ p' ꞉ ℚ , p < p' × p' ∈ L
      I ((a , b , c , d) , a<x , x<b , c<y , y<d , p<MIN) = II (ℚ-dense fe p (min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)) p<MIN)
       where
        II : (Σ p' ꞉ ℚ , p < p' × p' < min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d))
           → Σ p' ꞉ ℚ , p < p' × p' ∈ L
        II (p' , p<p' , p'<MIN) = p' , (p<p' , ∣ (a , b , c , d) , (a<x , x<b , c<y , y<d , p'<MIN) ∣)
    rtl : ∃ p' ꞉ ℚ , (p < p') × p' ∈ L → p ∈ L
    rtl p'-info = ∥∥-rec ∃-is-prop I p'-info
     where
      I : Σ p' ꞉ ℚ , (p < p') × p' ∈ L → p ∈ L
      I (p' , p<p' , p'<xy) = ∥∥-functor II p'<xy
       where
        II : Σ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a ∈ Lx × b ∈ Rx × c ∈ Ly × d ∈ Ry × p' < min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)
           → Σ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , a ∈ Lx × b ∈ Rx × c ∈ Ly × d ∈ Ry × p  < min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)
        II ((a , b , c , d) , a<x , x<b , c<x , x<d , p'<MIN) = (a , b , c , d) , a<x , x<b , c<x , x<d , ℚ<-trans p p' (min₄ (a ℚ* c) (a ℚ* d) (b ℚ* c) (b ℚ* d)) p<p' p'<MIN

  is-disjoint : disjoint L R
  is-disjoint p q (p<xy , xy<q) = ∥∥-rec (ℚ<-is-prop p q) I (binary-choice p<xy xy<q)
   where
    I : (Σ (a₁ , b₁ , c₁ , d₁) ꞉ ℚ × ℚ × ℚ × ℚ , a₁ ∈ Lx × b₁ ∈ Rx × c₁ ∈ Ly × d₁ ∈ Ry × p < min₄ (a₁ ℚ* c₁) (a₁ ℚ* d₁) (b₁ ℚ* c₁) (b₁ ℚ* d₁))
      × (Σ (a₂ , b₂ , c₂ , d₂) ꞉ ℚ × ℚ × ℚ × ℚ , a₂ ∈ Lx × b₂ ∈ Rx × c₂ ∈ Ly × d₂ ∈ Ry × max₄ (a₂ ℚ* c₂) (a₂ ℚ* d₂) (b₂ ℚ* c₂) (b₂ ℚ* d₂) < q)
      → p < q
    I ( ((a₁ , b₁ , c₁ , d₁) , a₁<x , x<b₁ , c₁<x , x<d₁ , p<MIN₁) ,
        ((a₂ , b₂ , c₂ , d₂) , a₂<x , x<b₂ , c₂<x , x<d₂ , MAX₁<q) )
     = ℚ<-≤-trans fe p MIN₂ q p<MIN₂ (ℚ≤-trans fe MIN₂ MAX₂ q MIN₂≤MAX₂ MAX₂≤q)
     where
      a₃ b₃ c₃ d₃ : ℚ
      a₃ = max a₁ a₂
      b₃ = min b₁ b₂
      c₃ = max c₁ c₂
      d₃ = min d₁ d₂

      MIN₁ MAX₁ MIN₂ MAX₂ : ℚ
      MIN₁ = min₄ (a₁ ℚ* c₁) (a₁ ℚ* d₁) (b₁ ℚ* c₁) (b₁ ℚ* d₁)
      MAX₁ = max₄ (a₂ ℚ* c₂) (a₂ ℚ* d₂) (b₂ ℚ* c₂) (b₂ ℚ* d₂)
      MIN₂ = min₄ (a₃ ℚ* c₃) (a₃ ℚ* d₃) (b₃ ℚ* c₃) (b₃ ℚ* d₃)
      MAX₂ = max₄ (a₃ ℚ* c₃) (a₃ ℚ* d₃) (b₃ ℚ* c₃) (b₃ ℚ* d₃)

      MIN₁≤MIN₂ : MIN₁ ≤ MIN₂
      MIN₁≤MIN₂ = {!!}

      MAX₂≤MAX₁ : MAX₂ ≤ MAX₁
      MAX₂≤MAX₁ = {!!}

      p<MIN₂ : p < MIN₂
      p<MIN₂ = ℚ<-≤-trans fe p MIN₁ MIN₂ p<MIN₁ MIN₁≤MIN₂

      MIN₂≤MAX₂ : MIN₂ ≤ MAX₂
      MIN₂≤MAX₂ = min₄≤max₄ (a₃ ℚ* c₃) (a₃ ℚ* d₃) (b₃ ℚ* c₃) (b₃ ℚ* d₃)

      MAX₂<q : MAX₂ < q
      MAX₂<q = ℚ≤-<-trans fe MAX₂ MAX₁ q MAX₂≤MAX₁ MAX₁<q

      MAX₂≤q : MAX₂ ≤ q
      MAX₂≤q = ℚ<-coarser-than-≤ MAX₂ q MAX₂<q
-}
\end{code}
