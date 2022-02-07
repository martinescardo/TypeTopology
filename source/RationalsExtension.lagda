Andrew Sneap - 8th January 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) --TypeTopology

open import OrderNotation --TypeTopology
open import UF-Base -- TypeTopology
open import UF-FunExt -- TypeTopology
open import UF-PropTrunc -- TypeTopology
open import UF-Powerset --TypeTopology
open import UF-Subsingletons --TypeTopology
open import UF-Subsingletons-FunExt --TypeTopology

open import Rationals
open import RationalsOrder

module RationalsExtension
  (pe : Prop-Ext)
  (pt : propositional-truncations-exist)
  (fe : Fun-Ext)
 where

open PropositionalTruncation pt

open import DedekindReals pe pt fe 

\end{code}

The proof is simple, and doesn't require condition (1) from the jamboard.

\begin{code}

order-preserving-and-bijection-statement : (f g : ℚ → ℚ) → 𝓤₀ ̇
order-preserving-and-bijection-statement f g = ((p q : ℚ) → p < q ⇔ f p < f q)
                                             → ((r : ℚ) → (g (f r) ≡ r) × (f (g r) ≡ r))
                                             → ((p q : ℚ) → p < q ⇔ g p < g q)

order-preserving-and-bijection : (f : ℚ → ℚ)
                               → (g : ℚ → ℚ) 
                               → ((p q : ℚ) → p < q ⇔ f p < f q)
                               → ((r : ℚ) → (g (f r) ≡ r) × (f (g r) ≡ r))
                               → ((p q : ℚ) → p < q ⇔ g p < g q)
order-preserving-and-bijection f g f-preserves-order f-g-bijection = γ
 where
  γ : (p q : ℚ) → (p < q) ⇔ (g p < g q)
  γ p q = I , II
   where
    α : (g p < g q) ⇔ (f (g p) < f (g q))
    α = f-preserves-order (g p) (g q)
    
    I : p < q → g p < g q
    I l = (rl-implication α) i
     where
      i : f (g p) < f (g q)
      i = transport₂ _<_ (pr₂ (f-g-bijection p) ⁻¹) (pr₂ (f-g-bijection q) ⁻¹) l


    II : g p < g q → p < q
    II l = transport₂ _<_ (pr₂ (f-g-bijection p)) (pr₂ (f-g-bijection q)) i
     where
      i : f (g p) < f (g q)
      i = (lr-implication α) l

\end{code}
The code without the unneeded assumption. 
\begin{code}

order-preserving-and-bijection' : (f g : ℚ → ℚ) 
                                → ((p q : ℚ) → p < q ⇔ f p < f q)
                                → ((r : ℚ) → (f (g r) ≡ r))
                                → ((p q : ℚ) → p < q ⇔ g p < g q)
order-preserving-and-bijection' f g f-preserves-order f-g-bijection = γ
 where
  γ : (p q : ℚ) → (p < q) ⇔ (g p < g q)
  γ p q = I , II
   where
    α : (g p < g q) ⇔ (f (g p) < f (g q))
    α = f-preserves-order (g p) (g q)

    f-preserves-order-forward : f (g p) < f (g q) → g p < g q
    f-preserves-order-forward = rl-implication α

    f-preserves-order-backward : g p < g q → f (g p) < f (g q)
    f-preserves-order-backward = lr-implication α
    
    I : p < q → g p < g q
    I l = f-preserves-order-forward i
     where
      i : f (g p) < f (g q)
      i = transport₂ _<_ ((f-g-bijection p) ⁻¹) ((f-g-bijection q) ⁻¹) l

    II : g p < g q → p < q
    II l = transport₂ _<_ (f-g-bijection p) (f-g-bijection q) i
     where
      i : f (g p) < f (g q)
      i = f-preserves-order-backward l

f-bar : (f g : ℚ → ℚ)
      → ((p q : ℚ) → p < q ⇔ f p < f q)
      → ((r : ℚ) → (g (f r) ≡ r) × (f (g r) ≡ r))
      → ℝ → ℝ
f-bar f g f-order-preserving f-g-bijective ((L , R) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x) = (left , right) , inhabited-left' , inhabited-right' , rounded-left' , rounded-right' , disjoint' , located'
 where
  x : ℝ
  x = ((L , R) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x)
  
  left : ℚ-subset-of-propositions
  left p = (g p ∈ L) , ∈-is-prop L (g p)
  right : ℚ-subset-of-propositions
  right q = g q ∈ R , ∈-is-prop R (g q)

  inhabited-left' : inhabited-left left
  inhabited-left' = ∥∥-functor I inhabited-left-x
   where
    I : Σ p ꞉ ℚ , p ∈ L → Σ p' ꞉ ℚ , p' ∈ left 
    I (p , p-L) = (f p) , transport (_∈ L) (pr₁ (f-g-bijective p) ⁻¹) p-L

  inhabited-right' : inhabited-right right
  inhabited-right' = ∥∥-functor I inhabited-right-x
   where
    I : Σ q ꞉ ℚ , q ∈ R → Σ q' ꞉ ℚ , q' ∈ right
    I (q , q-R) = f q , transport (_∈ R) (pr₁ (f-g-bijective q) ⁻¹) q-R

  rounded-left' : rounded-left left
  rounded-left' k = I , II
   where
    I : k ∈ left → ∃ p ꞉ ℚ , (k < p) × p ∈ left
    I k-L = ∥∥-functor iii ii
     where
      i : f (g k) ≡ k
      i = pr₂ (f-g-bijective k)
      ii : ∃ q ꞉ ℚ , (g k < q) × q ∈ L
      ii = (pr₁ (rounded-left-x (g k))) k-L
      iii : Σ q ꞉ ℚ , (g k < q) × q ∈ L → Σ p ꞉ ℚ , (k < p) × p ∈ left
      iii (q , (l , q-L)) = (f q) , vii , vi
       where
        iv : (g k < q) → (f (g k) < f q)
        iv = pr₁ (f-order-preserving (g k) q)
        v : g (f q) ∈ L
        v = transport (_∈ L) (pr₁ (f-g-bijective q) ⁻¹) q-L
        vi : g (f q) ∈ L
        vi = transport (_∈ L) (pr₁ (f-g-bijective q) ⁻¹) q-L
        vii : k < f q
        vii = transport (_< f q) i (iv l)
    II : ∃ p ꞉ ℚ , (k < p) × p ∈ left → k ∈ left
    II e = ∥∥-rec (∈-is-prop left k) i e
     where
      i : Σ p ꞉ ℚ , (k < p) × p ∈ left → k ∈ left
      i (p , (l , p-L)) = iv ∣ (g p) , iii , p-L ∣
       where
        ii : (k < p) ⇔ (g k < g p)
        ii = order-preserving-and-bijection f g f-order-preserving f-g-bijective k p
        iii : g k < g p
        iii = (pr₁ ii) l
        iv : ∃ p' ꞉ ℚ , (g k < p') × p' ∈ L → g k ∈ L
        iv = pr₂ (rounded-left-x (g k))

  rounded-right' : rounded-right right
  rounded-right' k = I , II
   where
    I : k ∈ right → ∃ q ꞉ ℚ , (q < k) × q ∈ right
    I k-R = ∥∥-functor ii i
     where
      i : ∃ q ꞉ ℚ , (q < g k) × q ∈ R
      i = pr₁ (rounded-right-x (g k)) k-R
      ii : Σ p ꞉ ℚ , (p < g k) × p ∈ R → Σ q ꞉ ℚ , (q < k) × q ∈ right
      ii (p , (l , p-R)) = (f p) , (transport (f p <_) iv iii) , transport (_∈ R) (pr₁ (f-g-bijective p) ⁻¹) p-R
       where
        iii : (f p < f (g k))
        iii = (pr₁ (f-order-preserving p (g k))) l
        iv : f (g k) ≡ k
        iv = pr₂ (f-g-bijective k)
    II : ∃ q ꞉ ℚ , (q < k) × q ∈ right → k ∈ right
    II e = ∥∥-rec (∈-is-prop right k) i e
     where
      i : Σ q ꞉ ℚ , (q < k) × q ∈ right → k ∈ right
      i (q , (l , q-R)) = iv ∣ (g q) , (iii , q-R) ∣
       where
        ii : (q < k) ⇔ (g q < g k)
        ii = order-preserving-and-bijection f g f-order-preserving f-g-bijective q k
        iii : g q < g k
        iii = (pr₁ ii) l
        iv : ∃ q ꞉ ℚ , (q < g k) × q ∈ R → g k ∈ R
        iv = pr₂ (rounded-right-x (g k))

  disjoint' : disjoint left right
  disjoint' p q l = (pr₂ I) II
   where
    I : (p < q) ⇔ (g p < g q)
    I = order-preserving-and-bijection f g f-order-preserving f-g-bijective p q
    II : g p < g q
    II = disjoint-x (g p) (g q) l
    
  located' : located left right
  located' p q l = III
   where
    I : (p < q) ⇔ (g p < g q)
    I = order-preserving-and-bijection f g f-order-preserving f-g-bijective p q
    II : p < q → g p < g q
    II = pr₁ I
    III : g p ∈ L ∨ g q ∈ R
    III = located-x (g p) (g q) (II l)

diagram-commutes : (f g : ℚ → ℚ) 
                 → (f-order-preserving : ((p q : ℚ) → p < q ⇔ f p < f q))
                 → (f-g-bijective : ((r : ℚ) → (g (f r) ≡ r) × (f (g r) ≡ r)))
                 → (q : ℚ) → (f-bar f g f-order-preserving f-g-bijective ∘ embedding-ℚ-to-ℝ) q ≡ (embedding-ℚ-to-ℝ ∘ f) q
diagram-commutes f g f-order-preserving f-g-bijective q = ℝ-equality' ((f-bar f g f-order-preserving f-g-bijective ∘ embedding-ℚ-to-ℝ) q) ((embedding-ℚ-to-ℝ ∘ f) q) I II III IV
 where
  I : (a : ℚ) → g a < q → a < f q 
  I a b = transport (_< f q) ii i
   where
    i : f (g a) < f q
    i = (pr₁ (f-order-preserving (g a) q)) b
    ii : f (g a) ≡ a
    ii = pr₂ (f-g-bijective a)
  II : (a : ℚ) → a < f q → g a < q
  II a b = transport (g a <_) ii i
   where
    i : g a < g (f q)
    i = (pr₁ (order-preserving-and-bijection f g f-order-preserving f-g-bijective a (f q))) b
    ii : g (f q) ≡ q
    ii = pr₁ (f-g-bijective q)
  III : (a : ℚ) → q < g a → f q < a
  III a b = transport (f q <_) ii i
   where
    i : f q < f (g a)
    i = (pr₁ (f-order-preserving q (g a))) b
    ii : f (g a) ≡ a
    ii = pr₂ (f-g-bijective a)
  IV : (a : ℚ) → f q < a → q < g a
  IV a b = transport (_< g a) ii i
   where
    i : g (f q) < g a
    i = (pr₁ (order-preserving-and-bijection f g f-order-preserving f-g-bijective (f q) a)) b
    ii : g (f q) ≡ q
    ii = pr₁ (f-g-bijective q)

open import RationalsAddition

ℚ-succ : ℚ → ℚ 
ℚ-succ q = q + 1ℚ

open import RationalsNegation

ℚ-pred : ℚ → ℚ
ℚ-pred q = q - 1ℚ

this : (p : ℚ) → p + 1ℚ + -1ℚ ≡ p
this p =   p + 1ℚ + -1ℚ   ≡⟨ ℚ+-assoc fe p 1ℚ (- 1ℚ) ⟩
           p + (1ℚ - 1ℚ)  ≡⟨ ap (p +_) (ℚ-inverse-sum-to-zero fe 1ℚ) ⟩
           p + 0ℚ         ≡⟨ ℚ-zero-right-neutral fe p ⟩ p ∎

ℚ-succ-ext : ℝ → ℝ
ℚ-succ-ext = f-bar ℚ-succ ℚ-pred I II
 where
  I : (p q : ℚ) → (p < q) ⇔ (ℚ-succ p < ℚ-succ q)
  I p q = i , ii
   where
    i : p < q → ℚ-succ p < ℚ-succ q
    i l = ℚ<-addition-preserves-order p q 1ℚ l
    ii : ℚ-succ p < ℚ-succ q → p < q
    ii l = transport₂ _<_ iv v iii
     where
      iii : (p + 1ℚ + (- 1ℚ)) < (q + 1ℚ + (- 1ℚ))
      iii = ℚ<-addition-preserves-order (p + 1ℚ) (q + 1ℚ) (- 1ℚ) l
      iv : p + 1ℚ + (-1ℚ) ≡ p
      iv = this p
      v : (q + 1ℚ + (- 1ℚ)) ≡ q
      v =  this q
  II : (r : ℚ) → (ℚ-pred (ℚ-succ r) ≡ r) × (ℚ-succ (ℚ-pred r) ≡ r)
  II r = i , ii
   where
    i : ℚ-pred (ℚ-succ r) ≡ r
    i = this r
    ii : ℚ-succ (ℚ-pred r) ≡ r
    ii = ℚ-succ (ℚ-pred r) ≡⟨ by-definition ⟩
         r - 1ℚ + 1ℚ       ≡⟨ ℚ+-assoc fe r (- 1ℚ) 1ℚ ⟩
         r + ((- 1ℚ) + 1ℚ) ≡⟨ ap (r +_) (ℚ+-comm (- 1ℚ) 1ℚ) ⟩
         r + (1ℚ + (- 1ℚ)) ≡⟨ ap (r +_) (ℚ-inverse-sum-to-zero fe 1ℚ) ⟩
         r + 0ℚ ≡⟨ ℚ-zero-right-neutral fe r ⟩
         r ∎

{-
single-extension : (f : ℚ → ℝ) → (ℝ → ℝ)
single-extension f = {!!}

embed : (ℚ → ℚ) → (ℝ → ℝ) 
embed = single-extension ∘ (embedding-ℚ-to-ℝ ∘_)
-}

