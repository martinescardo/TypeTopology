Andrew Sneap, November 2021

This file proves that a rational valued function on the rationals may
be extended to rational real valued functions on the reals, provided
that the function is strictly monotonic and has a bijection with
another rational valued function on the rationals.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan renaming (_+_ to _∔_) 

open import Notation.CanonicalMap 
open import Notation.Order 
open import UF.Base 
open import UF.FunExt 
open import UF.PropTrunc 
open import UF.Powerset 
open import UF.Subsingletons 
open import UF.Subsingletons-FunExt 

open import DedekindReals.Rationals.Rationals
open import DedekindReals.Rationals.Order

module DedekindReals.Rationals.Extension
  (pe : Prop-Ext)
  (pt : propositional-truncations-exist)
  (fe : Fun-Ext)
 where

open PropositionalTruncation pt

open import DedekindReals.Reals.Reals pe pt fe

\end{code}

We begin by proving a lemma. If f and g are bijective, and f is
strictly monotone, then g is strictly monotone.

TODO: Is it true that strictly monotone functions automatically have a
bijection?

\begin{code}

bijection-preserves-monotone : (f g : ℚ → ℚ) → 𝓤₀ ̇
bijection-preserves-monotone f g = ((p q : ℚ) → p < q ⇔ f p < f q)
                                 → ((r : ℚ) → (g (f r) ＝ r) × (f (g r) ＝ r))
                                 → ((p q : ℚ) → p < q ⇔ g p < g q)

bijective-preserves-monotone' : (f g : ℚ → ℚ) → 𝓤₀ ̇
bijective-preserves-monotone' f g = ((p q : ℚ) → p < q ⇔ f p > f q)
                                  → ((r : ℚ) → (g (f r) ＝ r) × (f (g r) ＝ r))
                                  → ((p q : ℚ) → p < q ⇔ g p > g q)

bijective-and-monotonic : (f : ℚ → ℚ)
                        → (g : ℚ → ℚ)
                        → bijection-preserves-monotone f g
bijective-and-monotonic f g f-preserves-order f-g-bijection = γ
 where
  γ : (p q : ℚ) → p < q ⇔ g p < g q
  γ p q = ltr , rtl
   where
    apply-order-preversation : g p < g q ⇔ f (g p) < f (g q)
    apply-order-preversation = f-preserves-order (g p) (g q)

    ltr : p < q → g p < g q
    ltr l = (rl-implication apply-order-preversation) i
     where
      i : f (g p) < f (g q)
      i = transport₂ _<_ (pr₂ (f-g-bijection p) ⁻¹) (pr₂ (f-g-bijection q) ⁻¹) l

    rtl : g p < g q → p < q
    rtl l = transport₂ _<_ (pr₂ (f-g-bijection p)) (pr₂ (f-g-bijection q)) i
     where
      i : f (g p) < f (g q)
      i = (lr-implication apply-order-preversation) l

bijective-and-monotonic' : (f g : ℚ → ℚ) → bijective-preserves-monotone' f g
bijective-and-monotonic' f g f-preserves-order f-g-bijection = γ
 where
  γ : (p q : ℚ) → p < q ⇔ g p > g q
  γ p q = ltr , rtl
   where
    apply-order-preservation : g q < g p ⇔ f (g q) > f (g p)
    apply-order-preservation = f-preserves-order (g q) (g p)
    
    ltr : p < q → g p > g q
    ltr l = (rl-implication apply-order-preservation) i
     where
      i : f (g q) > f (g p)
      i = transport₂ _<_ (pr₂ (f-g-bijection p) ⁻¹) (pr₂ (f-g-bijection q) ⁻¹) l
    
    rtl : g p > g q → p < q
    rtl l = transport₂ _<_ (pr₂ (f-g-bijection p)) (pr₂ (f-g-bijection q)) i
     where
      i : f (g p) < f (g q)
      i = (lr-implication apply-order-preservation) l
    
\end{code}

Now, given a monotonic function f, and a bijective function g, we construct an extension of f, which we call f̂.

Pictorially, we have the following:

                      f
   ℚ ────────────────────────────────▶ ℚ
   │                                   │           We want our extension to satisfy f̂ ∘ ι ＝ ι ∘ f
   │                                   │           This means f̂ does not change the behavour of f 
   │                                   │           for any point in the rationals.
 ι │                                   │ ι
   │                                   │
   │                                   │  
   ▼                                   ▼  
   ℝ ────────────────────────────────▶ ℝ
                      f̂


The following f→f̂ extends functions, and the is followed by diagram commutes which proves that the above diagram is satisfied.

\begin{code}

f→f̂ : (f g : ℚ → ℚ)
  → ((p q : ℚ) → p < q ⇔ f p < f q)
  → ((r : ℚ) → (g (f r) ＝ r) × (f (g r) ＝ r))
  → ℝ → ℝ
f→f̂ f g f-order-preserving f-g-bijective
 ((L , R) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x)
  = (left , right) , inhabited-left' , inhabited-right' , rounded-left' , rounded-right' , disjoint' , located'
 where
  x : ℝ
  x = ((L , R) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x)

  left : 𝓟 ℚ
  left p = (g p ∈ L) , ∈-is-prop L (g p)
  right : 𝓟 ℚ
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
      i : f (g k) ＝ k
      i = pr₂ (f-g-bijective k)
      ii : ∃ q ꞉ ℚ , g k < q × q ∈ L
      ii = (pr₁ (rounded-left-x (g k))) k-L
      iii : Σ q ꞉ ℚ , g k < q × q ∈ L → Σ p ꞉ ℚ , k < p × p ∈ left
      iii (q , (l , q-L)) = f q , vii , vi
       where
        iv : g k < q → f (g k) < f q
        iv = pr₁ (f-order-preserving (g k) q)
        v : g (f q) ∈ L
        v = transport (_∈ L) (pr₁ (f-g-bijective q) ⁻¹) q-L
        vi : g (f q) ∈ L
        vi = transport (_∈ L) (pr₁ (f-g-bijective q) ⁻¹) q-L
        vii : k < f q
        vii = transport (_< f q) i (iv l)
    II : ∃ p ꞉ ℚ , k < p × p ∈ left → k ∈ left
    II e = ∥∥-rec (∈-is-prop left k) i e
     where
      i : Σ p ꞉ ℚ , k < p × p ∈ left → k ∈ left
      i (p , (l , p-L)) = iv ∣ (g p) , iii , p-L ∣
       where
        ii : k < p ⇔ g k < g p
        ii = bijective-and-monotonic f g f-order-preserving f-g-bijective k p
        iii : g k < g p
        iii = (pr₁ ii) l
        iv : ∃ p' ꞉ ℚ , g k < p' × p' ∈ L → g k ∈ L
        iv = pr₂ (rounded-left-x (g k))

  rounded-right' : rounded-right right
  rounded-right' k = I , II
   where
    I : k ∈ right → ∃ q ꞉ ℚ , q < k × q ∈ right
    I k-R = ∥∥-functor ii i
     where
      i : ∃ q ꞉ ℚ , q < g k × q ∈ R
      i = pr₁ (rounded-right-x (g k)) k-R
      ii : Σ p ꞉ ℚ , p < g k × p ∈ R → Σ q ꞉ ℚ , (q < k) × q ∈ right
      ii (p , (l , p-R)) = (f p) , (transport (f p <_) iv iii) , transport (_∈ R) (pr₁ (f-g-bijective p) ⁻¹) p-R
       where
        iii : f p < f (g k)
        iii = (pr₁ (f-order-preserving p (g k))) l
        iv : f (g k) ＝ k
        iv = pr₂ (f-g-bijective k)
    II : ∃ q ꞉ ℚ , q < k × q ∈ right → k ∈ right
    II e = ∥∥-rec (∈-is-prop right k) i e
     where
      i : Σ q ꞉ ℚ , q < k × q ∈ right → k ∈ right
      i (q , (l , q-R)) = iv ∣ (g q) , (iii , q-R) ∣
       where
        ii : q < k ⇔ g q < g k
        ii = bijective-and-monotonic f g f-order-preserving f-g-bijective q k
        iii : g q < g k
        iii = (pr₁ ii) l
        iv : ∃ q ꞉ ℚ , q < g k × q ∈ R → g k ∈ R
        iv = pr₂ (rounded-right-x (g k))

  disjoint' : disjoint left right
  disjoint' p q l = (pr₂ I) II
   where
    I : p < q ⇔ g p < g q
    I = bijective-and-monotonic f g f-order-preserving f-g-bijective p q
    II : g p < g q
    II = disjoint-x (g p) (g q) l

  located' : located left right
  located' p q l = III
   where
    I : p < q ⇔ g p < g q
    I = bijective-and-monotonic f g f-order-preserving f-g-bijective p q
    II : p < q → g p < g q
    II = pr₁ I
    III : g p ∈ L ∨ g q ∈ R
    III = located-x (g p) (g q) (II l)

diagram-commutes : (f g : ℚ → ℚ)
                 → (f-order-preserving : ((p q : ℚ) → p < q ⇔ f p < f q))
                 → (f-g-bijective : ((r : ℚ) → (g (f r) ＝ r) × (f (g r) ＝ r)))
                 → (q : ℚ)
                 → (f→f̂ f g f-order-preserving f-g-bijective ∘ ι) q ＝ (ι ∘ f) q
diagram-commutes f g f-order-preserving f-g-bijective q = ℝ-equality' ((f̂ ∘ ι) q) ((ι ∘ f) q) I II III IV
 where
  f̂ : ℝ → ℝ
  f̂ = f→f̂ f g f-order-preserving f-g-bijective
  
  I : (a : ℚ) → g a < q → a < f q
  I a b = transport (_< f q) ii i
   where
    i : f (g a) < f q
    i = (pr₁ (f-order-preserving (g a) q)) b
    ii : f (g a) ＝ a
    ii = pr₂ (f-g-bijective a)
  II : (a : ℚ) → a < f q → g a < q
  II a b = transport (g a <_) ii i
   where
    i : g a < g (f q)
    i = (pr₁ (bijective-and-monotonic f g f-order-preserving f-g-bijective a (f q))) b
    ii : g (f q) ＝ q
    ii = pr₁ (f-g-bijective q)
  III : (a : ℚ) → q < g a → f q < a
  III a b = transport (f q <_) ii i
   where
    i : f q < f (g a)
    i = (pr₁ (f-order-preserving q (g a))) b
    ii : f (g a) ＝ a
    ii = pr₂ (f-g-bijective a)
  IV : (a : ℚ) → f q < a → q < g a
  IV a b = transport (_< g a) ii i
   where
    i : g (f q) < g a
    i = (pr₁ (bijective-and-monotonic f g f-order-preserving f-g-bijective (f q) a)) b
    ii : g (f q) ＝ q
    ii = pr₁ (f-g-bijective q)
\end{code}

With the monotonic extension theorem, here is an example of extending
the function which adds 1 to a rational.

\begin{code}

open import DedekindReals.Rationals.Addition
open import DedekindReals.Rationals.Negation

ℚ-succ : ℚ → ℚ
ℚ-succ q = q + 1ℚ

ℚ-pred : ℚ → ℚ
ℚ-pred q = q - 1ℚ

<-ℚ-succ : (p q : ℚ) → p < q ⇔ ℚ-succ p < ℚ-succ q
<-ℚ-succ p q = i , ii
 where
  i : p < q → ℚ-succ p < ℚ-succ q
  i l = ℚ<-addition-preserves-order p q 1ℚ l
  ii : ℚ-succ p < ℚ-succ q → p < q
  ii l = transport₂ _<_ iv v iii
   where
    iii : p + 1ℚ - 1ℚ < q + 1ℚ - 1ℚ
    iii = ℚ<-addition-preserves-order (p + 1ℚ) (q + 1ℚ) (- 1ℚ) l
    iv : p + 1ℚ - 1ℚ ＝ p
    iv = ℚ+-assoc fe p 1ℚ (- 1ℚ) ∙ ℚ-inverse-intro fe p 1ℚ ⁻¹
    v : q + 1ℚ - 1ℚ ＝ q
    v =  ℚ+-assoc fe q 1ℚ (- 1ℚ) ∙ ℚ-inverse-intro fe q 1ℚ ⁻¹

ℚ-succ-pred : (r : ℚ) → (ℚ-pred (ℚ-succ r) ＝ r) × (ℚ-succ (ℚ-pred r) ＝ r)
ℚ-succ-pred r = i , ii
 where
  i : ℚ-pred (ℚ-succ r) ＝ r
  i = ℚ+-assoc fe r 1ℚ (- 1ℚ) ∙ ℚ-inverse-intro fe r 1ℚ ⁻¹ 
  ii : ℚ-succ (ℚ-pred r) ＝ r
  ii = ℚ-succ (ℚ-pred r) ＝⟨ by-definition                           ⟩
       r - 1ℚ + 1ℚ       ＝⟨ ℚ+-assoc fe r (- 1ℚ) 1ℚ                 ⟩
       r + ((- 1ℚ) + 1ℚ) ＝⟨ ap (r +_) (ℚ+-comm (- 1ℚ) 1ℚ)           ⟩
       r + (1ℚ - 1ℚ)     ＝⟨ ap (r +_) (ℚ-inverse-sum-to-zero fe 1ℚ) ⟩
       r + 0ℚ            ＝⟨ ℚ-zero-right-neutral fe r ⟩
       r                 ∎

ℝ-succ : ℝ → ℝ
ℝ-succ = f→f̂ ℚ-succ ℚ-pred <-ℚ-succ ℚ-succ-pred

ℚ-succ-behaviour-preserved : (q : ℚ) → ℝ-succ (ι q) ＝ ι (ℚ-succ q)
ℚ-succ-behaviour-preserved q = diagram-commutes ℚ-succ ℚ-pred <-ℚ-succ ℚ-succ-pred q 

\end{code}

With this, we have a function which adds one to a real number, which
agrees with the function that adds one to a rational. Moreover, we
didn't have to write the proof that this function produces a real (by
proving that the output satisifies the properties of a real, because
this is taken care of by the f→f̂ function.

TODO: I would like to be able to show that the extended function
satisfies certain properties. For example, proving that x < x + 1 for
any real.

\begin{code}

open import DedekindReals.Reals.Order pe pt fe

ℚ-succ-preserves-order : (p : ℚ) → p < ℚ-succ p
ℚ-succ-preserves-order p = ℚ<-addition-preserves-order'' fe p 1ℚ (0 , refl)

test : (x : ℚ) -> (ι x) < ℝ-succ (ι x) -- With Todds Help
test x = transport (ι x <_) (ℚ-succ-behaviour-preserved x ⁻¹)
           (embedding-preserves-order x (ℚ-succ x)
             (ℚ-succ-preserves-order x)) 

bijection-preserves-monotone-multi : (f g : ℚ → ℚ → ℚ) → 𝓤₀ ̇
bijection-preserves-monotone-multi f g = ((p q r : ℚ) → p < q ⇔ f p r < f q r)
                                       → ((p q : ℚ) → (g (f p q) q ＝ p) × (f (g p q) q ＝ p))
                                       → ((p q r : ℚ) → p < q ⇔ g p r < g q r)

bijection-preserves-monotone-multi-proof : (f g : ℚ → ℚ → ℚ) → bijection-preserves-monotone-multi f g
bijection-preserves-monotone-multi-proof f g f-preserves-order f-g-bijection = γ
 where
  γ : (p q r : ℚ) → p < q ⇔ g p r < g q r
  γ p q r = ltr , rtl
   where
    apply-order-preversation :  g p r < g q r ⇔ f (g p r) r < f (g q r) r
    apply-order-preversation = f-preserves-order (g p r) (g q r) r
    
    ltr : p < q → g p r < g q r
    ltr l = (rl-implication apply-order-preversation) i
     where
      i :  f (g p r) r < f (g q r) r
      i = transport₂ _<_ (pr₂ (f-g-bijection p r) ⁻¹) (pr₂ (f-g-bijection q r) ⁻¹) l
    rtl : g p r < g q r → p < q
    rtl l = transport₂ _<_ (pr₂ (f-g-bijection p r)) (pr₂ (f-g-bijection q r)) i
     where
      i : f (g p r) r < f (g q r) r
      i = (lr-implication apply-order-preversation) l

open import DedekindReals.Reals.Properties fe pt pe
{-
composition-of-monotonic-functions : (f g : ℚ → ℚ → ℚ)
                                   → ((p q r : ℚ) → p < q ⇔ f p r < f q r)
                                   → ((p q : ℚ) → (g (f p q) q ＝ p) × (f (g p q) q ＝ p))
                                   → ℝ → ℝ → ℝ 
composition-of-monotonic-functions f g f-preserves-order f-g-bijective x y = (L , R) , inhabited-left' , inhabited-right' , rounded-left' , rounded-right' , disjoint' , located'
 where
  L : 𝓟 ℚ
  L p = (∃ a ꞉ ℚ , a < x × g p a < y) , ∃-is-prop
   
  R : 𝓟 ℚ
  R q = (∃ b ꞉ ℚ , x < b × y < g q b) , ∃-is-prop

  inhabited-left' : inhabited-left L
  inhabited-left' = ∥∥-rec ∃-is-prop I (binary-choice (inhabited-from-real-L x) (inhabited-from-real-L y))
   where
    I : (Σ a ꞉ ℚ , a < x) × (Σ b ꞉ ℚ , b < y) → ∃ p ꞉ ℚ , p ∈ L
    I ((a , a<x) , b , b<y) = ∣ f b a , ∣ a , (a<x , transport (_< y) (pr₁ (f-g-bijective b a) ⁻¹) b<y) ∣ ∣

  inhabited-right' : inhabited-right R
  inhabited-right' = ∥∥-functor I (binary-choice (inhabited-from-real-R x) (inhabited-from-real-R y))
   where
    I : (Σ a ꞉ ℚ , x < a) × (Σ b ꞉ ℚ , y < b) → Σ q ꞉ ℚ , q ∈ R
    I ((a , x<a) , b , y<b) = f b a ,  ∣ a , x<a , transport (y <_) (pr₁ (f-g-bijective b a) ⁻¹) y<b  ∣

  rounded-left' : rounded-left L
  rounded-left' k = ltr , rtl
   where
    ltr : k ∈ L → ∃ p ꞉ ℚ , k < p × p ∈ L
    ltr k<L = ∥∥-rec ∃-is-prop I k<L
     where
      I : Σ a ꞉ ℚ , a < x × g k a < y → ∃ p ꞉ ℚ , k < p × p ∈ L
      I (a , a<x , gka<y) = ∥∥-functor II ((rounded-left-b (lower-cut-of y) (rounded-from-real-L y) (g k a) gka<y))
       where
        II : (Σ t ꞉ ℚ , g k a < t × t < y) → Σ k' ꞉ ℚ , k < k' × (∃ a ꞉ ℚ , a < x × g k' a < y)
        II (t , l₁ , t<y) = f t a , goal₁ , ∣ a , a<x , goal₂ ∣ 
         where
          III :  f (g k a) a < f t a
          III = (pr₁ (f-preserves-order (g k a) t a)) l₁
          IV : f (g k a) a ＝ k
          IV = pr₂ (f-g-bijective k a)
          V : g (f t a) a ＝ t
          V = pr₁ (f-g-bijective t a)
          goal₁ : k < (f t a)
          goal₁ = transport (_< f t a) IV III
          goal₂ :  g (f t a) a < y
          goal₂ = transport (_< y) (V ⁻¹) t<y
     
    rtl : ∃ p ꞉ ℚ , k < p × p ∈ L → k ∈ L
    rtl = ∥∥-rec ∃-is-prop I
     where
      I : Σ p ꞉ ℚ , k < p × p ∈ L → k ∈ L
      I (p , k<p , p∈L) = ∥∥-functor II p∈L
       where
        II : (Σ a ꞉ ℚ , a < x × g p a < y) → Σ a ꞉ ℚ , a < x × g k a < y
        II (a , a<x , l₁) = a , a<x , rounded-left-c (lower-cut-of y) (rounded-from-real-L y) (g k a) (g p a) ((pr₁ III) k<p) l₁
         where
          III : k < p ⇔ g k a < g p a
          III = bijection-preserves-monotone-multi-proof f g f-preserves-order f-g-bijective k p a

  rounded-right' : rounded-right R
  rounded-right' k = ltr , rtl
   where
    ltr : k ∈ R → ∃ q ꞉ ℚ , q < k × q ∈ R
    ltr = ∥∥-rec ∃-is-prop I
     where
      I : Σ a ꞉ ℚ , x < a × y < g k a → ∃ q ꞉ ℚ , q < k × q ∈ R
      I (a , x<a , y<gka) = ∥∥-functor II (rounded-right-b (upper-cut-of y) (rounded-from-real-R y) (g k a) y<gka) 
       where
        II : Σ t ꞉ ℚ , t < g k a × y < t → Σ k' ꞉ ℚ , k' < k × k' ∈ R
        II (t , t<gka , y<t) = f t a , goal₁ , ∣ a , x<a , goal₂ ∣
         where
          III : f t a < f (g k a) a
          III = (pr₁ (f-preserves-order t (g k a) a)) t<gka
          IV : f (g k a) a ＝ k
          IV = pr₂ (f-g-bijective k a)
          V : g (f t a) a ＝ t
          V = pr₁ (f-g-bijective t a)
          
          goal₁ : f t a < k
          goal₁ = transport (f t a <_) IV III 
          goal₂ : y < (g (f t a) a)
          goal₂ = transport (y <_) (V ⁻¹) y<t
          
    rtl : ∃ q ꞉ ℚ , q < k × q ∈ R → k ∈ R
    rtl = ∥∥-rec ∃-is-prop I
     where
      I : Σ q ꞉ ℚ , q < k × q ∈ R → k ∈ R
      I (q , q<k , q∈R) = ∥∥-functor II q∈R
       where
        II : (Σ a ꞉ ℚ , x < a × y < g q a) → Σ a ꞉ ℚ , x < a × y < g k a
        II (a , x<a , l₁) = a , x<a , rounded-right-c (upper-cut-of y) (rounded-from-real-R y) (g q a) (g k a) (pr₁ III q<k) l₁
         where
          III : q < k ⇔ g q a < g k a
          III = bijection-preserves-monotone-multi-proof f g f-preserves-order f-g-bijective q k a

  located' : located L R
  located' = {!!}

  disjoint' : disjoint L R
  disjoint' p q (p∈L , q∈R) = ∥∥-rec (ℚ<-is-prop p q) I (binary-choice p∈L q∈R)
   where
    I : (Σ a ꞉ ℚ , a < x × g p a < y) × (Σ b ꞉ ℚ , x < b × y < g q b) → p < q
    I ((a , a<x , gpa<y) , b , x<b , y<gqb) = {!!}
     where
      II : f (g p a) b < f (g q b) b
      II = pr₁ (f-preserves-order (g p a) (g q b) b) (disjoint-from-real y (g p a) (g q b) (gpa<y , y<gqb))
      -- II : {!!}
      -- II = bijection-preserves-monotone-multi-proof f g f-preserves-order f-g-bijective p q
      
-}
{- disjoint→trans L R located' I
   where
    I : (q : ℚ) → ¬ (q ∈ L × q ∈ R)
    I q (q∈L , q∈R) = 𝟘-elim { 𝓤₀ } { 𝓤₀ } (∥∥-rec 𝟘-is-prop II (binary-choice q∈L q∈R))
     where
      II : (Σ a ꞉ ℚ , a < x × g q a < y) × (Σ b ꞉ ℚ , x < b × y < g q b) → 𝟘
      II = {!!}
  
  -}

{-
from-composition-to-reg : ℝ × (ℝ → ℝ) → (ℝ → ℝ → ℝ)
from-composition-to-reg (x , f) = λ p q → {!!}

multivariable-monotonic-function-extension : (f g : ℚ → ℚ)
                                           → ((p q : ℚ) → p < q ⇔ f p < f q)
                                           → ((r : ℚ) → (g (f r) ＝ r) × (f (g r) ＝ r))
                                           → ℝ → ℝ → ℝ
multivariable-monotonic-function-extension f g x y = {!!}
-}
{-
f→f̂ : (f g : ℚ → ℚ)
  → ((p q : ℚ) → p < q ⇔ f p < f q)
  → ((r : ℚ) → (g (f r) ＝ r) × (f (g r) ＝ r))
  → ℝ → ℝ
-}

\end{code}
