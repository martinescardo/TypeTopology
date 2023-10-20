Ian Ray, 25 July 2023.

Formalizing the auxilary notion of a delta-V-complete poset which is
sufficient for the main theorems of Section 6.2 from (link?) Tom de Jong's thesis
involving impredicativity (resizing axioms) in order theory.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import MLTT.Two-Properties
open import UF.FunExt
open import UF.PropTrunc
open import UF.Logic
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.Size
open import UF.Equiv
open import UF.Retracts
open import UF.Subsingletons-FunExt
open import UF.NotNotStablePropositions

module Posets.Delta-V-CompletePoset
 (pt : propositional-truncations-exist)
 (fe : Fun-Ext)
 (pe : Prop-Ext)
  where

open import Locales.Frame pt fe hiding (𝟚)

open import Posets.TwoElementPoset pt fe

module δ-complete-poset {𝓤 𝓦 : Universe} (𝓥 : Universe) (A : Poset 𝓤 𝓦) where

 δ : (x y : ∣ A ∣ₚ) → (P : Ω 𝓥) → (𝟙{𝓥} + P holds) → ∣ A ∣ₚ 
 δ x y P (inl _) = x
 δ x y P (inr _) = y

 _≤_ : ∣ A ∣ₚ → ∣ A ∣ₚ → Ω 𝓦
 _≤_ = rel-syntax A

 open Joins (_≤_)

 is-δ-complete : 𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺) ̇ 
 is-δ-complete = (x y : ∣ A ∣ₚ)
               → (x ≤ y) holds
               → (P : Ω 𝓥)
               → Σ s ꞉ ∣ A ∣ₚ , (s is-lub-of ((𝟙 + P holds) , (δ x y P))) holds

 sup-of-δ : is-δ-complete
          → (x y : ∣ A ∣ₚ)
          → (x ≤ y) holds
          → (P : Ω 𝓥)
          → ∣ A ∣ₚ
 sup-of-δ i x y o P = pr₁ (i x y o P)

 is-sup-of-δ : (i : is-δ-complete)
             → (x y : ∣ A ∣ₚ)
             → (o : (x ≤ y) holds)
             → (P : Ω 𝓥)
             → ((sup-of-δ i x y o P) is-lub-of ((𝟙 + P holds) , (δ x y P))) holds
 is-sup-of-δ i x y o P = pr₂ (i x y o P)

 is-ub-of-δ : (i : is-δ-complete)
            → (x y : ∣ A ∣ₚ)
            → (o : (x ≤ y) holds)
            → (P : Ω 𝓥)
            → ((sup-of-δ i x y o P) is-an-upper-bound-of ((𝟙 + P holds) , (δ x y P))) holds
 is-ub-of-δ i x y o P = pr₁ (is-sup-of-δ i x y o P)

 has-lub-cond-δ : (i : is-δ-complete)
                → (x y : ∣ A ∣ₚ)
                → (o : (x ≤ y) holds)
                → (P : Ω 𝓥)
                → ((u , _) : upper-bound ((𝟙 + P holds) , (δ x y P))) → ((sup-of-δ i x y o P) ≤ u) holds
 has-lub-cond-δ i x y o P = pr₂ (is-sup-of-δ i x y o P)

 not-P-x-＝-sup-δ : (i : is-δ-complete)
                  → (x y : ∣ A ∣ₚ)
                  → (o : (x ≤ y) holds)
                  → (P : Ω 𝓥)
                  → ¬ (P holds)
                  → x ＝ sup-of-δ i x y o P
 not-P-x-＝-sup-δ i x y o P not-P = ≤-is-antisymmetric A x-≤-sup sup-≤-x
  where
   x-≤-sup : (x ≤ sup-of-δ i x y o P) holds
   x-≤-sup = is-ub-of-δ i x y o P (inl ⋆)
   x-is-ub : (x is-an-upper-bound-of ((𝟙 + (P holds)) , δ x y P)) holds
   x-is-ub (inl ⋆) = ≤-is-reflexive A x
   x-is-ub (inr in-P) = 𝟘-induction (not-P in-P)
   sup-≤-x : (sup-of-δ i x y o P ≤ x) holds
   sup-≤-x = has-lub-cond-δ i x y o P (x , x-is-ub)

 P-y-＝-sup-δ : (i : is-δ-complete)
              → (x y : ∣ A ∣ₚ)
              → (o : (x ≤ y) holds)
              → (P : Ω 𝓥)
              → P holds
              → y ＝ sup-of-δ i x y o P
 P-y-＝-sup-δ i x y o P in-P = ≤-is-antisymmetric A y-≤-sup sup-≤-y
  where
   y-≤-sup : (y ≤ sup-of-δ i x y o P) holds
   y-≤-sup = is-ub-of-δ i x y o P (inr in-P)
   y-is-ub : (y is-an-upper-bound-of ((𝟙 + (P holds)) , δ x y P)) holds
   y-is-ub (inl ⋆) = o
   y-is-ub (inr in-P) = ≤-is-reflexive A y
   sup-≤-y : (sup-of-δ i x y o P ≤ y) holds
   sup-≤-y = has-lub-cond-δ i x y o P (y , y-is-ub)
   

\end{code}

Future work: I would be nice to show that classically every poset is
δ_𝓥 complete and to provide the critical examples of δ_𝓥 complete posets
(𝓥-sup lattices, etc.) We should also show that is-δ-complete is
a subsingleton.

We now define the type of δ_𝓥 complete posets.

\begin{code}

δ-complete-Poset : (𝓤 𝓦 𝓥 : Universe) → (𝓤 ⊔ 𝓦 ⊔ 𝓥) ⁺ ̇
δ-complete-Poset 𝓤 𝓦 𝓥 = Σ A ꞉ Poset 𝓤 𝓦 , is-δ-complete A
 where
  open δ-complete-poset 𝓥

Poset-δ : (D : δ-complete-Poset 𝓤 𝓦 𝓥) → Poset 𝓤 𝓦
Poset-δ D = pr₁ D

is-δ-complete-δ : (D : δ-complete-Poset 𝓤 𝓦 𝓥) →
 δ-complete-poset.is-δ-complete 𝓥 (Poset-δ D)
is-δ-complete-δ D = pr₂ D

\end{code}

\begin{code}

module non-trivial-posets {𝓤  𝓦 : Universe} (A : Poset 𝓤 𝓦) where
 is-non-trivial-poset : 𝓤 ⊔ 𝓦 ̇
 is-non-trivial-poset =  Σ x ꞉ ∣ A ∣ₚ , ( Σ y ꞉ ∣ A ∣ₚ , (x ≤[ A ] y) holds × ¬ (x ＝ y))

 lower : is-non-trivial-poset → ∣ A ∣ₚ
 lower i = pr₁ i

 upper : is-non-trivial-poset → ∣ A ∣ₚ
 upper i = pr₁ (pr₂ i)

 ordering : (i : is-non-trivial-poset) → (lower i ≤[ A ] upper i) holds
 ordering i = pr₁ (pr₂ (pr₂ i))

 nequal : (i : is-non-trivial-poset) → ¬ (lower i ＝ upper i)
 nequal i = pr₂ (pr₂ (pr₂ i))

 module _ (𝓥 : Universe) (i : is-non-trivial-poset) where

  open Joins (rel-syntax A)
  open δ-complete-poset 𝓥 A
  private
   x = lower i
   y = upper i
   x-≤-y = ordering i
   x-≠-y = nequal i 

  wlem-lemma : (P : Ω 𝓥)
             → ((x is-lub-of ((𝟙 + P holds) , (δ x y P))) holds → ¬ (P holds))
               × ((y is-lub-of ((𝟙 + P holds) , (δ x y P))) holds → ¬ ¬ (P holds)) 
  pr₁ (wlem-lemma P) (x-is-ub , _) p = x-≠-y (≤-is-antisymmetric A (x-≤-y) (x-is-ub (inr p)))
  pr₂ (wlem-lemma P) (_ , y-has-lub-cond) np = x-≠-y (≤-is-antisymmetric A (x-≤-y) (y-has-lub-cond (x , x-is-ub)))
   where
    x-is-ub : (x is-an-upper-bound-of ((𝟙 + P holds) , δ x y P)) holds
    x-is-ub (inl ✯) = ≤-is-reflexive A x
    x-is-ub (inr p) = 𝟘-induction (np p)
    
\end{code}

We now show that the two element poset is δ complete only if WLEM holds.

\begin{code}

2-is-non-trivial : non-trivial-posets.is-non-trivial-poset 2-Poset
2-is-non-trivial = (₀ , ₁ , ⋆ , zero-is-not-one)

2-is-δ-complete-WLEM : {𝓥 : Universe}
                     → δ-complete-poset.is-δ-complete {𝓤₀} {𝓤₀} 𝓥 2-Poset
                     → (P : Ω 𝓥)
                     → is-decidable (¬ (P holds))
2-is-δ-complete-WLEM {𝓥} i P = decide-¬P
 where
  open Joins (rel-syntax 2-Poset)
  open δ-complete-poset 𝓥 2-Poset
  open non-trivial-posets 2-Poset  

  sup-2-exists : Σ s ꞉ ∣ 2-Poset ∣ₚ , (s is-lub-of ((𝟙 + P holds) , (δ ₀ ₁ P))) holds
  sup-2-exists = i ₀ ₁ ⋆ P

  sup-2-exists-decides : Σ s ꞉ ∣ 2-Poset ∣ₚ , (s is-lub-of ((𝟙 + P holds) , (δ ₀ ₁ P))) holds → is-decidable (¬ (P holds))
  sup-2-exists-decides (₀ , sup) = inl (pr₁ (wlem-lemma 𝓥 2-is-non-trivial P) sup)
  sup-2-exists-decides (₁ , sup) = inr (pr₂ (wlem-lemma 𝓥 2-is-non-trivial P) sup)

  decide-¬P : is-decidable (¬ (P holds))
  decide-¬P = sup-2-exists-decides sup-2-exists

\end{code}

Since non-trivial is a negated concept it only has enough strength to derive WLEM, we now introduce the stronger concept of positivity.

\begin{code}

module Positive-Posets (𝓤  𝓦  𝓥 : Universe) (A : Poset 𝓤 𝓦) where
 
 open δ-complete-poset 𝓥 A
 open Universal fe
 open PosetReasoning A
 open Joins (_≤_)

 module positive-posets (i : is-δ-complete) where

  _<_ : (x y : ∣ A ∣ₚ) → 𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺) ̇ 
  _<_ x y = (x ≤ y) holds
          × ((z : ∣ A ∣ₚ)
           → (y ≤ z) holds
           → (P : Ω 𝓥)
           → (z is-lub-of ((𝟙 + P holds) , δ x z P)) holds
           → P holds)

  order-< : {x y : ∣ A ∣ₚ} → x < y → (x ≤ y) holds
  order-< c = pr₁ c

  sup-condition : {x y : ∣ A ∣ₚ}
                → x < y
                → ((z : ∣ A ∣ₚ)
                 → (y ≤ z) holds
                 → (P : Ω 𝓥)
                 → (z is-lub-of ((𝟙 + P holds) , δ x z P)) holds
                 → P holds)
  sup-condition c = pr₂ c

  strictly-below-implies-non-trivial : (x y : ∣ A ∣ₚ)
                                     → is-δ-complete
                                     → (x < y)
                                     → (x ≤ y) holds × ¬ (x ＝ y)
  pr₁ (strictly-below-implies-non-trivial x y i c) = order-< c
  pr₂ (strictly-below-implies-non-trivial x y i c) p =
   𝟘-induction (sup-condition c y (≤-is-reflexive A y) (𝟘{𝓥} , 𝟘-is-prop {𝓥}) (y-is-ub , y-has-lub-cond))
    where
     y-is-ub : (y is-an-upper-bound-of ((𝟙 + ((𝟘 , 𝟘-is-prop) holds)) , δ x y (𝟘 , 𝟘-is-prop))) holds
     y-is-ub (inl ⋆) = order-< c

     y-has-lub-cond : (Ɐ u ꞉ (upper-bound ((𝟙 + ((𝟘 , 𝟘-is-prop) holds)) , δ x y (𝟘 , 𝟘-is-prop))) , y ≤ (pr₁ u)) holds
     y-has-lub-cond u = y ＝⟨ p ⁻¹ ⟩ₚ pr₂ u (inl ⋆)

\end{code}

We could show that if the converse holds then so does LEM in 𝓥.

\begin{code}

  transitivity-lemma₁ : (x y z : ∣ A ∣ₚ)
                       → (i : is-δ-complete)
                       → (((x ≤ y) holds × y < z) → x < z) 
  transitivity-lemma₁ x y z i (x-≤-y , y-<-z) = (≤-is-transitive A x y z x-≤-y (order-< y-<-z) , sup-cond-P)
   where
    sup-cond-P : (w : ∣ A ∣ₚ)
               → (z ≤ w) holds
               → (P : Ω 𝓥)
               → (w is-lub-of ((𝟙 + (P holds)) , δ x w P)) holds
               → P holds
    sup-cond-P w z-≤-w P (w-is-ubₓ , w-has-lub-condₓ) = sup-condition y-<-z w z-≤-w P (w-is-ub , w-has-lub-cond)
     where
      w-is-ub : (w is-an-upper-bound-of ((𝟙 + (P holds)) , δ y w P)) holds
      w-is-ub (inl ⋆) = ≤-is-transitive A y z w (order-< y-<-z) z-≤-w
      w-is-ub (inr p) = ≤-is-reflexive A w

      w-has-lub-cond : (Ɐ (u , u-is-ub) ꞉ (upper-bound ((𝟙 + (P holds)) , δ y w P)) , w ≤ u) holds 
      w-has-lub-cond (u , u-is-ub) = w-has-lub-condₓ (u , u-is-ubₓ)
       where
        u-is-ubₓ : (u is-an-upper-bound-of ((𝟙 + (P holds)) , δ x w P)) holds
        u-is-ubₓ (inl ⋆) = ≤-is-transitive A x y u (x-≤-y) (u-is-ub (inl ⋆))
        u-is-ubₓ (inr p) = u-is-ub (inr p)

  transitivity-lemma₂ : (x y z : ∣ A ∣ₚ)
                       → (i : is-δ-complete)
                        → ((x < y × (y ≤ z) holds)
                        → x < z)
  transitivity-lemma₂ x y z i (x-<-y , y-≤-z) =
   (≤-is-transitive A x y z (order-< x-<-y) y-≤-z , sup-cond-P)
    where
     sup-cond-P : (w : ∣ A ∣ₚ)
                → (z ≤ w) holds
                → (P : Ω 𝓥)
                → (w is-lub-of ((𝟙 + (P holds)) , δ x w P)) holds
                → P holds
     sup-cond-P w z-≤-w P w-is-lub = sup-condition x-<-y w (≤-is-transitive A y z w y-≤-z z-≤-w) P w-is-lub

  is-positive-poset : 𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺) ̇ 
  is-positive-poset = Σ x ꞉ ∣ A ∣ₚ , (Σ y ꞉ ∣ A ∣ₚ , x < y)

\end{code}

Next I will formalize the relevant retract lemmas.

\begin{code}

module Retract-Lemmas (𝓤  𝓦  𝓥 : Universe) (A : Poset 𝓤 𝓦) where

 open δ-complete-poset 𝓥 A
 open Universal fe
 open PosetReasoning A
 open non-trivial-posets A
 open Positive-Posets 𝓤 𝓦 𝓥 A
 open Joins (_≤_)

 is-locally-small-≤ : 𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺)  ̇
 is-locally-small-≤ = (x y : ∣ A ∣ₚ) → ((x ≤ y) holds) is 𝓥 small

 module local-smallness (l : is-locally-small-≤) where

  _≤ⱽ_ : (x y : ∣ A ∣ₚ) → 𝓥  ̇
  x ≤ⱽ y = pr₁ (l x y)

  ≤ⱽ-is-prop : (x : ∣ A ∣ₚ) → (y : ∣ A ∣ₚ) → is-prop (x ≤ⱽ y)
  ≤ⱽ-is-prop x y = equiv-to-prop (pr₂ (l x y)) (holds-is-prop (x ≤ y))

  ≤ⱽ-≃-≤ : (x y : ∣ A ∣ₚ) → x ≤ⱽ y ≃ (x ≤ y) holds
  ≤ⱽ-≃-≤ x y = pr₂ (l x y)

  ≤ⱽ-to-≤ : (x y : ∣ A ∣ₚ) → x ≤ⱽ y → (x ≤ y) holds
  ≤ⱽ-to-≤ x y =  ⌜ ≤ⱽ-≃-≤ x y ⌝

  ≤-to-≤ⱽ : (x y : ∣ A ∣ₚ) → (x ≤ y) holds → x ≤ⱽ y
  ≤-to-≤ⱽ x y = ⌜ ≤ⱽ-≃-≤ x y ⌝⁻¹

 module def-Δ (i : is-δ-complete) (x y : ∣ A ∣ₚ) (x-≤-y : (x ≤ y) holds) where

  Δ : Ω 𝓥 → ∣ A ∣ₚ
  Δ P = sup-of-δ i x y x-≤-y P

 module retract-lemma₁ (l : is-locally-small-≤) (i : is-δ-complete) (x y : ∣ A ∣ₚ) (x-≤-y : (x ≤ y) holds) where

  open local-smallness l
  open def-Δ i x y x-≤-y

  non-trivial-to-Δ-section : x ≠ y → is-section (Δ ∘ Ω¬¬-to-Ω)
  non-trivial-to-Δ-section x-≠-y = (r , H)
   where
    r : ∣ A ∣ₚ → Ω¬¬ 𝓥
    r z = ((¬ (z ≤ⱽ x) , negations-are-props fe) , ¬-is-¬¬-stable)
    f : (((p , p-is-prop) , P-¬¬-stable) : Ω¬¬ 𝓥) → ¬ (Δ (p , p-is-prop) ≤ⱽ x) → p 
    f ((p , p-is-prop) , P-¬¬-stable) not-Δ-≤-x = P-¬¬-stable not-not-p
     where
      not-not-p : ¬¬ p
      not-not-p not-p = not-Δ-≤-x (≤-to-≤ⱽ (Δ (p , p-is-prop)) x (transport (λ z → (z ≤ x) holds) x-＝-Δ (≤-is-reflexive A x)))
       where
        x-＝-Δ : x ＝ Δ (p , p-is-prop)
        x-＝-Δ = not-P-x-＝-sup-δ i x y x-≤-y (p , p-is-prop) not-p
    g : (((p , p-is-prop) , P-¬¬-stable) : Ω¬¬ 𝓥) → p → ¬ (Δ (p , p-is-prop) ≤ⱽ x)
    g ((p , p-is-prop) , P-¬¬-stable) in-p Δ-≤-x = x-≠-y (≤-is-antisymmetric A x-≤-y y-≤-x)
     where
      y-＝-Δ : y ＝ Δ (p , p-is-prop)
      y-＝-Δ = P-y-＝-sup-δ i x y x-≤-y (p , p-is-prop) in-p
      y-≤-x : (y ≤ x) holds
      y-≤-x = transport (λ z → (z ≤ x) holds) (y-＝-Δ ⁻¹) (≤ⱽ-to-≤ (Δ (p , p-is-prop)) x Δ-≤-x)
    H : r ∘ Δ ∘ Ω¬¬-to-Ω ∼ id
    H ((p , p-is-prop) , P-¬¬-stable) = to-subtype-＝ (λ X → being-¬¬-stable-is-prop fe (holds-is-prop X))
                                                     (to-subtype-＝ (λ Y → being-prop-is-prop fe)
                                                                   (pe (negations-are-props fe)
                                                                       (holds-is-prop (p , p-is-prop))
                                                                       (f ((p , p-is-prop) , P-¬¬-stable))
                                                                       (g ((p , p-is-prop) , P-¬¬-stable))))

  Δ-section-to-non-trivial : is-section (Δ ∘ Ω¬¬-to-Ω) → x ≠ y
  Δ-section-to-non-trivial (r , H) x-＝-y = {!!}
   where
    path₁ : x ＝ Δ (𝟘 , 𝟘-is-prop)
    path₁ = not-P-x-＝-sup-δ i x y x-≤-y (𝟘 , 𝟘-is-prop) (λ z → 𝟘-induction z)
    path₂ : r x ＝ r (Δ (𝟘 , 𝟘-is-prop))
    path₂ = ap r path₁
    path₃ : r (Δ (𝟘 , 𝟘-is-prop)) ＝ ((𝟘 , 𝟘-is-prop) , 𝟘-is-¬¬-stable)
    path₃ = H ((𝟘 , 𝟘-is-prop) , 𝟘-is-¬¬-stable)
    r-x-＝-𝟘 : r x ＝ ((𝟘 , 𝟘-is-prop) , 𝟘-is-¬¬-stable)
    r-x-＝-𝟘 = path₂ ∙ path₃

\end{code}
