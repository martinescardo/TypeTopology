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
open import UF.Embeddings
open import UF.Sets

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

 lower-＝-sup-δ : (i : is-δ-complete)
                → (x y : ∣ A ∣ₚ)
                → (o : (x ≤ y) holds)
                → (P : Ω 𝓥)
                → ¬ (P holds)
                → x ＝ sup-of-δ i x y o P
 lower-＝-sup-δ i x y o P not-P = ≤-is-antisymmetric A x-≤-sup sup-≤-x
  where
   x-≤-sup : (x ≤ sup-of-δ i x y o P) holds
   x-≤-sup = is-ub-of-δ i x y o P (inl ⋆)
   x-is-ub : (x is-an-upper-bound-of ((𝟙 + (P holds)) , δ x y P)) holds
   x-is-ub (inl ⋆) = ≤-is-reflexive A x
   x-is-ub (inr in-P) = 𝟘-induction (not-P in-P)
   sup-≤-x : (sup-of-δ i x y o P ≤ x) holds
   sup-≤-x = has-lub-cond-δ i x y o P (x , x-is-ub)

 upper-＝-sup-δ : (i : is-δ-complete)
                → (x y : ∣ A ∣ₚ)
                → (o : (x ≤ y) holds)
                → (P : Ω 𝓥)
                → P holds
                → y ＝ sup-of-δ i x y o P
 upper-＝-sup-δ i x y o P in-P = ≤-is-antisymmetric A y-≤-sup sup-≤-y
  where
   y-≤-sup : (y ≤ sup-of-δ i x y o P) holds
   y-≤-sup = is-ub-of-δ i x y o P (inr in-P)
   y-is-ub : (y is-an-upper-bound-of ((𝟙 + (P holds)) , δ x y P)) holds
   y-is-ub (inl ⋆) = o
   y-is-ub (inr in-P) = ≤-is-reflexive A y
   sup-≤-y : (sup-of-δ i x y o P ≤ y) holds
   sup-≤-y = has-lub-cond-δ i x y o P (y , y-is-ub)
   
 sup-δ-≤-upper : (i : is-δ-complete)
               → (x y : ∣ A ∣ₚ)
               → (o : (x ≤ y) holds)
               → (P : Ω 𝓥)
               → (sup-of-δ i x y o P ≤ y) holds
 sup-δ-≤-upper i x y o P = has-lub-cond-δ i x y o P (y , y-is-ub)
  where
   y-is-ub : (y is-an-upper-bound-of ((𝟙 + (P holds)) , δ x y P)) holds
   y-is-ub (inl ⋆) = o
   y-is-ub (inr _) = ≤-is-reflexive A y

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
  x < y = (x ≤ y) holds
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

  transitivity-lemma₁ : (i : is-δ-complete)
                      → (x y z : ∣ A ∣ₚ)
                      → (((x ≤ y) holds × y < z) → x < z) 
  transitivity-lemma₁ i x y z (x-≤-y , y-<-z) = (≤-is-transitive A x y z x-≤-y (order-< y-<-z) , sup-cond-P)
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

  transitivity-lemma₂ : (i : is-δ-complete)
                      → (x y z : ∣ A ∣ₚ)
                      → ((x < y × (y ≤ z) holds)
                      → x < z)
  transitivity-lemma₂ i x y z (x-<-y , y-≤-z) =
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

Next we will fromalize the first retract lemma. The result will allows use to exhibit the type of not-not stable propositions
as a retract of a locally small non-trivial δ-complete poset. We start by defining local smallness.

\begin{code}

module Local-Smallness (𝓤  𝓦  𝓥 : Universe) (A : Poset 𝓤 𝓦) where

 _≤_ : ∣ A ∣ₚ → ∣ A ∣ₚ → Ω 𝓦
 _≤_ = rel-syntax A

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


module Retract-Lemmas (𝓤  𝓦  𝓥 : Universe) (A : Poset 𝓤 𝓦) where

 open δ-complete-poset 𝓥 A
 open PosetReasoning A
 open non-trivial-posets A
 open Positive-Posets 𝓤 𝓦 𝓥 A
 open Local-Smallness 𝓤 𝓦 𝓥 A hiding (_≤_)
 open Joins (_≤_)

 module def-Δ (i : is-δ-complete) {x y : ∣ A ∣ₚ} (x-≤-y : (x ≤ y) holds) where

  Δ : Ω 𝓥 → ∣ A ∣ₚ
  Δ P = sup-of-δ i x y x-≤-y P

 module retract-lemma₁ (l : is-locally-small-≤) (i : is-δ-complete) (x y : ∣ A ∣ₚ) (x-≤-y : (x ≤ y) holds) where

  open local-smallness l
  open def-Δ i x-≤-y

  non-trivial-to-Δ-section : x ≠ y → is-section (Δ ∘ Ω¬¬-to-Ω)
  non-trivial-to-Δ-section x-≠-y = (r , H)
   where
    r : ∣ A ∣ₚ → Ω¬¬ 𝓥
    r z = ((¬ (z ≤ⱽ x) , negations-are-props fe) , ¬-is-¬¬-stable)
    f : ((P , P-¬¬-stable) : Ω¬¬ 𝓥) → ¬ (Δ P ≤ⱽ x) → P holds
    f (P , P-¬¬-stable) not-Δ-≤-x = P-¬¬-stable not-not-P
     where
      not-not-P : ¬¬ (P holds)
      not-not-P not-P = not-Δ-≤-x (≤-to-≤ⱽ (Δ P) x (transport (λ z → (z ≤ x) holds) x-＝-Δ (≤-is-reflexive A x)))
       where
        x-＝-Δ : x ＝ Δ P
        x-＝-Δ = lower-＝-sup-δ i x y x-≤-y P not-P
    g : ((P , P-¬¬-stable) : Ω¬¬ 𝓥) → P holds → ¬ (Δ P ≤ⱽ x)
    g (P , P-¬¬-stable) in-P Δ-≤-x = x-≠-y (≤-is-antisymmetric A x-≤-y y-≤-x)
     where
      y-＝-Δ : y ＝ Δ P
      y-＝-Δ = upper-＝-sup-δ i x y x-≤-y P in-P
      y-≤-x : (y ≤ x) holds
      y-≤-x = transport (λ z → (z ≤ x) holds) (y-＝-Δ ⁻¹) (≤ⱽ-to-≤ (Δ P) x Δ-≤-x)
    H : r ∘ Δ ∘ Ω¬¬-to-Ω ∼ id
    H (P , P-¬¬-stable) = to-subtype-＝ (λ X → being-¬¬-stable-is-prop fe (holds-is-prop X))
                                        (to-subtype-＝ (λ Y → being-prop-is-prop fe)
                                        (pe (negations-are-props fe)
                                            (holds-is-prop P)
                                            (f (P , P-¬¬-stable))
                                            (g (P , P-¬¬-stable))))

  Δ-section-to-non-trivial : is-section (Δ ∘ Ω¬¬-to-Ω) → x ≠ y
  Δ-section-to-non-trivial (r , H) x-＝-y = 𝟘-is-not-𝟙 (ap (pr₁ ∘ pr₁) (r-x-＝-𝟘 ⁻¹ ∙ ap r x-＝-y ∙ r-y-＝-𝟙))
   where
    path₁ : x ＝ Δ (𝟘 , 𝟘-is-prop)
    path₁ = lower-＝-sup-δ i x y x-≤-y (𝟘 , 𝟘-is-prop) (λ z → 𝟘-induction z)
    path₂ : r x ＝ r (Δ (𝟘 , 𝟘-is-prop))
    path₂ = ap r path₁
    path₃ : r (Δ (𝟘 , 𝟘-is-prop)) ＝ ((𝟘 , 𝟘-is-prop) , 𝟘-is-¬¬-stable)
    path₃ = H ((𝟘 , 𝟘-is-prop) , 𝟘-is-¬¬-stable)
    r-x-＝-𝟘 : r x ＝ ((𝟘 , 𝟘-is-prop) , 𝟘-is-¬¬-stable)
    r-x-＝-𝟘 = path₂ ∙ path₃
    path₄ : y ＝ Δ (𝟙 , 𝟙-is-prop)
    path₄ = upper-＝-sup-δ i x y x-≤-y (𝟙 , 𝟙-is-prop) ⋆
    path₅ : r y ＝ r (Δ (𝟙 , 𝟙-is-prop))
    path₅ = ap r path₄
    path₆ : r (Δ (𝟙 , 𝟙-is-prop)) ＝ ((𝟙 , 𝟙-is-prop) , 𝟙-is-¬¬-stable)
    path₆ = H ((𝟙 , 𝟙-is-prop) , 𝟙-is-¬¬-stable)
    r-y-＝-𝟙 : r y ＝ ((𝟙 , 𝟙-is-prop) , 𝟙-is-¬¬-stable)
    r-y-＝-𝟙 = path₅ ∙ path₆

\end{code}

Is it worth it to collect the two directions as an iff statement?

We now formalize the second retract lemma. Here we replace the assumption of non-triviality with positivity.
This allows us to exhibit the type of propositions as a retract of a local non-trivial δ-complete poset. 

\begin{code}

 module retract-lemma₂ (l : is-locally-small-≤) (i : is-δ-complete) (x y : ∣ A ∣ₚ) (x-≤-y : (x ≤ y) holds) where

  open positive-posets i
  open local-smallness l
  open def-Δ i

  private
   t : (z : ∣ A ∣ₚ) → (y ≤ z) holds → (x ≤ z) holds
   t z y-≤-z = ≤-is-transitive A x y z x-≤-y y-≤-z

  positive-to-Δ-section : x < y → (z : ∣ A ∣ₚ) → (y-≤-z : (y ≤ z) holds) → is-section (Δ (t z y-≤-z))
  positive-to-Δ-section x-<-y z y-≤-z = (r , H)
   where
    r : ∣ A ∣ₚ → Ω 𝓥
    r w = (z ≤ⱽ w , ≤ⱽ-is-prop z w)
    f : (P : Ω 𝓥) → z ≤ⱽ Δ (t z y-≤-z) P → P holds
    f P z-≤ⱽ-Δ = sup-condition x-<-z
                               z
                               (≤-is-reflexive A z)
                               P
                               (transport (λ v → (v is-lub-of ((𝟙 + P holds) , δ x z P)) holds)
                                          (z-＝-Δ ⁻¹)
                                          (is-sup-of-δ i x z (t z y-≤-z) P))
     where
      z-≤-Δ : (z ≤ Δ (t z y-≤-z) P) holds
      z-≤-Δ = ≤ⱽ-to-≤ z (Δ (t z y-≤-z) P) z-≤ⱽ-Δ
      Δ-≤-z : (Δ (t z y-≤-z) P ≤ z) holds
      Δ-≤-z = sup-δ-≤-upper i x z (t z y-≤-z) P
      z-＝-Δ : z ＝ Δ (t z y-≤-z) P
      z-＝-Δ = ≤-is-antisymmetric A z-≤-Δ Δ-≤-z
      x-<-z : x < z
      x-<-z = transitivity-lemma₂ i x y z (x-<-y , y-≤-z)
    g : (P : Ω 𝓥) → P holds → z ≤ⱽ Δ (t z y-≤-z) P
    g P in-P = ≤-to-≤ⱽ z (Δ (t z y-≤-z) P) z-≤-Δ
     where
      z-＝-Δ : z ＝ Δ (t z y-≤-z) P
      z-＝-Δ = upper-＝-sup-δ i x z (t z y-≤-z) P in-P
      z-≤-Δ : (z ≤ Δ (t z y-≤-z) P) holds
      z-≤-Δ = transport (λ v → (z ≤ v) holds) z-＝-Δ (≤-is-reflexive A z)
    H : r ∘ (Δ (≤-is-transitive A x y z x-≤-y y-≤-z)) ∼ id
    H P = to-subtype-＝ (λ _ → being-prop-is-prop fe)
                                      (pe (≤ⱽ-is-prop z (Δ (t z y-≤-z) P))
                                          (holds-is-prop P)
                                          (f P)
                                          (g P))
 
  Δ-section-to-positive : ((z : ∣ A ∣ₚ) → (y-≤-z : (y ≤ z) holds) → is-section (Δ (t z y-≤-z))) → x < y
  Δ-section-to-positive G = (x-≤-y , sup-condition-Δ)
   where
    r : (z : ∣ A ∣ₚ) → (y ≤ z) holds → (∣ A ∣ₚ → Ω 𝓥)
    r z y-≤-z = pr₁ (G z y-≤-z)
    H : (z : ∣ A ∣ₚ) → (y-≤-z : (y ≤ z) holds) → (r z y-≤-z) ∘ (Δ (t z y-≤-z)) ∼ id
    H z y-≤-z = pr₂ (G z y-≤-z)
    sup-condition-Δ : (z : ∣ A ∣ₚ)
                    → (y ≤ z) holds
                    → (P : Ω 𝓥)
                    → (z is-lub-of ((𝟙 + (P holds)) , δ x z P)) holds
                    → P holds
    sup-condition-Δ z y-≤-z P (z-is-ub-Δ , z-has-lub-cond-Δ) = idtofun 𝟙 (P holds) 𝟙-＝-P ⋆
     where
      z-≤-Δ : (z ≤ Δ (t z y-≤-z) P) holds
      z-≤-Δ = z-has-lub-cond-Δ (Δ (t z y-≤-z) P , is-ub-of-δ i x z (t z y-≤-z) P)
      Δ-≤-z : (Δ (t z y-≤-z) P ≤ z) holds
      Δ-≤-z = sup-δ-≤-upper i x z (t z y-≤-z) P
      z-＝-Δ : z ＝ Δ (t z y-≤-z) P
      z-＝-Δ = ≤-is-antisymmetric A z-≤-Δ Δ-≤-z
      path₁ : (𝟙 , 𝟙-is-prop) ＝ (r z y-≤-z) (Δ (t z y-≤-z) (𝟙 , 𝟙-is-prop))
      path₁ = (H z y-≤-z (𝟙 , 𝟙-is-prop)) ⁻¹
      path₂ : (r z y-≤-z) (Δ (t z y-≤-z) (𝟙 , 𝟙-is-prop)) ＝ (r z y-≤-z) z
      path₂ = ap (r z y-≤-z) ((upper-＝-sup-δ i x z (t z y-≤-z) (𝟙 , 𝟙-is-prop) ⋆) ⁻¹)
      path₃ : (r z y-≤-z) z ＝ (r z y-≤-z) (Δ (t z y-≤-z) P)
      path₃ = ap (r z y-≤-z) z-＝-Δ
      path₄ : (r z y-≤-z) (Δ (t z y-≤-z) P) ＝ P
      path₄ = H z y-≤-z P
      path₅ : (𝟙 , 𝟙-is-prop) ＝ P
      path₅ = path₁ ∙ path₂ ∙ path₃ ∙ path₄
      𝟙-＝-P : 𝟙 ＝ P holds
      𝟙-＝-P = ap pr₁ path₅
   
\end{code}

We will now define what it means for a δ-complete poset to be small.

\begin{code}

module Small-δ-complete-poset (𝓤 𝓦 𝓥 : Universe) (A : Poset 𝓤 𝓦) where

 open δ-complete-poset 𝓥 A
 open Local-Smallness 𝓤 𝓦 𝓥 A hiding (_≤_)

 _poset-is-small : is-δ-complete → 𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺)  ̇
 δ-complete poset-is-small = is-locally-small-≤ × ∣ A ∣ₚ is 𝓥 small

\end{code}

Now we can prove the main theorems.

\begin{code}

module Large-Posets-Theorems (𝓤 𝓦 𝓥 : Universe) (A : Poset 𝓤 𝓦) where

 open δ-complete-poset 𝓥 A
 open non-trivial-posets A
 open Positive-Posets 𝓤 𝓦 𝓥 A
 open positive-posets
 open Local-Smallness 𝓤 𝓦 𝓥 A hiding (_≤_)
 open Small-δ-complete-poset 𝓤 𝓦 𝓥 A
 open Retract-Lemmas 𝓤 𝓦 𝓥 A

 ¬¬Ω-Resizing : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥 )⁺ ̇
 ¬¬Ω-Resizing 𝓤 𝓥 = (Ω¬¬ 𝓤) is 𝓥 small

 small-non-trivial-poset-implies-¬¬resizing : (δ-complete : is-δ-complete) → is-non-trivial-poset → δ-complete poset-is-small → ¬¬Ω-Resizing 𝓥 𝓥
 small-non-trivial-poset-implies-¬¬resizing δ-complete (x , y , x-≤-y , x-≠-y) (locally-small , carrier-small) =
  embedded-retract-is-small Δ-Retract Δ-Embedding carrier-small
  where
   open retract-lemma₁ locally-small δ-complete x y x-≤-y
   open def-Δ δ-complete
   r : ∣ A ∣ₚ → Ω¬¬ 𝓥
   r = pr₁ (non-trivial-to-Δ-section x-≠-y)
   H : r ∘ Δ x-≤-y ∘ Ω¬¬-to-Ω ∼ id
   H = pr₂ (non-trivial-to-Δ-section x-≠-y)
   Δ-Retract : retract Ω¬¬ 𝓥 of ∣ A ∣ₚ
   Δ-Retract = (r , Δ x-≤-y ∘ Ω¬¬-to-Ω , H)
   Δ-Embedding : is-embedding (section Δ-Retract)
   Δ-Embedding = sections-into-sets-are-embeddings (Δ x-≤-y ∘ Ω¬¬-to-Ω) (r , H) carrier-of-[ A ]-is-set

 small-positive-poset-implies-resizing : (δ-complete : is-δ-complete) → is-positive-poset δ-complete → δ-complete poset-is-small → Ω-Resizing 𝓥 𝓥
 small-positive-poset-implies-resizing δ-complete (x , y , x-≤-y , sup-condition) (locally-small , carrier-small) =
  embedded-retract-is-small Δ-Retract Δ-Embedding carrier-small
  where
   open retract-lemma₂ locally-small δ-complete x y x-≤-y
   open def-Δ δ-complete
   r : ∣ A ∣ₚ → Ω 𝓥
   r = pr₁ (positive-to-Δ-section (x-≤-y , sup-condition) y (≤-is-reflexive A y))
   H : r ∘ Δ (≤-is-transitive A x y y x-≤-y (≤-is-reflexive A y)) ∼ id
   H = pr₂ (positive-to-Δ-section (x-≤-y , sup-condition) y (≤-is-reflexive A y))
   Δ-Retract : retract Ω 𝓥 of ∣ A ∣ₚ
   Δ-Retract = (r , Δ (≤-is-transitive A x y y x-≤-y (≤-is-reflexive A y)) , H)
   Δ-Embedding : is-embedding (section Δ-Retract)
   Δ-Embedding = sections-into-sets-are-embeddings (Δ (≤-is-transitive A x y y x-≤-y (≤-is-reflexive A y))) (r , H) carrier-of-[ A ]-is-set 

\end{code}
