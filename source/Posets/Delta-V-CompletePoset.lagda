Ian Ray, 25 July 2023.

Formalizing the auxilary notion of a delta-V-complete poset which is
sufficient for the main theorems of Section 6.2 from Tom de Jong's thesis
  https://arxiv.org/abs/2301.12405
  https://tdejong.com/writings/phd-thesis.pdf
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
open import UF.ExcludedMiddle
open import Slice.Family

module Posets.Delta-V-CompletePoset
 (pt : propositional-truncations-exist)
 (fe : Fun-Ext)
 (pe : Prop-Ext)
  where

open import Locales.Frame pt fe hiding (𝟚)
open import Posets.TwoElementPoset pt fe
open AllCombinators pt fe

module δ-complete-poset {𝓤 𝓦 : Universe} (𝓥 : Universe) (A : Poset 𝓤 𝓦) where

 δ : (x y : ∣ A ∣ₚ) → (P : Ω 𝓥) → (𝟙{𝓥} + P holds) → ∣ A ∣ₚ 
 δ x y P (inl _) = x
 δ x y P (inr _) = y

 _≤_ : ∣ A ∣ₚ → ∣ A ∣ₚ → Ω 𝓦
 _≤_ = rel-syntax A

 open Joins (_≤_)

 δ-fam : (x y : ∣ A ∣ₚ) → (P : Ω 𝓥) → Fam 𝓥 ∣ A ∣ₚ
 δ-fam x y P = ((𝟙 + P holds) , δ x y P)

 is-δ-complete : 𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺) ̇ 
 is-δ-complete = (x y : ∣ A ∣ₚ)
               → (x ≤ y) holds
               → (P : Ω 𝓥)
               → Σ s ꞉ ∣ A ∣ₚ , (s is-lub-of (δ-fam x y P)) holds

 sup-of-δ : is-δ-complete
          → (x y : ∣ A ∣ₚ)
          → (x ≤ y) holds
          → (P : Ω 𝓥)
          → ∣ A ∣ₚ
 sup-of-δ i x y o P = pr₁ (i x y o P)

 module _ (i : is-δ-complete) (x y : ∣ A ∣ₚ) (o : (x ≤ y) holds) (P : Ω 𝓥) where

  is-sup-of-δ : ((sup-of-δ i x y o P) is-lub-of (δ-fam x y P)) holds
  is-sup-of-δ = pr₂ (i x y o P)

  is-ub-of-δ : ((sup-of-δ i x y o P) is-an-upper-bound-of (δ-fam x y P)) holds
  is-ub-of-δ = pr₁ is-sup-of-δ

  has-lub-cond-δ : ((u , _) : upper-bound (δ-fam x y P)) → ((sup-of-δ i x y o P) ≤ u) holds
  has-lub-cond-δ = pr₂ is-sup-of-δ

  lower-＝-sup-δ : ¬ (P holds) → x ＝ sup-of-δ i x y o P
  lower-＝-sup-δ not-P = ≤-is-antisymmetric A x-≤-sup sup-≤-x
   where
    x-≤-sup : (x ≤ sup-of-δ i x y o P) holds
    x-≤-sup = is-ub-of-δ (inl ⋆)

    x-is-ub : (x is-an-upper-bound-of (δ-fam x y P)) holds
    x-is-ub (inl ⋆) = ≤-is-reflexive A x
    x-is-ub (inr in-P) = 𝟘-induction (not-P in-P)

    sup-≤-x : (sup-of-δ i x y o P ≤ x) holds
    sup-≤-x = has-lub-cond-δ (x , x-is-ub)

  upper-＝-sup-δ : P holds → y ＝ sup-of-δ i x y o P
  upper-＝-sup-δ in-P = ≤-is-antisymmetric A y-≤-sup sup-≤-y
   where
    y-≤-sup : (y ≤ sup-of-δ i x y o P) holds
    y-≤-sup = is-ub-of-δ (inr in-P)

    y-is-ub : (y is-an-upper-bound-of (δ-fam x y P)) holds
    y-is-ub (inl ⋆) = o
    y-is-ub (inr in-P) = ≤-is-reflexive A y

    sup-≤-y : (sup-of-δ i x y o P ≤ y) holds
    sup-≤-y = has-lub-cond-δ (y , y-is-ub)
   
  sup-δ-≤-upper : (sup-of-δ i x y o P ≤ y) holds
  sup-δ-≤-upper = has-lub-cond-δ (y , y-is-ub)
   where
    y-is-ub : (y is-an-upper-bound-of (δ-fam x y P)) holds
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

δ-completeness : (D : δ-complete-Poset 𝓤 𝓦 𝓥) → δ-complete-poset.is-δ-complete 𝓥 (Poset-δ D)
δ-completeness D = pr₂ D

\end{code}

\begin{code}

module non-trivial-posets {𝓤  𝓦 : Universe} (A : Poset 𝓤 𝓦) where

 is-non-trivial-poset : 𝓤 ⊔ 𝓦 ̇
 is-non-trivial-poset =  Σ x ꞉ ∣ A ∣ₚ , ( Σ y ꞉ ∣ A ∣ₚ , (x ≤[ A ] y) holds × (x ≠ y))

 lower : is-non-trivial-poset → ∣ A ∣ₚ
 lower i = pr₁ i

 upper : is-non-trivial-poset → ∣ A ∣ₚ
 upper i = pr₁ (pr₂ i)

 ordering : (i : is-non-trivial-poset) → (lower i ≤[ A ] upper i) holds
 ordering i = pr₁ (pr₂ (pr₂ i))

 nequal : (i : is-non-trivial-poset) → lower i ≠ upper i
 nequal i = pr₂ (pr₂ (pr₂ i))

 module _ (𝓥 : Universe) (i : is-non-trivial-poset) where

  open Joins (rel-syntax A)
  open δ-complete-poset 𝓥 A
  private
   x = lower i
   y = upper i
   x-≤-y = ordering i
   x-≠-y = nequal i 

  WEM-lemma : (P : Ω 𝓥)
            → ((x is-lub-of (δ-fam x y P)) holds → ¬ (P holds))
            × ((y is-lub-of (δ-fam x y P)) holds → ¬ ¬ (P holds)) 
  pr₁ (WEM-lemma P) (x-is-ub , _) in-P = x-≠-y (≤-is-antisymmetric A (x-≤-y) (x-is-ub (inr in-P)))
  pr₂ (WEM-lemma P) (_ , y-has-lub-cond) not-P = x-≠-y (≤-is-antisymmetric A (x-≤-y) (y-has-lub-cond (x , x-is-ub)))
   where
    x-is-ub : (x is-an-upper-bound-of (δ-fam x y P)) holds
    x-is-ub (inl ✯) = ≤-is-reflexive A x
    x-is-ub (inr in-P) = 𝟘-induction (not-P in-P)
    
\end{code}

We now show that the two element poset is δ complete only if WEM holds.

\begin{code}

2-is-non-trivial : non-trivial-posets.is-non-trivial-poset 2-Poset
2-is-non-trivial = (₀ , ₁ , ⋆ , zero-is-not-one)

2-is-δ-complete-WEM : {𝓥 : Universe}
                    → δ-complete-poset.is-δ-complete {𝓤₀} {𝓤₀} 𝓥 2-Poset
                    → WEM 𝓥
2-is-δ-complete-WEM {𝓥} i P P-is-prop = wem
 where
  open Joins (rel-syntax 2-Poset)
  open δ-complete-poset 𝓥 2-Poset
  open non-trivial-posets 2-Poset  

  sup-2-exists : Σ s ꞉ ∣ 2-Poset ∣ₚ , (s is-lub-of (δ-fam ₀ ₁ (P , P-is-prop))) holds
  sup-2-exists = i ₀ ₁ ⋆ (P , P-is-prop)

  sup-2-exists-gives-wem : Σ s ꞉ ∣ 2-Poset ∣ₚ , (s is-lub-of (δ-fam ₀ ₁ (P , P-is-prop))) holds → ¬ P + ¬ (¬ P)
  sup-2-exists-gives-wem (₀ , sup) = inl (pr₁ (WEM-lemma 𝓥 2-is-non-trivial (P , P-is-prop)) sup)
  sup-2-exists-gives-wem (₁ , sup) = inr (pr₂ (WEM-lemma 𝓥 2-is-non-trivial (P , P-is-prop)) sup)

  wem : ¬ P + ¬ (¬ P)
  wem = sup-2-exists-gives-wem sup-2-exists

\end{code}

Since non-trivial is a negated concept it only has enough strength to derive WEM, we now introduce the stronger concept of positivity.

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
          → (z is-lub-of (δ-fam x z P)) holds
          → P holds)

  order-< : {x y : ∣ A ∣ₚ} → x < y → (x ≤ y) holds
  order-< c = pr₁ c

  sup-condition : {x y : ∣ A ∣ₚ}
                → x < y
                → ((z : ∣ A ∣ₚ)
                 → (y ≤ z) holds
                 → (P : Ω 𝓥)
                 → (z is-lub-of (δ-fam x z P)) holds
                 → P holds)
  sup-condition c = pr₂ c

  strictly-below-implies-non-trivial : (x y : ∣ A ∣ₚ)
                                     → is-δ-complete
                                     → (x < y)
                                     → (x ≤ y) holds × (x ≠ y)
  pr₁ (strictly-below-implies-non-trivial x y i c) = order-< c
  pr₂ (strictly-below-implies-non-trivial x y i c) p =
   𝟘-induction (sup-condition c y (≤-is-reflexive A y) ⊥ (y-is-ub , y-has-lub-cond))
    where
     y-is-ub : (y is-an-upper-bound-of (δ-fam x y ⊥)) holds
     y-is-ub (inl ⋆) = order-< c

     y-has-lub-cond : (u : upper-bound (δ-fam x y ⊥)) → (y ≤ (pr₁ u)) holds
     y-has-lub-cond u = y ＝⟨ p ⁻¹ ⟩ₚ pr₂ u (inl ⋆)

\end{code}

We could show that if the converse holds then so does EM in 𝓥.

\begin{code}

  ≤-<-to-< : (i : is-δ-complete)
           → (x y z : ∣ A ∣ₚ)
           → (x ≤ y) holds × y < z
           → x < z 
  ≤-<-to-< i x y z (x-≤-y , y-<-z) = (≤-is-transitive A x y z x-≤-y (order-< y-<-z) , sup-cond-P)
   where
    sup-cond-P : (w : ∣ A ∣ₚ)
               → (z ≤ w) holds
               → (P : Ω 𝓥)
               → (w is-lub-of (δ-fam x w P)) holds
               → P holds
    sup-cond-P w z-≤-w P (w-is-ubₓ , w-has-lub-condₓ) = sup-condition y-<-z w z-≤-w P (w-is-ub , w-has-lub-cond)
     where
      w-is-ub : (w is-an-upper-bound-of (δ-fam y w P)) holds
      w-is-ub (inl ⋆) = ≤-is-transitive A y z w (order-< y-<-z) z-≤-w
      w-is-ub (inr p) = ≤-is-reflexive A w

      w-has-lub-cond : ((u , u-is-ub) : (upper-bound (δ-fam y w P))) → (w ≤ u) holds 
      w-has-lub-cond (u , u-is-ub) = w-has-lub-condₓ (u , u-is-ubₓ)
       where
        u-is-ubₓ : (u is-an-upper-bound-of (δ-fam x w P)) holds
        u-is-ubₓ (inl ⋆) = ≤-is-transitive A x y u (x-≤-y) (u-is-ub (inl ⋆))
        u-is-ubₓ (inr p) = u-is-ub (inr p)

  <-≤-to-< : (i : is-δ-complete)
           → (x y z : ∣ A ∣ₚ)
           → x < y × (y ≤ z) holds
           → x < z
  <-≤-to-< i x y z (x-<-y , y-≤-z) =
   (≤-is-transitive A x y z (order-< x-<-y) y-≤-z , sup-cond-P)
    where
     sup-cond-P : (w : ∣ A ∣ₚ)
                → (z ≤ w) holds
                → (P : Ω 𝓥)
                → (w is-lub-of (δ-fam x w P)) holds
                → P holds
     sup-cond-P w z-≤-w P w-is-lub = sup-condition x-<-y w (≤-is-transitive A y z w y-≤-z z-≤-w) P w-is-lub

  is-positive-poset : 𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺) ̇ 
  is-positive-poset = Σ x ꞉ ∣ A ∣ₚ , (Σ y ꞉ ∣ A ∣ₚ , x < y)

\end{code}

Next we will formalize the first retract lemma. The result will allows use to exhibit the type of not-not stable propositions
as a retract of a locally small non-trivial δ-complete poset. We start by defining local smallness.

\begin{code}

module Local-Smallness (𝓤  𝓦  𝓥 : Universe) (A : Poset 𝓤 𝓦) (_≤_ : ∣ A ∣ₚ → ∣ A ∣ₚ → Ω 𝓦)  where

 is-locally-small-order : 𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺)  ̇
 is-locally-small-order = (x y : ∣ A ∣ₚ) → ((x ≤ y) holds) is 𝓥 small

 module local-smallness (l : is-locally-small-order) where

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
 open Local-Smallness 𝓤 𝓦 𝓥 A _≤_
 open Joins (_≤_)

 module def-Δ (i : is-δ-complete) {x y : ∣ A ∣ₚ} (x-≤-y : (x ≤ y) holds) where

  Δ : Ω 𝓥 → ∣ A ∣ₚ
  Δ P = sup-of-δ i x y x-≤-y P

 module retract-lemma₁ (l : is-locally-small-order) (i : is-δ-complete) (x y : ∣ A ∣ₚ) (x-≤-y : (x ≤ y) holds) where

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
    path₁ : x ＝ Δ ⊥
    path₁ = lower-＝-sup-δ i x y x-≤-y ⊥ ⊥-doesnt-hold

    path₂ : r x ＝ r (Δ ⊥)
    path₂ = ap r path₁

    path₃ : r (Δ ⊥) ＝ (⊥ , 𝟘-is-¬¬-stable)
    path₃ = H (⊥ , 𝟘-is-¬¬-stable)

    r-x-＝-𝟘 : r x ＝ (⊥ , 𝟘-is-¬¬-stable)
    r-x-＝-𝟘 = path₂ ∙ path₃

    path₄ : y ＝ Δ ⊤
    path₄ = upper-＝-sup-δ i x y x-≤-y ⊤ ⊤-holds

    path₅ : r y ＝ r (Δ ⊤)
    path₅ = ap r path₄

    path₆ : r (Δ ⊤) ＝ (⊤ , 𝟙-is-¬¬-stable)
    path₆ = H (⊤ , 𝟙-is-¬¬-stable)

    r-y-＝-𝟙 : r y ＝ (⊤ , 𝟙-is-¬¬-stable)
    r-y-＝-𝟙 = path₅ ∙ path₆

  non-trivial-iff-Δ-section : x ≠ y ↔ is-section (Δ ∘ Ω¬¬-to-Ω)
  non-trivial-iff-Δ-section = (non-trivial-to-Δ-section , Δ-section-to-non-trivial)


\end{code}

We now formalize the second retract lemma. Here we replace the assumption of non-triviality with positivity.
This allows us to exhibit the type of propositions as a retract of a locally small positive δ-complete poset. 

\begin{code}

 module retract-lemma₂ (l : is-locally-small-order) (i : is-δ-complete) (x y : ∣ A ∣ₚ) (x-≤-y : (x ≤ y) holds) where

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
                               (transport (λ v → (v is-lub-of (δ-fam x z P)) holds)
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
      x-<-z = <-≤-to-< i x y z (x-<-y , y-≤-z)

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
                    → (z is-lub-of (δ-fam x z P)) holds
                    → P holds
    sup-condition-Δ z y-≤-z P (z-is-ub-Δ , z-has-lub-cond-Δ) = idtofun 𝟙 (P holds) 𝟙-＝-P ⋆
     where
      z-≤-Δ : (z ≤ Δ (t z y-≤-z) P) holds
      z-≤-Δ = z-has-lub-cond-Δ (Δ (t z y-≤-z) P , is-ub-of-δ i x z (t z y-≤-z) P)

      Δ-≤-z : (Δ (t z y-≤-z) P ≤ z) holds
      Δ-≤-z = sup-δ-≤-upper i x z (t z y-≤-z) P

      z-＝-Δ : z ＝ Δ (t z y-≤-z) P
      z-＝-Δ = ≤-is-antisymmetric A z-≤-Δ Δ-≤-z

      path₁ : ⊤ ＝ (r z y-≤-z) (Δ (t z y-≤-z) ⊤)
      path₁ = (H z y-≤-z ⊤) ⁻¹

      path₂ : (r z y-≤-z) (Δ (t z y-≤-z) ⊤) ＝ (r z y-≤-z) z
      path₂ = ap (r z y-≤-z) ((upper-＝-sup-δ i x z (t z y-≤-z) ⊤ ⊤-holds) ⁻¹)

      path₃ : (r z y-≤-z) z ＝ (r z y-≤-z) (Δ (t z y-≤-z) P)
      path₃ = ap (r z y-≤-z) z-＝-Δ

      path₄ : (r z y-≤-z) (Δ (t z y-≤-z) P) ＝ P
      path₄ = H z y-≤-z P

      path₅ : ⊤ ＝ P
      path₅ = path₁ ∙ path₂ ∙ path₃ ∙ path₄

      𝟙-＝-P : 𝟙 ＝ P holds
      𝟙-＝-P = ap pr₁ path₅

  positive-iff-Δ-section : x < y ↔ ((z : ∣ A ∣ₚ) → (y-≤-z : (y ≤ z) holds) → is-section (Δ (t z y-≤-z)))
  positive-iff-Δ-section = (positive-to-Δ-section , Δ-section-to-positive)
   
\end{code}

We will now define what it means for a δ-complete poset to be small.

\begin{code}

module Small-δ-complete-poset (𝓤 𝓦 𝓥 : Universe) (A : Poset 𝓤 𝓦) where

 open δ-complete-poset 𝓥 A
 open Local-Smallness 𝓤 𝓦 𝓥 A _≤_

 module small-δ-complete-poset (i : is-δ-complete) where

  poset-is-small : 𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺)  ̇
  poset-is-small = is-locally-small-order × ∣ A ∣ₚ is 𝓥 small

\end{code}

We take a quick detour to give two concrete examples of non-trivial and positive δ-complete posets:
the type of not-not stable propositions and the type of propositions.

\begin{code}

module Ω-δ-complete-positive-Poset (𝓥 : Universe) where

 _⊑_ : Ω 𝓥 → Ω 𝓥 → 𝓥  ̇
 P ⊑ Q = P holds → Q holds

 ⊑-is-prop-valued : (P Q : Ω 𝓥) → is-prop (P ⊑ Q) 
 ⊑-is-prop-valued P Q = Π-is-prop fe (λ _ → holds-is-prop Q)

 ⊑-is-reflexive : (P : Ω 𝓥) → P ⊑ P
 ⊑-is-reflexive _ = id

 ⊑-is-antisymmetric : {P Q : Ω 𝓥} → P ⊑ Q → Q ⊑ P → P ＝ Q
 ⊑-is-antisymmetric {P} {Q} o r = to-subtype-＝ (λ _ → being-prop-is-prop fe) (pe (holds-is-prop P) (holds-is-prop Q) o r)

 ⊑-is-transitive : (P Q R : Ω 𝓥) → P ⊑ Q → Q ⊑ R → P ⊑ R
 ⊑-is-transitive P Q R o r p = r (o p)

 Ω-Poset : Poset (𝓥 ⁺) 𝓥
 Ω-Poset = (Ω 𝓥 ,
            (λ P → λ Q → (P ⊑ Q , ⊑-is-prop-valued P Q)) ,
            (⊑-is-reflexive , ⊑-is-transitive) , ⊑-is-antisymmetric)

 open Local-Smallness (𝓥 ⁺) 𝓥 𝓥 Ω-Poset (λ P → λ Q → (P ⊑ Q , ⊑-is-prop-valued P Q))

 ⊑-is-locally-small : is-locally-small-order
 ⊑-is-locally-small P Q = (P ⊑ Q , ≃-refl (P ⊑ Q))

 open δ-complete-poset 𝓥 Ω-Poset

 Ω-δ-complete : is-δ-complete
 Ω-δ-complete Q R Q-⊑-R P = ((Ǝ i ꞉ (𝟙 + P holds) , (δ Q R P i holds)) , (is-upbnd , has-sup-cond))
  where
   open Joins (λ Q → λ R → (Q ⊑ R , ⊑-is-prop-valued Q R))
   open propositional-truncations-exist pt

   is-upbnd : ((Ǝ i ꞉ (𝟙 + P holds) , (δ Q R P i holds)) is-an-upper-bound-of (δ-fam Q R P)) holds
   is-upbnd i e = ∣ (i , e) ∣

   has-sup-cond : ((U , _) : upper-bound (δ-fam Q R P)) → (Ǝ i ꞉ (𝟙 + P holds) , (δ Q R P i holds)) ⊑ U
   has-sup-cond (U , U-is-upbnd) = ∥∥-rec (holds-is-prop U) f
    where
     f : Σ i ꞉ (𝟙 + (P holds)) , δ Q R P i holds → U holds
     f (i , e) = U-is-upbnd i e

 open Positive-Posets (𝓥 ⁺) 𝓥 𝓥 Ω-Poset
 open positive-posets Ω-δ-complete

 Ω-positive : is-positive-poset
 Ω-positive = (⊥ , ⊤ , (𝟘-elim , f))
  where
   open Joins (λ Q → λ R → (Q ⊑ R , ⊑-is-prop-valued Q R))
   f : (Q : Ω 𝓥) → ⊤ ⊑ Q → (P : Ω 𝓥) → (Q is-lub-of (δ-fam ⊥ Q P)) holds → P holds
   f Q o P (Q-is-upbnd , Q-has-lub-cond) = Q-has-lub-cond (P , P-is-upbnd) (o ⋆)
    where
     P-is-upbnd : (P is-an-upper-bound-of (δ-fam ⊥ Q P)) holds
     P-is-upbnd (inr p) e = p

module Ω¬¬-δ-complete-non-trivial-Poset (𝓥 : Universe) where

 _⊑_ : Ω¬¬ 𝓥 → Ω¬¬ 𝓥 → 𝓥  ̇
 P ⊑ Q = P holds' → Q holds'

 ⊑-is-prop-valued : (P Q : Ω¬¬ 𝓥) → is-prop (P ⊑ Q) 
 ⊑-is-prop-valued P Q = Π-is-prop fe (λ _ → holds'-is-prop Q)

 ⊑-is-reflexive : (P : Ω¬¬ 𝓥) → P ⊑ P
 ⊑-is-reflexive _ = id

 ⊑-is-antisymmetric : {P Q : Ω¬¬ 𝓥} → P ⊑ Q → Q ⊑ P → P ＝ Q 
 ⊑-is-antisymmetric {P} {Q} o r =
   to-subtype-＝ (λ X → being-¬¬-stable-is-prop fe (holds-is-prop X))
                 (to-subtype-＝ (λ _ → being-prop-is-prop fe) (pe (holds'-is-prop P) (holds'-is-prop Q) o r))

 ⊑-is-transitive : (P Q R : Ω¬¬ 𝓥) → P ⊑ Q → Q ⊑ R → P ⊑ R
 ⊑-is-transitive P Q R o r p = r (o p)

 Ω¬¬-Poset : Poset (𝓥 ⁺) 𝓥
 Ω¬¬-Poset = (Ω¬¬ 𝓥 ,
              (λ P → λ Q → (P ⊑ Q , ⊑-is-prop-valued P Q)) ,
              (⊑-is-reflexive , ⊑-is-transitive) , ⊑-is-antisymmetric)

 open Local-Smallness (𝓥 ⁺) 𝓥 𝓥 Ω¬¬-Poset (λ P → λ Q → (P ⊑ Q , ⊑-is-prop-valued P Q))

 ⊑-is-locally-small : is-locally-small-order
 ⊑-is-locally-small P Q = (P ⊑ Q , ≃-refl (P ⊑ Q))

 open δ-complete-poset 𝓥 Ω¬¬-Poset

 Ω¬¬-δ-complete : is-δ-complete
 Ω¬¬-δ-complete Q R Q-⊑-R P =
   (((¬¬ (((Ǝ i ꞉ (𝟙 + P holds) , (δ Q R P i) holds') holds)) ,
   negations-are-props fe) ,
   ¬-is-¬¬-stable) ,
   (is-upbnd , has-lub-cond)) 
  where
   open Joins (λ Q → λ R → (Q ⊑ R , ⊑-is-prop-valued Q R))
   open propositional-truncations-exist pt

   E : Ω¬¬ 𝓥
   E = ((¬¬ ((Ǝ i ꞉ (𝟙 + P holds) , (δ Q R P i) holds') holds) ,
       negations-are-props fe) ,
       ¬-is-¬¬-stable)
   
   is-upbnd : (E is-an-upper-bound-of (δ-fam Q R P)) holds 
   is-upbnd i δ-i not-exists = not-exists ∣ (i , δ-i) ∣

   has-lub-cond : ((U , _) : upper-bound (δ-fam Q R P)) → E ⊑ U
   has-lub-cond (U , U-is-upbnd) = E-⊑-U
    where
     untrunc-map : Σ i ꞉ (𝟙 + (P holds)) , δ Q R P i holds' → U holds'
     untrunc-map (i , δ-i) = U-is-upbnd i δ-i
     f : (Ǝ i ꞉ (𝟙 + P holds) , (δ Q R P i) holds') holds → U holds'
     f = ∥∥-rec (holds'-is-prop U) untrunc-map
     g : ¬¬ ((Ǝ i ꞉ (𝟙 + P holds) , (δ Q R P i) holds') holds) → ¬¬ (U holds')
     g = double-contrapositive f
     h : ¬¬ (U holds') → U holds'
     h = holds'-is-¬¬-stable U
     E-⊑-U : E ⊑ U
     E-⊑-U = h ∘ g

 open non-trivial-posets Ω¬¬-Poset

 Ω¬¬-is-non-trivial : is-non-trivial-poset
 Ω¬¬-is-non-trivial = ((⊥ , 𝟘-is-¬¬-stable) , (⊤ , 𝟙-is-¬¬-stable) ,
                      𝟘-elim , (λ np → 𝟘-is-not-𝟙 (ap (pr₁ ∘ pr₁) np)))

\end{code}

Now we can prove Theorem 6.2.21 from Tom de Jong's thesis.

\begin{code}

module Predicative-Taboos (𝓤 𝓦 𝓥 : Universe) (A : Poset 𝓤 𝓦) where

 open δ-complete-poset 𝓥 A
 open non-trivial-posets A
 open Positive-Posets 𝓤 𝓦 𝓥 A
 open positive-posets
 open Local-Smallness 𝓤 𝓦 𝓥 A _≤_
 open Small-δ-complete-poset 𝓤 𝓦 𝓥 A
 open Retract-Lemmas 𝓤 𝓦 𝓥 A

 small-non-trivial-poset-implies-¬¬resizing : (δ-complete : is-δ-complete)
                                            → is-non-trivial-poset
                                            → small-δ-complete-poset.poset-is-small δ-complete
                                            → Ω¬¬-Resizing 𝓥 𝓥
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
 
 small-positive-poset-implies-resizing : (δ-complete : is-δ-complete)
                                       → is-positive-poset δ-complete
                                       → small-δ-complete-poset.poset-is-small δ-complete
                                       → Ω-Resizing 𝓥 𝓥
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
   Δ-Embedding = sections-into-sets-are-embeddings (Δ (≤-is-transitive A x y y x-≤-y (≤-is-reflexive A y)))
                                                   (r , H)
                                                   carrier-of-[ A ]-is-set

module Resizing-Implications (𝓥 : Universe) where

 module _ where

  open Ω¬¬-δ-complete-non-trivial-Poset 𝓥
  open δ-complete-poset 𝓥 Ω¬¬-Poset
  open non-trivial-posets Ω¬¬-Poset
  open Small-δ-complete-poset (𝓥 ⁺) 𝓥 𝓥 Ω¬¬-Poset
  open small-δ-complete-poset Ω¬¬-δ-complete

  ¬¬resizing-implies-small-non-trivial-poset : Ω¬¬-Resizing 𝓥 𝓥
                                             → Σ P ꞉ Poset (𝓥 ⁺) 𝓥 , is-δ-complete × is-non-trivial-poset × poset-is-small
  ¬¬resizing-implies-small-non-trivial-poset resize = (Ω¬¬-Poset , Ω¬¬-δ-complete , Ω¬¬-is-non-trivial , ⊑-is-locally-small , resize)

 module _ where

  open Ω-δ-complete-positive-Poset 𝓥
  open δ-complete-poset 𝓥 Ω-Poset
  open Positive-Posets (𝓥 ⁺) 𝓥 𝓥 Ω-Poset
  open positive-posets Ω-δ-complete
  open Small-δ-complete-poset (𝓥 ⁺) 𝓥 𝓥 Ω-Poset
  open small-δ-complete-poset Ω-δ-complete

  resizing-implies-small-positive-poset : Ω-Resizing 𝓥 𝓥
                                        → Σ P ꞉ Poset (𝓥 ⁺) 𝓥 , is-δ-complete × is-positive-poset × poset-is-small
  resizing-implies-small-positive-poset resize = (Ω-Poset , Ω-δ-complete , Ω-positive , ⊑-is-locally-small , resize)

\end{code}
