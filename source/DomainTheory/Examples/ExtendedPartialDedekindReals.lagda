Tom de Jong, 9 January 2026

The extended partial Dedekind reals as a pointed dcpo.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module DomainTheory.Examples.ExtendedPartialDedekindReals
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

 open PropositionalTruncation pt

 open import DomainTheory.Basics.Dcpo pt fe 𝓤₀
 open import DomainTheory.Basics.Pointed pt fe 𝓤₀
 open import OrderedTypes.Poset fe
 open PosetAxioms

 open import Notation.Order using (_<_ ; _≮_)
 open import Rationals.Order
 open import Rationals.Type

 open import UF.Base
 open import UF.Powerset
 open import UF.Powerset-MultiUniverse hiding (𝓟)
 open unions-of-small-families pt 𝓤₀ 𝓤₀ ℚ

 open import Various.DedekindNonAxiomatic pt fe pe

 extended-partial-Dedekind-reals : 𝓤₁ ̇
 extended-partial-Dedekind-reals = 𝓡∞

 private
  L U : 𝓡∞ → 𝓟 ℚ
  L x = pr₁ (pr₁ x)
  U x = pr₂ (pr₁ x)

  L-is-lower : (x : 𝓡∞) → is-lower (L x)
  L-is-lower x = pr₁ (pr₁ (pr₂ x))

  L-is-upper-open : (x : 𝓡∞) → is-upper-open (L x)
  L-is-upper-open x = pr₂ (pr₁ (pr₂ x))

  U-is-upper : (x : 𝓡∞) → is-upper (U x)
  U-is-upper x = pr₁ (pr₁ (pr₂ (pr₂ x)))

  U-is-lower-open : (x : 𝓡∞) → is-lower-open (U x)
  U-is-lower-open x = pr₂ (pr₁ (pr₂ (pr₂ x)))

  orderedness : (x : 𝓡∞) → are-ordered (L x) (U x)
  orderedness x = pr₂ (pr₂ (pr₂ x))

  -- TODO(?). Move this and the equivalence to Various.Dedekind?
  roundness : (x : 𝓟 ℚ × 𝓟 ℚ) → 𝓤₀ ̇
  roundness (L , U) =
     ((p : ℚ) → p ∈ L ↔ (∃ r ꞉ ℚ , (p < r) × (r ∈ L)))
   × ((q : ℚ) → q ∈ U ↔ (∃ s ꞉ ℚ , (s < q) × (s ∈ U)))

  roundness-equivalence
   : ((L , U) : 𝓟 ℚ × 𝓟 ℚ)
   → is-lower L × is-upper-open L × is-upper U × is-lower-open U
   ↔ roundness (L , U)
  roundness-equivalence (L , U) = I , II
   where
    I : is-lower L × is-upper-open L × is-upper U × is-lower-open U
      → roundness (L , U)
    I (L-low , L-uo , U-up , U-lo) =
     (λ p → L-uo p ,
            ∥∥-rec (∈-is-prop L p) (λ (r , l , r-in-L) → L-low r r-in-L p l)) ,
     (λ q → U-lo q ,
            ∥∥-rec (∈-is-prop U q) (λ (s , l , s-in-U) → U-up s s-in-U q l))
    II : roundness (L , U)
       → is-lower L × is-upper-open L × is-upper U × is-lower-open U
    II (ρ₁ , ρ₂) =
     (λ q q-in-L p l → rl-implication (ρ₁ p) ∣ q , l , q-in-L ∣) ,
     (λ p → lr-implication (ρ₁ p)) ,
     (λ p p-in-U q l → rl-implication (ρ₂ q) ∣ p , l , p-in-U ∣) ,
     (λ q → lr-implication (ρ₂ q))

  _⊑_ : 𝓡∞ → 𝓡∞ → 𝓤₀ ̇
  x ⊑ y = (L x ⊆ L y) × (U x ⊆ U y)

  L-inclusion : (x y : 𝓡∞) → x ⊑ y → L x ⊆ L y
  L-inclusion x y = pr₁

  U-inclusion : (x y : 𝓡∞) → x ⊑ y → U x ⊆ U y
  U-inclusion x y = pr₂

  ⊑-is-prop : (x y : 𝓡∞) → is-prop (x ⊑ y)
  ⊑-is-prop x y = ×-is-prop (⊆-is-prop fe (L x) (L y))
                            (⊆-is-prop fe (U x) (U y))

  ⊑-refl : is-reflexive _⊑_
  ⊑-refl x = (⊆-refl (L x) , ⊆-refl (U x))

  ⊑-trans : is-transitive _⊑_
  ⊑-trans x y z (u₁ , u₂) (v₁ , v₂) =
   (⊆-trans (L x) (L y) (L z) u₁ v₁) ,
    ⊆-trans (U x) (U y) (U z) u₂ v₂

  ⊑-antisym : is-antisymmetric _⊑_
  ⊑-antisym x y (u₁ , u₂) (v₁ , v₂) =
   to-subtype-＝
    (λ (L , U) → ×₃-is-prop
                  (×-is-prop (being-lower-is-prop L)
                             (being-upper-open-is-prop L))
                  (×-is-prop (being-upper-is-prop U)
                             (being-lower-open-is-prop U))
                  (being-ordered-is-prop L U))
    (to-×-＝ (subset-extensionality pe fe u₁ v₁)
             (subset-extensionality pe fe u₂ v₂))

  directed-join : {I : 𝓤₀ ̇ } (x : I → 𝓡∞) → is-directed _⊑_ x → 𝓡∞
  directed-join {I} x δ =
   (L∞ , U∞) , (L∞-is-lower , L∞-is-upper-open) ,
               (U∞-is-upper , U∞-is-lower-open) ,
               L∞-U∞-are-ordered
   where
    L∞ : 𝓟 ℚ
    L∞ = ⋃ (L ∘ x)
    U∞ : 𝓟 ℚ
    U∞ = ⋃ (U ∘ x)
    L∞-is-lower : is-lower L∞
    L∞-is-lower q q-in-union p p-below-q =
     ∥∥-rec (∈-is-prop L∞ p) h q-in-union
      where
       h : (Σ i ꞉ I , q ∈ L (x i)) → p ∈ L∞
       h (i , m) = ∣ i , L-is-lower (x i) q m p p-below-q ∣
    L∞-is-upper-open : is-upper-open L∞
    L∞-is-upper-open p = ∥∥-rec ∃-is-prop h
     where
      h : (Σ i ꞉ I , p ∈ L (x i)) → ∃ p' ꞉ ℚ , p < p' × p' ∈ L∞
      h (i , m) = ∥∥-functor (λ (p' , l , n) → p' , l , ∣ i , n ∣)
                             (L-is-upper-open (x i) p m)
    U∞-is-upper : is-upper U∞
    U∞-is-upper q q-in-union p q-below-p =
     ∥∥-rec (∈-is-prop U∞ p) h q-in-union
      where
       h : (Σ i ꞉ I , q ∈ U (x i)) → p ∈ U∞
       h (i , m) = ∣ i , U-is-upper (x i) q m p q-below-p ∣
    U∞-is-lower-open : is-lower-open U∞
    U∞-is-lower-open p = ∥∥-rec ∃-is-prop h
     where
      h : (Σ i ꞉ I , p ∈ U (x i)) → ∃ p' ꞉ ℚ , p' < p × p' ∈ U∞
      h (i , m) = ∥∥-functor (λ (p' , l , n) → p' , l , ∣ i , n ∣)
                             (U-is-lower-open (x i) p m)
    L∞-U∞-are-ordered : are-ordered L∞ U∞
    L∞-U∞-are-ordered p q p-in-L∞ q-in-U∞ =
     ∥∥-rec₂ (ℚ<-is-prop p q) h p-in-L∞ q-in-U∞
      where
       h : Σ i ꞉ I , p ∈ L (x i)
         → Σ j ꞉ I , q ∈ U (x j)
         → p < q
       h (i , m) (j , n) =
        ∥∥-rec (ℚ<-is-prop p q) h' (semidirected-if-directed _⊑_ x δ i j)
         where
          h' : Σ k ꞉ I , (x i ⊑ x k) × (x j ⊑ x k)
             → p < q
          h' (k , incl₁ , incl₂) =
           orderedness (x k) p q (L-inclusion (x i) (x k) incl₁ p m)
                                 (U-inclusion (x j) (x k) incl₂ q n)

  directed-join-is-upper-bound : {I : 𝓤₀ ̇ } (x : I → 𝓡∞) (δ : is-directed _⊑_ x)
                                → is-upperbound _⊑_ (directed-join x δ) x
  directed-join-is-upper-bound x δ i =
   ⋃-is-upperbound (L ∘ x) i , ⋃-is-upperbound (U ∘ x) i

  directed-join-is-lower-bound-of-upper-bounds
   : {I : 𝓤₀ ̇ } (x : I → 𝓡∞) (δ : is-directed _⊑_ x)
   → is-lowerbound-of-upperbounds _⊑_ (directed-join x δ) x
  directed-join-is-lower-bound-of-upper-bounds x δ y y-is-ub =
   ⋃-is-lowerbound-of-upperbounds
    (L ∘ x) (L y) (λ i → L-inclusion (x i) y (y-is-ub i)) ,
   ⋃-is-lowerbound-of-upperbounds
    (U ∘ x) (U y) (λ i → U-inclusion (x i) y (y-is-ub i))

 𝓡∞-DCPO : DCPO {𝓤₁} {𝓤₀}
 𝓡∞-DCPO = 𝓡∞ , _⊑_ ,
           (𝓡∞-is-set , ⊑-is-prop , ⊑-refl , ⊑-trans , ⊑-antisym) ,
           (λ I x δ → directed-join x δ ,
                      directed-join-is-upper-bound x δ ,
                      directed-join-is-lower-bound-of-upper-bounds x δ)

 𝓡∞-DCPO⊥ : DCPO⊥ {𝓤₁} {𝓤₀}
 𝓡∞-DCPO⊥ = 𝓡∞-DCPO , (⊥𝓡∞ , (λ x → (λ _ → 𝟘-elim) , (λ _ → 𝟘-elim)))

\end{code}
