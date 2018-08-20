Martin Escardo, 20th August 2018

We consider type and subtype classifiers, and discuss an obvious
generalization which is left undone for the moment.

 * (Σ \(X : U ̇) → X → Y) ≃ (Y → U ̇)
 * (Σ \(X : U ̇) → X ↪ Y) ≃ (Y → Ω U)

NB. This files takes a long time to typecheck. I am not sure why.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Classifiers where

open import SpartanMLTT
open import UF-Subsingletons
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-Base
open import UF-Univalence
open import UF-UA-FunExt
open import UF-FunExt
open import UF-Embedding

module type-classifier
        {U : Universe}
        (fe' : funext U (U ′))
        (ua : is-univalent U)
        (Y : U ̇) where

 χ : (Σ \(X : U ̇) → X → Y)  → (Y → U ̇)
 χ (X , f) = fiber f

 T : (Y → U ̇) → Σ \(X : U ̇) → X → Y
 T A = Σ A , pr₁

 χT : (A : Y → U ̇) → χ(T A) ≡ A
 χT A = dfunext fe' γ
  where
   f : ∀ y → (Σ \(σ : Σ A) → pr₁ σ ≡ y) → A y
   f y ((.y , a) , refl) = a
   g : ∀ y → A y → Σ \(σ : Σ A) → pr₁ σ ≡ y
   g y a = (y , a) , refl
   fg : ∀ y a → f y (g y a) ≡ a
   fg y a = refl
   gf : ∀ y σ → g y (f y σ) ≡ σ
   gf y ((.y , a) , refl) = refl
   γ : ∀ y → (Σ \(σ : Σ A) → pr₁ σ ≡ y) ≡ A y
   γ y = eqtoid ua _ _ (f y , ((g y , fg y) , (g y , gf y)))

 transport-map : ∀ {U} (ua : is-univalent U)
                {X X' Y : U ̇} (e : X ≃ X') (g : X → Y)
             → transport (λ - → - → Y) (eqtoid ua X X' e) g
             ≡ g ∘ eqtofun (≃-sym e)

 transport-map {U} ua {X} {X'} {Y} e = JEq ua X A b X' e
  where
   fe : funext U U
   fe = funext-from-univalence ua
   A : (X' : U ̇) → X ≃ X' → U ̇
   A X' e = (g : X → Y)
          → transport (λ (- : U ̇) → - → Y) (eqtoid ua X X' e) g
          ≡ g ∘ eqtofun (≃-sym e)
   b : A X (≃-refl X)
   b g = transport (λ - → - → Y) (eqtoid ua X X (≃-refl X)) g
                  ≡⟨ ap (λ - → transport (λ - → - → Y) - g) (eqtoid-refl ua X) ⟩
         g ∎

 Tχ : (σ : Σ \(X : U ̇) → X → Y) → T(χ σ) ≡ σ
 Tχ (X , f) = to-Σ-≡ (eqtoid ua _ _ (graph-domain-equiv f) ,
                       transport-map ua (graph-domain-equiv f) pr₁)

 χ-is-equivalence : is-equiv χ
 χ-is-equivalence = (T , χT) , (T , Tχ)

 classification-equivalence : (Σ \(X : U ̇) → X → Y) ≃ (Y → U ̇)
 classification-equivalence = χ , χ-is-equivalence


module subtype-classifier
        {U : Universe}
        (fe' : funext U (U ′))
        (ua : is-univalent U)
        (Y : U ̇)
       where

 fe : funext U U
 fe = funext-from-univalence ua

 χ : (Σ \(X : U ̇) → X ↪ Y)  → (Y → Ω U)
 χ (X , f , i) y = fiber f y , i y

 T : (Y → Ω U) → Σ \(X : U ̇) → X ↪ Y
 T P = (Σ \(y : Y) → P y holds) , pr₁ , pr₁-embedding (λ y → holds-is-prop (P y))

 χT : (P : Y → Ω U) → χ(T P) ≡ P
 χT P = dfunext fe' γ
  where
   f : ∀ y → χ (T P) y holds → P y holds
   f y ((.y , h) , refl) = h
   g : ∀ y → P y holds → χ (T P) y holds
   g y h = (y , h) , refl
   γ : (y : Y) → χ (T P) y ≡ P y
   γ y = PropExt-from-univalence ua (f y) (g y)

 transport-embedding : {X X' Y : U ̇} (e : X ≃ X') (g : X → Y) (i : is-embedding g)
                    → transport (λ - → - ↪ Y) (eqtoid ua X X' e) (g , i)
                    ≡ g ∘ eqtofun (≃-sym e) , comp-embedding
                                                 (is-equiv-is-embedding (eqtofun (≃-sym e))
                                                                        (is-equiv-eqtofun (≃-sym e))) i
 transport-embedding {X} {X'} {Y} e = JEq ua X A b X' e
  where
   A : (X' : U ̇) → X ≃ X' → U ̇
   A X' e = (g : X → Y) (i : is-embedding g)
          → transport (λ (- : U ̇) → - ↪ Y) (eqtoid ua X X' e) (g , i)
          ≡ g ∘ eqtofun (≃-sym e) ,
            comp-embedding (is-equiv-is-embedding (eqtofun (≃-sym e))
                           (is-equiv-eqtofun (≃-sym e))) i
   b : A X (≃-refl X)
   b g i = transport (λ - → - ↪ Y) (eqtoid ua X X (≃-refl X)) (g , i)
                  ≡⟨ ap (λ - → transport (λ - → - ↪ Y) - (g , i)) (eqtoid-refl ua X) ⟩
           g , i
                  ≡⟨ to-Σ-≡' (is-embedding-is-prop fe fe g _ _) ⟩
           g , comp-embedding
               (is-equiv-is-embedding (eqtofun (≃-sym (≃-refl X))) (is-equiv-eqtofun (≃-sym (≃-refl X)))) i ∎

 Tχ : (σ : Σ \(X : U ̇) → X ↪ Y) → T(χ σ) ≡ σ
 Tχ (X , f , i) = to-Σ-≡ (eqtoid ua _ _ (graph-domain-equiv f) ,
                          (transport-embedding (graph-domain-equiv f) pr₁ (pr₁-embedding i)
                         ∙ to-Σ-≡' (is-embedding-is-prop fe fe f _ _)))

 χ-is-equivalence : is-equiv χ
 χ-is-equivalence = (T , χT) , (T , Tχ)

 classification-equivalence : (Σ \(X : U ̇) → X ↪ Y) ≃ (Y → Ω U)
 classification-equivalence = χ , χ-is-equivalence

\end{code}

TODO. Consider a property "green" of types, and call a map green if
its fibers are all green. Then the maps of Y into green types should
correspond to the green maps X → Y. This generalizes the above
situation. In particular, the case green = contractible is of interest
and describes a previously known situation. Another example is that
surjections X → Y is in bijection with familities Y → Σ (Z : U ̇) → ∥ Z
∥), that is, families of inhabited types. It is not necessary that
"green" is proposition valued. It can be universe valued in general.
