Ian Ray, 7 February 2024

Singleton Properties. Of course there are a lot more we can add to this file.
For now we will show that singletons are closed under Σ types and equivalence.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Subsingletons

module UF.Singleton-Properties where

Σ-is-singleton : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
               → is-singleton X
               → ((x : X) → is-singleton (A x))
               → is-singleton (Σ A)
Σ-is-singleton {X = X} {A = A} (c , C) h = ((c , center (h c)) , Σ-centrality)
 where
  Σ-centrality : is-central (Σ A) (c , center (h c))
  Σ-centrality (x , a) = ⌜ Σ-＝-≃ ⌝⁻¹ (C x , p)
   where
    p = transport A (C x) (center (h c)) ＝⟨ centrality (h x)
                                                (transport A (C x)
                                                     (center (h c))) ⁻¹ ⟩
        center (h x)                     ＝⟨ centrality (h x) a ⟩
        a                                ∎

≃-is-singleton : FunExt
               → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
               → is-singleton X
               → is-singleton Y
               → is-singleton (X ≃ Y)
≃-is-singleton fe i j = pointed-props-are-singletons
                         (singleton-≃ i j)
                         (≃-is-prop fe (singletons-are-props j))

\end{code}

Added by Martin Escardo 22nd June 2025.

\begin{code}

open import UF.Subsingletons-FunExt

the-singletons-form-a-singleton-type
 : funext 𝓤 𝓤
 → propext 𝓤
 → is-singleton (Σ X ꞉ 𝓤 ̇ , is-singleton X)
the-singletons-form-a-singleton-type {𝓤} fe pe =
 equiv-to-singleton
  ((Σ X ꞉ 𝓤 ̇ , is-singleton X) ≃⟨ Σ-cong I ⟩
   (Σ X ꞉ 𝓤 ̇ , is-prop X × X) ■)
 (the-true-props-form-a-singleton-type fe pe)
  where
   I = λ X → logically-equivalent-props-are-equivalent
              (being-singleton-is-prop fe)
              (prop-criterion
                (λ (X-is-prop , _) → ×-is-prop
                                      (being-prop-is-prop fe)
                                      X-is-prop))
              (λ (i : is-singleton X) → singletons-are-props i , center i)
              (λ (j , x) → pointed-props-are-singletons x j)

\end{code}

Added 19 June 2026 by Tom de Jong.

\begin{code}

consts : (A : 𝓤 ̇ ) (X : 𝓥 ̇ ) → X → (A → X)
consts A X x = λ _ → x

universal-property-of-singletons⁻ : 𝓤 ̇  → 𝓤 ⁺ ̇
universal-property-of-singletons⁻ {𝓤} A =
 (X : 𝓤 ̇ ) → is-equiv (consts A X)

universal-property-of-singletons : 𝓤 ̇  → 𝓤ω
universal-property-of-singletons {𝓤} A =
 {𝓥 : Universe} (X : 𝓥 ̇ ) → is-equiv (consts A X)

singletons-satisfy-universal-property : Fun-Ext
                                      → {A : 𝓤 ̇ }
                                      → is-singleton A
                                      → universal-property-of-singletons A
singletons-satisfy-universal-property fe {A} s X =
 qinvs-are-equivs (consts A X) (f , (λ _ → refl) , II)
  where
   f : (A → X) → X
   f g = g (center s)
   II : (λ g _ → g (center s)) ∼ id
   II g = dfunext fe (λ a → ap g (centrality s a))

singleton-if-consts-is-equiv : {A : 𝓤 ̇ }
                             → is-equiv (consts A A)
                             → is-singleton A
singleton-if-consts-is-equiv {𝓤} {A} e = a₀ , I
 where
  c : A → A → A
  c = consts A A

  f : (A → A) → A
  f = inverse (consts A A) e

  a₀ : A
  a₀ = f id

  I : (a : A) → a₀ ＝ a
  I a = a₀         ＝⟨refl⟩
        c a₀ a     ＝⟨refl⟩
        c (f id) a ＝⟨ happly (inverses-are-sections c e id) a ⟩
        id a       ＝⟨refl⟩
        a          ∎

singleton-if-universal-property⁻ : {A : 𝓤 ̇ }
                                 → universal-property-of-singletons⁻ A
                                 → is-singleton A
singleton-if-universal-property⁻ {𝓤} {A} up =
 singleton-if-consts-is-equiv (up A)

singleton-if-universal-property : {A : 𝓤 ̇ }
                                → universal-property-of-singletons A
                                → is-singleton A
singleton-if-universal-property {𝓤} {A} up = singleton-if-universal-property⁻ up

\end{code}
