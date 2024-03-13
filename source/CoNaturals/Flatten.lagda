Martin Escardo 12-13 March 2024.

We construct an embedding of ℕ∞ into 𝓛 ℕ, the lifting on ℕ, or the
flat domain of natural numbers, and prove various properties of it.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.Subsingletons

module CoNaturals.Flatten
        (fe₀ : funext 𝓤₀ 𝓤₀)
        (pe : Prop-Ext)
       where

open import CoNaturals.GenericConvergentSequence
open import Lifting.Construction 𝓤₀
open import Lifting.IdentityViaSIP 𝓤₀ {𝓤₀} {ℕ}
open import Lifting.Set 𝓤₀
open import Lifting.UnivalentPrecategory 𝓤₀ {𝓤₀} ℕ
open import Notation.CanonicalMap
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons-FunExt

\end{code}

We refer to the following as the flatting map, but write flat for short.

\begin{code}

flat : ℕ∞ → 𝓛 ℕ
flat x = is-finite x , size , being-finite-is-prop fe₀ x

\end{code}

This map satisfies flat (ι n) ＝ η n and flat ∞ ＝ ⊥.

\begin{code}

flat-finite : (n : ℕ) → flat (ι n) ＝ η n
flat-finite n = II
 where
  I : flat (ι n) ⊑ η n
  I = unique-to-𝟙 , (λ (n , p) → ℕ-to-ℕ∞-lc p)

  II : flat (ι n) ＝ η n
  II = ⊑-anti-lemma pe fe₀ fe₀ I (λ _ → n , refl)

flat-∞ : flat ∞ ＝ ⊥
flat-∞ = II
 where
  I : flat ∞ ⊑ ⊥
  I = is-infinite-∞ , (λ is-finite-∞ → 𝟘-elim (is-infinite-∞ is-finite-∞))

  II : flat ∞ ＝ ⊥
  II = ⊑-anti-lemma pe fe₀ fe₀ I 𝟘-elim

\end{code}

It is left-cancellable and hence and embedding.

\begin{code}

flat-lc : left-cancellable flat
flat-lc {x} {y} e = ℕ∞-equality-criterion fe₀ x y
                     (h x y (Id-to-⋍· _ _ e))
                     (h y x (Id-to-⋍· _ _ (e ⁻¹)))
 where
  h : (x y : ℕ∞) → flat x ⋍· flat y → (n : ℕ) → ι n ＝ x → ι n ＝ y
  h x y a n e =
   ι n                      ＝⟨ ap ι (g (n , e)) ⟩
   ι (size (⌜ f ⌝ (n , e))) ＝⟨ size-property (⌜ f ⌝ (n , e)) ⟩
   y                        ∎
   where
    f : is-finite x ≃ is-finite y
    f = is-defined-⋍· (flat x) (flat y) a

    g : (φ : is-finite x) → size φ ＝ size (⌜ f ⌝ φ)
    g = value-⋍· (flat x) (flat y) a

flat-is-embedding : is-embedding flat
flat-is-embedding =
 lc-maps-into-sets-are-embeddings flat flat-lc
  (lifting-of-set-is-set fe₀ fe₀ pe ℕ ℕ-is-set)

\end{code}

We have the following two corollaries.

\begin{code}

flat-finite' : (x : ℕ∞) (n : ℕ) → flat x ＝ η n → x ＝ ι n
flat-finite' x n e = flat-lc (flat x     ＝⟨ e ⟩
                              η n        ＝⟨ (flat-finite n)⁻¹ ⟩
                              flat (ι n) ∎)

flat-∞' : (x : ℕ∞) → flat x ＝ ⊥ → x ＝ ∞
flat-∞' x e = flat-lc (flat x ＝⟨ e ⟩
                       ⊥      ＝⟨ flat-∞ ⁻¹ ⟩
                       flat ∞ ∎)

\end{code}

The image of the embedding has empty complement, in the following
sense.

\begin{code}

flat-image-has-empty-complement : ¬ (Σ l ꞉ 𝓛 ℕ , ((x : ℕ∞) → flat x ≠ l))
flat-image-has-empty-complement (l , f) =
 η-image fe₀ fe₀ pe
   (l ,
   (λ (e : l ＝ ⊥)
         → f ∞ (flat ∞ ＝⟨ flat-∞ ⟩
                ⊥      ＝⟨ e ⁻¹ ⟩
                l      ∎)) ,
   (λ n (e : l ＝ η n)
         → f (ι n)
              (flat (ι n) ＝⟨ flat-finite n ⟩
               η n        ＝⟨ e ⁻¹ ⟩
               l          ∎)))

\end{code}

But the embedding is a surjection if and only if excluded middle
holds.

\begin{code}

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt
 open import UF.ImageAndSurjection pt
 open import UF.ExcludedMiddle

 flat-is-surjection-gives-EM : is-surjection flat → EM 𝓤₀
 flat-is-surjection-gives-EM flat-is-surjection P P-is-prop =
  ∥∥-rec (decidability-of-prop-is-prop fe₀ P-is-prop) II I
  where
   y : 𝓛 ℕ
   y = P , (λ _ → 0) , P-is-prop

   I : ∃ x ꞉ ℕ∞ , flat x ＝ y
   I = flat-is-surjection y

   II : (Σ x ꞉ ℕ∞ , flat x ＝ y) → P + ¬ P
   II (x , e) = IV III
    where
     III : (ι 0 ＝ x) + (ι 0 ≠ x)
     III = finite-isolated fe₀ 0 x

     IV : (ι 0 ＝ x) + (ι 0 ≠ x) → P + ¬ P
     IV (inl d) = inl (⌜ C ⌝⁻¹ ⋆)
      where
       A = y          ＝⟨ e ⁻¹ ⟩
           flat x     ＝⟨ ap flat (d ⁻¹) ⟩
           flat (ι 0) ＝⟨ flat-finite 0 ⟩
           η 0        ∎

       B : y ⋍· η 0
       B = Id-to-⋍· _ _ A

       C : P ≃ 𝟙
       C = is-defined-⋍· y (η 0) B

     IV (inr ν) = inr (contrapositive B C)
      where
       A : y ⊑ η 0
       A = unique-to-𝟙 , (λ (p : P) → refl)

       B : P → y ＝ η 0
       B p = ⊑-anti-lemma pe fe₀ fe₀ A (λ _ → p)

       C : ¬ (y ＝ η 0)
       C d = ν (C₁ ⁻¹)
        where
         C₀ = flat x ＝⟨ e ⟩
              y      ＝⟨ d ⟩
              η 0    ∎

         C₁ : x ＝ ι 0
         C₁ = flat-finite' x 0 C₀

 EM-flat-is-surjection-gives : EM 𝓤₀ → is-surjection flat
 EM-flat-is-surjection-gives em y@(P , φ , P-is-prop) =
   ∣ I (em P P-is-prop) ∣
  where
   I : P + ¬ P → Σ x ꞉ ℕ∞ , flat x ＝ y
   I (inl p) = ι (φ p) , III
    where
     II : flat (ι (φ p)) ⊑ y
     II = (λ _ → p) , (λ (n , e) → ℕ-to-ℕ∞-lc e)

     III : flat (ι (φ p)) ＝ y
     III = ⊑-anti-lemma pe fe₀ fe₀ II (λ _ → φ p , refl)

   I (inr ν) = ∞ , III
    where
     II : flat ∞ ⊑ y
     II = transport (_⊑ y) (flat-∞ ⁻¹) (⊥-least y)

     III : flat ∞ ＝ y
     III = ⊑-anti-lemma pe fe₀ fe₀ II λ (p : P) → 𝟘-elim (ν p)

\end{code}
