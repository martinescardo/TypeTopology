Martin Escardo 12-13 March 2024.

We construct an embedding of ℕ∞ into ℕ⊥, the lifting on ℕ, or the
flat domain of natural numbers, and prove various properties of it.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.Subsingletons

module CoNaturals.Sharp
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

ℕ⊥ = 𝓛 ℕ

\end{code}

We define sharp : ℕ∞ → ℕ⊥ so that

 * sharp (ι n) ＝ η n and

 * sharp ∞ ＝ ⊥.

\begin{code}

sharp : ℕ∞ → ℕ⊥
sharp x = is-finite x , size , being-finite-is-prop fe₀ x

sharp-finite : (n : ℕ) → sharp (ι n) ＝ η n
sharp-finite n = II
 where
  I : sharp (ι n) ⊑ η n
  I = unique-to-𝟙 , (λ (n , p) → ℕ-to-ℕ∞-lc p)

  II : sharp (ι n) ＝ η n
  II = ⊑-anti-lemma pe fe₀ fe₀ I
        (λ (_ : is-defined (η n)) → ℕ-to-ℕ∞-is-finite n)

sharp-∞ : sharp ∞ ＝ ⊥
sharp-∞ = II
 where
  I : sharp ∞ ⊑ ⊥
  I = is-infinite-∞ , (λ is-finite-∞ → 𝟘-elim (is-infinite-∞ is-finite-∞))

  II : sharp ∞ ＝ ⊥
  II = ⊑-anti pe fe₀ fe₀ (I , ⊥-least (sharp ∞))

\end{code}

It is left-cancellable and hence and embedding.

\begin{code}

sharp-lc : left-cancellable sharp
sharp-lc {x} {y} e = II
 where
  I : (x y : ℕ∞) → sharp x ⋍· sharp y → (n : ℕ) → ι n ＝ x → ι n ＝ y
  I x y a n e =
   ι n                      ＝⟨ ap ι (g (n , e)) ⟩
   ι (size (⌜ f ⌝ (n , e))) ＝⟨ size-property (⌜ f ⌝ (n , e)) ⟩
   y                        ∎
   where
    f : is-finite x ≃ is-finite y
    f = is-defined-⋍· (sharp x) (sharp y) a

    g : (φ : is-finite x) → size φ ＝ size (⌜ f ⌝ φ)
    g = value-⋍· (sharp x) (sharp y) a

  II : x ＝ y
  II = ℕ∞-equality-criterion fe₀ x y
        (I x y (Id-to-⋍· _ _ e))
        (I y x (Id-to-⋍· _ _ (e ⁻¹)))

sharp-is-embedding : is-embedding sharp
sharp-is-embedding =
 lc-maps-into-sets-are-embeddings sharp sharp-lc
  (lifting-of-set-is-set fe₀ fe₀ pe ℕ ℕ-is-set)

\end{code}

We have the following two corollaries.

\begin{code}

sharp-finite' : (x : ℕ∞) (n : ℕ) → sharp x ＝ η n → x ＝ ι n
sharp-finite' x n e = sharp-lc (sharp x     ＝⟨ e ⟩
                              η n        ＝⟨ (sharp-finite n)⁻¹ ⟩
                              sharp (ι n) ∎)

sharp-∞' : (x : ℕ∞) → sharp x ＝ ⊥ → x ＝ ∞
sharp-∞' x e = sharp-lc (sharp x ＝⟨ e ⟩
                       ⊥      ＝⟨ sharp-∞ ⁻¹ ⟩
                       sharp ∞ ∎)

\end{code}

The image of the embedding has empty complement, in the following
sense.

\begin{code}

sharp-image-has-empty-complement : ¬ (Σ l ꞉ ℕ⊥ , ((x : ℕ∞) → sharp x ≠ l))
sharp-image-has-empty-complement (l , f) =
 η-image fe₀ fe₀ pe
   (l ,
   (λ (e : l ＝ ⊥)
         → f ∞ (sharp ∞ ＝⟨ sharp-∞ ⟩
                ⊥      ＝⟨ e ⁻¹ ⟩
                l      ∎)) ,
   (λ n (e : l ＝ η n)
         → f (ι n)
              (sharp (ι n) ＝⟨ sharp-finite n ⟩
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

 sharp-is-surjection-gives-EM : is-surjection sharp → EM 𝓤₀
 sharp-is-surjection-gives-EM sharp-is-surjection P P-is-prop =
  ∥∥-rec (decidability-of-prop-is-prop fe₀ P-is-prop) II I
  where
   y : ℕ⊥
   y = P , (λ _ → 0) , P-is-prop

   I : ∃ x ꞉ ℕ∞ , sharp x ＝ y
   I = sharp-is-surjection y

   II : (Σ x ꞉ ℕ∞ , sharp x ＝ y) → P + ¬ P
   II (x , e) = IV III
    where
     III : (ι 0 ＝ x) + (ι 0 ≠ x)
     III = finite-isolated fe₀ 0 x

     IV : (ι 0 ＝ x) + (ι 0 ≠ x) → P + ¬ P
     IV (inl d) = inl (⌜ C ⌝⁻¹ ⋆)
      where
       A = y          ＝⟨ e ⁻¹ ⟩
           sharp x     ＝⟨ ap sharp (d ⁻¹) ⟩
           sharp (ι 0) ＝⟨ sharp-finite 0 ⟩
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
         C₀ = sharp x ＝⟨ e ⟩
              y      ＝⟨ d ⟩
              η 0    ∎

         C₁ : x ＝ ι 0
         C₁ = sharp-finite' x 0 C₀

 EM-gives-sharp-is-surjection : EM 𝓤₀ → is-surjection sharp
 EM-gives-sharp-is-surjection em y@(P , φ , P-is-prop) =
   ∣ I (em P P-is-prop) ∣
  where
   I : P + ¬ P → Σ x ꞉ ℕ∞ , sharp x ＝ y
   I (inl p) = ι (φ p) , III
    where
     II : sharp (ι (φ p)) ⊑ y
     II = (λ _ → p) , (λ (n , e) → ℕ-to-ℕ∞-lc e)

     III : sharp (ι (φ p)) ＝ y
     III = ⊑-anti-lemma pe fe₀ fe₀ II (λ _ → ℕ-to-ℕ∞-is-finite (φ p))

   I (inr ν) = ∞ , III
    where
     II : sharp ∞ ⊑ y
     II = transport (_⊑ y) (sharp-∞ ⁻¹) (⊥-least y)

     III : sharp ∞ ＝ y
     III = ⊑-anti-lemma pe fe₀ fe₀ II λ (p : P) → 𝟘-elim (ν p)

\end{code}

In progress. The image of sharp consists precisely of the sharp
elements of ℕ⊥ in the sense of [1].

[1] Tom de Jong. Apartness, sharp elements, and the Scott topology of
    domains.
    Mathematical Structures in Computer Science , Volume 33 , Issue 7,
    August 2023 , pp. 573 - 604.
    https://doi.org/10.1017/S0960129523000282
