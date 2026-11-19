Martin Escardo, Paulo Oliva, 28th April - 26 May 2026.

Generalization of Part 2 of the module alpha-beta from March - April 2023.

We show how to compute optimal outcomes using the product of
quantifiers, rather than the product of selection functions.

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split #-}

open import MLTT.Spartan hiding (J)
open import UF.FunExt

module Games.OptimalPlaysViaProductsOfQuantifiers
        {𝓤 𝓦₀ : Universe}
        (R : 𝓦₀ ̇ )
        (fe : Fun-Ext)
       where

open import Games.FiniteHistoryDependent renaming (_Attains_ to Attains)
open import Games.TypeTrees
open import MonadOnTypes.J
open import MonadOnTypes.K

open J-definitions
open contravariant-functoriality-on-outcome-type
open K-definitions

\end{code}

We extend O-functor from types to type trees.

\begin{code}

𝓞-functor : (P : 𝓥 ̇ ) (Xt : 𝑻 {𝓤}) → 𝓙 R Xt → 𝓙 (R × P) Xt
𝓞-functor P []       ⟨⟩        = ⟨⟩
𝓞-functor P (X ∷ Xf) (ε :: εf) = (O-functor X pr₁ ε) ,
                                 (λ x → 𝓞-functor P (Xf x) (εf x))

\end{code}

We apply the following lemma for P := Path Xt and f := id. The general
version is needed to get a suitable induction hypothesis.

\begin{code}

lemma-𝓞-functor : {P : 𝓥 ̇ }
                  (Xt : 𝑻 {𝓤})
                  (εt : 𝓙 R Xt)
                  (q : Path Xt → R)
                  (f : Path Xt → P)
                → sequenceᴶ (R × P) (𝓞-functor P Xt εt) (λ xs → q xs , f xs)
                ＝ sequenceᴶ R εt q
lemma-𝓞-functor         []       ⟨⟩        q f = refl
lemma-𝓞-functor {𝓥} {P} (X ∷ Xf) (ε :: εf) q f = I
  where
   R' = R × P

   ε' : J X
   ε' = (λ p → ε (pr₁ ∘ p))

   δ : (x : X) → J (Path (Xf x))
   δ x = sequenceᴶ R (εf x)

   δ' : (x : X) → J (Path (Xf x))
   δ' x = sequenceᴶ R' (𝓞-functor P (Xf x) (εf x))

   q' : Path (X ∷ Xf) → R'
   q' xs = q xs , f xs

   x₀ x₁ : X
   x₀ = ε (λ x → subpred q x (δ' x (subpred q' x)))
   x₁ = ε (λ x → subpred q x (δ  x (subpred q  x)))

   IH : (x : X) → δ' x (subpred q' x) ＝ δ x (subpred q  x)
   IH x = lemma-𝓞-functor (Xf x) (εf x) (subpred q x) (subpred f x)

   e : x₀ ＝ x₁
   e = ap ε (dfunext fe (λ x → ap (subpred q x) (IH x)))

   I = sequenceᴶ R' (𝓞-functor P (X ∷ Xf) (ε :: εf)) q' ＝⟨ refl ⟩
       (ε' ⊗ᴶ δ') q'                            ＝⟨ refl ⟩
       x₀ :: δ' x₀ (subpred q' x₀)              ＝⟨ I₀ ⟩
       x₀ :: δ  x₀ (subpred q  x₀)              ＝⟨ I₁ ⟩
       x₁ :: δ  x₁ (subpred q  x₁)              ＝⟨ refl ⟩
       (ε ⊗ᴶ δ) q                               ＝⟨ refl ⟩
       sequenceᴶ R (ε :: εf) q                  ∎
    where
     I₀ = ap (x₀ ,_) (IH x₀)
     I₁ = ap (λ - → - :: δ - (subpred q -)) e

module _ (Xt : 𝑻 {𝓤})
         (ϕt : 𝓚 R Xt)
         (εt : 𝓙 R Xt)
       where

 R' = R × Path Xt

 εt' : 𝓙 R' Xt
 εt' = 𝓞-functor (Path Xt) Xt εt

 module _ (q : Path Xt → R)
        where

  q' : Path Xt → R'
  q' xs = q xs , xs

\end{code}

We now have two different ways of computing an optimal play, which
coincide:

\begin{code}

  lemma : sequenceᴶ R' εt' q' ＝ sequenceᴶ R εt q
  lemma = lemma-𝓞-functor Xt εt q id

  private
   G : Game R
   G = game Xt q ϕt

\end{code}

With this, we conclude that the optimal outcome of G together with the
particular optimal play sequenceᴶ R εt q can be computed as the
optimal outcome of G'.

\begin{code}

  module _ (ϕt' : 𝓚 R' Xt)
         where

   private
    G' : Game R'
    G' = game Xt q' ϕt'

   theorem
    : Attains R  εt  ϕt
    → Attains R' εt' ϕt'
    → (optimal-outcome R G , sequenceᴶ R εt q) ＝ optimal-outcome R' G'
   theorem a a'
    = optimal-outcome R G , sequenceᴶ R εt q        ＝⟨ I ⟩
      q (sequenceᴶ R εt q) , sequenceᴶ R εt q       ＝⟨ II ⟩
      q (sequenceᴶ R' εt' q') , sequenceᴶ R' εt' q' ＝⟨ refl ⟩
      q' (sequenceᴶ R' εt' q')                      ＝⟨ III ⟩
      optimal-outcome R' G'                         ∎
       where
        I   = ap (_, sequenceᴶ R εt q)
                 ((selection-strategy-corollary R fe G εt a)⁻¹)
        II  = ap (λ - → q - , -) (lemma ⁻¹)
        III = selection-strategy-corollary R' fe G' εt' a'

\end{code}

We are interested in the following corollary, which shows how to
compute a product of attainable selection functions as a product of
quantifiers, provided εt' attains ϕt.

\begin{code}

   products-of-selection-functions-via-products-of-quantifiers
    : Attains R  εt  ϕt
    → Attains R' εt' ϕt'
    → sequenceᴶ R εt q ＝ pr₂ (sequenceᴷ R' ϕt' q')
   products-of-selection-functions-via-products-of-quantifiers a a'
    = ap pr₂ (theorem a a')

   optimal-outcomes-coincide
    : Attains R  εt  ϕt
    → Attains R' εt' ϕt'
    → optimal-outcome R G ＝ pr₁ (optimal-outcome R' G')
   optimal-outcomes-coincide a a'
    = ap pr₁ (theorem a a')

\end{code}
