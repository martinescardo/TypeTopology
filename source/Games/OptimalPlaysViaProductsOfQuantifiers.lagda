Martin Escardo, Paulo Oliva, 28th April - 26 May 2026.

Generalization of Part 2 of the module alpha-beta from March - April 2023.

We show how to compute optimal outcomes using the product of
quantifiers, rather than the product of selection functions.

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split #-}

\end{code}

We now define standard minimax games.

\begin{code}

open import MLTT.Spartan hiding (J)

module Games.OptimalPlaysViaProductsOfQuantifiers
        {𝓤 𝓦₀ : Universe}
        (R : 𝓦₀ ̇ )
       where

open import Games.FiniteHistoryDependent renaming (_Attains_ to Attains)
open import Games.TypeTrees
open import MonadOnTypes.J
open import MonadOnTypes.K
open import UF.FunExt

open J-definitions
open K-definitions

private
 ψ : (P : 𝓥 ̇ ) (Xt : 𝑻 {𝓤}) → 𝓙 R Xt → 𝓙 (R × P) Xt
 ψ P []       ⟨⟩        = ⟨⟩
 ψ P (X ∷ Xf) (ε :: εf) = (λ p → ε (pr₁ ∘ p)) , (λ x → ψ P (Xf x) (εf x))

 lemma-ψ : (fe : Fun-Ext)
           {P : 𝓥 ̇ }
           (Xt : 𝑻 {𝓤})
           (εt : 𝓙 R Xt)
           (q : Path Xt → R)
           (f : Path Xt → P)
         → sequenceᴶ (R × P) (ψ P Xt εt) (λ xs → q xs , f xs)
         ＝ sequenceᴶ R εt q
 lemma-ψ fe []       ⟨⟩        q f = refl
 lemma-ψ fe {P} (X ∷ Xf) (ε :: εf) q f = I
   where
    R' = R × P

    ε' : J X
    ε' = (λ p → ε (pr₁ ∘ p))

    δ : (x : X) → J (Path (Xf x))
    δ x = sequenceᴶ R (εf x)

    δ' : (x : X) → J (Path (Xf x))
    δ' x = sequenceᴶ R' (ψ P (Xf x) (εf x))

    q' : Path (X ∷ Xf) → R'
    q' xs = q xs , f xs

    x₀ x₁ : X
    x₀ = ε (λ x → subpred q x (δ' x (subpred q' x)))
    x₁ = ε (λ x → subpred q x (δ  x (subpred q  x)))

    IH : (x : X) → δ' x (subpred q' x) ＝ δ x (subpred q  x)
    IH x = lemma-ψ fe (Xf x) (εf x) (subpred q x) (subpred f x)

    e : x₀ ＝ x₁
    e = ap ε (dfunext fe (λ x → ap (subpred q x) (IH x)))

    I = sequenceᴶ R' (ψ P (X ∷ Xf) (ε :: εf)) q' ＝⟨ refl ⟩
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
         (⦅1⦆ : Attains R εt ϕt)
       where

 R' = R × Path Xt

 εt' : 𝓙 R' Xt
 εt' = ψ (Path Xt) Xt εt

 module _ (ϕt' : 𝓚 R' Xt)
          (⦅2⦆ : Attains R' εt' ϕt')
          (q : Path Xt → R)
          (fe : Fun-Ext)
        where

   q' : Path Xt → R'
   q' xs = q xs , xs

   lemma : sequenceᴶ R' εt' q' ＝ sequenceᴶ R εt q
   lemma = lemma-ψ fe Xt εt q id

   private
    G' : Game R'
    G' = game Xt q' ϕt'

    G : Game R
    G = game Xt q ϕt

   theorem : (optimal-outcome R G) , sequenceᴶ R εt q ＝ optimal-outcome R' G'
   theorem =
    optimal-outcome R G , sequenceᴶ R εt q        ＝⟨ I ⟩
    q (sequenceᴶ R εt q) , sequenceᴶ R εt q       ＝⟨ II ⟩
    q (sequenceᴶ R' εt' q') , sequenceᴶ R' εt' q' ＝⟨ refl ⟩
    q' (sequenceᴶ R' εt' q')                      ＝⟨ III ⟩
    optimal-outcome R' G'                         ∎
     where
      I   = ap (_, sequenceᴶ R εt q) ((selection-strategy-corollary R fe G εt ⦅1⦆)⁻¹)
      II  = ap (λ - → q - , -) (lemma ⁻¹)
      III = selection-strategy-corollary R' fe G' εt' ⦅2⦆

\end{code}
