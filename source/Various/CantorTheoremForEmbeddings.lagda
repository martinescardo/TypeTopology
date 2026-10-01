Jon Sterling, 25th March 2023.

Proof of Cantor's theorem stated for embeddings from the powerset of A
onto A. This proof uses function extensionality, propositional
extensionality, and propositional resizing. Our argument follows Paul
Taylor's Practical Foundations of Mathematics, via the nLab:
https://ncatlab.org/nlab/show/Cantor%27s+theorem.

This applies Cantor's theorem for surjections, proved in
Various.LawvereFPT.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Various.CantorTheoremForEmbeddings where

open import MLTT.Spartan


open import UF.Base
open import UF.Embeddings
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.FunExt
open import UF.Size
open import Various.LawvereFPT
open import UF.SubtypeClassifier

open retract-version

cantor-theorem-for-embeddings
 : FunExt
 → PropExt
 → Propositional-Resizing
 → (A : 𝓤 ̇ )
 → (ϕ : (A → Ω₀) → A)
 → ¬ is-embedding ϕ
cantor-theorem-for-embeddings {𝓤} fe pe psz A ϕ ϕ-emb =
 cantor-theorem (fe _ _) A retr retr-has-section
 where

  retr-large : A → (A → Ω (𝓤₀ ⁺ ⊔ 𝓤))
  pr₁ (retr-large a b) = Π U ꞉ (A → Ω₀) , (ϕ U ＝ a → U b holds)
  pr₂ (retr-large a b) =
   Π-is-prop (fe _ _) λ U →
   Π-is-prop (fe _ _) λ _ →
   holds-is-prop (U b)

  retr : A → (A → Ω₀)
  pr₁ (retr a b) =
   resize psz
    (retr-large a b holds)
    (holds-is-prop (retr-large a b))
  pr₂ (retr a b) =
   resize-is-prop psz
    (retr-large a b holds)
    (holds-is-prop (retr-large a b))

  retr-has-section : has-section· retr
  pr₁ retr-has-section U = ϕ U
  pr₂ retr-has-section U a =
   to-Σ-＝ (lem·0 , being-prop-is-prop (fe 𝓤₀ 𝓤₀) _ _)
   where
    fwd : retr-large (ϕ U) a holds → U a holds
    fwd p = p U refl

    bwd : U a holds → retr-large (ϕ U) a holds
    bwd p V q =
     transport⁻¹
      (λ W → W a holds)
      (embeddings-are-lc ϕ ϕ-emb q)
      p

    lem·0 : resize psz (retr-large (ϕ U) a holds) _ ＝ U a holds
    lem·0 =
     pe 𝓤₀
      (resize-is-prop psz _ _)
      (holds-is-prop (U a))
      (fwd ∘ from-resize psz _ _)
      (to-resize psz _ _ ∘ bwd)

\end{code}
