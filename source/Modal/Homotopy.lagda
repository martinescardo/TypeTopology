Jon Sterling, started 5th Oct 2022

This file contains some lemmas about precomposing embeddings onto homotopies.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Modal.Homotopy where

open import MLTT.Spartan
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.FunExt

homotopy-precomp
  : {𝓤 𝓥 𝓦 : Universe}
  → {U : 𝓤 ̇ } {X : 𝓥 ̇ } {Y : 𝓦 ̇ }
  → (f g : X → Y)
  → (i : U → X)
  → f ∼ g
  → f ∘ i ∼ g ∘ i
homotopy-precomp f g i h =
 h ∘ i

\end{code}

The following is a slight generalization of Lemma 5.1.18 of Egbert Rijke's
doctoral dissertation.

\begin{code}
homotopy-precomp-by-embedding-is-equiv
 : {𝓤 𝓥 𝓦 : Universe}
 → (fe0 : funext 𝓥 𝓦)
 → (fe1 : funext 𝓤 𝓦)
 → (fe2 : funext (𝓥 ⊔ 𝓦) (𝓤 ⊔ 𝓦))
 → (fe3 : funext (𝓥 ⊔ 𝓦) (𝓥 ⊔ 𝓦))
 → {U : 𝓤 ̇ } {X : 𝓥 ̇ } {Y : 𝓦 ̇ }
 → (f g : X → Y)
 → (i : U → X)
 → (precomp-i-is-emb : is-embedding λ (- : X → Y) → - ∘ i)
 → is-equiv (homotopy-precomp f g i)
homotopy-precomp-by-embedding-is-equiv fe0 fe1 fe2 fe3 f g i precomp-i-is-emb =
 transport is-equiv composite-is-precomp (eqtofun- composite)

 where
  composite : f ∼ g ≃ (f ∘ i ∼ g ∘ i)
  composite =
   ≃-sym (≃-funext fe0 f g)
    ● (ap (_∘ i) , embedding-gives-embedding' _ precomp-i-is-emb _ _)
    ● ≃-funext fe1 (f ∘ i) (g ∘ i)

  composite-is-precomp : eqtofun composite ＝ homotopy-precomp f g i
  composite-is-precomp =
   dfunext fe2 λ h →
   eqtofun composite h ＝⟨ ap happly (aux h) ⟩
   happly (dfunext fe1 (h ∘ i)) ＝⟨ happly-funext fe1 _ _ (h ∘ i) ⟩
   homotopy-precomp f g i h ∎

   where
    aux : (h : f ∼ g) → ap (_∘ i) (inverse _ (fe0 f g) h) ＝ dfunext fe1 (h ∘ i)
    aux h =
     ap (_∘ i) (inverse (happly' f g) (fe0 f g) h)
      ＝⟨ ap (λ - → ap (_∘ i) (- h)) (inverse-happly-is-dfunext fe0 fe3 f g) ⟩
     ap (_∘ i) (dfunext fe0 h)
      ＝⟨ ap-precomp-funext _ _ i h fe0 fe1 ⟩
     dfunext fe1 (h ∘ i) ∎

\end{code}
