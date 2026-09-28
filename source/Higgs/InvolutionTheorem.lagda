Martin Escardo, 15 August 2014.

Higgs' Involution Theorem. In any 1-topos, if f : Ω → Ω is a
monomorphism, then it is an involution.

This is attributed to Denis Higgs in the literature.

We adapt and prove the result in univalent mathematics, using
propositional and functional extensionality. We don't rely on
propositional resizing (or impredicativity).

There is a proof by diagram chasing with iterated pullbacks, in page
65 of Johnstone's Sketches of an Elephant, volume 1.

The proof given here is based on an exercise in page 160 of Lambek and
Scott's Introduction to Higher-Order Categorical Logic, attributed to
Scedrov. Thanks to Phil Scott for bringing my attention to this proof
during a visit to Birmingham.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.Subsingletons
open import UF.SubtypeClassifier renaming (Ω to Ω-of-universe)

\end{code}

We work with a universe 𝓤 and assume functional and propositional
extensionality:

\begin{code}

module Higgs.InvolutionTheorem
        {𝓤 : Universe}
        (fe : Fun-Ext)
        (pe : propext 𝓤)
       where

Ω = Ω-of-universe 𝓤

\end{code}

Recall that a map f is left-cancellable if f p ＝ f q → p ＝ q, and
involutive if f (f p) ＝ p.

\begin{code}

higgs-involution-theorem : (f : Ω → Ω) → left-cancellable f → involutive f
higgs-involution-theorem f lc = VIII
 where
  I : (p : Ω) → f p ＝ ⊤ → p ＝ ⊤ → f ⊤ ＝ ⊤
  I p r s = transport (λ - → f - ＝ ⊤) s r

  II : (p : Ω) → f p ＝ ⊤ → f ⊤ ＝ ⊤ → p ＝ ⊤
  II p r s = lc (f p ＝⟨ r ⟩
                 ⊤   ＝⟨ s ⁻¹ ⟩
                 f ⊤ ∎)

  III : (p : Ω) → f p ＝ ⊤ → p ＝ f ⊤
  III p r = Ω-ext pe fe (I p r) (II p r)

  IV : (p : Ω) → f (f p) ＝ ⊤ → p ＝ ⊤
  IV p r = lc (III (f p) r)

  V : (p : Ω) → f (f (f p)) ＝ ⊤ → f p ＝ ⊤
  V p = IV (f p)

  VI : (p : Ω) → f p ＝ ⊤ → f (f (f p)) ＝ ⊤
  VI p r = f (f (f p)) ＝⟨ ap (f ∘ f) r ⟩
           f (f ⊤)     ＝⟨ ap f ((III p r)⁻¹) ⟩
           f p         ＝⟨ r ⟩
           ⊤           ∎

  VII : (p : Ω) → f (f (f p)) ＝ f p
  VII p = Ω-ext pe fe (V p) (VI p)

  VIII : (p : Ω) → f (f p) ＝ p
  VIII p = lc (VII p)

\end{code}

Added 2nd November 2023. Some immediate corollaries.

\begin{code}

open import UF.Embeddings
open import UF.Equiv hiding (_≅_ ; ≅-refl)
open import UF.Equiv-FunExt

autoembeddings-of-Ω-are-involutive : (f : Ω → Ω) → is-embedding f → involutive f
autoembeddings-of-Ω-are-involutive f e =
 higgs-involution-theorem f (embeddings-are-lc f e)

autoembeddings-of-Ω-are-equivs : (f : Ω → Ω) → is-embedding f → is-equiv f
autoembeddings-of-Ω-are-equivs f e =
 involutions-are-equivs f (autoembeddings-of-Ω-are-involutive f e)

automorphisms-of-Ω-are-involutive : (f : Ω → Ω) → is-equiv f → involutive f
automorphisms-of-Ω-are-involutive f e =
 higgs-involution-theorem f (equivs-are-lc f e)

Aut-Ω-is-boolean : (𝕗 : Aut Ω) → 𝕗 ● 𝕗 ＝ 𝕚𝕕
Aut-Ω-is-boolean 𝕗@(f , e) = to-≃-＝ fe (automorphisms-of-Ω-are-involutive f e)

\end{code}

Notice that the fact that the autoembeddings of Ω are equivalences says that Ω
is Dedekind finite (which is recorded explicitly in Fin.Dedekind, which imports
this one).
