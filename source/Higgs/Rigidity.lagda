Martin Escardo, 24-26 October 2023.

A type is called rigid if its only automorphism is the identity. In
HoTT/UF, we would instead say that its type of automorphisms is
contractible.

The type Ω is not rigid in boolean toposes, because in such toposes it
has precisely two automorphisms (the identity and negation).

But, in any topos, if there is an automorphism of Ω different from the
identity, then the topos is boolean.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.ClassicalLogic
open import UF.Embeddings
open import UF.Equiv hiding (_≅_)
open import UF.Equiv-FunExt
open import UF.FunExt
open import UF.Subsingletons
open import UF.SubtypeClassifier hiding (Ω)
open import UF.SubtypeClassifier-Properties

module Higgs.Rigidity
        {𝓤 : Universe}
        (fe : Fun-Ext)
        (pe : propext 𝓤)
       where

open import Higgs.InvolutionTheorem fe pe

\end{code}

From the existence of certain automorphisms of Ω, we conclude that
excluded middle holds.

\begin{code}

Ω-automorphism-that-maps-⊤-to-⊥-gives-EM
 : (Σ 𝕗 ꞉ Aut Ω , ⌜ 𝕗 ⌝ ⊤ ＝ ⊥)
 → EM 𝓤
Ω-automorphism-that-maps-⊤-to-⊥-gives-EM ((f , f-is-equiv) , e) = II
 where
  f-is-involutive : involutive f
  f-is-involutive = automorphisms-of-Ω-are-involutive f f-is-equiv

  I : (P : 𝓤 ̇ ) → is-prop P → Σ Q ꞉ 𝓤 ̇ , (P ↔ ¬ Q)
  I P P-is-prop = f p holds , g , h
   where
    p : Ω
    p = (P , P-is-prop)

    g : P → ¬ (f p holds)
    g p-holds = equal-⊥-gives-fails (f p)
                 (f p ＝⟨ ap f (holds-gives-equal-⊤ pe fe p p-holds) ⟩
                  f ⊤ ＝⟨ e ⟩
                  ⊥   ∎)

    h : ¬ (f p holds) → P
    h ν = equal-⊤-gives-holds p
           (p       ＝⟨ (f-is-involutive p)⁻¹ ⟩
            f (f p) ＝⟨ ap f (fails-gives-equal-⊥ pe fe (f p) ν) ⟩
            f ⊥     ＝⟨ ap f (e ⁻¹) ⟩
            f (f ⊤) ＝⟨ f-is-involutive ⊤ ⟩
            ⊤       ∎)

  II : EM 𝓤
  II = all-props-negative-gives-EM fe I

Ω-automorphism-swap-≃ : (𝕗 : Aut Ω)
                      → {p q : Ω}
                      → (⌜ 𝕗 ⌝ p ＝ q) ≃ (⌜ 𝕗 ⌝ q ＝ p)
Ω-automorphism-swap-≃ 𝕗 {p} {q} =
 involution-swap-≃ ⌜ 𝕗 ⌝
  (automorphisms-of-Ω-are-involutive ⌜ 𝕗 ⌝ ⌜ 𝕗 ⌝-is-equiv)
  (Ω-is-set fe pe)

\end{code}

A stronger version of the following is proved below.

\begin{code}

Ω-automorphism-apart-from-id-gives-EM
 : (Σ 𝕗 ꞉ Aut Ω , Σ p₀ ꞉ Ω , ⌜ 𝕗 ⌝ p₀ ≠ p₀)
 → EM 𝓤
Ω-automorphism-apart-from-id-gives-EM (𝕗@(f , f-is-equiv) , p₀ , ν) = VIII
 where
  I : f ⊤ ≠ ⊤
  I e = VI
   where
    II : p₀ ≠ ⊤
    II e₀ = ν II'
     where
      II' : f p₀ ＝ p₀
      II' = transport⁻¹ (λ - → f - ＝ -) e₀ e

    III : p₀ ＝ ⊥
    III = different-from-⊤-gives-equal-⊥ fe pe p₀ II

    IV : f ⊥ ≠ ⊥
    IV e₁ = ν IV'
     where
      IV' : f p₀ ＝ p₀
      IV' = transport⁻¹ (λ - → f - ＝ -) III e₁

    V : f ⊥ ≠ ⊤
    V e₂ = ⊥-is-not-⊤
            (⊥       ＝⟨ (⌜ Ω-automorphism-swap-≃ 𝕗 ⌝ e₂)⁻¹ ⟩
             f ⊤     ＝⟨ e ⟩
             ⊤       ∎)

    VI : 𝟘
    VI = no-truth-values-other-than-⊥-or-⊤ fe pe (f ⊥ , IV , V)

  VII : f ⊤ ＝ ⊥
  VII = different-from-⊤-gives-equal-⊥ fe pe (f ⊤) I

  VIII : EM 𝓤
  VIII = Ω-automorphism-that-maps-⊤-to-⊥-gives-EM (𝕗 , VII)

\end{code}

Notice that we can replace "Σ" by "∃" in the above propositions, to
get the same conclusion EM 𝓤, because the type EM 𝓤 is a proposition.

Notice also that the converses of the above propositions hold.

We show that there can't be any automorphism of Ω distinct from the
identity unless excluded middle holds.

The fact eval-at-⊤-is-lc stated and proved below, which is our main
lemma, is attributed to Denis Higgs in the literature [1] [2], without
any explicit citation I could find, with diagrammatic proofs in topos
theory rather than proofs in the internal language of a topos. Our
internal proofs don't necessarily follow the external diagrammatic
proofs.

[1] Peter T. Johnstone. Automorphisms of Ω. Algebra Universalis,
    9 (1979) 1-7.
    https://doi.org/10.1007/BF02488012

[2] Peter Freyd. Choice and well-ordering.  Annals of Pure and Applied
    Logic 35 (1987) 149-166.
    https://doi.org/10.1016/0168-0072(87)90060-1
    https://core.ac.uk/download/pdf/81927529.pdf

\begin{code}

private
 fe' : FunExt
 fe' 𝓥 𝓦 = fe {𝓥} {𝓦}

eval-at-⊤ : Aut Ω → Ω
eval-at-⊤ 𝕗 = ⌜ 𝕗 ⌝ ⊤

eval-at-⊤-is-lc : left-cancellable eval-at-⊤
eval-at-⊤-is-lc {𝕗@(f , _)} {𝕘@(g , _)} e = III
 where
  have-e : f ⊤ ＝ g ⊤
  have-e = e

  I : (p : Ω) → (f p ＝ ⊤) ≃ (g p ＝ ⊤)
  I p = (f p ＝ ⊤) ≃⟨ Ω-automorphism-swap-≃ 𝕗 ⟩
        (f ⊤ ＝ p) ≃⟨ transport-≃ (_＝ p) e ⟩
        (g ⊤ ＝ p) ≃⟨ Ω-automorphism-swap-≃ 𝕘 ⟩
        (g p ＝ ⊤) ■

  II : f ∼ g
  II p = Ω-ext' pe fe (I p)

  III : 𝕗 ＝ 𝕘
  III = to-≃-＝ fe II

eval-at-⊤-is-embedding : is-embedding eval-at-⊤
eval-at-⊤-is-embedding = lc-maps-into-sets-are-embeddings
                          eval-at-⊤ eval-at-⊤-is-lc
                          (Ω-is-set fe pe)

\end{code}

From this we conclude that there can't be any automorphism of Ω
distinct from the identity unless excluded middle holds. I don't think
this has been observed before in the literature, but it may have been
observed in the folklore.

\begin{code}

Ω-automorphism-distinct-from-𝕚𝕕-gives-EM
 : (Σ 𝕗 ꞉ Aut Ω , 𝕗 ≠ 𝕚𝕕)
 → EM 𝓤
Ω-automorphism-distinct-from-𝕚𝕕-gives-EM (𝕗 , ν) = IV
 where
  f : Ω → Ω
  f = ⌜ 𝕗 ⌝

  I : f ⊤ ＝ ⊤ → 𝕗 ＝ 𝕚𝕕
  I = eval-at-⊤-is-lc {𝕗} {𝕚𝕕}

  II : f ⊤ ≠ ⊤
  II = contrapositive I ν

  III : f ⊤ ＝ ⊥
  III = different-from-⊤-gives-equal-⊥ fe pe (f ⊤) II

  IV : EM 𝓤
  IV = Ω-automorphism-that-maps-⊤-to-⊥-gives-EM (𝕗 , III)

\end{code}

It follows that the type Σ f ꞉ Aut Ω , f ≠ id is a proposition,
constructively. In boolean toposes it is a singleton, in non-boolean
toposes it is empty, and in all toposes it is a subsingleton.  This is
because from any hypothetical element (f , ν) of this type we conclude
that excluded middle holds, and hence Ω ≃ 𝟚, and therefore f is
negation. So this is a constructive proof in which we deduce excluded
middle as an intermediate step. And once we conclude that this type is
a proposition, we see that it is equivalent to the type EM 𝓤, which is
also a proposition, as these two propositions imply each other:

(Σ f ꞉ Aut Ω , f ≠ id) ≃ EM 𝓤

and hence they are equal if we further assume propositional
extensionality (which follows from univalence).

TODO. Write down this argument in Agda.
