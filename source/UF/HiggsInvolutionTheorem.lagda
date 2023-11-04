Martin Escardo, 15 August 2014, with additions 23 January 2021,
October-November 2023.

Higgs' Involution Theorem. In any topos, if f : Ω → Ω is a
monomorphism, then it is an involution.

This is attributed to Denis Higgs in the literature.

We adapt and prove the result in univalent mathematics, using
propositional and functional extensionality. (We don't rely on
propositional resizing (or impredicativity).)

There is a proof by diagram chasing with iterated pullbacks, in page
65 of Johnstone's Sketches of an Elephant, volume 1.

The proof given here is based on an exercise in page 160 of Lambek and
Scott's Introduction to Higher-Order Categorical Logic, attributed to
Scedrov. Thanks to Phil Scott for bringing my attention to this proof
during a visit to Birmingham.

Added 23 Jan 2021. From a group structure on Ω we get excluded middle,
as an application of Higgs Involution Theorem. This doesn't seem to be
known in the topos theory community.

Added 24 Oct 2023. More about automorphisms of Ω.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier renaming (Ω to Ω-of-universe)

\end{code}

We work with a universe 𝓤 and assume functional and propositional
extensionality:

\begin{code}

module UF.HiggsInvolutionTheorem
        {𝓤 : Universe}
        (fe : Fun-Ext)
        (pe : propext 𝓤)
       where

\end{code}

We work with Ω of universe 𝓤:

\begin{code}

private
 Ω  = Ω-of-universe 𝓤
 Ω⁺ = Ω-of-universe (𝓤 ⁺)

\end{code}

Recall that a map f is left-cancellable if f p ＝ f q → p ＝ q, and
involutive if f (f p) ＝ p.

\begin{code}

higgs : (f : Ω → Ω) → left-cancellable f → involutive f
higgs f lc = VIII
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

autoembeddings-of-Ω-are-involutive : (f : Ω → Ω) → is-embedding f → involutive f
autoembeddings-of-Ω-are-involutive f e = higgs f (embeddings-are-lc f e)

automorphisms-of-Ω-are-equivs : (f : Ω → Ω) → is-embedding f → is-equiv f
automorphisms-of-Ω-are-equivs f e =
 involutions-are-equivs f (autoembeddings-of-Ω-are-involutive f e)

automorphisms-of-Ω-are-involutive : (f : Ω → Ω) → is-equiv f → involutive f
automorphisms-of-Ω-are-involutive f e = higgs f (equivs-are-lc f e)

\end{code}

Added 23 Jan 2021. From a group structure on Ω we get excluded middle,
as an application of Higgs Theorem. This doesn't seem to be known in
the topos theory community. I've written a blog post about this here:

https://homotopytypetheory.org/2021/01/23/can-the-type-of-truth-values-be-given-the-structure-of-a-group/

Such a group structure is necessarily abelian.

Moreover, any left-cancellable monoid structure (_⊕_ , O) on Ω is an
abelian group structure with p ⊕ p = O for all p : Ω, that is, such
that every element is its own inverse.

To define negation on Ω we need function extensionality, which we are
assuming in this module. We introduce friendlier notation for it:

\begin{code}

⇁_ : Ω → Ω
⇁_ = not fe

⇁⇁_ : Ω → Ω
⇁⇁ p = ⇁(⇁ p)

open import UF.ExcludedMiddle

lc-monoid-structure-on-Ω-gives-EM : (O : Ω)
                                    (_⊕_ : Ω → Ω → Ω)
                                  → left-neutral O _⊕_
                                  → right-neutral O _⊕_
                                  → associative _⊕_
                                  → ((p : Ω) → left-cancellable (p ⊕_))
                                  → EM 𝓤
lc-monoid-structure-on-Ω-gives-EM O _⊕_ left-neutral right-neutral assoc lc = γ
 where
  invol : (p : Ω) → involutive (p ⊕_)
  invol p = higgs (p ⊕_) (lc p)

  own-inv : (p : Ω) → p ⊕ p ＝ O
  own-inv p = p ⊕ p       ＝⟨ (right-neutral (p ⊕ p))⁻¹ ⟩
              (p ⊕ p) ⊕ O ＝⟨ assoc p p O ⟩
              p ⊕ (p ⊕ O) ＝⟨ invol p O ⟩
              O           ∎

  to-＝ : {p q : Ω} → p ⊕ q ＝ O → p ＝ q
  to-＝ {p} {q} e = p           ＝⟨ (right-neutral p)⁻¹ ⟩
                    p ⊕ O       ＝⟨ ap (p ⊕_) (e ⁻¹) ⟩
                    p ⊕ (p ⊕ q) ＝⟨ (assoc p p q)⁻¹ ⟩
                    (p ⊕ p) ⊕ q ＝⟨ ap (_⊕ q) (own-inv p) ⟩
                    O ⊕ q       ＝⟨ left-neutral q ⟩
                    q           ∎

  f : Ω → Ω
  f p = p ⊕ (⊥ ⊕ ⊤)

  f-invol : involutive f
  f-invol p = f (f p)                 ＝⟨ refl ⟩
              (p ⊕ (⊥ ⊕ ⊤)) ⊕ (⊥ ⊕ ⊤) ＝⟨ assoc p (⊥ ⊕ ⊤) (⊥ ⊕ ⊤) ⟩
              p ⊕ ((⊥ ⊕ ⊤) ⊕ (⊥ ⊕ ⊤)) ＝⟨ ap (p ⊕_) (own-inv (⊥ ⊕ ⊤)) ⟩
              p ⊕ O                   ＝⟨ right-neutral p ⟩
              p                       ∎

  α : (p : Ω) → f p ＝ ⊤ → p ＝ ⊥
  α p e = to-＝ (p ⊕ ⊥            ＝⟨ (right-neutral (p ⊕ ⊥))⁻¹ ⟩
                (p ⊕ ⊥) ⊕ O       ＝⟨ ap ((p ⊕ ⊥) ⊕_) ((own-inv ⊤)⁻¹) ⟩
                (p ⊕ ⊥) ⊕ (⊤ ⊕ ⊤) ＝⟨ (assoc (p ⊕ ⊥) ⊤ ⊤)⁻¹ ⟩
                ((p ⊕ ⊥) ⊕ ⊤) ⊕ ⊤ ＝⟨ ap (_⊕ ⊤) (assoc p ⊥ ⊤) ⟩
                (p ⊕ (⊥ ⊕ ⊤)) ⊕ ⊤ ＝⟨ refl ⟩
                f p ⊕ ⊤           ＝⟨ ap (_⊕ ⊤) e ⟩
                ⊤ ⊕ ⊤             ＝⟨ own-inv ⊤ ⟩
                O                 ∎)

  β : (p : Ω) → p ＝ ⊥ → f p ＝ ⊤
  β p e = f p         ＝⟨ refl ⟩
          p ⊕ (⊥ ⊕ ⊤) ＝⟨ (assoc p ⊥ ⊤)⁻¹ ⟩
          (p ⊕ ⊥) ⊕ ⊤ ＝⟨ ap (λ - → (- ⊕ ⊥) ⊕ ⊤) e ⟩
          (⊥ ⊕ ⊥) ⊕ ⊤ ＝⟨ ap (_⊕ ⊤) (own-inv ⊥) ⟩
          O ⊕ ⊤       ＝⟨ left-neutral ⊤ ⟩
          ⊤           ∎

  characterization-of-f : (p : Ω) → f p ＝ ⇁ p
  characterization-of-f p = Ω-ext pe fe a b
   where
    a : f p ＝ ⊤ → (⇁ p) ＝ ⊤
    a e = equal-⊥-gives-not-equal-⊤ fe pe p (α p e)

    b : (⇁ p) ＝ ⊤ → f p ＝ ⊤
    b e = β p (not-equal-⊤-gives-equal-⊥ fe pe p e)

  ν : (p : Ω) → (⇁⇁ p) ＝ p
  ν p = ⇁⇁ p      ＝⟨ ap ⇁_ ((characterization-of-f p)⁻¹) ⟩
        (⇁ (f p)) ＝⟨ (characterization-of-f (f p))⁻¹ ⟩
        f (f p)   ＝⟨ f-invol p ⟩
        p         ∎

  δ : (P : 𝓤 ̇ ) → is-prop P → ¬¬ P → P
  δ P i = Idtofun (ap _holds (ν (P , i)))

  γ : EM 𝓤
  γ = DNE-gives-EM fe δ

\end{code}

Additional facts that are not needed to conclude excluded middle:

\begin{code}

  from-＝ : (p q : Ω) → p ＝ q → p ⊕ q ＝ O
  from-＝ p q e = p ⊕ q ＝⟨ ap (_⊕ q) e ⟩
                  q ⊕ q ＝⟨ own-inv q ⟩
                  O     ∎

  abelian : (p q : Ω) → p ⊕ q ＝ q ⊕ p
  abelian p q = to-＝ ((p ⊕ q) ⊕ (q ⊕ p) ＝⟨ assoc p q (q ⊕ p) ⟩
                      p ⊕ (q ⊕ (q ⊕ p))  ＝⟨ ap (p ⊕_) ((assoc q q p)⁻¹) ⟩
                      p ⊕ ((q ⊕ q) ⊕ p)  ＝⟨ ap (λ - → p ⊕ (- ⊕ p)) (own-inv q) ⟩
                      p ⊕ (O ⊕ p)        ＝⟨ ap (p ⊕_) (left-neutral p) ⟩
                      p ⊕ p              ＝⟨ own-inv p ⟩
                      O                  ∎)

  charac₂-of-f : (p : Ω) → f p ＝ (⊥ ⊕ ⊤) ⊕ p
  charac₂-of-f p = abelian p (⊥ ⊕ ⊤)

  f-invol' : involutive f
  f-invol' p = f (f p)                   ＝⟨ charac₂-of-f (f p) ⟩
               ((⊥ ⊕ ⊤) ⊕ f p)           ＝⟨ ap ((⊥ ⊕ ⊤) ⊕_) (charac₂-of-f p) ⟩
               ((⊥ ⊕ ⊤) ⊕ ((⊥ ⊕ ⊤) ⊕ p)) ＝⟨ higgs ((⊥ ⊕ ⊤) ⊕_) (lc (⊥ ⊕ ⊤)) p ⟩
               p ∎

\end{code}

This shows that any cancellative monoid structure on Ω is
automatically an abelian group structure (which is not very surprising
given that we have already established excluded middle, but justifies
our additive notation).

Added 24th October 2023. More about automorphisms of Ω.

You can discuss this at
https://mathstodon.xyz/deck/@MartinEscardo/111291658836418672

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

  I : (P : 𝓤 ̇ ) → is-prop P → Σ Q ꞉ 𝓤 ̇ , (P ⇔ ¬ Q)
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

open import UF.SubtypeClassifier-Properties

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

Added 26 October 2023.

We show that there can't be any automorphism of Ω distinct from the
identity unless excluded middle holds.

The fact eval-at-⊤-is-lc stated and proved below, which is our main
lemma, is attributed to Denis Higgs in the literature [1], without any
explicit citation I could find, with diagrammatic proofs in topos
theory rather than proofs in the internal language of a topos. Our
internal proofs don't necessarily follow the external diagrammatic
proofs. See also [2].

[1] Peter T. Johnstone. Automorphisms of Ω. Algebra Universalis,
    9 (1979) 1-7.
    https://doi.org/10.1007/BF02488012

[2] Peter Freyd. Choice and well-ordering.  Annals of Pure and Applied
    Logic 35 (1987) 149-166.
    https://doi.org/10.1016/0168-0072(87)90060-1
    https://core.ac.uk/download/pdf/81927529.pdf

\begin{code}

open import UF.Equiv-FunExt

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
distinct from the identity unless excluded middle holds. I don't
think this has been observed before in the literature, but it may have
been observed in the folklore.

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

and hence they are equal if we further assume univalence.

TODO. Write down this argument in Agda.

Added 1st November 2023.

\begin{code}

open import UF.Logic
open Implication fe
open Conjunction
open Universal fe

can-recover-automorphism-from-its-value-at-⊤
 : (𝕗 : Aut Ω)
   (p : Ω)
 → ⌜ 𝕗 ⌝ p ＝ (p ↔ ⌜ 𝕗 ⌝ ⊤)
can-recover-automorphism-from-its-value-at-⊤ 𝕗@(f , _) p =
 Ω-ext' pe fe
  ((f p ＝ ⊤)       ≃⟨ Ω-automorphism-swap-≃ 𝕗 ⟩
   (f ⊤ ＝ p)       ≃⟨ ≃-sym (↔-equiv-to-＝ pe (f ⊤) p) ⟩
   ((f ⊤ ↔ p) ＝ ⊤) ≃⟨ transport-≃ (_＝ ⊤) (↔-sym pe (f ⊤) p) ⟩
   ((p ↔ f ⊤) ＝ ⊤) ■)

\end{code}

Added 2nd November 2023. Definiton of the Higgs object ℍ and proof
that it is equivalent to Aut Ω.

\begin{code}

is-higgs : Ω → 𝓤 ⁺ ̇
is-higgs r = (p : Ω) → ((p ↔ r) ↔ r) ＝ p

being-higgs-is-prop : (r : Ω) → is-prop (is-higgs r)
being-higgs-is-prop r = Π-is-prop fe (λ p → Ω-is-set fe pe)

ℍ : 𝓤 ⁺ ̇
ℍ = Σ r ꞉ Ω , is-higgs r

⟪_⟫ : ℍ → Ω
⟪ r , _ ⟫ = r

⟪_⟫-is-higgs : (h : ℍ) → is-higgs ⟪ h ⟫
⟪ _ , i ⟫-is-higgs = i

to-ℍ-＝ : (r s : Ω) {i : is-higgs r} {j : is-higgs s}
       → r ＝ s
       → (r , i) ＝[ ℍ ] (s , j)
to-ℍ-＝ r s {i} {j} = to-subtype-＝ being-higgs-is-prop

Ω-automorphisms-are-↔-embeddings : (𝕗 : Aut Ω)
                                   (p q : Ω)
                                 → (p ↔ q) ＝ (⌜ 𝕗 ⌝ p ↔ ⌜ 𝕗 ⌝ q)
Ω-automorphisms-are-↔-embeddings 𝕗@(f , f-is-equiv) p q =
 Ω-ext' pe fe
  (((p ↔ q) ＝ ⊤)     ≃⟨ I ⟩
   (p ＝ q)           ≃⟨ II ⟩
   (f p ＝ f q)       ≃⟨ III ⟩
   ((f p ↔ f q) ＝ ⊤) ■)
  where
   I   = ↔-equiv-to-＝ pe p q
   II  = embedding-criterion-converse' f (equivs-are-embeddings' 𝕗) p q
   III = ≃-sym (↔-equiv-to-＝ pe (f p) (f q))

eval-at-⊤-is-higgs : (𝕗 : Aut Ω) → is-higgs (eval-at-⊤ 𝕗)
eval-at-⊤-is-higgs 𝕗@(f , _) p = II
 where
  I = p ↔ ⊤           ＝⟨ I₀ ⟩
      f p ↔ f ⊤       ＝⟨ I₁ ⟩
      (p ↔ f ⊤) ↔ f ⊤ ∎
   where
    I₀ = Ω-automorphisms-are-↔-embeddings 𝕗 p ⊤
    I₁ = ap (_↔ f ⊤) (can-recover-automorphism-from-its-value-at-⊤ 𝕗 p)

  II : ((p ↔ f ⊤) ↔ f ⊤) ＝ p
  II = transport (_＝ p) I (⊤-↔-neutral pe p)

Aut-Ω-to-ℍ : Aut Ω → ℍ
Aut-Ω-to-ℍ 𝕗 = eval-at-⊤ 𝕗 , eval-at-⊤-is-higgs 𝕗

ℍ-to-Aut-Ω : ℍ → Aut Ω
ℍ-to-Aut-Ω (r , i) = g , involutions-are-equivs g g-is-involutive
 where
  g : Ω → Ω
  g p = p ↔ r

  g-is-involutive : involutive g
  g-is-involutive = i

η-ℍ : ℍ-to-Aut-Ω ∘ Aut-Ω-to-ℍ ∼ id
η-ℍ 𝕗@(f , f-is-equiv) = to-≃-＝ fe h
 where
  g : Ω → Ω
  g p = p ↔ f ⊤

  h : g ∼ f
  h p = (can-recover-automorphism-from-its-value-at-⊤ 𝕗 p)⁻¹

ε-ℍ : Aut-Ω-to-ℍ ∘ ℍ-to-Aut-Ω ∼ id
ε-ℍ (r , i) = to-ℍ-＝ (⊤ ↔ r) r (⊤-↔-neutral' pe r)

Aut-Ω-is-equiv-to-ℍ : Aut Ω ≃ ℍ
Aut-Ω-is-equiv-to-ℍ = qinveq Aut-Ω-to-ℍ (ℍ-to-Aut-Ω , η-ℍ , ε-ℍ)

\end{code}

The type Aut Ω is a group under composition, where the neutral element
is the identity automorphism and the inverse of any element is itself.
That is, Aut Ω is a boolean group, or a group order 2. We now show
that the group structure on ℍ induced by the above equivalence is
given by logical equivalence _↔_ with neutral element ⊤.

Notice that our convention is that composition _●_ of equivalences is
in the diagrammatic order, rather than the applicative order. And I
regret that - in particular, there isn't any contravariance in the
next lemma. But in the end it doesn't matter, because both of these
group operations are commutative.

\begin{code}

identity-corresponds-to-⊤
 : eval-at-⊤ 𝕚𝕕 ＝ ⊤
identity-corresponds-to-⊤ = refl

\end{code}

The following amounts to saying that  g (f ⊤) ＝ g ⊤ ↔ f ⊤.

\begin{code}

composition-corresponds-to-logical-equivalence
 : (𝕗 𝕘 : Aut Ω)
 → eval-at-⊤ (𝕗 ● 𝕘) ＝ eval-at-⊤ 𝕘 ↔ eval-at-⊤ 𝕗
composition-corresponds-to-logical-equivalence 𝕗@(f , _) 𝕘@(g , _) = I
 where
  I = g (f ⊤)   ＝⟨ can-recover-automorphism-from-its-value-at-⊤ 𝕘 (f ⊤) ⟩
      f ⊤ ↔ g ⊤ ＝⟨ ↔-sym pe (f ⊤) (g ⊤) ⟩
      g ⊤ ↔ f ⊤ ∎

open import Groups.Type
open import Groups.Symmetric fe

symmetric-group-of-Ω : Group (𝓤 ⁺)
symmetric-group-of-Ω = symmetric-group Ω (Ω-is-set fe pe)

ℍ-group-lemma : Σ s ꞉ Group-structure ℍ
                    , is-hom (ℍ , s) symmetric-group-of-Ω ℍ-to-Aut-Ω
ℍ-group-lemma =
 transport-Group-structure' symmetric-group-of-Ω ℍ (≃-sym Aut-Ω-is-equiv-to-ℍ)

ℍ-group : Group (𝓤 ⁺)
ℍ-group = ℍ , pr₁ ℍ-group-lemma

Johnstone : ℍ-group ≅ symmetric-group-of-Ω
Johnstone = pr₂ (group-copy symmetric-group-of-Ω
                 (ℍ , ≃-sym Aut-Ω-is-equiv-to-ℍ))

\end{code}

TODO. Characterize the unit of ℍ-group as ⊤ and its multiplication as
_↔_. Easy, given what we have already proved.

Alternative characterization of the Higgs property.

\begin{code}

open import UF.PropTrunc

module _ (pt : propositional-truncations-exist) where

 open Disjunction pt

 is-higgs' : Ω → 𝓤 ⁺ ̇
 is-higgs' r = (p : Ω) → (p ∨ (p ⇒ r)) holds

\end{code}

TODO. Write proof that is-higgs r ⇔ is-higgs' r. Easy if we know
enough general logic.
