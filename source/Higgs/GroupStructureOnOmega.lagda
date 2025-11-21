Martin Escardo, 23 January 2021.

From a group structure on Ω we get excluded middle, as an application
of Higgs Involution Theorem. This doesn't seem to be known in the
topos theory community. I've written a blog post about this:

https://homotopytypetheory.org/2021/01/23/can-the-type-of-truth-values-be-given-the-structure-of-a-group/

Such a group structure is necessarily abelian.

Moreover, any left-cancellable monoid structure (_⊕_ , O) on Ω is an
abelian group structure with p ⊕ p = O for all p : Ω, that is, such
that every element is its own inverse.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.ClassicalLogic
open import UF.FunExt
open import UF.Logic
open import UF.Subsingletons
open import UF.SubtypeClassifier hiding (Ω)

module Higgs.GroupStructureOnOmega
        {𝓤 : Universe}
        (fe : Fun-Ext)
        (pe : propext 𝓤)
       where

open import Higgs.InvolutionTheorem fe pe

open Negation {𝓤} fe

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
  invol p = higgs-involution-theorem (p ⊕_) (lc p)

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
  f-invol p = f (f p)                 ＝⟨refl⟩
              (p ⊕ (⊥ ⊕ ⊤)) ⊕ (⊥ ⊕ ⊤) ＝⟨ assoc p (⊥ ⊕ ⊤) (⊥ ⊕ ⊤) ⟩
              p ⊕ ((⊥ ⊕ ⊤) ⊕ (⊥ ⊕ ⊤)) ＝⟨ ap (p ⊕_) (own-inv (⊥ ⊕ ⊤)) ⟩
              p ⊕ O                   ＝⟨ right-neutral p ⟩
              p                       ∎

  α : (p : Ω) → f p ＝ ⊤ → p ＝ ⊥
  α p e = to-＝ (p ⊕ ⊥            ＝⟨ (right-neutral (p ⊕ ⊥))⁻¹ ⟩
                (p ⊕ ⊥) ⊕ O       ＝⟨ ap ((p ⊕ ⊥) ⊕_) ((own-inv ⊤)⁻¹) ⟩
                (p ⊕ ⊥) ⊕ (⊤ ⊕ ⊤) ＝⟨ (assoc (p ⊕ ⊥) ⊤ ⊤)⁻¹ ⟩
                ((p ⊕ ⊥) ⊕ ⊤) ⊕ ⊤ ＝⟨ ap (_⊕ ⊤) (assoc p ⊥ ⊤) ⟩
                (p ⊕ (⊥ ⊕ ⊤)) ⊕ ⊤ ＝⟨refl⟩
                f p ⊕ ⊤           ＝⟨ ap (_⊕ ⊤) e ⟩
                ⊤ ⊕ ⊤             ＝⟨ own-inv ⊤ ⟩
                O                 ∎)

  β : (p : Ω) → p ＝ ⊥ → f p ＝ ⊤
  β p e = f p         ＝⟨refl⟩
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
  f-invol' p = f (f p)                   ＝⟨ I ⟩
               ((⊥ ⊕ ⊤) ⊕ f p)           ＝⟨ II ⟩
               ((⊥ ⊕ ⊤) ⊕ ((⊥ ⊕ ⊤) ⊕ p)) ＝⟨ III ⟩
               p                         ∎
              where
               I   = charac₂-of-f (f p)
               II  = ap ((⊥ ⊕ ⊤) ⊕_) (charac₂-of-f p)
               III = higgs-involution-theorem ((⊥ ⊕ ⊤) ⊕_) (lc (⊥ ⊕ ⊤)) p

\end{code}

This shows that any cancellative monoid structure on Ω is
automatically an abelian group structure, which is not very surprising
given that we have already established excluded middle, but justifies
our additive notation.
