Martin Escardo, 5th September 2023

This is work in progress. For motivation, please read the comments in [1].

We give sufficient conditions to derive algebraic flabbiness of the
type Σ x ꞉ X , S x from algebraic flabbiness of the type X. (And hence
injectivity from injectivity.)

This should eventually subsume and improve [1], but this work is not
completed yet.

There are currently a couple of problems with this generalization,
including universe levels.

For the moment I am not going to work any further with this (until I
really need it).

For motivation, the reader should check the file

Two big improvements here are that

 1. We don't require the canonical map to be an equivalence - we
    merely require it to have a section. (So it is easier to apply the
    theorems are as there are fewer things to check.)

 2. We don't restrict to a particular flabiness structure, whereas in [1]
    we use the Π-flabbiness structure.

[1] InjectiveTypes.MathematicalStructures.

TODO. Rewrite [1] to use retractions rather than equivalences. This
will be not only more general but also shorter.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import UF.FunExt

module InjectiveTypes.Sigma
        (fe : FunExt)
       where

private

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import InjectiveTypes.Blackboard fe
open import MLTT.Spartan
open import UF.Base
open import UF.Retracts
open import UF.SubtypeClassifier

private
 extension : {X : 𝓦 ̇}
           → aflabby X 𝓤 → (p : Ω 𝓤) → (p holds → X) → X
 extension = aflabby-extension

 extends : {X : 𝓦 ̇} (ϕ : aflabby X 𝓤) (p : Ω 𝓤)
           (f : p holds → X) (h : p holds)
         → extension ϕ p f ＝ f h
 extends  = aflabby-extension-property


module _ {X : 𝓤 ̇ }
         (S : X → 𝓦 ̇ )
         (ϕ : aflabby X 𝓦)
       where

 ρ : (p : Ω 𝓦) (f : p holds → X)
   → S (extension ϕ p f) → ((h : p holds) → S (f h))
 ρ p f s h = transport S (extends ϕ p f h) s

 ρ-has-section : 𝓤 ⊔ (𝓦 ⁺)  ̇
 ρ-has-section = (p : Ω 𝓦)
                 (f : p holds → X)
               → has-section (ρ p f)

 Σ-is-aflabby : ρ-has-section → aflabby (Σ S) 𝓦
 Σ-is-aflabby hs = I
  where
   I : aflabby (Σ S) 𝓦
   I P P-is-prop ψ = (extension ϕ p f , s) , II
    where
     p : Ω 𝓦
     p = (P , P-is-prop)

     have-ϕ : p holds → Σ S
     have-ϕ = ψ

     f : p holds → X
     f = pr₁ ∘ ψ

     g : (h : P) → S (f h)
     g = pr₂ ∘ ψ

     σ : ((h : p holds) → S (f h)) → S (extension ϕ p f)
     σ = pr₁ (hs p f)

     η : ρ p f ∘ σ ∼ id
     η = pr₂ (hs p f)

     s : S (extension ϕ p f)
     s = σ g

     II : (h : p holds) → (extension ϕ p f , s) ＝ ψ h
     II h = extension ϕ p f , s ＝⟨ to-Σ-＝ (extends ϕ p f h , III) ⟩
            f h , g h           ＝⟨ refl ⟩
            ψ h                 ∎
      where
       III = transport S (extends ϕ p f h) s  ＝⟨ refl ⟩
             ρ p f s h                        ＝⟨ refl ⟩
             ρ p f (σ g) h                    ＝⟨ ap (λ - → - h) (η g) ⟩
             g h                              ∎

 Σ-ainjective : ρ-has-section → ainjective-type (Σ S) 𝓦 𝓦
 Σ-ainjective = aflabby-types-are-ainjective (Σ S)
                 ∘ Σ-is-aflabby

 module _ (T      : {x y : X} → x ＝ y → S x → S y)
          (T-refl : {x : X} → T (𝓻𝓮𝒻𝓵 x) ∼ id)
         where

  private
    T-is-transport : {x y : X} (e : x ＝ y)
                   → T e ∼ transport S e
    T-is-transport refl = T-refl

  ρ' : (p : Ω 𝓦) (f : p holds → X)
     → S (extension ϕ p f) → (h : p holds) → S (f h)
  ρ' p f s h = T (extends ϕ p f h) s

  ρs-agreement : (p : Ω 𝓦)
                             (f : p holds → X)
                           → ρ p f ∼ ρ' p f
  ρs-agreement p f s =
   ρ p f s                     ＝⟨ refl ⟩
   (λ h → transport S (extends ϕ p f h) s) ＝⟨ I ⟩
   (λ h → T (extends ϕ p f h) s)           ＝⟨ refl ⟩
   ρ' p f s                    ∎
   where
    I = dfunext fe' (λ h → (T-is-transport (extends ϕ p f h) s)⁻¹)

  ρ'-has-section : 𝓤 ⊔ (𝓦 ⁺) ̇
  ρ'-has-section = (p : Ω 𝓦)
                   (f : p holds → X)
                 → has-section (ρ' p f)

  canonical-section-criterion : ρ'-has-section
                              → ρ-has-section
  canonical-section-criterion ρ'-has-section p f =
   has-section-closed-under-∼
    (ρ' p f)
    (ρ p f)
    (ρ'-has-section p f)
    (ρs-agreement p f)

  canonical-section-criterion-converse : ρ-has-section
                                       → ρ'-has-section
  canonical-section-criterion-converse ρ-has-section p f =
   has-section-closed-under-∼
    (ρ p f)
    (ρ' p f)
    (ρ-has-section p f)
    (∼-sym (ρs-agreement p f))

\end{code}

Discussion. It is easy to prove (TODO) that

ΣΣ-is-aflabby : {X : 𝓤 ̇ }
                (A : X → ? ̇ ) (B : (x : X) → A x → ? ̇ )
              → (ϕ : aflabby X ?)
              → (hs : ρ-has-section A ϕ)
              → ρ-has-section (λ ((x , a) : Σ A) → B x a) (Σ-is-aflabby A ϕ hs) -- (*)
              → aflabby (Σ x ꞉ X , Σ a ꞉ A x , B x a) ?

where the question marks are universes that Agda should be able to
resolve, or at least give contraints to.

However, the hypothesis (*) will not be very useful in practice,
because it is very complicated to state and check. So a good thing to
do would be to formulate and prove an equivalent condition that would
be easier to work with.
