Martin Escardo, 5th September 2023

This is work in progress. For motivation, please read the comments in [1].

We give sufficient conditions to derive algebraic flabbiness of the
type Σ x ꞉ X , S x from algebraic flabbiness of the type X. (And hence
injectivity from injectivity.)

This should eventually subsume and improve [1], but this work is not
completed yet.

For motivation, the reader should check [1].

Two big improvements here are that

 1. We don't require the canonical map to be an equivalence - we
    merely require it to have a section. (So it is easier to apply the
    theorems are as there are fewer things to check.)

 2. We don't restrict to a particular flabiness structure, whereas in [1]
    we use the Π-flabbiness structure.

[1] InjectiveTypes.MathematicalStructures.

TODO. Rewrite [1] to use retractions rather than equivalences. This
will be not only more general but also shorter. Or just apply the
result here.

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
         (S : X → 𝓥 ̇ )
         (ϕ : aflabby X 𝓦)
       where

 ρ : (p : Ω 𝓦) (f : p holds → X)
   → S (extension ϕ p f) → ((h : p holds) → S (f h))
 ρ p f s h = transport S (extends ϕ p f h) s

 Σ-flabiness-sufficient-condition : 𝓤 ⊔ 𝓥 ⊔ (𝓦 ⁺)  ̇
 Σ-flabiness-sufficient-condition = (p : Ω 𝓦)
                                    (f : p holds → X)
                                  → has-section (ρ p f)

 Σ-is-aflabby : Σ-flabiness-sufficient-condition → aflabby (Σ S) 𝓦
 Σ-is-aflabby ρ-has-section = I
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
     σ = section-of (ρ p f) (ρ-has-section p f)

     η : ρ p f ∘ σ ∼ id
     η = section-equation (ρ p f) (ρ-has-section p f)

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

 Σ-ainjective : Σ-flabiness-sufficient-condition → ainjective-type (Σ S) 𝓦 𝓦
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

  Σ-flabiness-sufficient-condition' : 𝓤 ⊔ 𝓥 ⊔ (𝓦 ⁺) ̇
  Σ-flabiness-sufficient-condition' = (p : Ω 𝓦)
                                      (f : p holds → X)
                                    → has-section (ρ' p f)

  canonical-section-criterion : Σ-flabiness-sufficient-condition'
                              → Σ-flabiness-sufficient-condition
  canonical-section-criterion ρ'-has-section p f =
   has-section-closed-under-∼
    (ρ' p f)
    (ρ p f)
    (ρ'-has-section p f)
    (ρs-agreement p f)

  canonical-section-criterion-converse : Σ-flabiness-sufficient-condition
                                       → Σ-flabiness-sufficient-condition'
  canonical-section-criterion-converse ρ-has-section p f =
   has-section-closed-under-∼
    (ρ p f)
    (ρ' p f)
    (ρ-has-section p f)
    (∼-sym (ρs-agreement p f))

Σ-flabiness-sufficient-condition-× :
      {𝓤 𝓥₁ 𝓥₂ 𝓦 : Universe}
      {X : 𝓤 ̇ }
      (ϕ : aflabby X 𝓦)
      {S₁ : X → 𝓥₁ ̇ } {S₂ : X → 𝓥₂ ̇ }
    → Σ-flabiness-sufficient-condition S₁ ϕ
    → Σ-flabiness-sufficient-condition S₂ ϕ
    → Σ-flabiness-sufficient-condition (λ x → S₁ x × S₂ x) ϕ

Σ-flabiness-sufficient-condition-× {𝓤} {𝓥₁} {𝓥₂} {𝓦} {X} ϕ {S₁} {S₂}
                ρ₁-has-section ρ₂-has-section = γ
 where
  S : X → 𝓥₁ ⊔ 𝓥₂ ̇
  S x = S₁ x × S₂ x

  module _ (p : Ω 𝓦)
           (f : p holds → X)
         where

   σ₁ : ((h : p holds) → S₁ (f h)) → S₁ (extension ϕ p f)
   σ₁ = section-of (ρ S₁ ϕ p f) (ρ₁-has-section p f)

   σ₂ : ((h : p holds) → S₂ (f h)) → S₂ (extension ϕ p f)
   σ₂ = section-of (ρ S₂ ϕ p f) (ρ₂-has-section p f)

   σ : ((h : p holds) → S (f h)) → S (extension ϕ p f)
   σ α = σ₁ (λ h → pr₁ (α h)) , σ₂ (λ h → pr₂ (α h))

   ρσ : ρ S ϕ p f ∘ σ ∼ id
   ρσ α = dfunext fe' I
    where
     α₁ = λ h → pr₁ (α h)
     α₂ = λ h → pr₂ (α h)

     I : ρ S ϕ p f (σ α) ∼ α
     I h =
      ρ S ϕ p f (σ α) h                                       ＝⟨ refl ⟩
      transport S (e h) (σ₁ α₁ , σ₂ α₂)                       ＝⟨ II ⟩
      transport S₁ (e h) (σ₁ α₁) , transport S₂ (e h) (σ₂ α₂) ＝⟨ refl ⟩
      ρ S₁ ϕ p f (σ₁ α₁) h , ρ S₂ ϕ p f (σ₂ α₂) h             ＝⟨ III ⟩
      α₁ h , α₂ h                                             ＝⟨ refl ⟩
      α h                                                     ∎
       where
        e : (h : p holds) → extension ϕ p f ＝ f h
        e = extends ϕ p f

        II  = transport-× S₁ S₂ (e h)
        III = ap₂ _,_
                 (ap (λ - → - h)
                     (section-equation (ρ S₁ ϕ p f) (ρ₁-has-section p f) α₁))
                 (ap (λ - → - h)
                     (section-equation (ρ S₂ ϕ p f) (ρ₂-has-section p f) α₂))

   γ : has-section (ρ S ϕ p f)
   γ = (σ , ρσ)

open import UF.Subsingletons

Σ-flabiness-sufficient-condition-with-axioms
 : {𝓤 𝓥 𝓦 𝓣 : Universe}
   {X : 𝓤 ̇ }
   (ϕ : aflabby X 𝓦)
   (S : X → 𝓣 ̇ )
   (ρ-has-section : Σ-flabiness-sufficient-condition S ϕ)
   (axioms : (x : X ) → S x → 𝓦 ̇ )
   (axioms-are-prop-valued : (x : X) (s : S x) → is-prop (axioms x s))
   (axioms-closed-under-extension
     : (p : Ω 𝓦 )
       (f : p holds → X )
     → (α : (h : p holds) → S (f h))
     → ((h : p holds) → axioms (f h) (α h))
     → axioms (extension ϕ p f)
              (section-of (ρ S ϕ p f) (ρ-has-section p f) α))
 → Σ-flabiness-sufficient-condition (λ X → Σ s ꞉ S X , axioms X s) ϕ
Σ-flabiness-sufficient-condition-with-axioms
 {𝓤} {𝓥} {𝓦} {𝓣} {X}
 ϕ
 S
 ρ-has-section
 axioms
 axioms-are-prop-valued
 axioms-closed-under-extension = ρₐ-has-section
  where
   Sₐ : X → 𝓦 ⊔ 𝓣 ̇
   Sₐ x = Σ s ꞉ S x , axioms x s

   module _ (p : Ω 𝓦)
            (f : p holds → X)
          where

    σ : ((h : p holds) → S (f h)) → S (extension ϕ p f)
    σ = section-of (ρ S ϕ p f) (ρ-has-section p f)

    ρₐ : Sₐ (extension ϕ p f) → ((h : p holds) → Sₐ (f h))
    ρₐ = ρ Sₐ ϕ p f

    σₐ : ((h : p holds) → Sₐ (f h)) → Sₐ (extension ϕ p f)
    σₐ α = σ (λ h → pr₁ (α h)) ,
             axioms-closed-under-extension p f
             (λ h → pr₁ (α h))
             (λ h → pr₂ (α h))

    ρσₐ : ρₐ ∘ σₐ ∼ id
    ρσₐ α = dfunext fe' I
     where
      α₁ = λ h → pr₁ (α h)
      α₂ = λ h → pr₂ (α h)

      I : ρₐ (σₐ α) ∼ α
      I h =
       ρₐ (σₐ α) h                    ＝⟨ refl ⟩
       ρₐ (σ α₁ , _) h                ＝⟨ refl ⟩
       transport Sₐ (e h) (σ α₁ , _)  ＝⟨ II ⟩
       (transport S (e h) (σ α₁) , _) ＝⟨ refl ⟩
       (ρ S ϕ p f (σ α₁) h , _)       ＝⟨ III ⟩
       (α₁ h , α₂ h)                  ＝⟨ refl ⟩
       α h                            ∎
        where
         e : (h : p holds) → extension ϕ p f ＝ f h
         e = extends ϕ p f

         II  = transport-Σ S axioms (f h) (e h) (σ α₁)
         III = to-subtype-＝
                (axioms-are-prop-valued (f h))
                (ap (λ - → - h)
                    (section-equation (ρ S ϕ p f) (ρ-has-section p f) α₁))

    ρₐ-has-section : has-section ρₐ
    ρₐ-has-section = σₐ , ρσₐ

\end{code}

Discussion. It is easy to prove (TODO) that

 ΣΣ-is-aflabby
  : {X : 𝓤 ̇ }
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
be easier to work with. Or even a weaker condition that is good enough
in practice.
