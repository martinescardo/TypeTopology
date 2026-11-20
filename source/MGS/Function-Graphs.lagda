Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MGS.Function-Graphs where

open import MGS.Yoneda public

module function-graphs
        (ua : Univalence)
        {𝓤 𝓥 : Universe}
        (X : 𝓤 ̇ )
        (A : X → 𝓥 ̇ )
       where

 hfe : global-hfunext
 hfe = univalence-gives-global-hfunext ua

 fe : global-dfunext
 fe = univalence-gives-global-dfunext ua

 Function : 𝓤 ⊔ 𝓥 ̇
 Function = (x : X) → A x

 Relation : 𝓤 ⊔ (𝓥 ⁺) ̇
 Relation = (x : X) → A x → 𝓥 ̇

 is-functional : Relation → 𝓤 ⊔ 𝓥 ̇
 is-functional R = (x : X) → ∃! a ꞉ A x , R x a

 being-functional-is-subsingleton : (R : Relation)
                                  → is-subsingleton (is-functional R)

 being-functional-is-subsingleton R = Π-is-subsingleton fe
                                       (λ x → ∃!-is-subsingleton (R x) fe)

 Functional-Relation : 𝓤 ⊔ (𝓥 ⁺) ̇
 Functional-Relation = Σ R ꞉ Relation , is-functional R

 ρ : Function → Relation
 ρ f = λ x a → f x ＝ a

 ρ-is-embedding : is-embedding ρ
 ρ-is-embedding = NatΠ-is-embedding hfe hfe
                   (λ x → 𝑌 (A x))
                   (λ x → 𝓨-is-embedding ua (A x))
  where

   τ : (x : X) → A x → (A x → 𝓥 ̇ )
   τ x a b = a ＝ b

   remark₀ : τ ＝ λ x → 𝑌 (A x)
   remark₀ = refl _

   remark₁ : ρ ＝ NatΠ τ
   remark₁ = refl _

 ρ-is-functional : (f : Function) → is-functional (ρ f)
 ρ-is-functional f = σ
  where
   σ : (x : X) → ∃! a ꞉ A x , f x ＝ a
   σ x = singleton-types'-are-singletons (A x) (f x)

 Γ : Function → Functional-Relation
 Γ f = ρ f , ρ-is-functional f

 Φ : Functional-Relation → Function
 Φ (R , σ) = λ x → pr₁ (center (Σ a ꞉ A x , R x a) (σ x))

 Γ-is-equiv : is-equiv Γ
 Γ-is-equiv = invertibles-are-equivs Γ (Φ , η , ε)
  where
   η : Φ ∘ Γ ∼ id
   η = refl

   ε : Γ ∘ Φ ∼ id
   ε (R , σ) = a
    where
     f : Function
     f = Φ (R , σ)

     e : (x : X) → R x (f x)
     e x = pr₂ (center (Σ a ꞉ A x , R x a) (σ x))

     τ : (x : X) → Nat (𝓨 (f x)) (R x)
     τ x = 𝓝 (R x) (f x) (e x)

     τ-is-fiberwise-equiv : (x : X) → is-fiberwise-equiv (τ x)
     τ-is-fiberwise-equiv x = universal-fiberwise-equiv (R x) (σ x) (f x) (τ x)

     d : (x : X) (a : A x) → (f x ＝ a) ≃ R x a
     d x a = τ x a , τ-is-fiberwise-equiv x a

     c : (x : X) (a : A x) → (f x ＝ a) ＝ R x a
     c x a = Eq→Id (ua 𝓥) _ _ (d x a)

     b : ρ f ＝ R
     b = fe (λ x → fe (c x))

     a : (ρ f , ρ-is-functional f) ＝ (R , σ)
     a = to-subtype-＝ being-functional-is-subsingleton b

 functions-amount-to-functional-relations : Function ≃ Functional-Relation
 functions-amount-to-functional-relations = Γ , Γ-is-equiv

\end{code}
