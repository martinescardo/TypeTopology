Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module MGS-Equivalence-Constructions where

open import MGS-More-FunExt-Consequences public

id-≃-left : dfunext 𝓥 (𝓤 ⊔ 𝓥)
          → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
          → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (α : X ≃ Y)
          → id-≃ X ● α ≡ α

id-≃-left fe fe' α = to-subtype-≡ (being-equiv-is-subsingleton fe fe') (refl _)

≃-sym-left-inverse : dfunext 𝓥 𝓥
                   → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (α : X ≃ Y)
                   → ≃-sym α ● α ≡ id-≃ Y

≃-sym-left-inverse fe (f , e) = to-subtype-≡ (being-equiv-is-subsingleton fe fe) p
 where
  p : f ∘ inverse f e ≡ id
  p = fe (inverses-are-sections f e)

≃-sym-right-inverse : dfunext 𝓤 𝓤
                    → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (α : X ≃ Y)
                    → α ● ≃-sym α ≡ id-≃ X

≃-sym-right-inverse fe (f , e) = to-subtype-≡ (being-equiv-is-subsingleton fe fe) p
 where
  p : inverse f e ∘ f ≡ id
  p = fe (inverses-are-retractions f e)

≃-Sym : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
      → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
      → (X ≃ Y) ≃ (Y ≃ X)

≃-Sym fe₀ fe₁ fe₂ = ≃-sym , ≃-sym-is-equiv fe₀ fe₁ fe₂

≃-cong' : dfunext 𝓦 (𝓥 ⊔ 𝓦) → dfunext (𝓥 ⊔ 𝓦) (𝓥 ⊔ 𝓦 )
       → dfunext 𝓥 𝓥 → dfunext 𝓦 (𝓤 ⊔ 𝓦)
       → dfunext (𝓤 ⊔ 𝓦) (𝓤 ⊔ 𝓦 ) → dfunext 𝓤 𝓤
       → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (Z : 𝓦 ̇ )
       → X ≃ Y → (Y ≃ Z) ≃ (X ≃ Z)

≃-cong' fe₀ fe₁ fe₂ fe₃ fe₄ fe₅ Z α = invertibility-gives-≃ (α ●_)
                                      ((≃-sym α ●_) , p , q)
 where
  p = λ β → ≃-sym α ● (α ● β) ≡⟨ ●-assoc fe₀ fe₁ (≃-sym α) α β ⟩
            (≃-sym α ● α) ● β ≡⟨ ap (_● β) (≃-sym-left-inverse fe₂ α) ⟩
            id-≃ _ ● β        ≡⟨ id-≃-left fe₀ fe₁ _ ⟩
            β                 ∎

  q = λ γ → α ● (≃-sym α ● γ) ≡⟨ ●-assoc fe₃ fe₄ α (≃-sym α) γ ⟩
            (α ● ≃-sym α) ● γ ≡⟨ ap (_● γ) (≃-sym-right-inverse fe₅ α) ⟩
            id-≃ _ ● γ        ≡⟨ id-≃-left fe₃ fe₄ _ ⟩
            γ                 ∎

Eq-Eq-cong' : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥) → dfunext 𝓤 𝓤
            → dfunext 𝓥 (𝓥 ⊔ 𝓦) → dfunext (𝓥 ⊔ 𝓦) (𝓥 ⊔ 𝓦) → dfunext 𝓦 𝓦
            → dfunext 𝓦 (𝓥 ⊔ 𝓦) → dfunext 𝓥 𝓥 → dfunext 𝓦 (𝓦 ⊔ 𝓣)
            → dfunext (𝓦 ⊔ 𝓣) (𝓦 ⊔ 𝓣) → dfunext 𝓣 𝓣 → dfunext 𝓣 (𝓦 ⊔ 𝓣)
            → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } {B : 𝓣 ̇ }
            → X ≃ A → Y ≃ B → (X ≃ Y) ≃ (A ≃ B)

Eq-Eq-cong' fe₀ fe₁ fe₂ fe₃ fe₄ fe₅ fe₆ fe₇ fe₈ fe₉ fe₁₀ fe₁₁ {X} {Y} {A} {B} α β =

  X ≃ Y   ≃⟨ ≃-cong' fe₀ fe₁ fe₂ fe₃ fe₄ fe₅ Y (≃-sym α) ⟩
  A ≃ Y   ≃⟨ ≃-Sym fe₃ fe₆ fe₄ ⟩
  Y ≃ A   ≃⟨ ≃-cong' fe₆ fe₄ fe₇ fe₈ fe₉ fe₁₀ A (≃-sym β) ⟩
  B ≃ A   ≃⟨ ≃-Sym fe₈ fe₁₁ fe₉ ⟩
  A ≃ B   ■

Eq-Eq-cong : global-dfunext
           → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } {B : 𝓣 ̇ }
           → X ≃ A → Y ≃ B → (X ≃ Y) ≃ (A ≃ B)

Eq-Eq-cong fe = Eq-Eq-cong' fe fe fe fe fe fe fe fe fe fe fe fe

\end{code}
