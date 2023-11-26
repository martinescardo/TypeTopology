Martin Escardo, 23rd Feb 2023

Modified from SIP. We assume pre-univalence, instead of univalence,
after a suggestion by Peter Lumsdaine. This means that the canonical
map from the identity type to the equivalence type is an embedding,
rather than an equivalence.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.PreSIP where

open import MLTT.Spartan
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.PreUnivalence
open import UF.Subsingletons


module presip where

 ⟨_⟩ : {S : 𝓤 ̇ → 𝓥 ̇ } → Σ S → 𝓤 ̇
 ⟨ X , s ⟩ = X

 structure : {S : 𝓤 ̇ → 𝓥 ̇ } (A : Σ S) → S ⟨ A ⟩
 structure (X , s) = s

 canonical-map : {S : 𝓤 ̇ → 𝓥 ̇ }
                 (ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦 ̇ )
                 (ρ : (A : Σ S) → ι A A (≃-refl ⟨ A ⟩))
                 {X : 𝓤 ̇ }
                 (s t : S X)
               → s ＝ t → ι (X , s) (X , t) (≃-refl X)
 canonical-map ι ρ {X} s s (refl {s}) = ρ (X , s)

 SNS : (𝓤 ̇ → 𝓥 ̇ ) → (𝓦 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⊔ (𝓦 ⁺) ̇
 SNS {𝓤} {𝓥} S 𝓦 = Σ ι ꞉ ((A B : Σ S) → (⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦 ̇ ))
                 , Σ ρ ꞉ ((A : Σ S) → ι A A (≃-refl ⟨ A ⟩))
                 , ({X : 𝓤 ̇ } (s t : S X) → is-embedding (canonical-map ι ρ s t))

 homomorphic : {S : 𝓤 ̇ → 𝓥 ̇ } → SNS S 𝓦
             → (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦 ̇
 homomorphic (ι , ρ , θ) = ι

 _≃[_]_ : {S : 𝓤 ̇ → 𝓥 ̇ } → Σ S → SNS S 𝓦 → Σ S → 𝓤 ⊔ 𝓦 ̇
 A ≃[ σ ] B = Σ f ꞉ (⟨ A ⟩ → ⟨ B ⟩)
            , Σ i ꞉ is-equiv f
            , homomorphic σ A B (f , i)

 Id→homEq : {S : 𝓤 ̇ → 𝓥 ̇ } (σ : SNS S 𝓦)
          → (A B : Σ S) → (A ＝ B) → (A ≃[ σ ] B)
 Id→homEq (_ , ρ , _) A A (refl {A}) = id , id-is-equiv ⟨ A ⟩ , ρ A

 homomorphism-lemma : {S : 𝓤 ̇ → 𝓥 ̇ } (σ : SNS S 𝓦)
                      (A B : Σ S) (p : ⟨ A ⟩ ＝ ⟨ B ⟩)
                    →
                      (transport S p (structure A) ＝ structure B)
                    ↪  homomorphic σ A B (idtoeq ⟨ A ⟩ ⟨ B ⟩ p)
 homomorphism-lemma (ι , ρ , θ) (X , s) (X , t) (refl {X}) = γ
  where
   γ : (s ＝ t) ↪ ι (X , s) (X , t) (≃-refl X)
   γ = (canonical-map ι ρ s t ,
        θ s t)

 ＝-embedding : is-preunivalent 𝓤
              → {S : 𝓤 ̇ → 𝓥 ̇ } (σ : SNS S 𝓦)
                (A B : Σ S)
              → (A ＝ B) ↪ (A ≃[ σ ] B)
 ＝-embedding pua {S} σ A B =
    (A ＝ B)                                                            ↪⟨ i ⟩
    (Σ p ꞉ ⟨ A ⟩ ＝ ⟨ B ⟩ , transport S p (structure A) ＝ structure B) ↪⟨ ii ⟩
    (Σ p ꞉ ⟨ A ⟩ ＝ ⟨ B ⟩ , ι A B (idtoeq ⟨ A ⟩ ⟨ B ⟩ p))               ↪⟨ iii ⟩
    (Σ e ꞉ ⟨ A ⟩ ≃ ⟨ B ⟩ , ι A B e)                                     ↪⟨ iv ⟩
    (A ≃[ σ ] B)                                                        □
  where
   open import UF.PairFun
   ι   = homomorphic σ
   i   = ≃-gives-↪ Σ-＝-≃
   ii  = NatΣ-embedding (homomorphism-lemma σ A B)
   iii = Σ-change-of-variable-embedding
          (ι A B) (idtoeq ⟨ A ⟩ ⟨ B ⟩) (pua ⟨ A ⟩ ⟨ B ⟩)
   iv  = ≃-gives-↪ Σ-assoc

module presip-with-axioms where

 open presip

 [_] : {S : 𝓤 ̇ → 𝓥 ̇ } {axioms : (X : 𝓤 ̇ ) → S X → 𝓦 ̇ }
     → (Σ X ꞉ 𝓤 ̇ , Σ s ꞉ S X , axioms X s) → Σ S
 [ X , s , _ ] = (X , s)

 ⟪_⟫ : {S : 𝓤 ̇ → 𝓥 ̇ } {axioms : (X : 𝓤 ̇ ) → S X → 𝓦 ̇ }
     → (Σ X ꞉ 𝓤 ̇ , Σ s ꞉ S X , axioms X s) → 𝓤 ̇
 ⟪ X , _ , _ ⟫ = X

 add-axioms : {S : 𝓤 ̇ → 𝓥 ̇ }
              (axioms : (X : 𝓤 ̇ ) → S X → 𝓦 ̇ )
            → ((X : 𝓤 ̇ ) (s : S X) → is-prop (axioms X s))
            → SNS S 𝓣
            → SNS (λ X → Σ s ꞉ S X , axioms X s) 𝓣
 add-axioms {𝓤} {𝓥} {𝓦} {𝓣} {S} axioms i (ι , ρ , θ) = ι' , ρ' , θ'
  where
   S' : 𝓤 ̇ → 𝓥 ⊔ 𝓦  ̇
   S' X = Σ s ꞉ S X , axioms X s

   ι' : (A B : Σ S') → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓣 ̇
   ι' A B = ι [ A ] [ B ]

   ρ' : (A : Σ S') → ι' A A (≃-refl ⟨ A ⟩)
   ρ' A = ρ [ A ]

   θ' : {X : 𝓤 ̇ } (s' t' : S' X) → is-embedding (canonical-map ι' ρ' s' t')
   θ' {X} (s , a) (t , b) = γ
    where
     π : S' X → S X
     π (s , _) = s

     j : is-embedding π
     j = pr₁-is-embedding (i X)

     k : {s' t' : S' X} → is-embedding (ap π {s'} {t'})
     k {s'} {t'} = equivs-are-embeddings (ap π)
                    (embedding-gives-embedding' π j s' t')

     l : canonical-map ι' ρ' (s , a) (t , b)
       ∼ canonical-map ι ρ s t ∘ ap π {s , a} {t , b}

     l (refl {s , a}) = 𝓻𝓮𝒻𝓵 (ρ (X , s))

     e : is-embedding (canonical-map ι ρ s t ∘ ap π {s , a} {t , b})
     e = ∘-is-embedding k (θ s t)

     γ : is-embedding (canonical-map ι' ρ' (s , a) (t , b))
     γ = embedding-closed-under-∼ _ _ e l

 ＝-embedding-with-axioms : is-preunivalent 𝓤
                          → {S : 𝓤 ̇ → 𝓥 ̇ }
                            (σ : SNS S 𝓣)
                            (axioms : (X : 𝓤 ̇ ) → S X → 𝓦 ̇ )
                          → ((X : 𝓤 ̇ ) (s : S X) → is-prop (axioms X s))
                          → (A B : Σ X ꞉ 𝓤 ̇ , Σ s ꞉ S X , axioms X s)
                          → (A ＝ B) ↪ ([ A ] ≃[ σ ] [ B ])
 ＝-embedding-with-axioms ua σ axioms i = ＝-embedding ua (add-axioms axioms i σ)

{- TODO. Not needed yet. Only the technical lemma needs to be proved to conclude.

module sip-join where

 technical-lemma :

     {X : 𝓤 ̇ } {A : X → X → 𝓥 ̇ }
     {Y : 𝓦 ̇ } {B : Y → Y → 𝓣 ̇ }
     (f : (x₀ x₁ : X) → x₀ ＝ x₁ → A x₀ x₁)
     (g : (y₀ y₁ : Y) → y₀ ＝ y₁ → B y₀ y₁)
   → ((x₀ x₁ : X) → is-embedding (f x₀ x₁))
   → ((y₀ y₁ : Y) → is-embedding (g y₀ y₁))

   → ((x₀ , y₀) (x₁ , y₁) : X × Y)
   → is-embedding (λ (p : (x₀ , y₀) ＝ (x₁ , y₁))
                        → f x₀ x₁ (ap pr₁ p) ,
                          g y₀ y₁ (ap pr₂ p))

 technical-lemma {𝓤} {𝓥} {𝓦} {𝓣} {X} {A} {Y} {B} f g i j (x₀ , y₀)  (x₁ , y₁) = {!!}

 variable
  𝓥₀ 𝓥₁ 𝓦₀ 𝓦₁ : Universe

 open presip

 ⟪_⟫ : {S₀ : 𝓤 ̇ → 𝓥₀ ̇ } {S₁ : 𝓤 ̇ → 𝓥₁ ̇ }
     → (Σ X ꞉ 𝓤 ̇ , S₀ X × S₁ X) → 𝓤 ̇
 ⟪ X , s₀ , s₁ ⟫ = X

 [_]₀ : {S₀ : 𝓤 ̇ → 𝓥₀ ̇ } {S₁ : 𝓤 ̇ → 𝓥₁ ̇ }
      → (Σ X ꞉ 𝓤 ̇ , S₀ X × S₁ X) → Σ S₀
 [ X , s₀ , s₁ ]₀ = (X , s₀)

 [_]₁ : {S₀ : 𝓤 ̇ → 𝓥₀ ̇ } {S₁ : 𝓤 ̇ → 𝓥₁ ̇ }
      → (Σ X ꞉ 𝓤 ̇ , S₀ X × S₁ X) → Σ S₁
 [ X , s₀ , s₁ ]₁ = (X , s₁)

 join : {S₀ : 𝓤 ̇ → 𝓥₀ ̇ } {S₁ : 𝓤 ̇ → 𝓥₁ ̇ }
      → SNS S₀ 𝓦₀
      → SNS S₁ 𝓦₁
      → SNS (λ X → S₀ X × S₁ X) (𝓦₀ ⊔ 𝓦₁)
 join {𝓤} {𝓥₀} {𝓥₁} {𝓦₀} {𝓦₁} {S₀} {S₁} (ι₀ , ρ₀ , θ₀) (ι₁ , ρ₁ , θ₁) = ι , ρ , θ
  where
   S : 𝓤 ̇ → 𝓥₀ ⊔ 𝓥₁ ̇
   S X = S₀ X × S₁ X

   ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦₀ ⊔ 𝓦₁ ̇
   ι A B e = ι₀ [ A ]₀ [ B ]₀ e  ×  ι₁ [ A ]₁ [ B ]₁ e

   ρ : (A : Σ S) → ι A A (≃-refl ⟨ A ⟩)
   ρ A = (ρ₀ [ A ]₀ , ρ₁ [ A ]₁)

   θ : {X : 𝓤 ̇ } (s t : S X) → is-embedding (canonical-map ι ρ s t)
   θ {X} (s₀ , s₁) (t₀ , t₁) = γ
    where
     c : (p : s₀ , s₁ ＝ t₀ , t₁) → ι₀ (X , s₀) (X , t₀) (≃-refl X)
                                 × ι₁ (X , s₁) (X , t₁) (≃-refl X)

     c p = (canonical-map ι₀ ρ₀ s₀ t₀ (ap pr₁ p) ,
            canonical-map ι₁ ρ₁ s₁ t₁ (ap pr₂ p))

     i : is-embedding c
     i = technical-lemma
          (canonical-map ι₀ ρ₀)
          (canonical-map ι₁ ρ₁)
          θ₀ θ₁ (s₀ , s₁) (t₀ , t₁)

     e : canonical-map ι ρ (s₀ , s₁) (t₀ , t₁) ∼ c
     e (refl {s₀ , s₁}) = 𝓻𝓮𝒻𝓵 (ρ₀ (X , s₀) , ρ₁ (X , s₁))

     γ : is-embedding (canonical-map ι ρ (s₀ , s₁) (t₀ , t₁))
     γ = embedding-closed-under-∼ _ _ i e

 _≃⟦_,_⟧_ : {S₀ : 𝓤 ̇ → 𝓥 ̇ } {S₁ : 𝓤 ̇ → 𝓥₁ ̇ }
          → (Σ X ꞉ 𝓤 ̇ , S₀ X × S₁ X)
          → SNS S₀ 𝓦₀
          → SNS S₁ 𝓦₁
          → (Σ X ꞉ 𝓤 ̇ , S₀ X × S₁ X)
          → 𝓤 ⊔ 𝓦₀ ⊔ 𝓦₁ ̇
 A ≃⟦ σ₀ , σ₁ ⟧ B = Σ f ꞉ (⟪ A ⟫ → ⟪ B ⟫)
                  , Σ i ꞉ is-equiv f , homomorphic σ₀ [ A ]₀ [ B ]₀ (f , i)
                                     × homomorphic σ₁ [ A ]₁ [ B ]₁ (f , i)

 join-＝-embedding : is-preunivalent 𝓤
                  → {S₀ : 𝓤 ̇ → 𝓥 ̇ } {S₁ : 𝓤 ̇ → 𝓥₁ ̇ }
                    (σ₀ : SNS S₀ 𝓦₀)  (σ₁ : SNS S₁ 𝓦₁)
                    (A B : Σ X ꞉ 𝓤 ̇ , S₀ X × S₁ X)
                  → (A ＝ B) ↪ (A ≃⟦ σ₀ , σ₁ ⟧ B)
 join-＝-embedding ua σ₀ σ₁ = ＝-embedding ua (join σ₀ σ₁)
-}

\end{code}
