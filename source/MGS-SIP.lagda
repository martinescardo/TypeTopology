This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module MGS-SIP where

open import MGS-More-FunExt-Consequences public
open import MGS-Yoneda                   public
open import MGS-Powerset                 public
open import MGS-Classifiers              public
open import MGS-Subsingleton-Truncation  public

module sip where

 ⟨_⟩ : {S : 𝓤 ̇ → 𝓥 ̇ } → Σ S → 𝓤 ̇
 ⟨ X , s ⟩ = X

 structure : {S : 𝓤 ̇ → 𝓥 ̇ } (A : Σ S) → S ⟨ A ⟩
 structure (X , s) = s

 canonical-map : {S : 𝓤 ̇ → 𝓥 ̇ }
                 (ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦 ̇ )
                 (ρ : (A : Σ S) → ι A A (id-≃ ⟨ A ⟩))
                 {X : 𝓤 ̇ }
                 (s t : S X)

               → s ≡ t → ι (X , s) (X , t) (id-≃ X)

 canonical-map ι ρ {X} s s (refl s) = ρ (X , s)

 SNS : (𝓤 ̇ → 𝓥 ̇ ) → (𝓦 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⊔ (𝓦 ⁺) ̇

 SNS {𝓤} {𝓥} S 𝓦 = Σ ι ꞉ ((A B : Σ S) → (⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦 ̇ ))
                  , Σ ρ ꞉ ((A : Σ S) → ι A A (id-≃ ⟨ A ⟩))
                  , ({X : 𝓤 ̇ } (s t : S X) → is-equiv (canonical-map ι ρ s t))

 homomorphic : {S : 𝓤 ̇ → 𝓥 ̇ } → SNS S 𝓦
             → (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦 ̇

 homomorphic (ι , ρ , θ) = ι

 _≃[_]_ : {S : 𝓤 ̇ → 𝓥 ̇ } → Σ S → SNS S 𝓦 → Σ S → 𝓤 ⊔ 𝓦 ̇

 A ≃[ σ ] B = Σ f ꞉ (⟨ A ⟩ → ⟨ B ⟩)
            , Σ i ꞉ is-equiv f
            , homomorphic σ A B (f , i)

 Id→homEq : {S : 𝓤 ̇ → 𝓥 ̇ } (σ : SNS S 𝓦)
          → (A B : Σ S) → (A ≡ B) → (A ≃[ σ ] B)

 Id→homEq (_ , ρ , _) A A (refl A) = id , id-is-equiv ⟨ A ⟩ , ρ A

 homomorphism-lemma : {S : 𝓤 ̇ → 𝓥 ̇ } (σ : SNS S 𝓦)
                      (A B : Σ S) (p : ⟨ A ⟩ ≡ ⟨ B ⟩)
                    →
                      (transport S p (structure A) ≡ structure B)
                    ≃  homomorphic σ A B (Id→Eq ⟨ A ⟩ ⟨ B ⟩ p)

 homomorphism-lemma (ι , ρ , θ) (X , s) (X , t) (refl X) = γ
  where
   γ : (s ≡ t) ≃ ι (X , s) (X , t) (id-≃ X)
   γ = (canonical-map ι ρ s t , θ s t)

 characterization-of-≡ : is-univalent 𝓤
                       → {S : 𝓤 ̇ → 𝓥 ̇ } (σ : SNS S 𝓦)
                       → (A B : Σ S)

                       → (A ≡ B) ≃ (A ≃[ σ ] B)

 characterization-of-≡ ua {S} σ A B =

    (A ≡ B)                                                           ≃⟨ i ⟩
    (Σ p ꞉ ⟨ A ⟩ ≡ ⟨ B ⟩ , transport S p (structure A) ≡ structure B) ≃⟨ ii ⟩
    (Σ p ꞉ ⟨ A ⟩ ≡ ⟨ B ⟩ , ι A B (Id→Eq ⟨ A ⟩ ⟨ B ⟩ p))               ≃⟨ iii ⟩
    (Σ e ꞉ ⟨ A ⟩ ≃ ⟨ B ⟩ , ι A B e)                                   ≃⟨ iv ⟩
    (A ≃[ σ ] B)                                                      ■

  where
   ι   = homomorphic σ

   i   = Σ-≡-≃ A B
   ii  = Σ-cong (homomorphism-lemma σ A B)
   iii = ≃-sym (Σ-change-of-variable (ι A B) (Id→Eq ⟨ A ⟩ ⟨ B ⟩) (ua ⟨ A ⟩ ⟨ B ⟩))
   iv  = Σ-assoc

 Id→homEq-is-equiv : (ua : is-univalent 𝓤) {S : 𝓤 ̇ → 𝓥 ̇ } (σ : SNS S 𝓦)
                   → (A B : Σ S) → is-equiv (Id→homEq σ A B)

 Id→homEq-is-equiv ua {S} σ A B = γ
  where
   h : (A B : Σ S) → Id→homEq σ A B ∼ ⌜ characterization-of-≡ ua σ A B ⌝
   h A A (refl A) = refl _

   γ : is-equiv (Id→homEq σ A B)
   γ = equivs-closed-under-∼
       (⌜⌝-is-equiv (characterization-of-≡ ua σ A B))
       (h A B)

 module _ {S : 𝓤 ̇ → 𝓥 ̇ }
          (ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦 ̇ )
          (ρ : (A : Σ S) → ι A A (id-≃ ⟨ A ⟩))
          {X : 𝓤 ̇ }

        where

  canonical-map-charac : (s t : S X) (p : s ≡ t)

                       → canonical-map ι ρ s t p
                       ≡ transport (λ - → ι (X , s) (X , -) (id-≃ X)) p (ρ (X , s))

  canonical-map-charac s = transport-lemma (λ t → ι (X , s) (X , t) (id-≃ X)) s
                            (canonical-map ι ρ s)

  when-canonical-map-is-equiv : ((s t : S X) → is-equiv (canonical-map ι ρ s t))
                              ⇔ ((s : S X) → ∃! t ꞉ S X , ι (X , s) (X , t) (id-≃ X))

  when-canonical-map-is-equiv = (λ e s → fiberwise-equiv-universal (A s) s (τ s) (e s)) ,
                                (λ φ s → universal-fiberwise-equiv (A s) (φ s) s (τ s))
   where
    A = λ s t → ι (X , s) (X , t) (id-≃ X)
    τ = canonical-map ι ρ

  canonical-map-equiv-criterion : ((s t : S X) → (s ≡ t) ≃ ι (X , s) (X , t) (id-≃ X))
                                → (s t : S X) → is-equiv (canonical-map ι ρ s t)

  canonical-map-equiv-criterion φ s = fiberwise-equiv-criterion'
                                       (λ t → ι (X , s) (X , t) (id-≃ X))
                                       s (φ s) (canonical-map ι ρ s)

  canonical-map-equiv-criterion' : ((s t : S X) → ι (X , s) (X , t) (id-≃ X) ◁ (s ≡ t))
                                 → (s t : S X) → is-equiv (canonical-map ι ρ s t)

  canonical-map-equiv-criterion' φ s = fiberwise-equiv-criterion
                                        (λ t → ι (X , s) (X , t) (id-≃ X))
                                        s (φ s) (canonical-map ι ρ s)

module ∞-magma {𝓤 : Universe} where

 open sip

 ∞-magma-structure : 𝓤 ̇ → 𝓤 ̇
 ∞-magma-structure X = X → X → X

 ∞-Magma : 𝓤 ⁺ ̇
 ∞-Magma = Σ X ꞉ 𝓤 ̇ , ∞-magma-structure X

 sns-data : SNS ∞-magma-structure 𝓤
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : ∞-Magma) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ̇
   ι (X , _·_) (Y , _*_) (f , _) = (λ x x' → f (x · x')) ≡ (λ x x' → f x * f x')

   ρ : (A : ∞-Magma) → ι A A (id-≃ ⟨ A ⟩)
   ρ (X , _·_) = refl _·_

   h : {X : 𝓤 ̇ } {_·_ _*_ : ∞-magma-structure X}
     → canonical-map ι ρ _·_ _*_ ∼ 𝑖𝑑 (_·_ ≡ _*_)

   h (refl _·_) = refl (refl _·_)

   θ : {X : 𝓤 ̇ } (_·_ _*_ : ∞-magma-structure X)
     → is-equiv (canonical-map ι ρ _·_ _*_)

   θ _·_ _*_ = equivs-closed-under-∼ (id-is-equiv (_·_ ≡ _*_)) h

 _≅_ : ∞-Magma → ∞-Magma → 𝓤 ̇

 (X , _·_) ≅ (Y , _*_) =

           Σ f ꞉ (X → Y), is-equiv f
                        × ((λ x x' → f (x · x')) ≡ (λ x x' → f x * f x'))

 characterization-of-∞-Magma-≡ : is-univalent 𝓤 → (A B : ∞-Magma) → (A ≡ B) ≃ (A ≅ B)
 characterization-of-∞-Magma-≡ ua = characterization-of-≡ ua sns-data

 characterization-of-characterization-of-∞-Magma-≡ :

    (ua : is-univalent 𝓤) (A : ∞-Magma)
  →
    ⌜ characterization-of-∞-Magma-≡ ua A A ⌝ (refl A)
  ≡
    (𝑖𝑑 ⟨ A ⟩ , id-is-equiv ⟨ A ⟩ , refl _)

 characterization-of-characterization-of-∞-Magma-≡ ua A = refl _

module sip-with-axioms where

 open sip

 [_] : {S : 𝓤 ̇ → 𝓥 ̇ } {axioms : (X : 𝓤 ̇ ) → S X → 𝓦 ̇ }
     → (Σ X ꞉ 𝓤 ̇ , Σ s ꞉ S X , axioms X s) → Σ S

 [ X , s , _ ] = (X , s)

 ⟪_⟫ : {S : 𝓤 ̇ → 𝓥 ̇ } {axioms : (X : 𝓤 ̇ ) → S X → 𝓦 ̇ }
     → (Σ X ꞉ 𝓤 ̇ , Σ s ꞉ S X , axioms X s) → 𝓤 ̇

 ⟪ X , _ , _ ⟫ = X

 add-axioms : {S : 𝓤 ̇ → 𝓥 ̇ }
              (axioms : (X : 𝓤 ̇ ) → S X → 𝓦 ̇ )
            → ((X : 𝓤 ̇ ) (s : S X) → is-subsingleton (axioms X s))

            → SNS S 𝓣
            → SNS (λ X → Σ s ꞉ S X , axioms X s) 𝓣

 add-axioms {𝓤} {𝓥} {𝓦} {𝓣} {S} axioms i (ι , ρ , θ) = ι' , ρ' , θ'
  where
   S' : 𝓤 ̇ → 𝓥 ⊔ 𝓦  ̇
   S' X = Σ s ꞉ S X , axioms X s

   ι' : (A B : Σ S') → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓣 ̇
   ι' A B = ι [ A ] [ B ]

   ρ' : (A : Σ S') → ι' A A (id-≃ ⟨ A ⟩)
   ρ' A = ρ [ A ]

   θ' : {X : 𝓤 ̇ } (s' t' : S' X) → is-equiv (canonical-map ι' ρ' s' t')
   θ' {X} (s , a) (t , b) = γ
    where
     π : S' X → S X
     π (s , _) = s

     j : is-embedding π
     j = pr₁-embedding (i X)

     k : {s' t' : S' X} → is-equiv (ap π {s'} {t'})
     k {s'} {t'} = embedding-gives-ap-is-equiv π j s' t'

     l : canonical-map ι' ρ' (s , a) (t , b)
       ∼ canonical-map ι ρ s t ∘ ap π {s , a} {t , b}

     l (refl (s , a)) = refl (ρ (X , s))

     e : is-equiv (canonical-map ι ρ s t ∘ ap π {s , a} {t , b})
     e = ∘-is-equiv (θ s t) k

     γ : is-equiv (canonical-map ι' ρ' (s , a) (t , b))
     γ = equivs-closed-under-∼ e l

 characterization-of-≡-with-axioms :

     is-univalent 𝓤
   → {S : 𝓤 ̇ → 𝓥 ̇ }
     (σ : SNS S 𝓣)
     (axioms : (X : 𝓤 ̇ ) → S X → 𝓦 ̇ )
   → ((X : 𝓤 ̇ ) (s : S X) → is-subsingleton (axioms X s))
   → (A B : Σ X ꞉ 𝓤 ̇ , Σ s ꞉ S X , axioms X s)

   → (A ≡ B) ≃ ([ A ] ≃[ σ ] [ B ])

 characterization-of-≡-with-axioms ua σ axioms i =
   characterization-of-≡ ua (add-axioms axioms i σ)

module magma {𝓤 : Universe} where

 open sip-with-axioms

 Magma : 𝓤 ⁺ ̇
 Magma = Σ X ꞉ 𝓤 ̇ , (X → X → X) × is-set X

 _≅_ : Magma → Magma → 𝓤 ̇

 (X , _·_ , _) ≅ (Y , _*_ , _) =

               Σ f ꞉ (X → Y), is-equiv f
                            × ((λ x x' → f (x · x')) ≡ (λ x x' → f x * f x'))

 characterization-of-Magma-≡ : is-univalent 𝓤 → (A B : Magma ) → (A ≡ B) ≃ (A ≅ B)
 characterization-of-Magma-≡ ua =
   characterization-of-≡-with-axioms ua
     ∞-magma.sns-data
     (λ X s → is-set X)
     (λ X s → being-set-is-subsingleton (univalence-gives-dfunext ua))

module pointed-type {𝓤 : Universe} where

 open sip

 Pointed : 𝓤 ̇ → 𝓤 ̇
 Pointed X = X

 sns-data : SNS Pointed 𝓤
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Σ Pointed) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ̇
   ι (X , x₀) (Y , y₀) (f , _) = (f x₀ ≡ y₀)

   ρ : (A : Σ Pointed) → ι A A (id-≃ ⟨ A ⟩)
   ρ (X , x₀) = refl x₀

   θ : {X : 𝓤 ̇ } (x₀ x₁ : Pointed X) → is-equiv (canonical-map ι ρ x₀ x₁)
   θ x₀ x₁ = equivs-closed-under-∼ (id-is-equiv (x₀ ≡ x₁)) h
    where
     h : canonical-map ι ρ x₀ x₁ ∼ 𝑖𝑑 (x₀ ≡ x₁)
     h (refl x₀) = refl (refl x₀)

 _≅_ : Σ Pointed → Σ Pointed → 𝓤 ̇
 (X , x₀) ≅ (Y , y₀) = Σ f ꞉ (X → Y), is-equiv f × (f x₀ ≡ y₀)

 characterization-of-pointed-type-≡ : is-univalent 𝓤
                                    → (A B : Σ Pointed)

                                    → (A ≡ B) ≃ (A ≅ B)

 characterization-of-pointed-type-≡ ua = characterization-of-≡ ua sns-data

module sip-join where

 technical-lemma :
     {X : 𝓤 ̇ } {A : X → X → 𝓥 ̇ }
     {Y : 𝓦 ̇ } {B : Y → Y → 𝓣 ̇ }
     (f : (x₀ x₁ : X) → x₀ ≡ x₁ → A x₀ x₁)
     (g : (y₀ y₁ : Y) → y₀ ≡ y₁ → B y₀ y₁)
   → ((x₀ x₁ : X) → is-equiv (f x₀ x₁))
   → ((y₀ y₁ : Y) → is-equiv (g y₀ y₁))

   → ((x₀ , y₀) (x₁ , y₁) : X × Y) → is-equiv (λ (p : (x₀ , y₀) ≡ (x₁ , y₁)) → f x₀ x₁ (ap pr₁ p) ,
                                                                               g y₀ y₁ (ap pr₂ p))
 technical-lemma {𝓤} {𝓥} {𝓦} {𝓣} {X} {A} {Y} {B} f g i j (x₀ , y₀) = γ
  where
   u : ∃! x₁ ꞉ X , A x₀ x₁
   u = fiberwise-equiv-universal (A x₀) x₀ (f x₀) (i x₀)

   v : ∃! y₁ ꞉ Y , B y₀ y₁
   v = fiberwise-equiv-universal (B y₀) y₀ (g y₀) (j y₀)

   C : X × Y → 𝓥 ⊔ 𝓣 ̇
   C (x₁ , y₁) = A x₀ x₁ × B y₀ y₁

   w : (∃! x₁ ꞉ X , A x₀ x₁)
     → (∃! y₁ ꞉ Y , B y₀ y₁)
     →  ∃! (x₁ , y₁) ꞉ X × Y , C (x₁ , y₁)
   w ((x₁ , a₁) , φ) ((y₁ , b₁) , ψ) = ((x₁ , y₁) , (a₁ , b₁)) , δ
    where
     p : ∀ x y a b
       → (x₁ , a₁) ≡ (x , a)
       → (y₁ , b₁) ≡ (y , b)
       → (x₁ , y₁) , (a₁ , b₁) ≡ (x , y) , (a , b)
     p .x₁ .y₁ .a₁ .b₁ (refl .(x₁ , a₁)) (refl .(y₁ , b₁)) = refl ((x₁ , y₁) , (a₁ , b₁))

     δ : (((x , y) , (a , b)) : Σ C) → (x₁ , y₁) , (a₁ , b₁) ≡ ((x , y) , (a , b))
     δ ((x , y) , (a , b)) = p x y a b (φ (x , a)) (ψ (y , b))

   τ : Nat (𝓨 (x₀ , y₀)) C
   τ (x₁ , y₁) p = f x₀ x₁ (ap pr₁ p) , g y₀ y₁ (ap pr₂ p)

   γ : is-fiberwise-equiv τ
   γ = universal-fiberwise-equiv C (w u v) (x₀ , y₀) τ


 variable
  𝓥₀ 𝓥₁ 𝓦₀ 𝓦₁ : Universe

 open sip

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

   ρ : (A : Σ S) → ι A A (id-≃ ⟨ A ⟩)
   ρ A = (ρ₀ [ A ]₀ , ρ₁ [ A ]₁)

   θ : {X : 𝓤 ̇ } (s t : S X) → is-equiv (canonical-map ι ρ s t)
   θ {X} (s₀ , s₁) (t₀ , t₁) = γ
    where
     c : (p : s₀ , s₁ ≡ t₀ , t₁) → ι₀ (X , s₀) (X , t₀) (id-≃ X)
                                 × ι₁ (X , s₁) (X , t₁) (id-≃ X)

     c p = (canonical-map ι₀ ρ₀ s₀ t₀ (ap pr₁ p) ,
            canonical-map ι₁ ρ₁ s₁ t₁ (ap pr₂ p))

     i : is-equiv c
     i = technical-lemma
          (canonical-map ι₀ ρ₀)
          (canonical-map ι₁ ρ₁)
          θ₀ θ₁ (s₀ , s₁) (t₀ , t₁)

     e : canonical-map ι ρ (s₀ , s₁) (t₀ , t₁) ∼ c
     e (refl (s₀ , s₁)) = refl (ρ₀ (X , s₀) , ρ₁ (X , s₁))

     γ : is-equiv (canonical-map ι ρ (s₀ , s₁) (t₀ , t₁))
     γ = equivs-closed-under-∼ i e

 _≃⟦_,_⟧_ : {S₀ : 𝓤 ̇ → 𝓥 ̇ } {S₁ : 𝓤 ̇ → 𝓥₁ ̇ }

          → (Σ X ꞉ 𝓤 ̇ , S₀ X × S₁ X)
          → SNS S₀ 𝓦₀
          → SNS S₁ 𝓦₁
          → (Σ X ꞉ 𝓤 ̇ , S₀ X × S₁ X)

          → 𝓤 ⊔ 𝓦₀ ⊔ 𝓦₁ ̇

 A ≃⟦ σ₀ , σ₁ ⟧ B = Σ f ꞉ (⟪ A ⟫ → ⟪ B ⟫)
                  , Σ i ꞉ is-equiv f , homomorphic σ₀ [ A ]₀ [ B ]₀ (f , i)
                                     × homomorphic σ₁ [ A ]₁ [ B ]₁ (f , i)

 characterization-of-join-≡ : is-univalent 𝓤
                            → {S₀ : 𝓤 ̇ → 𝓥 ̇ } {S₁ : 𝓤 ̇ → 𝓥₁ ̇ }
                              (σ₀ : SNS S₀ 𝓦₀)  (σ₁ : SNS S₁ 𝓦₁)
                              (A B : Σ X ꞉ 𝓤 ̇ , S₀ X × S₁ X)

                            → (A ≡ B) ≃ (A ≃⟦ σ₀ , σ₁ ⟧ B)

 characterization-of-join-≡ ua σ₀ σ₁ = characterization-of-≡ ua (join σ₀ σ₁)

module pointed-∞-magma {𝓤 : Universe} where

 open sip-join

 ∞-Magma· : 𝓤 ⁺ ̇
 ∞-Magma· = Σ X ꞉ 𝓤 ̇ , (X → X → X) × X

 _≅_ : ∞-Magma· → ∞-Magma· → 𝓤 ̇

 (X ,  _·_ , x₀) ≅ (Y ,  _*_ , y₀) =

                 Σ f ꞉ (X → Y), is-equiv f
                              × ((λ x x' → f (x · x')) ≡ (λ x x' → f x * f x'))
                              × (f x₀ ≡ y₀)

 characterization-of-pointed-magma-≡ : is-univalent 𝓤
                                     → (A B : ∞-Magma·)

                                     → (A ≡ B) ≃ (A ≅ B)

 characterization-of-pointed-magma-≡ ua = characterization-of-join-≡ ua
                                            ∞-magma.sns-data
                                            pointed-type.sns-data

module monoid {𝓤 : Universe} (ua : is-univalent 𝓤) where

 dfe : dfunext 𝓤 𝓤
 dfe = univalence-gives-dfunext ua

 open sip
 open sip-join
 open sip-with-axioms

 monoid-structure : 𝓤 ̇ → 𝓤 ̇
 monoid-structure X = (X → X → X) × X

 monoid-axioms : (X : 𝓤 ̇ ) → monoid-structure X → 𝓤 ̇
 monoid-axioms X (_·_ , e) = is-set X
                           × monoids.left-neutral  e _·_
                           × monoids.right-neutral e _·_
                           × monoids.associative     _·_

 Monoid : 𝓤 ⁺ ̇
 Monoid = Σ X ꞉ 𝓤 ̇ , Σ s ꞉ monoid-structure X , monoid-axioms X s

 monoid-axioms-subsingleton : (X : 𝓤 ̇ ) (s : monoid-structure X)
                            → is-subsingleton (monoid-axioms X s)

 monoid-axioms-subsingleton X (_·_ , e) s = γ s
  where
   i : is-set X
   i = pr₁ s

   γ : is-subsingleton (monoid-axioms X (_·_ , e))
   γ = ×-is-subsingleton
         (being-set-is-subsingleton dfe)
      (×-is-subsingleton
         (Π-is-subsingleton dfe
           (λ x → i (e · x) x))
      (×-is-subsingleton
         (Π-is-subsingleton dfe
           (λ x → i (x · e) x))
         (Π-is-subsingleton dfe
           (λ x → Π-is-subsingleton dfe
           (λ y → Π-is-subsingleton dfe
           (λ z → i ((x · y) · z) (x · (y · z))))))))

 sns-data : SNS (λ X → Σ s ꞉ monoid-structure X , monoid-axioms X s) 𝓤
 sns-data = add-axioms
              monoid-axioms monoid-axioms-subsingleton
              (join
                 ∞-magma.sns-data
                 pointed-type.sns-data)

 _≅_ : Monoid → Monoid → 𝓤 ̇

 (X , (_·_ , d) , _) ≅ (Y , (_*_ , e) , _) =

                     Σ f ꞉ (X → Y), is-equiv f
                                  × ((λ x x' → f (x · x')) ≡ (λ x x' → f x * f x'))
                                  × (f d ≡ e)

 characterization-of-monoid-≡ : is-univalent 𝓤
                              → (A B : Monoid)

                              → (A ≡ B) ≃ (A ≅ B)

 characterization-of-monoid-≡ ua = characterization-of-≡ ua sns-data

module associative-∞-magma
        {𝓤 : Universe}
        (ua : is-univalent 𝓤)
       where

 fe : dfunext 𝓤 𝓤
 fe = univalence-gives-dfunext ua

 associative : {X : 𝓤 ̇ } → (X → X → X) → 𝓤 ̇
 associative _·_ = ∀ x y z → (x · y) · z ≡ x · (y · z)

 ∞-amagma-structure : 𝓤 ̇ → 𝓤 ̇
 ∞-amagma-structure X = Σ _·_ ꞉ (X → X → X), (associative _·_)

 ∞-aMagma : 𝓤 ⁺ ̇
 ∞-aMagma = Σ X ꞉ 𝓤 ̇ , ∞-amagma-structure X

 homomorphic : {X Y : 𝓤 ̇ } → (X → X → X) → (Y → Y → Y) → (X → Y) → 𝓤 ̇
 homomorphic _·_ _*_ f = (λ x y → f (x · y)) ≡ (λ x y → f x * f y)

 respect-assoc : {X A : 𝓤 ̇ } (_·_ : X → X → X) (_*_ : A → A → A)
               → associative _·_ → associative _*_
               → (f : X → A) → homomorphic _·_ _*_ f → 𝓤 ̇

 respect-assoc _·_ _*_ α β f h  =  fα ≡ βf
  where
   l = λ x y z → f ((x · y) · z)   ≡⟨ ap (λ - → - (x · y) z) h ⟩
                 f (x · y) * f z   ≡⟨ ap (λ - → - x y * f z) h ⟩
                 (f x * f y) * f z ∎

   r = λ x y z → f (x · (y · z))   ≡⟨ ap (λ - → - x (y · z)) h ⟩
                 f x * f (y · z)   ≡⟨ ap (λ - → f x * - y z) h ⟩
                 f x * (f y * f z) ∎

   fα βf : ∀ x y z → (f x * f y) * f z ≡ f x * (f y * f z)
   fα x y z = (l x y z)⁻¹ ∙ ap f (α x y z) ∙ r x y z
   βf x y z = β (f x) (f y) (f z)

 remark : {X : 𝓤 ̇ } (_·_ : X → X → X) (α β : associative _·_ )
        → respect-assoc _·_ _·_ α β id (refl _·_)
        ≡ ((λ x y z → refl ((x · y) · z) ∙ ap id (α x y z)) ≡ β)

 remark _·_ α β = refl _

 open sip hiding (homomorphic)

 sns-data : SNS ∞-amagma-structure 𝓤
 sns-data = (ι , ρ , θ)
  where
   ι : (𝓧 𝓐 : ∞-aMagma) → ⟨ 𝓧 ⟩ ≃ ⟨ 𝓐 ⟩ → 𝓤 ̇
   ι (X , _·_ , α) (A , _*_ , β) (f , i) = Σ h ꞉ homomorphic _·_ _*_ f
                                               , respect-assoc _·_ _*_ α β f h

   ρ : (𝓧 : ∞-aMagma) → ι 𝓧 𝓧 (id-≃ ⟨ 𝓧 ⟩)
   ρ (X , _·_ , α) = h , p
    where
     h : homomorphic _·_ _·_ id
     h = refl _·_

     p : (λ x y z → refl ((x · y) · z) ∙ ap id (α x y z)) ≡ α
     p = fe (λ x → fe (λ y → fe (λ z → refl-left ∙ ap-id (α x y z))))

   u : (X : 𝓤 ̇ ) → ∀ s → ∃! t ꞉ ∞-amagma-structure X , ι (X , s) (X , t) (id-≃ X)
   u X (_·_ , α) = c , φ
    where
     c : Σ t ꞉ ∞-amagma-structure X , ι (X , _·_ , α) (X , t) (id-≃ X)
     c = (_·_ , α) , ρ (X , _·_ , α)

     φ : (σ : Σ t ꞉ ∞-amagma-structure X , ι (X , _·_ , α) (X , t) (id-≃ X)) → c ≡ σ
     φ ((_·_ , β) , refl _·_ , k) = γ
      where
       a : associative _·_
       a x y z = refl ((x · y) · z) ∙ ap id (α x y z)

       g : singleton-type' a → Σ t ꞉ ∞-amagma-structure X , ι (X , _·_ , α) (X , t) (id-≃ X)
       g (β , k) = (_·_ , β) , refl _·_ , k

       i : is-subsingleton (singleton-type' a)
       i = singletons-are-subsingletons _ (singleton-types'-are-singletons _ a)

       q : α , pr₂ (ρ (X , _·_ , α)) ≡ β , k
       q = i _ _

       γ : c ≡ (_·_ , β) , refl _·_ , k
       γ = ap g q

   θ : {X : 𝓤 ̇ } (s t : ∞-amagma-structure X) → is-equiv (canonical-map ι ρ s t)
   θ {X} s = universal-fiberwise-equiv (λ t → ι (X , s) (X , t) (id-≃ X))
              (u X s) s (canonical-map ι ρ s)

 _≅_ : ∞-aMagma → ∞-aMagma → 𝓤 ̇
 (X , _·_ , α) ≅ (Y , _*_ , β) = Σ f ꞉ (X → Y)
                                     , is-equiv f
                                     × (Σ h ꞉ homomorphic _·_ _*_ f
                                            , respect-assoc _·_ _*_ α β f h)

 characterization-of-∞-aMagma-≡ : (A B : ∞-aMagma) → (A ≡ B) ≃ (A ≅ B)
 characterization-of-∞-aMagma-≡ = characterization-of-≡ ua sns-data

module group {𝓤 : Universe} (ua : is-univalent 𝓤) where

 hfe : hfunext 𝓤 𝓤
 hfe = univalence-gives-hfunext ua

 open sip
 open sip-with-axioms
 open monoid {𝓤} ua hiding (sns-data ; _≅_)

 group-structure : 𝓤 ̇ → 𝓤 ̇
 group-structure X = Σ s ꞉ monoid-structure X , monoid-axioms X s

 group-axiom : (X : 𝓤 ̇ ) → monoid-structure X → 𝓤 ̇
 group-axiom X (_·_ , e) = (x : X) → Σ x' ꞉ X , (x · x' ≡ e) × (x' · x ≡ e)

 Group : 𝓤 ⁺ ̇
 Group = Σ X ꞉ 𝓤 ̇ , Σ ((_·_ , e) , a) ꞉ group-structure X , group-axiom X (_·_ , e)

 inv-lemma : (X : 𝓤 ̇ ) (_·_ : X → X → X) (e : X)
           → monoid-axioms X (_·_ , e)
           → (x y z : X)
           → (y · x) ≡ e
           → (x · z) ≡ e
           → y ≡ z

 inv-lemma X _·_  e (s , l , r , a) x y z q p =

    y             ≡⟨ (r y)⁻¹ ⟩
    (y · e)       ≡⟨ ap (y ·_) (p ⁻¹) ⟩
    (y · (x · z)) ≡⟨ (a y x z)⁻¹ ⟩
    ((y · x) · z) ≡⟨ ap (_· z) q ⟩
    (e · z)       ≡⟨ l z ⟩
    z             ∎

 group-axiom-is-subsingleton : (X : 𝓤 ̇ )
                             → (s : group-structure X)
                             → is-subsingleton (group-axiom X (pr₁ s))

 group-axiom-is-subsingleton X ((_·_ , e) , (s , l , r , a)) = γ
  where
   i : (x : X) → is-subsingleton (Σ x' ꞉ X , (x · x' ≡ e) × (x' · x ≡ e))
   i x (y , _ , q) (z , p , _) = u
    where
     t : y ≡ z
     t = inv-lemma X _·_ e (s , l , r , a) x y z q p

     u : (y , _ , q) ≡ (z , p , _)
     u = to-subtype-≡ (λ x' → ×-is-subsingleton (s (x · x') e) (s (x' · x) e)) t

   γ : is-subsingleton (group-axiom X (_·_ , e))
   γ = Π-is-subsingleton dfe i

 sns-data : SNS (λ X → Σ s ꞉ group-structure X , group-axiom X (pr₁ s)) 𝓤
 sns-data = add-axioms
             (λ X s → group-axiom X (pr₁ s)) group-axiom-is-subsingleton
             (monoid.sns-data ua)

 _≅_ : Group → Group → 𝓤 ̇

 (X , ((_·_ , d) , _) , _) ≅ (Y , ((_*_ , e) , _) , _) =

            Σ f ꞉ (X → Y), is-equiv f
                         × ((λ x x' → f (x · x')) ≡ (λ x x' → f x * f x'))
                         × (f d ≡ e)

 characterization-of-group-≡ : (A B : Group) → (A ≡ B) ≃ (A ≅ B)
 characterization-of-group-≡ = characterization-of-≡ ua sns-data

 _≅'_ : Group → Group → 𝓤 ̇

 (X , ((_·_ , d) , _) , _) ≅' (Y , ((_*_ , e) , _) , _) =

            Σ f ꞉ (X → Y), is-equiv f
                         × ((λ x x' → f (x · x')) ≡ (λ x x' → f x * f x'))

 group-structure-of : (G : Group) → group-structure ⟨ G ⟩
 group-structure-of (X , ((_·_ , e) , i , l , r , a) , γ) = (_·_ , e) , i , l , r , a

 monoid-structure-of : (G : Group) → monoid-structure ⟨ G ⟩
 monoid-structure-of (X , ((_·_ , e) , i , l , r , a) , γ) = (_·_ , e)

 monoid-axioms-of : (G : Group) → monoid-axioms ⟨ G ⟩ (monoid-structure-of G)
 monoid-axioms-of (X , ((_·_ , e) , i , l , r , a) , γ) = i , l , r , a

 multiplication : (G : Group) → ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
 multiplication (X , ((_·_ , e) , i , l , r , a) , γ) = _·_

 syntax multiplication G x y = x ·⟨ G ⟩ y

 unit : (G : Group) → ⟨ G ⟩
 unit (X , ((_·_ , e) , i , l , r , a) , γ) = e

 group-is-set : (G : Group)
              → is-set ⟨ G ⟩

 group-is-set (X , ((_·_ , e) , i , l , r , a) , γ) = i

 unit-left : (G : Group) (x : ⟨ G ⟩)
           → unit G ·⟨ G ⟩ x ≡ x

 unit-left (X , ((_·_ , e) , i , l , r , a) , γ) x = l x

 unit-right : (G : Group) (x : ⟨ G ⟩)
            → x ·⟨ G ⟩ unit G ≡ x

 unit-right (X , ((_·_ , e) , i , l , r , a) , γ) x = r x

 assoc : (G : Group) (x y z : ⟨ G ⟩)
       → (x ·⟨ G ⟩ y) ·⟨ G ⟩ z ≡ x ·⟨ G ⟩ (y ·⟨ G ⟩ z)

 assoc (X , ((_·_ , e) , i , l , r , a) , γ) = a

 inv : (G : Group) → ⟨ G ⟩ → ⟨ G ⟩
 inv (X , ((_·_ , e) , i , l , r , a) , γ) x = pr₁ (γ x)

 inv-left : (G : Group) (x : ⟨ G ⟩)
          → inv G x ·⟨ G ⟩ x ≡ unit G

 inv-left (X , ((_·_ , e) , i , l , r , a) , γ) x = pr₂ (pr₂ (γ x))

 inv-right : (G : Group) (x : ⟨ G ⟩)
           → x ·⟨ G ⟩ inv G x ≡ unit G

 inv-right (X , ((_·_ , e) , i , l , r , a) , γ) x = pr₁ (pr₂ (γ x))

 preserves-multiplication : (G H : Group) → (⟨ G ⟩ → ⟨ H ⟩) → 𝓤 ̇
 preserves-multiplication G H f = (λ (x y : ⟨ G ⟩) → f (x ·⟨ G ⟩ y))
                                ≡ (λ (x y : ⟨ G ⟩) → f x ·⟨ H ⟩ f y)

 preserves-unit : (G H : Group) → (⟨ G ⟩ → ⟨ H ⟩) → 𝓤 ̇
 preserves-unit G H f = f (unit G) ≡ unit H

 idempotent-is-unit : (G : Group) (x : ⟨ G ⟩)
                    → x ·⟨ G ⟩ x ≡ x
                    → x ≡ unit G

 idempotent-is-unit G x p = γ
  where
   x' = inv G x
   γ = x                        ≡⟨ (unit-left G x)⁻¹ ⟩
       unit G ·⟨ G ⟩ x          ≡⟨ (ap (λ - → - ·⟨ G ⟩ x) (inv-left G x))⁻¹ ⟩
       (x' ·⟨ G ⟩ x) ·⟨ G ⟩ x   ≡⟨ assoc G x' x x ⟩
       x' ·⟨ G ⟩ (x ·⟨ G ⟩ x)   ≡⟨ ap (λ - → x' ·⟨ G ⟩ -) p ⟩
       x' ·⟨ G ⟩ x              ≡⟨ inv-left G x ⟩
       unit G                   ∎

 unit-preservation-lemma : (G H : Group) (f : ⟨ G ⟩ → ⟨ H ⟩)
                         → preserves-multiplication G H f
                         → preserves-unit G H f

 unit-preservation-lemma G H f m = idempotent-is-unit H e p
  where
   e  = f (unit G)

   p = e ·⟨ H ⟩ e               ≡⟨ ap (λ - → - (unit G) (unit G)) (m ⁻¹) ⟩
       f (unit G ·⟨ G ⟩ unit G) ≡⟨ ap f (unit-left G (unit G)) ⟩
       e                        ∎

 inv-Lemma : (G : Group) (x y z : ⟨ G ⟩)
           → (y ·⟨ G ⟩ x) ≡ unit G
           → (x ·⟨ G ⟩ z) ≡ unit G
           → y ≡ z

 inv-Lemma G = inv-lemma ⟨ G ⟩ (multiplication G) (unit G) (monoid-axioms-of G)

 one-left-inv : (G : Group) (x x' : ⟨ G ⟩)
              → (x' ·⟨ G ⟩ x) ≡ unit G
              → x' ≡ inv G x

 one-left-inv G x x' p = inv-Lemma G x x' (inv G x) p (inv-right G x)

 one-right-inv : (G : Group) (x x' : ⟨ G ⟩)
               → (x ·⟨ G ⟩ x') ≡ unit G
               → x' ≡ inv G x

 one-right-inv G x x' p = (inv-Lemma G x (inv G x) x' (inv-left G x) p)⁻¹

 preserves-inv : (G H : Group) → (⟨ G ⟩ → ⟨ H ⟩) → 𝓤 ̇
 preserves-inv G H f = (x : ⟨ G ⟩) → f (inv G x) ≡ inv H (f x)

 inv-preservation-lemma : (G H : Group) (f : ⟨ G ⟩ → ⟨ H ⟩)
                        → preserves-multiplication G H f
                        → preserves-inv G H f

 inv-preservation-lemma G H f m x = γ
  where
   p = f (inv G x) ·⟨ H ⟩ f x ≡⟨ (ap (λ - → - (inv G x) x) m)⁻¹ ⟩
       f (inv G x ·⟨ G ⟩ x)   ≡⟨ ap f (inv-left G x) ⟩
       f (unit G)             ≡⟨ unit-preservation-lemma G H f m ⟩
       unit H                 ∎

   γ : f (inv G x) ≡ inv H (f x)
   γ = one-left-inv H (f x) (f (inv G x)) p

 is-homomorphism : (G H : Group) → (⟨ G ⟩ → ⟨ H ⟩) → 𝓤 ̇
 is-homomorphism G H f = preserves-multiplication G H f
                       × preserves-unit G H f

 preservation-of-mult-is-subsingleton : (G H : Group) (f : ⟨ G ⟩ → ⟨ H ⟩)
                                      → is-subsingleton (preserves-multiplication G H f)
 preservation-of-mult-is-subsingleton G H f = j
  where
   j : is-subsingleton (preserves-multiplication G H f)
   j = Π-is-set hfe
        (λ _ → Π-is-set hfe
        (λ _ → group-is-set H))
        (λ (x y : ⟨ G ⟩) → f (x ·⟨ G ⟩ y))
        (λ (x y : ⟨ G ⟩) → f x ·⟨ H ⟩ f y)

 being-homomorphism-is-subsingleton : (G H : Group) (f : ⟨ G ⟩ → ⟨ H ⟩)
                                    → is-subsingleton (is-homomorphism G H f)
 being-homomorphism-is-subsingleton G H f = i
  where

   i : is-subsingleton (is-homomorphism G H f)
   i = ×-is-subsingleton
        (preservation-of-mult-is-subsingleton G H f)
        (group-is-set H (f (unit G)) (unit H))

 notions-of-homomorphism-agree : (G H : Group) (f : ⟨ G ⟩ → ⟨ H ⟩)
                               → is-homomorphism G H f
                               ≃ preserves-multiplication G H f

 notions-of-homomorphism-agree G H f = γ
  where
   α : is-homomorphism G H f → preserves-multiplication G H f
   α = pr₁

   β : preserves-multiplication G H f → is-homomorphism G H f
   β m = m , unit-preservation-lemma G H f m

   γ : is-homomorphism G H f ≃ preserves-multiplication G H f
   γ = logically-equivalent-subsingletons-are-equivalent _ _
        (being-homomorphism-is-subsingleton G H f)
        (preservation-of-mult-is-subsingleton G H f)
        (α , β)

 ≅-agreement : (G H : Group) → (G ≅ H) ≃ (G ≅' H)
 ≅-agreement G H = Σ-cong (λ f → Σ-cong (λ _ → notions-of-homomorphism-agree G H f))

 forget-unit-preservation : (G H : Group) → (G ≅ H) → (G ≅' H)
 forget-unit-preservation G H (f , e , m , _) = f , e , m

 NB : (G H : Group) → ⌜ ≅-agreement G H ⌝ ≡ forget-unit-preservation G H
 NB G H = refl _

 forget-unit-preservation-is-equiv : (G H : Group)
                                   → is-equiv (forget-unit-preservation G H)

 forget-unit-preservation-is-equiv G H = ⌜⌝-is-equiv (≅-agreement G H)

module subgroup
        (𝓤  : Universe)
        (ua : Univalence)
       where

 gfe : global-dfunext
 gfe = univalence-gives-global-dfunext ua

 open sip
 open monoid {𝓤} (ua 𝓤) hiding (sns-data ; _≅_)
 open group {𝓤} (ua 𝓤)

 module ambient (G : Group) where

  _·_ : ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
  x · y = x ·⟨ G ⟩ y

  infixl 42 _·_

  group-closed : (⟨ G ⟩ → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
  group-closed 𝓐 = 𝓐 (unit G)
                 × ((x y : ⟨ G ⟩) → 𝓐 x → 𝓐 y → 𝓐 (x · y))
                 × ((x : ⟨ G ⟩) → 𝓐 x → 𝓐 (inv G x))

  Subgroups : 𝓤 ⁺ ̇
  Subgroups = Σ A ꞉ 𝓟 ⟨ G ⟩ , group-closed (_∈ A)

  ⟪_⟫ : Subgroups → 𝓟 ⟨ G ⟩
  ⟪ A , u , c , ι ⟫ = A

  being-group-closed-subset-is-subsingleton : (A : 𝓟 ⟨ G ⟩) → is-subsingleton (group-closed (_∈ A))
  being-group-closed-subset-is-subsingleton A = ×-is-subsingleton
                                                  (∈-is-subsingleton A (unit G))
                                               (×-is-subsingleton
                                                  (Π-is-subsingleton dfe
                                                     (λ x → Π-is-subsingleton dfe
                                                     (λ y → Π-is-subsingleton dfe
                                                     (λ _ → Π-is-subsingleton dfe
                                                     (λ _ → ∈-is-subsingleton A (x · y))))))
                                                  (Π-is-subsingleton dfe
                                                     (λ x → Π-is-subsingleton dfe
                                                     (λ _ → ∈-is-subsingleton A (inv G x)))))

  ⟪⟫-is-embedding : is-embedding ⟪_⟫
  ⟪⟫-is-embedding = pr₁-embedding being-group-closed-subset-is-subsingleton

  ap-⟪⟫ : (S T : Subgroups) → S ≡ T → ⟪ S ⟫ ≡ ⟪ T ⟫
  ap-⟪⟫ S T = ap ⟪_⟫

  ap-⟪⟫-is-equiv : (S T : Subgroups) → is-equiv (ap-⟪⟫ S T)
  ap-⟪⟫-is-equiv = embedding-gives-ap-is-equiv ⟪_⟫ ⟪⟫-is-embedding

  subgroups-form-a-set : is-set Subgroups
  subgroups-form-a-set S T = equiv-to-subsingleton
                              (ap-⟪⟫ S T , ap-⟪⟫-is-equiv S T)
                              (powersets-are-sets' ua ⟪ S ⟫ ⟪ T ⟫)

  subgroup-equality : (S T : Subgroups)
                    → (S ≡ T)
                    ≃ ((x : ⟨ G ⟩) → (x ∈ ⟪ S ⟫) ⇔ (x ∈ ⟪ T ⟫))

  subgroup-equality S T = γ
   where
    f : S ≡ T → (x : ⟨ G ⟩) → x ∈ ⟪ S ⟫ ⇔ x ∈ ⟪ T ⟫
    f p x = transport (λ - → x ∈ ⟪ - ⟫) p , transport (λ - → x ∈ ⟪ - ⟫) (p ⁻¹)

    h : ((x : ⟨ G ⟩) → x ∈ ⟪ S ⟫ ⇔ x ∈ ⟪ T ⟫) → ⟪ S ⟫ ≡ ⟪ T ⟫
    h φ = subset-extensionality' ua α β
     where
      α : ⟪ S ⟫ ⊆ ⟪ T ⟫
      α x = lr-implication (φ x)

      β : ⟪ T ⟫ ⊆ ⟪ S ⟫
      β x = rl-implication (φ x)

    g : ((x : ⟨ G ⟩) → x ∈ ⟪ S ⟫ ⇔ x ∈ ⟪ T ⟫) → S ≡ T
    g = inverse (ap-⟪⟫ S T) (ap-⟪⟫-is-equiv S T) ∘ h

    γ : (S ≡ T) ≃ ((x : ⟨ G ⟩) → x ∈ ⟪ S ⟫ ⇔ x ∈ ⟪ T ⟫)
    γ = logically-equivalent-subsingletons-are-equivalent _ _
          (subgroups-form-a-set S T)
          (Π-is-subsingleton dfe
             (λ x → ×-is-subsingleton
                      (Π-is-subsingleton dfe (λ _ → ∈-is-subsingleton ⟪ T ⟫ x))
                      (Π-is-subsingleton dfe (λ _ → ∈-is-subsingleton ⟪ S ⟫ x))))
          (f , g)

  T : 𝓤 ̇ → 𝓤 ̇
  T X = Σ ((_·_ , e) , a) ꞉ group-structure X , group-axiom X (_·_ , e)

  module _ {X : 𝓤 ̇ } (h : X → ⟨ G ⟩) (e : is-embedding h) where

   private
    h-lc : left-cancellable h
    h-lc = embeddings-are-lc h e

   having-group-closed-fiber-is-subsingleton : is-subsingleton (group-closed (fiber h))
   having-group-closed-fiber-is-subsingleton = being-group-closed-subset-is-subsingleton
                                                (λ x → (fiber h x , e x))

   at-most-one-homomorphic-structure : is-subsingleton (Σ τ ꞉ T X , is-homomorphism (X , τ) G h)
   at-most-one-homomorphic-structure
      ((((_*_ ,  unitH) ,  maxioms) ,  gaxiom) ,  (pmult ,  punit))
      ((((_*'_ , unitH') , maxioms') , gaxiom') , (pmult' , punit'))
    = γ
    where
     τ τ' : T X
     τ  = ((_*_ ,  unitH) ,  maxioms) ,  gaxiom
     τ' = ((_*'_ , unitH') , maxioms') , gaxiom'

     i :  is-homomorphism (X , τ)  G h
     i  = (pmult ,  punit)

     i' : is-homomorphism (X , τ') G h
     i' = (pmult' , punit')

     p : _*_ ≡ _*'_
     p = gfe (λ x → gfe (λ y → h-lc (h (x * y)  ≡⟨  ap (λ - → - x y) pmult ⟩
                                     h x · h y  ≡⟨ (ap (λ - → - x y) pmult')⁻¹ ⟩
                                     h (x *' y) ∎)))
     q : unitH ≡ unitH'
     q = h-lc (h unitH  ≡⟨  punit ⟩
               unit G   ≡⟨  punit' ⁻¹ ⟩
               h unitH' ∎)

     r : (_*_ , unitH) ≡ (_*'_ , unitH')
     r = to-×-≡ (p , q)

     δ : τ ≡ τ'
     δ = to-subtype-≡
           (group-axiom-is-subsingleton X)
           (to-subtype-≡
              (monoid-axioms-subsingleton X)
              r)

     γ : (τ  , i) ≡ (τ' , i')
     γ = to-subtype-≡ (λ τ → being-homomorphism-is-subsingleton (X , τ) G h) δ

   group-closed-fiber-gives-homomorphic-structure : group-closed (fiber h)
                                                  → (Σ τ ꞉ T X , is-homomorphism (X , τ) G h)

   group-closed-fiber-gives-homomorphic-structure (unitc , mulc , invc) = τ , i
    where
     φ : (x : X) → fiber h (h x)
     φ x = (x , refl (h x))

     unitH : X
     unitH = fiber-point unitc

     _*_ : X → X → X
     x * y = fiber-point (mulc (h x) (h y) (φ x) (φ y))

     invH : X → X
     invH x = fiber-point (invc (h x) (φ x))

     pmul : (x y : X) → h (x * y) ≡ h x · h y
     pmul x y = fiber-identification (mulc (h x) (h y) (φ x) (φ y))

     punit : h unitH ≡ unit G
     punit = fiber-identification unitc

     pinv : (x : X) → h (invH x) ≡ inv G (h x)
     pinv x = fiber-identification (invc (h x) (φ x))

     unitH-left : (x : X) → unitH * x ≡ x
     unitH-left x = h-lc (h (unitH * x) ≡⟨ pmul unitH x ⟩
                          h unitH · h x ≡⟨ ap (_· h x) punit ⟩
                          unit G · h x  ≡⟨ unit-left G (h x) ⟩
                          h x           ∎)

     unitH-right : (x : X) → x * unitH ≡ x
     unitH-right x = h-lc (h (x * unitH) ≡⟨ pmul x unitH ⟩
                           h x · h unitH ≡⟨ ap (h x ·_) punit ⟩
                           h x · unit G  ≡⟨ unit-right G (h x) ⟩
                           h x           ∎)

     assocH : (x y z : X) → ((x * y) * z) ≡ (x * (y * z))
     assocH x y z = h-lc (h ((x * y) * z)   ≡⟨ pmul (x * y) z ⟩
                          h (x * y) · h z   ≡⟨ ap (_· h z) (pmul x y) ⟩
                          (h x · h y) · h z ≡⟨ assoc G (h x) (h y) (h z) ⟩
                          h x · (h y · h z) ≡⟨ (ap (h x ·_) (pmul y z))⁻¹ ⟩
                          h x · h (y * z)   ≡⟨ (pmul x (y * z))⁻¹ ⟩
                          h (x * (y * z))   ∎)

     group-axiomH : (x : X) → Σ x' ꞉ X , (x * x' ≡ unitH) × (x' * x ≡ unitH)
     group-axiomH x = invH x ,

                      h-lc (h (x * invH x)     ≡⟨ pmul x (invH x) ⟩
                            h x · h (invH x)   ≡⟨ ap (h x ·_) (pinv x) ⟩
                            h x · inv G (h x)  ≡⟨ inv-right G (h x) ⟩
                            unit G             ≡⟨ punit ⁻¹ ⟩
                            h unitH            ∎),

                      h-lc ((h (invH x * x)    ≡⟨ pmul (invH x) x ⟩
                             h (invH x) · h x  ≡⟨ ap (_· h x) (pinv x) ⟩
                             inv G (h x) · h x ≡⟨ inv-left G (h x) ⟩
                             unit G            ≡⟨ punit ⁻¹ ⟩
                             h unitH           ∎))

     j : is-set X
     j = subtypes-of-sets-are-sets h h-lc (group-is-set G)

     τ : T X
     τ = ((_*_ , unitH) , (j , unitH-left , unitH-right , assocH)) , group-axiomH

     i : is-homomorphism (X , τ) G h
     i = gfe (λ x → gfe (pmul x)) , punit

   homomorphic-structure-gives-group-closed-fiber : (Σ τ ꞉ T X , is-homomorphism (X , τ) G h)
                                                  → group-closed (fiber h)

   homomorphic-structure-gives-group-closed-fiber
       ((((_*_ , unitH) , maxioms) , gaxiom) , (pmult , punit))
     = (unitc , mulc , invc)
    where
     H : Group
     H = X , ((_*_ , unitH) , maxioms) , gaxiom

     unitc : fiber h (unit G)
     unitc = unitH , punit

     mulc : ((x y : ⟨ G ⟩) → fiber h x → fiber h y → fiber h (x · y))
     mulc x y (a , p) (b , q) = (a * b) ,
                                (h (a * b) ≡⟨ ap (λ - → - a b) pmult ⟩
                                 h a · h b ≡⟨ ap₂ (λ - -' → - · -') p q ⟩
                                 x · y     ∎)

     invc : ((x : ⟨ G ⟩) → fiber h x → fiber h (inv G x))
     invc x (a , p) = inv H a ,
                      (h (inv H a) ≡⟨ inv-preservation-lemma H G h pmult a ⟩
                       inv G (h a) ≡⟨ ap (inv G) p ⟩
                       inv G x     ∎)

   fiber-structure-lemma : group-closed (fiber h)
                         ≃ (Σ τ ꞉ T X , is-homomorphism (X , τ) G h)

   fiber-structure-lemma = logically-equivalent-subsingletons-are-equivalent _ _
                             having-group-closed-fiber-is-subsingleton
                             at-most-one-homomorphic-structure
                             (group-closed-fiber-gives-homomorphic-structure ,
                              homomorphic-structure-gives-group-closed-fiber)

  characterization-of-the-type-of-subgroups :  Subgroups ≃  (Σ H ꞉ Group
                                                           , Σ h ꞉ (⟨ H ⟩ → ⟨ G ⟩)
                                                           , is-embedding h
                                                           × is-homomorphism H G h)
  characterization-of-the-type-of-subgroups =

   Subgroups                                                                                       ≃⟨ i ⟩
   (Σ A ꞉ 𝓟 ⟨ G ⟩ , group-closed (_∈ A))                                                           ≃⟨ ii ⟩
   (Σ (X , h , e) ꞉ Subtypes ⟨ G ⟩ , group-closed (fiber h))                                       ≃⟨ iii ⟩
   (Σ X ꞉ 𝓤 ̇ , Σ (h , e) ꞉ X ↪ ⟨ G ⟩ , group-closed (fiber h))                                     ≃⟨ iv ⟩
   (Σ X ꞉ 𝓤 ̇ , Σ (h , e) ꞉ X ↪ ⟨ G ⟩ , Σ τ ꞉ T X , is-homomorphism (X , τ) G h)                    ≃⟨ v ⟩
   (Σ X ꞉ 𝓤 ̇ , Σ h ꞉ (X → ⟨ G ⟩) , Σ e ꞉ is-embedding h , Σ τ ꞉ T X , is-homomorphism (X , τ) G h) ≃⟨ vi ⟩
   (Σ X ꞉ 𝓤 ̇ , Σ h ꞉ (X → ⟨ G ⟩) , Σ τ ꞉ T X , Σ e ꞉ is-embedding h , is-homomorphism (X , τ) G h) ≃⟨ vii ⟩
   (Σ X ꞉ 𝓤 ̇ , Σ τ ꞉ T X , Σ h ꞉ (X → ⟨ G ⟩) , is-embedding h × is-homomorphism (X , τ) G h)       ≃⟨ viii ⟩
   (Σ H ꞉ Group , Σ h ꞉ (⟨ H ⟩ → ⟨ G ⟩) , is-embedding h × is-homomorphism H G h)                  ■

      where
       φ : Subtypes ⟨ G ⟩ → 𝓟 ⟨ G ⟩
       φ = χ-special is-subsingleton ⟨ G ⟩

       j : is-equiv φ
       j = χ-special-is-equiv (ua 𝓤) gfe is-subsingleton ⟨ G ⟩

       i    = id-≃ Subgroups
       ii   = Σ-change-of-variable (λ (A : 𝓟 ⟨ G ⟩) → group-closed (_∈ A)) φ j
       iii  = Σ-assoc
       iv   = Σ-cong (λ X → Σ-cong (λ (h , e) → fiber-structure-lemma h e))
       v    = Σ-cong (λ X → Σ-assoc)
       vi   = Σ-cong (λ X → Σ-cong (λ h → Σ-flip))
       vii  = Σ-cong (λ X → Σ-flip)
       viii = ≃-sym Σ-assoc

  induced-group : Subgroups → Group
  induced-group S = pr₁ (⌜ characterization-of-the-type-of-subgroups ⌝ S)

module slice
        {𝓤 𝓥 : Universe}
        (R : 𝓥 ̇ )
       where

 open sip

 S : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 S X = X → R

 sns-data : SNS S (𝓤 ⊔ 𝓥)
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ⊔ 𝓥 ̇
   ι (X , g) (Y , h) (f , _) = (g ≡ h ∘ f)

   ρ : (A : Σ S) → ι A A (id-≃ ⟨ A ⟩)
   ρ (X , g) = refl g

   k : {X : 𝓤 ̇ } {g h : S X} → canonical-map ι ρ g h ∼ 𝑖𝑑 (g ≡ h)
   k (refl g) = refl (refl g)

   θ : {X : 𝓤 ̇ } (g h : S X) → is-equiv (canonical-map ι ρ g h)
   θ g h = equivs-closed-under-∼ (id-is-equiv (g ≡ h)) k

 _≅_  : 𝓤 / R → 𝓤 / R → 𝓤 ⊔ 𝓥 ̇
 (X , g) ≅ (Y , h) = Σ f ꞉ (X → Y), is-equiv f × (g ≡ h ∘ f )

 characterization-of-/-≡ : is-univalent 𝓤 → (A B : 𝓤 / R) → (A ≡ B) ≃ (A ≅ B)
 characterization-of-/-≡ ua = characterization-of-≡ ua sns-data

module generalized-metric-space
        {𝓤 𝓥 : Universe}
        (R : 𝓥 ̇ )
        (axioms  : (X : 𝓤 ̇ ) → (X → X → R) → 𝓤 ⊔ 𝓥 ̇ )
        (axiomss : (X : 𝓤 ̇ ) (d : X → X → R) → is-subsingleton (axioms X d))
       where

 open sip
 open sip-with-axioms

 S : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 S X = X → X → R

 sns-data : SNS S (𝓤 ⊔ 𝓥)
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ⊔ 𝓥 ̇
   ι (X , d) (Y , e) (f , _) = (d ≡ λ x x' → e (f x) (f x'))

   ρ : (A : Σ S) → ι A A (id-≃ ⟨ A ⟩)
   ρ (X , d) = refl d

   h : {X : 𝓤 ̇ } {d e : S X} → canonical-map ι ρ d e ∼ 𝑖𝑑 (d ≡ e)
   h (refl d) = refl (refl d)

   θ : {X : 𝓤 ̇ } (d e : S X) → is-equiv (canonical-map ι ρ d e)
   θ d e = equivs-closed-under-∼ (id-is-equiv (d ≡ e)) h

 M : 𝓤 ⁺ ⊔ 𝓥  ̇
 M = Σ X ꞉ 𝓤 ̇ , Σ d ꞉ (X → X → R) , axioms X d

 _≅_  : M → M → 𝓤 ⊔ 𝓥 ̇
 (X , d , _) ≅ (Y , e , _) = Σ f ꞉ (X → Y), is-equiv f
                                          × (d ≡ λ x x' → e (f x) (f x'))

 characterization-of-M-≡ : is-univalent 𝓤
                         → (A B : M)

                         → (A ≡ B) ≃ (A ≅ B)

 characterization-of-M-≡ ua = characterization-of-≡-with-axioms ua
                                sns-data
                                axioms axiomss

module generalized-topological-space
        (𝓤 𝓥 : Universe)
        (R : 𝓥 ̇ )
        (axioms  : (X : 𝓤 ̇ ) → ((X → R) → R) → 𝓤 ⊔ 𝓥 ̇ )
        (axiomss : (X : 𝓤 ̇ ) (𝓞 : (X → R) → R) → is-subsingleton (axioms X 𝓞))
       where

 open sip
 open sip-with-axioms

 ℙ : 𝓦 ̇ → 𝓥 ⊔ 𝓦 ̇
 ℙ X = X → R

 _∊_ : {X : 𝓦 ̇ } → X → ℙ X → R
 x ∊ A = A x

 inverse-image : {X Y : 𝓤 ̇ } → (X → Y) → ℙ Y → ℙ X
 inverse-image f B = λ x → f x ∊ B

 ℙℙ : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 ℙℙ X = ℙ (ℙ X)

 Space : 𝓤 ⁺ ⊔ 𝓥  ̇
 Space = Σ X ꞉ 𝓤 ̇ , Σ 𝓞 ꞉ ℙℙ X , axioms X 𝓞

 sns-data : SNS ℙℙ (𝓤 ⊔ 𝓥)
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Σ ℙℙ) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ⊔ 𝓥 ̇
   ι (X , 𝓞X) (Y , 𝓞Y) (f , _) = (λ (V : ℙ Y) → inverse-image f V ∊ 𝓞X) ≡ 𝓞Y

   ρ : (A : Σ ℙℙ) → ι A A (id-≃ ⟨ A ⟩)
   ρ (X , 𝓞) = refl 𝓞

   h : {X : 𝓤 ̇ } {𝓞 𝓞' : ℙℙ X} → canonical-map ι ρ 𝓞 𝓞' ∼ 𝑖𝑑 (𝓞 ≡ 𝓞')
   h (refl 𝓞) = refl (refl 𝓞)

   θ : {X : 𝓤 ̇ } (𝓞 𝓞' : ℙℙ X) → is-equiv (canonical-map ι ρ 𝓞 𝓞')
   θ {X} 𝓞 𝓞' = equivs-closed-under-∼ (id-is-equiv (𝓞 ≡ 𝓞')) h

 _≅_  : Space → Space → 𝓤 ⊔ 𝓥 ̇

 (X , 𝓞X , _) ≅ (Y , 𝓞Y , _) =

              Σ f ꞉ (X → Y), is-equiv f
                           × ((λ V → inverse-image f V ∊ 𝓞X) ≡ 𝓞Y)

 characterization-of-Space-≡ : is-univalent 𝓤
                             → (A B : Space)

                             → (A ≡ B) ≃ (A ≅ B)

 characterization-of-Space-≡ ua = characterization-of-≡-with-axioms ua
                                   sns-data axioms axiomss

 _≅'_  : Space → Space → 𝓤 ⊔ 𝓥 ̇

 (X , F , _) ≅' (Y , G , _) =

             Σ f ꞉ (X → Y), is-equiv f
                          × ((λ (v : Y → R) → F (v ∘ f)) ≡ G)

 characterization-of-Space-≡' : is-univalent 𝓤
                              → (A B : Space)

                              → (A ≡ B) ≃ (A ≅' B)

 characterization-of-Space-≡' = characterization-of-Space-≡

module selection-space
        (𝓤 𝓥 : Universe)
        (R : 𝓥 ̇ )
        (axioms  : (X : 𝓤 ̇ ) → ((X → R) → X) → 𝓤 ⊔ 𝓥 ̇ )
        (axiomss : (X : 𝓤 ̇ ) (ε : (X → R) → X) → is-subsingleton (axioms X ε))
       where

 open sip
 open sip-with-axioms

 S : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 S X = (X → R) → X

 SelectionSpace : 𝓤 ⁺ ⊔ 𝓥  ̇
 SelectionSpace = Σ X ꞉ 𝓤 ̇ , Σ ε ꞉ S X , axioms X ε

 sns-data : SNS S (𝓤 ⊔ 𝓥)
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ⊔ 𝓥 ̇
   ι (X , ε) (Y , δ) (f , _) = (λ (q : Y → R) → f (ε (q ∘ f))) ≡ δ

   ρ : (A : Σ S) → ι A A (id-≃ ⟨ A ⟩)
   ρ (X , ε) = refl ε

   θ : {X : 𝓤 ̇ } (ε δ : S X) → is-equiv (canonical-map ι ρ ε δ)
   θ {X} ε δ = γ
    where
     h : canonical-map ι ρ ε δ ∼ 𝑖𝑑 (ε ≡ δ)
     h (refl ε) = refl (refl ε)

     γ : is-equiv (canonical-map ι ρ ε δ)
     γ = equivs-closed-under-∼ (id-is-equiv (ε ≡ δ)) h

 _≅_  :  SelectionSpace → SelectionSpace → 𝓤 ⊔ 𝓥 ̇

 (X , ε , _) ≅ (Y , δ , _) =

             Σ f ꞉ (X → Y), is-equiv f
                          × ((λ (q : Y → R) → f (ε (q ∘ f))) ≡ δ)

 characterization-of-selection-space-≡ : is-univalent 𝓤
                                       → (A B : SelectionSpace)

                                       → (A ≡ B) ≃ (A ≅ B)

 characterization-of-selection-space-≡ ua = characterization-of-≡-with-axioms ua
                                             sns-data
                                             axioms axiomss

module contrived-example (𝓤 : Universe) where

 open sip

 contrived-≡ : is-univalent 𝓤 →

    (X Y : 𝓤 ̇ ) (φ : (X → X) → X) (γ : (Y → Y) → Y)
  →
    ((X , φ) ≡ (Y , γ)) ≃ (Σ f ꞉ (X → Y)
                         , Σ i ꞉ is-equiv f
                         , (λ (g : Y → Y) → f (φ (inverse f i ∘ g ∘ f))) ≡ γ)

 contrived-≡ ua X Y φ γ =
   characterization-of-≡ ua
    ((λ (X , φ) (Y , γ) (f , i) → (λ (g : Y → Y) → f (φ (inverse f i ∘ g ∘ f))) ≡ γ) ,
     (λ (X , φ) → refl φ) ,
     (λ φ γ → equivs-closed-under-∼ (id-is-equiv (φ ≡ γ)) (λ {(refl φ) → refl (refl φ)})))
    (X , φ) (Y , γ)

module generalized-functor-algebra
         {𝓤 𝓥 : Universe}
         (F : 𝓤 ̇ → 𝓥 ̇ )
         (𝓕 : {X Y : 𝓤 ̇ } → (X → Y) → F X → F Y)
         (𝓕-id : {X : 𝓤 ̇ } → 𝓕 (𝑖𝑑 X) ≡ 𝑖𝑑 (F X))
       where

 open sip

 S : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 S X = F X → X

 sns-data : SNS S (𝓤 ⊔ 𝓥)
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ⊔ 𝓥 ̇
   ι (X , α) (Y , β) (f , _) = f ∘ α ≡ β ∘ 𝓕 f

   ρ : (A : Σ S) → ι A A (id-≃ ⟨ A ⟩)
   ρ (X , α) = α        ≡⟨ ap (α ∘_) (𝓕-id ⁻¹) ⟩
               α ∘ 𝓕 id ∎

   θ : {X : 𝓤 ̇ } (α β : S X) → is-equiv (canonical-map ι ρ α β)
   θ {X} α β = γ
    where
     c : α ≡ β → α ≡ β ∘ 𝓕 id
     c = transport (α ≡_) (ρ (X , β))

     i : is-equiv c
     i = transport-is-equiv (α ≡_) (ρ (X , β))

     h : canonical-map ι ρ α β ∼ c
     h (refl _) = ρ (X , α)          ≡⟨ refl-left ⁻¹ ⟩
                  refl α ∙ ρ (X , α) ∎

     γ : is-equiv (canonical-map ι ρ α β)
     γ = equivs-closed-under-∼ i h

 characterization-of-functor-algebra-≡ : is-univalent 𝓤
   → (X Y : 𝓤 ̇ ) (α : F X → X) (β : F Y → Y)

   → ((X , α) ≡ (Y , β))  ≃  (Σ f ꞉ (X → Y), is-equiv f × (f ∘ α ≡ β ∘ 𝓕 f))

 characterization-of-functor-algebra-≡ ua X Y α β =
   characterization-of-≡ ua sns-data (X , α) (Y , β)

type-valued-preorder-S : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ̇
type-valued-preorder-S {𝓤} {𝓥} X = Σ _≤_ ꞉ (X → X → 𝓥 ̇ )
                                         , ((x : X) → x ≤ x)
                                         × ((x y z : X) → x ≤ y → y ≤ z → x ≤ z)

module type-valued-preorder
        (𝓤 𝓥 : Universe)
        (ua : Univalence)
       where

 open sip

 fe : global-dfunext
 fe = univalence-gives-global-dfunext ua

 hfe : global-hfunext
 hfe = univalence-gives-global-hfunext ua

 S : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ̇
 S = type-valued-preorder-S {𝓤} {𝓥}

 Type-valued-preorder : (𝓤 ⊔ 𝓥) ⁺ ̇
 Type-valued-preorder = Σ S

 Ob : Σ S → 𝓤 ̇
 Ob (X , homX , idX , compX ) = X

 hom : (𝓧 : Σ S) → Ob 𝓧 → Ob 𝓧 → 𝓥 ̇
 hom (X , homX , idX , compX) = homX

 𝒾𝒹 : (𝓧 : Σ S) (x : Ob 𝓧) → hom 𝓧 x x
 𝒾𝒹 (X , homX , idX , compX) = idX

 comp : (𝓧 : Σ S) (x y z : Ob 𝓧) → hom 𝓧 x y → hom 𝓧 y z → hom 𝓧 x z
 comp (X , homX , idX , compX) = compX

 functorial : (𝓧 𝓐 : Σ S)
            → (F : Ob 𝓧 → Ob 𝓐)
            → ((x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
            → 𝓤 ⊔ 𝓥 ̇

 functorial 𝓧 𝓐 F 𝓕' = pidentity × pcomposition
  where

   _o_ : {x y z : Ob 𝓧} → hom 𝓧 y z → hom 𝓧 x y → hom 𝓧 x z
   g o f = comp 𝓧 _ _ _ f g

   _□_ : {a b c : Ob 𝓐} → hom 𝓐 b c → hom 𝓐 a b → hom 𝓐 a c
   g □ f = comp 𝓐 _ _ _ f g

   𝓕 : {x y : Ob 𝓧} → hom 𝓧 x y → hom 𝓐 (F x) (F y)
   𝓕 f = 𝓕' _ _ f

   pidentity = (λ x → 𝓕 (𝒾𝒹 𝓧 x)) ≡ (λ x → 𝒾𝒹 𝓐 (F x))

   pcomposition = (λ x y z (f : hom 𝓧 x y) (g : hom 𝓧 y z) → 𝓕 (g o f))
                ≡ (λ x y z (f : hom 𝓧 x y) (g : hom 𝓧 y z) → 𝓕 g □ 𝓕 f)

 sns-data : SNS S (𝓤 ⊔ (𝓥 ⁺))
 sns-data = (ι , ρ , θ)
  where
   ι : (𝓧 𝓐 : Σ S) → ⟨ 𝓧 ⟩ ≃ ⟨ 𝓐 ⟩ → 𝓤 ⊔ (𝓥 ⁺) ̇
   ι 𝓧 𝓐 (F , _) = Σ p ꞉ hom 𝓧 ≡ (λ x y → hom 𝓐 (F x) (F y))
                       , functorial 𝓧 𝓐 F (λ x y → transport (λ - → - x y) p)

   ρ : (𝓧 : Σ S) → ι 𝓧 𝓧 (id-≃ ⟨ 𝓧 ⟩)
   ρ 𝓧 = refl (hom 𝓧) , refl (𝒾𝒹 𝓧) , refl (comp 𝓧)

   θ : {X : 𝓤 ̇ } (s t : S X) → is-equiv (canonical-map ι ρ s t)
   θ {X} (homX , idX , compX) (homA , idA , compA) = g
    where
     φ = canonical-map ι ρ (homX , idX , compX) (homA , idA , compA)

     γ : codomain φ → domain φ
     γ (refl _ , refl _ , refl _) = refl _

     η : γ ∘ φ ∼ id
     η (refl _) = refl _

     ε : φ ∘ γ ∼ id
     ε (refl _ , refl _ , refl _) = refl _

     g : is-equiv φ
     g = invertibles-are-equivs φ (γ , η , ε)

 lemma : (𝓧 𝓐 : Σ S) (F : Ob 𝓧 → Ob 𝓐)
       →
         (Σ p ꞉ hom 𝓧 ≡ (λ x y → hom 𝓐 (F x) (F y))
              , functorial 𝓧 𝓐 F (λ x y → transport (λ - → - x y) p))
       ≃
         (Σ 𝓕 ꞉ ((x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
              , (∀ x y → is-equiv (𝓕 x y))
              × functorial 𝓧 𝓐 F 𝓕)

 lemma 𝓧 𝓐 F = γ
  where
   e = (hom 𝓧 ≡ λ x y → hom 𝓐 (F x) (F y))                            ≃⟨ i ⟩
       (∀ x y → hom 𝓧 x y ≡ hom 𝓐 (F x) (F y))                        ≃⟨ ii ⟩
       (∀ x y → hom 𝓧 x y ≃ hom 𝓐 (F x) (F y))                        ≃⟨ iii ⟩
       (∀ x → Σ φ ꞉ (∀ y → hom 𝓧 x y → hom 𝓐 (F x) (F y))
                  , ∀ y → is-equiv (φ y))                             ≃⟨ iv ⟩
       (Σ 𝓕 ꞉ ((x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
            , (∀ x y → is-equiv (𝓕 x y)))                             ■
    where
     i   = hfunext₂-≃ hfe hfe (hom 𝓧 )  λ x y → hom 𝓐 (F x) (F y)
     ii  = Π-cong fe fe
            (λ x → Π-cong fe fe
            (λ y → univalence-≃ (ua 𝓥) (hom 𝓧 x y) (hom 𝓐 (F x) (F y))))
     iii = Π-cong fe fe (λ y → ΠΣ-distr-≃)
     iv  = ΠΣ-distr-≃

   v : (p : hom 𝓧 ≡ λ x y → hom 𝓐 (F x) (F y))
     → functorial 𝓧 𝓐 F (λ x y → transport (λ - → - x y) p)
     ≃ functorial 𝓧 𝓐 F (pr₁ (⌜ e ⌝ p))

   v (refl _) = id-≃ _

   γ =

    (Σ p ꞉ hom 𝓧 ≡ (λ x y → hom 𝓐 (F x) (F y))
         , functorial 𝓧 𝓐 F (λ x y → transport (λ - → - x y) p)) ≃⟨ vi ⟩

    (Σ p ꞉ hom 𝓧 ≡ (λ x y → hom 𝓐 (F x) (F y))
         , functorial 𝓧 𝓐 F (pr₁ (⌜ e ⌝ p)))                     ≃⟨ vii ⟩

    (Σ σ ꞉ (Σ 𝓕 ꞉ ((x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
                , (∀ x y → is-equiv (𝓕 x y)))
         , functorial 𝓧 𝓐 F (pr₁ σ))                             ≃⟨ viii ⟩

    (Σ 𝓕 ꞉ ((x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
                  , (∀ x y → is-equiv (𝓕 x y))
                  × functorial 𝓧 𝓐 F 𝓕)                          ■
    where
     vi   = Σ-cong v
     vii  = ≃-sym (Σ-change-of-variable _ ⌜ e ⌝ (⌜⌝-is-equiv e))
     viii = Σ-assoc

 characterization-of-type-valued-preorder-≡ :

      (𝓧 𝓐 : Σ S)
    →
      (𝓧 ≡ 𝓐)
    ≃
      (Σ F ꞉ (Ob 𝓧 → Ob 𝓐)
           , is-equiv F
           × (Σ 𝓕 ꞉ ((x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
                  , (∀ x y → is-equiv (𝓕 x y))
                  × functorial 𝓧 𝓐 F 𝓕))

 characterization-of-type-valued-preorder-≡ 𝓧 𝓐 =

   (𝓧 ≡ 𝓐)                                                              ≃⟨ i ⟩
   (Σ F ꞉ (Ob 𝓧 → Ob 𝓐)
        , is-equiv F
        × (Σ p ꞉ hom 𝓧 ≡ (λ x y → hom 𝓐 (F x) (F y))
               , functorial 𝓧 𝓐 F (λ x y → transport (λ - → - x y) p))) ≃⟨ ii ⟩
   (Σ F ꞉ (Ob 𝓧 → Ob 𝓐)
     , is-equiv F
     × (Σ 𝓕 ꞉ ((x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
            , (∀ x y → is-equiv (𝓕 x y))
            × functorial 𝓧 𝓐 F 𝓕))                                      ■

  where
   i  = characterization-of-≡ (ua 𝓤) sns-data 𝓧 𝓐
   ii = Σ-cong (λ F → Σ-cong (λ _ → lemma 𝓧 𝓐 F))

module type-valued-preorder-with-axioms
        (𝓤 𝓥 𝓦 : Universe)
        (ua : Univalence)
        (axioms  : (X : 𝓤 ̇ ) → type-valued-preorder-S {𝓤} {𝓥} X → 𝓦 ̇ )
        (axiomss : (X : 𝓤 ̇ ) (s : type-valued-preorder-S X) → is-subsingleton (axioms X s))
       where

 open sip
 open sip-with-axioms
 open type-valued-preorder 𝓤 𝓥 ua

 S' : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦 ̇
 S' X = Σ s ꞉ S X , axioms X s

 sns-data' : SNS S' (𝓤 ⊔ (𝓥 ⁺))
 sns-data' = add-axioms axioms axiomss sns-data

 characterization-of-type-valued-preorder-≡-with-axioms :

      (𝓧' 𝓐' : Σ S')
    →
      (𝓧' ≡ 𝓐')
    ≃
      (Σ F ꞉ (Ob [ 𝓧' ] → Ob [ 𝓐' ])
           , is-equiv F
           × (Σ 𝓕 ꞉ ((x y : Ob [ 𝓧' ]) → hom [ 𝓧' ] x y → hom [ 𝓐' ] (F x) (F y))
                    , (∀ x y → is-equiv (𝓕 x y))
                    × functorial [ 𝓧' ] [ 𝓐' ] F 𝓕))

 characterization-of-type-valued-preorder-≡-with-axioms 𝓧' 𝓐' =

  (𝓧' ≡ 𝓐')                     ≃⟨ i ⟩
  ([ 𝓧' ] ≃[ sns-data ] [ 𝓐' ]) ≃⟨ ii ⟩
  _                              ■

  where
   i  = characterization-of-≡-with-axioms (ua 𝓤) sns-data axioms axiomss 𝓧' 𝓐'
   ii = Σ-cong (λ F → Σ-cong (λ _ → lemma [ 𝓧' ] [ 𝓐' ] F))

module category
        (𝓤 𝓥 : Universe)
        (ua : Univalence)
       where

 open type-valued-preorder-with-axioms 𝓤 𝓥 (𝓤 ⊔ 𝓥) ua

 fe : global-dfunext
 fe = univalence-gives-global-dfunext ua

 S : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ̇
 S = type-valued-preorder-S {𝓤} {𝓥}

 category-axioms : (X : 𝓤 ̇ ) → S X → 𝓤 ⊔ 𝓥 ̇
 category-axioms X (homX , idX , compX) = hom-sets × identityl × identityr × associativity
  where
   _o_ : {x y z : X} → homX y z → homX x y → homX x z
   g o f = compX _ _ _ f g

   hom-sets      = ∀ x y → is-set (homX x y)

   identityl     = ∀ x y (f : homX x y) → f o (idX x) ≡ f

   identityr     = ∀ x y (f : homX x y) → (idX y) o f ≡ f

   associativity = ∀ x y z t (f : homX x y) (g : homX y z) (h : homX z t)
                 → (h o g) o f ≡ h o (g o f)

 category-axioms-subsingleton : (X : 𝓤 ̇ ) (s : S X) → is-subsingleton (category-axioms X s)
 category-axioms-subsingleton X (homX , idX , compX) ca = γ ca
  where
   i : ∀ x y → is-set (homX x y)
   i = pr₁ ca

   γ : is-subsingleton (category-axioms X (homX , idX , compX))
   γ = ×-is-subsingleton ss (×-is-subsingleton ls (×-is-subsingleton rs as))
    where
     ss = Π-is-subsingleton fe
           (λ x → Π-is-subsingleton fe
           (λ y → being-set-is-subsingleton fe))

     ls = Π-is-subsingleton fe
           (λ x → Π-is-subsingleton fe
           (λ y → Π-is-subsingleton fe
           (λ f → i x y (compX x x y (idX x) f) f)))

     rs = Π-is-subsingleton fe
           (λ x → Π-is-subsingleton fe
           (λ y → Π-is-subsingleton fe
           (λ f → i x y (compX x y y f (idX y)) f)))

     as = Π-is-subsingleton fe
           (λ x → Π-is-subsingleton fe
           (λ y → Π-is-subsingleton fe
           (λ z → Π-is-subsingleton fe
           (λ t → Π-is-subsingleton fe
           (λ f → Π-is-subsingleton fe
           (λ g → Π-is-subsingleton fe
           (λ h → i x t (compX x y t f (compX y z t g h))
                        (compX x z t (compX x y z f g) h))))))))

 Cat : (𝓤 ⊔ 𝓥)⁺ ̇
 Cat = Σ X ꞉ 𝓤 ̇ , Σ s ꞉ S X , category-axioms X s

 Ob : Cat → 𝓤 ̇
 Ob (X , (homX , idX , compX) , _) = X

 hom : (𝓧 : Cat) → Ob 𝓧 → Ob 𝓧 → 𝓥 ̇
 hom (X , (homX , idX , compX) , _) = homX

 𝒾𝒹 : (𝓧 : Cat) (x : Ob 𝓧) → hom 𝓧 x x
 𝒾𝒹 (X , (homX , idX , compX) , _) = idX

 comp : (𝓧 : Cat) (x y z : Ob 𝓧) (f : hom 𝓧 x y) (g : hom 𝓧 y z) → hom 𝓧 x z
 comp (X , (homX , idX , compX) , _) = compX

 is-functorial : (𝓧 𝓐 : Cat)
               → (F : Ob 𝓧 → Ob 𝓐)
               → ((x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
               → 𝓤 ⊔ 𝓥 ̇

 is-functorial 𝓧 𝓐 F 𝓕' = pidentity × pcomposition
  where
   _o_ : {x y z : Ob 𝓧} → hom 𝓧 y z → hom 𝓧 x y → hom 𝓧 x z
   g o f = comp 𝓧 _ _ _ f g

   _□_ : {a b c : Ob 𝓐} → hom 𝓐 b c → hom 𝓐 a b → hom 𝓐 a c
   g □ f = comp 𝓐 _ _ _ f g

   𝓕 : {x y : Ob 𝓧} → hom 𝓧 x y → hom 𝓐 (F x) (F y)
   𝓕 f = 𝓕' _ _ f

   pidentity    = (λ x → 𝓕 (𝒾𝒹 𝓧 x)) ≡ (λ x → 𝒾𝒹 𝓐 (F x))

   pcomposition = (λ x y z (f : hom 𝓧 x y) (g : hom 𝓧 y z) → 𝓕 (g o f))
                ≡ (λ x y z (f : hom 𝓧 x y) (g : hom 𝓧 y z) → 𝓕 g □ 𝓕 f)

 _⋍_ : Cat → Cat → 𝓤 ⊔ 𝓥 ̇

 𝓧 ⋍ 𝓐 = Σ F ꞉ (Ob 𝓧 → Ob 𝓐)
              , is-equiv F
              × (Σ 𝓕 ꞉ ((x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
                     , (∀ x y → is-equiv (𝓕 x y))
                     × is-functorial 𝓧 𝓐 F 𝓕)

 Id→EqCat : (𝓧 𝓐 : Cat) → 𝓧 ≡ 𝓐 → 𝓧 ⋍ 𝓐
 Id→EqCat 𝓧 𝓧 (refl 𝓧) = 𝑖𝑑 (Ob 𝓧 ) ,
                         id-is-equiv (Ob 𝓧 ) ,
                         (λ x y → 𝑖𝑑 (hom 𝓧 x y)) ,
                         (λ x y → id-is-equiv (hom 𝓧 x y)) ,
                         refl (𝒾𝒹 𝓧) ,
                         refl (comp 𝓧)

 characterization-of-category-≡ : (𝓧 𝓐 : Cat) → (𝓧 ≡ 𝓐) ≃ (𝓧 ⋍ 𝓐)
 characterization-of-category-≡ = characterization-of-type-valued-preorder-≡-with-axioms
                                   category-axioms category-axioms-subsingleton

 Id→EqCat-is-equiv : (𝓧 𝓐 : Cat) → is-equiv (Id→EqCat 𝓧 𝓐)
 Id→EqCat-is-equiv 𝓧 𝓐 = equivs-closed-under-∼
                           (⌜⌝-is-equiv (characterization-of-category-≡ 𝓧 𝓐))
                           (γ 𝓧 𝓐)
  where
   γ : (𝓧 𝓐 : Cat) → Id→EqCat 𝓧 𝓐 ∼ ⌜ characterization-of-category-≡ 𝓧 𝓐 ⌝
   γ 𝓧 𝓧 (refl 𝓧) = refl _

module ring {𝓤 : Universe} (ua : Univalence) where
 open sip hiding (⟨_⟩)
 open sip-with-axioms
 open sip-join

 fe : global-dfunext
 fe = univalence-gives-global-dfunext ua

 hfe : global-hfunext
 hfe = univalence-gives-global-hfunext ua

 rng-structure : 𝓤 ̇ → 𝓤 ̇
 rng-structure X = (X → X → X) × (X → X → X)

 rng-axioms : (R : 𝓤 ̇ ) → rng-structure R → 𝓤 ̇
 rng-axioms R (_+_ , _·_) = I × II × III × IV × V × VI × VII
  where
    I   = is-set R
    II  = (x y z : R) → (x + y) + z ≡ x + (y + z)
    III = (x y : R) → x + y ≡ y + x
    IV  = Σ O ꞉ R , ((x : R) → x + O ≡ x) × ((x : R) → Σ x' ꞉ R , x + x' ≡ O)
    V   = (x y z : R) → (x · y) · z ≡ x · (y · z)
    VI  = (x y z : R) → x · (y + z) ≡ (x · y) + (x · z)
    VII = (x y z : R) → (y + z) · x ≡ (y · x) + (z · x)

 Rng : 𝓤 ⁺ ̇
 Rng = Σ R ꞉ 𝓤 ̇ , Σ s ꞉ rng-structure R , rng-axioms R s

 rng-axioms-is-subsingleton : (R : 𝓤 ̇ ) (s : rng-structure R)
                            → is-subsingleton (rng-axioms R s)

 rng-axioms-is-subsingleton R (_+_ , _·_) (i , ii , iii , iv-vii) = δ
  where
    A   = λ (O : R) → ((x : R) → x + O ≡ x)
                    × ((x : R) → Σ x' ꞉ R , x + x' ≡ O)

    IV  = Σ A

    a : (O O' : R) → ((x : R) → x + O ≡ x) → ((x : R) → x + O' ≡ x) → O ≡ O'
    a O O' f f' = O       ≡⟨ (f' O)⁻¹ ⟩
                 (O + O') ≡⟨ iii O O' ⟩
                 (O' + O) ≡⟨ f O' ⟩
                  O'      ∎

    b : (O : R) → is-subsingleton ((x : R) → x + O ≡ x)
    b O = Π-is-subsingleton fe (λ x → i (x + O) x)

    c : (O : R)
      → ((x : R) → x + O ≡ x)
      → (x : R) → is-subsingleton (Σ x' ꞉ R , x + x' ≡ O)
    c O f x (x' , p') (x'' , p'') = to-subtype-≡ (λ x' → i (x + x') O) r
     where
      r : x' ≡ x''
      r = x'               ≡⟨ (f x')⁻¹ ⟩
          (x' + O)         ≡⟨ ap (x' +_) (p'' ⁻¹) ⟩
          (x' + (x + x'')) ≡⟨ (ii x' x x'')⁻¹ ⟩
          ((x' + x) + x'') ≡⟨ ap (_+ x'') (iii x' x) ⟩
          ((x + x') + x'') ≡⟨ ap (_+ x'') p' ⟩
          (O + x'')        ≡⟨ iii O x'' ⟩
          (x'' + O)        ≡⟨ f x'' ⟩
          x''              ∎

    d : (O : R) → is-subsingleton (A O)
    d O (f , g) = φ (f , g)
     where
      φ : is-subsingleton (A O)
      φ = ×-is-subsingleton (b O) (Π-is-subsingleton fe (λ x → c O f x))

    IV-is-subsingleton : is-subsingleton IV
    IV-is-subsingleton (O , f , g) (O' , f' , g') = e
     where
      e : (O , f , g) ≡ (O' , f' , g')
      e = to-subtype-≡ d (a O O' f f')

    γ : is-subsingleton (rng-axioms R (_+_ , _·_))
    γ = ×-is-subsingleton
          (being-set-is-subsingleton fe)
       (×-is-subsingleton
          (Π-is-subsingleton fe
          (λ x → Π-is-subsingleton fe
          (λ y → Π-is-subsingleton fe
          (λ z → i ((x + y) + z) (x + (y + z))))))
       (×-is-subsingleton
          (Π-is-subsingleton fe
          (λ x → Π-is-subsingleton fe
          (λ y → i (x + y) (y + x))))
       (×-is-subsingleton
          IV-is-subsingleton
       (×-is-subsingleton
          (Π-is-subsingleton fe
          (λ x → Π-is-subsingleton fe
          (λ y → Π-is-subsingleton fe
          (λ z → i ((x · y) · z) (x · (y · z))))))
       (×-is-subsingleton
          (Π-is-subsingleton fe
          (λ x → Π-is-subsingleton fe
          (λ y → Π-is-subsingleton fe
          (λ z → i (x · (y + z)) ((x · y) + (x · z))))))

          (Π-is-subsingleton fe
          (λ x → Π-is-subsingleton fe
          (λ y → Π-is-subsingleton fe
          (λ z → i ((y + z) · x) ((y · x) + (z · x)))))))))))

    δ : (α : rng-axioms R (_+_ , _·_)) → (i , ii , iii , iv-vii) ≡ α
    δ = γ (i , ii , iii , iv-vii)

 _≅[Rng]_ : Rng → Rng → 𝓤 ̇

 (R , (_+_ , _·_) , _) ≅[Rng] (R' , (_+'_ , _·'_) , _) =

                       Σ f ꞉ (R → R')
                           , is-equiv f
                           × ((λ x y → f (x + y)) ≡ (λ x y → f x +' f y))
                           × ((λ x y → f (x · y)) ≡ (λ x y → f x ·' f y))

 characterization-of-rng-≡ : (𝓡 𝓡' : Rng) → (𝓡 ≡ 𝓡') ≃ (𝓡 ≅[Rng] 𝓡')
 characterization-of-rng-≡ = characterization-of-≡ (ua 𝓤)
                              (add-axioms
                                rng-axioms
                                rng-axioms-is-subsingleton
                                (join
                                  ∞-magma.sns-data
                                  ∞-magma.sns-data))

 ⟨_⟩ : (𝓡 : Rng) → 𝓤 ̇
 ⟨ R , _ ⟩ = R

 ring-structure : 𝓤 ̇ → 𝓤 ̇
 ring-structure X = X × rng-structure X

 ring-axioms : (R : 𝓤 ̇ ) → ring-structure R → 𝓤 ̇
 ring-axioms R (𝟏 , _+_ , _·_) = rng-axioms R (_+_ , _·_) × VIII
  where
   VIII = (x : R) → (x · 𝟏 ≡ x) × (𝟏 · x ≡ x)

 ring-axioms-is-subsingleton : (R : 𝓤 ̇ ) (s : ring-structure R)
                             → is-subsingleton (ring-axioms R s)

 ring-axioms-is-subsingleton R (𝟏 , _+_ , _·_) ((i , ii-vii) , viii) = γ ((i , ii-vii) , viii)
  where
   γ : is-subsingleton (ring-axioms R (𝟏 , _+_ , _·_))
   γ = ×-is-subsingleton
         (rng-axioms-is-subsingleton R (_+_ , _·_))
         (Π-is-subsingleton fe (λ x → ×-is-subsingleton (i (x · 𝟏) x) (i (𝟏 · x) x)))

 Ring : 𝓤 ⁺ ̇
 Ring = Σ R ꞉ 𝓤 ̇ , Σ s ꞉ ring-structure R , ring-axioms R s

 _≅[Ring]_ : Ring → Ring → 𝓤 ̇

 (R , (𝟏 , _+_ , _·_) , _) ≅[Ring] (R' , (𝟏' , _+'_ , _·'_) , _) =

                           Σ f ꞉ (R → R')
                               , is-equiv f
                               × (f 𝟏 ≡ 𝟏')
                               × ((λ x y → f (x + y)) ≡ (λ x y → f x +' f y))
                               × ((λ x y → f (x · y)) ≡ (λ x y → f x ·' f y))

 characterization-of-ring-≡ : (𝓡 𝓡' : Ring) → (𝓡 ≡ 𝓡') ≃ (𝓡 ≅[Ring] 𝓡')
 characterization-of-ring-≡ = sip.characterization-of-≡ (ua 𝓤)
                                (sip-with-axioms.add-axioms
                                  ring-axioms
                                  ring-axioms-is-subsingleton
                                  (sip-join.join
                                    pointed-type.sns-data
                                      (join
                                        ∞-magma.sns-data
                                        ∞-magma.sns-data)))

 is-commutative : Rng → 𝓤 ̇
 is-commutative (R , (_+_ , _·_) , _) = (x y : R) → x · y ≡ y · x

 being-commutative-is-subsingleton : (𝓡 : Rng) → is-subsingleton (is-commutative 𝓡)
 being-commutative-is-subsingleton (R , (_+_ , _·_) , i , ii-vii) =

   Π-is-subsingleton fe
   (λ x → Π-is-subsingleton fe
   (λ y → i (x · y) (y · x)))

 is-ideal : (𝓡 : Rng) → 𝓟 ⟨ 𝓡 ⟩ → 𝓤 ̇
 is-ideal (R , (_+_ , _·_) , _) I = (x y : R) → (x ∈ I → y ∈ I → (x + y) ∈ I)
                                              × (x ∈ I → (x · y) ∈ I)
                                              × (y ∈ I → (x · y) ∈ I)

 is-local : Rng → 𝓤 ⁺ ̇
 is-local 𝓡 = ∃! I ꞉ 𝓟 ⟨ 𝓡 ⟩ , (is-ideal 𝓡 I → (J : 𝓟 ⟨ 𝓡 ⟩) → is-ideal 𝓡 J → J ⊆ I)

 being-local-is-subsingleton : (𝓡 : Rng) → is-subsingleton (is-local 𝓡)
 being-local-is-subsingleton 𝓡 = ∃!-is-subsingleton _ fe

 module _ (pt : subsingleton-truncations-exist) where

  open basic-truncation-development pt hfe
  open ℕ-order

  is-noetherian : (𝓡 : Rng) → 𝓤 ⁺ ̇
  is-noetherian 𝓡 = (I : ℕ → 𝓟 ⟨ 𝓡 ⟩)
                  → ((n : ℕ) → is-ideal 𝓡 (I n))
                  → ((n : ℕ) → I n ⊆ I (succ n))
                  → ∃ m ꞉ ℕ , ((n : ℕ) → m ≤ n → I m ≡ I n)

  NoetherianRng : 𝓤 ⁺ ̇
  NoetherianRng = Σ 𝓡 ꞉ Rng , is-noetherian 𝓡

  being-noetherian-is-subsingleton : (𝓡 : Rng) → is-subsingleton (is-noetherian 𝓡)

  being-noetherian-is-subsingleton 𝓡 = Π-is-subsingleton fe
                                       (λ I → Π-is-subsingleton fe
                                       (λ _ → Π-is-subsingleton fe
                                       (λ _ → ∃-is-subsingleton)))

  forget-Noether : NoetherianRng → Rng
  forget-Noether (𝓡 , _) = 𝓡

  forget-Noether-is-embedding : is-embedding forget-Noether
  forget-Noether-is-embedding = pr₁-embedding being-noetherian-is-subsingleton

  _≅[NoetherianRng]_ : NoetherianRng → NoetherianRng → 𝓤 ̇

  ((R , (_+_ , _·_) , _) , _) ≅[NoetherianRng] ((R' , (_+'_ , _·'_) , _) , _) =

                              Σ f ꞉ (R → R')
                                  , is-equiv f
                                  × ((λ x y → f (x + y)) ≡ (λ x y → f x +' f y))
                                  × ((λ x y → f (x · y)) ≡ (λ x y → f x ·' f y))

  NB : (𝓡 𝓡' : NoetherianRng)
     → (𝓡 ≅[NoetherianRng] 𝓡') ≡ (forget-Noether 𝓡 ≅[Rng] forget-Noether 𝓡')

  NB 𝓡 𝓡' = refl _

  characterization-of-nrng-≡ : (𝓡 𝓡' : NoetherianRng)
                             → (𝓡 ≡ 𝓡') ≃ (𝓡 ≅[NoetherianRng] 𝓡')

  characterization-of-nrng-≡ 𝓡 𝓡' =

    (𝓡 ≡ 𝓡')                               ≃⟨ i ⟩
    (forget-Noether 𝓡 ≡ forget-Noether 𝓡') ≃⟨ ii ⟩
    (𝓡 ≅[NoetherianRng] 𝓡')                ■

    where
     i = ≃-sym (embedding-criterion-converse forget-Noether
                  forget-Noether-is-embedding 𝓡 𝓡')
     ii = characterization-of-rng-≡ (forget-Noether 𝓡) (forget-Noether 𝓡')

  isomorphic-NoetherianRng-transport :

      (A : NoetherianRng → 𝓥 ̇ )
    → (𝓡 𝓡' : NoetherianRng) → 𝓡 ≅[NoetherianRng] 𝓡' → A 𝓡 → A 𝓡'

  isomorphic-NoetherianRng-transport A 𝓡 𝓡' i a = a'
   where
    p : 𝓡 ≡ 𝓡'
    p = ⌜ ≃-sym (characterization-of-nrng-≡ 𝓡 𝓡') ⌝ i

    a' : A 𝓡'
    a' = transport A p a

  is-CNL : Ring → 𝓤 ⁺ ̇
  is-CNL (R , (𝟏 , _+_ , _·_) , i-vii , viii) = is-commutative 𝓡
                                              × is-noetherian 𝓡
                                              × is-local 𝓡
   where
    𝓡 : Rng
    𝓡 = (R , (_+_ , _·_) , i-vii)

  being-CNL-is-subsingleton : (𝓡 : Ring) → is-subsingleton (is-CNL 𝓡)
  being-CNL-is-subsingleton (R , (𝟏 , _+_ , _·_) , i-vii , viii) =

     ×-is-subsingleton (being-commutative-is-subsingleton 𝓡)
    (×-is-subsingleton (being-noetherian-is-subsingleton 𝓡)
                       (being-local-is-subsingleton 𝓡))
   where
    𝓡 : Rng
    𝓡 = (R , (_+_ , _·_) , i-vii)

  CNL-Ring : 𝓤 ⁺ ̇
  CNL-Ring = Σ 𝓡 ꞉ Ring , is-CNL 𝓡

  _≅[CNL]_ : CNL-Ring → CNL-Ring → 𝓤 ̇

  ((R , (𝟏 , _+_ , _·_) , _) , _) ≅[CNL] ((R' , (𝟏' , _+'_ , _·'_) , _) , _) =

                                  Σ f ꞉ (R → R')
                                      , is-equiv f
                                      × (f 𝟏 ≡ 𝟏')
                                      × ((λ x y → f (x + y)) ≡ (λ x y → f x +' f y))
                                      × ((λ x y → f (x · y)) ≡ (λ x y → f x ·' f y))

  forget-CNL : CNL-Ring → Ring
  forget-CNL (𝓡 , _) = 𝓡

  forget-CNL-is-embedding : is-embedding forget-CNL
  forget-CNL-is-embedding = pr₁-embedding being-CNL-is-subsingleton

  NB' : (𝓡 𝓡' : CNL-Ring)
      → (𝓡 ≅[CNL] 𝓡') ≡ (forget-CNL 𝓡 ≅[Ring] forget-CNL 𝓡')

  NB' 𝓡 𝓡' = refl _

  characterization-of-CNL-ring-≡ : (𝓡 𝓡' : CNL-Ring)
                                 → (𝓡 ≡ 𝓡') ≃ (𝓡 ≅[CNL] 𝓡')

  characterization-of-CNL-ring-≡ 𝓡 𝓡' =

     (𝓡 ≡ 𝓡')                               ≃⟨ i ⟩
     (forget-CNL 𝓡 ≡ forget-CNL 𝓡')         ≃⟨ ii ⟩
     (𝓡 ≅[CNL] 𝓡')                          ■

     where
      i = ≃-sym (embedding-criterion-converse forget-CNL
                   forget-CNL-is-embedding 𝓡 𝓡')
      ii = characterization-of-ring-≡ (forget-CNL 𝓡) (forget-CNL 𝓡')

  isomorphic-CNL-Ring-transport :

      (A : CNL-Ring → 𝓥 ̇ )
    → (𝓡 𝓡' : CNL-Ring) → 𝓡 ≅[CNL] 𝓡' → A 𝓡 → A 𝓡'

  isomorphic-CNL-Ring-transport A 𝓡 𝓡' i a = a'
   where
    p : 𝓡 ≡ 𝓡'
    p = ⌜ ≃-sym (characterization-of-CNL-ring-≡ 𝓡 𝓡') ⌝ i

    a' : A 𝓡'
    a' = transport A p a

\end{code}
