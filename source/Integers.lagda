Tom de Jong, 18 September 2020
22 January 2021 reboot

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base

open import UF-Embeddings
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-FunExt
open import UF-Lower-FunExt
open import UF-Subsingletons
open import UF-Retracts

module Integers where

-- The following two lemmas are dependent adaptations from
-- https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#ℕ-is-nno
-- We should move them to some file on ℕ.
ℕ-induction-retract : funext 𝓤₀ 𝓤
                    → (Y : ℕ → 𝓤 ̇ ) (y₀ : Y 0) (g : (n : ℕ) → Y n → Y (succ n))
                    → (Σ h ꞉ (Π Y) , (h 0 ≡ y₀) ×
                                     ((n : ℕ) → h (succ n) ≡ g n (h n)))
                    ◁ (Σ h ꞉ (Π Y) , h ≡ induction y₀ g)
ℕ-induction-retract fe Y y₀ g = Σ-retract _ _ γ
 where
  γ : (h : Π Y)
    → (h 0 ≡ y₀) × ((n : ℕ) → h (succ n) ≡ g n (h n))
    ◁ (h ≡ induction y₀ g)
  γ h =  (h 0 ≡ y₀) × ((n : ℕ) → h (succ n) ≡ g n (h n)) ◁⟨ i  ⟩
         (h ∼ induction y₀ g)                            ◁⟨ ii ⟩
         (h ≡ induction y₀ g)                            ◀
   where
    ii = ≃-gives-◁ (≃-sym (≃-funext fe h (induction y₀ g)))
    i  = r , s , η
     where
      r : h ∼ induction y₀ g
        → (h 0 ≡ y₀) × ((n : ℕ) → h (succ n) ≡ g n (h n))
      r H = H 0 , (λ n → h (succ n)              ≡⟨ H (succ n)          ⟩
                         induction y₀ g (succ n) ≡⟨ refl                ⟩
                         g n (induction y₀ g n)  ≡⟨ ap (g n) ((H n) ⁻¹) ⟩
                         g n (h n)               ∎)
      s : (h 0 ≡ y₀) × ((n : ℕ) → h (succ n) ≡ g n (h n))
        → h ∼ induction y₀ g
      s (p , K) 0 = p
      s (p , K) (succ n) = h (succ n)              ≡⟨ K n                    ⟩
                           g n (h n)               ≡⟨ ap (g n) (s (p , K) n) ⟩
                           g n (induction y₀ g n)  ≡⟨ refl                   ⟩
                           induction y₀ g (succ n) ∎
      η : r ∘ s ∼ id
      η (p , K) =
       r (s (p , K))                                      ≡⟨ refl ⟩
       (p , λ n → s (p , K) (succ n)
                  ∙ (refl ∙ ap (g n) ((s (p , K) n) ⁻¹))) ≡⟨ φ    ⟩
       (p , K)                                            ∎
         where
          φ = ap (p ,_) (dfunext fe ψ)
           where
            ψ : (n : ℕ)
              → s (p , K) (succ n) ∙ (refl ∙ ap (g n) (s (p , K) n ⁻¹))
              ≡ K n
            ψ n = s (p , K) (succ n)
                    ∙ (refl ∙ ap (g n) (s (p , K) n ⁻¹))   ≡⟨ refl ⟩
                  K n ∙ ap (g n) (s (p , K) n)
                    ∙ (refl ∙ ap (g n) ((s (p , K) n) ⁻¹)) ≡⟨ I    ⟩
                  K n ∙ ap (g n) (s (p , K) n)
                    ∙ ap (g n) ((s (p , K) n) ⁻¹)          ≡⟨ II   ⟩
                  K n ∙ (ap (g n) (s (p , K) n)
                    ∙ ap (g n) ((s (p , K) n) ⁻¹))         ≡⟨ III  ⟩
                  K n ∙ (ap (g n) (s (p , K) n)
                    ∙ (ap (g n) (s (p , K) n)) ⁻¹)         ≡⟨ IV   ⟩
                  K n ∙ refl                               ≡⟨ refl ⟩
                  K n                                      ∎
             where
              I   = ap (K n ∙ ap (g n) (s (p , K) n) ∙_)
                     (refl-left-neutral {_} {_} {_} {_}
                       {ap (g n) ((s (p , K) n) ⁻¹)})
              II  = ∙assoc
                     (K n)
                     (ap (g n) (s (p , K) n))
                     (ap (g n) ((s (p , K) n) ⁻¹))
              III = ap (λ - → K n ∙ (ap (g n) (s (p , K) n) ∙ -))
                     ((ap-sym (g n) (s (p , K) n)) ⁻¹)
              IV  = ap (K n ∙_)
                     ((right-inverse (ap (g n) (s (p , K) n))) ⁻¹)

ℕ-is-nno-dep : funext 𝓤₀ 𝓤
             → (Y : ℕ → 𝓤 ̇ ) (y₀ : Y 0) (g : (n : ℕ) → Y n → Y (succ n))
             → ∃! h ꞉ (Π Y) , ((h 0 ≡ y₀) × ((n : ℕ) → h (succ n) ≡ g n (h n)))
ℕ-is-nno-dep {𝓤} fe Y y₀ g = γ
 where
  γ : is-singleton
       (Σ h ꞉ (Π Y) , (h 0 ≡ y₀) × ((n : ℕ) → h (succ n) ≡ g n (h n)))
  γ = retract-of-singleton (ℕ-induction-retract fe Y y₀ g)
       (singleton-types'-are-singletons (induction {𝓤} {Y} y₀ g))

-- We don't have a use of this (yet)
{-
exercise : funext 𝓤₀ 𝓤
         → (Y : ℕ → 𝓤 ̇ ) (g : (n : ℕ) → Y n → Y (succ n))
         → (Σ h ꞉ (Π Y) , ((n : ℕ) → h (succ n) ≡ g n (h n)))
         ≃ Y 0
exercise fe Y g = qinveq π₀ (r , ε , η)
 where
  π₀ : (Σ h ꞉ (Π Y) , ((n : ℕ) → h (succ n) ≡ g n (h n))) → Y 0
  π₀ (h , p) = h 0
  r : Y 0
    → (Σ h ꞉ (Π Y) , ((n : ℕ) → h (succ n) ≡ g n (h n)))
  r y₀ = h , (λ n → refl)
   where
    h : Π Y
    h zero = y₀
    h (succ n) = g n (h n)
  ε : r ∘ π₀ ∼ id
  ε (h , p) = ap u e
   where
    h' : Π Y
    h' = pr₁ (r (π₀ (h , p)))
    p' : (n : ℕ)
       → h' (succ n) ≡ g n (h' n)
    p' = pr₂ (r (π₀ (h , p)))
    s : Σ f ꞉ (Π Y) , ((f 0 ≡ h 0) × ((n : ℕ) → f (succ n) ≡ g n (f n)))
    s = h' , refl , p'
    t : Σ f ꞉ (Π Y) , ((f 0 ≡ h 0) × ((n : ℕ) → f (succ n) ≡ g n (f n)))
    t = h , refl , p
    e : s ≡ t
    e = singletons-are-props (ℕ-is-nno-dep fe Y (h 0) g) s t
    u : (Σ f ꞉ (Π Y) , ((f 0 ≡ h 0) × ((n : ℕ) → f (succ n) ≡ g n (f n))))
      → (Σ f ꞉ (Π Y) , ((n : ℕ) → f (succ n) ≡ g n (f n)))
    u (f , _ , q) = f , q
  η : π₀ ∘ r ∼ id
  η y₀ = refl
-}

ℤ : 𝓤₀ ̇
ℤ = 𝟙 + ℕ + ℕ

pattern 𝟎 = inl *
pattern pos i = inr (inl i)
pattern neg i = inr (inr i)

ℕ-to-ℤ₊ : ℕ → ℤ
ℕ-to-ℤ₊ 0        = 𝟎
ℕ-to-ℤ₊ (succ n) = pos n

ℕ-to-ℤ₋ : ℕ → ℤ
ℕ-to-ℤ₋ 0        = 𝟎
ℕ-to-ℤ₋ (succ n) = neg n

ℤ-induction : {𝓤 : Universe} (P : ℤ → 𝓤 ̇ )
            → P 𝟎
            → ((n : ℕ) → P (ℕ-to-ℤ₊ n) → P (ℕ-to-ℤ₊ (succ n)))
            → ((n : ℕ) → P (ℕ-to-ℤ₋ n) → P (ℕ-to-ℤ₋ (succ n)))
            → (z : ℤ) → P z
ℤ-induction {𝓤} P p₀ p₊ p₋ 𝟎       = p₀
ℤ-induction {𝓤} P p₀ p₊ p₋ (pos i) = h (succ i)
 where
  P₊ : ℕ → 𝓤 ̇
  P₊ = P ∘ ℕ-to-ℤ₊
  h : (n : ℕ) → P₊ n
  h = induction p₀ p₊
ℤ-induction {𝓤} P p₀ p₊ p₋ (neg i) = h (succ i)
 where
  P₋ : ℕ → 𝓤 ̇
  P₋ = P ∘ ℕ-to-ℤ₋
  h : (n : ℕ) → P₋ n
  h = induction p₀ p₋

succ-ℤ : ℤ → ℤ
succ-ℤ 𝟎              = pos 0
succ-ℤ (pos n)        = pos (succ n)
succ-ℤ (neg 0)        = 𝟎
succ-ℤ (neg (succ n)) = neg n

-- Theorem 3.13 of "Construction of the Circle in UniMath"
-- by Bezem, Buchholtz, Grayson and Shulman
-- https://arxiv.org/abs/1910.01856
ℤ-symmetric-induction : {𝓤 : Universe}
                      → funext 𝓤₀ 𝓤
                      → (A : ℤ → 𝓤 ̇ )
                        (f : (z : ℤ) → A z ≃ A (succ-ℤ z))
                      → (Σ h ꞉ Π A , ((z : ℤ) → h (succ-ℤ z) ≡ ⌜ f z ⌝ (h z)))
                      ≃ A 𝟎
ℤ-symmetric-induction {𝓤} fe A f =
 (Σ h ꞉ Π A , Q₁ h)                                               ≃⟨ I    ⟩
 (Σ h ꞉ (Π (A ∘ ⌜𝟎⌝) × Π (A ∘ inr)) , Q₁ (g₁ h))                  ≃⟨ II   ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , Σ hᵣ ꞉ Π (A ∘ inr) , Q₁ (g₁ (hₒ , hᵣ)))    ≃⟨ III  ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , Σ hᵣ ꞉ (Π (A ∘ pos) × Π (A ∘ neg)),
                         Q₂ hₒ (g₂ hᵣ))                           ≃⟨ IV   ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , Σ hₚ ꞉ Π (A ∘ pos) ,
                       Σ hₙ ꞉ Π (A ∘ neg) , Q₂ hₒ (g₂ (hₚ , hₙ))) ≃⟨ V    ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , Σ hₚ ꞉ Π (A ∘ pos) ,
                       Σ hₙ ꞉ Π (A ∘ neg) , Qₚ (hₒ *) hₚ
                                          × Qₙ' (hₒ *) hₙ)        ≃⟨ VI   ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , ((Σ hₚ ꞉ Π (A ∘ pos) , Qₚ (hₒ *) hₚ)
                     ×  (Σ hₙ ꞉ Π (A ∘ neg) , Qₙ' (hₒ *) hₙ)))    ≃⟨ VII  ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , 𝟙 × (Σ hₙ ꞉ Π (A ∘ neg) , Qₙ' (hₒ *) hₙ))  ≃⟨ VIII ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , Σ hₙ ꞉ Π (A ∘ neg) , Qₙ' (hₒ *) hₙ)        ≃⟨ IX   ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , Σ hₙ ꞉ Π (A ∘ neg) , Qₙ (hₒ *) hₙ)         ≃⟨ X    ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , 𝟙)                                         ≃⟨ XI   ⟩
 Π (A ∘ ⌜𝟎⌝)                                                      ≃⟨ XII  ⟩
 A 𝟎 ■
  where
   ⌜𝟎⌝ : 𝟙 {𝓤₀} → ℤ
   ⌜𝟎⌝ _ = 𝟎
   Q₁ : Π A → 𝓤 ̇
   Q₁ h = (z : ℤ) → h (succ-ℤ z) ≡ ⌜ f z ⌝ (h z)
   g₁ : Π (A ∘ ⌜𝟎⌝) × Π (A ∘ inr) → Π A
   g₁ = ⌜ Π×+ fe ⌝
   Q₂ : Π (A ∘ ⌜𝟎⌝) → Π (A ∘ inr) → 𝓤 ̇
   Q₂ hₒ hᵣ = Q₁ (g₁ (hₒ , hᵣ))
   g₂ : Π (A ∘ pos) × Π (A ∘ neg) → Π (A ∘ inr)
   g₂ = ⌜ Π×+ fe ⌝
   Qₚ : A 𝟎 → Π (A ∘ pos) → 𝓤 ̇
   Qₚ aₒ hₚ = (hₚ 0 ≡ ⌜ f 𝟎 ⌝ aₒ)
            × ((n : ℕ) → hₚ (succ n) ≡ ⌜ f (pos n) ⌝ (hₚ n))
   Qₙ' : A 𝟎 → Π (A ∘ neg) → 𝓤 ̇
   Qₙ' a₀ hₙ = (a₀ ≡ ⌜ f (neg 0) ⌝ (hₙ 0))
             × ((n : ℕ) → hₙ n ≡ ⌜ f (neg (succ n)) ⌝ (hₙ (succ n)))
   Qₙ : A 𝟎 → Π (A ∘ neg) → 𝓤 ̇
   Qₙ aₒ hₙ = (hₙ 0 ≡ ⌜ ≃-sym (f (neg 0)) ⌝ aₒ)
            × ((n : ℕ) → hₙ (succ n) ≡ ⌜ ≃-sym (f (neg (succ n))) ⌝ (hₙ n))
   I    = ≃-sym (Σ-change-of-variable Q₁ g₁ (⌜⌝-is-equiv (Π×+ fe)))
   II   = Σ-assoc
   III  = Σ-cong
          (λ hₒ → ≃-sym (Σ-change-of-variable (Q₂ hₒ) g₂ (⌜⌝-is-equiv (Π×+ fe))))
   IV   = Σ-cong (λ _ → Σ-assoc)
   V    = Σ-cong λ hₒ → Σ-cong (λ hₚ → Σ-cong (λ hₙ → γ hₒ hₚ hₙ))
    where
     γ : (hₒ : Π (A ∘ ⌜𝟎⌝))  (hₚ : Π (A ∘ pos)) (hₙ : Π (A ∘ neg))
       → Q₂ hₒ (g₂ (hₚ , hₙ)) ≃ Qₚ (hₒ *) hₚ × Qₙ' (hₒ *) hₙ
     γ hₒ hₚ hₙ = qinveq φ (ψ , η , ε)
      where
       φ : Q₂ hₒ (g₂ (hₚ , hₙ)) → Qₚ (hₒ *) hₚ × Qₙ' (hₒ *) hₙ
       φ q = ((q 𝟎 , q ∘ pos) , (q (neg 0) , q ∘ neg ∘ succ))
       ψ : (Qₚ (hₒ *) hₚ × Qₙ' (hₒ *) hₙ) → Q₂ hₒ (g₂ (hₚ , hₙ))
       ψ ((qₒ , qₚ) , (qₒ' , qₙ')) = c
        where
         c : Q₂ hₒ (g₂ (hₚ , hₙ))
         c 𝟎              = qₒ
         c (pos n)        = qₚ n
         c (neg zero)     = qₒ'
         c (neg (succ n)) = qₙ' n
       ε : φ ∘ ψ ∼ id
       ε q = refl
       η : ψ ∘ φ ∼ id
       η q = dfunext fe c
        where
         c : (z : ℤ) → (ψ (φ q)) z ≡ q (z)
         c 𝟎              = refl
         c (pos n)        = refl
         c (neg zero)     = refl
         c (neg (succ n)) = refl
   VI   = Σ-cong γ
    where
     γ : (hₒ : Π (A ∘ ⌜𝟎⌝))
       → (Σ hₚ ꞉ Π (A ∘ pos) , Σ hₙ ꞉ Π (A ∘ neg) , Qₚ (hₒ *) hₚ × Qₙ' (hₒ *) hₙ)
       ≃ (  (Σ hₚ ꞉ Π (A ∘ pos) , Qₚ (hₒ *) hₚ)
          × (Σ hₙ ꞉ Π (A ∘ neg) , Qₙ' (hₒ *) hₙ))
     γ hₒ = qinveq φ (ψ , η , ε)
      where
       φ : _
       φ (hₙ , hₚ , q' , q) = ((hₙ , q') , (hₚ , q))
       ψ : _
       ψ ((hₙ , q') , (hₚ , q)) = hₙ , hₚ , q' , q
       η : ψ ∘ φ ∼ id
       η _ = refl
       ε : φ ∘ ψ ∼ id
       ε _ = refl
   VII  = Σ-cong (λ hₒ → ×-cong (singleton-≃-𝟙 {𝓤} {𝓤₀} (γ hₒ)) (≃-refl _))
    where
     γ : (hₒ : Π (A ∘ ⌜𝟎⌝))
       → is-singleton ((Σ hₚ ꞉ Π (A ∘ pos) , Qₚ  (hₒ *) hₚ))
     γ hₒ = (ℕ-is-nno-dep fe (A ∘ pos) a₀ s)
      where
       a₀ : A (pos 0)
       a₀ = ⌜ (f 𝟎) ⌝ (hₒ *)
       s : (n : ℕ) → A (pos n) → A (pos (succ n))
       s n = ⌜ f (pos n) ⌝
   VIII = Σ-cong (λ hₒ → 𝟙-lneutral)
   IX   = Σ-cong (λ hₒ → Σ-cong (λ hₙ → γ hₒ hₙ))
    where
     γ : (hₒ : Π (A ∘ ⌜𝟎⌝)) (hₙ : Π (A ∘ neg))
       → Qₙ' (hₒ *) hₙ ≃ Qₙ (hₒ *) hₙ
     γ hₒ hₙ = ×-cong γ₀ (Π-cong fe fe ℕ _ _ γₙ)
      where
       f₀ = ⌜ f (neg 0) ⌝
       f₀⁻¹ = ⌜ ≃-sym (f (neg 0)) ⌝
       e₀ : is-equiv f₀
       e₀ = ⌜⌝-is-equiv (f (neg 0))
       γ₀ : (hₒ * ≡ f₀ (hₙ 0))
          ≃ (hₙ 0 ≡ f₀⁻¹ (hₒ *))
       γ₀ = (hₒ * ≡ f₀ (hₙ 0))             ≃⟨ I₀   ⟩
            (f₀ (hₙ 0) ≡ hₒ *)             ≃⟨ II₀  ⟩
            (f₀ (hₙ 0) ≡ f₀ (f₀⁻¹ (hₒ *))) ≃⟨ III₀ ⟩
            (hₙ 0 ≡ f₀⁻¹ (hₒ *)) ■
        where
         I₀   = ≡-flip
         II₀  = ≡-cong-r (f₀ (hₙ 0)) (hₒ *)
                 ((inverses-are-sections f₀ e₀ (hₒ *)) ⁻¹)
         III₀ = embedding-criterion-converse f₀
                 (equivs-are-embeddings f₀ e₀)
                 (hₙ 0) (f₀⁻¹ (hₒ *))
       fₙ : (n : ℕ) → A (neg (succ n)) → A (neg n)
       fₙ n = ⌜ f (neg (succ n)) ⌝
       eₙ : (n : ℕ) → is-equiv (fₙ n)
       eₙ n = ⌜⌝-is-equiv (f (neg (succ n)))
       fₙ⁻¹ : (n : ℕ) → A (neg n) → A (neg (succ n))
       fₙ⁻¹ n = ⌜ ≃-sym (f (neg (succ n))) ⌝
       γₙ : (n : ℕ)
          → (hₙ n ≡ fₙ n (hₙ (succ n)))
          ≃ (hₙ (succ n) ≡ fₙ⁻¹ n (hₙ n))
       γₙ n = (hₙ n ≡ fₙ n (hₙ (succ n)))                 ≃⟨ Iₙ ⟩
              (fₙ n (hₙ (succ n)) ≡ hₙ n)                 ≃⟨ IIₙ ⟩
              (fₙ n (hₙ (succ n)) ≡ fₙ n (fₙ⁻¹ n (hₙ n))) ≃⟨ IIIₙ ⟩
              (hₙ (succ n) ≡ fₙ⁻¹ n (hₙ n))               ■
        where
         Iₙ   = ≡-flip
         IIₙ  = ≡-cong-r (fₙ n (hₙ (succ n))) (hₙ n)
                 ((inverses-are-sections (fₙ n) (eₙ n) (hₙ n)) ⁻¹)
         IIIₙ = embedding-criterion-converse (fₙ n)
                 (equivs-are-embeddings (fₙ n) (eₙ n))
                 (hₙ (succ n)) (fₙ⁻¹ n (hₙ n))
   X    = Σ-cong (λ hₒ → singleton-≃-𝟙 {𝓤} {𝓤₀} (γ hₒ))
    where
     γ : (hₒ : Π (A ∘ ⌜𝟎⌝))
       → is-singleton ((Σ hₙ ꞉ Π (A ∘ neg) , Qₙ  (hₒ *) hₙ))
     γ hₒ = (ℕ-is-nno-dep fe (A ∘ neg) a₀ s)
      where
       a₀ : A (neg 0)
       a₀ = ⌜ ≃-sym (f (neg 0)) ⌝ (hₒ *)
       s : (n : ℕ) → A (neg n) → A (neg (succ n))
       s n = ⌜ ≃-sym (f (neg (succ n))) ⌝
   XI   = 𝟙-rneutral
   XII  = ≃-sym (𝟙→ fe)

\end{code}

\begin{code}

pred-ℤ : ℤ → ℤ
pred-ℤ 𝟎              = neg 0
pred-ℤ (pos 0)        = 𝟎
pred-ℤ (pos (succ n)) = pos n
pred-ℤ (neg n)        = neg (succ n)

pred-section-of-succ : succ-ℤ ∘ pred-ℤ ∼ id
pred-section-of-succ 𝟎              = refl
pred-section-of-succ (pos zero)     = refl
pred-section-of-succ (pos (succ n)) = refl
pred-section-of-succ (neg n)        = refl

pred-retraction-of-succ : pred-ℤ ∘ succ-ℤ ∼ id
pred-retraction-of-succ 𝟎              = refl
pred-retraction-of-succ (pos n)        = refl
pred-retraction-of-succ (neg zero)     = refl
pred-retraction-of-succ (neg (succ n)) = refl

succ-ℤ-is-equiv : is-equiv succ-ℤ
succ-ℤ-is-equiv = qinvs-are-equivs succ-ℤ
                   (pred-ℤ , pred-retraction-of-succ , pred-section-of-succ)

succ-ℤ-≃ : ℤ ≃ ℤ
succ-ℤ-≃ = (succ-ℤ , succ-ℤ-is-equiv)

pred-ℤ-is-equiv : is-equiv pred-ℤ
pred-ℤ-is-equiv = ⌜⌝-is-equiv (≃-sym succ-ℤ-≃)

\end{code}

\begin{code}

-- TO DO: Possibly move this?
commute-with-iterated-function : {X : 𝓤 ̇ } (f g : X → X)
                               → f ∘ g ∼ g ∘ f
                               → (n : ℕ) → f ∘ (g ^ n) ∼ (g ^ n) ∘ f
commute-with-iterated-function f g h zero     x = refl
commute-with-iterated-function f g h (succ n) x =
 (f ∘ g ∘ (g ^ n)) x ≡⟨ h ((g ^ n) x) ⟩
 (g ∘ f ∘ (g ^ n)) x ≡⟨ ap g (IH x)   ⟩
 (g ∘ (g ^ n) ∘ f) x ∎
  where
   IH : f ∘ (g ^ n) ∼ (g ^ n) ∘ f
   IH = commute-with-iterated-function f g h n

iterated-function-section : {X : 𝓤 ̇ } (s : X → X) (r : X → X)
                          → r ∘ s ∼ id
                          → (n : ℕ) → (r ^ n) ∘ (s ^ n) ∼ id
iterated-function-section s r ρ zero     x = refl
iterated-function-section s r ρ (succ n) x =
 (r ∘ (r ^ n) ∘ s ∘ (s ^ n)) x ≡⟨ I   ⟩
 (r ∘ (r ^ n) ∘ (s ^ n) ∘ s) x ≡⟨ II  ⟩
 (r ∘ s) x                     ≡⟨ ρ x ⟩
 x                             ∎
  where
   I  = ap (r ^ (succ n)) (commute-with-iterated-function s s (λ x → refl) n x)
   II = ap r (iterated-function-section s r ρ n (s x))

iterated-function-is-equiv : {X : 𝓤 ̇ } (f : X → X)
                           → is-equiv f
                           → (n : ℕ) → is-equiv (f ^ n)
iterated-function-is-equiv f ((s , ε) , (r , η)) n =
 (((s ^ n) , (iterated-function-section s f ε n)) ,
  ((r ^ n) , (iterated-function-section f r η n)))

commute-with-succ-ℤ-iterated : (f : ℤ → ℤ)
                             → (f ∘ succ-ℤ ∼ succ-ℤ ∘ f)
                             → (n : ℕ) → f ∘ (succ-ℤ ^ n) ∼ (succ-ℤ ^ n) ∘ f
commute-with-succ-ℤ-iterated f c = commute-with-iterated-function f succ-ℤ c

commute-with-pred-ℤ : (f : ℤ → ℤ)
                    → (f ∘ succ-ℤ ∼ succ-ℤ ∘ f)
                    → f ∘ pred-ℤ ∼ pred-ℤ ∘ f
commute-with-pred-ℤ f c z =
 ⌜ embedding-criterion-converse succ-ℤ
    (equivs-are-embeddings succ-ℤ succ-ℤ-is-equiv)
    ((f ∘ pred-ℤ) z) ((pred-ℤ ∘ f) z)              ⌝ γ
 where
  γ : succ-ℤ (f (pred-ℤ z)) ≡ succ-ℤ (pred-ℤ (f z))
  γ = succ-ℤ (f (pred-ℤ z)) ≡⟨ (c (pred-ℤ z)) ⁻¹               ⟩
      f (succ-ℤ (pred-ℤ z)) ≡⟨ ap f (pred-section-of-succ z)   ⟩
      f z                   ≡⟨ (pred-section-of-succ (f z)) ⁻¹ ⟩
      succ-ℤ (pred-ℤ (f z)) ∎

commute-with-pred-ℤ-iterated : (f : ℤ → ℤ)
                             → (f ∘ succ-ℤ ∼ succ-ℤ ∘ f)
                             → (n : ℕ) → f ∘ (pred-ℤ ^ n) ∼ (pred-ℤ ^ n) ∘ f
commute-with-pred-ℤ-iterated f c =
 commute-with-iterated-function f pred-ℤ (commute-with-pred-ℤ f c)

pos-succ-ℤ-iterated : (n : ℕ) → pos n ≡ (succ-ℤ ^ (succ n)) 𝟎
pos-succ-ℤ-iterated zero     = refl
pos-succ-ℤ-iterated (succ n) = ap succ-ℤ (pos-succ-ℤ-iterated n)

neg-pred-ℤ-iterated : (n : ℕ) → neg n ≡ (pred-ℤ ^ (succ n)) 𝟎
neg-pred-ℤ-iterated zero     = refl
neg-pred-ℤ-iterated (succ n) = ap pred-ℤ (neg-pred-ℤ-iterated n)

commute-with-succ-ℤ-equiv-𝟎 : (f : ℤ → ℤ)
                            → (f ∘ succ-ℤ ∼ succ-ℤ ∘ f)
                            → f 𝟎 ≡ 𝟎
                            → is-equiv f
commute-with-succ-ℤ-equiv-𝟎 f c p =
 equiv-closed-under-∼ id f (id-is-equiv ℤ) h
  where
   h : f ∼ id
   h 𝟎 = p
   h (pos n) = f (pos n)                 ≡⟨ I   ⟩
               f ((succ-ℤ ^ (succ n)) 𝟎) ≡⟨ II  ⟩
               (succ-ℤ ^ (succ n)) (f 𝟎) ≡⟨ III ⟩
               (succ-ℤ ^ (succ n)) 𝟎     ≡⟨ IV  ⟩
               pos n                     ∎
    where
     I   = ap f (pos-succ-ℤ-iterated n)
     II  = commute-with-succ-ℤ-iterated f c (succ n) 𝟎
     III = ap (succ-ℤ ^ (succ n)) p
     IV  = (pos-succ-ℤ-iterated n) ⁻¹
   h (neg n) = f (neg n)                 ≡⟨ I   ⟩
               f ((pred-ℤ ^ (succ n)) 𝟎) ≡⟨ II  ⟩
               (pred-ℤ ^ (succ n)) (f 𝟎) ≡⟨ III ⟩
               (pred-ℤ ^ (succ n)) 𝟎     ≡⟨ IV  ⟩
               neg n                     ∎
    where
     I   = ap f (neg-pred-ℤ-iterated n)
     II  = commute-with-pred-ℤ-iterated f c (succ n) 𝟎
     III = ap (pred-ℤ ^ (succ n)) p
     IV  = (neg-pred-ℤ-iterated n) ⁻¹

pred-section-of-succ-iterated : (n : ℕ) → (succ-ℤ ^ n) ∘ (pred-ℤ ^ n) ∼ id
pred-section-of-succ-iterated =
 iterated-function-section pred-ℤ succ-ℤ pred-section-of-succ

pred-retraction-of-succ-iterated : (n : ℕ) → (pred-ℤ ^ n) ∘ (succ-ℤ ^ n) ∼ id
pred-retraction-of-succ-iterated =
 iterated-function-section succ-ℤ pred-ℤ pred-retraction-of-succ

commute-with-succ-ℤ-equiv-pos : (f : ℤ → ℤ)
                              → (f ∘ succ-ℤ ∼ succ-ℤ ∘ f)
                              → (n : ℕ)
                              → f 𝟎 ≡ pos n
                              → is-equiv f
commute-with-succ-ℤ-equiv-pos f c n p =
 equiv-closed-under-∼ (succ-ℤ ^ (succ n) ∘ g) f
  (∘-is-equiv g-is-equiv
   (iterated-function-is-equiv succ-ℤ succ-ℤ-is-equiv (succ n)))
  (λ z → (pred-section-of-succ-iterated (succ n) (f z)) ⁻¹)
  where
   g : ℤ → ℤ
   g = (pred-ℤ ^ (succ n)) ∘ f
   g-is-𝟎-on-𝟎 : g 𝟎 ≡ 𝟎
   g-is-𝟎-on-𝟎 = ((pred-ℤ ^ (succ n)) ∘ f) 𝟎              ≡⟨ I   ⟩
                  (pred-ℤ ^ succ n) (pos n)               ≡⟨ II  ⟩
                  (pred-ℤ ^ succ n) ((succ-ℤ ^ succ n) 𝟎) ≡⟨ III ⟩
                  𝟎                                       ∎
    where
     I   = ap (pred-ℤ ^ (succ n)) p
     II  = ap (pred-ℤ ^ (succ n)) (pos-succ-ℤ-iterated n)
     III = pred-retraction-of-succ-iterated (succ n) 𝟎
   g-commutes-with-succ : g ∘ succ-ℤ ∼ succ-ℤ ∘ g
   g-commutes-with-succ z = ((pred-ℤ ^ (succ n)) ∘ f ∘ succ-ℤ) z ≡⟨ I  ⟩
                            ((pred-ℤ ^ (succ n)) ∘ succ-ℤ ∘ f) z ≡⟨ II ⟩
                            (succ-ℤ ∘ (pred-ℤ ^ (succ n)) ∘ f) z ∎
    where
     I  = ap (pred-ℤ ^ (succ n)) (c z)
     II = (commute-with-iterated-function succ-ℤ pred-ℤ
            (λ x → pred-section-of-succ x ∙ (pred-retraction-of-succ x) ⁻¹)
            (succ n) (f z)) ⁻¹
   g-is-equiv : is-equiv g
   g-is-equiv = commute-with-succ-ℤ-equiv-𝟎 g g-commutes-with-succ g-is-𝟎-on-𝟎

commute-with-succ-ℤ-equiv-neg : (f : ℤ → ℤ)
                              → (f ∘ succ-ℤ ∼ succ-ℤ ∘ f)
                              → (n : ℕ)
                              → f 𝟎 ≡ neg n
                              → is-equiv f
commute-with-succ-ℤ-equiv-neg f c n p =
 equiv-closed-under-∼ (pred-ℤ ^ (succ n) ∘ g) f
  (∘-is-equiv g-is-equiv
   (iterated-function-is-equiv pred-ℤ pred-ℤ-is-equiv (succ n)))
  (λ z → (pred-retraction-of-succ-iterated (succ n) (f z)) ⁻¹)
  where
   g : ℤ → ℤ
   g = (succ-ℤ ^ (succ n)) ∘ f
   g-is-𝟎-on-𝟎 : g 𝟎 ≡ 𝟎
   g-is-𝟎-on-𝟎 = ((succ-ℤ ^ (succ n)) ∘ f) 𝟎              ≡⟨ I   ⟩
                  (succ-ℤ ^ succ n) (neg n)               ≡⟨ II  ⟩
                  (succ-ℤ ^ succ n) ((pred-ℤ ^ succ n) 𝟎) ≡⟨ III ⟩
                  𝟎                                       ∎
    where
     I   = ap (succ-ℤ ^ (succ n)) p
     II  = ap (succ-ℤ ^ (succ n)) (neg-pred-ℤ-iterated n)
     III = pred-section-of-succ-iterated (succ n) 𝟎
   g-commutes-with-succ : g ∘ succ-ℤ ∼ succ-ℤ ∘ g
   g-commutes-with-succ z = ((succ-ℤ ^ (succ n)) ∘ f ∘ succ-ℤ) z ≡⟨ I  ⟩
                            ((succ-ℤ ^ (succ n)) ∘ succ-ℤ ∘ f) z ≡⟨ II ⟩
                            (succ-ℤ ∘ (succ-ℤ ^ (succ n)) ∘ f) z ∎
    where
     I  = ap (succ-ℤ ^ (succ n)) (c z)
     II = (commute-with-iterated-function succ-ℤ succ-ℤ
            (λ x → refl) (succ n) (f z)) ⁻¹
   g-is-equiv : is-equiv g
   g-is-equiv = commute-with-succ-ℤ-equiv-𝟎 g g-commutes-with-succ g-is-𝟎-on-𝟎

commute-with-succ-ℤ-equiv : (f : ℤ → ℤ)
                          → (f ∘ succ-ℤ ∼ succ-ℤ ∘ f)
                          → is-equiv f
commute-with-succ-ℤ-equiv f c = γ (f 𝟎) refl
 where
  γ : (z : ℤ) → f 𝟎 ≡ z → is-equiv f
  γ 𝟎       p = commute-with-succ-ℤ-equiv-𝟎 f c p
  γ (pos n) p = commute-with-succ-ℤ-equiv-pos f c n p
  γ (neg n) p = commute-with-succ-ℤ-equiv-neg f c n p

\end{code}

\begin{code}

open import UF-Miscelanea

ℤ-is-set : is-set ℤ
ℤ-is-set = +-is-set 𝟙 (ℕ + ℕ) (props-are-sets 𝟙-is-prop)
            (+-is-set ℕ ℕ ℕ-is-set ℕ-is-set)

\end{code}
