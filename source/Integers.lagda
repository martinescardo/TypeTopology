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
ℤ = ℕ + 𝟙 + ℕ

pattern 𝟎 = inr (inl *)
pattern pos i = inr (inr i)
pattern neg i = inl i

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
 (Σ h ꞉ (Π (A ∘ neg) × Π (A ∘ inr)) , Q₁ (g₁ h))                  ≃⟨ II   ⟩
 (Σ hₙ ꞉ Π (A ∘ neg) , Σ hᵣ ꞉ Π (A ∘ inr) , Q₁ (g₁ (hₙ , hᵣ)))    ≃⟨ III  ⟩
 (Σ hₙ ꞉ Π (A ∘ neg) , Σ hᵣ ꞉ (Π (A ∘ ⌜𝟎⌝) × Π (A ∘ pos)) ,
                         Q₂ hₙ (g₂ hᵣ))                           ≃⟨ IV   ⟩
 (Σ hₙ ꞉ Π (A ∘ neg) , Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) ,
                       Σ hₚ ꞉ Π (A ∘ pos) , Q₂ hₙ (g₂ (hₒ , hₚ))) ≃⟨ V    ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , Σ hₙ ꞉ Π (A ∘ neg) ,
                       Σ hₚ ꞉ Π (A ∘ pos) , Q₂ hₙ (g₂ (hₒ , hₚ))) ≃⟨ VI   ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , Σ hₙ ꞉ Π (A ∘ neg) ,
                       Σ hₚ ꞉ Π (A ∘ pos) , Qₙ' (hₒ *) hₙ
                                          × Qₚ (hₒ *) hₚ)         ≃⟨ VII  ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , (Σ hₙ ꞉ Π (A ∘ neg) , Qₙ' (hₒ *) hₙ)
                     × (Σ hₚ ꞉ Π (A ∘ pos) , Qₚ (hₒ *) hₚ))       ≃⟨ VIII ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , (Σ hₙ ꞉ Π (A ∘ neg) , Qₙ' (hₒ *) hₙ) × 𝟙)  ≃⟨ IX   ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , (Σ hₙ ꞉ Π (A ∘ neg) , Qₙ' (hₒ *) hₙ))      ≃⟨ X    ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , (Σ hₙ ꞉ Π (A ∘ neg) , Qₙ (hₒ *) hₙ))       ≃⟨ XI   ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , 𝟙)                                         ≃⟨ XII  ⟩
 Π (A ∘ ⌜𝟎⌝)                                                      ≃⟨ XIII ⟩
 A 𝟎                                                              ■
  where
   ⌜𝟎⌝ : 𝟙 {𝓤₀} → ℤ
   ⌜𝟎⌝ _ = 𝟎
   Q₁ : Π A → 𝓤 ̇
   Q₁ h = (z : ℤ) → h (succ-ℤ z) ≡ ⌜ f z ⌝ (h z)
   g₁ : Π (A ∘ neg) × Π (A ∘ inr) → Π A
   g₁ = ⌜ Π×+ fe ⌝
   Q₂ : Π (A ∘ neg) → Π (A ∘ inr) → 𝓤 ̇
   Q₂ hₙ hᵣ = Q₁ (g₁ (hₙ , hᵣ))
   g₂ : Π (A ∘ ⌜𝟎⌝) × Π (A ∘ pos) → Π (A ∘ inr)
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
   I    =  ≃-sym (Σ-change-of-variable Q₁ g₁ (⌜⌝-is-equiv (Π×+ fe)))
   II   = Σ-assoc
   III  = Σ-cong
          (λ hₙ → ≃-sym (Σ-change-of-variable (Q₂ hₙ) g₂ (⌜⌝-is-equiv (Π×+ fe))))
   IV   = Σ-cong (λ hᵣ → Σ-assoc)
   V    = Σ-flip
   VI   = Σ-cong (λ hₒ → Σ-cong (λ hₙ → Σ-cong (λ hₚ → γ hₒ hₙ hₚ)))
    where
     γ : (hₒ : Π (A ∘ ⌜𝟎⌝)) (hₙ : Π (A ∘ neg)) (hₚ : Π (A ∘ pos))
       → Q₂ hₙ (g₂ (hₒ , hₚ)) ≃ Qₙ' (hₒ *) hₙ × Qₚ (hₒ *) hₚ
     γ hₒ hₙ hₚ = qinveq φ (ψ , η , ε)
      where
       φ : Q₂ hₙ (g₂ (hₒ , hₚ)) → Qₙ' (hₒ *) hₙ × Qₚ (hₒ *) hₚ
       φ q = ((q (neg 0) , q ∘ neg ∘ succ) , (q 𝟎 , q ∘ pos))
       ψ : (Qₙ' (hₒ *) hₙ × Qₚ (hₒ *) hₚ) → Q₂ hₙ (g₂ (hₒ , hₚ))
       ψ ((qₒ' , qₙ') , (qₒ , qₚ)) = c
        where
         c : Q₂ hₙ (g₂ (hₒ , hₚ))
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
   VII  = Σ-cong γ
    where
     γ : (hₒ : Π (A ∘ ⌜𝟎⌝))
       → (Σ hₙ ꞉ Π (A ∘ neg) , Σ hₚ ꞉ Π (A ∘ pos) , Qₙ' (hₒ *) hₙ
                                                  × Qₚ  (hₒ *) hₚ)
       ≃ ((Σ hₙ ꞉ Π (A ∘ neg) , Qₙ' (hₒ *) hₙ)
        × (Σ hₚ ꞉ Π (A ∘ pos) , Qₚ  (hₒ *) hₚ))
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
   VIII = Σ-cong (λ hₒ → Σ-cong (λ _ → singleton-≃-𝟙 {𝓤} {𝓤₀} (γ hₒ)))
    where
     γ : (hₒ : Π (A ∘ ⌜𝟎⌝))
       → is-singleton ((Σ hₚ ꞉ Π (A ∘ pos) , Qₚ  (hₒ *) hₚ))
     γ hₒ = (ℕ-is-nno-dep fe (A ∘ pos) a₀ s)
      where
       a₀ : A (pos 0)
       a₀ = ⌜ (f 𝟎) ⌝ (hₒ *)
       s : (n : ℕ) → A (pos n) → A (pos (succ n))
       s n = ⌜ f (pos n) ⌝
   IX   = Σ-cong (λ _ → 𝟙-rneutral)
   X    = Σ-cong (λ hₒ → Σ-cong (λ hₙ → γ hₒ hₙ))
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
   XI   = Σ-cong (λ hₒ → singleton-≃-𝟙 {𝓤} {𝓤₀} (γ hₒ))
    where
     γ : (hₒ : Π (A ∘ ⌜𝟎⌝))
       → is-singleton ((Σ hₙ ꞉ Π (A ∘ neg) , Qₙ  (hₒ *) hₙ))
     γ hₒ = (ℕ-is-nno-dep fe (A ∘ neg) a₀ s)
      where
       a₀ : A (neg 0)
       a₀ = ⌜ ≃-sym (f (neg 0)) ⌝ (hₒ *)
       s : (n : ℕ) → A (neg n) → A (neg (succ n))
       s n = ⌜ ≃-sym (f (neg (succ n))) ⌝
   XII  = 𝟙-rneutral
   XIII = ≃-sym (𝟙→ fe)

{-
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
-}

\end{code}
