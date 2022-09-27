Jon Sterling, started 27th Sep 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Modal.Subuniverse where

open import MLTT.Spartan
open import UF.Subsingletons
open import UF.Base
open import UF.FunExt
open import UF.Equiv
open import UF.Retracts
open import UF.UA-FunExt
open import UF.Univalence

subuniverse
  : (𝓤 𝓥 : Universe)
  → (𝓤 ⊔ 𝓥)⁺ ̇
subuniverse 𝓤 𝓥 =
  Σ P ꞉ (𝓤 ̇ → 𝓥 ̇) ,
  Π A ꞉ 𝓤 ̇ ,
  is-prop (P A)

subuniverse-contains
  : subuniverse 𝓤 𝓥
  → 𝓤 ̇
  → 𝓥 ̇
subuniverse-contains P A =
  pr₁ P A

subuniverse-member
  : subuniverse 𝓤 𝓥
  → 𝓤 ⁺ ⊔ 𝓥  ̇
subuniverse-member P =
  Σ (subuniverse-contains P)

reflection-candidate
  : subuniverse 𝓤 𝓥
  → 𝓤 ̇
  → 𝓤 ⁺ ⊔ 𝓥  ̇
reflection-candidate P A =
  Σ A' ꞉ subuniverse-member P ,
  (A → pr₁ A')

is-reflection
  : (P : subuniverse 𝓤 𝓥)
  → (A : 𝓤 ̇)
  → reflection-candidate P A
  → 𝓤 ⁺ ⊔ 𝓥  ̇
is-reflection P A (A' , η) =
  Π B ꞉ subuniverse-member P ,
  is-equiv λ (f : pr₁ A' → pr₁ B) → f ∘ η

subuniverse-reflects
  : subuniverse 𝓤 𝓥
  → 𝓤 ̇
  → 𝓤 ⁺ ⊔ 𝓥  ̇
subuniverse-reflects {𝓤 = 𝓤} P A =
  Σ A' ꞉ reflection-candidate P A ,
  is-reflection P A A'

subuniverse-is-reflective
  : subuniverse 𝓤 𝓥
  → 𝓤 ⁺ ⊔ 𝓥  ̇
subuniverse-is-reflective P =
  Π (subuniverse-reflects P)



module ReflectiveSubuniverse (P : subuniverse 𝓤 𝓥) (P-is-reflective : subuniverse-is-reflective P) where
  Type○ = subuniverse-member P

  ○ : 𝓤 ̇ → 𝓤 ̇
  ○ A = pr₁ (pr₁ (pr₁ (P-is-reflective A)))

  ○-in-subuniverse : (A : 𝓤 ̇) → subuniverse-contains P (○ A)
  ○-in-subuniverse A = pr₂ (pr₁ (pr₁ (P-is-reflective A)))

  η : (A : 𝓤 ̇) → A → ○ A
  η A = pr₂ (pr₁ (P-is-reflective A))

  ○-rec
    : (A B : 𝓤 ̇)
    → (B-in-P : subuniverse-contains P B)
    → (A → B)
    → (○ A → B)
  ○-rec A B B-in-P =
    inverse
     (_∘ (η A))
     (pr₂ (P-is-reflective A) (B , B-in-P))

  ○-rec-compute
    : (A B : 𝓤 ̇)
    → (B-in-P : subuniverse-contains P B)
    → (f : A → B)
    → (x : A)
    → ○-rec A B B-in-P f (η A x) ＝ f x
  ○-rec-compute A B B-in-P f =
    happly
     (inverses-are-sections
      (_∘ (η A))
      (pr₂ (P-is-reflective A) (B , B-in-P))
      f)

  ○-rec-ext
    : (A B : 𝓤 ̇)
    → (B-in-P : subuniverse-contains P B)
    → (f g : ○ A → B)
    → (f ∘ η A) ＝ (g ∘ η A)
    → f ＝ g
  ○-rec-ext A B B-in-P f g fgη =
    let H = inverses-are-retractions (_∘ (η A)) (pr₂ (P-is-reflective A) (B , B-in-P)) in
    f ＝⟨ H f ⁻¹ ⟩
    ○-rec A B B-in-P (f ∘ η A) ＝⟨ ap (○-rec A B B-in-P) fgη ⟩
    ○-rec A B B-in-P (g ∘ η A) ＝⟨ H g ⟩
    g ∎


  η-is-section-implies-has-section
    : (fe : funext 𝓤 𝓤)
    → (A : 𝓤 ̇)
    → is-section (η A)
    → has-section (η A)
  pr₁ (η-is-section-implies-has-section fe A η-is-section) = pr₁ η-is-section
  pr₂ (η-is-section-implies-has-section fe A η-is-section) =
    happly
     (○-rec-ext A (○ A) (○-in-subuniverse A) _ _
       (dfunext fe λ x →
        η A (pr₁ η-is-section (η A x)) ＝⟨ ap (η A) (pr₂ η-is-section x) ⟩
        η A x ∎))

  η-is-equiv-implies-subuniverse-contains
    : (ua : is-univalent 𝓤)
    → (A : 𝓤 ̇)
    → is-equiv (η A)
    → subuniverse-contains P A
  η-is-equiv-implies-subuniverse-contains ua A η-is-equiv =
    transport⁻¹
     (subuniverse-contains P)
     (eqtoid ua A (○ A) (η A , η-is-equiv))
     (○-in-subuniverse A)

  reflective-subuniverse-closed-under-retracts
    : (ua : is-univalent 𝓤)
    → (E B : 𝓤 ̇)
    → retract B of E
    → subuniverse-contains P E
    → subuniverse-contains P B
  reflective-subuniverse-closed-under-retracts ua E B B-retract-of-E E-in-P =
    η-is-equiv-implies-subuniverse-contains ua B
     (η-is-section-implies-has-section (univalence-gives-funext ua) B η-is-section ,
      η-is-section)
    where
      h : ○ B → E
      h = ○-rec B E E-in-P (section B-retract-of-E)

      ε : ○ B → B
      ε = retraction B-retract-of-E ∘ h

      η-is-section : is-section (η B)
      pr₁ η-is-section = ε
      pr₂ η-is-section x =
        ε (η B x) ＝⟨ ap (retraction B-retract-of-E) (○-rec-compute B E E-in-P (section B-retract-of-E) x) ⟩
        retraction B-retract-of-E (section B-retract-of-E x) ＝⟨ retract-condition B-retract-of-E x ⟩
        x ∎

  reflective-subuniverse-closed-under-products
    : (ua : is-univalent 𝓤)
    → (A : 𝓤 ̇)
    → (B : A → 𝓤 ̇)
    → (B-in-P : Π x ꞉ A , subuniverse-contains P (B x))
    → subuniverse-contains P (Π B)
  reflective-subuniverse-closed-under-products ua A B B-in-P =
    reflective-subuniverse-closed-under-retracts ua (○ (Π B)) (Π B) ret (○-in-subuniverse (Π B))
    where

      h : (x : A) → ○ (Π B) → B x
      h x = ○-rec (Π B) (B x) (B-in-P x) (λ f → f x)

      ret : retract Π B of ○ (Π B)
      pr₁ ret f x = h x f
      pr₁ (pr₂ ret) = η (Π B)
      pr₂ (pr₂ ret) f =
       dfunext (univalence-gives-funext ua) λ x →
         ○-rec-compute (Π B) (B x) (B-in-P x) (λ g → g x) f

\end{code}
