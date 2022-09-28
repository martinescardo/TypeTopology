Jon Sterling, started 27th Sep 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt
open import UF.Equiv
open import UF.Retracts
import Slice.Slice as Slice

open import Modal.Subuniverse

module Modal.ReflectiveSubuniverse (P : subuniverse 𝓤 𝓥) (P-is-reflective : subuniverse-is-reflective P) where

reflection : (A : 𝓤 ̇) → reflection-candidate P A
reflection A = pr₁ (P-is-reflective A)

○-packed : (A : 𝓤 ̇) → subuniverse-member P
○-packed A = pr₁ (reflection A)

○ : 𝓤 ̇ → 𝓤 ̇
○ A = pr₁ (○-packed A)

subuniverse-contains-reflection : (A : 𝓤 ̇) → subuniverse-contains P (○ A)
subuniverse-contains-reflection A = pr₂ (○-packed A)

η : (A : 𝓤 ̇) → A → ○ A
η A = pr₂ (reflection A)

precomp-η : {𝓥 : _} (A : 𝓤 ̇) (B : 𝓥 ̇) → (○ A → B) → A → B
precomp-η A B f = f ∘ η A

precomp-η-is-equiv
 : {A B : 𝓤 ̇}
 → subuniverse-contains P B
 → is-equiv (precomp-η A B)
precomp-η-is-equiv B-in-P =
 pr₂ (P-is-reflective _) _ B-in-P

○-rec
 : (A B : 𝓤 ̇)
 → (B-in-P : subuniverse-contains P B)
 → (A → B)
 → (○ A → B)
○-rec A B B-in-P =
 inverse _ (precomp-η-is-equiv B-in-P)

○-rec-compute
 : (A B : 𝓤 ̇)
 → (B-in-P : subuniverse-contains P B)
 → (f : A → B)
 → (x : A)
 → ○-rec A B B-in-P f (η A x) ＝ f x
○-rec-compute A B B-in-P f =
 happly (inverses-are-sections _ (precomp-η-is-equiv B-in-P) f)

abstract
 ○-rec-ext
  : (A B : 𝓤 ̇)
  → (B-in-P : subuniverse-contains P B)
  → (f g : ○ A → B)
  → (f ∘ η A) ＝ (g ∘ η A)
  → f ＝ g
 ○-rec-ext A B B-in-P f g fgη =
  H f ⁻¹ ∙ ap (○-rec A B B-in-P) fgη ∙ H g
  where
   H : inverse (precomp-η A B) (precomp-η-is-equiv B-in-P) ∘ precomp-η A B ∼ id
   H = inverses-are-retractions _ (precomp-η-is-equiv B-in-P)

 ○-rec-ext-beta
  : (A B : 𝓤 ̇)
  → (B-in-P : subuniverse-contains P B)
  → (f : ○ A → B)
  → ○-rec-ext A B B-in-P f f refl ＝ refl
 ○-rec-ext-beta A B B-in-P f =
    (H f ⁻¹ ∙ H f) ＝⟨ (sym-is-inverse (H f)) ⁻¹ ⟩
    refl ∎

  where
   H : inverse (precomp-η A B) (precomp-η-is-equiv B-in-P) ∘ precomp-η A B ∼ id
   H = inverses-are-retractions _ (precomp-η-is-equiv B-in-P)



η-is-section-gives-has-section
 : (fe : funext 𝓤 𝓤)
 → (A : 𝓤 ̇)
 → is-section (η A)
 → has-section (η A)
pr₁ (η-is-section-gives-has-section fe A η-is-section) = pr₁ η-is-section
pr₂ (η-is-section-gives-has-section fe A η-is-section) =
 happly
  (○-rec-ext A (○ A) (subuniverse-contains-reflection A) _ _
    (dfunext fe λ x →
     η A (pr₁ η-is-section (η A x)) ＝⟨ ap (η A) (pr₂ η-is-section x) ⟩
     η A x ∎))

η-is-section-gives-is-equiv
 : (fe : funext 𝓤 𝓤)
 → (A : 𝓤 ̇)
 → is-section (η A)
 → is-equiv (η A)
pr₁ (η-is-section-gives-is-equiv fe A η-is-section) = η-is-section-gives-has-section fe A η-is-section
pr₂ (η-is-section-gives-is-equiv fe A η-is-section) = η-is-section

η-is-equiv-gives-subuniverse-contains
 : (P-is-replete : subuniverse-is-replete P)
 → (A : 𝓤 ̇)
 → is-equiv (η A)
 → subuniverse-contains P A
η-is-equiv-gives-subuniverse-contains P-is-replete A η-is-equiv =
 P-is-replete _ _
  (η A , η-is-equiv)
  (subuniverse-contains-reflection A)

reflective-subuniverse-closed-under-retracts
 : (fe : funext 𝓤 𝓤)
 → (P-is-replete : subuniverse-is-replete P)
 → (E B : 𝓤 ̇)
 → retract B of E
 → subuniverse-contains P E
 → subuniverse-contains P B
reflective-subuniverse-closed-under-retracts fe P-is-replete E B B-retract-of-E E-in-P =
 η-is-equiv-gives-subuniverse-contains P-is-replete B
  (η-is-section-gives-is-equiv fe B η-is-section)
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
 : (fe : funext 𝓤 𝓤)
 → (P-is-replete : subuniverse-is-replete P)
 → (A : 𝓤 ̇)
 → (B : A → 𝓤 ̇)
 → (B-in-P : Π x ꞉ A , subuniverse-contains P (B x))
 → subuniverse-contains P (Π B)
reflective-subuniverse-closed-under-products fe P-is-replete A B B-in-P =
 reflective-subuniverse-closed-under-retracts fe P-is-replete _ _ ret (subuniverse-contains-reflection (Π B))
 where
  h : (x : A) → ○ (Π B) → B x
  h x = ○-rec (Π B) (B x) (B-in-P x) (λ f → f x)

  ret : retract Π B of ○ (Π B)
  pr₁ ret f x = h x f
  pr₁ (pr₂ ret) = η (Π B)
  pr₂ (pr₂ ret) f =
   dfunext fe λ x →
   ○-rec-compute (Π B) (B x) (B-in-P x) (λ g → g x) f


-- The following is currently too hard to prove!
{-
reflective-subuniverse-closed-under-id
 : (fe : funext 𝓤 𝓤)
 → (P-is-replete : subuniverse-is-replete P)
 → (A : 𝓤 ̇)
 → (u v : A)
 → (A-in-P : subuniverse-contains P A)
 → subuniverse-contains P (u ＝ v)
reflective-subuniverse-closed-under-id fe P-is-replete A u v A-in-P =


-}

\end{code}


TODO: try to do this the way it is done in Egbert's thesis. It feels like he has a reasonable proof that reflective subuniverses are closed under pullback (5.1.19) which will then give the main result by repleteness.
