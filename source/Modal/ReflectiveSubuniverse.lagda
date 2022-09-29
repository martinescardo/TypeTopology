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


transport-Σ
  : {𝓤 𝓥 𝓦 : _}
  → (A : 𝓤 ̇)
  → (B : A → 𝓥 ̇)
  → (C : (x : A) → B x → 𝓦 ̇)
  → {x y : A}
  → (p : x ＝ y)
  → (h : Σ (C x))
  → transport (λ - → Σ (C -)) p h ＝ transport B p (pr₁ h) , transport (λ - → C (pr₁ -) (pr₂ -)) (to-Σ-＝ (p , refl)) (pr₂ h)
transport-Σ A B C refl h = refl


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


○-rec-compute-pointsfree
 : (A B : 𝓤 ̇)
 → (B-in-P : subuniverse-contains P B)
 → (f : A → B)
 → ○-rec A B B-in-P f ∘ η A ＝ f
○-rec-compute-pointsfree A B B-in-P f =
 inverses-are-sections _ (precomp-η-is-equiv B-in-P) f


○-rec-compute
 : (A B : 𝓤 ̇)
 → (B-in-P : subuniverse-contains P B)
 → (f : A → B)
 → (x : A)
 → ○-rec A B B-in-P f (η A x) ＝ f x
○-rec-compute A B B-in-P f =
 happly (○-rec-compute-pointsfree _ _ _ _)

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


module _ {𝓤 𝓥 : _} (A A' : 𝓤 ̇) (B : A → 𝓥 ̇) (B' : A' → 𝓥 ̇) (f : A → A') (g : (x : A) → B x → B' (f x)) where

 Σ-map-fwd : Σ B → Σ B'
 Σ-map-fwd (x , y) = f x , g x y

 module _ (f-equiv : is-equiv f) (g-equiv : (x : A) → is-equiv (g x)) where
  private
   f-hae : is-hae f
   f-hae = equivs-are-haes f f-equiv

   inv-f = pr₁ f-hae
   inv-f-sec = pr₁ (pr₂ (pr₂ f-hae))
   inv-f-ret = pr₁ (pr₂ f-hae)
   inv-f-sec-coh = pr₂ (pr₂ (pr₂ f-hae))

   inv-g[_] = λ x → inverse (g x) (g-equiv x)
   inv-g-sec[_] = λ x → inverses-are-sections (g x) (g-equiv x)
   inv-g-ret[_] = λ x → inverses-are-retractions (g x) (g-equiv x)


  Σ-map-bwd : Σ B' → Σ B
  pr₁ (Σ-map-bwd (x , y)) = inv-f x
  pr₂ (Σ-map-bwd (x , y)) = inv-g[ inv-f x ] (transport⁻¹ B' (inv-f-sec x) y)

  Σ-map-bwd-is-section-pr₁ : pr₁ ∘ Σ-map-fwd ∘ Σ-map-bwd ∼ pr₁
  Σ-map-bwd-is-section-pr₁ (x , _) = inv-f-sec x

  Σ-map-bwd-is-section-pr₂ : (u : Σ B') → transport B' (inv-f-sec (pr₁ u)) (pr₂ (Σ-map-fwd (Σ-map-bwd u))) ＝ pr₂ u
  Σ-map-bwd-is-section-pr₂ (x , y) =
   transport B' (inv-f-sec x) (g (inv-f x) (inv-g[ (inv-f x) ] (transport⁻¹ B' (inv-f-sec x) y))) ＝⟨ ap (transport B' (inv-f-sec x)) (inv-g-sec[ inv-f x ] (transport⁻¹ B' (inv-f-sec x) y)) ⟩
   transport B' (inv-f-sec x) (transport⁻¹ B' (inv-f-sec x) y) ＝⟨ back-and-forth-transport (inv-f-sec x) ⟩
   y ∎

  Σ-map-bwd-is-section : Σ-map-fwd ∘ Σ-map-bwd ∼ id
  Σ-map-bwd-is-section u = to-Σ-＝ (Σ-map-bwd-is-section-pr₁ u , Σ-map-bwd-is-section-pr₂ u)

  Σ-map-bwd-is-retraction-pr₁ : pr₁ ∘ Σ-map-bwd ∘ Σ-map-fwd ∼ pr₁
  Σ-map-bwd-is-retraction-pr₁ (x , y) = inv-f-ret x

  Σ-map-bwd-is-retraction-pr₂ : (u : Σ B) → transport B (inv-f-ret (pr₁ u)) (pr₂ (Σ-map-bwd (Σ-map-fwd u))) ＝ pr₂ u
  Σ-map-bwd-is-retraction-pr₂ (x , y) =
   transport B (inv-f-ret x) (inv-g[ inv-f (f x) ] (transport⁻¹ B' (inv-f-sec (f x)) (g x y))) ＝⟨ nat-transport inv-g[_] (inv-f-ret x) ⁻¹ ⟩
   inv-g[ x ] (transport (B' ∘ f) (inv-f-ret x) (transport B' (inv-f-sec (f x) ⁻¹) (g x y))) ＝⟨ ap inv-g[ x ] (transport-ap B' f (inv-f-ret x)) ⟩
   inv-g[ x ] (transport B' (ap f (inv-f-ret x)) (transport B' (inv-f-sec (f x) ⁻¹) (g x y))) ＝⟨ ap inv-g[ x ] (transport-∙ B' (inv-f-sec (f x) ⁻¹) (ap f (inv-f-ret x)) ⁻¹) ⟩
   inv-g[ x ] (transport B' (inv-f-sec (f x) ⁻¹ ∙ ap f (inv-f-ret x)) (g x y)) ＝⟨ ap (λ - → inv-g[ x ] (transport B' - (g x y))) aux ⟩
   inv-g[ x ] (g x y) ＝⟨ inv-g-ret[ x ] y ⟩
   y ∎
   where
    aux : inv-f-sec (f x) ⁻¹ ∙ ap f (inv-f-ret x) ＝ refl
    aux =
     inv-f-sec (f x) ⁻¹ ∙ ap f (inv-f-ret x) ＝⟨ ap (inv-f-sec (f x) ⁻¹ ∙_) (inv-f-sec-coh x) ⟩
     inv-f-sec (f x) ⁻¹ ∙ inv-f-sec (f x) ＝⟨ trans-sym (inv-f-sec (f x)) ⟩
     refl ∎


  Σ-map-bwd-is-retraction : Σ-map-bwd ∘ Σ-map-fwd ∼ id
  Σ-map-bwd-is-retraction u = to-Σ-＝ (Σ-map-bwd-is-retraction-pr₁ u , Σ-map-bwd-is-retraction-pr₂ u)

  Σ-map-fwd-is-equiv : is-equiv Σ-map-fwd
  pr₁ (pr₁ Σ-map-fwd-is-equiv) = Σ-map-bwd
  pr₂ (pr₁ Σ-map-fwd-is-equiv) = Σ-map-bwd-is-section
  pr₁ (pr₂ Σ-map-fwd-is-equiv) = Σ-map-bwd
  pr₂ (pr₂ Σ-map-fwd-is-equiv) = Σ-map-bwd-is-retraction



Σ-equiv-piecewise
  : {𝓤 𝓥 : _}
  → (A A' : 𝓤 ̇)
  → (B : A → 𝓥 ̇)
  → (B' : A' → 𝓥 ̇)
  → (f : A ≃ A')
  → (g : (x : A) → B x ≃ B' (eqtofun f x))
  → Σ B ≃ Σ B'
pr₁ (Σ-equiv-piecewise A A' B B' f g) =
 Σ-map-fwd _ _ _ _ _ _
pr₂ (Σ-equiv-piecewise A A' B B' f g) =
 Σ-map-fwd-is-equiv _ _ _ _ _ _ (pr₂ f) (λ x → pr₂ (g x))


module Pullbacks (fe : funext 𝓤 𝓤) (P-is-replete : subuniverse-is-replete P) (A B X : 𝓤 ̇) (A-in-P : subuniverse-contains P A) (B-in-P : subuniverse-contains P B) (X-in-P : subuniverse-contains P X) (f : A → X) (g : B → X) where

  private
   C : 𝓤 ̇
   C = Slice.pullback 𝓤 f g

   p : C → A
   p (a , _ , _) = a

   q : C → B
   q (_ , b , _) = b

   H : f ∘ p ∼ g ∘ q
   H (_ , _ , α) = α

   cone : 𝓤 ̇ → 𝓤 ̇
   cone Z = Slice.to-span 𝓤 f g Z

   cone-map-equiv : (Z : 𝓤 ̇) → (Z → C) ≃ cone Z
   cone-map-equiv Z = Slice.→-pullback-≃ 𝓤 f g Z fe

   restrict-cone : (Z : 𝓤 ̇) → cone (○ Z) → cone Z
   pr₁ (restrict-cone Z (ha , hb , hα)) = ha ∘ η Z
   pr₁ (pr₂ (restrict-cone Z (hq , hb , hα))) = hb ∘ η Z
   pr₂ (pr₂ (restrict-cone Z (hq , hb , hα))) = hα ∘ η Z

   extend-cone : cone C → cone (○ C)
   pr₁ (extend-cone (ha , hb , hα)) = ○-rec C A A-in-P ha
   pr₁ (pr₂ (extend-cone (ha , hb , hα))) = ○-rec C B B-in-P hb
   pr₂ (pr₂ (extend-cone (ha , hb , hα))) =
    happly
     (○-rec-ext C X X-in-P _ _
      (dfunext fe λ c →
       f (○-rec C A A-in-P ha (η C c)) ＝⟨ ap f (○-rec-compute C A A-in-P ha c) ⟩
       f (ha c) ＝⟨ hα c ⟩
       g (hb c) ＝⟨ ap g (○-rec-compute C B B-in-P hb c ⁻¹) ⟩
       g (○-rec C B B-in-P hb (η C c)) ∎))

   restrict-cone-equiv : cone (○ C) ≃ cone C
   restrict-cone-equiv =
    Σ-equiv-piecewise _ _ _ _
     (precomp-η C A , precomp-η-is-equiv A-in-P)
     (λ (ca : ○ C → A) →
      Σ-equiv-piecewise _ _ _ _
       (precomp-η C B , (precomp-η-is-equiv B-in-P))
       (λ (cb : ○ C → B) → help ca cb))

    where
     help : (ca : ○ C → A) (cb : ○ C → B) → (f ∘ ca ∼ g ∘ cb) ≃ (f ∘ ca ∘ η C ∼ g ∘ cb ∘ η C)
     help = {!!}

  reflective-subuniverse-closed-under-pullbacks : subuniverse-contains P (Slice.pullback 𝓤 f g)
  reflective-subuniverse-closed-under-pullbacks =
    {!!}


to-point
 : {A : 𝓤 ̇}
 → A
 → 𝟙 {𝓤} → A
to-point a _ = a

id-type-to-pullback
 : (A : 𝓤 ̇)
 → (x y : A)
 → (x ＝ y)
 → Slice.pullback 𝓤 (to-point x) (to-point y)
id-type-to-pullback A x y p = ⋆ , ⋆ , p

id-type-to-pullback-is-equiv
 : (A : 𝓤 ̇)
 → (x y : A)
 → is-equiv (id-type-to-pullback A x y)
pr₁ (pr₁ (id-type-to-pullback-is-equiv A x y)) = pr₂ ∘ pr₂
pr₂ (pr₁ (id-type-to-pullback-is-equiv A x y)) (_ , _ , p) = refl
pr₁ (pr₂ (id-type-to-pullback-is-equiv A x y)) = pr₂ ∘ pr₂
pr₂ (pr₂ (id-type-to-pullback-is-equiv A x y)) p = refl

id-type-to-pullback-equiv
 : (A : 𝓤 ̇)
 → (x y : A)
 → (x ＝ y) ≃ Slice.pullback 𝓤 (to-point x) (to-point y)
pr₁ (id-type-to-pullback-equiv A x y) = id-type-to-pullback A x y
pr₂ (id-type-to-pullback-equiv A x y) = id-type-to-pullback-is-equiv A x y

retract-𝟙-of-○-𝟙 : retract (𝟙 {𝓤}) of ○ 𝟙
pr₁ retract-𝟙-of-○-𝟙 _ = ⋆
pr₁ (pr₂ retract-𝟙-of-○-𝟙) _ = η _ ⋆
pr₂ (pr₂ retract-𝟙-of-○-𝟙) ⋆ = refl

reflective-subuniverse-contains-𝟙
 : (fe : funext 𝓤 𝓤)
 → (P-is-replete : subuniverse-is-replete P)
 → subuniverse-contains P (𝟙 {𝓤})
reflective-subuniverse-contains-𝟙 fe P-is-replete =
  reflective-subuniverse-closed-under-retracts fe P-is-replete (○ 𝟙) 𝟙
   retract-𝟙-of-○-𝟙
   (subuniverse-contains-reflection 𝟙)

reflective-subuniverse-closed-under-id
 : (fe : funext 𝓤 𝓤)
 → (P-is-replete : subuniverse-is-replete P)
 → (A : 𝓤 ̇)
 → (u v : A)
 → (A-in-P : subuniverse-contains P A)
 → subuniverse-contains P (u ＝ v)
reflective-subuniverse-closed-under-id fe P-is-replete A u v A-in-P =
 P-is-replete
  (u ＝ v)
  (Slice.pullback 𝓤 (to-point u) (to-point v))
  (id-type-to-pullback-equiv A u v)
  (Pullbacks.reflective-subuniverse-closed-under-pullbacks fe P-is-replete 𝟙 𝟙 A
   (reflective-subuniverse-contains-𝟙 fe P-is-replete)
   (reflective-subuniverse-contains-𝟙 fe P-is-replete)
   A-in-P
   (to-point u)
   (to-point v))

\end{code}


TODO: try to do this the way it is done in Egbert's thesis. It feels like he has a reasonable proof that reflective subuniverses are closed under pullback (5.1.19) which will then give the main result by repleteness.
