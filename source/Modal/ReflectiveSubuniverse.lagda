Jon Sterling, started 27th Sep 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan
open import UF.Subsingletons
open import UF.Base
open import UF.FunExt
open import UF.Equiv
open import UF.Retracts
open import UF.Embeddings
open import UF.EquivalenceExamples
import Utilities.PairFun as PairFun
import Slice.Slice as Slice

open import Modal.Subuniverse



module Modal.ReflectiveSubuniverse
 (P : subuniverse 𝓤 𝓥)
 (P-is-reflective : subuniverse-is-reflective P)
 where

-- TODO: ripped from MGS, move into UF
sym-is-equiv
 : {𝓤 : Universe}
 → {X : 𝓤 ̇}
 → {x y : X}
 → is-equiv (_⁻¹ {𝓤} {X} {x} {y})
pr₁ (pr₁ sym-is-equiv) = _⁻¹
pr₂ (pr₁ sym-is-equiv) refl = refl
pr₁ (pr₂ sym-is-equiv) = _⁻¹
pr₂ (pr₂ sym-is-equiv) refl = refl

-- TODO: ripped from MGS, move into UF
singleton-equiv-lemma
 : {𝓤 𝓥 : _} {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (x : X)
 → (f : (y : X) → x ＝ y → A y)
 → is-singleton (Σ A)
 → (y : X)
 → is-equiv (f y)
singleton-equiv-lemma {𝓤} {𝓥} {X} {A} x f i = γ
 where
  g : singleton-type x → Σ A
  g = NatΣ f

  e : is-equiv g
  e = maps-of-singletons-are-equivs g (singleton-types-are-singletons x) i

  abstract
   γ : (y : X) → is-equiv (f y)
   γ = NatΣ-equiv-gives-fiberwise-equiv f e

embedding-gives-ap-is-equiv
 : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
 → is-embedding f
 → (x x' : X)
 → is-equiv (ap f {x} {x'})
embedding-gives-ap-is-equiv {𝓤} {𝓥} {X} f e = γ
 where
  d : (x' : X) → (Σ x ꞉ X , f x' ＝ f x) ≃ (Σ x ꞉ X , f x ＝ f x')
  d x' = Σ-cong λ x → _⁻¹ , sym-is-equiv

  s : (x' : X) → is-prop (Σ x ꞉ X , f x' ＝ f x)
  s x' = equiv-to-prop (d x') (e (f x'))

  γ : (x x' : X) → is-equiv (ap f {x} {x'})
  γ x =
   singleton-equiv-lemma x
    (λ x' → ap f {x} {x'})
    (pointed-props-are-singletons (x , refl) (s x))

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

precomp-η-equiv
 : {A B : 𝓤 ̇}
 → subuniverse-contains P B
 → (○ A → B) ≃ (A → B)
pr₁ (precomp-η-equiv B-in-P) = precomp-η _ _
pr₂ (precomp-η-equiv B-in-P) = precomp-η-is-equiv B-in-P

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
pr₁ (η-is-section-gives-is-equiv fe A η-is-section) =
 η-is-section-gives-has-section fe A η-is-section
pr₂ (η-is-section-gives-is-equiv fe A η-is-section) =
 η-is-section

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
   ε (η B x)
    ＝⟨ ap
         (retraction B-retract-of-E)
         (○-rec-compute B E E-in-P (section B-retract-of-E) x) ⟩
   retraction B-retract-of-E (section B-retract-of-E x)
    ＝⟨ retract-condition B-retract-of-E x ⟩
   x ∎

reflective-subuniverse-closed-under-products
 : (fe : funext 𝓤 𝓤)
 → (P-is-replete : subuniverse-is-replete P)
 → (A : 𝓤 ̇)
 → (B : A → 𝓤 ̇)
 → (B-in-P : Π x ꞉ A , subuniverse-contains P (B x))
 → subuniverse-contains P (Π B)
reflective-subuniverse-closed-under-products fe P-is-replete A B B-in-P =
 reflective-subuniverse-closed-under-retracts fe P-is-replete _ _ ret
  (subuniverse-contains-reflection (Π B))
 where
  h : (x : A) → ○ (Π B) → B x
  h x = ○-rec (Π B) (B x) (B-in-P x) (λ f → f x)

  ret : retract Π B of ○ (Π B)
  pr₁ ret f x = h x f
  pr₁ (pr₂ ret) = η (Π B)
  pr₂ (pr₂ ret) f =
   dfunext fe λ x →
   ○-rec-compute (Π B) (B x) (B-in-P x) (λ g → g x) f


homotopy-whisker-η
 : {X Y : 𝓤 ̇}
 → (f g : ○ X → Y)
 → f ∼ g
 → (f ∘ η _) ∼ (g ∘ η _)
homotopy-whisker-η f g h x = h (η _ x)

whisker-η
 : {X Y : 𝓤 ̇}
 → (f g : ○ X → Y)
 → (α : f ＝ g)
 → (f ∘ η _) ＝ (g ∘ η _)
whisker-η f g α =
 ap (precomp-η _ _) α

whisker-η-is-equiv
 : {X Y : 𝓤 ̇}
 → (Y-in-P : subuniverse-contains P Y)
 → (f g : ○ X → Y)
 → is-equiv (whisker-η f g)
whisker-η-is-equiv Y-in-P =
 embedding-gives-ap-is-equiv
  (precomp-η _ _)
  (equivs-are-embeddings
   (precomp-η _ _)
   (precomp-η-is-equiv Y-in-P))


homotopy-whisker-η-is-equiv
 : (fe : funext 𝓤 𝓤)
 → (X Y : 𝓤 ̇)
 → (Y-in-P : subuniverse-contains P Y)
 → (f g : ○ X → Y)
 → is-equiv (homotopy-whisker-η f g)
homotopy-whisker-η-is-equiv fe X Y Y-in-P f g =
 transport
  is-equiv
  composite-is-homotopy-whisker
  composite-is-equiv

 where
  composite : f ∼ g → f ∘ η _ ∼ g ∘ η _
  composite =
   happly' (f ∘ η X) (g ∘ η X)
   ∘ whisker-η f g
   ∘ inverse (happly' f g) (fe f g)

  composite-is-equiv : is-equiv composite
  composite-is-equiv =
   ∘-is-equiv
    (inverses-are-equivs (happly' f g) (fe f g))
    (∘-is-equiv
     (whisker-η-is-equiv Y-in-P f g)
     (fe (f ∘ η X) (g ∘ η X)))

  composite-is-homotopy-whisker : composite ＝ homotopy-whisker-η f g
  composite-is-homotopy-whisker =
   dfunext fe λ h →
   composite h ＝⟨ ap happly (helper h) ⟩
   happly (dfunext fe (λ z → h (η X z))) ＝⟨ happly-funext fe _ _ (h ∘ η X) ⟩
   homotopy-whisker-η f g h ∎

   where
    helper
     : (h : f ∼ g)
     → whisker-η f g (inverse (happly' f g) (fe f g) h) ＝ dfunext fe (h ∘ η X)
    helper h =
     whisker-η f g (inverse (happly' f g) (fe f g) h)
       ＝⟨ ap (λ - → whisker-η f g (- h)) (inverse-happly-is-dfunext fe f g) ⟩
     ap (precomp-η X Y) (dfunext fe h)
       ＝⟨ ap-precomp-funext _ _ (η X) h fe fe ⟩
     dfunext fe (h ∘ η X) ∎



module Pullbacks
 (fe : funext 𝓤 𝓤)
 (P-is-replete : subuniverse-is-replete P)
 (A B X : 𝓤 ̇)
 (A-in-P : subuniverse-contains P A)
 (B-in-P : subuniverse-contains P B)
 (X-in-P : subuniverse-contains P X)
 (f : A → X)
 (g : B → X)
 where

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
   pr₁ restrict-cone-equiv =
    PairFun.pair-fun (precomp-η C A) λ ca →
    PairFun.pair-fun (precomp-η C B) λ cb ϕ x →
    ϕ (η _ x)
   pr₂ restrict-cone-equiv =
    PairFun.pair-fun-is-equiv _ _ (precomp-η-is-equiv A-in-P) λ ca →
    PairFun.pair-fun-is-equiv _ _ (precomp-η-is-equiv B-in-P) λ cb →
    homotopy-whisker-η-is-equiv fe C X X-in-P (f ∘ ca) (g ∘ cb)

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


TODO: try to do this the way it is done in Egbert's thesis. It feels like he has
a reasonable proof that reflective subuniverses are closed under pullback (5.1.19)
 which will then give the main result by repleteness.
