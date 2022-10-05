Jon Sterling, started 27th Sep 2022

Much of this file is based on the proofs from Egbert Rijke's PhD thesis.

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

is-modal : (A : 𝓤 ̇) → 𝓥 ̇
is-modal = subuniverse-contains P

reflection : (A : 𝓤 ̇) → reflection-candidate P A
reflection A = pr₁ (P-is-reflective A)

○-packed : (A : 𝓤 ̇) → subuniverse-member P
○-packed A = pr₁ (reflection A)

○ : 𝓤 ̇ → 𝓤 ̇
○ A = pr₁ (○-packed A)

○-is-modal : (A : 𝓤 ̇) → is-modal (○ A)
○-is-modal A = pr₂ (○-packed A)

η : (A : 𝓤 ̇) → A → ○ A
η A = pr₂ (reflection A)

precomp-η : {𝓥 : _} (A : 𝓤 ̇) (B : 𝓥 ̇) → (○ A → B) → A → B
precomp-η A B f = f ∘ η A

precomp-η-is-equiv
 : {A B : 𝓤 ̇}
 → is-modal B
 → is-equiv (precomp-η A B)
precomp-η-is-equiv B-in-P =
 pr₂ (P-is-reflective _) _ B-in-P

precomp-η-equiv
 : {A B : 𝓤 ̇}
 → is-modal B
 → (○ A → B) ≃ (A → B)
pr₁ (precomp-η-equiv B-in-P) = precomp-η _ _
pr₂ (precomp-η-equiv B-in-P) = precomp-η-is-equiv B-in-P

○-rec
 : (A B : 𝓤 ̇)
 → (B-in-P : is-modal B)
 → (A → B)
 → (○ A → B)
○-rec A B B-in-P =
 inverse _ (precomp-η-is-equiv B-in-P)


○-rec-compute-pointsfree
 : (A B : 𝓤 ̇)
 → (B-in-P : is-modal B)
 → (f : A → B)
 → ○-rec A B B-in-P f ∘ η A ＝ f
○-rec-compute-pointsfree A B B-in-P f =
 inverses-are-sections _ (precomp-η-is-equiv B-in-P) f


○-rec-compute
 : (A B : 𝓤 ̇)
 → (B-in-P : is-modal B)
 → (f : A → B)
 → (x : A)
 → ○-rec A B B-in-P f (η A x) ＝ f x
○-rec-compute A B B-in-P f =
 happly (○-rec-compute-pointsfree _ _ _ _)

abstract
 ○-rec-ext
  : (A B : 𝓤 ̇)
  → (B-in-P : is-modal B)
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
  → (B-in-P : is-modal B)
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
  (○-rec-ext A (○ A) (○-is-modal A) _ _
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

η-is-equiv-gives-is-modal
 : (P-is-replete : subuniverse-is-replete P)
 → (A : 𝓤 ̇)
 → is-equiv (η A)
 → is-modal A
η-is-equiv-gives-is-modal P-is-replete A η-is-equiv =
 P-is-replete _ _
  (η A , η-is-equiv)
  (○-is-modal A)

generic-precomp-η-is-equiv-gives-η-is-section
  : (A : 𝓤 ̇)
  → is-equiv (precomp-η A A)
  → is-section (η A)
pr₁ (generic-precomp-η-is-equiv-gives-η-is-section A h) =
 inverse _ h id
pr₂ (generic-precomp-η-is-equiv-gives-η-is-section A h) =
 happly (inverses-are-sections _ h id)

generic-precomp-η-is-equiv-gives-η-is-equiv
  : (fe : funext 𝓤 𝓤)
  → (A : 𝓤 ̇)
  → is-equiv (precomp-η A A)
  → is-equiv (η A)
generic-precomp-η-is-equiv-gives-η-is-equiv fe A h =
 η-is-section-gives-is-equiv fe A
  (generic-precomp-η-is-equiv-gives-η-is-section A h)

retracts-of-modal-types-are-modal
 : (fe : funext 𝓤 𝓤)
 → (P-is-replete : subuniverse-is-replete P)
 → (E B : 𝓤 ̇)
 → retract B of E
 → is-modal E
 → is-modal B
retracts-of-modal-types-are-modal fe P-is-replete E B B-retract-of-E E-in-P =
 η-is-equiv-gives-is-modal P-is-replete B
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
 → (B-in-P : Π x ꞉ A , is-modal (B x))
 → is-modal (Π B)
reflective-subuniverse-closed-under-products fe P-is-replete A B B-in-P =
 retracts-of-modal-types-are-modal fe P-is-replete _ _ ret
  (○-is-modal (Π B))
 where
  h : (x : A) → ○ (Π B) → B x
  h x = ○-rec (Π B) (B x) (B-in-P x) (λ f → f x)

  ret : retract Π B of ○ (Π B)
  pr₁ ret f x = h x f
  pr₁ (pr₂ ret) = η (Π B)
  pr₂ (pr₂ ret) f =
   dfunext fe λ x →
   ○-rec-compute (Π B) (B x) (B-in-P x) (λ g → g x) f


homotopy-pre-whisker
  : {U X Y : 𝓤 ̇}
  → (f g : X → Y)
  → (i : U → X)
  → f ∼ g
  → f ∘ i ∼ g ∘ i
homotopy-pre-whisker f g i h =
 h ∘ i

homotopy-pre-whisker-is-equiv
 : (fe : funext 𝓤 𝓤)
 → {U X Y : 𝓤 ̇}
 → (f g : X → Y)
 → (i : U → X)
 → (precomp-i-is-emb : is-embedding λ (- : X → Y) → - ∘ i)
 → is-equiv (homotopy-pre-whisker f g i)
homotopy-pre-whisker-is-equiv fe f g i precomp-i-is-emb =
 transport is-equiv composite-is-pre-whisker (eqtofun- composite)

 where
  composite : f ∼ g ≃ (f ∘ i ∼ g ∘ i)
  composite =
   ≃-sym (≃-funext fe f g)
    ● (ap (_∘ i) , embedding-gives-ap-is-equiv _ precomp-i-is-emb f g)
    ● ≃-funext fe (f ∘ i) (g ∘ i)

  composite-is-pre-whisker : eqtofun composite ＝ homotopy-pre-whisker f g i
  composite-is-pre-whisker =
   dfunext fe λ h →
   eqtofun composite h ＝⟨ ap happly (aux h) ⟩
   happly (dfunext fe (h ∘ i)) ＝⟨ happly-funext fe _ _ (h ∘ i) ⟩
   homotopy-pre-whisker f g i h ∎

   where
    aux : (h : f ∼ g) → ap (_∘ i) (inverse _ (fe f g) h) ＝ dfunext fe (h ∘ i)
    aux h =
     ap (_∘ i) (inverse (happly' f g) (fe f g) h)
      ＝⟨ ap (λ - → ap (_∘ i) (- h)) (inverse-happly-is-dfunext fe f g) ⟩
     ap (_∘ i) (dfunext fe h)
      ＝⟨ ap-precomp-funext _ _ i h fe fe ⟩
     dfunext fe (h ∘ i) ∎

homotopy-whisker-η-is-equiv
 : (fe : funext 𝓤 𝓤)
 → (X Y : 𝓤 ̇)
 → (Y-in-P : is-modal Y)
 → (f g : ○ X → Y)
 → is-equiv (homotopy-pre-whisker f g (η _))
homotopy-whisker-η-is-equiv fe X Y Y-in-P f g =
 homotopy-pre-whisker-is-equiv fe f g (η _)
  (equivs-are-embeddings
   (precomp-η X Y)
   (precomp-η-is-equiv Y-in-P))

private
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

module _ (fe : funext 𝓤 𝓤) (P-is-replete : subuniverse-is-replete P) where
 𝟙-is-modal : is-modal (𝟙 {𝓤})
 𝟙-is-modal =
   retracts-of-modal-types-are-modal fe P-is-replete (○ 𝟙) 𝟙
    retract-𝟙-of-○-𝟙
    (○-is-modal 𝟙)

 pullbacks-of-modal-types-are-modal
  : (A B X : 𝓤 ̇)
  → (A-modal : is-modal A)
  → (B-modal : is-modal B)
  → (X-modal : is-modal X)
  → (f : A → X)
  → (g : B → X)
  → is-modal (Slice.pullback 𝓤 f g)
 pullbacks-of-modal-types-are-modal A B X A-modal B-modal X-modal f g =
  η-is-equiv-gives-is-modal P-is-replete C
   (generic-precomp-η-is-equiv-gives-η-is-equiv fe C
    (eqtofun-
     (cone-map-equiv (○ C)
      ● restrict-cone-equiv
      ● ≃-sym (cone-map-equiv C))))

  where
   C : 𝓤 ̇
   C = Slice.pullback 𝓤 f g

   cone : 𝓤 ̇ → 𝓤 ̇
   cone Z = Slice.to-span 𝓤 f g Z

   cone-map-equiv : (Z : 𝓤 ̇) → (Z → C) ≃ cone Z
   cone-map-equiv Z = Slice.→-pullback-≃ 𝓤 f g Z fe

   restrict-cone-equiv : cone (○ C) ≃ cone C
   pr₁ restrict-cone-equiv =
    PairFun.pair-fun (precomp-η C A) λ ca →
    PairFun.pair-fun (precomp-η C B) λ cb ϕ x →
    ϕ (η _ x)
   pr₂ restrict-cone-equiv =
    PairFun.pair-fun-is-equiv _ _ (precomp-η-is-equiv A-modal) λ ca →
    PairFun.pair-fun-is-equiv _ _ (precomp-η-is-equiv B-modal) λ cb →
    homotopy-whisker-η-is-equiv fe C X X-modal (f ∘ ca) (g ∘ cb)

 id-types-of-modal-types-are-modal
  : (A : 𝓤 ̇)
  → (u v : A)
  → (A-modal : is-modal A)
  → is-modal (u ＝ v)
 id-types-of-modal-types-are-modal A u v A-modal =
  P-is-replete
   (u ＝ v)
   (Slice.pullback 𝓤 (to-point u) (to-point v))
   (id-type-to-pullback-equiv A u v)
   (pullbacks-of-modal-types-are-modal 𝟙 𝟙 A
    𝟙-is-modal
    𝟙-is-modal
    A-modal
    (to-point u)
    (to-point v))

\end{code}
