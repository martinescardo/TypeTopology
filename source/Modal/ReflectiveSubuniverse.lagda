Jon Sterling, started 27th Sep 2022

Much of this file is based on the proofs from Egbert Rijke's PhD thesis.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt
open import UF.Equiv
open import UF.Retracts
open import UF.Embeddings
import UF.PairFun as PairFun
import Slice.Construction as Slice

open import Modal.Subuniverse
open import Modal.Homotopy

module Modal.ReflectiveSubuniverse
 (P : subuniverse 𝓤 𝓥)
 (P-is-reflective : subuniverse-is-reflective P)
 where

is-modal : (A : 𝓤 ̇ )→ 𝓥 ̇
is-modal = subuniverse-contains P

reflection : (A : 𝓤 ̇ )→ reflection-candidate P A
reflection A = pr₁ (P-is-reflective A)

○-packed : (A : 𝓤 ̇ )→ subuniverse-member P
○-packed A = pr₁ (reflection A)

○ : 𝓤 ̇ → 𝓤 ̇
○ A = pr₁ (○-packed A)

○-is-modal : (A : 𝓤 ̇ )→ is-modal (○ A)
○-is-modal A = pr₂ (○-packed A)

η : (A : 𝓤 ̇ )→ A → ○ A
η A = pr₂ (reflection A)

precomp-η : {𝓥 : _} (A : 𝓤 ̇ )(B : 𝓥 ̇ )→ (○ A → B) → A → B
precomp-η A B f = f ∘ η A

precomp-η-is-equiv
 : {A B : 𝓤 ̇ }
 → is-modal B
 → is-equiv (precomp-η A B)
precomp-η-is-equiv =
 pr₂ (P-is-reflective _) _

precomp-η-equiv
 : {A B : 𝓤 ̇ }
 → is-modal B
 → (○ A → B) ≃ (A → B)
pr₁ (precomp-η-equiv B-modal) =
 precomp-η _ _
pr₂ (precomp-η-equiv B-modal) =
 precomp-η-is-equiv B-modal

○-rec
 : (A B : 𝓤 ̇ )
 → (B-modal : is-modal B)
 → (A → B)
 → (○ A → B)
○-rec A B B-modal =
 inverse _ (precomp-η-is-equiv B-modal)

○-rec-compute-pointsfree
 : (A B : 𝓤 ̇ )
 → (B-modal : is-modal B)
 → (f : A → B)
 → ○-rec A B B-modal f ∘ η A ＝ f
○-rec-compute-pointsfree A B B-modal f =
 inverses-are-sections _ (precomp-η-is-equiv B-modal) f

○-rec-compute
 : (A B : 𝓤 ̇ )
 → (B-modal : is-modal B)
 → (f : A → B)
 → (x : A)
 → ○-rec A B B-modal f (η A x) ＝ f x
○-rec-compute A B B-modal f =
 happly (○-rec-compute-pointsfree _ _ _ _)

○-rec-ext
 : (A B : 𝓤 ̇ )
 → (B-modal : is-modal B)
 → (f g : ○ A → B)
 → (f ∘ η A) ＝ (g ∘ η A)
 → f ＝ g
○-rec-ext A B B-modal f g fgη =
 H f ⁻¹ ∙ ap (○-rec A B B-modal) fgη ∙ H g
 where
  H : inverse (precomp-η A B) (precomp-η-is-equiv B-modal) ∘ precomp-η A B ∼ id
  H = inverses-are-retractions _ (precomp-η-is-equiv B-modal)

○-rec-ext-beta
 : (A B : 𝓤 ̇ )
 → (B-modal : is-modal B)
 → (f : ○ A → B)
 → ○-rec-ext A B B-modal f f refl ＝ refl
○-rec-ext-beta A B B-modal f =
   (H f ⁻¹ ∙ H f) ＝⟨ (sym-is-inverse (H f)) ⁻¹ ⟩
   refl ∎

 where
  H : inverse (precomp-η A B) (precomp-η-is-equiv B-modal) ∘ precomp-η A B ∼ id
  H = inverses-are-retractions _ (precomp-η-is-equiv B-modal)



η-is-section-gives-has-section
 : (fe : funext 𝓤 𝓤)
 → (A : 𝓤 ̇ )
 → is-section (η A)
 → has-section (η A)
pr₁ (η-is-section-gives-has-section fe A η-is-section) =
 pr₁ η-is-section
pr₂ (η-is-section-gives-has-section fe A η-is-section) =
 happly
  (○-rec-ext A (○ A) (○-is-modal A) _ _
    (dfunext fe λ x →
     η A (pr₁ η-is-section (η A x)) ＝⟨ ap (η A) (pr₂ η-is-section x) ⟩
     η A x ∎))

η-is-section-gives-is-equiv
 : (fe : funext 𝓤 𝓤)
 → (A : 𝓤 ̇ )
 → is-section (η A)
 → is-equiv (η A)
pr₁ (η-is-section-gives-is-equiv fe A η-is-section) =
 η-is-section-gives-has-section fe A η-is-section
pr₂ (η-is-section-gives-is-equiv fe A η-is-section) =
 η-is-section

η-is-equiv-gives-is-modal
 : (P-is-replete : subuniverse-is-replete P)
 → (A : 𝓤 ̇ )
 → is-equiv (η A)
 → is-modal A
η-is-equiv-gives-is-modal P-is-replete A η-is-equiv =
 P-is-replete _ _
  (η A , η-is-equiv)
  (○-is-modal A)

generic-precomp-η-is-equiv-gives-η-is-section
 : (A : 𝓤 ̇ )
 → is-equiv (precomp-η A A)
 → is-section (η A)
pr₁ (generic-precomp-η-is-equiv-gives-η-is-section A h) =
 inverse _ h id
pr₂ (generic-precomp-η-is-equiv-gives-η-is-section A h) =
 happly (inverses-are-sections _ h id)

\end{code}

The converse of η-is-equiv-gives-is-modal, added 10 January 2025 by Tom de Jong.

\begin{code}

is-modal-gives-η-is-equiv : funext 𝓤 𝓤 → (A : 𝓤 ̇ ) → is-modal A → is-equiv (η A)
is-modal-gives-η-is-equiv fe A A-modal =
 η-is-section-gives-is-equiv fe A
  (generic-precomp-η-is-equiv-gives-η-is-section A (precomp-η-is-equiv A-modal))

\end{code}

The following is Lemma 5.1.18 of Egbert Rijke's thesis.

\begin{code}
module _ (fe : funext 𝓤 𝓤) (X Y : 𝓤 ̇ )(Y-modal : is-modal Y) (f g : ○ X → Y) where
 homotopy-precomp-η-is-equiv : is-equiv (homotopy-precomp f g (η _))
 homotopy-precomp-η-is-equiv =
  homotopy-precomp-by-embedding-is-equiv fe fe fe fe f g (η _)
   (equivs-are-embeddings
    (precomp-η X Y)
    (precomp-η-is-equiv Y-modal))

 homotopy-precomp-η-equiv : (f ∼ g) ≃ (f ∘ η _ ∼ g ∘ η _)
 pr₁ (homotopy-precomp-η-equiv) = homotopy-precomp f g (η _)
 pr₂ (homotopy-precomp-η-equiv) = homotopy-precomp-η-is-equiv
\end{code}

Here we prove that identity types can be constructed by pullback; this will be
useful later when we establish closure of modal types under identity types
using closure of modal types under pullbacks.

\begin{code}
module _ (A : 𝓤 ̇ )(x y : A) where
 private
  [x] [y] : 𝟙{𝓤} → A
  [x] _ = x
  [y] _ = y

 id-type-as-pullback : 𝓤 ̇
 id-type-as-pullback = Slice.pullback 𝓤 [x] [y]

 id-type-to-pullback : x ＝ y → id-type-as-pullback
 id-type-to-pullback p = ⋆ , ⋆ , p

 pullback-to-id-type : id-type-as-pullback → x ＝ y
 pullback-to-id-type (_ , _ , p) = p

 id-type-to-pullback-is-equiv : is-equiv id-type-to-pullback
 pr₁ id-type-to-pullback-is-equiv = pullback-to-id-type , λ _ → refl
 pr₂ id-type-to-pullback-is-equiv = pullback-to-id-type , λ _ → refl

 id-type-to-pullback-equiv : (x ＝ y) ≃ id-type-as-pullback
 pr₁ id-type-to-pullback-equiv = id-type-to-pullback
 pr₂ id-type-to-pullback-equiv = id-type-to-pullback-is-equiv
\end{code}

\begin{code}
retract-𝟙-of-○-𝟙 : retract (𝟙 {𝓤}) of ○ 𝟙
pr₁ retract-𝟙-of-○-𝟙 _ = ⋆
pr₁ (pr₂ retract-𝟙-of-○-𝟙) _ = η _ ⋆
pr₂ (pr₂ retract-𝟙-of-○-𝟙) ⋆ = refl
\end{code}


We establish the closure conditions of modal types; every such lemma requires
both function extensionality and repleteness of the subuniverse.

\begin{code}
module _ (fe : funext 𝓤 𝓤) (P-is-replete : subuniverse-is-replete P) where
 retracts-of-modal-types-are-modal
  : (E B : 𝓤 ̇ )
  → retract B of E
  → is-modal E
  → is-modal B
 retracts-of-modal-types-are-modal E B B-retract-of-E E-modal =
  η-is-equiv-gives-is-modal P-is-replete B
   (η-is-section-gives-is-equiv fe B η-is-section)
  where
   B-to-E : B → E
   B-to-E = section B-retract-of-E

   E-to-B : E → B
   E-to-B = retraction B-retract-of-E

   h : ○ B → E
   h = ○-rec B E E-modal B-to-E

   ε : ○ B → B
   ε = E-to-B ∘ h

   η-is-section : is-section (η B)
   pr₁ η-is-section = ε
   pr₂ η-is-section x =
    ε (η B x) ＝⟨ ap E-to-B (○-rec-compute B E E-modal B-to-E x) ⟩
    E-to-B (B-to-E x) ＝⟨ retract-condition B-retract-of-E x ⟩
    x ∎

 𝟙-is-modal : is-modal (𝟙 {𝓤})
 𝟙-is-modal =
  retracts-of-modal-types-are-modal (○ 𝟙) 𝟙
   retract-𝟙-of-○-𝟙
   (○-is-modal 𝟙)

 products-of-modal-types-are-modal
  : (A : 𝓤 ̇ )
  → (B : A → 𝓤 ̇ )
  → (B-modal : Π x ꞉ A , is-modal (B x))
  → is-modal (Π B)
 products-of-modal-types-are-modal A B B-modal =
  retracts-of-modal-types-are-modal _ _ ret (○-is-modal (Π B))
  where
   h : (x : A) → ○ (Π B) → B x
   h x = ○-rec (Π B) (B x) (B-modal x) (λ - → - x)

   ret : retract Π B of ○ (Π B)
   pr₁ ret f x = h x f
   pr₁ (pr₂ ret) = η (Π B)
   pr₂ (pr₂ ret) f =
    dfunext fe λ x →
    ○-rec-compute (Π B) (B x) (B-modal x) (λ - → - x) f

 pullbacks-of-modal-types-are-modal
  : (A B X : 𝓤 ̇ )
  → (A-modal : is-modal A)
  → (B-modal : is-modal B)
  → (X-modal : is-modal X)
  → (f : A → X)
  → (g : B → X)
  → is-modal (Slice.pullback 𝓤 f g)
 pullbacks-of-modal-types-are-modal A B X A-modal B-modal X-modal f g =
  η-is-equiv-gives-is-modal P-is-replete C
   (η-is-section-gives-is-equiv fe C
    (generic-precomp-η-is-equiv-gives-η-is-section C
     (eqtofun-
      (cone-map-equiv (○ C)
       ● restrict-cone-equiv
       ● ≃-sym (cone-map-equiv C)))))

  where
   C : 𝓤 ̇
   C = Slice.pullback 𝓤 f g

   cone : 𝓤 ̇ → 𝓤 ̇
   cone Z = Slice.to-span 𝓤 f g Z

   cone-map-equiv : (Z : 𝓤 ̇ )→ (Z → C) ≃ cone Z
   cone-map-equiv Z = Slice.→-pullback-≃ 𝓤 f g Z fe

   restrict-cone-equiv : cone (○ C) ≃ cone C
   restrict-cone-equiv =
    PairFun.pair-fun-equiv (precomp-η-equiv A-modal) λ hA →
    PairFun.pair-fun-equiv (precomp-η-equiv B-modal) λ hB →
    homotopy-precomp-η-equiv fe C X X-modal (f ∘ hA) (g ∘ hB)

 id-types-of-modal-types-are-modal
  : (A : 𝓤 ̇ )
  → (u v : A)
  → (A-modal : is-modal A)
  → is-modal (u ＝ v)
 id-types-of-modal-types-are-modal A u v A-modal =
  P-is-replete
   (u ＝ v)
   (id-type-as-pullback A u v)
   (id-type-to-pullback-equiv A u v)
   (pullbacks-of-modal-types-are-modal 𝟙 𝟙 A 𝟙-is-modal 𝟙-is-modal A-modal _ _)

\end{code}
