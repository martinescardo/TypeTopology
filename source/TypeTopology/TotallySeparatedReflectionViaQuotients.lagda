Martin Escardo, 24 June 2026.

In the module TypeTopology.TotallySeparated we construct the totally
separated reflection of a type X as the image of the evaluation map
X → ((X → 𝟚) → 𝟚).

An alternative construction, developed here, is given by the set-quotient
of X by the equivalence relation

  x ＝₂ y := (p : X → 𝟚) → p x ＝ p y.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import Quotient.Type

module TypeTopology.TotallySeparatedReflectionViaQuotients
        (fe : FunExt)
        (pt : propositional-truncations-exist)
        (sq : set-quotients-exist)
       where

open import MLTT.Spartan
open import MLTT.Two-Properties
open import TypeTopology.TotallySeparated
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.ImageAndSurjection pt
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open PropositionalTruncation pt
open general-set-quotients-exist sq
open totally-separated-reflection fe pt

private
 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

＝₂-eqrel : {X : 𝓤 ̇ } → EqRel {𝓤} {𝓤} X
＝₂-eqrel = _＝₂_ ,
           (λ x y → Π-is-prop fe' (λ _ → 𝟚-is-set)) ,
           (λ x p → refl) ,
           (λ x y e p → (e p)⁻¹) ,
           (λ x y z e d p → e p ∙ d p)

𝕋₂ : 𝓤 ̇ → 𝓤 ̇
𝕋₂ X = X / ＝₂-eqrel

τ : {X : 𝓤 ̇ } → X → 𝕋₂ X
τ = η/ ＝₂-eqrel

τ-identifies-＝₂ : {X : 𝓤 ̇ } {x y : X}
                 → x ＝₂ y → τ x ＝ τ y
τ-identifies-＝₂ = η/-identifies-related-points ＝₂-eqrel

𝕋₂-is-set : {X : 𝓤 ̇ } → is-set (𝕋₂ X)
𝕋₂-is-set = /-is-set ＝₂-eqrel

τ-is-surjection : {X : 𝓤 ̇ } → is-surjection (τ {𝓤} {X})
τ-is-surjection = η/-is-surjection ＝₂-eqrel pt

\end{code}

Every map into a totally separated type respects ＝₂.

\begin{code}

maps-into-ts-identify-related-points : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                                     → is-totally-separated A
                                     → (f : X → A)
                                     → ({x x' : X} → x ＝₂ x' → f x ＝ f x')
maps-into-ts-identify-related-points ts f e = ts (λ p → e (p ∘ f))

\end{code}

The universal property says that for any totally separated type A, the
restriction map _∘ τ : (𝕋₂ X → A) → (X → A) is an equivalence.

The extension of f : X → A along τ is the unique extension given by the
quotient universal property, which applies because A is totally
separated (hence f respects ＝₂).

\begin{code}

private
 ts-types-are-sets : {A : 𝓥 ̇ } → is-totally-separated A → is-set A
 ts-types-are-sets {𝓥} {A} ts = totally-separated-types-are-sets fe' A ts

extension : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
          → is-totally-separated A
          → (X → A) → (𝕋₂ X → A)
extension {𝓤} {𝓥} {X} {A} ts f =
 ∃!-witness
  (/-universality ＝₂-eqrel (ts-types-are-sets ts) f
    (maps-into-ts-identify-related-points ts f))

extension-property : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                   → (ts  : is-totally-separated A)
                   → (f : X → A)
                   → extension ts f ∘ τ ∼ f
extension-property ts f =
 ∃!-is-witness
  (/-universality ＝₂-eqrel (ts-types-are-sets ts) f
    (maps-into-ts-identify-related-points ts f))

\end{code}

We now show that the quotient type 𝕋₂ X is totally separated.  Given
two points u v : 𝕋₂ X with all 𝟚-valued maps agreeing on them, we use
the surjectivity of τ to get preimages x and y, and then show that
x ＝₂ y by extending each p : X → 𝟚 along τ.

\begin{code}

𝕋₂-is-totally-separated : {X : 𝓤 ̇ } → is-totally-separated (𝕋₂ X)
𝕋₂-is-totally-separated {𝓤} {X} {u} {v} e₂ = III
 where
  _ : u ＝₂ v
  _ = e₂

  ε : (X → 𝟚) → 𝕋₂ X → 𝟚
  ε = extension 𝟚-is-totally-separated

  I : (x y : X) → τ x ＝ u → τ y ＝ v → x ＝₂ y
  I x y ex ey p =
   p x       ＝⟨ (extension-property 𝟚-is-totally-separated p x)⁻¹ ⟩
   ε p (τ x) ＝⟨ ap (ε p) ex ⟩
   ε p u     ＝⟨ e₂ (ε p) ⟩
   ε p v     ＝⟨ ap (ε p) (ey ⁻¹) ⟩
   ε p (τ y) ＝⟨ extension-property 𝟚-is-totally-separated p y ⟩
   p y       ∎

  II : (Σ x ꞉ X , τ x ＝ u) → (Σ y ꞉ X , τ y ＝ v) → u ＝ v
  II (x , ex) (y , ey) =
   u   ＝⟨ ex ⁻¹ ⟩
   τ x ＝⟨ τ-identifies-＝₂ (I x y ex ey) ⟩
   τ y ＝⟨ ey ⟩
   v   ∎

  III : u ＝ v
  III = ∥∥-rec₂ 𝕋₂-is-set II (τ-is-surjection u) (τ-is-surjection v)

extension-of-restriction : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                         → (ts  : is-totally-separated A)
                         → (g : 𝕋₂ X → A)
                         → extension ts (g ∘ τ) ＝ g
extension-of-restriction ts g =
 ap pr₁
    (∃!-uniqueness
      (/-universality ＝₂-eqrel (ts-types-are-sets ts) (g ∘ τ)
        (maps-into-ts-identify-related-points ts (g ∘ τ)))
      g (λ x → refl))

universal-property : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                   → is-totally-separated A
                   → (𝕋₂ X → A) ≃ (X → A)
universal-property ts = qinveq (_∘ τ)
                         (extension ts ,
                          extension-of-restriction ts ,
                          (λ f → dfunext fe' (extension-property ts f)))


\end{code}

We now record the comparison maps between 𝕋 X (the image construction)
and 𝕋₂ X (the quotient construction). Each one is the unique map given
by the universal property of the other.

\begin{code}

module comparison {X : 𝓤 ̇ } where

 c : 𝕋 X → 𝕋₂ X
 c = extᵀ 𝕋₂-is-totally-separated τ

 c-triangle : c ∘ ηᵀ ∼ τ
 c-triangle = ext-ηᵀ 𝕋₂-is-totally-separated τ

 𝕋-is-set : is-set (𝕋 X)
 𝕋-is-set = totally-separated-types-are-sets fe' (𝕋 X) 𝕋-is-totally-separated

 c⁻¹ : 𝕋₂ X → 𝕋 X
 c⁻¹ = extension 𝕋-is-totally-separated ηᵀ

 c⁻¹-triangle : c⁻¹ ∘ τ ∼ ηᵀ
 c⁻¹-triangle = extension-property 𝕋-is-totally-separated ηᵀ

 c-is-section : c⁻¹ ∘ c ∼ id
 c-is-section = ηᵀ-induction _ (λ _ → 𝕋-is-set) (λ x →
  c⁻¹ (c (ηᵀ x)) ＝⟨ ap c⁻¹ (c-triangle x) ⟩
  c⁻¹ (τ x)      ＝⟨ c⁻¹-triangle x ⟩
  ηᵀ x           ∎)

 c-is-retraction : c ∘ c⁻¹ ∼ id
 c-is-retraction = surjection-induction τ τ-is-surjection _ (λ _ → 𝕋₂-is-set {𝓤} {X}) (λ x →
  c (c⁻¹ (τ x)) ＝⟨ ap c (c⁻¹-triangle x) ⟩
  c (ηᵀ x)      ＝⟨ c-triangle x ⟩
  τ x           ∎)

 𝕋-≃-𝕋₂ : 𝕋 X ≃ 𝕋₂ X
 𝕋-≃-𝕋₂ = qinveq c (c⁻¹ , c-is-section , c-is-retraction)

\end{code}
