Todd Waugh Ambridge, 22 May 2020

This gives a structured identity principle for
 * midpoint algebras,
 * convex bodies,
 * interval objects,
with each building on the last.

The defintions for these are found in Escardo-Simpson-LICS2001.

For each structure we define a standard notion of structure (SNS),
which gives rise to an equivalence type for the structure.
We then show that this equivalence characterizes the identity type
for the structure.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt

module TWA.SIP-IntervalObject {𝓤 : Universe} (fe' : FunExt) where

fe : funext 𝓥 𝓦
fe {𝓥} {𝓦} = fe' 𝓥 𝓦

open import TWA.Escardo-Simpson-LICS2001 fe'
open import UF.Base
open import UF.Equiv
open import UF.SIP
open import UF.SIP-Examples
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons-FunExt
open import UF.Univalence

open sip
open sip-with-axioms

\end{code}

(1) Midpoint Algebras.

\begin{code}

midpoint-algebra-structure : 𝓤 ̇ → 𝓤 ̇
midpoint-algebra-structure X = Σ (midpoint-algebra-axioms X)

midpoint-algebra : 𝓤 ⁺ ̇
midpoint-algebra = Σ (midpoint-algebra-structure)

midpoint-algebra-prop : {X : 𝓤 ̇ } (_⊕_ : X → X → X)
                      → is-set X
                      → is-prop (midpoint-algebra-axioms X _⊕_)
midpoint-algebra-prop _⊕_ i = ×-is-prop
                                (being-set-is-prop fe)
                                (×-is-prop
                                  (Π-is-prop fe (λ x → i {x ⊕ x} {x}))
                                  (×-is-prop
                                    (Π-is-prop fe
                                      (λ x → Π-is-prop fe
                                      (λ y → i {x ⊕ y} {y ⊕ x})))
                                    (Π-is-prop fe
                                      (λ x → Π-is-prop fe
                                      (λ y → Π-is-prop fe
                                      (λ w → Π-is-prop fe
                                      (λ z → i {(x ⊕ y) ⊕ (w ⊕ z)}
                                               {(x ⊕ w) ⊕ (y ⊕ z)})))))))

midpoint-algebra-sns : SNS midpoint-algebra-structure 𝓤
midpoint-algebra-sns = add-axioms midpoint-algebra-axioms s
                                  ∞-magma.sns-data
  where
   s : (X : 𝓤 ̇ ) (_⊕_ : X → X → X) → is-prop (midpoint-algebra-axioms X _⊕_)
   s X _⊕_ (i , p) = midpoint-algebra-prop _⊕_ i (i , p)

_≊⟨midpoint-algebra⟩_ : midpoint-algebra → midpoint-algebra → 𝓤 ̇
(X , _⊕_ , _) ≊⟨midpoint-algebra⟩ (Y , _⊗_ , _)
 = Σ f ꞉ (X → Y) , is-equiv f
                 × ((λ x y → f (x ⊕ y)) ＝ (λ x y → f x ⊗ f y))

characterization-of-midpoint-algebra-＝ : is-univalent 𝓤
                                       → (A B : midpoint-algebra)
                                       → (A ＝ B) ≃ (A ≊⟨midpoint-algebra⟩ B)
characterization-of-midpoint-algebra-＝ ua = characterization-of-＝ ua
                                            midpoint-algebra-sns

\end{code}

(2) Convex bodies.

\begin{code}

convex-body-structure : 𝓤 ̇ → 𝓤 ̇
convex-body-structure X = Σ (convex-body-axioms X)

convex-body : 𝓤 ⁺ ̇
convex-body = Σ (convex-body-structure)

full-iterative-uniqueness : (A : 𝓤 ̇ ) → (_⊕_ : A → A → A)
                          → is-set A
                          → (F M : iterative _⊕_)
                          → F ＝ M
full-iterative-uniqueness A _⊕_ i M₁-iterative M₂-iterative
   = to-subtype-＝
     (λ M → ×-is-prop
             (Π-is-prop fe (λ a → i {M a} {a 0 ⊕ M (a ∘ succ)}))
             (Π-is-prop fe (λ a → Π-is-prop fe
                           (λ x → Π-is-prop fe
                           (λ _ → i {a 0} {M x})))))
     (iterative-uniqueness _⊕_ M₁-iterative M₂-iterative)

convex-body-prop : (X : 𝓤 ̇ ) (_⊕_ : X → X → X)
                 → is-prop (convex-body-axioms X _⊕_)
convex-body-prop X _⊕_ ((i , p) , q) = γ ((i , p) , q)
  where
    γ : is-prop (convex-body-axioms X _⊕_)
    γ = ×-is-prop
          (midpoint-algebra-prop _⊕_ i)
          (×-is-prop
            (Π-is-prop fe
              (λ x → Π-is-prop fe
              (λ y → Π-is-prop fe
              (λ _ → Π-is-prop fe
              (λ _ → i {x} {y})))))
            (full-iterative-uniqueness X _⊕_ i))

convex-body-sns : SNS convex-body-structure 𝓤
convex-body-sns = add-axioms convex-body-axioms
                             convex-body-prop
                             ∞-magma.sns-data

_≊⟨convex-body⟩_ : convex-body → convex-body → 𝓤 ̇
(X , _⊕_ , mx , _) ≊⟨convex-body⟩ (Y , _⊗_ , my , _)
 = (X , _⊕_ , mx) ≊⟨midpoint-algebra⟩ (Y , _⊗_ , my)

characterization-of-convex-body-＝ : is-univalent 𝓤
                                  → (A B : convex-body)
                                  → (A ＝ B) ≃ (A ≊⟨convex-body⟩ B)
characterization-of-convex-body-＝ ua = characterization-of-＝ ua
                                       convex-body-sns

\end{code}

(3) Interval Objects.

\begin{code}

interval-object-axioms : (𝓥 : Universe)
                       → (X : 𝓤 ̇ ) → (X → X → X) × X × X → 𝓤 ⊔ 𝓥 ⁺ ̇
interval-object-axioms 𝓥 X (_⊕_ , u , v)
 = Σ 𝓘 ꞉ convex-body-axioms X _⊕_ , is-interval-object (X , _⊕_ , 𝓘) 𝓥 u v

interval-object-structure : (𝓥 : Universe) → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ⁺ ̇
interval-object-structure 𝓥 X = Σ (interval-object-axioms 𝓥 X)

interval-object : (𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
interval-object 𝓥 = Σ (interval-object-structure 𝓥)

interval-axioms-prop : (𝓥 : Universe) → (X : 𝓤 ̇ )
                     → (_⊕_uv : (X → X → X) × X × X)
                     → is-set X
                     → is-prop (interval-object-axioms 𝓥 X _⊕_uv)
interval-axioms-prop 𝓥 X (_⊕_ , u , v) i
 = ×-is-prop
     (convex-body-prop X _⊕_)
     (Π-is-prop fe
       (λ _ → Π-is-prop fe
       (λ _ → Π-is-prop fe
       (λ _ → being-singleton-is-prop fe)))) -- exists unique is prop

open sip-join

interval-object-sns : (𝓥 : Universe) → SNS (interval-object-structure 𝓥) 𝓤
interval-object-sns 𝓥 = add-axioms (interval-object-axioms 𝓥) s
                          (join ∞-magma.sns-data
                            (join pointed-type.sns-data
                                  pointed-type.sns-data))
 where
  s : (X : 𝓤 ̇ ) (s : (X → X → X) × X × X)
    → is-prop (interval-object-axioms 𝓥 X s)
  s X _⊕_uv (((i , p) , q) , r)
    = interval-axioms-prop 𝓥 X _⊕_uv i (((i , p) , q) , r)

_≊⟨interval-object⟩_ : {𝓥 : Universe}
                     → interval-object 𝓥 → interval-object 𝓥 → 𝓤 ̇
(X , (_⊕_ , u , v) , _)  ≊⟨interval-object⟩ (Y , (_⊗_ , s , t) , _)
 = Σ f ꞉ (X → Y) , is-equiv f
                 × (((λ x y → f (x ⊕ y)) ＝ (λ x y → f x ⊗ f y)))
                 × (f u ＝ s) × (f v ＝ t)

characterization-of-interval-object-＝ : {𝓥 : Universe} → is-univalent 𝓤
                                      → (A B : interval-object 𝓥)
                                      → (A ＝ B) ≃ (A ≊⟨interval-object⟩ B)
characterization-of-interval-object-＝ {𝓥} ua = characterization-of-＝ ua
                                               (interval-object-sns 𝓥)

all-interval-objects-equiv : (A B : interval-object 𝓤) → A ≊⟨interval-object⟩ B
all-interval-objects-equiv (X , (_⊕_ , u , v) , p , up) (Y , (_⊗_ , s , t) , p' , up')
 = h , ((h' , happly h∘h'＝id) , (h' , happly h'∘h＝id))
 , dfunext fe (λ x → dfunext fe (λ y → hᵢ x y)) , hₗ , hᵣ
 where
  hX→Y! : ∃! (λ h → (h u ＝ s) × (h v ＝ t) × ((a b : X) → h (a ⊕ b) ＝ h a ⊗ h b))
  hX→Y! = up (Y , _⊗_ , p') s t
  hY→X! : ∃! (λ h → (h s ＝ u) × (h t ＝ v) × ((a b : Y) → h (a ⊗ b) ＝ h a ⊕ h b))
  hY→X! = up' (X , _⊕_ , p) u v
  h : X → Y
  h = ∃!-witness hX→Y!
  hₗ : h u ＝ s
  hₗ = pr₁ (∃!-is-witness hX→Y!)
  hᵣ : h v ＝ t
  hᵣ = pr₁ (pr₂ (∃!-is-witness hX→Y!))
  hᵢ : (a b : X) → h (a ⊕ b) ＝ h a ⊗ h b
  hᵢ = pr₂ (pr₂ (∃!-is-witness hX→Y!))
  h' : Y → X
  h' = ∃!-witness hY→X!
  h'ₗ : h' s ＝ u
  h'ₗ = pr₁ (∃!-is-witness hY→X!)
  h'ᵣ : h' t ＝ v
  h'ᵣ = pr₁ (pr₂ (∃!-is-witness hY→X!))
  h'ᵢ : (a b : Y) → h' (a ⊗ b) ＝ h' a ⊕ h' b
  h'ᵢ = pr₂ (pr₂ (∃!-is-witness hY→X!))
  h∘h'＝id : h ∘ h' ＝ id
  h∘h'＝id = ap pr₁ (∃!-uniqueness'' (up' (Y , _⊗_ , p') s t)
              (h ∘ h' , (ap h h'ₗ ∙ hₗ) , (ap h h'ᵣ ∙ hᵣ)
                      , λ a b → ap h (h'ᵢ a b) ∙ hᵢ (h' a) (h' b))
              (id     , refl            , refl
                      , λ a b → refl))
  h'∘h＝id : h' ∘ h ＝ id
  h'∘h＝id = ap pr₁ (∃!-uniqueness'' (up (X , _⊕_ , p) u v)
              (h' ∘ h , (ap h' hₗ ∙ h'ₗ) , (ap h' hᵣ ∙ h'ᵣ)
                      , λ a b → ap h' (hᵢ a b) ∙ h'ᵢ (h a) (h b))
              (id     , refl            , refl
                      , λ a b → refl))

interval-object-prop : is-univalent 𝓤 → is-prop (interval-object 𝓤)
interval-object-prop ua A B = f (all-interval-objects-equiv A B)
 where
  f : A ≊⟨interval-object⟩ B → A ＝ B
  f = pr₁ (pr₁ (pr₂ (characterization-of-interval-object-＝ ua A B)))

\end{code}
