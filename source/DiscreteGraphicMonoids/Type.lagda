Martin Escardo and Paulo Oliva, April 2024.

The type of discrete graphic monoids.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module DiscreteGraphicMonoids.Type where

open import MLTT.Spartan
open import UF.DiscreteAndSeparated
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.FunExt

graphical : {X : 𝓤 ̇ } → (X → X → X) → 𝓤 ̇
graphical _·_ = ∀ x y → (x · y) · x ＝ x · y

monoid-structure : 𝓤 ̇ → 𝓤 ̇
monoid-structure X = X × (X → X → X)

discrete-graphic-monoid-axioms : (X : 𝓤 ̇ ) → monoid-structure X → 𝓤 ̇
discrete-graphic-monoid-axioms X (e , _·_) =
   is-discrete X
 × left-neutral  e _·_
 × right-neutral e _·_
 × associative'    _·_
 × graphical       _·_

discrete-graphic-monoid-axioms-is-prop
 : FunExt
 → (X : 𝓤 ̇ ) (s : monoid-structure X)
 → is-prop (discrete-graphic-monoid-axioms X s)
discrete-graphic-monoid-axioms-is-prop fe X s =
 prop-criterion (λ axioms@(d , _) →
  ×₅-is-prop
  (being-discrete-is-prop fe)
  (Π-is-prop (fe _ _) (λ x → discrete-types-are-sets d))
  (Π-is-prop (fe _ _) (λ x → discrete-types-are-sets d))
  (Π₃-is-prop (fe _ _) (λ x y z → discrete-types-are-sets d))
  (Π₂-is-prop (fe _ _) (λ x y → discrete-types-are-sets d)))

DGM : (𝓤 : Universe) → 𝓤 ⁺ ̇
DGM 𝓤 = Σ M ꞉ 𝓤 ̇
      , Σ s ꞉ monoid-structure M
      , discrete-graphic-monoid-axioms M s

⟨_⟩ : DGM 𝓤 → 𝓤 ̇
⟨ M , (e , _·_) , d , ln , rn , a , gl ⟩ = M

unit : (𝓜 : DGM 𝓤)
     → ⟨ 𝓜 ⟩
unit (M , (e , _·_) , d , ln , rn , a , gl) = e

syntax unit 𝓜 = e⟨ 𝓜 ⟩

multiplication : (𝓜 : DGM 𝓤)
               → ⟨ 𝓜 ⟩ → ⟨ 𝓜 ⟩ → ⟨ 𝓜 ⟩
multiplication (M , (e , _·_) , d , ln , rn , a , gl) = _·_

syntax multiplication 𝓜 x y = x ·⟨ 𝓜 ⟩ y

discreteness : (𝓜 : DGM 𝓤) → is-discrete ⟨ 𝓜 ⟩
discreteness (M , (e , _·_) , d , ln , rn , a , gl) = d

underlying-type-is-set : (𝓜 : DGM 𝓤) → is-set ⟨ 𝓜 ⟩
underlying-type-is-set 𝓜 = discrete-types-are-sets (discreteness 𝓜)

left-neutrality : (𝓜 : DGM 𝓤)
                → left-neutral (e⟨ 𝓜 ⟩) (multiplication 𝓜)
left-neutrality (M , (e , _·_) , d , ln , rn , a , gl) = ln

right-neutrality : (𝓜 : DGM 𝓤)
                 → right-neutral (e⟨ 𝓜 ⟩) (multiplication 𝓜)
right-neutrality (M , (e , _·_) , d , ln , rn , a , gl) = rn

associativity : (𝓜 : DGM 𝓤)
              → associative' (multiplication 𝓜)
associativity (M , (e , _·_) , d , ln , rn , a , gl) = a

graphicality : (𝓜 : DGM 𝓤)
             → graphical (multiplication 𝓜)
graphicality (M , (e , _·_) , d , ln , rn , a , gl) = gl

idempotency : (𝓜 : DGM 𝓤) (x : ⟨ 𝓜 ⟩) → x ·⟨ 𝓜 ⟩ x ＝ x
idempotency 𝓜 x =
 x · x       ＝⟨ ap (_· x) ((right-neutrality 𝓜 x)⁻¹) ⟩
 (x · e) · x ＝⟨ graphicality 𝓜 x e ⟩
 x · e       ＝⟨ right-neutrality 𝓜 x ⟩
 x           ∎
 where
  e   = unit 𝓜
  _·_ = multiplication 𝓜

is-hom : (𝓜 : DGM 𝓤) (𝓝 : DGM 𝓥) → (⟨ 𝓜 ⟩ → ⟨ 𝓝 ⟩) → 𝓤 ⊔ 𝓥 ̇
is-hom 𝓜 𝓝 f = (f e⟨ 𝓜 ⟩ ＝ e⟨ 𝓝 ⟩)
               × (∀ x y → f (x ·⟨ 𝓜 ⟩ y) ＝ f x ·⟨ 𝓝 ⟩ f y)

homs-preserve-unit : (𝓜 : DGM 𝓤) (𝓝 : DGM 𝓥)
                   → (f : ⟨ 𝓜 ⟩ → ⟨ 𝓝 ⟩)
                   → is-hom 𝓜 𝓝 f
                   → f e⟨ 𝓜 ⟩ ＝ e⟨ 𝓝 ⟩
homs-preserve-unit _ _ _ (u , m) = u

homs-preserve-mul : (𝓜 : DGM 𝓤) (𝓝 : DGM 𝓥)
                  → (f : ⟨ 𝓜 ⟩ → ⟨ 𝓝 ⟩)
                  → is-hom 𝓜 𝓝 f
                  → (x y : ⟨ 𝓜 ⟩) → f (x ·⟨ 𝓜 ⟩ y) ＝ f x ·⟨ 𝓝 ⟩ f y
homs-preserve-mul _ _ _ (u , m) = m

id-is-hom : (𝓜 : DGM 𝓤)
          → is-hom 𝓜 𝓜 id
id-is-hom 𝓜 = (refl , (λ _ _ → refl))

∘-is-hom : (𝓜₀ : DGM 𝓤) (𝓜₁ : DGM 𝓥) (𝓜₂ : DGM 𝓦)
           (f : ⟨ 𝓜₀ ⟩ → ⟨ 𝓜₁ ⟩) (g : ⟨ 𝓜₁ ⟩ → ⟨ 𝓜₂ ⟩)
         → is-hom 𝓜₀ 𝓜₁ f
         → is-hom 𝓜₁ 𝓜₂ g
         → is-hom 𝓜₀ 𝓜₂ (g ∘ f)
∘-is-hom 𝓜₀ 𝓜₁ 𝓜₂ f g (f-unit , f-mul) (g-unit , g-mul)  =
 ((g ∘ f) (unit 𝓜₀) ＝⟨ ap g f-unit ⟩
  g (unit 𝓜₁)       ＝⟨ g-unit ⟩
  unit 𝓜₂           ∎) ,
 (λ x y → g (f (x ·⟨ 𝓜₀ ⟩ y))     ＝⟨ ap g (f-mul x y) ⟩
          g (f x ·⟨ 𝓜₁ ⟩ f y)     ＝⟨ g-mul (f x) (f y) ⟩
          g (f x) ·⟨ 𝓜₂ ⟩ g (f y) ∎)

\end{code}
