Andrew Sneap - 27th April 2021

I link to this module within the Dedekind Reals and Discussion sections of my report.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


open import SpartanMLTT renaming (_+_ to _∔_) -- TypeTopology

open import UF-Subsingletons

module FieldAxioms where

distributive : {X : 𝓤 ̇ } → (X → X → X) → (X → X → X) → 𝓤 ̇
distributive _⊕_ _⊙_ = ∀ x y z → x ⊙ (y ⊕ z) ≡ ((x ⊙ y) ⊕ (x ⊙ z))

field-structure : 𝓤 ̇ → {𝓥 : Universe}  → 𝓤 ⊔ (𝓥 ⁺) ̇
field-structure F {𝓥} = (F → F → F) × (F → F → F) × (F → F → 𝓥 ̇)

\end{code}

In the following axioms, e₀ is the additive identity element (usually 0), e₁ is the multiplicative identity element (usually 1)
We cannot simply say that e₀ ≢ e₁, since this is not constructive for the Dedekind Reals, so we use an apartness relation.
For the rationals, the apartness relation is defined as x ≢ y, but for the reals it is defined as (x < y) ∔ (y < x)

\begin{code}

field-axioms : (F : 𝓤 ̇) → { 𝓥 : Universe } → field-structure F { 𝓥 } → Set (𝓤 ⊔ 𝓥) 
field-axioms F { 𝓥 } (_⊕_ , _⊙_ , _#_) = is-set F × associative _⊕_
                                                   × associative _⊙_
                                                   × commutative _⊕_
                                                   × commutative _⊙_
                                                   × distributive _⊕_ _⊙_
                                                   × (Σ (e₀ , e₁) ꞉ F × F , ((e₀ # e₁) × left-neutral e₀ _⊕_
                                                                                       × ((x : F) → Σ x' ꞉ F , x ⊕ x' ≡ e₀) 
                                                                                       × left-neutral e₁ _⊙_
                                                                                       × ((x : F) → (x # e₀) → Σ x' ꞉ F , x ⊙ x' ≡ e₁)))

Field-structure : 𝓤 ̇ → { 𝓥 : Universe } → 𝓤 ⊔ (𝓥 ⁺) ̇
Field-structure F  { 𝓥 } = Σ fs ꞉ field-structure F { 𝓥 } , field-axioms F fs

ordered-field-structure : {𝓤 𝓥 𝓦 : Universe} → (F : 𝓤 ̇) → (fs : field-structure F { 𝓥 }) → (fa : field-axioms F fs) → (𝓤 ⊔ (𝓦 ⁺)) ̇
ordered-field-structure {𝓤} {𝓥} {𝓦} F fs fa = (F → F → 𝓦 ̇)

ordered-field-axioms : {𝓤 𝓥 𝓦 : Universe} → (F : 𝓤 ̇) → (fs : field-structure F) → (fa : field-axioms F fs) →  ordered-field-structure { 𝓤 } { 𝓥 } { 𝓦 } F fs fa → (𝓤 ⊔ 𝓦) ̇
ordered-field-axioms {𝓤} {𝓥} {𝓦} F (_⊕_ , _⊙_ , _#_) (s , a , a' , c , c' , d , (e , e') , i) _<_ = ((x y z : F) → x < y → (x ⊕ z) < (y ⊕ z))
                                                                                                     × ((x y : F) → e < x → e < y → e < (x ⊙ y))                                                                               
Ordered-field-structure : {𝓤 𝓥 𝓦 : Universe} → (F : 𝓤 ̇) → Field-structure F { 𝓥 } → 𝓤 ⊔ (𝓦 ⁺) ̇
Ordered-field-structure {𝓤} {𝓥} {𝓦} F (fs , fa) = Σ ofa ꞉ (ordered-field-structure {𝓤} {𝓥} {𝓦} F fs fa) , ordered-field-axioms {𝓤} {𝓥} F fs fa ofa

Field : (𝓤 : Universe) → { 𝓥  : Universe} → (𝓤 ⁺) ⊔ (𝓥 ⁺) ̇
Field 𝓤 { 𝓥 } = Σ X ꞉ 𝓤 ̇ , Field-structure X { 𝓥 }

ordered-field-structure' : (𝓤 : Universe) → {𝓥 𝓦 : Universe} → (F : Field 𝓤 { 𝓥 }) → 𝓤 ⊔ (𝓦 ⁺) ̇ 
ordered-field-structure' _ { 𝓥 } { 𝓦 } (F , _) = F → F → 𝓦 ̇

ordered-field-axioms' : (𝓤 : Universe) → {𝓥 𝓦 : Universe} → (F : Field 𝓤 { 𝓥 }) → ordered-field-structure' 𝓤 { 𝓥 } { 𝓦 } F → 𝓤 ⊔ 𝓦 ̇
ordered-field-axioms' 𝓤 {𝓥} {𝓦} (F , (_⊕_ , _⊛_ , _) , (s , a , a' , c , c' , d , (e , e') , i)) _<_
 = ((x y z : F) → x < y → (x ⊕ z) < (y ⊕ z)) × ((x y : F) → e < x → e < y → e < (x ⊛ y))

Ordered-field-structure' : (𝓤 : Universe) → { 𝓥 𝓦 : Universe } → (F : Field 𝓤 { 𝓥 }) → 𝓤 ⊔ (𝓦 ⁺) ̇
Ordered-field-structure' 𝓤 {𝓥} {𝓦} F = Σ ofs ꞉ ordered-field-structure' 𝓤 { 𝓥 } { 𝓦 } F , ordered-field-axioms' 𝓤 F ofs

Ordered-Field : (𝓤 : Universe) → { 𝓥 𝓦 : Universe } → (𝓤 ⁺) ⊔ (𝓥 ⁺) ⊔ (𝓦 ⁺) ̇ 
Ordered-Field 𝓤 {𝓥} {𝓦} = Σ X ꞉ Field 𝓤 { 𝓥 } , Ordered-field-structure' 𝓤 { 𝓥 } { 𝓦 } X

⟨_⟩ : Ordered-Field 𝓤 { 𝓥 } { 𝓦 } → 𝓤 ̇
⟨ (F , fs) , ofs ⟩ = F

addition : {𝓥 𝓦 : Universe} → (F : Ordered-Field 𝓤 { 𝓥 } { 𝓦 }) → ⟨ F ⟩ → ⟨ F ⟩ → ⟨ F ⟩
addition ((_ , (_+_ , _) , _) , _ , _ , _) = _+_

multiplication : {𝓥 𝓦 : Universe} → (F : Ordered-Field 𝓤 { 𝓥 } { 𝓦 }) → ⟨ F ⟩ → ⟨ F ⟩ → ⟨ F ⟩
multiplication ((_ , (_ , _*_ , _) , _) , _ , _ , _) = _*_

apartness : {𝓥 𝓦 : Universe} → (F : Ordered-Field 𝓤 { 𝓥 } { 𝓦 }) → ⟨ F ⟩ → ⟨ F ⟩ → 𝓥 ̇
apartness ((_ , (_ , _ , _♯_) , _) , _ , _ , _) = _♯_

additive-identity : {𝓥 𝓦 : Universe} → (F : Ordered-Field 𝓤 { 𝓥 } { 𝓦 }) → ⟨ F ⟩
additive-identity ((F , _ , _ , _ , _ , _ , _ , _ , (e₀ , e₁) , _) , _) = e₀

multiplicative-identity : {𝓥 𝓦 : Universe} → (F : Ordered-Field 𝓤 { 𝓥 } { 𝓦 }) → ⟨ F ⟩
multiplicative-identity ((F , _ , _ , _ , _ , _ , _ , _ , (e₀ , e₁) , _) , _) = e₁

\end{code}
