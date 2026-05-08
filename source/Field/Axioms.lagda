Andrew Sneap, 7 Feb 2021

In this file I define the constructive field axioms.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import UF.Sets

module Field.Axioms where

distributive : {X : 𝓤 ̇ } → (X → X → X) → (X → X → X) → 𝓤 ̇
distributive _⊕_ _⊙_ = ∀ x y z → x ⊙ (y ⊕ z) ＝ ((x ⊙ y) ⊕ (x ⊙ z))

field-structure : 𝓤 ̇ → {𝓥 : Universe}  → 𝓤 ⊔ (𝓥 ⁺) ̇
field-structure F {𝓥} = (F → F → F) × (F → F → F) × (F → F → 𝓥 ̇ )

\end{code}

In the following axioms, e₀ is the additive identity element (usually
0), e₁ is the multiplicative identity element (usually 1). We cannot
simply say that e₀ ≠ e₁, since this is not constructive for the
Dedekind Reals, so we use an apartness relation.  For the rationals,
the apartness relation is defined as x ≠ y, but for the reals it is
defined as (x < y) ∔ (y < x)

\begin{code}

field-axioms : (F : 𝓤 ̇ )→ { 𝓥 : Universe} → field-structure F { 𝓥} → 𝓤 ⊔ 𝓥 ̇
field-axioms F { 𝓥} (_⊕_ , _⊙_ , _#_) = is-set F × associative _⊕_
                                                   × associative _⊙_
                                                   × commutative _⊕_
                                                   × commutative _⊙_
                                                   × distributive _⊕_ _⊙_
                                                   × (Σ (e₀ , e₁) ꞉ F × F , ((e₀ # e₁) × left-neutral e₀ _⊕_
                                                                                       × ((x : F) → Σ x' ꞉ F , x ⊕ x' ＝ e₀)
                                                                                       × left-neutral e₁ _⊙_
                                                                                       × ((x : F) → (x # e₀) → Σ x' ꞉ F , x ⊙ x' ＝ e₁)))

Field-structure : 𝓤 ̇ → { 𝓥 : Universe} → 𝓤 ⊔ (𝓥 ⁺) ̇
Field-structure F  { 𝓥} = Σ fs ꞉ field-structure F { 𝓥} , field-axioms F fs

ordered-field-structure : {𝓤 𝓥 𝓦 : Universe} → (F : 𝓤 ̇ )→ (fs : field-structure F { 𝓥}) → (fa : field-axioms F fs) → (𝓤 ⊔ (𝓦 ⁺)) ̇
ordered-field-structure {𝓤} {𝓥} {𝓦} F fs fa = (F → F → 𝓦 ̇ )

ordered-field-axioms : {𝓤 𝓥 𝓦 : Universe} → (F : 𝓤 ̇ )→ (fs : field-structure F) → (fa : field-axioms F fs) →  ordered-field-structure { 𝓤} { 𝓥} { 𝓦} F fs fa → (𝓤 ⊔ 𝓦) ̇
ordered-field-axioms {𝓤} {𝓥} {𝓦} F (_⊕_ , _⊙_ , _#_) (s , a , a' , c , c' , d , (e , e') , i) _<_ = ((x y z : F) → x < y → (x ⊕ z) < (y ⊕ z))
                                                                                                     × ((x y : F) → e < x → e < y → e < (x ⊙ y))
Ordered-field-structure : {𝓤 𝓥 𝓦 : Universe} → (F : 𝓤 ̇ )→ Field-structure F { 𝓥} → 𝓤 ⊔ (𝓦 ⁺) ̇
Ordered-field-structure {𝓤} {𝓥} {𝓦} F (fs , fa) = Σ ofa ꞉ (ordered-field-structure {𝓤} {𝓥} {𝓦} F fs fa) , ordered-field-axioms {𝓤} {𝓥} F fs fa ofa

Field : (𝓤 : Universe) → { 𝓥  : Universe} → (𝓤 ⁺) ⊔ (𝓥 ⁺) ̇
Field 𝓤 { 𝓥} = Σ X ꞉ 𝓤 ̇ , Field-structure X { 𝓥}

ordered-field-structure' : (𝓤 : Universe) → {𝓥 𝓦 : Universe} → (F : Field 𝓤 { 𝓥}) → 𝓤 ⊔ (𝓦 ⁺) ̇
ordered-field-structure' _ { 𝓥} { 𝓦} (F , _) = F → F → 𝓦 ̇

ordered-field-axioms' : (𝓤 : Universe) → {𝓥 𝓦 : Universe} → (F : Field 𝓤 { 𝓥}) → ordered-field-structure' 𝓤 { 𝓥} { 𝓦} F → 𝓤 ⊔ 𝓦 ̇
ordered-field-axioms' 𝓤 {𝓥} {𝓦} (F , (_⊕_ , _⊛_ , _) , (s , a , a' , c , c' , d , (e , e') , i)) _<_
 = ((x y z : F) → x < y → (x ⊕ z) < (y ⊕ z)) × ((x y : F) → e < x → e < y → e < (x ⊛ y))

Ordered-field-structure' : (𝓤 : Universe) → { 𝓥 𝓦 : Universe} → (F : Field 𝓤 { 𝓥}) → 𝓤 ⊔ (𝓦 ⁺) ̇
Ordered-field-structure' 𝓤 {𝓥} {𝓦} F = Σ ofs ꞉ ordered-field-structure' 𝓤 { 𝓥} { 𝓦} F , ordered-field-axioms' 𝓤 F ofs

Ordered-Field : (𝓤 : Universe) → { 𝓥 𝓦 : Universe} → (𝓤 ⁺) ⊔ (𝓥 ⁺) ⊔ (𝓦 ⁺) ̇
Ordered-Field 𝓤 {𝓥} {𝓦} = Σ X ꞉ Field 𝓤 { 𝓥} , Ordered-field-structure' 𝓤 { 𝓥} { 𝓦} X

⟨_⟩ : Ordered-Field 𝓤 { 𝓥} { 𝓦} → 𝓤 ̇
⟨ (F , fs) , ofs ⟩ = F

addition : {𝓥 𝓦 : Universe} → (F : Ordered-Field 𝓤 { 𝓥} { 𝓦}) → ⟨ F ⟩ → ⟨ F ⟩ → ⟨ F ⟩
addition ((F , (_+_ , _*_ , _♯_) , F-is-set , +-assoc , *-assoc , +-comm , *-comm , dist , (e₀ , e₁) , e₀♯e₁ , zero-left-neutral , +-inverse , *-left-neutral , *-inverse) , _<_ , <-respects-additions , <-respects-multiplication) = _+_

addition-commutative : {𝓥 𝓦 : Universe} → (F : Ordered-Field 𝓤 { 𝓥} { 𝓦}) → _
addition-commutative ((F , (_+_ , _*_ , _♯_) , F-is-set , +-assoc , *-assoc , +-comm , *-comm , dist , (e₀ , e₁) , e₀♯e₁ , zero-left-neutral , +-inverse , *-left-neutral , *-inverse) , _<_ , <-respects-additions , <-respects-multiplication) = +-comm

multiplication-commutative : {𝓥 𝓦 : Universe} → (F : Ordered-Field 𝓤 { 𝓥} { 𝓦}) → _
multiplication-commutative ((F , (_+_ , _*_ , _♯_) , F-is-set , +-assoc , *-assoc , +-comm , *-comm , dist , (e₀ , e₁) , e₀♯e₁ , zero-left-neutral , +-inverse , *-left-neutral , *-inverse) , _<_ , <-respects-additions , <-respects-multiplication) = *-comm

multiplication : {𝓥 𝓦 : Universe} → (F : Ordered-Field 𝓤 { 𝓥} { 𝓦}) → ⟨ F ⟩ → ⟨ F ⟩ → ⟨ F ⟩
multiplication ((F , (_+_ , _*_ , _♯_) , F-is-set , +-assoc , *-assoc , +-comm , *-comm , dist , (e₀ , e₁) , e₀♯e₁ , zero-left-neutral , +-inverse , *-left-neutral , *-inverse) , _<_ , <-respects-additions , <-respects-multiplication) = _*_

apartness : {𝓥 𝓦 : Universe} → (F : Ordered-Field 𝓤 { 𝓥} { 𝓦}) → ⟨ F ⟩ → ⟨ F ⟩ → 𝓥 ̇
apartness ((F , (_+_ , _*_ , _♯_) , F-is-set , +-assoc , *-assoc , +-comm , *-comm , dist , (e₀ , e₁) , e₀♯e₁ , zero-left-neutral , +-inverse , *-left-neutral , *-inverse) , _<_ , <-respects-additions , <-respects-multiplication) = _♯_

additive-identity : {𝓥 𝓦 : Universe} → (F : Ordered-Field 𝓤 { 𝓥} { 𝓦}) → ⟨ F ⟩
additive-identity ((F , (_+_ , _*_ , _♯_) , F-is-set , +-assoc , *-assoc , +-comm , *-comm , dist , (e₀ , e₁) , e₀♯e₁ , zero-left-neutral , +-inverse , *-left-neutral , *-inverse) , _<_ , <-respects-additions , <-respects-multiplication)  = e₀

multiplicative-identity : {𝓥 𝓦 : Universe} → (F : Ordered-Field 𝓤 { 𝓥} { 𝓦}) → ⟨ F ⟩
multiplicative-identity ((F , (_+_ , _*_ , _♯_) , F-is-set , +-assoc , *-assoc , +-comm , *-comm , dist , (e₀ , e₁) , e₀♯e₁ , zero-left-neutral , +-inverse , *-left-neutral , *-inverse) , _<_ , <-respects-additions , <-respects-multiplication) =  e₁

underlying-type-is-set : {𝓥 𝓦 : Universe} → (F : Ordered-Field 𝓤 { 𝓥} { 𝓦}) → is-set ⟨ F ⟩
underlying-type-is-set {𝓥} ((a , (pr₃ , pr₄) , F-is-set , c) , d) = F-is-set

zero-left-neutral : {𝓥 𝓦 : Universe} → (F : Ordered-Field 𝓤 { 𝓥} { 𝓦}) → _
zero-left-neutral ((F , (_+_ , _*_ , _♯_) , F-is-set , +-assoc , *-assoc , +-comm , *-comm , dist , (e₀ , e₁) , e₀♯e₁ , zln , +-inverse , *-left-neutral , *-inverse) , _<_ , <-respects-additions , <-respects-multiplication) = zln

addition-associative : {𝓥 𝓦 : Universe} → (F : Ordered-Field 𝓤 { 𝓥} { 𝓦}) → _
addition-associative ((F , (_+_ , _*_ , _♯_) , F-is-set , +-assoc , *-assoc , +-comm , *-comm , dist , (e₀ , e₁) , e₀♯e₁ , zln , +-inverse , *-left-neutral , *-inverse) , _<_ , <-respects-additions , <-respects-multiplication) = +-assoc

{-

ArchimedeanOrderedField : (𝓤 : Universe) → {𝓥 𝓦 : Universe} → (𝓤 ⁺) ⊔ (𝓥 ⁺) ⊔ (𝓦 ⁺) ̇
ArchimedeanOrderedField 𝓤 {𝓥} {𝓦} = Σ (F , (_<_ , ofa)) ꞉ Ordered-Field 𝓤 {𝓥} { 𝓦} , ((embedding : (ℚ → ⟨ (F , (_<_ , ofa)) ⟩)) → (∀ x y → ∃ z ꞉ ℚ , (x < embedding z) × (embedding z < y)))
-}

\end{code}
