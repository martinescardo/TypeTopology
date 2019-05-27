Tom de Jong & Martin Escardo, 20 May 2019.

 * Directed complete posets.
 * Continuous maps.
 * Function space.
 * Least fixed points.
 * Example: lifting, and the semantic counter-parts of the PCF constants.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-PropTrunc
open import SpartanMLTT

module Dcpos (pt : propositional-truncations-exist)
             (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
             (𝓥 : Universe) -- where the index set for directed completeness lives
       where

open PropositionalTruncation pt

open import UF-Subsingletons
open import UF-Subsingletons-FunExt

module _
        {𝓤 𝓣 : Universe}
        {D : 𝓤 ̇ }
        (_⊑_ : D → D → 𝓣 ̇ )
       where

 is-prop-valued : 𝓤 ⊔ 𝓣 ̇
 is-prop-valued = (x y : D) → is-prop(x ⊑ y)

 is-reflexive : 𝓤 ⊔ 𝓣 ̇
 is-reflexive = (x : D) → x ⊑ x

 is-transitive : 𝓤 ⊔ 𝓣 ̇
 is-transitive = (x y z : D) → x ⊑ y → y ⊑ z → x ⊑ z

 is-antisymmetric : 𝓤 ⊔ 𝓣 ̇
 is-antisymmetric = (x y : D) → x ⊑ y → y ⊑ x → x ≡ y

 is-upperbound : {I : 𝓥 ̇ } (u : D) (α : I → D) → 𝓥 ⊔ 𝓣 ̇
 is-upperbound u α = (i : domain α) → α i ⊑ u

 is-sup : {I : 𝓥 ̇ } → D → (I → D) → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
 is-sup s α = (is-upperbound s α)
            × ((u : D) → is-upperbound u α → s ⊑ u)

 is-sup-is-upperbound : {I : 𝓥 ̇ } {s : D} {α : I → D}
                      → is-sup s α
                      → is-upperbound s α
 is-sup-is-upperbound i = pr₁ i

 is-sup-is-lowerbound-of-upperbounds : {I : 𝓥 ̇ } {s : D} {α : I → D}
                                     → is-sup s α
                                     → ((u : D) → is-upperbound u α → s ⊑ u)
 is-sup-is-lowerbound-of-upperbounds i = pr₂ i

 has-sup : {I : 𝓥 ̇ } → (I → D) → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
 has-sup α = Σ \(s : D) → is-sup s α

 the-sup : {I : 𝓥 ̇ } {α : I → D} → has-sup α → D
 the-sup (s , i) = s

 sup-property : {I : 𝓥 ̇ } {α : I → D} (h : has-sup α) → is-sup (the-sup h) α
 sup-property (s , i) = i

 is-directed : {I : 𝓥 ̇ } → (I → D) → 𝓥 ⊔ 𝓣 ̇
 is-directed {I} α = (i j : I) → ∃ \(k : I) → (α i ⊑ α k) × (α j ⊑ α k)

 being-directed-is-a-prop : {I : 𝓥 ̇ } (α : I → D) → is-prop (is-directed α)
 being-directed-is-a-prop α = Π-is-prop fe
                               (λ i → Π-is-prop fe
                                       (λ j → ∥∥-is-a-prop ))

 is-directed-complete : 𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓣  ̇
 is-directed-complete = {I : 𝓥 ̇ } {α : I → D} → is-directed α → has-sup α

 dcpo-axioms : 𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓣 ̇
 dcpo-axioms = is-set D × is-prop-valued × is-reflexive × is-transitive × is-antisymmetric × is-directed-complete

 is-sup-is-a-prop : dcpo-axioms → {I : 𝓥 ̇ } (d : D) (α : I → D) → is-prop (is-sup d α)
 is-sup-is-a-prop (s , p , r , t , a , c) {I} d α = γ
  where
   γ : is-prop (is-sup d α)
   γ = ×-is-prop (Π-is-prop fe (λ (i : I) → p (α i) d))
                 (Π-is-prop fe (λ (x : D) → Π-is-prop fe (λ l → p d x)))

 has-sup-is-a-prop : dcpo-axioms → {I : 𝓥 ̇ } (α : I → D) → is-prop (has-sup α)
 has-sup-is-a-prop (s , p , r , t , a , c) {I} α = γ
  where
   γ : is-prop (has-sup α)
   γ (j , (u , l)) (j' , (u' , l')) = to-Σ-≡ (q , is-sup-is-a-prop (s , p , r , t , a , c) j' α _ _)
    where
     q : j ≡ j'
     q = a j j' (l j' u') (l' j u)

 being-directed-complete-is-a-prop : dcpo-axioms → is-prop is-directed-complete
 being-directed-complete-is-a-prop a =
  Π-is-prop' fe
   (λ I → Π-is-prop' fe 
             (λ α → Π-is-prop fe (λ d → has-sup-is-a-prop a α)))

 dcpo-axioms-is-a-prop : is-prop dcpo-axioms
 dcpo-axioms-is-a-prop = iprops-are-props γ
  where
   γ : dcpo-axioms → is-prop dcpo-axioms
   γ (s , p , r , t , a , c) =
    ×-is-prop  (being-set-is-a-prop fe)
    (×-is-prop (Π-is-prop fe
                 (λ (x : D) → Π-is-prop fe
                                (λ (y : D) → being-a-prop-is-a-prop fe)))
    (×-is-prop (Π-is-prop fe (λ (x : D) → p x x))
    (×-is-prop (Π-is-prop fe
                 (λ (x : D) → Π-is-prop fe
                               (λ (y : D) → Π-is-prop fe
                                             (λ (z : D) → Π-is-prop fe
                                                           (λ (l : x ⊑ y) → Π-is-prop fe
                                                                             (λ (m : y ⊑ z) → p x z))))))
    (×-is-prop (Π-is-prop fe
                 (λ (x : D) → Π-is-prop fe
                               (λ y → Π-is-prop fe
                                       (λ (l : x ⊑ y) → Π-is-prop fe
                                                         λ (m : y ⊑ x) → s))))
              (being-directed-complete-is-a-prop (s , p , r , t , a , c))))))

module _ {𝓤 𝓣 : Universe} where

 DCPO-structure : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ⊔ (𝓣 ⁺) ̇
 DCPO-structure D = Σ \(_⊑_ : D → D → 𝓣 ̇ ) → dcpo-axioms {𝓤} {𝓣} _⊑_

 DCPO : (𝓤 ⁺) ⊔ (𝓥 ⁺) ⊔ (𝓣 ⁺) ̇
 DCPO = Σ \(D : 𝓤 ̇ ) → DCPO-structure D

 ⟨_⟩ : DCPO → 𝓤 ̇
 ⟨ D , _⊑_ , d ⟩ = D

 underlying-order : (𝓓 : DCPO) → ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓣 ̇
 underlying-order (D , _⊑_ , d) = _⊑_

 syntax underlying-order  𝓓 x y = x ⊑⟨ 𝓓 ⟩ y

 axioms-of-dcpo : (𝓓 : DCPO) → dcpo-axioms (underlying-order 𝓓)
 axioms-of-dcpo (D , _⊑_ , d) = d

 sethood : (𝓓 : DCPO) → is-set ⟨ 𝓓 ⟩
 sethood (D , _⊑_ , (s  , p  , r  , t  , a  , c )) = s

 prop-valuedness : (𝓓 : DCPO) → is-prop-valued (underlying-order 𝓓 )
 prop-valuedness (D , _⊑_ , (s  , p  , r  , t  , a  , c )) = p

 reflexivity : (𝓓 : DCPO) → is-reflexive (underlying-order 𝓓)
 reflexivity (D , _⊑_ , (s  , p  , r  , t  , a  , c )) = r

 transitivity : (𝓓 : DCPO) → is-transitive (underlying-order 𝓓)
 transitivity (D , _⊑_ , (s  , p  , r  , t  , a  , c )) = t

 antisymmetry : (𝓓 : DCPO) → is-antisymmetric (underlying-order 𝓓)
 antisymmetry (D , _⊑_ , (s  , p  , r  , t  , a  , c )) = a

 directed-completeness : (𝓓 : DCPO) → is-directed-complete (underlying-order 𝓓)
 directed-completeness (D , _⊑_ , (s  , p  , r  , t  , a  , c )) = c

 is-Directed : (𝓓 : DCPO) {I : 𝓥 ̇ } (α : I → ⟨ 𝓓 ⟩) → 𝓥 ⊔ 𝓣 ̇
 is-Directed 𝓓 α = is-directed (underlying-order 𝓓) α

 ∐ : (𝓓 : DCPO) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩} → is-Directed 𝓓 α → ⟨ 𝓓 ⟩
 ∐ 𝓓 δ = pr₁ (directed-completeness 𝓓 δ)

 ∐-is-sup : (𝓓 : DCPO) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩} (δ : is-Directed 𝓓 α)
          → ((i : I) → α i ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ)
          × ((u : ⟨ 𝓓 ⟩) → ((i : I) → α i ⊑⟨ 𝓓 ⟩ u) → ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩ u)
 ∐-is-sup 𝓓 δ = pr₂ (directed-completeness 𝓓 δ)

 ∐-is-upperbound : (𝓓 : DCPO) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩} (δ : is-Directed 𝓓 α)
                 → ((i : I) → α i ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ)
 ∐-is-upperbound 𝓓 δ = pr₁ (∐-is-sup 𝓓 δ)

 ∐-is-lowerbound-of-upperbounds : (𝓓 : DCPO) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩} (δ : is-Directed 𝓓 α)
                                → ((u : ⟨ 𝓓 ⟩) → ((i : I) → α i ⊑⟨ 𝓓 ⟩ u) → ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩ u)
 ∐-is-lowerbound-of-upperbounds 𝓓 δ = pr₂ (∐-is-sup 𝓓 δ)

is-monotone : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) → (⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) → 𝓤 ⊔ 𝓣 ⊔ 𝓣' ̇
is-monotone 𝓓 𝓔 f = (x y : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ y → f x ⊑⟨ 𝓔 ⟩ f y

is-continuous : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
              → (⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩)
              → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
is-continuous 𝓓 𝓔 f = (I : 𝓥 ̇) (α : I → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 α)
                     → is-sup (underlying-order 𝓔) (f (∐ 𝓓 δ)) (f ∘ α)

being-continuous-is-a-prop : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) (f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩)
                           → is-prop (is-continuous 𝓓 𝓔 f)
being-continuous-is-a-prop 𝓓 𝓔 f =
   Π-is-prop fe
    (λ I → Π-is-prop fe
            (λ α → Π-is-prop fe
                     (λ δ → is-sup-is-a-prop (underlying-order 𝓔)
                            (axioms-of-dcpo 𝓔) (f (∐ 𝓓 δ)) (f ∘ α))))

[_,_] : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                     → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
[ 𝓓 , 𝓔 ] = Σ (\(f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) → is-continuous 𝓓 𝓔 f)

underlying-function : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                    → [ 𝓓 , 𝓔 ] → ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩
underlying-function 𝓓 𝓔 (f , _) = f

continuity-of-function : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) (f : [ 𝓓 , 𝓔 ])
                       → is-continuous 𝓓 𝓔 (underlying-function 𝓓 𝓔 f)
continuity-of-function 𝓓 𝓔 (_ , c) = c
                            
continuous-functions-are-monotone : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) (f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩)
                                  → is-continuous 𝓓 𝓔 f → is-monotone 𝓓 𝓔 f
continuous-functions-are-monotone 𝓓 𝓔 f cts x y l = γ
  where
   α : 𝟙 {𝓥} + 𝟙 {𝓥} → ⟨ 𝓓 ⟩
   α (inl *) = x
   α (inr *) = y
   δ : is-Directed 𝓓 α
   δ (inl *) (inl *) = ∣ inr * , l , l ∣
   δ (inl *) (inr *) = ∣ inr * , l , reflexivity 𝓓 y ∣
   δ (inr *) (inl *) = ∣ inr * , reflexivity 𝓓 y , l ∣
   δ (inr *) (inr *) = ∣ inr * , reflexivity 𝓓 y , reflexivity 𝓓 y ∣
   a : y ≡ ∐ 𝓓 δ
   a = antisymmetry 𝓓 y (∐ 𝓓 δ)
           (∐-is-upperbound 𝓓 δ (inr *))
           (∐-is-lowerbound-of-upperbounds 𝓓 δ y h)
    where
     h : (i : 𝟙 + 𝟙) → α i ⊑⟨ 𝓓 ⟩ y
     h (inl *) = l
     h (inr *) = reflexivity 𝓓 y
   b : is-sup (underlying-order 𝓔) (f y) (f ∘ α)
   b = transport (λ - → is-sup (underlying-order 𝓔) - (f ∘ α)) (ap f (a ⁻¹))
       (cts (𝟙 + 𝟙) α δ)
   γ : f x ⊑⟨ 𝓔 ⟩ f y
   γ = is-sup-is-upperbound (underlying-order 𝓔) b (inl *)

\end{code}
