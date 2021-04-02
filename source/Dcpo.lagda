Tom de Jong & Martin Escardo, 20 May 2019.

 * Directed complete posets.
 * Continuous maps.
 * Examples and constructions in DcpoConstructions

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base
open import UF-PropTrunc
open import UF-Subsingletons
open import UF-FunExt
open import UF-PropTrunc

module Dcpo
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe) -- where the index type for directed completeness lives
       where

open PropositionalTruncation pt

open import UF-Subsingletons
open import UF-Subsingletons-FunExt

module _ {𝓤 𝓣 : Universe}
         {D : 𝓤 ̇ }
         (_⊑_ : D → D → 𝓣 ̇ )
       where

 is-prop-valued : 𝓤 ⊔ 𝓣 ̇
 is-prop-valued = (x y : D) → is-prop (x ⊑ y)

 is-reflexive : 𝓤 ⊔ 𝓣 ̇
 is-reflexive = (x : D) → x ⊑ x

 is-transitive : 𝓤 ⊔ 𝓣 ̇
 is-transitive = (x y z : D) → x ⊑ y → y ⊑ z → x ⊑ z

 is-antisymmetric : 𝓤 ⊔ 𝓣 ̇
 is-antisymmetric = (x y : D) → x ⊑ y → y ⊑ x → x ≡ y

 is-least : D → 𝓤 ⊔ 𝓣 ̇
 is-least x = ∀ (y : D) → x ⊑ y

 has-least : 𝓤 ⊔ 𝓣 ̇
 has-least = Σ x ꞉ D , is-least x

 is-upperbound : {I : 𝓥 ̇ } (u : D) (α : I → D) → 𝓥 ⊔ 𝓣 ̇
 is-upperbound u α = (i : domain α) → α i ⊑ u

 is-sup : {I : 𝓥 ̇ } → D → (I → D) → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
 is-sup s α = (is-upperbound s α)
            × ((u : D) → is-upperbound u α → s ⊑ u)

 is-sup-gives-is-upperbound : {I : 𝓥 ̇ } {s : D} {α : I → D}
                            → is-sup s α
                            → is-upperbound s α
 is-sup-gives-is-upperbound i = pr₁ i

 is-sup-gives-is-lowerbound-of-upperbounds : {I : 𝓥 ̇ } {s : D} {α : I → D}
                                           → is-sup s α
                                           → (u : D)
                                           → is-upperbound u α → s ⊑ u
 is-sup-gives-is-lowerbound-of-upperbounds i = pr₂ i

 has-sup : {I : 𝓥 ̇ } → (I → D) → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
 has-sup α = Σ s ꞉ D , is-sup s α

 the-sup : {I : 𝓥 ̇ } {α : I → D} → has-sup α → D
 the-sup (s , i) = s

 sup-property : {I : 𝓥 ̇ } {α : I → D} (h : has-sup α) → is-sup (the-sup h) α
 sup-property (s , i) = i

 is-directed : {I : 𝓥 ̇ } → (I → D) → 𝓥 ⊔ 𝓣 ̇
 is-directed {I} α = ∥ I ∥ × ((i j : I) → ∃ k ꞉ I , (α i ⊑ α k) × (α j ⊑ α k))

 is-directed-gives-inhabited : {I : 𝓥 ̇ } (α : I → D) → is-directed α → ∥ I ∥
 is-directed-gives-inhabited α = pr₁

 is-directed-order : {I : 𝓥 ̇ } (α : I → D) → is-directed α
                   → (i j : I) → ∃ k ꞉ I , (α i ⊑ α k) × (α j ⊑ α k)
 is-directed-order α = pr₂

 being-directed-is-prop : {I : 𝓥 ̇ } (α : I → D) → is-prop (is-directed α)
 being-directed-is-prop α = ×-is-prop ∥∥-is-prop
                            (Π-is-prop fe
                               (λ i → Π-is-prop fe
                                       (λ j → ∥∥-is-prop )))

 is-directed-complete : 𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓣  ̇
 is-directed-complete = (I : 𝓥 ̇ ) (α : I → D) → is-directed α → has-sup α

 dcpo-axioms : 𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓣 ̇
 dcpo-axioms = is-set D
             × is-prop-valued
             × is-reflexive
             × is-transitive
             × is-antisymmetric
             × is-directed-complete

 is-sup-is-prop : dcpo-axioms → {I : 𝓥 ̇ } (d : D) (α : I → D)
                  → is-prop (is-sup d α)
 is-sup-is-prop (s , p , r , t , a , c) {I} d α = γ
  where
   γ : is-prop (is-sup d α)
   γ = ×-is-prop (Π-is-prop fe (λ (i : I) → p (α i) d))
                 (Π-is-prop fe (λ (x : D) → Π-is-prop fe (λ l → p d x)))

 having-sup-is-prop : dcpo-axioms → {I : 𝓥 ̇ } (α : I → D)
                      → is-prop (has-sup α)
 having-sup-is-prop (s , p , r , t , a , c) {I} α = γ
  where
   γ : is-prop (has-sup α)
   γ (j , (u , l)) (j' , (u' , l')) =
     to-Σ-≡ (q , is-sup-is-prop (s , p , r , t , a , c) j' α _ _)
    where
     q : j ≡ j'
     q = a j j' (l j' u') (l' j u)

 being-directed-complete-is-prop : dcpo-axioms → is-prop is-directed-complete
 being-directed-complete-is-prop a =
  Π-is-prop fe
   (λ I → Π-is-prop fe
             (λ α → Π-is-prop fe (λ d → having-sup-is-prop a α)))

 dcpo-axioms-is-prop : is-prop dcpo-axioms
 dcpo-axioms-is-prop = prop-criterion γ
  where
   γ : dcpo-axioms → is-prop dcpo-axioms
   γ (s , p , r , t , a , c) =
    ×-is-prop  (being-set-is-prop fe)
    (×-is-prop (Π-is-prop fe
                 (λ (x : D) → Π-is-prop fe
                                (λ (y : D) → being-prop-is-prop fe)))
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
              (being-directed-complete-is-prop (s , p , r , t , a , c))))))

module _ {𝓤 𝓣 : Universe} where

 DCPO-structure : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ⊔ (𝓣 ⁺) ̇
 DCPO-structure D = Σ _⊑_ ꞉ (D → D → 𝓣 ̇ ), (dcpo-axioms {𝓤} {𝓣} _⊑_)

 DCPO : (𝓤 ⁺) ⊔ (𝓥 ⁺) ⊔ (𝓣 ⁺) ̇
 DCPO = Σ D ꞉ 𝓤 ̇ , DCPO-structure D

 ⟨_⟩ : DCPO → 𝓤 ̇
 ⟨ D , _⊑_ , d ⟩ = D

 underlying-order : (𝓓 : DCPO) → ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓣 ̇
 underlying-order (D , _⊑_ , d) = _⊑_

 syntax underlying-order 𝓓 x y = x ⊑⟨ 𝓓 ⟩ y

 DCPO⊥ : (𝓥 ⁺) ⊔ (𝓤 ⁺) ⊔ (𝓣 ⁺) ̇
 DCPO⊥ = Σ 𝓓 ꞉ DCPO , has-least (underlying-order 𝓓)

 ⟪_⟫ : DCPO⊥ → DCPO
 ⟪ 𝓓 , x , p ⟫  = 𝓓

 the-least : (𝓓 : DCPO⊥) → ⟨ ⟪ 𝓓 ⟫ ⟩
 the-least (𝓓 , x , p) = x

 least-property : (𝓓 : DCPO⊥) → is-least (underlying-order ⟪ 𝓓 ⟫) (the-least 𝓓)
 least-property (𝓓 , x , p) = p

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

 is-Directed-gives-inhabited : (𝓓 : DCPO) {I : 𝓥 ̇ } (α : I → ⟨ 𝓓 ⟩) → is-Directed 𝓓 α → ∥ I ∥
 is-Directed-gives-inhabited 𝓓 α = pr₁

 is-Directed-order : (𝓓 : DCPO) {I : 𝓥 ̇ } (α : I → ⟨ 𝓓 ⟩) → is-Directed 𝓓 α
                   → (i j : I) → ∃ k ꞉ I , (α i ⊑⟨ 𝓓 ⟩ α k) × (α j ⊑⟨ 𝓓 ⟩ α k)
 is-Directed-order 𝓓 α = pr₂

 ∐ : (𝓓 : DCPO) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩} → is-Directed 𝓓 α → ⟨ 𝓓 ⟩
 ∐ 𝓓 {I} {α} δ = pr₁ (directed-completeness 𝓓 I α δ)

 ∐-is-sup : (𝓓 : DCPO) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩} (δ : is-Directed 𝓓 α)
          → ((i : I) → α i ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ)
          × ((u : ⟨ 𝓓 ⟩) → ((i : I) → α i ⊑⟨ 𝓓 ⟩ u) → ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩ u)
 ∐-is-sup 𝓓 {I} {α} δ = pr₂ (directed-completeness 𝓓 I α δ)

 ∐-is-upperbound : (𝓓 : DCPO) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩} (δ : is-Directed 𝓓 α)
                 → ((i : I) → α i ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ)
 ∐-is-upperbound 𝓓 δ = pr₁ (∐-is-sup 𝓓 δ)

 ∐-is-lowerbound-of-upperbounds : (𝓓 : DCPO) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩} (δ : is-Directed 𝓓 α)
                                → ((u : ⟨ 𝓓 ⟩) → ((i : I) → α i ⊑⟨ 𝓓 ⟩ u) → ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩ u)
 ∐-is-lowerbound-of-upperbounds 𝓓 δ = pr₂ (∐-is-sup 𝓓 δ)

\end{code}

We introduce pretty syntax for chain reasoning with inequalities.
(Cf. ≡⟨_⟩ and ∎ in Id.lagda, ≃⟨_⟩ and ■ in UF-Equiv.lagda)

For example, given (a b c d : ⟨ 𝓓 ⟩) and
u : a ⊑⟨ 𝓓 ⟩ b
v : b ⊑⟨ 𝓓 ⟩ c
w : c ⊑⟨ 𝓓 ⟩ d

this will allow us to write

z : a ⊑⟨ 𝓓 ⟩ d
z = a ⊑⟨ 𝓓 ⟩[ u ]
    b ⊑⟨ 𝓓 ⟩[ v ]
    c ⊑⟨ 𝓓 ⟩[ w ]
    d ∎⟨ 𝓓 ⟩

rather than the hard(er) to read

z : a ⊑⟨ 𝓓 ⟩ d
z = transitivity 𝓓 a c d z' w
 where
  z' : a ⊑⟨ 𝓓 ⟩ c
  z' = transitivity 𝓓 a b c u v

\begin{code}

 transitivity' : (𝓓 : DCPO) (x : ⟨ 𝓓 ⟩) {y z : ⟨ 𝓓 ⟩}
               → x ⊑⟨ 𝓓 ⟩ y → y ⊑⟨ 𝓓 ⟩ z → x ⊑⟨ 𝓓 ⟩ z
 transitivity' 𝓓 x {y} {z} u v = transitivity 𝓓 x y z u v

 syntax transitivity' 𝓓 x u v = x ⊑⟨ 𝓓 ⟩[ u ] v
 infixr 0 transitivity'

 syntax reflexivity 𝓓 x = x ∎⟨ 𝓓 ⟩
 infix 1 reflexivity

\end{code}

Next, we define continuous maps between dcpos.

\begin{code}

is-monotone : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) → (⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) → 𝓤 ⊔ 𝓣 ⊔ 𝓣' ̇
is-monotone 𝓓 𝓔 f = (x y : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ y → f x ⊑⟨ 𝓔 ⟩ f y

is-continuous : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
              → (⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩)
              → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
is-continuous 𝓓 𝓔 f = (I : 𝓥 ̇ ) (α : I → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 α)
                     → is-sup (underlying-order 𝓔) (f (∐ 𝓓 δ)) (f ∘ α)

being-continuous-is-prop : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) (f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩)
                           → is-prop (is-continuous 𝓓 𝓔 f)
being-continuous-is-prop 𝓓 𝓔 f =
   Π-is-prop fe
    (λ I → Π-is-prop fe
            (λ α → Π-is-prop fe
                     (λ δ → is-sup-is-prop (underlying-order 𝓔)
                            (axioms-of-dcpo 𝓔) (f (∐ 𝓓 δ)) (f ∘ α))))

DCPO[_,_] : DCPO {𝓤} {𝓣} → DCPO {𝓤'} {𝓣'} → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
DCPO[ 𝓓 , 𝓔 ] = Σ f ꞉ (⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩), is-continuous 𝓓 𝓔 f

DCPO⊥[_,_] : DCPO⊥ {𝓤} {𝓣} → DCPO⊥ {𝓤'} {𝓣'} → (𝓥 ⁺) ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
DCPO⊥[ 𝓓 , 𝓔 ] = DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓔 ⟫ ]

underlying-function : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                    → DCPO[ 𝓓 , 𝓔 ] → ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩
underlying-function 𝓓 𝓔 (f , _) = f

continuity-of-function : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) (f : DCPO[ 𝓓 , 𝓔 ])
                       → is-continuous 𝓓 𝓔 (underlying-function 𝓓 𝓔 f)
continuity-of-function 𝓓 𝓔 (_ , c) = c

continuous-functions-are-monotone : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                                    (f : DCPO[ 𝓓 , 𝓔 ])
                                  → is-monotone 𝓓 𝓔 (underlying-function 𝓓 𝓔 f)
continuous-functions-are-monotone 𝓓 𝓔 (f , cts) x y l = γ
  where
   α : 𝟙 {𝓥} + 𝟙 {𝓥} → ⟨ 𝓓 ⟩
   α (inl *) = x
   α (inr *) = y
   δ : is-Directed 𝓓 α
   δ = (∣ inl * ∣ , ε)
    where
     ε : (i j : 𝟙 + 𝟙) → ∃ (\k → α i ⊑⟨ 𝓓 ⟩ α k × α j ⊑⟨ 𝓓 ⟩ α k)
     ε (inl *) (inl *) = ∣ inr * , l , l ∣
     ε (inl *) (inr *) = ∣ inr * , l , reflexivity 𝓓 y ∣
     ε (inr *) (inl *) = ∣ inr * , reflexivity 𝓓 y , l ∣
     ε (inr *) (inr *) = ∣ inr * , reflexivity 𝓓 y , reflexivity 𝓓 y ∣
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
   γ = is-sup-gives-is-upperbound (underlying-order 𝓔) b (inl *)

constant-functions-are-continuous : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                                    (e : ⟨ 𝓔 ⟩) → is-continuous 𝓓 𝓔 (λ d → e)
constant-functions-are-continuous 𝓓 𝓔 e I α δ = u , v where
 u : (i : I) → e ⊑⟨ 𝓔 ⟩ e
 u i = reflexivity 𝓔 e
 v : (y : ⟨ 𝓔 ⟩) → ((i : I) → e ⊑⟨ 𝓔 ⟩ y) → e ⊑⟨ 𝓔 ⟩ y
 v y l  = ∥∥-rec (prop-valuedness 𝓔 e y) (λ (i : I) → l i)
          (is-directed-gives-inhabited (underlying-order 𝓓) α δ)

image-is-directed : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                    (f : DCPO[ 𝓓 , 𝓔 ]) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩}
                  → is-Directed 𝓓 α
                  → is-Directed 𝓔 ((underlying-function 𝓓 𝓔 f) ∘ α)
image-is-directed 𝓓 𝓔 (f , c) {I} {α} δ =
 (is-Directed-gives-inhabited 𝓓 α δ) , γ
  where
   γ : (i j : I)
     → ∃ k ꞉ I , f (α i) ⊑⟨ 𝓔 ⟩ f (α k) × f (α j) ⊑⟨ 𝓔 ⟩ f (α k)
   γ i j = ∥∥-functor h (is-Directed-order 𝓓 α δ i j)
    where
     h : (Σ k ꞉ I , (α i) ⊑⟨ 𝓓 ⟩ (α k) × (α j) ⊑⟨ 𝓓 ⟩ (α k))
       → Σ k ꞉ I , f (α i) ⊑⟨ 𝓔 ⟩ f (α k) × f (α j) ⊑⟨ 𝓔 ⟩ f (α k)
     h (k , l , m) =
      k , (continuous-functions-are-monotone 𝓓 𝓔 (f , c) (α i) (α k) l ,
      (continuous-functions-are-monotone 𝓓 𝓔 (f , c) (α j) (α k) m))

continuous-function-∐-≡ : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                          (f : DCPO[ 𝓓 , 𝓔 ]) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩}
                          (δ : is-Directed 𝓓 α)
                        → (underlying-function 𝓓 𝓔 f) (∐ 𝓓 δ) ≡
                          ∐ 𝓔 (image-is-directed 𝓓 𝓔 f δ)
continuous-function-∐-≡ 𝓓 𝓔 (f , c) {I} {α} δ =
 antisymmetry 𝓔 (f (∐ 𝓓 δ)) (∐ 𝓔 (image-is-directed 𝓓 𝓔 (f , c) δ)) a b
  where
   s : is-sup (underlying-order 𝓔) (f (∐ 𝓓 δ)) (f ∘ α)
   s = c I α δ
   ε : is-Directed 𝓔 (f ∘ α)
   ε = image-is-directed 𝓓 𝓔 (f , c) δ
   a : f (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩ ∐ 𝓔 (image-is-directed 𝓓 𝓔 (f , c) δ)
   a = is-sup-gives-is-lowerbound-of-upperbounds (underlying-order 𝓔) s
       (∐ 𝓔 (image-is-directed 𝓓 𝓔 (f , c) δ))
       (∐-is-upperbound 𝓔 ε)
   b : ∐ 𝓔 ε  ⊑⟨ 𝓔 ⟩ f (∐ 𝓓 δ)
   b = ∐-is-lowerbound-of-upperbounds 𝓔 ε (f (∐ 𝓓 δ))
       (is-sup-gives-is-upperbound (underlying-order 𝓔) s)

\end{code}
