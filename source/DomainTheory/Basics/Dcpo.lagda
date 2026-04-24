Tom de Jong & Martin Escardo, 20 May 2019.
Refactored January 2020, December 2021 by Tom de Jong.

Definitions of:
 * Directed complete posets (dcpos).
 * Scott continuous maps.

See DomainTheory.lagda for an overview of the formalization of the theory of
dcpos.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.SubtypeClassifier

module DomainTheory.Basics.Dcpo
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import Naturals.Addition renaming (_+_ to _+'_)
open import Naturals.Order
open import Naturals.Subtraction
open import Notation.Order

open import OrderedTypes.Poset fe

module _ {𝓤 𝓣 : Universe}
         {D : 𝓤 ̇ }
         (_⊑_ : D → D → 𝓣 ̇ )
       where

 open PosetAxioms

 is-upperbound : {I : 𝓦 ̇ } (u : D) (α : I → D) → 𝓦 ⊔ 𝓣 ̇
 is-upperbound u α = (i : domain α) → α i ⊑ u

 is-lowerbound-of-upperbounds : {I : 𝓦 ̇ } (u : D) (α : I → D) → 𝓦 ⊔ 𝓤 ⊔ 𝓣 ̇
 is-lowerbound-of-upperbounds u α = (v : D) → is-upperbound v α → u ⊑ v

 is-sup : {I : 𝓦 ̇ } → D → (I → D) → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
 is-sup s α = (is-upperbound s α) × (is-lowerbound-of-upperbounds s α)

 sup-is-upperbound : {I : 𝓦 ̇ } {s : D} {α : I → D}
                   → is-sup s α
                   → is-upperbound s α
 sup-is-upperbound i = pr₁ i

 sup-is-lowerbound-of-upperbounds : {I : 𝓦 ̇ } {s : D} {α : I → D}
                                  → is-sup s α
                                  → (u : D)
                                  → is-upperbound u α → s ⊑ u
 sup-is-lowerbound-of-upperbounds i = pr₂ i

 has-sup : {I : 𝓦 ̇ } → (I → D) → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
 has-sup α = Σ s ꞉ D , is-sup s α

 the-sup : {I : 𝓦 ̇ } {α : I → D} → has-sup α → D
 the-sup (s , i) = s

 sup-property : {I : 𝓦 ̇ } {α : I → D} (h : has-sup α) → is-sup (the-sup h) α
 sup-property (s , i) = i

 is-inhabited : (X : 𝓦 ̇ ) → 𝓦 ̇
 is-inhabited = ∥_∥

 is-semidirected : {I : 𝓦 ̇ } → (I → D) → 𝓦 ⊔ 𝓣 ̇
 is-semidirected {𝓦} {I} α = (i j : I) → ∃ k ꞉ I , (α i ⊑ α k) × (α j ⊑ α k)

 is-directed : {I : 𝓦 ̇ } → (I → D) → 𝓦 ⊔ 𝓣 ̇
 is-directed {𝓦} {I} α = is-inhabited I × is-semidirected α

 inhabited-if-directed : {I : 𝓦 ̇ } (α : I → D) → is-directed α → ∥ I ∥
 inhabited-if-directed α = pr₁

 semidirected-if-directed : {I : 𝓦 ̇ } (α : I → D) → is-directed α
                               → (i j : I) → ∃ k ꞉ I , (α i ⊑ α k) × (α j ⊑ α k)
 semidirected-if-directed α = pr₂

 being-inhabited-is-prop : {I : 𝓦 ̇ } → is-prop (is-inhabited I)
 being-inhabited-is-prop = ∥∥-is-prop

 being-semidirected-is-prop : {I : 𝓦 ̇ } (α : I → D) → is-prop (is-semidirected α)
 being-semidirected-is-prop α = Π₂-is-prop fe (λ i j → ∥∥-is-prop)

 being-directed-is-prop : {I : 𝓦 ̇ } (α : I → D) → is-prop (is-directed α)
 being-directed-is-prop α =
  ×-is-prop being-inhabited-is-prop (being-semidirected-is-prop α)

 is-directed-complete : 𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓣 ̇
 is-directed-complete = (I : 𝓥 ̇ ) (α : I → D) → is-directed α → has-sup α

 is-sup-is-prop : poset-axioms _⊑_
                → {I : 𝓦 ̇ } (d : D) (α : I → D)
                → is-prop (is-sup d α)
 is-sup-is-prop (s , p , r , t , a) {I} d α = γ
  where
   γ : is-prop (is-sup d α)
   γ = ×-is-prop (Π-is-prop fe (λ i → p (α i) d))
                 (Π₂-is-prop fe (λ x l → p d x))

 sups-are-unique : poset-axioms _⊑_
                 → {I : 𝓦 ̇ } (α : I → D) {x y : D}
                 → is-sup x α → is-sup y α → x ＝ y
 sups-are-unique (s , p , r , t , a) {I} α {x} {y} x-is-sup y-is-sup =
  a x y
   (sup-is-lowerbound-of-upperbounds x-is-sup y (sup-is-upperbound y-is-sup))
   (sup-is-lowerbound-of-upperbounds y-is-sup x (sup-is-upperbound x-is-sup))

 having-sup-is-prop : poset-axioms _⊑_
                    → {I : 𝓦 ̇ } (α : I → D)
                    → is-prop (has-sup α)
 having-sup-is-prop ax {I} α σ τ =
  to-subtype-＝ (λ x → is-sup-is-prop ax x α)
               (sups-are-unique ax α (pr₂ σ) (pr₂ τ))

 dcpo-axioms : 𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓣 ̇
 dcpo-axioms = poset-axioms _⊑_ × is-directed-complete

 being-directed-complete-is-prop : dcpo-axioms → is-prop is-directed-complete
 being-directed-complete-is-prop a =
  Π₃-is-prop fe (λ I α δ → having-sup-is-prop (pr₁ a) α)

 dcpo-axioms-is-prop : is-prop dcpo-axioms
 dcpo-axioms-is-prop = prop-criterion γ
  where
   γ : dcpo-axioms → is-prop dcpo-axioms
   γ a = ×-is-prop (poset-axioms-is-prop _⊑_)
                   (being-directed-complete-is-prop a)

\end{code}

Since we will also consider dcpos with a least element later, we make the
following definitions.

\begin{code}

 is-least : D → 𝓤 ⊔ 𝓣 ̇
 is-least x = ∀ (y : D) → x ⊑ y

 has-least : 𝓤 ⊔ 𝓣 ̇
 has-least = Σ x ꞉ D , is-least x

\end{code}

Added 23 June 2024.

\begin{code}

 is-ω-chain : (ℕ → D) → 𝓣 ̇
 is-ω-chain α = (n : ℕ) → α n ⊑ α (succ n)

 is-ω-complete : 𝓤 ⊔ 𝓣 ̇
 is-ω-complete = (α : ℕ → D) → is-ω-chain α → has-sup α

 module _
         (⊑-refl : is-reflexive _⊑_)
         (⊑-trans : is-transitive _⊑_)
         (α : ℕ → D)
        where

  ω-chains-increase : is-ω-chain α
                    → (n m : ℕ) → n ≤ m → α n ⊑ α m
  ω-chains-increase c n 0        l =
   transport⁻¹ (λ - → α - ⊑ α 0) (unique-least n l) (⊑-refl (α 0))
  ω-chains-increase c n (succ m) l = I (≤-split n m l)
   where
    I : n ≤ m + (n ＝ succ m) → α n ⊑ α (succ m)
    I (inl k) = ⊑-trans (α n) (α m) (α (succ m)) (ω-chains-increase c n m k) (c m)
    I (inr refl) = ⊑-refl (α (succ m))

  ω-chains-are-directed : is-ω-chain α → is-directed α
  ω-chains-are-directed c = ∣ 0 ∣ , I
   where
    I : is-semidirected α
    I n m = ∣ n +' m , II , III ∣
     where
      II : α n ⊑ α (n +' m)
      II = ω-chains-increase c n (n +' m)
            (cosubtraction n (n +' m) (m , (addition-commutativity m n)))
      III : α m ⊑ α (n +' m)
      III = ω-chains-increase c m (n +' m)
             (cosubtraction m (n +' m) (n , refl))

\end{code}

End of addition.


We have now developed enough material to define dcpos and we introduce some
convenient projections.

\begin{code}

module _ {𝓤 𝓣 : Universe} where

 open PosetAxioms

 DCPO-structure : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ⊔ (𝓣 ⁺) ̇
 DCPO-structure D = Σ _⊑_ ꞉ (D → D → 𝓣 ̇ ), (dcpo-axioms {𝓤} {𝓣} _⊑_)

 DCPO : (𝓤 ⁺) ⊔ (𝓥 ⁺) ⊔ (𝓣 ⁺) ̇
 DCPO = Σ D ꞉ 𝓤 ̇ , DCPO-structure D

 ⟨_⟩ : DCPO → 𝓤 ̇
 ⟨ D , _⊑_ , d ⟩ = D

 underlying-order : (𝓓 : DCPO) → ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓣 ̇
 underlying-order (D , _⊑_ , d) = _⊑_

 syntax underlying-order 𝓓 x y = x ⊑⟨ 𝓓 ⟩ y

 axioms-of-dcpo : (𝓓 : DCPO) → dcpo-axioms (underlying-order 𝓓)
 axioms-of-dcpo (D , _⊑_ , d) = d

 poset-axioms-of-dcpo : (𝓓 : DCPO) → poset-axioms (underlying-order 𝓓)
 poset-axioms-of-dcpo (D , _⊑_ , d) = pr₁ d

 sethood : (𝓓 : DCPO) → is-set ⟨ 𝓓 ⟩
 sethood (D , _⊑_ , (s  , p  , r  , t  , a)  , c ) = s

 prop-valuedness : (𝓓 : DCPO) → is-prop-valued (underlying-order 𝓓 )
 prop-valuedness (D , _⊑_ , (s  , p  , r  , t  , a)  , c ) = p

 reflexivity : (𝓓 : DCPO) → is-reflexive (underlying-order 𝓓)
 reflexivity (D , _⊑_ , (s  , p  , r  , t  , a)  , c ) = r

 transitivity : (𝓓 : DCPO) → is-transitive (underlying-order 𝓓)
 transitivity (D , _⊑_ , (s  , p  , r  , t  , a)  , c ) = t

 antisymmetry : (𝓓 : DCPO) → is-antisymmetric (underlying-order 𝓓)
 antisymmetry (D , _⊑_ , (s  , p  , r  , t  , a)  , c ) = a

\end{code}

Added by Ayberk Tosun on 2024-04-19.

To work with the combinators in `UF.Logic`, it is convenient to have a version
of equality on domain elements that is packaged up with the proof that it is
a proposition.

\begin{code}

 dcpo-equalityₚ : (𝓓 : DCPO) → ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → Ω 𝓤
 dcpo-equalityₚ 𝓓 x y = (x ＝ y) , sethood 𝓓

 syntax dcpo-equalityₚ 𝓓 x y = x ＝ₚ[ 𝓓 ] y
 infix 2 dcpo-equalityₚ

\end{code}

We introduce pretty syntax for chain reasoning with inequalities.
(Cf. ＝⟨_⟩ and ∎ in Id.lagda, ≃⟨_⟩ and ■ in UF.Equiv.lagda)

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

 has-bottom : DCPO → 𝓤 ⊔ 𝓣 ̇
 has-bottom 𝓓 = has-least (underlying-order 𝓓)

\end{code}

Next, we introduce ∐-notation for the supremum of a directed family in a dcpo.

\begin{code}

 directed-completeness : (𝓓 : DCPO) → is-directed-complete (underlying-order 𝓓)
 directed-completeness (D , _⊑_ , a) = pr₂ a

 is-Semidirected : (𝓓 : DCPO) {I : 𝓦 ̇ } (α : I → ⟨ 𝓓 ⟩) → 𝓦 ⊔ 𝓣 ̇
 is-Semidirected 𝓓 α = is-semidirected (underlying-order 𝓓) α

 is-Directed : (𝓓 : DCPO) {I : 𝓦 ̇ } (α : I → ⟨ 𝓓 ⟩) → 𝓦 ⊔ 𝓣 ̇
 is-Directed 𝓓 α = is-directed (underlying-order 𝓓) α

 inhabited-if-Directed : (𝓓 : DCPO) {I : 𝓦 ̇ } (α : I → ⟨ 𝓓 ⟩)
                       → is-Directed 𝓓 α
                       → ∥ I ∥
 inhabited-if-Directed 𝓓 α = pr₁

 semidirected-if-Directed : (𝓓 : DCPO) {I : 𝓦 ̇ } (α : I → ⟨ 𝓓 ⟩)
                          → is-Directed 𝓓 α
                          → is-Semidirected 𝓓 α
 semidirected-if-Directed 𝓓 α = pr₂

 ω-chains-are-Directed : (𝓓 : DCPO) (α : ℕ → ⟨ 𝓓 ⟩)
                       → is-ω-chain (underlying-order 𝓓) α
                       → is-Directed 𝓓 α
 ω-chains-are-Directed 𝓓 α =
  ω-chains-are-directed (underlying-order 𝓓) (reflexivity 𝓓) (transitivity 𝓓) α

 ∐ : (𝓓 : DCPO) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩} → is-Directed 𝓓 α → ⟨ 𝓓 ⟩
 ∐ 𝓓 {I} {α} δ = pr₁ (directed-completeness 𝓓 I α δ)

 ∐-is-sup : (𝓓 : DCPO) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩} (δ : is-Directed 𝓓 α)
          → is-sup (underlying-order 𝓓) (∐ 𝓓 δ) α
 ∐-is-sup 𝓓 {I} {α} δ = pr₂ (directed-completeness 𝓓 I α δ)

 ∐-is-upperbound : (𝓓 : DCPO) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩} (δ : is-Directed 𝓓 α)
                 → is-upperbound (underlying-order 𝓓) (∐ 𝓓 δ) α
 ∐-is-upperbound 𝓓 δ = pr₁ (∐-is-sup 𝓓 δ)

 ∐-is-lowerbound-of-upperbounds : (𝓓 : DCPO) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩}
                                  (δ : is-Directed 𝓓 α)
                                → is-lowerbound-of-upperbounds
                                    (underlying-order 𝓓) (∐ 𝓓 δ) α
 ∐-is-lowerbound-of-upperbounds 𝓓 δ = pr₂ (∐-is-sup 𝓓 δ)

\end{code}

Finally, we define (strict) continuous maps between (pointed) dcpos.

\begin{code}

is-continuous : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
              → (⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩)
              → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
is-continuous 𝓓 𝓔 f = (I : 𝓥 ̇ ) (α : I → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 α)
                     → is-sup (underlying-order 𝓔) (f (∐ 𝓓 δ)) (f ∘ α)

being-continuous-is-prop : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                             (f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩)
                           → is-prop (is-continuous 𝓓 𝓔 f)
being-continuous-is-prop 𝓓 𝓔 f =
 Π₃-is-prop fe (λ I α δ → is-sup-is-prop (underlying-order 𝓔)
                          (pr₁ (axioms-of-dcpo 𝓔))
                          (f (∐ 𝓓 δ)) (f ∘ α))

DCPO[_,_] : DCPO {𝓤} {𝓣} → DCPO {𝓤'} {𝓣'} → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
DCPO[ 𝓓 , 𝓔 ] = Σ f ꞉ (⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) , is-continuous 𝓓 𝓔 f

underlying-function : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                    → DCPO[ 𝓓 , 𝓔 ] → ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩
underlying-function 𝓓 𝓔 (f , _) = f

syntax underlying-function 𝓓 𝓔 f = [ 𝓓 , 𝓔 ]⟨ f ⟩

continuity-of-function : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) (f : DCPO[ 𝓓 , 𝓔 ])
                       → is-continuous 𝓓 𝓔 [ 𝓓 ,  𝓔 ]⟨ f ⟩
continuity-of-function 𝓓 𝓔 (_ , c) = c

\end{code}
