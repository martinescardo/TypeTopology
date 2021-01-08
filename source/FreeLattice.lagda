Tom de Jong, 8 January 2021

We construct the free lattice on a set X as the powerset of X.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

--open import UF-Equiv
open import UF-FunExt
open import UF-Powerset
open import UF-PropTrunc
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

module FreeLattice
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

\end{code}

We start with some basic constructions on the powerset.

\begin{code}

𝕋 : {X : 𝓥 ̇ } → 𝓟 X → 𝓥 ̇
𝕋 {𝓥} {X} A = Σ x ꞉ X , (x ∈ A)

𝕋-to-carrier : {X : 𝓥 ̇ } (A : 𝓟 X) → 𝕋 A → X
𝕋-to-carrier A = pr₁

𝕋-to-membership : {X : 𝓥 ̇ } (A : 𝓟 X) (t : 𝕋 A) → (𝕋-to-carrier A t) ∈ A
𝕋-to-membership A = pr₂

⦅_⦆[_] : {X : 𝓥 ̇ } → X → is-set X → 𝓟 X
⦅ x ⦆[ i ] = (λ y → ((y ≡ x) , i))

{-
∅ : {X : 𝓤 ̇ } → 𝓟 X
∅ x = 𝟘 , 𝟘-is-prop

∅-is-least : {X : 𝓤 ̇ } (A : 𝓟 X) → ∅ ⊆ A
∅-is-least x _ = 𝟘-induction
-}

⋃  : {X I : 𝓥 ̇ } (α : I → 𝓟 X) → 𝓟 X
⋃ {𝓥} {X} {I} α x = (∃ i ꞉ I , x ∈ α i) , ∃-is-prop

⋃-is-upperbound : {X I : 𝓥 ̇ } (α : I → 𝓟 X) (i : I)
                → α i ⊆ ⋃ α
⋃-is-upperbound α i x a = ∣ i , a ∣

⋃-is-lowerbound-of-upperbounds : {X I : 𝓥 ̇ } (α : I → 𝓟 X) (A : 𝓟 X)
                               → ((i : I) → α i ⊆ A)
                               → ⋃ α ⊆ A
⋃-is-lowerbound-of-upperbounds {𝓥} {X} {I} α A ub x u =
 ∥∥-rec (∈-is-prop A x) γ u
  where
   γ : (Σ i ꞉ I , x ∈ α i) → x ∈ A
   γ (i , a) = ub i x a

\end{code}

\begin{code}

\end{code}

\begin{code}

record Lattice (𝓥 𝓤 𝓣 : Universe) : 𝓤ω where
  constructor
    lattice
  field
    L : 𝓤 ̇
    L-is-set : is-set L
    _⊑_ : L → L → 𝓣 ̇
    ⊑-is-prop-valued : (x y : L) → is-prop (x ⊑ y)
    ⊑-is-reflexive : (x : L) → x ⊑ x
    ⊑-is-transitive : (x y z : L) → x ⊑ y → y ⊑ z → x ⊑ z
    ⊑-is-antisymmetric : (x y : L) → x ⊑ y → y ⊑ x → x ≡ y
    ⋁ : {I : 𝓥 ̇ } → (I → L) → L
    ⋁-is-upperbound : {I : 𝓥 ̇ } (α : I → L) (i : I) → α i ⊑ ⋁ α
    ⋁-is-lowerbound-of-upperbounds : {I : 𝓥 ̇ } (α : I → L) (x : L)
                                   → ((i : I) → α i ⊑ x)
                                   → ⋁ α ⊑ x

  transitivity' : (x : L) {y z : L}
                → x ⊑ y → y ⊑ z → x ⊑ z
  transitivity' x {y} {z} = ⊑-is-transitive x y z

  syntax transitivity' x u v = x ⊑⟨ u ⟩ v
  infixr 0 transitivity'

  reflexivity' : (x : L) → x ⊑ x
  reflexivity' x = ⊑-is-reflexive x

  syntax reflexivity' x = x ⊑∎
  infix 1 reflexivity'

  ≡-to-⊑ : {x y : L} → x ≡ y → x ⊑ y
  ≡-to-⊑ {x} {x} refl = reflexivity' x

\end{code}

\begin{code}

module _
        (pe : propext 𝓥)
        (fe₁ : funext 𝓥 𝓥)
        (fe₂ : funext 𝓥 (𝓥 ⁺))
        (X : 𝓥 ̇ )
        (X-is-set : is-set X)
       where

 𝓟-lattice : Lattice 𝓥 (𝓥 ⁺) 𝓥
 Lattice.L 𝓟-lattice                              = 𝓟 X
 Lattice.L-is-set 𝓟-lattice                       = powersets-are-sets fe₂ fe₁ pe
 Lattice._⊑_ 𝓟-lattice                            = _⊆_
 Lattice.⊑-is-prop-valued 𝓟-lattice               = ⊆-is-prop fe₁ fe₁
 Lattice.⊑-is-reflexive 𝓟-lattice                 = ⊆-refl
 Lattice.⊑-is-transitive 𝓟-lattice                = ⊆-trans
 Lattice.⊑-is-antisymmetric 𝓟-lattice             = (λ A B → subset-extensionality pe fe₁ fe₂)
 Lattice.⋁ 𝓟-lattice                              = ⋃
 Lattice.⋁-is-upperbound 𝓟-lattice                = ⋃-is-upperbound
 Lattice.⋁-is-lowerbound-of-upperbounds 𝓟-lattice = ⋃-is-lowerbound-of-upperbounds

 express-subset-as-union : (A : 𝓟 X)
                         → A ≡ ⋃ {𝓥} {X} {𝕋 A} (⦅_⦆[ X-is-set ] ∘ pr₁)
 express-subset-as-union A = subset-extensionality pe fe₁ fe₂ u v
  where
   u : A ⊆ ⋃ (⦅_⦆[ X-is-set ] ∘ pr₁)
   u x a = ∣ (x , a) , refl ∣
   v : ⋃ (⦅_⦆[ X-is-set ] ∘ pr₁) ⊆ A
   v x = ∥∥-rec (∈-is-prop A x) γ
    where
     γ : (Σ i ꞉ 𝕋 A , x ∈ (⦅_⦆[ X-is-set ] ∘ pr₁) i) → x ∈ A
     γ ((x , a) , refl) = a
