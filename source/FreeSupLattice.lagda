Tom de Jong, 8 & 15 January 2021

We construct the free 𝓥-sup-lattice on a set X : 𝓥 as the (𝓥-)powerset of X.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

open import UF-FunExt
open import UF-Lower-FunExt
open import UF-Powerset
open import UF-PropTrunc
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

module FreeSupLattice
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

∅ : {X : 𝓤 ̇ } → 𝓟 X
∅ x = 𝟘 , 𝟘-is-prop

∅-is-least : {X : 𝓤 ̇ } (A : 𝓟 X) → ∅ ⊆ A
∅-is-least x _ = 𝟘-induction

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

We define sup-lattices using a record. We also introduce convenient helpers
and syntax for reasoning about the order ⊑.

\begin{code}

record SupLattice (𝓥 𝓤 𝓣 : Universe) : 𝓤ω where
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

  ⋁-transport : {I : 𝓥 ̇ } (α β : I → L)
              → α ∼ β
              → ⋁ α ≡ ⋁ β
  ⋁-transport {I} α β H = ⊑-is-antisymmetric (⋁ α) (⋁ β) u v
   where
    u : ⋁ α ⊑ ⋁ β
    u = ⋁-is-lowerbound-of-upperbounds α (⋁ β) γ
     where
      γ : (i : I) → α i ⊑ ⋁ β
      γ i = α i  ⊑⟨ ≡-to-⊑ (H i) ⟩
             β i ⊑⟨ ⋁-is-upperbound β i ⟩
             ⋁ β ⊑∎
    v : ⋁ β ⊑ ⋁ α
    v = ⋁-is-lowerbound-of-upperbounds β (⋁ α) γ
     where
      γ : (i : I) → β i ⊑ ⋁ α
      γ i = β i ⊑⟨ ≡-to-⊑ (H i ⁻¹) ⟩
            α i ⊑⟨ ⋁-is-upperbound α i ⟩
            ⋁ α ⊑∎

\end{code}

The powerset of X is an example of a sup-lattice and every subset can be written
as a union of singletons (this will come in useful later).

\begin{code}

module _
        (pe : propext 𝓥)
        (fe : funext 𝓥 (𝓥 ⁺))
        (X : 𝓥 ̇ )
        (X-is-set : is-set X)
       where

 𝓟-lattice : SupLattice 𝓥 (𝓥 ⁺) 𝓥
 SupLattice.L 𝓟-lattice                              = 𝓟 X
 SupLattice.L-is-set 𝓟-lattice                       = powersets-are-sets fe pe
 SupLattice._⊑_ 𝓟-lattice                            = _⊆_
 SupLattice.⊑-is-prop-valued 𝓟-lattice               = ⊆-is-prop (lower-funext 𝓥 (𝓥 ⁺) fe)
 SupLattice.⊑-is-reflexive 𝓟-lattice                 = ⊆-refl
 SupLattice.⊑-is-transitive 𝓟-lattice                = ⊆-trans
 SupLattice.⊑-is-antisymmetric 𝓟-lattice             = (λ A B → subset-extensionality pe fe)
 SupLattice.⋁ 𝓟-lattice                              = ⋃
 SupLattice.⋁-is-upperbound 𝓟-lattice                = ⋃-is-upperbound
 SupLattice.⋁-is-lowerbound-of-upperbounds 𝓟-lattice = ⋃-is-lowerbound-of-upperbounds

 express-subset-as-union-of-singletons :
  (A : 𝓟 X) → A ≡ ⋃ {𝓥} {X} {𝕋 A} (⦅_⦆[ X-is-set ] ∘ pr₁)
 express-subset-as-union-of-singletons A = subset-extensionality pe fe u v
  where
   u : A ⊆ ⋃ (⦅_⦆[ X-is-set ] ∘ pr₁)
   u x a = ∣ (x , a) , refl ∣
   v : ⋃ (⦅_⦆[ X-is-set ] ∘ pr₁) ⊆ A
   v x = ∥∥-rec (∈-is-prop A x) γ
    where
     γ : (Σ i ꞉ 𝕋 A , x ∈ (⦅_⦆[ X-is-set ] ∘ pr₁) i) → x ∈ A
     γ ((x , a) , refl) = a

\end{code}

Finally we will show that 𝓟 X is the free 𝓥-sup-lattice on a set X : 𝓥.
Concretely, if L is a 𝓥-sup-lattice and f : X → L is any function,
then there is a *unique* mediating map f♭ : 𝓟 X → L such that:
(i)  f♭ is a sup-lattice homomorphism, i.e.
     - f♭ preserves joins (of families indexed by types in 𝓥)
(ii) the diagram
           f
     X ---------> L
      \          ^
       \        /
      η \      / ∃! f♭
         \    /
          v  /
          𝓟 X
     commutes.

\begin{code}

module _
        (𝓛 : SupLattice 𝓥 𝓤 𝓣)
       where

 open SupLattice 𝓛

 module _
         (X : 𝓥 ̇ )
         (X-is-set : is-set X)
         (f : X → L)
        where

  f♭ : 𝓟 X → L
  f♭ A = ⋁ {𝕋 A} (f ∘ pr₁)

  η : X → 𝓟 X
  η = ⦅_⦆[ X-is-set ]

  f♭-after-η-is-f : f♭ ∘ η ∼ f
  f♭-after-η-is-f x = ⊑-is-antisymmetric ((f♭ ∘ η) x) (f x) u v
   where
    u : ⋁ (λ x₁ → f (pr₁ x₁)) ⊑ f x
    u = ⋁-is-lowerbound-of-upperbounds (f ∘ pr₁) (f x) γ
     where
      γ : (i : Σ y ꞉ X , y ≡ x) → f (pr₁ i) ⊑ f x
      γ (x , refl) = ⊑-is-reflexive (f x)
    v : f x ⊑ ⋁ (λ x₁ → f (pr₁ x₁))
    v = ⋁-is-upperbound (λ (x , _) → f x) (x , refl)

  f♭-is-monotone : (A B : 𝓟 X) → A ⊆ B → f♭ A ⊑ f♭ B
  f♭-is-monotone A B s = ⋁-is-lowerbound-of-upperbounds (f ∘ pr₁) (f♭ B) γ₁
   where
    γ₁ : (i : Σ x ꞉ X , x ∈ A) → f (pr₁ i) ⊑ ⋁ (f ∘ pr₁)
    γ₁ (x , a) = ⋁-is-upperbound (f ∘ pr₁) (x , s x a)

  f♭-preserves-joins : (I : 𝓥 ̇ ) (α : I → 𝓟 X)
                     → f♭ (⋃ α) ≡ ⋁ (f♭ ∘ α)
  f♭-preserves-joins I α = ⊑-is-antisymmetric (f♭ (⋃ α)) (⋁ (f♭ ∘ α)) u v
   where
    u : ⋁ (f ∘ pr₁) ⊑ ⋁ (λ (i : I) → ⋁ (f ∘ pr₁))
    u = ⋁-is-lowerbound-of-upperbounds (f ∘ pr₁) (⋁ (λ i → ⋁ (f ∘ pr₁))) γ
     where
      γ : (p : (Σ x ꞉ X , x ∈ ⋃ α))
        → f (pr₁ p) ⊑ ⋁ (λ i → ⋁ (λ x → f (pr₁ x)))
      γ (x , a) = ∥∥-rec (⊑-is-prop-valued _ _) ψ a
       where
        ψ : (Σ i ꞉ I , x ∈ α i) → f x ⊑ ⋁ (λ i' → ⋁ (f ∘ pr₁))
        ψ (i , a') = f x                    ⊑⟨ u₁ ⟩
                     ⋁ (f ∘ pr₁)            ⊑⟨ u₂ ⟩
                     ⋁ (λ i' → ⋁ (f ∘ pr₁)) ⊑∎
         where
          u₁ = ⋁-is-upperbound (f ∘ pr₁) (x , a')
          u₂ = ⋁-is-upperbound (λ i' → ⋁ (f ∘ pr₁)) i
    v : ⋁ (λ (i : I) → ⋁ (f ∘ pr₁)) ⊑ ⋁ (f ∘ pr₁)
    v = ⋁-is-lowerbound-of-upperbounds (λ i → ⋁ (f ∘ pr₁)) (⋁ (f ∘ pr₁)) γ
     where
      γ : (i : I)
        → ⋁ {Σ x ꞉ X , x ∈ α i} (f ∘ pr₁) ⊑ ⋁ {Σ x ꞉ X , x ∈ ⋃ α} (f ∘ pr₁)
      γ i = ⋁-is-lowerbound-of-upperbounds (f ∘ pr₁) (⋁ (f ∘ pr₁)) ψ
       where
        ψ : (p : Σ x ꞉ X , x ∈ α i)
          → f (pr₁ p) ⊑ ⋁ (f ∘ pr₁)
        ψ (x , a) = ⋁-is-upperbound (f ∘ pr₁) (x , ∣ i , a ∣)

\end{code}

Finally we prove that f♭ is the unique map with the above properties (i) & (ii).

\begin{code}

  module _
          (pe : propext 𝓥)
          (fe : funext 𝓥 (𝓥 ⁺))
         where

   f♭-is-unique : (h : 𝓟 X → L)
                → ((I : 𝓥 ̇ ) (α : I → 𝓟 X) → h (⋃ α) ≡ ⋁ (h ∘ α))
                → (h ∘ η ∼ f)
                → h ∼ f♭
   f♭-is-unique h p₁ p₂ A =
    h A               ≡⟨ ap h (express-subset-as-union-of-singletons pe fe X X-is-set A) ⟩
    h (⋃ (η ∘ pr₁))   ≡⟨ p₁ (𝕋 A) (η ∘ pr₁) ⟩
    ⋁ (h ∘ η ∘ pr₁)   ≡⟨ ⋁-transport (h ∘ η ∘ pr₁) (f ∘ pr₁) (λ p → p₂ (pr₁ p)) ⟩
    ⋁ (f ∘ pr₁)       ≡⟨ refl ⟩
    f♭ A ∎

\end{code}

Assuming some more function extensionality axioms, we can prove "homotopy
uniqueness", i.e. the tuple consisting of f♭ together with the proofs of (i) and
(ii) is unique. This follows easily from the above, because (i) and (ii) are
subsingletons (as L is a set).

\begin{code}

  module _
          (pe : propext 𝓥)
          (fe : funext (𝓥 ⁺) (𝓥 ⁺ ⊔ 𝓤))
         where

   homotopy-uniqueness-of-f♭ :
    ∃! h ꞉ (𝓟 X → L) , (((I : 𝓥 ̇ ) (α : I → 𝓟 X) → h (⋃ α) ≡ ⋁ (h ∘ α)))
                     × (h ∘ η ∼ f)
   homotopy-uniqueness-of-f♭ =
    (f♭ , f♭-preserves-joins , f♭-after-η-is-f) , γ
     where
      γ : (t : (Σ h ꞉ (𝓟 X → L) ,
                   (((I : 𝓥 ̇ ) (α : I → 𝓟 X) → h (⋃ α) ≡ ⋁ (h ∘ α)))
                 × (h ∘ η ∼ f)))
        → (f♭ , f♭-preserves-joins , f♭-after-η-is-f) ≡ t
      γ (h , p₁ , p₂) = to-subtype-≡ ψ
                        (dfunext (lower-funext (𝓥 ⁺) (𝓥 ⁺) fe)
                          (λ A → (f♭-is-unique
                                   pe
                                   (lower-funext (𝓥 ⁺) 𝓤 fe)
                                   h p₁ p₂ A) ⁻¹))
       where
        ψ : (k : 𝓟 X → L)
          → is-prop (((I : 𝓥 ̇ ) (α : I → 𝓟 X) → k (⋃ α) ≡ ⋁ (k ∘ α))
                    × k ∘ η ∼ f)
        ψ k = ×-is-prop (Π-is-prop fe
                              (λ _ → Π-is-prop (lower-funext (𝓥 ⁺) (𝓥 ⁺) fe)
                              (λ _ → L-is-set)))
                            (Π-is-prop (lower-funext (𝓥 ⁺) (𝓥 ⁺) fe)
                              (λ _ → L-is-set))

\end{code}
