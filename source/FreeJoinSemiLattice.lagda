Tom de Jong, 18-24 December 2020
(Formalizing a paper proof sketch from 12 November 2020)

We construct the free join-semilattice on a set X as the Kuratowski finite
subsets of X.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import ArithmeticViaEquivalence
open import Fin hiding (⟨_⟩)
open import SpartanMLTT

open import UF-Base
open import UF-Equiv
open import UF-FunExt
open import UF-Lower-FunExt
open import UF-ImageAndSurjection
open import UF-Powerset
open import UF-PropTrunc
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

module FreeJoinSemiLattice
        (pt : propositional-truncations-exist)
       where

open ImageAndSurjection pt
open PropositionalTruncation pt hiding (_∨_)

\end{code}

We start with some basic constructions on the powerset.

\begin{code}

𝕋  : {X : 𝓤 ̇ } → 𝓟 X → 𝓤 ̇
𝕋 {𝓤} {X} A = Σ x ꞉ X , (x ∈ A)

𝕋-to-carrier : {X : 𝓤 ̇ } (A : 𝓟 X) → 𝕋 A → X
𝕋-to-carrier A = pr₁

𝕋-to-membership : {X : 𝓤 ̇ } (A : 𝓟 X) (t : 𝕋 A) → (𝕋-to-carrier A t) ∈ A
𝕋-to-membership A = pr₂

⦅_⦆[_] : {X : 𝓤 ̇ } → X → is-set X → 𝓟 X
⦅ x ⦆[ i ] = (λ y → ((y ≡ x) , i))

∅ : {X : 𝓤 ̇ } → 𝓟 X
∅ x = 𝟘 , 𝟘-is-prop

∅-is-least : {X : 𝓤 ̇ } (A : 𝓟 X) → ∅ ⊆ A
∅-is-least x _ = 𝟘-induction

_∪_ : {X : 𝓤 ̇ } → 𝓟 X → 𝓟 X → 𝓟 X
(A ∪ B) x = ∥ x ∈ A + x ∈ B ∥ , ∥∥-is-prop

to-∪₁ : {X : 𝓤 ̇ } (A B : 𝓟 X) {x : X} → x ∈ A → x ∈ (A ∪ B)
to-∪₁ A B a = ∣ inl a ∣

to-∪₂ : {X : 𝓤 ̇ } (A B : 𝓟 X) {x : X} → x ∈ B → x ∈ (A ∪ B)
to-∪₂ A B b = ∣ inr b ∣

∪-is-upperbound₁ : {X : 𝓤 ̇ } (A B : 𝓟 X) → A ⊆ (A ∪ B)
∪-is-upperbound₁ A B x a = ∣ inl a ∣

∪-is-upperbound₂ : {X : 𝓤 ̇ } (A B : 𝓟 X) → B ⊆ (A ∪ B)
∪-is-upperbound₂ A B x b = ∣ inr b ∣

∪-is-lowerbound-of-upperbounds : {X : 𝓤 ̇ } (A B C : 𝓟 X)
                               → A ⊆ C → B ⊆ C → (A ∪ B) ⊆ C
∪-is-lowerbound-of-upperbounds {𝓤} {X} A B C s t x = ∥∥-rec (∈-is-prop C x) γ
  where
   γ : (x ∈ A + x ∈ B) → x ∈ C
   γ (inl a) = s x a
   γ (inr b) = t x b

\end{code}

Next we define when a type is Kuratowski finite and we construct the type 𝓚 X of
Kuratowski finite subsets of X.

\begin{code}

is-Kuratowski-finite :  𝓤 ̇ → 𝓤 ̇
is-Kuratowski-finite X = ∃ n ꞉ ℕ , Σ e ꞉ (Fin n → X) , is-surjection e

being-Kuratowski-finite-is-prop : {X : 𝓤 ̇ } → is-prop (is-Kuratowski-finite X)
being-Kuratowski-finite-is-prop = ∥∥-is-prop

𝓚 : 𝓤 ̇ → 𝓤 ⁺ ̇
𝓚 X = Σ A ꞉ 𝓟 X , is-Kuratowski-finite (𝕋 A)

⟨_⟩ : {X : 𝓤 ̇ } → 𝓚 X → 𝓟 X
⟨_⟩ = pr₁

⟨_⟩₂ : {X : 𝓤 ̇ } (A : 𝓚 X) → is-Kuratowski-finite (𝕋 ⟨ A ⟩)
⟨_⟩₂ = pr₂

\end{code}

The empty set and singletons and Kuratowski finite subsets.

\begin{code}

η : {X : 𝓤 ̇ } → is-set X → X → 𝓚 X
η i x = ⦅ x ⦆[ i ] , κ
 where
  κ : is-Kuratowski-finite (𝕋 ⦅ x ⦆[ i ])
  κ = ∣ 1 , e , σ ∣
   where
    e : Fin 1 → 𝕋 ⦅ x ⦆[ i ]
    e 𝟎 = x , refl
    σ : is-surjection e
    σ (x , refl) = ∣ inr * , refl ∣

from-Fin-0 : {X : 𝓤 ̇ } → Fin 0 → X
from-Fin-0 = unique-from-𝟘

∅-is-Kuratowski-finite : {X : 𝓤 ̇ }
                       → is-Kuratowski-finite (𝕋 {𝓤} {X} ∅)
∅-is-Kuratowski-finite = ∣ 0 , from-Fin-0 , σ ∣
 where
  σ : (t : 𝕋 ∅) → ∃ k ꞉ Fin 0 , from-Fin-0 k ≡ t
  σ (x , e) = unique-from-𝟘 e

⊥[𝓚] : {X : 𝓤 ̇ } → 𝓚 X
⊥[𝓚] {X} = ∅ , ∅-is-Kuratowski-finite

\end{code}

As a subtype of the powerset 𝓟 X, the type of Kuratowski finite subsets can be
partially ordered by subset inclusion and is a set.

\begin{code}

_⊑[𝓚]_ : {X : 𝓤 ̇ } → 𝓚 X → 𝓚 X → 𝓤 ̇
A ⊑[𝓚] B = ⟨ A ⟩ ⊆ ⟨ B ⟩

⊑[𝓚]-is-reflexive : {X : 𝓤 ̇ } (A : 𝓚 X) → A ⊑[𝓚] A
⊑[𝓚]-is-reflexive {𝓤} {X} A = ⊆-refl ⟨ A ⟩

⊑[𝓚]-is-transitive : {X : 𝓤 ̇ } (A B C : 𝓚 X) → A ⊑[𝓚] B → B ⊑[𝓚] C → A ⊑[𝓚] C
⊑[𝓚]-is-transitive {𝓤} {X} A B C = ⊆-trans ⟨ A ⟩ ⟨ B ⟩ ⟨ C ⟩

module _
        (fe : funext 𝓤 (𝓤 ⁺))
       where

 ⊑[𝓚]-is-prop-valued : {X : 𝓤 ̇ } (A B : 𝓚 X) → is-prop (A ⊑[𝓚] B)
 ⊑[𝓚]-is-prop-valued {X} A B = ⊆-is-prop (lower-funext 𝓤 (𝓤 ⁺) fe) ⟨ A ⟩ ⟨ B ⟩

 module _
        (pe : propext 𝓤)
       where

  ⊑[𝓚]-is-antisymmetric : {X : 𝓤 ̇ } (A B : 𝓚 X) → A ⊑[𝓚] B → B ⊑[𝓚] A → A ≡ B
  ⊑[𝓚]-is-antisymmetric {X} A B s t =
   to-subtype-≡ (λ _ → being-Kuratowski-finite-is-prop)
                (subset-extensionality pe fe s t)

  𝓚-is-set : {X : 𝓤 ̇ } → is-set (𝓚 X)
  𝓚-is-set {X} = subtypes-of-sets-are-sets ⟨_⟩ s (powersets-are-sets fe pe)
    where
     s : left-cancellable ⟨_⟩
     s e = to-subtype-≡ (λ _ → being-Kuratowski-finite-is-prop) e

\end{code}

We proceed by showing that 𝓚 X has binary joins, specifically if A and B are
Kuratowski finite subsets, then so is A ∪ B.

\begin{code}

∪-enum' : {X : 𝓤 ̇ } (A B : 𝓟 X) {n m : ℕ}
        → (Fin n → 𝕋 A)
        → (Fin m → 𝕋 B)
        → (Fin n + Fin m) → 𝕋 (A ∪ B)
∪-enum' A B e f (inl k) = (𝕋-to-carrier A (e k) ,
                           to-∪₁ A B (𝕋-to-membership A (e k)))
∪-enum' A B e f (inr k) = (𝕋-to-carrier B (f k) ,
                           to-∪₂ A B (𝕋-to-membership B (f k)))

∪-enum : {X : 𝓤 ̇ } (A B : 𝓟 X) {n m : ℕ}
       → (Fin n → 𝕋 A)
       → (Fin m → 𝕋 B)
       → Fin (n +' m) → 𝕋 (A ∪ B)
∪-enum A B {n} {m} e f = ∪-enum' A B e f ∘ ⌜ Fin+homo n m ⌝

∪-enum'-is-surjection : {X : 𝓤 ̇ } (A B : 𝓟 X) {n m : ℕ}
                        (e : Fin n → 𝕋 A)
                        (f : Fin m → 𝕋 B)
                      → is-surjection e
                      → is-surjection f
                      → is-surjection (∪-enum' A B e f)
∪-enum'-is-surjection A B {n} {m} e f σ τ (x , p) = ∥∥-rec ∥∥-is-prop γ p
  where
   γ : (x ∈ A + x ∈ B)
     → ∃ c ꞉ (Fin n + Fin m) , ∪-enum' A B e f c ≡ (x , p)
   γ (inl a) = ∥∥-functor γ₁ (σ (x , a))
    where
     γ₁ : (Σ k ꞉ Fin n , e k ≡ (x , a))
        → Σ c ꞉ (Fin n + Fin m) , ∪-enum' A B e f c ≡ (x , p)
     γ₁ (k , p) = inl k , to-subtype-≡ (∈-is-prop (A ∪ B)) (ap pr₁ p)
   γ (inr b) = ∥∥-functor γ₂ (τ (x , b))
    where
     γ₂ : (Σ k ꞉ Fin m , f k ≡ (x , b))
        → Σ c ꞉ (Fin n + Fin m) , ∪-enum' A B e f c ≡ (x , p)
     γ₂ (k , p) = inr k , to-subtype-≡ (∈-is-prop (A ∪ B)) (ap pr₁ p)

∪-enum-is-surjection : {X : 𝓤 ̇ } (A B : 𝓟 X) {n m : ℕ}
                       (e : Fin n → 𝕋 A)
                       (f : Fin m → 𝕋 B)
                     → is-surjection e
                     → is-surjection f
                     → is-surjection (∪-enum A B e f)
∪-enum-is-surjection A B {n} {m} e f σ τ =
 ∘-is-surjection
  (equivs-are-surjections (⌜⌝-is-equiv (Fin+homo n m)))
  (∪-enum'-is-surjection A B e f σ τ)

_∨[𝓚]_ : {X : 𝓤 ̇ } → 𝓚 X → 𝓚 X → 𝓚 X
_∨[𝓚]_ {𝓤} {X} (A , κ₁) (B , κ₂) = (A ∪ B) , κ
 where
  κ : is-Kuratowski-finite (𝕋 (A ∪ B))
  κ = ∥∥-rec being-Kuratowski-finite-is-prop γ₁ κ₁
   where
    γ₁ : (Σ n ꞉ ℕ , Σ e ꞉ (Fin n → 𝕋 A) , is-surjection e)
       → is-Kuratowski-finite (𝕋 (A ∪ B))
    γ₁ (n , e , σ) = ∥∥-rec being-Kuratowski-finite-is-prop γ₂ κ₂
     where
      γ₂ : (Σ m ꞉ ℕ , Σ f ꞉ (Fin m → 𝕋 B) , is-surjection f)
         → is-Kuratowski-finite (𝕋 (A ∪ B))
      γ₂ (m , f , τ) = ∣ (n +' m) , g , ρ ∣
       where
        g : Fin (n +' m) → 𝕋 (A ∪ B)
        g = ∪-enum A B e f
        ρ : is-surjection g
        ρ = ∪-enum-is-surjection A B e f σ τ

∨[𝓚]-is-upperbound₁ : {X : 𝓤 ̇ } (A B : 𝓚 X) → A ⊑[𝓚] (A ∨[𝓚] B)
∨[𝓚]-is-upperbound₁ {𝓤} {X} A B = ∪-is-upperbound₁ ⟨ A ⟩ ⟨ B ⟩

∨[𝓚]-is-upperbound₂ : {X : 𝓤 ̇ } (A B : 𝓚 X) → B ⊑[𝓚] (A ∨[𝓚] B)
∨[𝓚]-is-upperbound₂ {𝓤} {X} A B = ∪-is-upperbound₂ ⟨ A ⟩ ⟨ B ⟩

∨[𝓚]-is-lowerbound-of-upperbounds : {X : 𝓤 ̇ } (A B C : 𝓚 X)
                             → A ⊑[𝓚] C → B ⊑[𝓚] C → (A ∨[𝓚] B) ⊑[𝓚] C
∨[𝓚]-is-lowerbound-of-upperbounds {𝓤} {X} A B C =
 ∪-is-lowerbound-of-upperbounds ⟨ A ⟩ ⟨ B ⟩ ⟨ C ⟩

\end{code}

Finally, the empty set (considered as a Kuratowski finite subset) is of course
the least Kuratowski finite subset.

\begin{code}

⊥[𝓚]-is-least : {X : 𝓤 ̇ } (A : 𝓚 X) → ⊥[𝓚] ⊑[𝓚] A
⊥[𝓚]-is-least {𝓤} {X} A = ∅-is-least ⟨ A ⟩

\end{code}

We define join-semilattices using a record. We also introduce convenient helpers
and syntax for reasoning about the order ⊑ and we construct finite joins using
the least element and binary joins.

\begin{code}

record JoinSemiLattice (𝓥 𝓣 : Universe) : 𝓤ω where
  constructor
    joinsemilattice
  field
    L : 𝓥 ̇
    L-is-set : is-set L
    _⊑_ : L → L → 𝓣 ̇
    ⊑-is-prop-valued : (x y : L) → is-prop (x ⊑ y)
    ⊑-is-reflexive : (x : L) → x ⊑ x
    ⊑-is-transitive : (x y z : L) → x ⊑ y → y ⊑ z → x ⊑ z
    ⊑-is-antisymmetric : (x y : L) → x ⊑ y → y ⊑ x → x ≡ y
    ⊥ : L
    ⊥-is-least : (x : L) → ⊥ ⊑ x
    _∨_ : L → L → L
    ∨-is-upperbound₁ : (x y : L) → x ⊑ (x ∨ y)
    ∨-is-upperbound₂ : (x y : L) → y ⊑ (x ∨ y)
    ∨-is-lowerbound-of-upperbounds : (x y z : L) → x ⊑ z → y ⊑ z → (x ∨ y) ⊑ z

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

  ∨ⁿ : {n : ℕ} → (Fin n → L) → L
  ∨ⁿ {zero}   e = ⊥
  ∨ⁿ {succ m} e = (∨ⁿ (e ∘ suc)) ∨ (e 𝟎)

  ∨ⁿ-is-upperbound : {n : ℕ} (σ : Fin n → L)
                   → (k : Fin n) → σ k ⊑ ∨ⁿ σ
  ∨ⁿ-is-upperbound {succ n} σ 𝟎       = ∨-is-upperbound₂ _ _
  ∨ⁿ-is-upperbound {succ n} σ (suc k) = σ (suc k)    ⊑⟨ IH ⟩
                                        ∨ⁿ (σ ∘ suc) ⊑⟨ ∨-is-upperbound₁ _ _ ⟩
                                        ∨ⁿ σ         ⊑∎
   where
    IH = ∨ⁿ-is-upperbound (σ ∘ suc) k

  ∨ⁿ-is-lowerbound-of-upperbounds : {n : ℕ} (σ : Fin n → L)
                                    (x : L)
                                  → ((k : Fin n) → σ k ⊑ x)
                                  → ∨ⁿ σ ⊑ x
  ∨ⁿ-is-lowerbound-of-upperbounds {zero}   σ x ub = ⊥-is-least x
  ∨ⁿ-is-lowerbound-of-upperbounds {succ n} σ x ub =
   ∨-is-lowerbound-of-upperbounds _ _ _ u v
    where
     u : ∨ⁿ (σ ∘ suc) ⊑ x
     u = ∨ⁿ-is-lowerbound-of-upperbounds {n} (σ ∘ suc) x (ub ∘ suc)
     v : σ 𝟎 ⊑ x
     v = ub 𝟎

\end{code}

The Kuratowski finite subsets are an example of a join-semilattice.

\begin{code}

module _
        (pe : propext 𝓤)
        (fe : funext 𝓤 (𝓤 ⁺))
        (X : 𝓤 ̇ )
        (X-is-set : is-set X)
       where

\end{code}

We use copatterns instead of the below (which we left for comparison),
because copatterns are said to avoid unnecessary unfoldings in
typechecking.

\begin{code}

 𝓚-join-semilattice : JoinSemiLattice (𝓤 ⁺) 𝓤
 JoinSemiLattice.L                              𝓚-join-semilattice = 𝓚 X
 JoinSemiLattice.L-is-set                       𝓚-join-semilattice = 𝓚-is-set fe pe
 JoinSemiLattice._⊑_                            𝓚-join-semilattice = _⊑[𝓚]_
 JoinSemiLattice.⊑-is-prop-valued               𝓚-join-semilattice = ⊑[𝓚]-is-prop-valued fe
 JoinSemiLattice.⊑-is-reflexive                 𝓚-join-semilattice = ⊑[𝓚]-is-reflexive
 JoinSemiLattice.⊑-is-transitive                𝓚-join-semilattice = ⊑[𝓚]-is-transitive
 JoinSemiLattice.⊑-is-antisymmetric             𝓚-join-semilattice = ⊑[𝓚]-is-antisymmetric fe pe
 JoinSemiLattice.⊥                              𝓚-join-semilattice = ⊥[𝓚]
 JoinSemiLattice.⊥-is-least                     𝓚-join-semilattice = ⊥[𝓚]-is-least
 JoinSemiLattice._∨_                            𝓚-join-semilattice = _∨[𝓚]_
 JoinSemiLattice.∨-is-upperbound₁               𝓚-join-semilattice = ∨[𝓚]-is-upperbound₁
 JoinSemiLattice.∨-is-upperbound₂               𝓚-join-semilattice = ∨[𝓚]-is-upperbound₂
 JoinSemiLattice.∨-is-lowerbound-of-upperbounds 𝓚-join-semilattice = ∨[𝓚]-is-lowerbound-of-upperbounds

 {-
 𝓚-join-semilattice = joinsemilattice
                        (𝓚 X)
                        (𝓚-is-set fe pe)
                        _⊑[𝓚]_
                        (⊑[𝓚]-is-prop-valued fe)
                        ⊑[𝓚]-is-reflexive
                        ⊑[𝓚]-is-transitive
                        (⊑[𝓚]-is-antisymmetric fe pe)
                        ⊥[𝓚]
                        ⊥[𝓚]-is-least
                        _∨[𝓚]_
                        ∨[𝓚]-is-upperbound₁
                        ∨[𝓚]-is-upperbound₂
                        ∨[𝓚]-is-lowerbound-of-upperbounds
 -}

\end{code}

The following lemma is absolutely crucial. Any Kuratowski finite subset can be
expressed as a finite join of singletons. This lemma also allows us to prove an
abstract induction principle for Kuratowski finite subsets.

\begin{code}

 open JoinSemiLattice 𝓚-join-semilattice

 Kuratowski-finite-subset-expressed-as-finite-join : (A : 𝓚 X)
                                                     {n : ℕ}
                                                     {e : Fin n → 𝕋 ⟨ A ⟩}
                                                     (σ : is-surjection e)
                                                   → A ≡ ∨ⁿ (η X-is-set
                                                            ∘ 𝕋-to-carrier ⟨ A ⟩
                                                            ∘ e)
 Kuratowski-finite-subset-expressed-as-finite-join A {n} {e} σ = γ
  where
   ε : Fin n → 𝓚 X
   ε = η X-is-set ∘ 𝕋-to-carrier ⟨ A ⟩ ∘ e
   γ : A ≡ ∨ⁿ ε
   γ = ⊑[𝓚]-is-antisymmetric fe pe A (∨ⁿ ε) u v
    where
     u : A ⊑[𝓚] ∨ⁿ ε
     u x a = ∥∥-rec (∈-is-prop ⟨ ∨ⁿ ε ⟩ x) μ (σ (x , a))
      where
       μ : (Σ k ꞉ Fin n , e k ≡ (x , a))
         → x ∈ ⟨ ∨ⁿ ε ⟩
       μ (k , refl) = ∨ⁿ-is-upperbound ε k x refl
     v : ∨ⁿ ε ⊑[𝓚] A
     v = ∨ⁿ-is-lowerbound-of-upperbounds ε A ν
      where
       ν : (k : Fin n) → ε k ⊑[𝓚] A
       ν k x refl = 𝕋-to-membership ⟨ A ⟩ (e k)

 Kuratowski-finite-subset-induction : {𝓣 : Universe}
                                      (P : 𝓚 X → 𝓣 ̇ )
                                    → ((A : 𝓚 X) → is-prop (P A))
                                    → P (⊥[𝓚])
                                    → ((x : X) → P (η X-is-set x))
                                    → ((A B : 𝓚 X) → P A → P B → P (A ∨[𝓚] B))
                                    → (A : 𝓚 X) → P A
 Kuratowski-finite-subset-induction P i p₁ p₂ p₃ A = ∥∥-rec (i A) γ ⟨ A ⟩₂
  where
   γ : (Σ n ꞉ ℕ , Σ e ꞉ (Fin n → 𝕋 ⟨ A ⟩) , is-surjection e)
     → P A
   γ (n , e , σ) = transport P ϕ (ψ n (𝕋-to-carrier ⟨ A ⟩ ∘ e))
    where
     ϕ : ∨ⁿ (η X-is-set ∘ 𝕋-to-carrier ⟨ A ⟩ ∘ e) ≡ A
     ϕ = (Kuratowski-finite-subset-expressed-as-finite-join A σ) ⁻¹
     ψ : (m : ℕ) (f : Fin m → X) → P (∨ⁿ (η X-is-set ∘ f))
     ψ zero     f = p₁
     ψ (succ m) f = p₃
                     (∨ⁿ (η X-is-set ∘ f ∘ suc)) ((η X-is-set ∘ f) 𝟎)
                     (ψ m (f ∘ suc)) (p₂ (f 𝟎))

\end{code}

Finally we will show that 𝓚 X is the free join-semilattice on a set X.
Concretely, if L is a join-semilattice and f : X → L is any function, then there
is a *unique* mediating map f♭ : 𝓚 X → L such that:
(i)  f♭ is a join-semilattice homomorphism, i.e.
     - f♭ preserves the least element;
     - f♭ preserves binary joins.
(ii) the diagram
           f
     X ---------> L
      \          ^
       \        /
      η \      / ∃! f♭
         \    /
          v  /
          𝓚 X
     commutes.

The idea in defining f♭ is to map a Kuratowski finite subset A to the finite
join ∨ⁿ (f ∘ 𝕋-to-carrier ⟨ A ⟩ ∘ e) in L, where e is some eumeration
(i.e. surjection) e : Fin n ↠ 𝕋 ⟨ A ⟩.

However, since Kuratowski finite subsets come with an *unspecified* such
enumeration, we must show that the choice of enumeration is irrelevant, i.e. any
two enumerations give rise to the same finite join. We then use a theorem by
Kraus et al. [1] (see wconstant-map-to-set-factors-through-truncation-of-domain)
to construct the desired mapping.

[1] Theorem 5.4 in
    "Notions of Anonymous Existence in Martin-Löf Type Theory"
    by Nicolai Kraus, Martín Escardó, Thierry Coquand and Thorsten Altenkirch.
    In Logical Methods in Computer Science, volume 13, issue 1.
    2017.

\begin{code}

module _
        (𝓛 : JoinSemiLattice 𝓥 𝓣)
       where

 open JoinSemiLattice 𝓛

 module _
         (X : 𝓤 ̇ )
         (X-is-set : is-set X)
         (f : X → L)
        where

\end{code}

We start by defining the mapping for a specified enumeration and we show that
the choice of enumeration is irrelevant, i.e. fₛ A is weakly constant.

\begin{code}
  fₛ : (A : 𝓟 X)
     → (Σ n ꞉ ℕ , Σ e ꞉ (Fin n → 𝕋 A) , is-surjection e)
     → L
  fₛ A (_ , e , _) = ∨ⁿ (f ∘ pr₁ ∘ e)

  fₛ-is-wconstant : (A : 𝓟 X) → wconstant (fₛ A)
  fₛ-is-wconstant A (n , e , σ) (n' , e' , σ') = ⊑-is-antisymmetric _ _ u v
   where
    f' : 𝕋 A → L
    f' = f ∘ 𝕋-to-carrier A
    u : ∨ⁿ (f' ∘ e) ⊑ ∨ⁿ (f' ∘ e')
    u = ∨ⁿ-is-lowerbound-of-upperbounds (f' ∘ e) (∨ⁿ (f' ∘ e')) ψ
     where
      ψ : (k : Fin n) → (f' ∘ e) k ⊑ ∨ⁿ (f' ∘ e')
      ψ k = ∥∥-rec (⊑-is-prop-valued _ _) ϕ (σ' (e k))
       where
        ϕ : (Σ k' ꞉ Fin n' , e' k' ≡ e k) → (f' ∘ e) k ⊑ ∨ⁿ (f' ∘ e')
        ϕ (k' , p) = (f' ∘ e) k   ⊑⟨ ≡-to-⊑ (ap f' p ⁻¹) ⟩
                     (f' ∘ e') k' ⊑⟨ ∨ⁿ-is-upperbound (f' ∘ e') k' ⟩
                     ∨ⁿ (f' ∘ e') ⊑∎
    v : ∨ⁿ (f' ∘ e') ⊑ ∨ⁿ (f' ∘ e)
    v = ∨ⁿ-is-lowerbound-of-upperbounds (f' ∘ e') (∨ⁿ (f' ∘ e)) ψ
     where
      ψ : (k' : Fin n') → (f' ∘ e') k' ⊑ ∨ⁿ (f' ∘ e)
      ψ k' = ∥∥-rec (⊑-is-prop-valued _ _) ϕ (σ (e' k'))
       where
        ϕ : (Σ k ꞉ Fin n , e k ≡ e' k') → (f' ∘ e') k' ⊑ ∨ⁿ (f' ∘ e)
        ϕ (k , p) = (f' ∘ e') k' ⊑⟨ ≡-to-⊑ (ap f' p ⁻¹) ⟩
                    (f' ∘ e) k   ⊑⟨ ∨ⁿ-is-upperbound (f' ∘ e) k ⟩
                    ∨ⁿ (f' ∘ e)  ⊑∎

\end{code}

We now use the theorem by Kraus et al. to construct the map f♭ from fₛ.

\begin{code}

  f♭ : 𝓚 X → L
  f♭ (A , κ) =
   wconstant-map-to-set-truncation-of-domain-map _ L-is-set
    (fₛ A) (fₛ-is-wconstant A) κ

  f♭-in-terms-of-fₛ : (A : 𝓟 X) {n : ℕ} {e : (Fin n → 𝕋 A)} (σ : is-surjection e)
                     (κ : is-Kuratowski-finite (𝕋 A))
                   → f♭ (A , κ) ≡ fₛ A (n , e , σ)
  f♭-in-terms-of-fₛ A {n} {e} σ κ = f♭ (A , κ)             ≡⟨ I  ⟩
                                    f♭ (A , ∣ n , e , σ ∣) ≡⟨ II ⟩
                                    fₛ A (n , e , σ)       ∎
   where
    I  = ap (λ - → f♭ (A , -)) (∥∥-is-prop κ ∣ n , e , σ ∣)
    II = (wconstant-map-to-set-factors-through-truncation-of-domain
          (Σ n ꞉ ℕ , Σ e ꞉ (Fin n → 𝕋 A) , is-surjection e) L-is-set
          (fₛ A) (fₛ-is-wconstant A) (n , e , σ)) ⁻¹

\end{code}

Recall that we must show that
(i)  f♭ is a join-semilattice homomorphism, i.e.
     - f♭ preserves the least element;
     - f♭ preserves binary joins.
(ii) the diagram
           f
     X ---------> L
      \          ^
       \        /
      η \      / ∃! f♭
         \    /
          v  /
          𝓚 X
     commutes.

We show (ii) and then (i) now.

\begin{code}

  f♭-after-η-is-f : f♭ ∘ (η X-is-set) ∼ f
  f♭-after-η-is-f x = f♭ (η X-is-set x) ≡⟨ I  ⟩
                      fₛ A (1 , e , σ)  ≡⟨ II ⟩
                      f x               ∎
   where
    A : 𝓟 X
    A = ⦅ x ⦆[ X-is-set ]
    e : Fin 1 → 𝕋 A
    e 𝟎 = x , refl
    σ : is-surjection e
    σ (x , refl) = ∣ 𝟎 , refl ∣
    I = f♭-in-terms-of-fₛ A σ ⟨ η X-is-set x ⟩₂
    II = ⊑-is-antisymmetric _ _
          (∨-is-lowerbound-of-upperbounds _ _ _
           (⊥-is-least (f x)) (⊑-is-reflexive (f x)))
          (∨-is-upperbound₂ _ _)

  f♭-preserves-⊥ : f♭ (⊥[𝓚]) ≡ ⊥
  f♭-preserves-⊥ = ⊑-is-antisymmetric _ _ u v
   where
    u : f♭ ⊥[𝓚] ⊑ ⊥
    u = f♭ ⊥[𝓚]                                        ⊑⟨ u₁ ⟩
        ∨ⁿ (f ∘ 𝕋-to-carrier ∅ ∘ from-Fin-0 {𝓤} {𝕋 ∅}) ⊑⟨ u₂ ⟩
        ⊥                                              ⊑∎
     where
      σ : is-surjection (from-Fin-0 {𝓤} {𝕋 ∅})
      σ (x , e) = unique-from-𝟘 e
      u₁ = ≡-to-⊑ (f♭-in-terms-of-fₛ ∅ σ ∅-is-Kuratowski-finite)
      u₂ = ⊑-is-reflexive ⊥
    v : ⊥ ⊑ f♭ ⊥[𝓚]
    v = ⊥-is-least (f♭ ⊥[𝓚])

  f♭-is-monotone : (A B : 𝓚 X)
                → ((x : X) → x ∈ ⟨ A ⟩ → x ∈ ⟨ B ⟩)
                → f♭ A ⊑ f♭ B
  f♭-is-monotone (A , κ₁) (B , κ₂) s = ∥∥-rec (⊑-is-prop-valued _ _) γ₁ κ₁
   where
    γ₁ : (Σ n ꞉ ℕ , Σ e ꞉ (Fin n → 𝕋 A) , is-surjection e)
       → f♭ (A , κ₁) ⊑ f♭ (B , κ₂)
    γ₁ (n , e , σ) = ∥∥-rec (⊑-is-prop-valued _ _) γ₂ κ₂
     where
      γ₂ : (Σ n' ꞉ ℕ , Σ e' ꞉ (Fin n' → 𝕋 B) , is-surjection e')
         → f♭ (A , κ₁) ⊑ f♭ (B , κ₂)
      γ₂ (n' , e' , σ') = f♭ (A , κ₁)                  ⊑⟨ u₁ ⟩
                          ∨ⁿ (f ∘ 𝕋-to-carrier A ∘ e)  ⊑⟨ u₂ ⟩
                          ∨ⁿ (f ∘ 𝕋-to-carrier B ∘ e') ⊑⟨ u₃ ⟩
                          f♭ (B , κ₂)                  ⊑∎
       where
        u₁ = ≡-to-⊑ (f♭-in-terms-of-fₛ A σ κ₁)
        u₃ = ≡-to-⊑ ((f♭-in-terms-of-fₛ B σ' κ₂) ⁻¹)
        u₂ = ∨ⁿ-is-lowerbound-of-upperbounds (f ∘ 𝕋-to-carrier A ∘ e)
                                             (∨ⁿ (f ∘ 𝕋-to-carrier B ∘ e')) γ₃
         where
          γ₃ : (k : Fin n) → (f ∘ 𝕋-to-carrier A ∘ e) k
                           ⊑ ∨ⁿ (f ∘ 𝕋-to-carrier B ∘ e')
          γ₃ k = ∥∥-rec (⊑-is-prop-valued _ _) γ₄ t
           where
            x : X
            x = 𝕋-to-carrier A (e k)
            a : x ∈ A
            a = 𝕋-to-membership A (e k)
            b : x ∈ B
            b = s x a
            t : ∃ k' ꞉ Fin n' , e' k' ≡ (x , b)
            t = σ' (x , b)
            γ₄ : (Σ k' ꞉ Fin n' , e' k' ≡ (x , b))
               → (f ∘ pr₁ ∘ e) k ⊑ ∨ⁿ (f ∘ pr₁ ∘ e')
            γ₄ (k' , p) = (f ∘ 𝕋-to-carrier A) (e k)   ⊑⟨ v₁ ⟩
                          (f ∘ 𝕋-to-carrier B) (e' k') ⊑⟨ v₂ ⟩
                          ∨ⁿ (f ∘ 𝕋-to-carrier B ∘ e') ⊑∎
             where
              v₁ = ≡-to-⊑ (ap f q)
               where
                q : 𝕋-to-carrier A (e k) ≡ 𝕋-to-carrier B (e' k')
                q = ap pr₁ (p ⁻¹)
              v₂ = ∨ⁿ-is-upperbound (f ∘ 𝕋-to-carrier B ∘ e') k'

  f♭-preserves-∨ : (A B : 𝓚 X) → f♭ (A ∨[𝓚] B) ≡ f♭ A ∨ f♭ B
  f♭-preserves-∨ A B = ⊑-is-antisymmetric _ _ u v
   where
    v : (f♭ A ∨ f♭ B) ⊑ f♭ (A ∨[𝓚] B)
    v = ∨-is-lowerbound-of-upperbounds _ _ _
        (f♭-is-monotone A (A ∨[𝓚] B) (∨[𝓚]-is-upperbound₁ A B))
        (f♭-is-monotone B (A ∨[𝓚] B) (∨[𝓚]-is-upperbound₂ A B))
    u : f♭ (A ∨[𝓚] B) ⊑ (f♭ A ∨ f♭ B)
    u = ∥∥-rec (⊑-is-prop-valued (f♭ (A ∨[𝓚] B)) (f♭ A ∨ f♭ B)) γ₁ (⟨ A ⟩₂)
     where
      γ₁ : (Σ n ꞉ ℕ , Σ e ꞉ (Fin n → 𝕋 ⟨ A ⟩) , is-surjection e)
         → f♭ (A ∨[𝓚] B) ⊑ (f♭ A ∨ f♭ B)
      γ₁ (n , e , σ) = ∥∥-rec (⊑-is-prop-valued _ _) γ₂ (⟨ B ⟩₂)
       where
        γ₂ : (Σ n' ꞉ ℕ , Σ e' ꞉ (Fin n' → 𝕋 ⟨ B ⟩) , is-surjection e')
           → f♭ (A ∨[𝓚] B) ⊑ (f♭ A ∨ f♭ B)
        γ₂ (n' , e' , σ') = f♭ (A ∨[𝓚] B)    ⊑⟨ l₁ ⟩
                            ∨ⁿ (f' ∘ [e,e']) ⊑⟨ l₂ ⟩
                            f♭ A ∨ f♭ B      ⊑∎
         where
          f' : 𝕋 (⟨ A ⟩ ∪ ⟨ B ⟩) → L
          f' = f ∘ 𝕋-to-carrier (⟨ A ⟩ ∪ ⟨ B ⟩)
          [e,e'] : Fin (n +' n') → 𝕋 (⟨ A ⟩ ∪ ⟨ B ⟩)
          [e,e'] = (∪-enum ⟨ A ⟩ ⟨ B ⟩ e e')
          τ : is-surjection [e,e']
          τ = ∪-enum-is-surjection ⟨ A ⟩ ⟨ B ⟩ e e' σ σ'
          l₁ = ≡-to-⊑ p
           where
            p : f♭ (A ∨[𝓚] B) ≡ fₛ (⟨ A ⟩ ∪ ⟨ B ⟩) (n +' n' , [e,e'] , τ)
            p = f♭-in-terms-of-fₛ (⟨ A ⟩ ∪ ⟨ B ⟩) τ ⟨ A ∨[𝓚] B ⟩₂
          l₂ = ∨ⁿ-is-lowerbound-of-upperbounds (f' ∘ [e,e']) (f♭ A ∨ f♭ B) ϕ
           where
            ϕ : (k : Fin (n +' n'))
              → (f' ∘ [e,e']) k ⊑ (f♭ A ∨ f♭ B)
            ϕ k = (f' ∘ [e,e']) k                   ⊑⟨ ⊑-is-reflexive _ ⟩
                  (f' ∘ ∪-enum' ⟨ A ⟩ ⟨ B ⟩ e e') c ⊑⟨ ψ c ⟩
                  (f♭ A ∨ f♭ B)                     ⊑∎
             where
              c : Fin n + Fin n'
              c = ⌜ Fin+homo n n' ⌝ k
              ψ : (c : Fin n + Fin n')
                → (f' ∘ ∪-enum' ⟨ A ⟩ ⟨ B ⟩ e e') c ⊑ (f♭ A ∨ f♭ B)
              ψ (inl k) = (f' ∘ ∪-enum' ⟨ A ⟩ ⟨ B ⟩ e e') (inl k) ⊑⟨ u₁ ⟩
                          (f ∘ 𝕋-to-carrier ⟨ A ⟩ ∘ e) k          ⊑⟨ u₂ ⟩
                          ∨ⁿ (f ∘ 𝕋-to-carrier ⟨ A ⟩ ∘ e)         ⊑⟨ u₃ ⟩
                          fₛ ⟨ A ⟩ (n , e , σ)                    ⊑⟨ u₄ ⟩
                          f♭ A                                    ⊑⟨ u₅ ⟩
                          f♭ A ∨ f♭ B                             ⊑∎
               where
                u₁ = ⊑-is-reflexive ((f ∘ 𝕋-to-carrier ⟨ A ⟩ ∘ e) k)
                u₂ = ∨ⁿ-is-upperbound (f ∘ 𝕋-to-carrier ⟨ A ⟩ ∘ e) k
                u₃ = ⊑-is-reflexive (∨ⁿ (f ∘ 𝕋-to-carrier ⟨ A ⟩ ∘ e))
                u₄ = ≡-to-⊑ ((f♭-in-terms-of-fₛ ⟨ A ⟩ σ ⟨ A ⟩₂) ⁻¹)
                u₅ = ∨-is-upperbound₁ (f♭ A) (f♭ B)
              ψ (inr k) = (f' ∘ ∪-enum' ⟨ A ⟩ ⟨ B ⟩ e e') (inr k) ⊑⟨ u₁' ⟩
                          (f ∘ 𝕋-to-carrier ⟨ B ⟩ ∘ e') k         ⊑⟨ u₂' ⟩
                          ∨ⁿ (f ∘ 𝕋-to-carrier ⟨ B ⟩ ∘ e')        ⊑⟨ u₃' ⟩
                          fₛ ⟨ B ⟩ (n' , e' , σ')                 ⊑⟨ u₄' ⟩
                          f♭ B                                    ⊑⟨ u₅' ⟩
                          f♭ A ∨ f♭ B                             ⊑∎
               where
                u₁' = ⊑-is-reflexive ((f ∘ 𝕋-to-carrier ⟨ B ⟩ ∘ e') k)
                u₂' = ∨ⁿ-is-upperbound (f ∘ 𝕋-to-carrier ⟨ B ⟩ ∘ e') k
                u₃' = ⊑-is-reflexive (∨ⁿ (f ∘ 𝕋-to-carrier ⟨ B ⟩ ∘ e'))
                u₄' = ≡-to-⊑ ((f♭-in-terms-of-fₛ ⟨ B ⟩ σ' ⟨ B ⟩₂) ⁻¹)
                u₅' = ∨-is-upperbound₂ (f♭ A) (f♭ B)

\end{code}

Finally we prove that f♭ is the unique map with the above properties (i) & (ii).
We do so by using the aforementioned induction principle.

\begin{code}

  module _
          (pe : propext 𝓤)
          (fe : funext 𝓤 (𝓤 ⁺))
         where

   f♭-is-unique : (h : 𝓚 X → L)
                → h ⊥[𝓚] ≡ ⊥
                → ((A B : 𝓚 X) → h (A ∨[𝓚] B) ≡ h A ∨ h B)
                → (h ∘ η X-is-set ∼ f)
                → h ∼ f♭
   f♭-is-unique h p₁ p₂ p₃ = Kuratowski-finite-subset-induction pe fe
                             X X-is-set
                             (λ A → h A ≡ f♭ A)
                             (λ _ → L-is-set)
                             q₁ q₂ q₃
    where
     q₁ : h ⊥[𝓚] ≡ f♭ ⊥[𝓚]
     q₁ = h ⊥[𝓚]  ≡⟨ p₁ ⟩
          ⊥       ≡⟨ f♭-preserves-⊥ ⁻¹ ⟩
          f♭ ⊥[𝓚] ∎
     q₂ : (x : X) → h (η X-is-set x) ≡ f♭ (η X-is-set x)
     q₂ x = h (η X-is-set x)  ≡⟨ p₃ x ⟩
            f x               ≡⟨ (f♭-after-η-is-f x) ⁻¹ ⟩
            f♭ (η X-is-set x) ∎
     q₃ : (A B : 𝓚 X)
        → h A ≡ f♭ A
        → h B ≡ f♭ B
        → h (A ∨[𝓚] B) ≡ f♭ (A ∨[𝓚] B)
     q₃ A B r₁ r₂ = h (A ∨[𝓚] B)  ≡⟨ p₂ A B ⟩
                    h A ∨ h B     ≡⟨ ap₂ _∨_ r₁ r₂ ⟩
                    f♭ A ∨ f♭ B   ≡⟨ (f♭-preserves-∨ A B) ⁻¹ ⟩
                    f♭ (A ∨[𝓚] B) ∎

\end{code}

Assuming some more function extensionality axioms, we can prove "homotopy
uniqueness", i.e. the tuple consisting of f♭ together with the proofs of (i) and
(ii) is unique. This follows easily from the above, because (i) and (ii) are
subsingletons (as L is a set).

\begin{code}

  module _
          (pe : propext 𝓤)
          (fe : funext (𝓤 ⁺) (𝓤 ⁺ ⊔ 𝓥))
         where

   homotopy-uniqueness-of-f♭ :
    ∃! h ꞉ (𝓚 X → L) , (h ⊥[𝓚] ≡ ⊥)
                     × ((A B : 𝓚 X) → h (A ∨[𝓚] B) ≡ h A ∨ h B)
                     × h ∘ η X-is-set ∼ f
   homotopy-uniqueness-of-f♭ =
    (f♭ , f♭-preserves-⊥ , f♭-preserves-∨ , f♭-after-η-is-f) , γ
     where
      γ : (t : (Σ h ꞉ (𝓚 X → L) , (h ⊥[𝓚] ≡ ⊥)
                                × ((A B : 𝓚 X) → h (A ∨[𝓚] B) ≡ h A ∨ h B)
                                × h ∘ η X-is-set ∼ f))
        → (f♭ , f♭-preserves-⊥ , f♭-preserves-∨ , f♭-after-η-is-f) ≡ t
      γ (h , p₁ , p₂ , p₃) = to-subtype-≡ ψ
                             (dfunext (lower-funext (𝓤 ⁺) (𝓤 ⁺) fe)
                               (λ A → (f♭-is-unique
                                         pe
                                         (lower-funext (𝓤 ⁺) 𝓥 fe)
                                         h p₁ p₂ p₃ A) ⁻¹))
       where
        ψ : (k : 𝓚 X → L)
          → is-prop ((k ⊥[𝓚] ≡ ⊥)
                    × ((A B : 𝓚 X) → k (A ∨[𝓚] B) ≡ (k A ∨ k B))
                    × k ∘ η X-is-set ∼ f)
        ψ k = ×-is-prop L-is-set (×-is-prop
                                   (Π-is-prop fe
                                     (λ _ → Π-is-prop (lower-funext (𝓤 ⁺) (𝓤 ⁺) fe)
                                     (λ _ → L-is-set)))
                                   (Π-is-prop (lower-funext (𝓤 ⁺) (𝓤 ⁺) fe)
                                     (λ _ → L-is-set)))

\end{code}

Added 17th March 2021 by Martin Escardo. Alternative definition of 𝓚:

\begin{code}

open import UF-Embeddings

𝓚' : 𝓤 ̇ → 𝓤 ⁺ ̇
𝓚' {𝓤} X = Σ A ꞉ 𝓤 ̇ , (A ↪ X) × is-Kuratowski-finite A

\end{code}

TODO. Show that 𝓚' X is equivalent to 𝓚 X (using UF-Classifiers).
