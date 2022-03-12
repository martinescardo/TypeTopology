Tom de Jong, 24 January 2022
(Based on code from FreeJoinSemiLattice.lagda written 18-24 December 2020.)

TODO: Comment

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT

open import UF-PropTrunc

module UF-Powerset-Fin
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import ArithmeticViaEquivalence
open import Fin
open import Fin-Properties
open import List
open import JoinSemiLattices

open import UF-Base
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-FunExt
open import UF-Lower-FunExt
open import UF-ImageAndSurjection
open import UF-Powerset
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

open binary-union-of-subsets pt
open ImageAndSurjection pt
open Kuratowski-finiteness pt

is-Kuratowski-finite-subset : {X : 𝓤 ̇ } (A : 𝓟 X) → 𝓤 ̇
is-Kuratowski-finite-subset A = is-Kuratowski-finite (𝕋 A)

∅-is-Kuratowski-finite-subset : {X : 𝓤 ̇ }
                              → is-Kuratowski-finite-subset ∅
∅-is-Kuratowski-finite-subset {𝓤} {X} = ∣ 0 , e , σ ∣
 where
  e : Fin 0 → 𝕋 {𝓤} {X} ∅
  e = 𝟘-elim
  σ : is-surjection e
  σ (x , x-in-emptyset) = 𝟘-elim x-in-emptyset

module _
        {X : 𝓤 ̇  }
        (X-is-set : is-set X)
       where

 open singleton-subsets X-is-set

 ❴❵-is-Kuratowski-finite-subset : {x : X}
                                → is-Kuratowski-finite-subset ❴ x ❵
 ❴❵-is-Kuratowski-finite-subset {x} = ∣ 1 , e , σ ∣
  where
   e : Fin 1 → 𝕋 ❴ x ❵
   e 𝟎 = x , refl
   σ : is-surjection e
   σ (x , refl) = ∣ inr ⋆ , refl ∣

\end{code}

We proceed by that Kuratowski finite subsets are closed under binary unions.

\begin{code}

module _
        {X : 𝓤 ̇ }
       where

 ∪-enum' : (A B : 𝓟 X) {n m : ℕ}
         → (Fin n → 𝕋 A)
         → (Fin m → 𝕋 B)
         → (Fin n + Fin m) → 𝕋 (A ∪ B)
 ∪-enum' A B e f (inl k) = (𝕋-to-carrier A (e k) ,
                            ∪-is-upperbound₁ A B (𝕋-to-carrier A (e k))
                                                 (𝕋-to-membership A (e k)))
 ∪-enum' A B e f (inr k) = (𝕋-to-carrier B (f k) ,
                            ∪-is-upperbound₂ A B (𝕋-to-carrier B (f k))
                                                 (𝕋-to-membership B (f k)))

 ∪-enum : (A B : 𝓟 X) {n m : ℕ}
        → (Fin n → 𝕋 A)
        → (Fin m → 𝕋 B)
        → Fin (n +' m) → 𝕋 (A ∪ B)
 ∪-enum A B {n} {m} e f = ∪-enum' A B e f ∘ ⌜ Fin+homo n m ⌝

 ∪-enum'-is-surjection : (A B : 𝓟 X) {n m : ℕ}
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

 ∪-enum-is-surjection : (A B : 𝓟 X) {n m : ℕ}
                        (e : Fin n → 𝕋 A)
                        (f : Fin m → 𝕋 B)
                      → is-surjection e
                      → is-surjection f
                      → is-surjection (∪-enum A B e f)
 ∪-enum-is-surjection A B {n} {m} e f σ τ =
  ∘-is-surjection
   (equivs-are-surjections (⌜⌝-is-equiv (Fin+homo n m)))
   (∪-enum'-is-surjection A B e f σ τ)

 ∪-is-Kuratowski-finite-subset : (A B : 𝓟 X)
                               → is-Kuratowski-finite-subset A
                               → is-Kuratowski-finite-subset B
                               → is-Kuratowski-finite-subset (A ∪ B)
 ∪-is-Kuratowski-finite-subset A B kᴬ kᴮ = k
  where
   k : is-Kuratowski-finite-subset (A ∪ B)
   k = ∥∥-functor₂ γ kᴬ kᴮ
    where
     γ : (Σ nᴬ ꞉ ℕ , Fin nᴬ ↠ 𝕋 A)
       → (Σ nᴮ ꞉ ℕ , Fin nᴮ ↠ 𝕋 B)
       → Σ n ꞉ ℕ , Fin n ↠ 𝕋 (A ∪ B)
     γ (nᴬ , eᴬ , eᴬ-is-surj) (nᴮ , eᴮ , eᴮ-is-surj) =
      (nᴬ +' nᴮ , ∪-enum A B eᴬ eᴮ
                , ∪-enum-is-surjection A B eᴬ eᴮ eᴬ-is-surj eᴮ-is-surj)

\end{code}

The Kuratowski finite subsets (ordered by subset inclusion) are a natural
example of a join-semilattice, which we are going to prove now.

(In fact, the Kuratowski finite subsets are the free join-semilattice, see
FreeJoinSemiLattice.lagda.)

\begin{code}

𝓚 : (X : 𝓤 ̇  ) → 𝓤 ⁺ ̇
𝓚 X = Σ A ꞉ 𝓟 X , is-Kuratowski-finite-subset A

module _
        {X : 𝓤 ̇  }
       where

 ⟨_⟩ : 𝓚 X → 𝓟 X
 ⟨_⟩ = pr₁

 ⟨_⟩₂ : (A : 𝓚 X) → is-Kuratowski-finite-subset ⟨ A ⟩
 ⟨_⟩₂ = pr₂

 _⊆[𝓚]_ : 𝓚 X → 𝓚 X → 𝓤 ̇
 A ⊆[𝓚] B = ⟨ A ⟩ ⊆ ⟨ B ⟩

 ⊆[𝓚]-is-reflexive : (A : 𝓚 X) → A ⊆[𝓚] A
 ⊆[𝓚]-is-reflexive A = ⊆-refl ⟨ A ⟩

 ⊆[𝓚]-is-transitive : (A B C : 𝓚 X) → A ⊆[𝓚] B → B ⊆[𝓚] C → A ⊆[𝓚] C
 ⊆[𝓚]-is-transitive A B C = ⊆-trans ⟨ A ⟩ ⟨ B ⟩ ⟨ C ⟩

 module singleton-Kuratowski-finite-subsets
         (X-is-set : is-set X)
       where

  open singleton-subsets X-is-set

  ❴_❵[𝓚] : X → 𝓚 X
  ❴ x ❵[𝓚] = (❴ x ❵ , ❴❵-is-Kuratowski-finite-subset X-is-set)

 ∅[𝓚] : 𝓚 X
 ∅[𝓚] = ∅ , ∅-is-Kuratowski-finite-subset

 ∅[𝓚]-is-least : (A : 𝓚 X) → ∅[𝓚] ⊆[𝓚] A
 ∅[𝓚]-is-least A = ∅-is-least ⟨ A ⟩

 _∪[𝓚]_ : 𝓚 X → 𝓚 X → 𝓚 X
 _∪[𝓚]_ (A , k₁) (B , k₂) = (A ∪ B) , k
  where
   k : is-Kuratowski-finite-subset (A ∪ B)
   k = ∪-is-Kuratowski-finite-subset A B k₁ k₂

 ∪[𝓚]-is-upperbound₁ : (A B : 𝓚 X) → A ⊆[𝓚] (A ∪[𝓚] B)
 ∪[𝓚]-is-upperbound₁ A B = ∪-is-upperbound₁ ⟨ A ⟩ ⟨ B ⟩

 ∪[𝓚]-is-upperbound₂ : (A B : 𝓚 X) → B ⊆[𝓚] (A ∪[𝓚] B)
 ∪[𝓚]-is-upperbound₂ A B = ∪-is-upperbound₂ ⟨ A ⟩ ⟨ B ⟩

 ∪[𝓚]-is-lowerbound-of-upperbounds : (A B C : 𝓚 X)
                                   → A ⊆[𝓚] C → B ⊆[𝓚] C → (A ∪[𝓚] B) ⊆[𝓚] C
 ∪[𝓚]-is-lowerbound-of-upperbounds A B C =
  ∪-is-lowerbound-of-upperbounds ⟨ A ⟩ ⟨ B ⟩ ⟨ C ⟩

 module _
         (fe : funext 𝓤 (𝓤 ⁺))
        where

  ⊆[𝓚]-is-prop-valued : (A B : 𝓚 X) → is-prop (A ⊆[𝓚] B)
  ⊆[𝓚]-is-prop-valued A B = ⊆-is-prop (lower-funext 𝓤 (𝓤 ⁺) fe) ⟨ A ⟩ ⟨ B ⟩

  module _
         (pe : propext 𝓤)
        where

   ⊆[𝓚]-is-antisymmetric : (A B : 𝓚 X) → A ⊆[𝓚] B → B ⊆[𝓚] A → A ≡ B
   ⊆[𝓚]-is-antisymmetric A B s t =
    to-subtype-≡ (λ _ → being-Kuratowski-finite-is-prop)
                 (subset-extensionality pe fe s t)

   𝓚-is-set : is-set (𝓚 X)
   𝓚-is-set = subtypes-of-sets-are-sets ⟨_⟩ s (powersets-are-sets fe pe)
     where
      s : left-cancellable ⟨_⟩
      s e = to-subtype-≡ (λ _ → being-Kuratowski-finite-is-prop) e

\end{code}

We are now ready to prove that the Kuratowski finite subsets are a join-semilattice.

\begin{code}

module _
        (pe : propext 𝓤)
        (fe : funext 𝓤 (𝓤 ⁺))
        (X : 𝓤 ̇  )
       where

 𝓚-join-semilattice : JoinSemiLattice (𝓤 ⁺) 𝓤
 𝓚-join-semilattice = record {
   L                              = 𝓚 X ;
   L-is-set                       = 𝓚-is-set fe pe;
   _⊑_                            = _⊆[𝓚]_;
   ⊑-is-prop-valued               = ⊆[𝓚]-is-prop-valued fe;
   ⊑-is-reflexive                 = ⊆[𝓚]-is-reflexive;
   ⊑-is-transitive                = ⊆[𝓚]-is-transitive;
   ⊑-is-antisymmetric             = ⊆[𝓚]-is-antisymmetric fe pe;
   ⊥                              = ∅[𝓚];
   ⊥-is-least                     = ∅[𝓚]-is-least;
   _∨_                            = _∪[𝓚]_;
   ∨-is-upperbound₁               = ∪[𝓚]-is-upperbound₁;
   ∨-is-upperbound₂               = ∪[𝓚]-is-upperbound₂;
   ∨-is-lowerbound-of-upperbounds = ∪[𝓚]-is-lowerbound-of-upperbounds
  }

\end{code}

Now that we have that the Kuratowski finite subsets are a join-semilattice, we
automatically have binary joins available, which will come in useful when
proving a general induction principle for Kuratowski finite subsets.

\begin{code}

 module _
         (X-is-set : is-set X)
        where

  open JoinSemiLattice 𝓚-join-semilattice
  open singleton-Kuratowski-finite-subsets X-is-set

  Kuratowski-finite-subset-expressed-as-finite-join :
     (A : 𝓚 X)
     {n : ℕ}
     {e : Fin n → 𝕋 ⟨ A ⟩}
     (σ : is-surjection e)
   → A ≡ ∨ⁿ (❴_❵[𝓚] ∘ 𝕋-to-carrier ⟨ A ⟩ ∘ e)
  Kuratowski-finite-subset-expressed-as-finite-join A {n} {e} σ = γ
   where
    ε : Fin n → 𝓚 X
    ε = ❴_❵[𝓚] ∘ 𝕋-to-carrier ⟨ A ⟩ ∘ e
    γ : A ≡ ∨ⁿ ε
    γ = ⊆[𝓚]-is-antisymmetric fe pe A (∨ⁿ ε) u v
     where
      u : A ⊆[𝓚] ∨ⁿ ε
      u x a = ∥∥-rec (∈-is-prop ⟨ ∨ⁿ ε ⟩ x) μ (σ (x , a))
       where
        μ : (Σ k ꞉ Fin n , e k ≡ (x , a))
          → x ∈ ⟨ ∨ⁿ ε ⟩
        μ (k , refl) = ∨ⁿ-is-upperbound ε k x refl
      v : ∨ⁿ ε ⊆[𝓚] A
      v = ∨ⁿ-is-lowerbound-of-upperbounds ε A ν
       where
        ν : (k : Fin n) → ε k ⊆[𝓚] A
        ν k x refl = 𝕋-to-membership ⟨ A ⟩ (e k)

  Kuratowski-finite-subset-induction :
     (Q : 𝓚 X → 𝓣 ̇  )
   → ((A : 𝓚 X) → is-prop (Q A))
   → Q (∅[𝓚])
   → ((x : X) → Q (❴ x ❵[𝓚]))
   → ((A B : 𝓚 X) → Q A → Q B → Q (A ∪[𝓚] B))
   → (A : 𝓚 X) → Q A
  Kuratowski-finite-subset-induction
   Q Q-is-prop-valued Q-empty Q-singletons Q-unions 𝔸@(A , k) =
    ∥∥-rec (Q-is-prop-valued 𝔸) γ k
     where
      γ : (Σ n ꞉ ℕ , Fin n ↠ 𝕋 A) → Q 𝔸
      γ (n , e , e-surj) = transport Q ϕ (ψ n (𝕋-to-carrier A ∘ e))
       where
        ϕ : ∨ⁿ (❴_❵[𝓚] ∘ 𝕋-to-carrier A ∘ e) ≡ 𝔸
        ϕ = (Kuratowski-finite-subset-expressed-as-finite-join 𝔸 e-surj) ⁻¹
        ψ : (m : ℕ) (f : Fin m → X) → Q (∨ⁿ (❴_❵[𝓚] ∘ f))
        ψ zero     f = Q-empty
        ψ (succ m) f = Q-unions
                        (∨ⁿ (❴_❵[𝓚] ∘ f ∘ suc))
                        ((❴_❵[𝓚] ∘ f) 𝟎)
                        IH
                        (Q-singletons (f 𝟎))
         where
          IH : Q (∨ⁿ (❴_❵[𝓚] ∘ f ∘ suc))
          IH = ψ m (f ∘ suc)

\end{code}

We consider the canonical map from lists on X to the powerset of X and prove
that its image is exactly the type of Kuratowski finite powersets of X.

\begin{code}

module _
        {X : 𝓤 ̇  }
        (X-is-set : is-set X)
       where

 open singleton-subsets X-is-set
 open singleton-Kuratowski-finite-subsets X-is-set

 κ : List X → 𝓟 X
 κ [] = ∅
 κ (x ∷ xs) = ❴ x ❵ ∪ κ xs

 κ-of-concatenated-lists-is-union : propext 𝓤
                                  → funext 𝓤 (𝓤 ⁺)
                                  → (l l' : List X)
                                  → κ (l ++ l') ≡ κ l ∪ κ l'
 κ-of-concatenated-lists-is-union pe fe [] l' =
  ∅-left-neutral-for-∪ pe fe (κ l') ⁻¹
 κ-of-concatenated-lists-is-union pe fe (x ∷ l) l' =
  ❴ x ❵ ∪ κ (l ++ l')  ≡⟨ ap (❴ x ❵ ∪_) IH                      ⟩
  ❴ x ❵ ∪ (κ l ∪ κ l') ≡⟨ (∪-assoc pe fe ❴ x ❵ (κ l) (κ l')) ⁻¹ ⟩
  (❴ x ❵ ∪ κ l) ∪ κ l' ∎
   where
    IH : κ (l ++ l') ≡ (κ l ∪ κ l')
    IH = κ-of-concatenated-lists-is-union pe fe l l'

 κ-of-list-is-Kuratowski-finite-subset : (l : List X)
                                       → is-Kuratowski-finite-subset (κ l)
 κ-of-list-is-Kuratowski-finite-subset [] = ∅-is-Kuratowski-finite-subset
 κ-of-list-is-Kuratowski-finite-subset (x ∷ l) =
  ∪-is-Kuratowski-finite-subset ❴ x ❵ (κ l)
   (❴❵-is-Kuratowski-finite-subset X-is-set)
   (κ-of-list-is-Kuratowski-finite-subset l)

 Kuratowski-finite-subset-if-in-image-of-κ : (A : 𝓟 X)
                                           → A ∈image κ
                                           → is-Kuratowski-finite-subset A
 Kuratowski-finite-subset-if-in-image-of-κ A =
  ∥∥-rec being-Kuratowski-finite-is-prop γ
   where
    γ : (Σ l ꞉ List X , κ l ≡ A)
      → is-Kuratowski-finite-subset A
    γ (l , refl) = κ-of-list-is-Kuratowski-finite-subset l

\end{code}

For proving the converse, the aforementioned induction principle for
Kuroratowski finite subsets comes in handy (as suggested by Martín Escardó
during an Agda Club meeting).

\begin{code}

 in-image-of-κ-if-Kuratowski-finite-subset : propext 𝓤
                                           → funext 𝓤 (𝓤 ⁺)
                                           → (A : 𝓟 X)
                                           → is-Kuratowski-finite-subset A
                                           → A ∈image κ
 in-image-of-κ-if-Kuratowski-finite-subset pe fe = goal
  where
   Q : 𝓚 X → 𝓤 ⁺ ̇
   Q A = ⟨ A ⟩ ∈image κ
   Q-is-prop-valued : (A : 𝓚 X) → is-prop (Q A)
   Q-is-prop-valued A = being-in-the-image-is-prop ⟨ A ⟩ κ
   Q-empty : Q ∅[𝓚]
   Q-empty = ∣ [] , refl ∣
   Q-singleton : (x : X) → Q ❴ x ❵[𝓚]
   Q-singleton x = ∣ [ x ] , subset-extensionality pe fe s t ∣
    where
     s : κ [ x ] ⊆ ❴ x ❵
     s y = ∥∥-rec (∈-is-prop ❴ x ❵ y) γ
      where
       γ : (y ∈ ❴ x ❵ + y ∈ κ []) → y ∈ ❴ x ❵
       γ (inl p) = p
       γ (inr q) = 𝟘-elim q
     t : ❴ x ❵ ⊆ κ [ x ]
     t y p = ∣ inl p ∣
   Q-unions : (A B : 𝓚 X) → Q A → Q B → Q (A ∪[𝓚] B)
   Q-unions A B qᴬ qᴮ = ∥∥-functor₂ γ qᴬ qᴮ
    where
     γ : (Σ lᴬ ꞉ List X , κ lᴬ ≡ ⟨ A ⟩)
       → (Σ lᴮ ꞉ List X , κ lᴮ ≡ ⟨ B ⟩)
       → (Σ l  ꞉ List X , κ l  ≡ ⟨ A ∪[𝓚] B ⟩)
     γ (lᴬ , pᴬ) (lᴮ , pᴮ) = ((lᴬ ++ lᴮ) , p)
      where
       p = κ (lᴬ ++ lᴮ)  ≡⟨ κ-of-concatenated-lists-is-union pe fe lᴬ lᴮ ⟩
           κ lᴬ ∪ κ lᴮ   ≡⟨ ap₂ _∪_ pᴬ pᴮ ⟩
           ⟨ A ⟩ ∪ ⟨ B ⟩ ∎
   Q-holds-everywhere : (A : 𝓚 X) → Q A
   Q-holds-everywhere = Kuratowski-finite-subset-induction pe fe X X-is-set
                         Q Q-is-prop-valued
                         Q-empty
                         Q-singleton
                         Q-unions
   goal : (A : 𝓟 X) → is-Kuratowski-finite-subset A → A ∈image κ
   goal A k = Q-holds-everywhere (A , k)

\end{code}

Putting this all together, we obtained the promised equivalence between the
image of κ and the Kuratowski finite subsets of X.

\begin{code}

 image-of-κ-is-the-Kuratowski-finite-powerset : propext 𝓤
                                              → funext 𝓤 (𝓤 ⁺)
                                              → image κ ≃ 𝓚 X
 image-of-κ-is-the-Kuratowski-finite-powerset pe fe = Σ-cong γ
  where
   γ : (A : 𝓟 X) → (A ∈image κ) ≃ is-Kuratowski-finite-subset A
   γ A = logically-equivalent-props-are-equivalent
          (being-in-the-image-is-prop A κ)
          being-Kuratowski-finite-is-prop
          (Kuratowski-finite-subset-if-in-image-of-κ A)
          (in-image-of-κ-if-Kuratowski-finite-subset pe fe A)

\end{code}
