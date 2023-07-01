Martin Escardo & Tom de Jong, June 2023.

Iterative ordinals.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.Univalence

module Iterative.Ordinals
        (𝓤 : Universe)
        (ua : Univalence)
       where

open import UF.FunExt
open import UF.UA-FunExt

private
 fe : Fun-Ext
 fe = Univalence-gives-Fun-Ext ua

 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import Iterative.Multisets 𝓤
open import Iterative.Sets 𝓤 ua
open import Ordinals.Notions
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.PairFun
open import UF.PropIndexedPiSigma
open import UF.Subsingletons
open import UF.Subsingletons-FunExt


\end{code}

The type of iterative ordinals.

\begin{code}

is-transitive-iset : 𝕍 → 𝓤 ⁺ ̇
is-transitive-iset A = (B C : 𝕍) → B ∈ A → C ∈ B → C ∈ A

being-transitive-iset-is-prop : (A : 𝕍) → is-prop (is-transitive-iset A)
being-transitive-iset-is-prop A = Π₄-is-prop fe (λ B C l m → ∈-is-prop-valued C A)

is-iterative-ordinal : 𝕍 → 𝓤 ⁺ ̇
is-iterative-ordinal A = is-transitive-iset A
                       × ((B : 𝕍) → B ∈ A → is-transitive-iset B)

iterative-ordinals-are-transitive : (A : 𝕍)
                                  → is-iterative-ordinal A
                                  → is-transitive-iset A
iterative-ordinals-are-transitive A = pr₁

members-of-iordinals-are-transitive : (A : 𝕍)
                                    → is-iterative-ordinal A
                                    → (B : 𝕍) → B ∈ A → is-transitive-iset B
members-of-iordinals-are-transitive A = pr₂

being-iordinal-is-prop : (A : 𝕍) → is-prop (is-iterative-ordinal A )
being-iordinal-is-prop A =
 ×-is-prop
  (being-transitive-iset-is-prop A)
  (Π₂-is-prop fe (λ B l → being-transitive-iset-is-prop B))

ordinal-is-hereditary : (A B : 𝕍)
                      → B ∈ A
                      → is-iterative-ordinal A
                      → is-iterative-ordinal B
ordinal-is-hereditary A B B-in-A (A-trans , A-members-trans) = III
 where
  I : is-transitive-iset B
  I = A-members-trans B B-in-A

  II : (C : 𝕍) → C ∈ B → is-transitive-iset C
  II C C-in-B = A-members-trans C (A-trans B C B-in-A C-in-B)

  III : is-iterative-ordinal B
  III = I , II

𝕆 : 𝓤 ⁺ ̇
𝕆 = Σ A ꞉ 𝕍 , is-iterative-ordinal A

underlying-iset : 𝕆 → 𝕍
underlying-iset = pr₁

underlying-iset-is-embedding : is-embedding underlying-iset
underlying-iset-is-embedding = pr₁-is-embedding being-iordinal-is-prop

ordinals-are-iterative : (α : 𝕆) → is-iterative-ordinal (underlying-iset α)
ordinals-are-iterative = pr₂

_<_ : 𝕆 → 𝕆 → 𝓤 ⁺ ̇
α < β = underlying-iset α ∈ underlying-iset β

_≤_ : 𝕆 → 𝕆 → 𝓤 ⁺ ̇
α ≤ β = ∀ γ → γ < α → γ < β

⊆-gives-≤ : (α β : 𝕆)
          → underlying-iset α ⊆ underlying-iset β
          → α ≤ β
⊆-gives-≤ α β u (C , _) = u C

≤-gives-⊆ : (α β : 𝕆)
          → α ≤ β
          → underlying-iset α ⊆ underlying-iset β
≤-gives-⊆ (A , iA) (B , iB) u = I
 where
  I : A ⊆ B
  I C C-in-A = I₃
   where
    iC : is-iterative-ordinal C
    iC = ordinal-is-hereditary A C C-in-A iA

    I₁ : is-transitive-iset C
    I₁ = iterative-ordinals-are-transitive C iC

    I₂ : (B : 𝕍) → B ∈ C → is-transitive-iset B
    I₂ = members-of-iordinals-are-transitive C iC

    I₃ : C ∈ B
    I₃ = u (C , I₁ , I₂) C-in-A

𝕆-root : 𝕆 → 𝓤 ̇
𝕆-root ((sup X _ , _) , _) = X

𝕆-forest : (α : 𝕆) → 𝕆-root α → 𝕆
𝕆-forest (A@(sup X φ , φ-emb , is) , io) x = 𝕍-forest A x , io'
 where
  m : 𝕍-forest A x ∈ A
  m = (x , refl)

  io' : is-iterative-ordinal (𝕍-forest A x)
  io' = ordinal-is-hereditary A (𝕍-forest A x) m io

𝕆-forest-is-embedding : (α : 𝕆) → is-embedding (𝕆-forest α)
𝕆-forest-is-embedding α@(A@(sup _ _ , _) , _) =
 pair-fun-is-embedding-special
  (pr₁ ∘ 𝕆-forest α)
  (pr₂ ∘ 𝕆-forest α)
  (𝕍-forest-is-embedding A)
  being-iordinal-is-prop

is-lower-closed : {X : 𝓤 ̇ } → (X → 𝕆) → 𝓤 ⁺ ̇
is-lower-closed {X} ϕ = (x : X) (β : 𝕆) → β < ϕ x → Σ y ꞉ X , ϕ y ＝ β

being-lower-closed-is-prop : {X : 𝓤 ̇ } (ϕ : X → 𝕆)
                           → is-embedding ϕ
                           → is-prop (is-lower-closed ϕ)
being-lower-closed-is-prop ϕ e = Π₃-is-prop fe (λ x β _ → e β)

𝕆-forest-is-< : (α : 𝕆) (x : 𝕆-root α) → 𝕆-forest α x < α
𝕆-forest-is-< ((sup X φ , φ-emb , is) , io) x = x , refl

-- TODO. (β < α) ＝ (Σ x ꞉ 𝕆-root α , β = 𝕆-forest α x). (Direct.)

<-is-prop-valued : (α β : 𝕆) → is-prop (α < β)
<-is-prop-valued (A , _) (B , _) = ∈-is-prop-valued A B

<-is-transitive : (α β γ : 𝕆) → α < β → β < γ → α < γ
<-is-transitive (A , _) (B , _) (C , C-trans , _) u v = I
 where
  I : A ∈ C
  I = C-trans B A v u

<-is-extensional : is-extensional _<_
<-is-extensional α@(A , iA) β@(B , iB) u v = II
 where
  I : A ＝ B
  I = ∈-is-extensional A B (≤-gives-⊆ α β u) (≤-gives-⊆ β α v)

  II : A , iA ＝ B , iB
  II = to-subtype-＝ (being-iordinal-is-prop) I

<-is-accessible : (α : 𝕆) → is-accessible _<_ α
<-is-accessible ((M , is) , io) = h M is io
 where
  h : (M : 𝕄) (is : is-iterative-set M) (io : is-iterative-ordinal (M , is))
    → is-accessible _<_ ((M , is) , io)
  h M@(sup X φ) (φ-emb , i) io@(io₁ , io₂) = step III
   where
    have-i : (x : X) → is-iterative-set (φ x)
    have-i = i

    have-io : is-iterative-ordinal (sup X φ , φ-emb , i)
    have-io = io

    A : 𝕍
    A = M , φ-emb , i

    α : 𝕆
    α = A , io

    A' : X → 𝕍
    A' x = φ x , i x

    m : (x : X) → A' x ∈ A
    m x = (x , refl)

    I : (x : X) (B : 𝕍) → B ∈ A' x → is-transitive-iset B
    I x B b = I₂
     where
      I₁ : B ∈ A
      I₁ = io₁ (A' x) B (m x) b

      I₂ : is-transitive-iset B
      I₂ = io₂ B I₁

    IH : (x : X) → is-accessible _<_ (A' x , io₂ (A' x) (m x) , I x)
    IH x = h (φ x) (i x) (io₂ (A' x) (m x) , I x)

    II : (M : 𝕄) (j : is-iterative-set M) (k : is-iterative-ordinal (M , j))
       → fiber φ M
       → is-accessible _<_ ((M , j) , k)
    II .(φ x) j k (x , refl) = II₂
     where
      II₁ : (A' x , io₂ (A' x) (m x) , I x) ＝[ 𝕆 ] ((φ x , j) , k)
      II₁ = to-subtype-＝
             being-iordinal-is-prop
             (ap (λ - → φ x , -)
                 (being-iset-is-prop (φ x) (i x) j))

      II₂ : is-accessible _<_ ((φ x , j) , k)
      II₂ = transport (is-accessible _<_) II₁ (IH x)

    III : (β : 𝕆) → β < α → is-accessible _<_ β
    III ((N , is) , io) = II N is io

open import Ordinals.Type

𝓞 : Ordinal (𝓤 ⁺)
𝓞 = 𝕆 ,
    _<_ ,
    <-is-prop-valued ,
    <-is-accessible ,
    <-is-extensional ,
    <-is-transitive

\end{code}

To be continued.

TODO. Define 𝕆-induction following the pattern for 𝕍-induction and
∈-induction. Then replace the proof of accessibility by a shorter one
using 𝕆-induction.
