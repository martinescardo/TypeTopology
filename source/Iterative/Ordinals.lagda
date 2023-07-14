Martin Escardo & Tom de Jong, June 2023.

Iterative ordinals.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.Spartan
open import UF.Univalence

module Iterative.Ordinals
        (𝓤 : Universe)
        (ua : Univalence)
       where

open import UF.FunExt
open import UF.UA-FunExt

private
 𝓤⁺ : Universe
 𝓤⁺ = 𝓤 ⁺

 fe : Fun-Ext
 fe = Univalence-gives-Fun-Ext ua

 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import Iterative.Multisets 𝓤
open import Iterative.Sets 𝓤 ua
open import MLTT.W
open import Ordinals.Notions
open import Ordinals.Type
open import Ordinals.WellOrderTransport
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.PairFun
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

An iterative ordinal is a transitive iterative set.

\begin{code}

is-transitive-iset : 𝕍 → 𝓤⁺ ̇
is-transitive-iset A = (B C : 𝕍) → B ∈ A → C ∈ B → C ∈ A

has-transitive-members : 𝕍 → 𝓤⁺ ̇
has-transitive-members A = (B : 𝕍) → B ∈ A → is-transitive-iset B

being-transitive-iset-is-prop : (A : 𝕍) → is-prop (is-transitive-iset A)
being-transitive-iset-is-prop A = Π₄-is-prop fe (λ B C l m → ∈-is-prop-valued C A)

having-transitive-members-is-prop : (A : 𝕍) → is-prop (has-transitive-members A)
having-transitive-members-is-prop A =
 Π₂-is-prop fe (λ B l → being-transitive-iset-is-prop B)

is-iterative-ordinal : 𝕍 → 𝓤⁺ ̇
is-iterative-ordinal A = is-transitive-iset A × has-transitive-members A

iordinals-are-transitive : (A : 𝕍)
                         → is-iterative-ordinal A
                         → is-transitive-iset A
iordinals-are-transitive A = pr₁

members-of-iordinals-are-transitive : (A : 𝕍)
                                    → is-iterative-ordinal A
                                    → has-transitive-members A
members-of-iordinals-are-transitive A = pr₂

being-iordinal-is-prop : (A : 𝕍) → is-prop (is-iterative-ordinal A)
being-iordinal-is-prop A =
 ×-is-prop
  (being-transitive-iset-is-prop A)
  (having-transitive-members-is-prop A)

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

\end{code}

The type of iterative ordinals.

\begin{code}

𝕆 : 𝓤⁺ ̇
𝕆 = Σ A ꞉ 𝕍 , is-iterative-ordinal A

𝕆-is-locally-small : is-locally-small 𝕆
𝕆-is-locally-small = subtype-is-locally-small
                      being-iordinal-is-prop
                      𝕍-is-locally-small

underlying-iset : 𝕆 → 𝕍
underlying-iset = pr₁

underlying-iset-is-embedding : is-embedding underlying-iset
underlying-iset-is-embedding = pr₁-is-embedding being-iordinal-is-prop

underlying-iset-is-iordinal : (α : 𝕆) → is-iterative-ordinal (underlying-iset α)
underlying-iset-is-iordinal = pr₂

_<_ : 𝕆 → 𝕆 → 𝓤⁺ ̇
α < β = underlying-iset α ∈ underlying-iset β

_<⁻_ : 𝕆 → 𝕆 → 𝓤 ̇
α <⁻ β = underlying-iset α ∈⁻ underlying-iset β

<⁻≃-< : (α β : 𝕆) → (α < β) ≃ (α <⁻ β)
<⁻≃-< α@(A@(ssup _ _ , _) , _) β@(B@(ssup _ _ , _) , _) = ∈⁻≃∈ A B

<-is-prop-valued : (α β : 𝕆) → is-prop (α < β)
<-is-prop-valued (A , _) (B , _) = ∈-is-prop-valued A B

<-is-transitive : (α β γ : 𝕆) → α < β → β < γ → α < γ
<-is-transitive (A , _) (B , _) (C , C-trans , _) u v = I
 where
  I : A ∈ C
  I = C-trans B A v u

_≤_ : 𝕆 → 𝕆 → 𝓤⁺ ̇
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
    I₁ = iordinals-are-transitive C iC

    I₂ : (B : 𝕍) → B ∈ C → is-transitive-iset B
    I₂ = members-of-iordinals-are-transitive C iC

    I₃ : C ∈ B
    I₃ = u (C , I₁ , I₂) C-in-A

𝕆-root : 𝕆 → 𝓤 ̇
𝕆-root ((ssup X _ , _) , _) = X

𝕆-forest : (α : 𝕆) → 𝕆-root α → 𝕆
𝕆-forest (A@(ssup X φ , φ-emb , is) , io) x = 𝕍-forest A x , io'
 where
  m : 𝕍-forest A x ∈ A
  m = (x , refl)

  io' : is-iterative-ordinal (𝕍-forest A x)
  io' = ordinal-is-hereditary A (𝕍-forest A x) m io

𝕆-forest-is-< : (α : 𝕆) (x : 𝕆-root α) → 𝕆-forest α x < α
𝕆-forest-is-< ((ssup X φ , φ-emb , is) , io) x = x , refl

𝕆-forest-is-embedding : (α : 𝕆) → is-embedding (𝕆-forest α)
𝕆-forest-is-embedding α@(A@(ssup _ _ , _) , _) =
 pair-fun-is-embedding-special
  (underlying-iset ∘ 𝕆-forest α)
  (underlying-iset-is-iordinal ∘ 𝕆-forest α)
  (𝕍-forest-is-embedding A)
  being-iordinal-is-prop

≤-is-antisymmetric : (α β : 𝕆) → α ≤ β → β ≤ α → α ＝ β
≤-is-antisymmetric α@(A , _) β@(B , _) u v = II
 where
  I : A ＝ B
  I = ∈-is-extensional A B (≤-gives-⊆ α β u) (≤-gives-⊆ β α v)

  II : α ＝ β
  II = to-subtype-＝ (being-iordinal-is-prop) I

<-is-extensional : is-extensional _<_
<-is-extensional = ≤-is-antisymmetric

<-behaviour : (α β : 𝕆)
            → (α < β) ≃ (Σ y ꞉ 𝕆-root β , 𝕆-forest β y ＝ α)
<-behaviour α@(A@(M , _) , _) β@(B@(N@(ssup Y γ) , _) , _) = II
 where
  I : (y : Y) → (γ y ＝ M) ≃ (𝕆-forest β y ＝ α)
  I y = (γ y ＝ M)          ≃⟨ a ⟩
        (𝕍-forest B y ＝ A) ≃⟨ b ⟩
        (𝕆-forest β y ＝ α) ■
         where
          a = embedding-criterion-converse
               underlying-mset
               underlying-mset-is-embedding
               (𝕍-forest B y)
               A
          b = embedding-criterion-converse
               underlying-iset
               underlying-iset-is-embedding
               (𝕆-forest β y)
               α

  II : (Σ y ꞉ Y , γ y ＝ M) ≃ (Σ y ꞉ Y , 𝕆-forest β y ＝ α)
  II = Σ-cong I

is-lower-closed : {X : 𝓤 ̇ } → (X → 𝕆) → 𝓤⁺ ̇
is-lower-closed {X} ϕ = (x : X) (β : 𝕆) → β < ϕ x → Σ y ꞉ X , ϕ y ＝ β

being-lower-closed-is-prop : {X : 𝓤 ̇ } (ϕ : X → 𝕆)
                           → is-embedding ϕ
                           → is-prop (is-lower-closed ϕ)
being-lower-closed-is-prop ϕ e = Π₃-is-prop fe (λ x β _ → e β)

𝕆-forest-is-lower-closed : (α : 𝕆) → is-lower-closed (𝕆-forest α)
𝕆-forest-is-lower-closed α x β l = VII
 where
  have-l : β < 𝕆-forest α x
  have-l = l

  I : 𝕆-forest α x < α
  I = 𝕆-forest-is-< α x

  II : β < α
  II = <-is-transitive β (𝕆-forest α x) α l I

  VII : Σ y ꞉ 𝕆-root α , 𝕆-forest α y ＝ β
  VII = ⌜ <-behaviour β α ⌝ II

𝕆-ssup : (X : 𝓤 ̇ ) (ϕ : X → 𝕆) → is-embedding ϕ → is-lower-closed ϕ → 𝕆
𝕆-ssup X ϕ ϕ-emb ϕ-lower = A , io
 where
  φ : X → 𝕍
  φ = underlying-iset ∘ ϕ

  φ-iter : (x : X) → is-iterative-ordinal (φ x)
  φ-iter = underlying-iset-is-iordinal ∘ ϕ

  φ-emb : is-embedding φ
  φ-emb = ∘-is-embedding ϕ-emb underlying-iset-is-embedding

  A : 𝕍
  A = 𝕍-ssup X φ φ-emb

  A-behaviour : (B : 𝕍) → B ∈ A ≃ (Σ x ꞉ X , φ x ＝ B)
  A-behaviour B = ∈-behaviour B X φ φ-emb

  I : (B : 𝕍) → B ∈ A → is-iterative-ordinal B
  I B B-in-A = transport is-iterative-ordinal (pr₂ I₀) (φ-iter (pr₁ I₀))
   where
    I₀ : Σ x ꞉ X , φ x ＝ B
    I₀ = ⌜ A-behaviour B ⌝ B-in-A

  II :  (B C : 𝕍) → B ∈ A → C ∈ B → C ∈ A
  II B C B-in-A C-in-B = II₅
   where
    x : X
    x = pr₁ (⌜ A-behaviour B ⌝ B-in-A)

    p : φ x ＝ B
    p = pr₂ (⌜ A-behaviour B ⌝ B-in-A)

    β γ : 𝕆
    β = (B , I B B-in-A)
    γ = (C , ordinal-is-hereditary B C C-in-B (I B B-in-A))

    II₀ : γ < β
    II₀ = C-in-B

    q : ϕ x ＝ β
    q = embeddings-are-lc underlying-iset underlying-iset-is-embedding p

    II₁ : γ < ϕ x
    II₁ = transport (γ <_) (q ⁻¹) II₀

    II₂ : Σ y ꞉ X , ϕ y ＝ γ
    II₂ = ϕ-lower x γ II₁

    II₃ : type-of II₂ → Σ y ꞉ X , φ y ＝ C
    II₃ (y , p) = y , ap underlying-iset p

    II₄ : Σ x ꞉ X , underlying-mset (φ x) ＝ underlying-mset C
    II₄ = ⌜ A-behaviour C ⌝⁻¹ (II₃ II₂)

    II₅ : C ∈ A
    II₅ = II₄

  III : (B : 𝕍) → B ∈ A → is-transitive-iset B
  III B m = iordinals-are-transitive B (I B m)

  io : is-iterative-ordinal A
  io = II , III

𝕆-ssup-root : (X : 𝓤 ̇ )
              (ϕ : X → 𝕆) (e : is-embedding ϕ) (l : is-lower-closed ϕ)
            → 𝕆-root (𝕆-ssup X ϕ e l) ＝ X
𝕆-ssup-root X ϕ e l = refl

𝕆-ssup-forest : (X : 𝓤 ̇ )
                (ϕ : X → 𝕆) (e : is-embedding ϕ) (l : is-lower-closed ϕ)
              → 𝕆-forest (𝕆-ssup X ϕ e l) ∼ ϕ
𝕆-ssup-forest X ϕ e l x = to-subtype-＝ being-iordinal-is-prop refl

𝕆-η : (α : 𝕆)
    → 𝕆-ssup (𝕆-root α)
             (𝕆-forest α)
             (𝕆-forest-is-embedding α)
             (𝕆-forest-is-lower-closed α)
    ＝ α
𝕆-η (A@(ssup _ _ , _) , _) =  to-subtype-＝ being-iordinal-is-prop (p _)
 where
  p : (e : is-embedding (𝕍-forest (ssup _ _ , _)))
    → 𝕍-ssup (𝕍-root A) (𝕍-forest A) e ＝ A
  p e = 𝕍-ssup (𝕍-root A) (𝕍-forest A) e                         ＝⟨ I ⟩
        𝕍-ssup (𝕍-root A) (𝕍-forest A) (𝕍-forest-is-embedding A) ＝⟨ 𝕍-η A ⟩
        A                                                        ∎
         where
          I = ap (𝕍-ssup (𝕍-root A) (𝕍-forest A)) (being-embedding-is-prop fe _ _ _)

\end{code}

𝕆-ssup X ϕ e l is the unique ordinal whose predecessors are precisely
the members of the family ϕ.

\begin{code}

𝕆-ssup-behaviour : (X : 𝓤 ̇ )
                   (ϕ : X → 𝕆) (e : is-embedding ϕ) (l : is-lower-closed ϕ)
                   (α : 𝕆)
                 → (α < 𝕆-ssup X ϕ e l) ≃ (Σ x ꞉ X , ϕ x ＝ α)
𝕆-ssup-behaviour X ϕ e l α =
 (α < 𝕆-ssup X ϕ e l)                         ≃⟨ I ⟩
 (Σ x ꞉ X , 𝕆-forest (𝕆-ssup X ϕ e l) x ＝ α) ≃⟨ II ⟩
 (Σ x ꞉ X , ϕ x ＝ α)                         ■
 where
  I  = <-behaviour α (𝕆-ssup X ϕ e l)
  II = Σ-cong (λ x → ＝-cong-l _ _ (𝕆-ssup-forest X ϕ e l x))

\end{code}

All iterative ordinals are generated by the "constructor" 𝕆-ssup, in
the following sense:

\begin{code}

𝕆-induction : (P : 𝕆 → 𝓥 ̇ )
            → ((X : 𝓤 ̇ ) (ϕ : X → 𝕆) (e : is-embedding ϕ) (l : is-lower-closed ϕ)
                  → ((x : X) → P (ϕ x))
                  → P (𝕆-ssup X ϕ e l))
            → (α : 𝕆) → P α
𝕆-induction P f ((M , is) , io) = h M is io
 where
  h : (M : 𝕄) (is : is-iterative-set M) (io : is-iterative-ordinal (M , is))
    → P ((M , is)  , io)
  h M@(ssup X φ) is@(φ-emb , φ-iter) io = II
   where
    α : 𝕆
    α = (M , is) , io

    IH : (x : X) → P (𝕆-forest α x)
    IH x = h (φ x)
             (φ-iter x)
             (ordinal-is-hereditary (M , is) (φ x , φ-iter x) (x , refl) io)

    I : P (𝕆-ssup X
            (𝕆-forest α)
            (𝕆-forest-is-embedding α)
            (𝕆-forest-is-lower-closed α))
    I = f X (𝕆-forest α) (𝕆-forest-is-embedding α) (𝕆-forest-is-lower-closed α) IH

    II : P α
    II = transport P (𝕆-η α) I

\end{code}

The usual induction principle follows directly from the above form of
induction.

\begin{code}

<-induction : (P : 𝕆 → 𝓥 ̇ )
            → ((α : 𝕆) → ((β : 𝕆) → β < α → P β) → P α)
            → (α : 𝕆) → P α
<-induction P g = 𝕆-induction P f
 where
  f : (X : 𝓤 ̇) (ϕ : X → 𝕆) (e : is-embedding ϕ) (l : is-lower-closed ϕ)
    → ((x : X) → P (ϕ x))
    → P (𝕆-ssup X ϕ e l)
  f X ϕ e l u = g α s
   where
    α : 𝕆
    α = 𝕆-ssup X ϕ e l

    s : (β : 𝕆) → β < α → P β
    s β@((.(underlying-mset (underlying-iset (ϕ x))) , is) , io) (x , refl) = III
     where
      I : P (ϕ x)
      I = u x

      II : ϕ x ＝ β
      II = to-subtype-＝
            being-iordinal-is-prop
             (to-subtype-＝ being-iset-is-prop refl)

      III : P β
      III = transport P II I

\end{code}

Which in turn gives the accessibility of the order:

\begin{code}

<-is-accessible : (α : 𝕆) → is-accessible _<_ α
<-is-accessible = <-induction (is-accessible _<_) (λ _ → acc)

\end{code}

Putting the above together we conclude that the type of iterative
ordinals has the structure of an ordinal in the sense of the HoTT
book.

\begin{code}

𝓞 : Ordinal 𝓤⁺
𝓞 = 𝕆 ,
    _<_ ,
    <-is-prop-valued ,
    <-is-accessible ,
    <-is-extensional ,
    <-is-transitive

\end{code}

Every iterative ordinal can be mapped to a HoTT-book ordinal:

\begin{code}

O : 𝕆 → Ordinal 𝓤
O α = α'
 where
  X : 𝓤 ̇
  X = 𝕆-root α

  _≺_ :  X → X → 𝓤⁺ ̇
  x ≺ y = (𝕆-forest α x) < (𝕆-forest α y)

  _≼_ :  X → X → 𝓤⁺ ̇
  x ≼ y = ∀ z → z ≺ x → z ≺ y

  ≼-gives-≤ : (x y : X) → x ≼ y → (𝕆-forest α x) ≤ (𝕆-forest α y)
  ≼-gives-≤ x y l β m = IV
   where
    I : Σ z ꞉ X , 𝕆-forest α z ＝ β
    I = 𝕆-forest-is-lower-closed α x β m

    II : pr₁ I ≺ x
    II = transport⁻¹ (_< 𝕆-forest α x) (pr₂ I) m

    III : pr₁ I ≺ y
    III = l (pr₁ I) II

    IV : β < (𝕆-forest α y)
    IV = transport (_< (𝕆-forest α y)) (pr₂ I) III

  ≤-gives-≼ : (x y : X) → (𝕆-forest α x) ≤ (𝕆-forest α y) → x ≼ y
  ≤-gives-≼ x y l z = l (𝕆-forest α z)

  ≺-is-prop-valued : (x y : X) → is-prop (x ≺ y)
  ≺-is-prop-valued x y = <-is-prop-valued (𝕆-forest α x) (𝕆-forest α y)

  ≺-is-accessible : (x : X) → is-accessible _≺_ x
  ≺-is-accessible x = f x (<-is-accessible (𝕆-forest α x))
   where
    f : (x : X) → is-accessible _<_ (𝕆-forest α x) → is-accessible _≺_ x
    f x (acc u) = acc (λ y l → f y (u (𝕆-forest α y) l))

  ≺-is-extensional : is-extensional _≺_
  ≺-is-extensional x y u v = II
   where
    I : 𝕆-forest α x ＝ 𝕆-forest α y
    I = <-is-extensional _ _ (≼-gives-≤ x y u) (≼-gives-≤ y x v)

    II : x ＝ y
    II = embeddings-are-lc (𝕆-forest α) (𝕆-forest-is-embedding α) I

  ≺-is-transitive : is-transitive _≺_
  ≺-is-transitive x y z = <-is-transitive
                           (𝕆-forest α x)
                           (𝕆-forest α y)
                           (𝕆-forest α z)

  ≺-is-well-order : is-well-order _≺_
  ≺-is-well-order = ≺-is-prop-valued ,
                    ≺-is-accessible ,
                    ≺-is-extensional ,
                    ≺-is-transitive

  _≺⁻_ :  X → X → 𝓤 ̇
  x ≺⁻ y = (𝕆-forest α x) <⁻ (𝕆-forest α y)

  ≺⁻≃-≺ : (x y : X) → (x ≺ y) ≃ (x ≺⁻ y)
  ≺⁻≃-≺ x y = <⁻≃-< (𝕆-forest α x) (𝕆-forest α y)

  ≺⁻-is-well-order : is-well-order _≺⁻_
  ≺⁻-is-well-order = order-transfer-lemma₃.well-order←
                      fe'
                      X
                      _≺⁻_
                      _≺_
                      (λ x y → ≃-sym (≺⁻≃-≺ x y))
                      ≺-is-well-order

  α' : Ordinal 𝓤
  α' = X , _≺⁻_ , ≺⁻-is-well-order

\end{code}

TODO. This map is an equivalence.

TODO. Add lots of comments to this file and the files it depends on.

\begin{code}

open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Underlying
open import UF.Equiv-FunExt

Ord-to-𝕄 : Ordinal 𝓤 → 𝕄
Ord-to-𝕄 = transfinite-recursion-on-OO 𝕄 (λ α → ssup ⟨ α ⟩)

Ord-to-𝕄-behaviour : (α : Ordinal 𝓤)
                   → Ord-to-𝕄 α ＝ ssup ⟨ α ⟩ (λ (x : ⟨ α ⟩) → Ord-to-𝕄 (α ↓ x))
Ord-to-𝕄-behaviour = transfinite-recursion-on-OO-behaviour 𝕄 (λ α → ssup ⟨ α ⟩)

\end{code}


\begin{code}

Ord-to-𝕄-lc : (α β : Ordinal 𝓤) → Ord-to-𝕄 α ＝ Ord-to-𝕄 β → α ＝ β
Ord-to-𝕄-lc = transfinite-induction-on-OO _ f
 where
  f : (α : Ordinal 𝓤)
    → ((a : ⟨ α ⟩) (β : Ordinal 𝓤) → Ord-to-𝕄 (α ↓ a) ＝ Ord-to-𝕄 β → (α ↓ a) ＝ β)
    → (β : Ordinal 𝓤) → Ord-to-𝕄 α ＝ Ord-to-𝕄 β → α ＝ β
  f α IH β p = Extensionality (OO 𝓤) α β VI VI'
   where
    I : ssup ⟨ α ⟩ (λ (a : ⟨ α ⟩) → Ord-to-𝕄 (α ↓ a))
     ＝ ssup ⟨ β ⟩ (λ (b : ⟨ β ⟩) → Ord-to-𝕄 (β ↓ b))
    I = transport₂ (_＝_) (Ord-to-𝕄-behaviour α) (Ord-to-𝕄-behaviour β) p

    II : ⟨ α ⟩ ＝ ⟨ β ⟩
    II = pr₁ (from-𝕄-＝ I)

    III : (a : ⟨ α ⟩) → Ord-to-𝕄 (α ↓ a) ＝ Ord-to-𝕄 (β ↓ Idtofun II a)
    III = happly (pr₂ (from-𝕄-＝ I))

    IV : (a : ⟨ α ⟩) → (α ↓ a) ＝ (β ↓ Idtofun II a)
    IV a = IH a (β ↓ Idtofun II a) (III a)

    V : (a : ⟨ α ⟩) → (α ↓ a) ⊲ β
    V a = Idtofun II a , IV a

    VI : α ≼ β
    VI = to-≼ V

    II' : ⟨ β ⟩ ＝ ⟨ α ⟩
    II' = pr₁ (from-𝕄-＝ (I ⁻¹))

    III' : (b : ⟨ β ⟩) → Ord-to-𝕄 (β ↓ b) ＝ Ord-to-𝕄 (α ↓ Idtofun II' b)
    III' = happly (pr₂ (from-𝕄-＝ (I ⁻¹)))

    IV' : (b : ⟨ β ⟩) → (β ↓ b) ＝ (α ↓ Idtofun II' b)
    IV' b = (IH (Idtofun II' b) (β ↓ b) ((III' b)⁻¹))⁻¹

    V' : (b : ⟨ β ⟩) → (β ↓ b) ⊲ α
    V' b = Idtofun II' b , IV' b

    VI' : β ≼ α
    VI' = to-≼ V'

Ord-to-𝕄-is-iset : (α : Ordinal 𝓤) → is-iterative-set (Ord-to-𝕄 α)
Ord-to-𝕄-is-iset = transfinite-induction-on-OO _ f
 where
  f : (α : Ordinal 𝓤)
    → ((x : ⟨ α ⟩) → is-iterative-set (Ord-to-𝕄 (α ↓ x)))
    → is-iterative-set (Ord-to-𝕄 α)
  f α IH = transport⁻¹ is-iterative-set (Ord-to-𝕄-behaviour α) I
   where
    I : is-iterative-set (ssup ⟨ α ⟩ (λ (x : ⟨ α ⟩) → Ord-to-𝕄 (α ↓ x)))
    I = II , IH
     where
      II : is-embedding (λ x → Ord-to-𝕄 (α ↓ x))
      II M = III
       where
        III : is-prop (Σ a ꞉ ⟨ α ⟩ , Ord-to-𝕄 (α ↓ a) ＝ M)
        III (a , p) (b , q) = VI
         where
          IV : α ↓ a ＝ α ↓ b
          IV = Ord-to-𝕄-lc _ _
                (Ord-to-𝕄 (α ↓ a) ＝⟨ p ⟩
                 M                ＝⟨ q ⁻¹ ⟩
                 Ord-to-𝕄 (α ↓ b) ∎)

          V : a ＝ b
          V = ↓-lc α a b IV

          VI : (a , p) ＝ (b , q)
          VI = to-subtype-＝
                (λ x → isets-are-h-isolated (Ord-to-𝕄 (α ↓ x)) (IH x))
                V

Ord-to-𝕄-is-embedding : is-embedding Ord-to-𝕄
Ord-to-𝕄-is-embedding α' = I
 where
  I : is-prop (Σ α ꞉ Ordinal 𝓤 , Ord-to-𝕄 α ＝ α')
  I (α , p) (β , q) = IV
   where
    II = Ord-to-𝕄 α ＝⟨ p ⟩
         α'         ＝⟨ q ⁻¹ ⟩
         Ord-to-𝕄 β ∎

    III : α ＝ β
    III = Ord-to-𝕄-lc α β II

    IV : (α , p) ＝ (β , q)
    IV = to-subtype-＝
           (λ α → isets-are-h-isolated (Ord-to-𝕄 α) (Ord-to-𝕄-is-iset α))
           III

Ord-to-𝕍 : Ordinal 𝓤 → 𝕍
Ord-to-𝕍 α = Ord-to-𝕄 α , Ord-to-𝕄-is-iset α

Ord-to-𝕍-is-embedding : is-embedding Ord-to-𝕍
Ord-to-𝕍-is-embedding = pair-fun-is-embedding-special
                         Ord-to-𝕄
                         Ord-to-𝕄-is-iset
                         Ord-to-𝕄-is-embedding
                         being-iset-is-prop

Ord-to-𝕍↓-is-embedding : (α : Ordinal 𝓤) → is-embedding (λ x → Ord-to-𝕍 (α ↓ x))
Ord-to-𝕍↓-is-embedding α = ∘-is-embedding
                            (↓-is-embedding α)
                            Ord-to-𝕍-is-embedding

Ord-to-𝕍' : Ordinal 𝓤 → 𝕍
Ord-to-𝕍' α = 𝕍-ssup ⟨ α ⟩
                     (λ (x : ⟨ α ⟩) → Ord-to-𝕍 (α ↓ x))
                     (Ord-to-𝕍↓-is-embedding α)

Ord-to-𝕍-behaviour : (α : Ordinal 𝓤)
                   → Ord-to-𝕍 α ＝ Ord-to-𝕍' α
Ord-to-𝕍-behaviour α = to-subtype-＝ being-iset-is-prop (Ord-to-𝕄-behaviour α)

Ord-to-𝕍'-membership : (A : 𝕍) (α : Ordinal 𝓤)
                     → A ∈ Ord-to-𝕍' α ≃ (Σ x ꞉ ⟨ α ⟩ , Ord-to-𝕍 (α ↓ x) ＝ A)
Ord-to-𝕍'-membership A α = ∈-behaviour
                            A
                            ⟨ α ⟩
                            (λ x → Ord-to-𝕍 (α ↓ x))
                            (Ord-to-𝕍↓-is-embedding α)
\end{code}

We now show that Ord-to-𝕍 α is an iterative ordinal. The proof
doesn't require induction.

\begin{code}

Ord-to-𝕍-is-lower : (α : Ordinal 𝓤) (A : 𝕍) (x : ⟨ α ⟩)
                  → A ∈ Ord-to-𝕍 (α ↓ x)
                  → Σ y ꞉ ⟨ α ⟩ , (y ≺⟨ α ⟩ x) × (A ＝ Ord-to-𝕍 (α ↓ y))
Ord-to-𝕍-is-lower α A x m = IV III
 where
  I : A ∈ Ord-to-𝕍' (α ↓ x)
  I = transport (A ∈_) (Ord-to-𝕍-behaviour (α ↓ x)) m

  II : A ∈ Ord-to-𝕍' (α ↓ x) ≃ (Σ u ꞉ ⟨ α ↓ x ⟩ , Ord-to-𝕍 ((α ↓ x) ↓ u) ＝ A)
  II = Ord-to-𝕍'-membership A (α ↓ x)

  III : Σ u ꞉ ⟨ α ↓ x ⟩ , Ord-to-𝕍 ((α ↓ x) ↓ u) ＝ A
  III = ⌜ II ⌝ I

  IV : type-of III → Σ y ꞉ ⟨ α ⟩ , (y ≺⟨ α ⟩ x) × (A ＝ Ord-to-𝕍 (α ↓ y))
  IV ((y , l) , p) = y , l , q
   where
    q = A                            ＝⟨ p ⁻¹ ⟩
        Ord-to-𝕍 ((α ↓ x) ↓ (y , l)) ＝⟨ ap Ord-to-𝕍 (iterated-↓ α x y l) ⟩
        Ord-to-𝕍 (α ↓ y)             ∎

Ord-to-𝕍-is-transitive-iset : (α : Ordinal 𝓤) → is-transitive-iset (Ord-to-𝕍 α)
Ord-to-𝕍-is-transitive-iset α =
 transport⁻¹ is-transitive-iset (Ord-to-𝕍-behaviour α) I
 where
  g : (B : 𝕍) → B ∈ Ord-to-𝕍' α ≃ (Σ x ꞉ ⟨ α ⟩ , Ord-to-𝕍 (α ↓ x) ＝ B)
  g B = Ord-to-𝕍'-membership B α

  I : is-transitive-iset (Ord-to-𝕍' α)
  I B C B-in-α C-in-B = I₁ I₀
   where
    I₀ : Σ x ꞉ ⟨ α ⟩ , Ord-to-𝕍 (α ↓ x) ＝ B
    I₀ = ⌜ g B ⌝ B-in-α

    I₁ : type-of I₀ → C ∈ Ord-to-𝕍' α
    I₁ (x , p) = I₄ I₃
     where
      I₂ : C ∈ Ord-to-𝕍 (α ↓ x)
      I₂ = transport (C ∈_) (p ⁻¹) C-in-B

      I₃ : Σ y ꞉ ⟨ α ⟩ , (y ≺⟨ α ⟩ x) × (C ＝ Ord-to-𝕍 (α ↓ y))
      I₃ = Ord-to-𝕍-is-lower α C x I₂

      I₄ : type-of I₃ → C ∈ Ord-to-𝕍' α
      I₄ (y , _ , q) = ⌜ g C ⌝⁻¹ (y , (q ⁻¹))

Ord-to-𝕍-has-transitive-members : (α : Ordinal 𝓤)
                                → has-transitive-members (Ord-to-𝕍 α)
Ord-to-𝕍-has-transitive-members α =
 transport⁻¹ has-transitive-members (Ord-to-𝕍-behaviour α) I
 where
  I : has-transitive-members (Ord-to-𝕍' α)
  I B B-in-α = I₁ I₀
   where
    I₀ : Σ x ꞉ ⟨ α ⟩ , Ord-to-𝕍 (α ↓ x) ＝ B
    I₀ = ⌜ Ord-to-𝕍'-membership B α ⌝ B-in-α

    I₁ : type-of I₀ → is-transitive-iset B
    I₁ (x , p) = transport
                  is-transitive-iset
                  p
                  (Ord-to-𝕍-is-transitive-iset (α ↓ x))

Ord-to-𝕍-is-iordinal : (α : Ordinal 𝓤) → is-iterative-ordinal (Ord-to-𝕍 α)
Ord-to-𝕍-is-iordinal α = Ord-to-𝕍-is-transitive-iset α ,
                         Ord-to-𝕍-has-transitive-members α

Ord-to-𝕆 : Ordinal 𝓤 → 𝕆
Ord-to-𝕆 α = Ord-to-𝕍 α , Ord-to-𝕍-is-iordinal α

Ord-to-𝕆-is-embedding : is-embedding Ord-to-𝕆
Ord-to-𝕆-is-embedding = pair-fun-is-embedding-special
                         Ord-to-𝕍
                         Ord-to-𝕍-is-iordinal
                         Ord-to-𝕍-is-embedding
                         being-iordinal-is-prop
\end{code}

To be continued.
