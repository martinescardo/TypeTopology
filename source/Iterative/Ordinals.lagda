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
 fe : Fun-Ext
 fe = Univalence-gives-Fun-Ext ua

 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import Iterative.Multisets 𝓤
open import Iterative.Sets 𝓤 ua
open import Ordinals.Notions
open import Ordinals.Type
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.PairFun
open import UF.PropIndexedPiSigma
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

An iterative ordinal is a transitive iterative set.

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

\end{code}

The type of iterative ordinals.

\begin{code}

𝕆 : 𝓤 ⁺ ̇
𝕆 = Σ A ꞉ 𝕍 , is-iterative-ordinal A

underlying-iset : 𝕆 → 𝕍
underlying-iset = pr₁

underlying-iset-is-embedding : is-embedding underlying-iset
underlying-iset-is-embedding = pr₁-is-embedding being-iordinal-is-prop

underlying-iset-is-iordinal : (α : 𝕆) → is-iterative-ordinal (underlying-iset α)
underlying-iset-is-iordinal = pr₂

_<_ : 𝕆 → 𝕆 → 𝓤 ⁺ ̇
α < β = underlying-iset α ∈ underlying-iset β

<-is-prop-valued : (α β : 𝕆) → is-prop (α < β)
<-is-prop-valued (A , _) (B , _) = ∈-is-prop-valued A B

<-is-transitive : (α β γ : 𝕆) → α < β → β < γ → α < γ
<-is-transitive (A , _) (B , _) (C , C-trans , _) u v = I
 where
  I : A ∈ C
  I = C-trans B A v u

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
  (pr₁ ∘ 𝕆-forest α)
  (pr₂ ∘ 𝕆-forest α)
  (𝕍-forest-is-embedding A)
  being-iordinal-is-prop

<-is-extensional : is-extensional _<_
<-is-extensional α@(A , iA) β@(B , iB) u v = II
 where
  I : A ＝ B
  I = ∈-is-extensional A B (≤-gives-⊆ α β u) (≤-gives-⊆ β α v)

  II : A , iA ＝ B , iB
  II = to-subtype-＝ (being-iordinal-is-prop) I

<-behaviour : (α β : 𝕆)
            → (α < β)
            ≃ (Σ y ꞉ 𝕆-root β , 𝕆-forest β y ＝ α)
<-behaviour α@(A@(M , _) , _) β@(B@(N@(ssup Y γ) , _) , _) = II
 where
  I : (y : Y) → (γ y ＝ M) ≃ (𝕆-forest β y ＝ α)
  I y = (γ y ＝ M)          ≃⟨ a ⟩
        (𝕍-forest B y ＝ A) ≃⟨ b ⟩
        (𝕆-forest β y ＝ α) ■
         where
          a = embedding-criterion-converse
               pr₁
               (pr₁-is-embedding being-iset-is-prop)
               (𝕍-forest B y)
               A
          b = embedding-criterion-converse
               pr₁
               (pr₁-is-embedding being-iordinal-is-prop)
               (𝕆-forest β y)
               α

  II : (Σ y ꞉ Y , γ y ＝ M) ≃ (Σ y ꞉ Y , 𝕆-forest β y ＝ α)
  II = Σ-cong I

is-lower-closed : {X : 𝓤 ̇ } → (X → 𝕆) → 𝓤 ⁺ ̇
is-lower-closed {X} ϕ = (x : X) (β : 𝕆) → β < ϕ x → Σ y ꞉ X , ϕ y ＝ β

being-lower-closed-is-prop : {X : 𝓤 ̇ } (ϕ : X → 𝕆)
                           → is-embedding ϕ
                           → is-prop (is-lower-closed ϕ)
being-lower-closed-is-prop ϕ e = Π₃-is-prop fe (λ x β _ → e β)

𝕆-forest-is-lower-closed : (α : 𝕆) → is-lower-closed (𝕆-forest α)
𝕆-forest-is-lower-closed α@(A@(M@(ssup X φ) , _) , _)
                         x
                         β@(B@(N , _) , _) l = VII
 where
  have-l : β < 𝕆-forest α x
  have-l = l

  I : 𝕆-forest α x < α
  I = 𝕆-forest-is-< α x

  II : β < α
  II = <-is-transitive β (𝕆-forest α x) α l I

  VII : Σ y ꞉ X , 𝕆-forest α y ＝ β
  VII = ⌜ <-behaviour β α ⌝ II

𝕆-ssup : (X : 𝓤 ̇ ) (ϕ : X → 𝕆) → is-embedding ϕ → is-lower-closed ϕ → 𝕆
𝕆-ssup X ϕ ϕ-emb ϕ-lower = A , io
 where
  φ : X → 𝕍
  φ = underlying-iset ∘ ϕ

  φ-iter : (x : X) → is-iterative-ordinal (φ x)
  φ-iter = underlying-iset-is-iordinal ∘ ϕ

  φ-emb : is-embedding φ
  φ-emb = ∘-is-embedding ϕ-emb (pr₁-is-embedding being-iordinal-is-prop)

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
    q = embeddings-are-lc pr₁ (pr₁-is-embedding being-iordinal-is-prop) p

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
  III B m = iterative-ordinals-are-transitive B (I B m)

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
    s β@((.(underlying-mset (underlying-iset (ϕ x))) , is) , io) (x , refl) = II
     where
      I : P (ϕ x)
      I = u x

      III : ϕ x ＝ β
      III = to-subtype-＝
             being-iordinal-is-prop
              (to-subtype-＝ being-iset-is-prop refl)

      II : P β
      II = transport P III I

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

𝓞 : Ordinal (𝓤 ⁺)
𝓞 = 𝕆 ,
    _<_ ,
    <-is-prop-valued ,
    <-is-accessible ,
    <-is-extensional ,
    <-is-transitive

\end{code}

To be continued.

TODO. 𝓞 is locally small.
