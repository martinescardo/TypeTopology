Martin Escardo & Tom de Jong, June 2023.

Iterative ordinals.

We define the type of iterative ordinals as a subtype of that of
iterative sets, which in turn, is defined a subtype of that of
iterative multisets.

Iterative ordinals are defined in the same way as in the constructive
and non-constructive set theories CZF and ZFC, following Powell [7],
as transitive sets whose members are also transitive.

The main theorem in this module is that the iterative ordinals
coincide with the HoTT-book ordinals. This builds on

[5] Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg and
    Chuangjie Xu. "Set-Theoretic and Type-Theoretic Ordinals
    Coincide". To appear at LICS 2023, June 2023.
    https://arxiv.org/abs/2301.10696

The difference is that instead of using the HoTT-book higher-inductive
definition of the cumulative hierarchy, we use Gylterud's
construction.

[4] H. R. Gylterud, "From multisets to sets in homotopy type theory".
    The Journal of Symbolic Logic, vol. 83, no. 3, pp. 1132–1146,
    2018. https://doi.org/10.1017/jsl.2017.84

See the module Iterative.index for more bibliographic references,
which uses the same numbering as above.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.Univalence

module Iterative.Ordinals
        (ua : Univalence)
        (𝓤 : Universe)
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
open import Iterative.Sets ua 𝓤
open import Ordinals.Equivalence
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type hiding (Ord)
open import Ordinals.Underlying
open import Ordinals.WellOrderTransport
open import UF.Equiv-FunExt
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.PairFun
open import UF.Sets
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import W.Type

\end{code}

An iterative ordinal is a transitive iterative set whose members are
also transitive. This definition is due to Powell [7] in the context
of ZF. Notice that it is not by induction. (von Neumann's inductive
definition is that a set is an ordinal if it is a well-ordered set of
all smaller ordinals.)

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
is-iterative-ordinal A = is-transitive-iset A
                       × has-transitive-members A

being-iordinal-is-prop : (A : 𝕍) → is-prop (is-iterative-ordinal A)
being-iordinal-is-prop A = ×-is-prop
                            (being-transitive-iset-is-prop A)
                            (having-transitive-members-is-prop A)
\end{code}

We name the projections for the sake of clarity:

\begin{code}

iordinals-are-transitive : (A : 𝕍)
                         → is-iterative-ordinal A
                         → is-transitive-iset A
iordinals-are-transitive A = pr₁

members-of-iordinals-are-transitive : (A : 𝕍)
                                    → is-iterative-ordinal A
                                    → has-transitive-members A
members-of-iordinals-are-transitive A = pr₂

\end{code}

Although the definition of iterative ordinal is not by induction, it
does satisfy the following inductive characterization, which we use a
number of times.

\begin{code}

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

The type of iterative ordinals is defined as a subtype of that of
iterative sets.

\begin{code}

𝕆 : 𝓤⁺ ̇
𝕆 = Σ A ꞉ 𝕍 , is-iterative-ordinal A

𝕆-is-locally-small : is-locally-small 𝕆
𝕆-is-locally-small = subtype-is-locally-small
                      being-iordinal-is-prop
                      𝕍-is-locally-small
\end{code}

We again name the projections for the sake of clarity:

\begin{code}

underlying-iset : 𝕆 → 𝕍
underlying-iset = pr₁

underlying-iset-is-iordinal : (α : 𝕆) → is-iterative-ordinal (underlying-iset α)
underlying-iset-is-iordinal = pr₂

\end{code}

Because the notion of iterative ordinal is property, we get that 𝕆 is
a subtype of 𝕍.

\begin{code}

underlying-iset-is-embedding : is-embedding underlying-iset
underlying-iset-is-embedding = pr₁-is-embedding being-iordinal-is-prop

𝕆-is-set : is-set 𝕆
𝕆-is-set = subtypes-of-sets-are-sets
            underlying-iset
            underlying-iset-is-embedding
            𝕍-is-set

\end{code}

We define the less-than relation on ordinals to be the membership
relation, as in material set theory under von Newmann's encoding:

\begin{code}

_<_ : 𝕆 → 𝕆 → 𝓤⁺ ̇
α < β = underlying-iset α ∈ underlying-iset β

\end{code}

As is the case for iterative sets, there is a resized down, equivalent
definition of the less-than relation on ordinals:

\begin{code}

_<⁻_ : 𝕆 → 𝕆 → 𝓤 ̇
α <⁻ β = underlying-iset α ∈⁻ underlying-iset β

<⁻≃-< : (α β : 𝕆) → (α < β) ≃ (α <⁻ β)
<⁻≃-< α β = ∈⁻≃∈ (underlying-iset α) (underlying-iset β)

<-is-prop-valued : (α β : 𝕆) → is-prop (α < β)
<-is-prop-valued α β = ∈-is-prop-valued (underlying-iset α) (underlying-iset β)

\end{code}

We now show that this order is transitive, extensional and accessible,
so that 𝕆 is an ordinal in the sense of the HoTT book. This result is
in de Jong, Kraus, Nordvall Forsberg and Xu [5]. As discussed above,
the difference is that [5] uses the higher-inductive definition of 𝕍.

\begin{code}

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
⊆-gives-≤ α β u γ = u (underlying-iset γ)

≤-gives-⊆ : (α β : 𝕆)
          → α ≤ β
          → underlying-iset α ⊆ underlying-iset β
≤-gives-⊆ α@(A , A-is-iord) β@(B , _) u = I
 where
  I : A ⊆ B
  I C C-in-A = I₃
   where
    C-is-iord : is-iterative-ordinal C
    C-is-iord = ordinal-is-hereditary A C C-in-A A-is-iord

    I₁ : is-transitive-iset C
    I₁ = iordinals-are-transitive C C-is-iord

    I₂ : (B : 𝕍) → B ∈ C → is-transitive-iset B
    I₂ = members-of-iordinals-are-transitive C C-is-iord

    I₃ : C ∈ B
    I₃ = u (C , I₁ , I₂) C-in-A

\end{code}

We now define root and forest "destructors" for the type 𝕆. This will
give rise to an inductive characterization of 𝕆 which doesn't mention
𝕄 or 𝕍, which seems to be new.

\begin{code}

𝕆-root : 𝕆 → 𝓤 ̇
𝕆-root α = 𝕍-root (underlying-iset α)

𝕆-forest : (α : 𝕆) → 𝕆-root α → 𝕆
𝕆-forest α x = 𝕍-forest A x ,
               ordinal-is-hereditary
                A
                (𝕍-forest A x)
                (𝕍-forest-∈ A x)
                (underlying-iset-is-iordinal α)
 where
  A = underlying-iset α

\end{code}

By definition, any (immediate) subtree of α is less than α:

\begin{code}

𝕆-forest-< : (α : 𝕆) (x : 𝕆-root α) → 𝕆-forest α x < α
𝕆-forest-< α = 𝕍-forest-∈ (underlying-iset α)

\end{code}

The 𝕆-forest map is an embedding, which follows from the fact that the
𝕍-forest map is an embedding:

\begin{code}

𝕆-forest-is-embedding : (α : 𝕆) → is-embedding (𝕆-forest α)
𝕆-forest-is-embedding α@(A@(ssup _ _ , _) , _) =
 pair-fun-is-embedding-special
  (underlying-iset ∘ 𝕆-forest α)
  (underlying-iset-is-iordinal ∘ 𝕆-forest α)
  (𝕍-forest-is-embedding A)
  being-iordinal-is-prop

\end{code}

The antisymmetry of the ≤ relation, which amounts to the
extensionality condition:

\begin{code}

≤-is-antisymmetric : (α β : 𝕆) → α ≤ β → β ≤ α → α ＝ β
≤-is-antisymmetric α@(A , _) β@(B , _) u v = II
 where
  I : A ＝ B
  I = ∈-is-extensional A B (≤-gives-⊆ α β u) (≤-gives-⊆ β α v)

  II : α ＝ β
  II = to-subtype-＝ (being-iordinal-is-prop) I

<-is-extensional : is-extensional _<_
<-is-extensional = ≤-is-antisymmetric

\end{code}

A characterization of the < relation:

\begin{code}

<-behaviour : (α β : 𝕆)
            → (α < β) ≃ (Σ y ꞉ 𝕆-root β , 𝕆-forest β y ＝ α)
<-behaviour α@(A@(M , _) , _) β@(B@(N@(ssup Y γ) , _) , _) = II
 where
  I : (y : Y) → (γ y ＝ M) ≃ (𝕆-forest β y ＝ α)
  I y = (γ y ＝ M)          ≃⟨ I₁ ⟩
        (𝕍-forest B y ＝ A) ≃⟨ I₂ ⟩
        (𝕆-forest β y ＝ α) ■
         where
          I₁ = embedding-criterion-converse
                underlying-mset
                underlying-mset-is-embedding
                (𝕍-forest B y)
                A
          I₂ = embedding-criterion-converse
                underlying-iset
                underlying-iset-is-embedding
                (𝕆-forest β y)
                α

  II : (Σ y ꞉ Y , γ y ＝ M) ≃ (Σ y ꞉ Y , 𝕆-forest β y ＝ α)
  II = Σ-cong I

\end{code}

The 𝕆-forest map is lower closed:

\begin{code}

is-lower-closed : {X : 𝓤 ̇ } → (X → 𝕆) → 𝓤⁺ ̇
is-lower-closed {X} ϕ = (β : 𝕆) (x : X) → β < ϕ x → Σ y ꞉ X , ϕ y ＝ β

being-lower-closed-is-prop : {X : 𝓤 ̇ } (ϕ : X → 𝕆)
                           → is-embedding ϕ
                           → is-prop (is-lower-closed ϕ)
being-lower-closed-is-prop ϕ e = Π₃-is-prop fe (λ β _ _ → e β)

𝕆-forest-is-lower-closed : (α : 𝕆) → is-lower-closed (𝕆-forest α)
𝕆-forest-is-lower-closed α β x l = VII
 where
  have-l : β < 𝕆-forest α x
  have-l = l

  I : 𝕆-forest α x < α
  I = 𝕆-forest-< α x

  II : β < α
  II = <-is-transitive β (𝕆-forest α x) α l I

  VII : Σ y ꞉ 𝕆-root α , 𝕆-forest α y ＝ β
  VII = ⌜ <-behaviour β α ⌝ II

\end{code}

The "constructor" of elements of 𝕆:

\begin{code}

𝕆-ssup : (X : 𝓤 ̇ ) (ϕ : X → 𝕆) → is-embedding ϕ → is-lower-closed ϕ → 𝕆
𝕆-ssup X ϕ ϕ-emb ϕ-lower = A , A-is-iord
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
  I B B-in-A = I₁
   where
    I₀ : Σ x ꞉ X , φ x ＝ B
    I₀ = ⌜ A-behaviour B ⌝ B-in-A

    I₁ : is-iterative-ordinal B
    I₁ = transport is-iterative-ordinal (pr₂ I₀) (φ-iter (pr₁ I₀))

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
    II₂ = ϕ-lower γ x II₁

    II₃ : type-of II₂ → Σ y ꞉ X , φ y ＝ C
    II₃ (y , p) = y , ap underlying-iset p

    II₄ : Σ x ꞉ X , underlying-mset (φ x) ＝ underlying-mset C
    II₄ = ⌜ A-behaviour C ⌝⁻¹ (II₃ II₂)

    II₅ : C ∈ A
    II₅ = II₄

  III : (B : 𝕍) → B ∈ A → is-transitive-iset B
  III B m = iordinals-are-transitive B (I B m)

  A-is-iord : is-iterative-ordinal A
  A-is-iord = II , III

\end{code}

It satisfies the expected properties with respect to the destructors:

\begin{code}

𝕆-ssup-root : (X : 𝓤 ̇ )
              (ϕ : X → 𝕆) (e : is-embedding ϕ) (l : is-lower-closed ϕ)
            → 𝕆-root (𝕆-ssup X ϕ e l) ＝ X
𝕆-ssup-root X ϕ e l = refl

𝕆-ssup-forest : (X : 𝓤 ̇ )
                (ϕ : X → 𝕆) (e : is-embedding ϕ) (l : is-lower-closed ϕ)
              → 𝕆-forest (𝕆-ssup X ϕ e l) ∼ ϕ
𝕆-ssup-forest X ϕ e l x = to-subtype-＝ being-iordinal-is-prop refl

𝕆-η' : (α : 𝕆) (e : is-embedding (𝕆-forest α)) (l : is-lower-closed (𝕆-forest α))
     → 𝕆-ssup (𝕆-root α) (𝕆-forest α) e l ＝ α
𝕆-η' (A@(ssup _ _ , _) , _) _ _ = to-subtype-＝ being-iordinal-is-prop (𝕍-η' A _)

𝕆-η : (α : 𝕆)
    → 𝕆-ssup (𝕆-root α)
             (𝕆-forest α)
             (𝕆-forest-is-embedding α)
             (𝕆-forest-is-lower-closed α)
    ＝ α
𝕆-η A =  𝕆-η' A (𝕆-forest-is-embedding A) (𝕆-forest-is-lower-closed A)

\end{code}

A criterion for equality in 𝕆, which is much less general than we can
have, but enough for our purposes for the moment:

\begin{code}

to-𝕆-＝-special : (X : 𝓤 ̇ ) (ϕ ϕ' : X → 𝕆)
                  (e  : is-embedding ϕ ) (l  : is-lower-closed ϕ )
                  (e' : is-embedding ϕ') (l' : is-lower-closed ϕ')
                → ϕ ＝ ϕ'
                → 𝕆-ssup X ϕ e l ＝ 𝕆-ssup X ϕ' e' l'
to-𝕆-＝-special X ϕ ϕ' e l e' l' refl = to-subtype-＝
                                         being-iordinal-is-prop
                                         (to-subtype-＝
                                           being-iset-is-prop
                                           refl)
\end{code}

We now justify our notation "ssup" in comparison with the more
traditional notation "sup" for the constructors.

𝕆-ssup X ϕ e l is the unique iterative ordinal whose predecessors are
precisely the members of the family ϕ, which is known as the strict
supremum (or successor supremum, or strong supremum) of ϕ, and is also
its rank in the sense of set theory.

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

We now discuss various equivalent induction principles on 𝕆.

\begin{code}

𝕆-induction' : (P : 𝕆 → 𝓥 ̇ )
             → ((α : 𝕆) → ((x : 𝕆-root α) → P (𝕆-forest α x)) → P α)
             → (α : 𝕆) → P α
𝕆-induction' P f ((M , M-is-iset) , M-is-iord) = h M M-is-iset M-is-iord
 where
  h : (M : 𝕄)
      (M-is-iset : is-iterative-set M)
      (M-is-iord : is-iterative-ordinal (M , M-is-iset))
    → P ((M , M-is-iset) , M-is-iord)
  h M@(ssup X φ) M-is-iset@(φ-emb , φ-iter) M-is-iord = I
   where
    α : 𝕆
    α = (M , M-is-iset) , M-is-iord

    IH : (x : X) → P (𝕆-forest α x)
    IH x = h (φ x)
             (φ-iter x)
             (ordinal-is-hereditary
               (M , M-is-iset)
               (φ x , φ-iter x)
               (𝕄-forest-⁅ M x)
               M-is-iord)
    I : P α
    I = f α IH

𝕆-recursion' : (P : 𝓥 ̇ )
             → ((α : 𝕆) → (𝕆-root α → P) → P)
             → 𝕆 → P
𝕆-recursion' P = 𝕆-induction' (λ _ → P)

\end{code}

TODO. Do things get nicer if use use induction on 𝕍 rather than 𝕄 in
the above proof?

It would be nice if we could define 𝕆 inductively as follows:

 data 𝕆 : 𝓤⁺ ̇ where
  ssup : (X : 𝓤 ̇ ) (φ : X → 𝕆) → is-embedding φ → is-lower-closed φ → 𝕆

However, this is not a strictly positive definition, for the criterion
of strict positivity adopted by Agda, and so it is not accepted.

Nevertheless, all iterative ordinals *are* generated by the
"constructor" 𝕆-ssup, in the following sense, so that we can view 𝕆 as
really inductively defined by the above data declaration, which seems
to be a new result. This is close to von Neumann's definition, with
the difference that we don't require φ to be well-ordered - this
follows automatically.

\begin{code}

𝕆-induction : (P : 𝕆 → 𝓥 ̇ )
            → ((X : 𝓤 ̇ ) (ϕ : X → 𝕆) (e : is-embedding ϕ) (l : is-lower-closed ϕ)
                  → ((x : X) → P (ϕ x))
                  → P (𝕆-ssup X ϕ e l))
            → (α : 𝕆) → P α
𝕆-induction P f = 𝕆-induction' P f'
 where
  f' : (α : 𝕆) → ((x : 𝕆-root α) → P (𝕆-forest α x)) → P α
  f' α IH = transport P (𝕆-η α) I
   where
    I : P (𝕆-ssup (𝕆-root α)
                  (𝕆-forest α)
                  (𝕆-forest-is-embedding α)
                  (𝕆-forest-is-lower-closed α))
    I = f (𝕆-root α)
          (𝕆-forest α)
          (𝕆-forest-is-embedding α)
          (𝕆-forest-is-lower-closed α)
          IH

𝕆-recursion : (P : 𝓥 ̇ )
            → ((X : 𝓤 ̇ ) (ϕ : X → 𝕆)
                  → is-embedding ϕ
                  → is-lower-closed ϕ
                  → (X → P)
                  → P)
            → 𝕆 → P
𝕆-recursion P f = 𝕆-induction (λ _ → P) (λ X ϕ e l s → f X ϕ e l s)

𝕆-iteration : (P : 𝓥 ̇ )
            → ((X : 𝓤 ̇ ) → (X → P) → P)
            → 𝕆 → P
𝕆-iteration P f = 𝕆-induction (λ _ → P) (λ X ϕ e l → f X)

\end{code}

The usual induction principle for ordinals follows directly from the
above form of induction.

\begin{code}

<-induction : (P : 𝕆 → 𝓥 ̇ )
            → ((α : 𝕆) → ((β : 𝕆) → β < α → P β) → P α)
            → (α : 𝕆) → P α
<-induction P IH = 𝕆-induction P f
 where
  f : (X : 𝓤 ̇) (ϕ : X → 𝕆) (e : is-embedding ϕ) (l : is-lower-closed ϕ)
    → ((x : X) → P (ϕ x))
    → P (𝕆-ssup X ϕ e l)
  f X ϕ e l u = IH α s
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

Which in turn gives the accessibility of the order directly:

\begin{code}

<-is-accessible : (α : 𝕆) → is-accessible _<_ α
<-is-accessible = <-induction (is-accessible _<_) (λ _ → acc)

\end{code}

Putting the above together we conclude that the type of iterative
ordinals has the structure of an ordinal in the sense of the HoTT
book, which, as mentioned above, had already been proved in [5].

\begin{code}

𝓞 : Ordinal 𝓤⁺
𝓞 = 𝕆 ,
    _<_ ,
    <-is-prop-valued ,
    <-is-accessible ,
    <-is-extensional ,
    <-is-transitive

\end{code}

We now want to show that 𝓞 is equivalent to the "ordinal of ordinals"
in the sense of the HoTT book.

Every iterative ordinal can be mapped to a HoTT-book ordinal, by
taking the root of the iterative ordinal to be the underlying set of
the HoTT-book ordinal. This is similar to [5, Proposition 43], with
the difference that we don't need to quotient because the forest is an
embedding in our conception of iterative ordinals. There is also a
minor improvement in avoiding propositional truncations in the
definition of the order on the root of α, which, together with the
avoidance of quotients, makes the proof more direct.

\begin{code}

Ord : 𝓤⁺ ̇
Ord = Ordinal 𝓤

𝕆-to-Ord : 𝕆 → Ord
𝕆-to-Ord α = α'
 where
  X : 𝓤 ̇
  X = 𝕆-root α

  _≺_ :  X → X → 𝓤⁺ ̇
  x ≺ y = 𝕆-forest α x < 𝕆-forest α y

  _⊑_ :  X → X → 𝓤⁺ ̇
  x ⊑ y = ∀ z → z ≺ x → z ≺ y

  ⊑-gives-≤ : (x y : X) → x ⊑ y → 𝕆-forest α x ≤ 𝕆-forest α y
  ⊑-gives-≤ x y l β m = IV
   where
    I : Σ z ꞉ X , 𝕆-forest α z ＝ β
    I = 𝕆-forest-is-lower-closed α β x m

    II : pr₁ I ≺ x
    II = transport⁻¹ (_< 𝕆-forest α x) (pr₂ I) m

    III : pr₁ I ≺ y
    III = l (pr₁ I) II

    IV : β < (𝕆-forest α y)
    IV = transport (_< (𝕆-forest α y)) (pr₂ I) III

  ≤-gives-⊑ : (x y : X) → 𝕆-forest α x ≤ 𝕆-forest α y → x ⊑ y
  ≤-gives-⊑ x y l z = l (𝕆-forest α z)

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
    I = <-is-extensional _ _ (⊑-gives-≤ x y u) (⊑-gives-≤ y x v)

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
  α' : Ord
  α' = X , _≺⁻_ , ≺⁻-is-well-order

\end{code}

The order of 𝕆-to-Ord α is characterized as follows in terms of the
order of 𝕆, by definition:

\begin{code}

𝕆-to-Ord-order : (α : 𝕆) (x y : ⟨ 𝕆-to-Ord α ⟩)
               → (𝕆-forest α x < 𝕆-forest α y) ≃ (x ≺⟨ 𝕆-to-Ord α ⟩ y)
𝕆-to-Ord-order α x y = <⁻≃-< (𝕆-forest α x) (𝕆-forest α y)

\end{code}

We now define the map in the other direction, essentially in the same
way as in [5], in several steps, but we start mapping into 𝕄 rather
than into 𝕍 directly. In any case, 𝕄 doesn't occur in the set-up of [5].

\begin{code}

Ord-to-𝕄 : Ord → 𝕄
Ord-to-𝕄 = transfinite-recursion-on-OO 𝕄 (λ α → ssup ⟨ α ⟩)

\end{code}

This is characterized by the following recursive definition,
where α ↓ x denotes the sub-ordinal of α consisting of the
elements below x.

\begin{code}

Ord-to-𝕄-behaviour : (α : Ord)
                   → Ord-to-𝕄 α ＝ ssup ⟨ α ⟩ (λ (x : ⟨ α ⟩) → Ord-to-𝕄 (α ↓ x))
Ord-to-𝕄-behaviour = transfinite-recursion-on-OO-behaviour 𝕄 (λ α → ssup ⟨ α ⟩)

\end{code}

This map is left cancellable and we will later conclude from this fact
that it is actually an embedding.

\begin{code}

Ord-to-𝕄-is-lc : left-cancellable Ord-to-𝕄
Ord-to-𝕄-is-lc {α} {β} = transfinite-induction-on-OO _ f α β
 where
  f : (α : Ord)
    → ((a : ⟨ α ⟩) (β : Ord) → Ord-to-𝕄 (α ↓ a) ＝ Ord-to-𝕄 β → (α ↓ a) ＝ β)
    → (β : Ord) → Ord-to-𝕄 α ＝ Ord-to-𝕄 β → α ＝ β
  f α IH β p = VII
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

    VII : α ＝ β
    VII = Extensionality (OO 𝓤) α β VI VI'

\end{code}

Using this we can show that the elements in the image of Ord-to-𝕄 are
iterative sets, by induction on the ordinal of ordinals in the sense
of the HoTT book.

\begin{code}

Ord-to-𝕄-is-iset : (α : Ord) → is-iterative-set (Ord-to-𝕄 α)
Ord-to-𝕄-is-iset = transfinite-induction-on-OO _ f
 where
  f : (α : Ord)
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
          IV = Ord-to-𝕄-is-lc
                (Ord-to-𝕄 (α ↓ a) ＝⟨ p ⟩
                 M                ＝⟨ q ⁻¹ ⟩
                 Ord-to-𝕄 (α ↓ b) ∎)

          V : a ＝ b
          V = ↓-lc α a b IV

          VI : (a , p) ＝ (b , q)
          VI = to-subtype-＝
                (λ x → isets-are-h-isolated (Ord-to-𝕄 (α ↓ x)) (IH x))
                V
\end{code}

So we get a map Ord → 𝕍 from the above map Ord → 𝕄.

\begin{code}

Ord-to-𝕍 : Ord → 𝕍
Ord-to-𝕍 α = Ord-to-𝕄 α , Ord-to-𝕄-is-iset α

\end{code}

The next step is to get a map Ord → 𝕆 from this map Ord-to-𝕍.

We have the definitionally commutative triangle

                Ord-to-𝕍
             Ord ------> 𝕍
               \       /
                \     /
       Ord-to-𝕄 \    / underlying-mset
                  \ /
                   v
                   𝕄

We previously showed that Ord-to-𝕄 is left cancellable. Hence Ord-to-𝕍
is left cancellable as well. But 𝕍 is a 0-type, so Ord-to-𝕍 is
actually an embedding. Finally, the map underlying-mset is an
embedding, as 𝕍 is a subtype of 𝕄, so Ord-to-𝕄 is a composition of
embeddings, and therefore an embedding itself.

\begin{code}

private
 commutative-triangle : Ord-to-𝕄 ＝ underlying-mset ∘ Ord-to-𝕍
 commutative-triangle = refl

Ord-to-𝕍-is-embedding : is-embedding Ord-to-𝕍
Ord-to-𝕍-is-embedding = lc-maps-into-sets-are-embeddings
                         Ord-to-𝕍
                         (factor-is-lc
                           Ord-to-𝕍
                           underlying-mset
                           Ord-to-𝕄-is-lc)
                         𝕍-is-set

Ord-to-𝕄-is-embedding : is-embedding Ord-to-𝕄
Ord-to-𝕄-is-embedding = ∘-is-embedding
                          Ord-to-𝕍-is-embedding
                          underlying-mset-is-embedding

Ord-to-𝕍↓-is-embedding : (α : Ord) → is-embedding (λ x → Ord-to-𝕍 (α ↓ x))
Ord-to-𝕍↓-is-embedding α = ∘-is-embedding
                            (↓-is-embedding α)
                            Ord-to-𝕍-is-embedding
\end{code}

The fact that Ord-to-𝕄 is an embedding seems to be new, and it is
interesting because 𝕄 is not a 0-type.

The following gives a recursive characterization of Ord-to-𝕍:

\begin{code}

Ord-to-𝕍-behaviour : (α : Ord)
                   → Ord-to-𝕍 α ＝ 𝕍-ssup ⟨ α ⟩
                                    (λ (x : ⟨ α ⟩) → Ord-to-𝕍 (α ↓ x))
                                    (Ord-to-𝕍↓-is-embedding α)
Ord-to-𝕍-behaviour α = to-subtype-＝ being-iset-is-prop (Ord-to-𝕄-behaviour α)

\end{code}

It is convenient to name the "body" of the definition for the sake of
brevity.

\begin{code}

Ord-to-𝕍-body : Ord → 𝕍
Ord-to-𝕍-body α = 𝕍-ssup ⟨ α ⟩
                   (λ (x : ⟨ α ⟩) → Ord-to-𝕍 (α ↓ x))
                   (Ord-to-𝕍↓-is-embedding α)
\end{code}

We now show that Ord-to-𝕍 α is an iterative ordinal. We begin with a
useful observation.

\begin{code}

Ord-to-𝕍-membership : (A : 𝕍) (α : Ord)
                    → A ∈ Ord-to-𝕍-body α ≃ (Σ x ꞉ ⟨ α ⟩ , Ord-to-𝕍 (α ↓ x) ＝ A)
Ord-to-𝕍-membership A α = ∈-behaviour
                           A
                           ⟨ α ⟩
                           (λ x → Ord-to-𝕍 (α ↓ x))
                           (Ord-to-𝕍↓-is-embedding α)
\end{code}

The map Ord-to-𝕍 (α ↓ -) is lower closed in the following sense:

\begin{code}

Ord-to-𝕍↓-is-lower : (α : Ord) (A : 𝕍) (x : ⟨ α ⟩)
                   → A ∈ Ord-to-𝕍 (α ↓ x)
                   → Σ y ꞉ ⟨ α ⟩ , (y ≺⟨ α ⟩ x) × (A ＝ Ord-to-𝕍 (α ↓ y))
Ord-to-𝕍↓-is-lower α A x m = IV III
 where
  I : A ∈ Ord-to-𝕍-body (α ↓ x)
  I = transport (A ∈_) (Ord-to-𝕍-behaviour (α ↓ x)) m

  II : A ∈ Ord-to-𝕍-body (α ↓ x) ≃ (Σ u ꞉ ⟨ α ↓ x ⟩ , Ord-to-𝕍 ((α ↓ x) ↓ u) ＝ A)
  II = Ord-to-𝕍-membership A (α ↓ x)

  III : Σ u ꞉ ⟨ α ↓ x ⟩ , Ord-to-𝕍 ((α ↓ x) ↓ u) ＝ A
  III = ⌜ II ⌝ I

  IV : type-of III → Σ y ꞉ ⟨ α ⟩ , (y ≺⟨ α ⟩ x) × (A ＝ Ord-to-𝕍 (α ↓ y))
  IV ((y , l) , p) = y , (l , q)
   where
    q = A                            ＝⟨ p ⁻¹ ⟩
        Ord-to-𝕍 ((α ↓ x) ↓ (y , l)) ＝⟨ ap Ord-to-𝕍 (iterated-↓ α x y l) ⟩
        Ord-to-𝕍 (α ↓ y)             ∎

\end{code}

After the above preparation we are ready to show the desired
result. Notice that it doesn't require induction.

\begin{code}

Ord-to-𝕍-is-transitive-iset : (α : Ord) → is-transitive-iset (Ord-to-𝕍 α)
Ord-to-𝕍-is-transitive-iset α =
 transport⁻¹ is-transitive-iset (Ord-to-𝕍-behaviour α) I
 where
  g : (B : 𝕍) → B ∈ Ord-to-𝕍-body α ≃ (Σ x ꞉ ⟨ α ⟩ , Ord-to-𝕍 (α ↓ x) ＝ B)
  g B = Ord-to-𝕍-membership B α

  I : is-transitive-iset (Ord-to-𝕍-body α)
  I B C B-in-α C-in-B = I₁ I₀
   where
    I₀ : Σ x ꞉ ⟨ α ⟩ , Ord-to-𝕍 (α ↓ x) ＝ B
    I₀ = ⌜ g B ⌝ B-in-α

    I₁ : type-of I₀ → C ∈ Ord-to-𝕍-body α
    I₁ (x , p) = I₄ I₃
     where
      I₂ : C ∈ Ord-to-𝕍 (α ↓ x)
      I₂ = transport (C ∈_) (p ⁻¹) C-in-B

      I₃ : Σ y ꞉ ⟨ α ⟩ , (y ≺⟨ α ⟩ x) × (C ＝ Ord-to-𝕍 (α ↓ y))
      I₃ = Ord-to-𝕍↓-is-lower α C x I₂

      I₄ : type-of I₃ → C ∈ Ord-to-𝕍-body α
      I₄ (y , _ , q) = ⌜ g C ⌝⁻¹ (y , (q ⁻¹))

Ord-to-𝕍-has-transitive-members : (α : Ord)
                                → has-transitive-members (Ord-to-𝕍 α)
Ord-to-𝕍-has-transitive-members α =
 transport⁻¹ has-transitive-members (Ord-to-𝕍-behaviour α) I
 where
  I : has-transitive-members (Ord-to-𝕍-body α)
  I B B-in-α = I₁ I₀
   where
    I₀ : Σ x ꞉ ⟨ α ⟩ , Ord-to-𝕍 (α ↓ x) ＝ B
    I₀ = ⌜ Ord-to-𝕍-membership B α ⌝ B-in-α

    I₁ : type-of I₀ → is-transitive-iset B
    I₁ (x , p) = transport
                  is-transitive-iset
                  p
                  (Ord-to-𝕍-is-transitive-iset (α ↓ x))

Ord-to-𝕍-is-iordinal : (α : Ord) → is-iterative-ordinal (Ord-to-𝕍 α)
Ord-to-𝕍-is-iordinal α = Ord-to-𝕍-is-transitive-iset α ,
                         Ord-to-𝕍-has-transitive-members α
\end{code}

From this we get the desired map Ord → 𝕆, which is easily seen to be
an embedding from the above development:

\begin{code}

Ord-to-𝕆 : Ord → 𝕆
Ord-to-𝕆 α = Ord-to-𝕍 α , Ord-to-𝕍-is-iordinal α

Ord-to-𝕆-is-embedding : is-embedding Ord-to-𝕆
Ord-to-𝕆-is-embedding = pair-fun-is-embedding-special
                         Ord-to-𝕍
                         Ord-to-𝕍-is-iordinal
                         Ord-to-𝕍-is-embedding
                         being-iordinal-is-prop
\end{code}

In order to show that this map is an equivalence, with two sided
inverse 𝕆-to-Ord, we need some preparation:

\begin{code}

Ord-to-𝕆↓-is-embedding : (α : Ord)
                       → is-embedding (λ x → Ord-to-𝕆 (α ↓ x))
Ord-to-𝕆↓-is-embedding α = ∘-is-embedding
                            (↓-is-embedding α)
                            Ord-to-𝕆-is-embedding

Ord-to-𝕆↓-is-lower-closed : (α : Ord)
                          → is-lower-closed (λ x → Ord-to-𝕆 (α ↓ x))
Ord-to-𝕆↓-is-lower-closed α β x l = II I
 where
  B : 𝕍
  B = underlying-iset β

  I : Σ y ꞉ ⟨ α ⟩ , (y ≺⟨ α ⟩ x) × (B ＝ Ord-to-𝕍 (α ↓ y))
  I = Ord-to-𝕍↓-is-lower α B x l

  II : type-of I → Σ y ꞉ ⟨ α ⟩ , Ord-to-𝕆 (α ↓ y) ＝ β
  II (y , _ , p) = y , to-subtype-＝ being-iordinal-is-prop (p ⁻¹)

\end{code}

TODO. Instead show that the composition of two lower closed maps is
lower closed, and use this to give a direct proof of the above.

We use this to obtain the following recursive characterization of the
map Ord-to-𝕆.

\begin{code}

Ord-to-𝕆-behaviour : (α : Ord)
                   → Ord-to-𝕆 α ＝ 𝕆-ssup
                                    ⟨ α ⟩
                                    ((λ (x : ⟨ α ⟩) → Ord-to-𝕆 (α ↓ x)))
                                    (Ord-to-𝕆↓-is-embedding α)
                                    (Ord-to-𝕆↓-is-lower-closed α)
Ord-to-𝕆-behaviour α = to-subtype-＝
                        being-iordinal-is-prop
                         (to-subtype-＝
                           being-iset-is-prop
                           (Ord-to-𝕄-behaviour α))
\end{code}

We now establish the following equation by nested induction, first on
𝕆 and then on the ordinal 𝕆-to-Ord α, which seems to be a new
observation.

\begin{code}

𝕆-to-Ord-equation : (α : 𝕆) (x : 𝕆-root α)
                  → (𝕆-to-Ord α) ↓ x ＝ 𝕆-to-Ord (𝕆-forest α x)
𝕆-to-Ord-equation = 𝕆-induction' _ f
 where
  f : (α : 𝕆)
    → ((x : 𝕆-root α) (y : 𝕆-root (𝕆-forest α x))
          →  𝕆-to-Ord (𝕆-forest α x) ↓ y
          ＝ 𝕆-to-Ord (𝕆-forest (𝕆-forest α x) y))
    → (x : 𝕆-root α) → (𝕆-to-Ord α ↓ x) ＝ 𝕆-to-Ord (𝕆-forest α x)
  f α IH-f = Transfinite-induction (𝕆-to-Ord α) _ g
   where
    g : (x : 𝕆-root α)
      → ((y : 𝕆-root α) → y ≺⟨ 𝕆-to-Ord α ⟩ x
            → (𝕆-to-Ord α ↓ y) ＝ 𝕆-to-Ord (𝕆-forest α y))
      → (𝕆-to-Ord α ↓ x) ＝ 𝕆-to-Ord (𝕆-forest α x)
    g x IH-g = ⊲-is-extensional _ _ (to-≼ I) (to-≼ II)
     where
      I : (y : ⟨ 𝕆-to-Ord α ↓ x ⟩)
        → ((𝕆-to-Ord α ↓ x) ↓ y) ⊲ 𝕆-to-Ord (𝕆-forest α x)
      I 𝕪@(y , l) = (y' , eq)
       where
        I₁ : Σ y' ꞉ 𝕆-root (𝕆-forest α x)
                  , 𝕆-forest (𝕆-forest α x) y' ＝ 𝕆-forest α y
        I₁ = ⌜ <-behaviour (𝕆-forest α y) (𝕆-forest α x) ⌝
              (⌜ 𝕆-to-Ord-order α y x ⌝⁻¹ l)
        y'  = pr₁ I₁
        eq' = pr₂ I₁

        eq = (𝕆-to-Ord α ↓ x) ↓ 𝕪                  ＝⟨ ⦅1⦆ ⟩
             𝕆-to-Ord α ↓ y                        ＝⟨ ⦅2⦆ ⟩
             𝕆-to-Ord (𝕆-forest α y)               ＝⟨ ⦅3⦆ ⟩
             𝕆-to-Ord (𝕆-forest (𝕆-forest α x) y') ＝⟨ ⦅4⦆ ⟩
             𝕆-to-Ord (𝕆-forest α x) ↓ y'          ∎
         where
          ⦅1⦆ = iterated-↓ (𝕆-to-Ord α) x y l
          ⦅2⦆ = IH-g y l
          ⦅3⦆ = ap 𝕆-to-Ord (eq' ⁻¹)
          ⦅4⦆ = (IH-f x y')⁻¹

      II : (y : ⟨ 𝕆-to-Ord (𝕆-forest α x) ⟩)
         → (𝕆-to-Ord (𝕆-forest α x) ↓ y) ⊲ (𝕆-to-Ord α ↓ x)
      II y = (𝕪 , (eq ⁻¹))
       where
        note : 𝕆-root (𝕆-forest α x) ＝ ⟨ 𝕆-to-Ord (𝕆-forest α x) ⟩
        note = refl

        I₂ : Σ y' ꞉ 𝕆-root α
                  , 𝕆-forest α y' ＝ 𝕆-forest (𝕆-forest α x) y
        I₂ = 𝕆-forest-is-lower-closed
              α
              (𝕆-forest (𝕆-forest α x) y)
              x
              (𝕆-forest-< (𝕆-forest α x) y)
        y'  = pr₁ I₂
        eq' = pr₂ I₂

        l : 𝕆-forest α y' < 𝕆-forest α x
        l = ⌜ <-behaviour (𝕆-forest α y') (𝕆-forest α x) ⌝⁻¹
             (y , (eq' ⁻¹))
        l' : y' ≺⟨ 𝕆-to-Ord α ⟩ x
        l' = ⌜ 𝕆-to-Ord-order α y' x ⌝ l
        𝕪 = (y' , l')

        eq = (𝕆-to-Ord α ↓ x) ↓ 𝕪                 ＝⟨ ⦅1⦆ ⟩
             𝕆-to-Ord α ↓ y'                      ＝⟨ ⦅2⦆ ⟩
             𝕆-to-Ord (𝕆-forest α y')             ＝⟨ ⦅3⦆ ⟩
             𝕆-to-Ord (𝕆-forest (𝕆-forest α x) y) ＝⟨ ⦅4⦆ ⟩
             𝕆-to-Ord (𝕆-forest α x) ↓ y          ∎
         where
          ⦅1⦆ = iterated-↓ (𝕆-to-Ord α) x y' l'
          ⦅2⦆ = IH-g y' l'
          ⦅3⦆ = ap 𝕆-to-Ord eq'
          ⦅4⦆ = (IH-f x y)⁻¹

\end{code}

From this equation and the previous results, we easily deduce that the
map Ord-to-𝕆 is an equivalence, by induction on 𝕆.

\begin{code}

Ord-to-𝕆-is-equiv : is-equiv Ord-to-𝕆
Ord-to-𝕆-is-equiv = embeddings-with-sections-are-equivs
                     Ord-to-𝕆
                     Ord-to-𝕆-is-embedding
                     (𝕆-to-Ord , η)
 where
  f : (α : 𝕆)
    → ((x : 𝕆-root α) → Ord-to-𝕆 (𝕆-to-Ord (𝕆-forest α x)) ＝ 𝕆-forest α x)
    → Ord-to-𝕆 (𝕆-to-Ord α) ＝ α
  f α IH =
   Ord-to-𝕆 (𝕆-to-Ord α)                                   ＝⟨ I ⟩
   𝕆-ssup (𝕆-root α) (λ x → Ord-to-𝕆 (𝕆-to-Ord α ↓ x)) e l ＝⟨ II ⟩
   𝕆-ssup (𝕆-root α) (𝕆-forest α) e' l'                    ＝⟨ 𝕆-η α ⟩
   α                                                       ∎
    where
     e = Ord-to-𝕆↓-is-embedding (𝕆-to-Ord α)
     l = Ord-to-𝕆↓-is-lower-closed (𝕆-to-Ord α)

     I   = Ord-to-𝕆-behaviour (𝕆-to-Ord α)

     e' = 𝕆-forest-is-embedding α
     l' = 𝕆-forest-is-lower-closed α

     II' = λ x →
      Ord-to-𝕆 (𝕆-to-Ord α ↓ x)          ＝⟨ ap Ord-to-𝕆 (𝕆-to-Ord-equation α x) ⟩
      Ord-to-𝕆 (𝕆-to-Ord (𝕆-forest α x)) ＝⟨ IH x ⟩
      𝕆-forest α x                       ∎

     II  = to-𝕆-＝-special
            (𝕆-root α)
            (λ x → Ord-to-𝕆 (𝕆-to-Ord α ↓ x))
            (𝕆-forest α)
            e l e' l'
            (dfunext fe II')

  η : Ord-to-𝕆 ∘ 𝕆-to-Ord ∼ id
  η = 𝕆-induction' _ f

\end{code}

Hence Ord and 𝕆 are equivalent types:

\begin{code}

Ordinals-≃ : Ord ≃ 𝕆
Ordinals-≃ = Ord-to-𝕆 , Ord-to-𝕆-is-equiv

\end{code}

But more than this is true: the types 𝓞 (HoTT-book ordinal of
iterative ordinals) and OO 𝓤 (HoTT-book ordinal of HoTT-book ordinals)
are isomorphic as HoTT-book ordinals.

It is easy to see that 𝕆-to-Ord reflects order:

\begin{code}

𝕆-to-Ord-reflects-order : (α β : 𝕆) → 𝕆-to-Ord α ⊲ 𝕆-to-Ord β → α < β
𝕆-to-Ord-reflects-order α β (y , p) = III
 where
  I = 𝕆-to-Ord (𝕆-forest β y) ＝⟨ (𝕆-to-Ord-equation β y)⁻¹ ⟩
      (𝕆-to-Ord β ↓ y)        ＝⟨ p ⁻¹ ⟩
      𝕆-to-Ord α              ∎

  II : 𝕆-forest β y ＝ α
  II = equivs-are-lc ⌜ Ordinals-≃ ⌝⁻¹ ⌜ Ordinals-≃ ⌝⁻¹-is-equiv I

  III : α < β
  III = ⌜ <-behaviour α β ⌝⁻¹ (y , II)

\end{code}

And a second application of the above equation shows that 𝕆-to-Ord
preserves order.

\begin{code}

𝕆-to-Ord-preserves-order : (α β : 𝕆) → α < β → 𝕆-to-Ord α ⊲ 𝕆-to-Ord β
𝕆-to-Ord-preserves-order α β l = II I
 where
  I : Σ y ꞉ 𝕆-root β , 𝕆-forest β y ＝ α
  I = ⌜ <-behaviour α β ⌝ l

  II : type-of I → 𝕆-to-Ord α ⊲ 𝕆-to-Ord β
  II (y , refl) = IV
   where
    III : 𝕆-to-Ord (𝕆-forest β y) ＝ (𝕆-to-Ord β ↓ y)
    III = (𝕆-to-Ord-equation β y)⁻¹

    IV : 𝕆-to-Ord (𝕆-forest β y) ⊲ 𝕆-to-Ord β
    IV = y , III

\end{code}

Putting this together we get our desired isomorphism of ordinals:

\begin{code}

Ordinals-agreementₒ : 𝓞 ≃ₒ OO 𝓤
Ordinals-agreementₒ = ⌜ Ordinals-≃ ⌝⁻¹ ,
                      order-preserving-reflecting-equivs-are-order-equivs
                       𝓞
                       (OO 𝓤)
                       ⌜ Ordinals-≃ ⌝⁻¹
                       ⌜ Ordinals-≃ ⌝⁻¹-is-equiv
                       𝕆-to-Ord-preserves-order
                       𝕆-to-Ord-reflects-order
\end{code}

Which then gives an identification between the two types.

\begin{code}

Ordinals-agreement : 𝓞 ＝ OO 𝓤
Ordinals-agreement = eqtoidₒ (ua 𝓤⁺) fe 𝓞 (OO 𝓤) Ordinals-agreementₒ

\end{code}

Notice that this identification lives in the identity type of the type
of ordinals in the universe 𝓤⁺, which is a 0-type, and therefore is
unique.

\begin{code}

Ordinals-agreement-is-unique : is-singleton (𝓞 ＝[ Ordinal 𝓤⁺ ] OO 𝓤)
Ordinals-agreement-is-unique = pointed-props-are-singletons
                                Ordinals-agreement
                                (the-type-of-ordinals-is-a-set (ua (𝓤 ⁺)) fe)
\end{code}
