--------------------------------------------------------------------------------
title:          Frame isomorphisms
author:         Ayberk Tosun
date-started:   2024-04-11
--------------------------------------------------------------------------------

Notions of frame isomorphism and their equivalences.

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.FunExt
open import UF.PropTrunc

module Locales.ContinuousMap.FrameIsomorphism-Definition
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.Frame pt fe
open import Slice.Family
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.Logic
open import UF.Retracts
open import UF.SIP
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

open AllCombinators pt fe
open FrameHomomorphismProperties
open FrameHomomorphisms

\end{code}

We work in a module parameterized by two frames `F` and `G`.

\begin{code}

module FrameIsomorphisms (F : Frame 𝓤 𝓥 𝓦) (G : Frame 𝓤' 𝓥' 𝓦) where

\end{code}

We start with the record-based definition of the notion of frame isomorphism.

\begin{code}

 record Isomorphismᵣ : 𝓤 ⊔ 𝓤' ⊔ 𝓥 ⊔ 𝓥' ⊔ 𝓦 ⁺  ̇ where
  field
   forward  : F ─f→ G
   backward : G ─f→ F

  s : ⟨ F ⟩ → ⟨ G ⟩
  s = fun F G forward

  r : ⟨ G ⟩ → ⟨ F ⟩
  r = fun G F backward

  s-is-homomorphism : is-a-frame-homomorphism F G s holds
  s-is-homomorphism = fun-is-a-frame-homomorphism F G forward

  r-is-homomorphism : is-a-frame-homomorphism G F r holds
  r-is-homomorphism = fun-is-a-frame-homomorphism G F backward

  field
   backward-cancels-forward : r ∘ s ∼ id
   forward-cancels-backward : s ∘ r ∼ id

\end{code}

We now show the equivalence of this to a record-based definition.

Given a frame homomorphism `F ─f→ G`, its type of homomorphic inverses is a
proposition.

\begin{code}

 homomorphic-inverse : (F ─f→ G) → 𝓤 ⊔ 𝓤' ⊔ 𝓥 ⊔ 𝓦 ⁺  ̇
 homomorphic-inverse s =
  Σ r ꞉ (G ─f→ F) , fun F G s ∘ fun G F r ∼ id
                  × fun G F r ∘ fun F G s ∼ id

 homomorphic-inverse-is-prop : (h : F ─f→ G) → is-prop (homomorphic-inverse h)
 homomorphic-inverse-is-prop h (r , φ , ψ) (r′ , φ′ , ψ′) =
  to-subtype-＝ † (to-frame-homomorphism-＝ G F r r′ ‡)
   where
    † : (h′ : G ─f→ F)
      → is-prop (fun F G h ∘ fun G F h′ ∼ id × fun G F h′ ∘ fun F G h ∼ id)
    † h′ = ×-is-prop
            (Π-is-prop fe (λ _ → carrier-of-[ poset-of G ]-is-set))
            (Π-is-prop fe (λ _ → carrier-of-[ poset-of F ]-is-set))

    ϑ : fun F G h ∘ fun G F r ∼ fun F G h ∘ fun G F r′
    ϑ y = fun F G h (fun G F r y)   ＝⟨ Ⅰ ⟩
          y                         ＝⟨ Ⅱ ⟩
          fun F G h (fun G F r′ y)  ∎
           where
            Ⅰ = φ y
            Ⅱ = φ′ y ⁻¹

    ξ : left-cancellable (fun F G h)
    ξ = sections-are-lc (fun F G h) (fun G F r , ψ)

    ‡ : (y : ⟨ G ⟩) → fun G F r y ＝ fun G F r′ y
    ‡ y = ξ (ϑ y)

\end{code}

To say that a frame homomorphism is an isomorphism is to say that its type
of homomorphic inverses is inhabited.

\begin{code}

 is-isomorphism : (F ─f→ G) → Ω (𝓤 ⊔ 𝓤' ⊔ 𝓥 ⊔ 𝓦 ⁺)
 is-isomorphism h = homomorphic-inverse h , homomorphic-inverse-is-prop h

\end{code}

Accordingly, we define the type of isomorphisms between frames `F` and `G`.

\begin{code}

 Isomorphism : 𝓤 ⊔ 𝓤' ⊔ 𝓥 ⊔ 𝓥' ⊔ 𝓦 ⁺  ̇
 Isomorphism = Σ h ꞉ F ─f→ G , is-isomorphism h holds

\end{code}

It is immediate that `Isomorphism` and `Isomorphismᵣ` are equivalent types.

\begin{code}

 isomorphism-to-isomorphismᵣ : Isomorphism → Isomorphismᵣ
 isomorphism-to-isomorphismᵣ (𝓈 , 𝓇 , φ , ψ) =
  record
   { forward                  = 𝓈
   ; backward                 = 𝓇
   ; backward-cancels-forward = ψ
   ; forward-cancels-backward = φ
   }

 isomorphismᵣ-to-isomorphism : Isomorphismᵣ → Isomorphism
 isomorphismᵣ-to-isomorphism iso =
  let
   open Isomorphismᵣ iso
  in
   forward , backward , forward-cancels-backward , backward-cancels-forward

 isomorphism-equiv-to-isomorphismᵣ : Isomorphism ≃ Isomorphismᵣ
 isomorphism-equiv-to-isomorphismᵣ = isomorphism-to-isomorphismᵣ
                                   , (isomorphismᵣ-to-isomorphism , λ _ → refl)
                                   , isomorphismᵣ-to-isomorphism , λ _ → refl

\end{code}

We now give an alternative definition of the same notion.

The predicate `is-homomorphic` below expresses what it means for an equivalence
between the carrier sets of `F` and `G` to be homomorphic.

\begin{code}

 is-homomorphic : (⟨ F ⟩ ≃ ⟨ G ⟩) → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥' ⊔ 𝓦 ⁺)
 is-homomorphic e = is-a-frame-homomorphism F G ⌜ e ⌝
                  ∧ is-a-frame-homomorphism G F (e⁻¹ (⌜⌝-is-equiv e))
  where
   e⁻¹ = inverse ⌜ e ⌝

\end{code}

The type of isomorphisms between `F` and `G` could alternatively be defined
as the type of homomorphic equivalences.

\begin{code}

 Isomorphism₀ : 𝓤 ⊔ 𝓤' ⊔ 𝓥 ⊔ 𝓥' ⊔ 𝓦 ⁺  ̇
 Isomorphism₀ = Σ e ꞉ ⟨ F ⟩ ≃ ⟨ G ⟩ , is-homomorphic e holds

\end{code}

These two notions of frame isomorphism are equivalent.

\begin{code}

 isomorphismᵣ-to-isomorphism₀ : Isomorphismᵣ → Isomorphism₀
 isomorphismᵣ-to-isomorphism₀ iso = (s , † , ‡) , φ , ψ
  where
   open Isomorphismᵣ iso

   † : has-section s
   † = r , forward-cancels-backward

   ‡ : is-section s
   ‡ = r , backward-cancels-forward

   φ : is-a-frame-homomorphism F G s holds
   φ = fun-is-a-frame-homomorphism F G forward

   ψ : is-a-frame-homomorphism G F r holds
   ψ = fun-is-a-frame-homomorphism G F backward

 isomorphism₀-to-isomorphismᵣ : Isomorphism₀ → Isomorphismᵣ
 isomorphism₀-to-isomorphismᵣ (e , φ , ψ)  =
  record
   { forward                  = ⌜ e ⌝ , φ
   ; backward                 = inverse ⌜ e ⌝ (⌜⌝-is-equiv e) , ψ
   ; backward-cancels-forward = inverses-are-retractions ⌜ e ⌝ (⌜⌝-is-equiv e)
   ; forward-cancels-backward = inverses-are-sections ⌜ e ⌝ (⌜⌝-is-equiv e)
   }

 isomorphism-to-isomorphism₀ : Isomorphism → Isomorphism₀
 isomorphism-to-isomorphism₀ =
  isomorphismᵣ-to-isomorphism₀ ∘ isomorphism-to-isomorphismᵣ

 isomorphism₀-to-isomorphism : Isomorphism₀ → Isomorphism
 isomorphism₀-to-isomorphism =
  isomorphismᵣ-to-isomorphism ∘ isomorphism₀-to-isomorphismᵣ

 isomorphism-equivalent-to-isomorphism₀ : Isomorphism ≃ Isomorphism₀
 isomorphism-equivalent-to-isomorphism₀ = isomorphism-to-isomorphism₀
                                        , (isomorphism₀-to-isomorphism , †)
                                        , (isomorphism₀-to-isomorphism , ‡)
  where
   † : isomorphism-to-isomorphism₀ ∘ isomorphism₀-to-isomorphism ∼ id
   † (h , _) =
    to-subtype-＝
     (holds-is-prop ∘ is-homomorphic)
     (to-subtype-＝ (being-equiv-is-prop (λ 𝓤 𝓥 → fe {𝓤} {𝓥})) refl)

   ‡ : isomorphism₀-to-isomorphism ∘ isomorphism-to-isomorphism₀ ∼ id
   ‡ iso = to-subtype-＝ (holds-is-prop ∘ is-isomorphism) refl

 isomorphismᵣ-equivalent-to-isomorphism₀ : Isomorphismᵣ ≃ Isomorphism₀
 isomorphismᵣ-equivalent-to-isomorphism₀ =
  Isomorphismᵣ   ≃⟨ Ⅰ ⟩
  Isomorphism    ≃⟨ Ⅱ ⟩
  Isomorphism₀   ■
   where
    Ⅰ = ≃-sym isomorphism-equiv-to-isomorphismᵣ
    Ⅱ = isomorphism-equivalent-to-isomorphism₀

\end{code}

Declare syntax for frame isomorphisms.

\begin{code}

Isomorphismᵣ-Syntax : Frame 𝓤 𝓥 𝓦 → Frame 𝓤' 𝓥' 𝓦 → 𝓤 ⊔ 𝓤' ⊔ 𝓥 ⊔ 𝓥' ⊔ 𝓦 ⁺  ̇
Isomorphismᵣ-Syntax = FrameIsomorphisms.Isomorphismᵣ

infix 0 Isomorphismᵣ-Syntax
syntax Isomorphismᵣ-Syntax F G = F ≅f≅ G

\end{code}

Added on 2024-04-14.

The identity equivalence is trivially homomorphic.

\begin{code}

𝔦𝔡 : (L : Frame 𝓤 𝓥 𝓦) → ⟨ L ⟩ ≃ ⟨ L ⟩
𝔦𝔡 L = ≃-refl sip.⟨ L ⟩

𝔦𝔡-preserves-top : (L : Frame 𝓤 𝓥 𝓦) → preserves-top L L ⌜ 𝔦𝔡 L ⌝ holds
𝔦𝔡-preserves-top L = refl

𝔦𝔡-preserves-binary-meets : (L : Frame 𝓤 𝓥 𝓦)
                          → preserves-binary-meets L L ⌜ 𝔦𝔡 L ⌝ holds
𝔦𝔡-preserves-binary-meets _ _ _ = refl

𝔦𝔡-preserves-joins : (L : Frame 𝓤 𝓥 𝓦) → preserves-joins L L ⌜ 𝔦𝔡 L ⌝ holds
𝔦𝔡-preserves-joins L S = † , ‡
 where
  open Joins (λ x y → x ≤[ poset-of L ] y)

  † : ((⋁[ L ] S) is-an-upper-bound-of S) holds
  † = ⋁[ L ]-upper S

  ‡ : ((u , _) : upper-bound S) → ((⋁[ L ] S) ≤[ poset-of L ] u) holds
  ‡ = ⋁[ L ]-least S

𝔦𝔡-is-frame-homomorphism : (L : Frame 𝓤 𝓥 𝓦)
                         → is-a-frame-homomorphism L L ⌜ 𝔦𝔡 L ⌝ holds
𝔦𝔡-is-frame-homomorphism L = 𝔦𝔡-preserves-top L
                           , 𝔦𝔡-preserves-binary-meets L
                           , 𝔦𝔡-preserves-joins L

𝔦𝔡ₕ : (L : Frame 𝓤 𝓥 𝓦) → L ─f·→ L
𝔦𝔡ₕ L =
 frame-homomorphism-to-frame-homomorphismᵣ
  L
  L
  (⌜ 𝔦𝔡 L ⌝ , 𝔦𝔡-is-frame-homomorphism L)

id-equiv-is-homomorphic : (L : Frame 𝓤 𝓥 𝓦)
                         → FrameIsomorphisms.is-homomorphic L L (𝔦𝔡 L) holds
id-equiv-is-homomorphic L =
 𝔦𝔡-is-frame-homomorphism L , 𝔦𝔡-is-frame-homomorphism L

\end{code}
