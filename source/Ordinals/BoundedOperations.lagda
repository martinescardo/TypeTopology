Tom de Jong, 14 and 15 July 2025.
In collaboration with Nicolai Kraus, Fredrik Nordvall Forsberg and Chuangjie Xu.

Following sketches from July 2024.

We consider the construction of certain bounded operations. The comments in the
file offer more explanation as the development continues.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.BoundedOperations
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import MLTT.Spartan
open import UF.ClassicalLogic
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import Ordinals.AdditionProperties ua
open import Ordinals.Arithmetic fe
open import Ordinals.Exponentiation.Supremum ua pt sr
open import Ordinals.Exponentiation.Taboos ua pt sr
open import Ordinals.MultiplicationProperties ua
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Type
open import Ordinals.Underlying

open PropositionalTruncation pt
open suprema pt sr

\end{code}

We start by proving that every bounded and antitone predicate that is closed
under suprema has a greatest element satisfying it.

\begin{code}

_is-upper-bound-for_ : (γ : Ordinal 𝓤) → (Ordinal 𝓤 → 𝓥 ̇ ) → 𝓤 ⁺ ⊔ 𝓥 ̇
_is-upper-bound-for_ {𝓤} γ P = (α : Ordinal 𝓤) → P α → α ⊴ γ

is-upper-bound-for-is-prop : {P : Ordinal 𝓤 → 𝓥 ̇ } → (γ : Ordinal 𝓤)
                           → is-prop (γ is-upper-bound-for P)
is-upper-bound-for-is-prop γ = Π₂-is-prop fe' (λ α _ → ⊴-is-prop-valued α γ)

_greatest-satisfying_ : Ordinal 𝓤 → (Ordinal 𝓤 → 𝓥 ̇ ) → 𝓤 ⁺ ⊔ 𝓥 ̇
_greatest-satisfying_ {𝓤} γ P = P γ × γ is-upper-bound-for P

greatest-satisfies : (γ : Ordinal 𝓤) {P : Ordinal 𝓤 → 𝓥 ̇ }
                   → γ greatest-satisfying P
                   → P γ
greatest-satisfies γ {P} = pr₁

greatest-is-upper-bound : (γ : Ordinal 𝓤) {P : Ordinal 𝓤 → 𝓥 ̇ }
                        → γ greatest-satisfying P
                        → γ is-upper-bound-for P
greatest-is-upper-bound γ {P} = pr₂

greatest-is-unique : (α β : Ordinal 𝓤) {P : Ordinal 𝓤 → 𝓥 ̇ }
                   → α greatest-satisfying P
                   → β greatest-satisfying P
                   → α ＝ β
greatest-is-unique α β (p , g) (p' , g') = ⊴-antisym α β I II
 where
  I : α ⊴ β
  I = g' α p

  II : β ⊴ α
  II = g β p'

module _ (P : Ordinal 𝓤  → 𝓥 ̇ ) where

 bounded antitone closed-under-suprema : 𝓤 ⁺ ⊔ 𝓥 ̇

 bounded = ∃ δ ꞉ Ordinal 𝓤 , ((α : Ordinal 𝓤) → P α → α ⊴ δ)
 antitone = (α β : Ordinal 𝓤) → α ⊴ β → P β → P α
 closed-under-suprema =
  (I : 𝓤 ̇ ) (F : I → Ordinal 𝓤) → ((i : I) → P (F i)) → P (sup F)

greatest-ordinal-satisfying-predicate : (P : Ordinal 𝓤 → 𝓤 ̇ )
                                      → is-prop-valued-family P
                                      → bounded P
                                      → antitone P
                                      → closed-under-suprema P
                                      → Σ γ ꞉ Ordinal 𝓤 , γ greatest-satisfying P
greatest-ordinal-satisfying-predicate
 {𝓤} P P-is-prop P-bounded P-antitone P-closed-under-sup =
  ∥∥-rec goal-is-prop goal' P-bounded
   where
    goal-is-prop : is-prop (Σ γ ꞉ Ordinal 𝓤 , γ greatest-satisfying P)
    goal-is-prop (γ , γ-greatest) (γ' , γ'-greatest) =
     to-subtype-＝ (λ δ → ×-is-prop (P-is-prop δ) (is-upper-bound-for-is-prop δ))
                   (greatest-is-unique γ γ' γ-greatest γ'-greatest)

    goal' : Σ δ ꞉ Ordinal 𝓤 , ((α : Ordinal 𝓤) → P α → α ⊴ δ)
          → Σ γ ꞉ Ordinal 𝓤 , γ greatest-satisfying P
    goal' (δ , δ-bound) = γ , γ-satisfies-P , γ-is-upper-bound
     where
      S : (α : Ordinal 𝓤) → ⟨ α ⟩ → Ordinal 𝓤
      S α a = (α ↓ a) +ₒ 𝟙ₒ

      γ : Ordinal 𝓤
      γ = sup {𝓤} {Σ x ꞉ ⟨ δ ⟩ , P (S δ x)} (λ (x , _) → S δ x)

      γ-satisfies-P : P γ
      γ-satisfies-P = P-closed-under-sup _ (λ (x , _) → S δ x) (λ (_ , p) → p)

      γ-is-upper-bound : γ is-upper-bound-for P
      γ-is-upper-bound α p = to-⊴ α γ II
       where
        I : (a : ⟨ α ⟩) → Σ bₐ ꞉ ⟨ δ ⟩ , α ↓ a ＝ δ ↓ bₐ
        I = from-≼ (⊴-gives-≼ α δ (δ-bound α p))
        II : (a : ⟨ α ⟩) → α ↓ a ⊲ γ
        II a = c , (α ↓ a         ＝⟨ II₁ ⟩
                   δ ↓ bₐ         ＝⟨ II₂ ⟩
                   S δ bₐ ↓ inr ⋆ ＝⟨ II₃ ⟩
                   γ ↓ c          ∎)
         where
          bₐ = pr₁ (I a)
          II₁ = pr₂ (I a)
          II₂ = (successor-lemma-right (δ ↓ bₐ)) ⁻¹

          p' : P (S δ bₐ)
          p' = transport P (ap (_+ₒ 𝟙ₒ) II₁) p''
           where
            p'' : P (S α a)
            p'' = P-antitone (S α a) α
                   (upper-bound-of-successors-of-initial-segments α a) p
          c : ⟨ γ ⟩
          c = [ S δ bₐ , γ ]⟨ sup-is-upper-bound _ (bₐ , p') ⟩ (inr ⋆)

          II₃ = (initial-segment-of-sup-at-component _ (bₐ , p') (inr ⋆)) ⁻¹

\end{code}

Inspecting the proof, we see that we can drop the assumption that P is
proposition-valued if we are given an explicit bound δ rather than just a proof
of the mere existence of a bound:

\begin{code}

Σ-bounded : (Ordinal 𝓤  → 𝓥 ̇ ) → 𝓤 ⁺ ⊔ 𝓥 ̇
Σ-bounded {𝓤} P = Σ δ ꞉ Ordinal 𝓤 , ((α : Ordinal 𝓤) → P α → α ⊴ δ)

greatest-ordinal-satisfying-predicate' : (P : Ordinal 𝓤 → 𝓤 ̇ )
                                       → Σ-bounded P
                                       → antitone P
                                       → closed-under-suprema P
                                       → Σ γ ꞉ Ordinal 𝓤 , γ greatest-satisfying P
greatest-ordinal-satisfying-predicate'
 {𝓤} P (δ , δ-bound) P-antitone P-closed-under-sup =
   γ , γ-satisfies-P , γ-is-upper-bound
     where
      S : (α : Ordinal 𝓤) → ⟨ α ⟩ → Ordinal 𝓤
      S α a = (α ↓ a) +ₒ 𝟙ₒ

      γ : Ordinal 𝓤
      γ = sup {𝓤} {Σ x ꞉ ⟨ δ ⟩ , P (S δ x)} (λ (x , _) → S δ x)

      γ-satisfies-P : P γ
      γ-satisfies-P = P-closed-under-sup _ (λ (x , _) → S δ x) (λ (_ , p) → p)

      γ-is-upper-bound : γ is-upper-bound-for P
      γ-is-upper-bound α p = to-⊴ α γ II
       where
        I : (a : ⟨ α ⟩) → Σ bₐ ꞉ ⟨ δ ⟩ , α ↓ a ＝ δ ↓ bₐ
        I = from-≼ (⊴-gives-≼ α δ (δ-bound α p))
        II : (a : ⟨ α ⟩) → α ↓ a ⊲ γ
        II a = c , (α ↓ a         ＝⟨ II₁ ⟩
                   δ ↓ bₐ         ＝⟨ II₂ ⟩
                   S δ bₐ ↓ inr ⋆ ＝⟨ II₃ ⟩
                   γ ↓ c          ∎)
         where
          bₐ = pr₁ (I a)
          II₁ = pr₂ (I a)
          II₂ = (successor-lemma-right (δ ↓ bₐ)) ⁻¹

          p' : P (S δ bₐ)
          p' = transport P (ap (_+ₒ 𝟙ₒ) II₁) p''
           where
            p'' : P (S α a)
            p'' = P-antitone (S α a) α
                   (upper-bound-of-successors-of-initial-segments α a) p
          c : ⟨ γ ⟩
          c = [ S δ bₐ , γ ]⟨ sup-is-upper-bound _ (bₐ , p') ⟩ (inr ⋆)

          II₃ = (initial-segment-of-sup-at-component _ (bₐ , p') (inr ⋆)) ⁻¹

\end{code}

Now we consider an endofunction t on ordinals and assume that it preserves
suprema up to a binary join in the following sense:
   t (sup F) ＝ δ₀ ∨ sup (t ∘ F)             (†)
for some fixed ordinal δ₀.

(Note that Eq. (†) forces t 𝟘ₒ to be δ₀ by considering the supremum of the empty
family.)

Examples of such endofunctions are
* addition α +ₒ_ with δ₀ ＝ α,
* multiplication α ×ₒ_ with δ₀ ＝ 𝟘ₒ
* and exponentiation α ^ₒ_ with δ₀ ＝ 𝟙ₒ (for α ⊵ 𝟙ₒ).

Then for any bound δ with δ₀ ⊴ δ, we have a greatest ordinal γ such that
γ ⊴ δ and t γ ⊴ δ.

This is close to [Theorem Schema 8D, End77] but with a few differences:
(1) loc. cit. restricts to "normal" operations, i.e. endomaps t such that
    (a) t preserves ⊲ and
    (b) t λ = sup_{β ⊲ γ} t β for all limit ordinals λ;
(2) loc. cit proves: for any bound δ with δ₀ ⊴ δ, we have a greatest ordinal γ
    such that t γ ⊴ δ (so the condition γ ⊴ δ is absent).

We will see that in several examples of t and δ, excluded middle is equivalent
to the existence of γ such that γ ⊴ δ and γ is the greatest such that t γ ⊴ δ.

[End77] Herbert B. Enderton
        Elements of Set Theory
        Academic Press
        1977
        doi:10.1016/c2009-0-22079-4

\begin{code}

module Enderton-like
        (t : Ordinal 𝓤 → Ordinal 𝓤)
        (δ₀ δ : Ordinal 𝓤)
        (δ₀-below-δ : δ₀ ⊴ δ)
        (t-preserves-suprema-up-to-join
          : (I : 𝓤 ̇ ) (F : I → Ordinal 𝓤)
          → t (sup F) ＝ sup (cases (λ (_ : 𝟙{𝓤}) → δ₀) (t ∘ F)))
       where

 private
  t-is-monotone : (α β : Ordinal 𝓤) → α ⊴ β → t α ⊴ t β
  t-is-monotone α β l = III
   where
    F : 𝟙{𝓤} + 𝟙{𝓤} → Ordinal 𝓤
    F (inl ⋆) = α
    F (inr ⋆) = β
    I : sup F ＝ β
    I = ⊴-antisym (sup F) β
         (sup-is-lower-bound-of-upper-bounds F β ub)
         (sup-is-upper-bound F (inr ⋆))
     where
      ub : (i : 𝟙 + 𝟙) → F i ⊴ β
      ub (inl ⋆) = l
      ub (inr ⋆) = ⊴-refl β
    II : t (sup F) ＝ sup (cases (λ _ → δ₀) (t ∘ F))
    II = t-preserves-suprema-up-to-join _ F
    III : t α ⊴ t β
    III = transport⁻¹
           (t α ⊴_)
           (ap t I ⁻¹ ∙ II)
           (sup-is-upper-bound (cases (λ _ → δ₀) (t ∘ F)) (inr (inl ⋆)))

 enderton-like
  : Σ γ ꞉ Ordinal 𝓤 , γ greatest-satisfying (λ - → (t - ⊴ δ) × (- ⊴ δ))
 enderton-like = greatest-ordinal-satisfying-predicate
                  P
                  P-is-prop
                  P-bounded
                  P-antitone
                  P-closed-under-suprema
  where
   P : Ordinal 𝓤 → 𝓤 ̇
   P α = (t α ⊴ δ) × (α ⊴ δ)
   P-is-prop : (α : Ordinal 𝓤) → is-prop (P α)
   P-is-prop α = ×-is-prop (⊴-is-prop-valued (t α) δ) (⊴-is-prop-valued α δ)
   P-closed-under-suprema : closed-under-suprema P
   P-closed-under-suprema I F ρ =
    transport⁻¹ (_⊴ δ) (t-preserves-suprema-up-to-join _ F) l ,
    sup-is-lower-bound-of-upper-bounds F δ (λ i → pr₂ (ρ i))
     where
      l : sup (cases (λ ⋆ → δ₀) (λ i → t (F i))) ⊴ δ
      l = sup-is-lower-bound-of-upper-bounds _ δ h
       where
        h : (x : 𝟙 + I) → cases (λ ⋆ → δ₀) (λ i → t (F i)) x ⊴ δ
        h (inl ⋆) = δ₀-below-δ
        h (inr i) = pr₁ (ρ i)
   P-antitone : (α₁ α₂ : Ordinal 𝓤) → α₁ ⊴ α₂ → P α₂ → P α₁
   P-antitone α₁ α₂ k (l , m) =
     ⊴-trans (t α₁) (t α₂) δ (t-is-monotone α₁ α₂ k) l ,
     ⊴-trans α₁ α₂ δ k m
   P-bounded : ∃ β ꞉ Ordinal 𝓤 , ((α : Ordinal 𝓤) → P α → α ⊴ β)
   P-bounded = ∣ δ , (λ α p → pr₂ p) ∣

\end{code}

We also provide the following more convenient interface in case we have an
endofunction t that simply preserves suprema.

\begin{code}

module Enderton-like'
        (t : Ordinal 𝓤 → Ordinal 𝓤)
        (δ : Ordinal 𝓤)
        (t-preserves-suprema : (I : 𝓤 ̇ ) (F : I → Ordinal 𝓤)
                             → t (sup F) ＝ sup (t ∘ F))
       where

 preservation-of-suprema-up-to-join
  : (I : 𝓤 ̇) (F : I → Ordinal 𝓤)
  → t (sup F) ＝ sup (cases (λ _  → 𝟘ₒ) (t ∘ F))
 preservation-of-suprema-up-to-join I F =
  t-preserves-suprema I F
  ∙ (⊴-antisym (sup (t ∘ F)) (sup G) u v)
  where
   G : 𝟙{𝓤} + I → Ordinal 𝓤
   G = cases (λ _ → 𝟘ₒ) (t ∘ F)
   u : sup (t ∘ F) ⊴ sup G
   u = sup-is-lower-bound-of-upper-bounds (t ∘ F) (sup G)
        (λ i → sup-is-upper-bound G (inr i))
   v : sup G ⊴ sup (t ∘ F)
   v = sup-is-lower-bound-of-upper-bounds G (sup (t ∘ F)) w
    where
     w : (x : 𝟙 + I)
       → cases (λ _ → 𝟘ₒ) (t ∘ F) x ⊴ sup (t ∘ F)
     w (inl ⋆) = 𝟘ₒ-least-⊴ (sup (t ∘ F))
     w (inr i) = sup-is-upper-bound (t ∘ F) i

 open Enderton-like
       t 𝟘ₒ δ (𝟘ₒ-least-⊴ δ) preservation-of-suprema-up-to-join
      public

\end{code}

If we additionally assume that t is inflationary, then can construct the
greatest γ such that t γ ⊴ δ (and the separate property γ ⊴ δ follows).

\begin{code}

module Enderton-like-inflationary
        (t : Ordinal 𝓤 → Ordinal 𝓤)
        (δ₀ δ : Ordinal 𝓤)
        (δ₀-below-δ : δ₀ ⊴ δ)
        (t-preserves-suprema-up-to-join
          : (I : 𝓤 ̇ ) (F : I → Ordinal 𝓤)
          → t (sup F) ＝ sup (cases (λ (_ : 𝟙{𝓤}) → δ₀) (t ∘ F)))
        (t-inflationary : (α : Ordinal 𝓤) → α ⊴ t α)
       where

 enderton-like-inflationary
  : Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ δ) × (γ greatest-satisfying (λ - → t - ⊴ δ))
 enderton-like-inflationary = γ , IV , III , VI
  where
   open Enderton-like t δ₀ δ δ₀-below-δ t-preserves-suprema-up-to-join
   I : Σ γ ꞉ Ordinal 𝓤 , γ greatest-satisfying (λ - → (t - ⊴ δ) × (- ⊴ δ))
   I = enderton-like
   γ : Ordinal 𝓤
   γ = pr₁ I
   II : γ greatest-satisfying (λ - → (t - ⊴ δ) × (- ⊴ δ))
   II = pr₂ I
   III : t γ ⊴ δ
   III = pr₁ (greatest-satisfies γ II)
   IV : γ ⊴ δ
   IV = pr₂ (greatest-satisfies γ II)
   V : γ is-upper-bound-for (λ - → (t - ⊴ δ) × (- ⊴ δ))
   V = pr₂ II
   VI : γ is-upper-bound-for (λ - → t - ⊴ δ)
   VI α l = V α (l , (⊴-trans α (t α) δ (t-inflationary α) l))

\end{code}

The following provides a convenient interface for inflationary endofunctions
that simply preserve suprema.

\begin{code}

module Enderton-like-inflationary'
        (t : Ordinal 𝓤 → Ordinal 𝓤)
        (δ : Ordinal 𝓤)
        (t-preserves-suprema : (I : 𝓤 ̇ ) (F : I → Ordinal 𝓤)
                             → t (sup F) ＝ sup (t ∘ F))
        (t-inflationary : (α : Ordinal 𝓤) → α ⊴ t α)
       where

 open Enderton-like-inflationary
       t 𝟘ₒ δ (𝟘ₒ-least-⊴ δ)
       (Enderton-like'.preservation-of-suprema-up-to-join
         t δ t-preserves-suprema)
       t-inflationary
      public

\end{code}

We now consider some examples and applications.

While the existence of a subtraction function on ordinals implies excluded
middle (see Ordinals.AdditionProperties), we can construct an approximation of what
would be the ordinal β - α (for α ⊴ β) in the following sense.

\begin{code}

approximate-subtraction
 : (α β : Ordinal 𝓤) → α ⊴ β
 → Σ γ ꞉ Ordinal 𝓤 , γ greatest-satisfying (λ - → (α +ₒ - ⊴ β) × (- ⊴ β))
approximate-subtraction {𝓤} α β l = enderton-like
 where
  open Enderton-like (α +ₒ_) α β l (+ₒ-preserves-suprema-up-to-join pt sr α)

\end{code}

In a similar sense, we can approximate division of ordinals.

\begin{code}

approximate-division
 : (α β : Ordinal 𝓤)
 → Σ γ ꞉ Ordinal 𝓤 , γ greatest-satisfying (λ - → (α ×ₒ - ⊴ β) × (- ⊴ β))
approximate-division {𝓤} α β = enderton-like
 where
  open Enderton-like' (α ×ₒ_) β (×ₒ-preserves-suprema pt sr α)

\end{code}

Note that it is not technically necessary to assume 𝟘ₒ ⊲ α in the above, even
though division by 𝟘ₒ is not well defined. In fact, the - ⊴ β requirement forces
γ ＝ β in case α ＝ 𝟘₀.

Again, in a similar sense, we can approximate logarithms of
ordinals. And similarly, assuming 𝟙ₒ ⊲ α isn't needed.

\begin{code}

aproximate-logarithm
 : (α β : Ordinal 𝓤) → 𝟙ₒ ⊴ β
 → Σ γ ꞉ Ordinal 𝓤 ,
    γ greatest-satisfying (λ - → (α ^ₒ - ⊴ β) × (- ⊴ β))
aproximate-logarithm {𝓤} α β β-pos = enderton-like
 where
 open Enderton-like (α ^ₒ_) 𝟙ₒ β β-pos (^ₒ-satisfies-strong-sup-specification α)

\end{code}

Now, as alluded to above, the seemingly mild variation

approximate-subtraction-variation
 : (α β : Ordinal 𝓤) → α ⊴ β
 → Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ β) × (γ greatest-satisfying (λ - → (α +ₒ - ⊴ β)))

is equivalent to excluded middle, and similarly for division and logarithm.

\begin{code}

approximate-subtraction-variation-implies-EM
 : ((α β : Ordinal 𝓤) → α ⊴ β
   → Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ β) × (γ greatest-satisfying (λ - → (α +ₒ - ⊴ β))))
 → EM 𝓤
approximate-subtraction-variation-implies-EM {𝓤} hyp =
 +ₒ-as-large-as-right-summand-implies-EM I
  where
   I : (α β : Ordinal 𝓤) → β ⊴ α +ₒ β
   I α β = IV
    where
     II : Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ α +ₒ β)
                          × (γ greatest-satisfying (λ - → α +ₒ - ⊴ α +ₒ β))
     II = hyp α (α +ₒ β) (+ₒ-left-⊴ α β)
     γ = pr₁ II
     III : β ⊴ γ
     III = greatest-is-upper-bound γ (pr₂ (pr₂ II)) β (⊴-refl (α +ₒ β))
     IV : β ⊴ α +ₒ β
     IV = ⊴-trans β γ (α +ₒ β) III (pr₁ (pr₂ II))

EM-implies-approximate-subtraction-variation
 : EM 𝓤
 → (α β : Ordinal 𝓤) → α ⊴ β
   → Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ β) × (γ greatest-satisfying (λ - → (α +ₒ - ⊴ β)))
EM-implies-approximate-subtraction-variation {𝓤} em α β l =
 enderton-like-inflationary
  where
   open Enderton-like-inflationary
         (α +ₒ_) α β l
         (+ₒ-preserves-suprema-up-to-join pt sr α)
         (EM-implies-+ₒ-as-large-as-right-summand em α)

\end{code}

Indeed, analogous results hold for approximate division (with the assumption
𝟘₀ ⊲ α this time) and logarithm (with the assumption 𝟙₀ ⊲ α this time).

\begin{code}

approximate-division-variation-implies-EM
 : ((α β : Ordinal 𝓤) → 𝟘ₒ ⊲ α
   → Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ β) × (γ greatest-satisfying (λ - → (α ×ₒ - ⊴ β))))
 → EM 𝓤
approximate-division-variation-implies-EM {𝓤} hyp =
 ×ₒ-as-large-as-right-factor-implies-EM I
  where
   I : (α β : Ordinal 𝓤) → 𝟘ₒ ⊲ α → β ⊴ α ×ₒ β
   I α β α-pos = IV
    where
     II : Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ α ×ₒ β)
                          × (γ greatest-satisfying (λ - → α ×ₒ - ⊴ α ×ₒ β))
     II = hyp α (α ×ₒ β) α-pos
     γ = pr₁ II
     III : β ⊴ γ
     III = greatest-is-upper-bound γ (pr₂ (pr₂ II)) β (⊴-refl (α ×ₒ β))
     IV : β ⊴ α ×ₒ β
     IV = ⊴-trans β γ (α ×ₒ β) III (pr₁ (pr₂ II))

EM-implies-approximate-division-variation
 : EM 𝓤
 → (α β : Ordinal 𝓤) → 𝟘ₒ ⊲ α
   → Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ β) × (γ greatest-satisfying (λ - → (α ×ₒ - ⊴ β)))
EM-implies-approximate-division-variation em α β α-pos =
 enderton-like-inflationary
  where
   open Enderton-like-inflationary'
         (α ×ₒ_) β
         (×ₒ-preserves-suprema pt sr α)
         (λ δ → EM-implies-×ₒ-as-large-as-right-factor em α δ α-pos)

approximate-logarithm-variation-implies-EM
 : ((α β : Ordinal 𝓤) → 𝟙ₒ ⊴ β → 𝟙ₒ ⊲ α
   → Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ β) × (γ greatest-satisfying (λ - → (α ^ₒ - ⊴ β))))
 → EM 𝓤
approximate-logarithm-variation-implies-EM {𝓤} hyp =
 ^ₒ-as-large-as-exponent-implies-EM I
  where
   I : (α β : Ordinal 𝓤) → 𝟙ₒ ⊲ α → β ⊴ α ^ₒ β
   I α β α-strictly-pos = IV
    where
     II : Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ α ^ₒ β)
                          × (γ greatest-satisfying (λ - → α ^ₒ - ⊴ α ^ₒ β))
     II = hyp α (α ^ₒ β) (^ₒ-has-least-element α β) α-strictly-pos
     γ = pr₁ II
     III : β ⊴ γ
     III = greatest-is-upper-bound γ (pr₂ (pr₂ II)) β (⊴-refl (α ^ₒ β))
     IV : β ⊴ α ^ₒ β
     IV = ⊴-trans β γ (α ^ₒ β) III (pr₁ (pr₂ II))

EM-implies-approximate-logarithm-variation
 : EM 𝓤
 → (α β : Ordinal 𝓤) → 𝟙ₒ ⊴ β → 𝟙ₒ ⊲ α
   → Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ β) × (γ greatest-satisfying (λ - → (α ^ₒ - ⊴ β)))
EM-implies-approximate-logarithm-variation em α β β-pos α-strictly-pos =
 enderton-like-inflationary
  where
   open Enderton-like-inflationary
         (α ^ₒ_) 𝟙ₒ β β-pos
         (^ₒ-satisfies-strong-sup-specification α)
         (λ δ → EM-implies-^ₒ-as-large-as-exponent em α δ α-strictly-pos)

\end{code}
