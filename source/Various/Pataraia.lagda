Martin Escardo, 26 Feb 2023

We implement Pataraia's result that every monotone endomap of a dcpo
(directed complete poset) with a least element has a least fixed point
in topos logic. This is Corollary-2·1 below.

Pataraia [1] was the first to give a constructive proof of this in
topos logic. A version of his proof is published in [2] by Escardo,
with Pataraia's permission. Pataraia himself didn't publish the
result. An earlier, less general, theorem was proved by Coquand [3]
for *bounded complete* dcpos, with an easier proof.

The proof given here follows [2] closely and is impredicative (as is
the one given in [3]). For a predicative version, see the module
Various.Pataraia-Taylor.

[1] Dito Pataraia. A constructive proof of Tarski’s fixed-point
    theorem for dcpo’s. Presented at the 65th Peripatetic Seminar on
    Sheaves and Logic, Aarhus, Denmark, November 1997.

[2] Martin Escardo. Joins in the frame of nuclei.
    Applied Categorical Structures 11: 117–124, 2003.
    https://doi.org/10.1023/A:1023555514029

[3] Thierry Coquand. A topos theoretic fix point theorem.
    Unpublished manuscript, June 1995.
    https://web.archive.org/web/20110822085930/
    https://www.cse.chalmers.se/~coquand/fix.pdf

We prove the following from [2].

  Lemma 2·1.     The set of all monotone inflationary maps on any dcpo
                 has a common fixed point.

  Theorem 2·2.   Any set F of monotone inflationary maps on a dcpo 𝓓
                 with a least element ⊥ has a least common fixed
                 point.

                 Moreover, any subset of D that has ⊥ as a member, is
                 closed under every f in F, and is closed under
                 directed suprema has the least common fixed point as
                 a member.

  Corollary 2·1. Any monotone endomap of a dcpo with ⊥ has a least
                 fixed point.

Notice that Corollary 2.1 doesn't generalize from single monotone maps
to sets of monotone maps, as exemplified by any poset with a least
element and two maximal elements and by the two constant endomaps that
fix each of these two maximal elements.

I am not sure why the publisher gave the number 2.1 to the corollary
that follows Theorem 2.2.

One minor difference here is that we work with families of functions
rather than sets of functions, which is more natural in dependent type
theory.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module Various.Pataraia
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓤 : Universe)
       where

open PropositionalTruncation pt

open import DomainTheory.Basics.Dcpo pt fe 𝓤
open import DomainTheory.Basics.Miscelanea pt fe 𝓤
open import UF.Sets
open import UF.Sets-Properties
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

The following is Lemma 2.1 of [2].

\begin{code}

module lemma₂·₁ (𝓔 : DCPO {𝓤} {𝓤}) where

 private
  E   = ⟨ 𝓔 ⟩
  _⊑_ = underlying-order 𝓔

\end{code}

We now define the pointed type MI of monotone inflationary endomaps of
the underlying set E of the dcpo 𝓔. Notice that E is allowed to be
empty.

\begin{code}

 MI : 𝓤 ̇
 MI = Σ f ꞉ (E → E) , is-monotone 𝓔 𝓔 f × is-inflationary 𝓔 f

 𝕚𝕕 : MI
 𝕚𝕕 = id , id-is-monotone 𝓔 , id-is-inflationary 𝓔

\end{code}

We use the following auxiliary function Γ : E → MI → E to define a
function γ : E → E with suitable properties. For each x : E we get a
directed family Γ x : MI → E, and we define γ x to be the supremum of
this family.

\begin{code}

 Γ : E → MI → E
 Γ x (f , _) = f x

 Γ-is-semidirected : (x : E) → is-Semidirected 𝓔 (Γ x)
 Γ-is-semidirected x 𝕗@(f , fm , fi) 𝕘@(g , gm , gi) = ∣ 𝕙 , f-le-h , g-le-h ∣
  where
   h = g ∘ f

   𝕙 : MI
   𝕙 = (h , ∘-is-monotone 𝓔 𝓔 𝓔 f g fm gm , ∘-is-inflationary 𝓔 f g fi gi)

   f-le-h : f x ⊑ h x
   f-le-h = gi (f x)

   g-le-h : g x ⊑ h x
   g-le-h = gm x (f x) (fi x)

 Γ-is-directed : (x : E) → is-Directed 𝓔 (Γ x)
 Γ-is-directed x = ∣ 𝕚𝕕 ∣ , Γ-is-semidirected x

 γ : E → E
 γ x = ∐ 𝓔 (Γ-is-directed x)

\end{code}

So the function γ is the pointwise supremum of the monotone
inflationary endomaps of E.

\begin{code}

 γ-is-monotone : is-monotone 𝓔 𝓔 γ
 γ-is-monotone x y l = ∐-is-monotone 𝓔 (Γ-is-directed x) (Γ-is-directed y) l'
  where
   l' : (𝕗 : MI) → Γ x 𝕗 ⊑ Γ y 𝕗
   l' (f , fm , fi) = fm x y l

\end{code}

From this it is easy to conclude that γ is the greatest monotone
inflationary map for any x : E.

\begin{code}

 γ-is-greatest-mi-map : ((f , fm , fi) : MI) (x : E) → f x ⊑ γ x
 γ-is-greatest-mi-map 𝕗 x = ∐-is-upperbound 𝓔 (Γ-is-directed x) 𝕗

 γ-is-inflationary : is-inflationary 𝓔 γ
 γ-is-inflationary = γ-is-greatest-mi-map 𝕚𝕕

\end{code}

And, in turn, from this we conclude that γ x is a fixed point of any
monotone inflationary map f : E → E.

\begin{code}

 γ-is-fixed-point : ((f , fm , fi) : MI) (x : E) → f (γ x) ＝ γ x
 γ-is-fixed-point (f , fm , fi) x = antisymmetry 𝓔 _ _ I II
  where
   I : f (γ x) ⊑ γ x
   I = γ-is-greatest-mi-map
        (f ∘ γ ,
         ∘-is-monotone 𝓔 𝓔 𝓔 γ f γ-is-monotone fm ,
         ∘-is-inflationary 𝓔 γ f γ-is-inflationary fi)
       x

   II : γ x ⊑ f (γ x)
   II = fi (γ x)

\end{code}

This concludes the proof of Lemma 2·1, which we use to
prove Theorem 2·2.

\begin{code}

module theorem₂·₂
        (ρ : Propositional-Resizing)
        (𝓓 : DCPO {𝓤} {𝓤})
        ((⊥ , ⊥-is-least) : has-bottom 𝓓)
        (I : 𝓤 ̇ )
        (f : I → ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩)
        (fm : (i : I) → is-monotone 𝓓 𝓓 (f i))
        (fi : (i : I) → is-inflationary 𝓓 (f i))
       where

 private
  D   = ⟨ 𝓓 ⟩
  _⊑_ = underlying-order 𝓓

 open import UF.Logic
 open import UF.Powerset
 open import UF.Powerset-Resizing fe ρ
 open import UF.SubtypeClassifier hiding (⊥)

 open AllCombinators pt fe

 C₁ : (D → Ω 𝓤) → Ω (𝓤 ⁺)
 C₁ = is-closed-under-directed-supsₚ 𝓓

 C₂ : (D → Ω 𝓤) → Ω 𝓤
 C₂ = λ A → ⊥ ∈ₚ A

 C₃ : (D → Ω 𝓤) → Ω 𝓤
 C₃ = λ A → Ɐ i ꞉ I , Ɐ x ꞉ D , x ∈ₚ A ⇒ f i x ∈ₚ A

 C : (D → Ω 𝓤) → Ω (𝓤 ⁺)
 C = λ A → A ∈ₚ C₁ ∧ A ∈ₚ C₂ ∧ A ∈ₚ C₃

 B₁ : ⋂ C ∈ C₁
 B₁ {I} α δ κ =
  to-⋂ C (∐ 𝓓 δ)
  (λ A c@(c₁ , c₂ , c₃) → c₁ α δ (λ (i : I) → from-⋂ C (α i) (κ i) A c))

 B₂ : ⋂ C ∈ C₂
 B₂ = to-⋂ C ⊥ (λ A (c₁ , c₂ , c₃) → c₂)

 B₃ : ⋂ C ∈ C₃
 B₃ i x x-in-⋂ =
  to-⋂ C
   (f i x)
   (λ A c@(c₁ , c₂ , c₃) → c₃ i x (from-⋂ C x x-in-⋂ A c))

 B : ⋂ C ∈ C
 B = B₁ , B₂ , B₃

 private
  𝓔 : DCPO
  𝓔 = subdcpoₚ 𝓓 (⋂ C) B₁

  E = ⟨ 𝓔 ⟩
  _≤_ : E → E → 𝓤 ̇
  s ≤ t = s ⊑⟨ 𝓔 ⟩ t

  ι : E → D
  ι (x , c) = x

  τ : (t : E) → ι t ∈ ⋂ C
  τ (x , c) = c

  ⊥𝓔 : E
  ⊥𝓔 =  ⊥ , B₂

\end{code}

The monotone inflationary functions fᵢ : D → D restrict to monotone
inflationary functions 𝓯ᵢ : E → E.

\begin{code}

 private
  𝓯 : I → E → E
  𝓯 i (x , c) = f i x , B₃ i x c

  𝓯-is-monotone : (i : I) (s t : E) → s ≤ t → 𝓯 i s ≤ 𝓯 i t
  𝓯-is-monotone i (x , _) (y , _) = fm i x y

  𝓯-is-inflationary : (i : I) (t : E) → t ≤ 𝓯 i t
  𝓯-is-inflationary i (x , c) = fi i x

\end{code}

So now we can apply lemma₂·₁.

\begin{code}

 open lemma₂·₁ 𝓔

 𝕗 : I → MI
 𝕗 i = (𝓯 i , 𝓯-is-monotone i , 𝓯-is-inflationary i)

 e₀ : E
 e₀ = γ ⊥𝓔

 e₀-is-fp : (i : I) → 𝓯 i e₀ ＝ e₀
 e₀-is-fp i = γ-is-fixed-point (𝕗 i) ⊥𝓔

 d₀ : D
 d₀ = ι e₀

\end{code}

d₀ is a common fixed point of the family f.

\begin{code}

 d₀-is-fp : (i : I) → f i d₀ ＝ d₀
 d₀-is-fp i = ap ι (e₀-is-fp i)

 fp-induction : (S : D → Ω 𝓤) → S ∈ C → d₀ ∈ S
 fp-induction = from-⋂ C d₀ (τ e₀)

\end{code}

d₀ is the least common pre-fixed point of the family f.

\begin{code}

 d₀-is-lpfp : (x : D) → ((i : I) → f i x ⊑ x) → d₀ ⊑ x
 d₀-is-lpfp x le = fp-induction S S-in-C
  where
   S : D → Ω 𝓤
   S = λ (d : D) → (d ⊑ x , prop-valuedness 𝓓 d x)

   S-in-C : S ∈ C
   S-in-C =
    (λ α δ α-in-S → ∐-is-lowerbound-of-upperbounds 𝓓 δ x α-in-S) ,
    ⊥-is-least x ,
    (λ i d d-in-S → f i d ⊑⟨ 𝓓 ⟩[ fm i d x d-in-S ]
                    f i x ⊑⟨ 𝓓 ⟩[ le i ]
                    x     ∎⟨ 𝓓 ⟩)

\end{code}

And so it is the least common fixed point.

\begin{code}

 d₀-is-lfp : (x : D) → ((i : I) → f i x ＝ x) → d₀ ⊑ x
 d₀-is-lfp x e = d₀-is-lpfp x (λ i → ＝-to-⊑ 𝓓 (e i))

\end{code}

This concludes the proof of Theorem 2·2, which has the following
corollary.

\begin{code}

module corollary₂·₁
        (ρ : Propositional-Resizing)
        (𝓒 : DCPO {𝓤} {𝓤})
        ((⊥ , ⊥-is-least) : has-bottom 𝓒)
        (f : ⟨ 𝓒 ⟩ → ⟨ 𝓒 ⟩)
        (fm : is-monotone 𝓒 𝓒 f)
       where

 𝓓 : DCPO
 𝓓 = subdcpo 𝓒
      (λ x → x ⊑⟨ 𝓒 ⟩ f x)
      (λ x → prop-valuedness 𝓒 x (f x))
      (λ {I} α δ le →
        ∐-is-lowerbound-of-upperbounds 𝓒 δ
         (f (∐ 𝓒 δ))
         (λ i → α i       ⊑⟨ 𝓒 ⟩[ le i ]
                f (α i)   ⊑⟨ 𝓒 ⟩[ fm (α i) (∐ 𝓒 δ) (∐-is-upperbound 𝓒 δ i) ]
                f (∐ 𝓒 δ) ∎⟨ 𝓒 ⟩))

 𝓯 : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩
 𝓯 (x , le) = f x , fm x (f x) le

 𝓯-is-monotone : (s t : ⟨ 𝓓 ⟩) → s ⊑⟨ 𝓓 ⟩ t → 𝓯 s ⊑⟨ 𝓓 ⟩ 𝓯 t
 𝓯-is-monotone (x , _) (y , _) = fm x y

 𝓯-is-inflationary : (t : ⟨ 𝓓 ⟩) → t ⊑⟨ 𝓓 ⟩ 𝓯 t
 𝓯-is-inflationary (x , c) = c

 𝓓-has-bottom : has-bottom 𝓓
 𝓓-has-bottom = (⊥ , ⊥-is-least (f ⊥)) , (λ (x , _) → ⊥-is-least x)

 open theorem₂·₂ ρ 𝓓 𝓓-has-bottom 𝟙
       (λ _ → 𝓯)
       (λ _ → 𝓯-is-monotone)
       (λ _ → 𝓯-is-inflationary)

 ι : ⟨ 𝓓 ⟩ → ⟨ 𝓒 ⟩
 ι (x , le) = x

 τ : (d : ⟨ 𝓓 ⟩) → d ⊑⟨ 𝓓 ⟩ 𝓯 d
 τ (x , le) = le

 c₀ : ⟨ 𝓒 ⟩
 c₀ = ι d₀

 c₀-is-fp : f c₀ ＝ c₀
 c₀-is-fp = ap ι (d₀-is-fp ⋆)

 c₀-is-lfp : (c : ⟨ 𝓒 ⟩) → f c ＝ c → c₀ ⊑⟨ 𝓒 ⟩ c
 c₀-is-lfp c e = d₀-is-lfp
                  (c , ＝-to-⊑ 𝓒 (e ⁻¹))
                  (λ _ → to-subtype-＝ (λ x → prop-valuedness 𝓒 x (f x)) e)
\end{code}

This concludes the proof of Corollary 2·1, which we repackage as
follows.

\begin{code}

Pataraia : Propositional-Resizing
         → (𝓒 : DCPO {𝓤} {𝓤})
         → has-bottom 𝓒
         → (f : ⟨ 𝓒 ⟩ → ⟨ 𝓒 ⟩)
         → is-monotone 𝓒 𝓒 f
         → Σ c₀ ꞉ ⟨ 𝓒 ⟩
                , (f c₀ ＝ c₀)
                × ((c : ⟨ 𝓒 ⟩) → f c ＝ c → c₀ ⊑⟨ 𝓒 ⟩ c)
Pataraia ρ 𝓒 hb f fm = c₀ , c₀-is-fp , c₀-is-lfp
 where
  open corollary₂·₁ ρ 𝓒 hb f fm

\end{code}

See the module Various.Pataraia-Taylor for a proof that doesn't assume
propositional resizing.
