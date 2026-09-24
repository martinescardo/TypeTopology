Martin Escardo 2012.

Based on [1] and [2].

1. Nicolai Kraus, Martín Escardó, Thierry Coquand & Thorsten Altenkirch.
   Generalizations of Hedberg’s Theorem.
   TLCA 2013
   https://doi.org/10.1007/978-3-642-38946-7_14

2. Nicolai Kraus, Martín Escardó, Thierry Coquand & Thorsten Altenkirch.
   Notions of Anonymous Existence in Martin-Löf Type Theory.
   Logical Methods in Computer Science, March 24, 2017, Volume 13, Issue 1.
   https://doi.org/10.23638/LMCS-13(1:15)2017

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.ExitPropTrunc where

open import MLTT.Spartan
open import UF.Hedberg
open import UF.KrausLemma
open import UF.PropTrunc
open import UF.Subsingletons

to-fix : {X : 𝓤 ̇ } (f : X → X) → wconstant f → X → fix f
to-fix f g x = (f x , g x (f x))

from-to-fix : {X : 𝓤 ̇ } (f : X → X) (κ : wconstant f)
            → from-fix f ∘ to-fix f κ ∼ f
from-to-fix f κ w = refl

to-from-fix : {X : 𝓤 ̇ } (f : X → X) (κ : wconstant f)
            → to-fix f κ ∘ from-fix f ∼ id
to-from-fix f κ _ = fix-is-prop f κ _ _

has-split-support' : 𝓤 ̇ → 𝓤 ⁺ ̇
has-split-support' {𝓤} X = Σ P ꞉ 𝓤 ̇ , is-prop P × (X ↔ P)

fix-has-split-support' : {X : 𝓤 ̇ }
                       → collapsible X
                       → has-split-support' X
fix-has-split-support' {𝓤} {X} (f , κ) =
 fix f , fix-is-prop f κ , to-fix f κ , from-fix f

has-prop-truncation : (𝓥 : Universe) → 𝓤 ̇ → (𝓤 ⊔ 𝓥)⁺ ̇
has-prop-truncation {𝓤} 𝓥 X =
 Σ X' ꞉ 𝓤 ̇ , is-prop X'
           × (X → X')
           × ((P : 𝓥 ̇ ) → is-prop P → (X → P) → X' → P)

split-truncation : {X : 𝓤 ̇ }
                 → has-split-support' X
                 → ∀ 𝓥 → has-prop-truncation 𝓥 X
split-truncation {𝓤} {X} (X' , i , f , g) V = X' , i , f , λ P j h x' → h (g x')

collapsible-has-prop-truncation : {X : 𝓤 ̇ }
                                → collapsible X
                                → ∀ 𝓥 → has-prop-truncation 𝓥 X
collapsible-has-prop-truncation {𝓤} {X} c =
 split-truncation (fix-has-split-support' c)

module split-support-and-collapsibility (pe : propositional-truncations-exist) where

 open PropositionalTruncation pe

 has-split-support : 𝓤 ̇ → 𝓤 ̇
 has-split-support X = ∥ X ∥ → X

 has-split-support→ : {X : 𝓤 ̇ } → has-split-support X → has-split-support' X
 has-split-support→ {𝓤} {X} f = ∥ X ∥ , ∥∥-is-prop , (λ x → ∣ x ∣) , f

 has-split-support← : {X : 𝓤 ̇ } → has-split-support' X → has-split-support X
 has-split-support← {𝓤} {X} (P , P-is-prop , g , f) = f ∘ ∥∥-rec P-is-prop g

\end{code}

TODO. Are the above two functions mutually inverse and hence we get an
equivalence?

\begin{code}

 collapsible-gives-split-support : {X : 𝓤 ̇ }
                                 → collapsible X
                                 → has-split-support X
 collapsible-gives-split-support {𝓤} {X} (f , κ) s = x
  where
   g : ∥ X ∥ → fix f
   g = ∥∥-rec (fix-is-prop f κ) (to-fix f κ)

   x : X
   x = from-fix f (g s)

 exit-prop-trunc : {X : 𝓤 ̇ }
                 → (f : X → X)
                 → wconstant f
                 → ∥ X ∥ → X
 exit-prop-trunc f κ = collapsible-gives-split-support (f , κ)

 exit-prop-trunc-is-fixed : {X : 𝓤 ̇ }
                            (f : X → X)
                            (κ : wconstant f)
                            (s : ∥ X ∥)
                          → f (exit-prop-trunc f κ s) ＝ exit-prop-trunc f κ s
 exit-prop-trunc-is-fixed f κ s =
  (from-fix-is-fixed f (∥∥-rec (fix-is-prop f κ) (to-fix f κ) s))⁻¹

 split-support-gives-collapsible : {X : 𝓤 ̇ }
                                 → has-split-support X
                                 → collapsible X
 split-support-gives-collapsible {𝓤} {X} g = γ
  where
   f : X → X
   f x = g ∣ x ∣

   κ : (x y : X) → f x ＝ f y
   κ x y = ap g (∥∥-is-prop ∣ x ∣ ∣ y ∣)

   γ : collapsible X
   γ = f , κ

\end{code}

Added 23rd September 2024. Perhaps the following is better notation
for the above.

\begin{code}

∥_∥⌜_⌝ : (X : 𝓤 ̇ ) → collapsible X → 𝓤 ̇
∥ X ∥⌜ f , w ⌝ = fix f

∥∥⌜_⌝-is-prop : {X : 𝓤 ̇ } (c : collapsible X) → is-prop ∥ X ∥⌜ c ⌝
∥∥⌜ f , w ⌝-is-prop = fix-is-prop f w

∣_∣⌜_⌝ : {X : 𝓤 ̇ } → X → (c : collapsible X) → ∥ X ∥⌜ c ⌝
∣ x ∣⌜ f , w ⌝ = to-fix f w x

\end{code}

Notice that recursion principle doesn't require the family A to be
prop-valued, which allows us to exit truncations.

\begin{code}

∥∥⌜_⌝-rec : {X : 𝓤 ̇ } (c : collapsible X) {A : 𝓥 ̇ }
         → (X → A) → ∥ X ∥⌜ c ⌝ → A
∥∥⌜ c ⌝-rec {A} g (x , φ) = g x

∣∣⌜_⌝-exit : {X : 𝓤 ̇ } (c : collapsible X) → ∥ X ∥⌜ c ⌝ → X
∣∣⌜ c ⌝-exit = ∥∥⌜ c ⌝-rec id

module propositional-truncation-of-decidable-type
        (pt : propositional-truncations-exist)
       where

 open propositional-truncations-exist pt public

 module _ {X : 𝓤 ̇ } (c : collapsible X) where

  ∥∥⌜_⌝-to-∥∥ : ∥ X ∥⌜ c ⌝ → ∥ X ∥
  ∥∥⌜_⌝-to-∥∥ = ∥∥⌜ c ⌝-rec ∣_∣

  ∥∥-to-∥∥⌜_⌝ : ∥ X ∥ → ∥ X ∥⌜ c ⌝
  ∥∥-to-∥∥⌜_⌝ = ∥∥-rec (∥∥⌜ c ⌝-is-prop) ∣_∣⌜ c ⌝

  collapsible-types-have-split-support : ∥ X ∥ → X
  collapsible-types-have-split-support s = ∣∣⌜ c ⌝-exit (∥∥-to-∥∥⌜_⌝ s)

\end{code}

TODO. Perhaps rewrite all uses of this file to use the new notation,
and get rid of the original old notation.
