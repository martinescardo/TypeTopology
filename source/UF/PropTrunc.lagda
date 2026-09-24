Martin Escardo

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.PropTrunc where

open import MLTT.Plus-Properties
open import MLTT.Spartan
open import MLTT.Two-Properties
open import UF.Base
open import UF.Equiv
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

We use the existence of propositional truncations as an
assumption. The following type collects the data that constitutes this
assumption.

\begin{code}

record propositional-truncations-exist : 𝓤ω where
 field
  ∥_∥ : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇
  ∥∥-is-prop : {𝓤 : Universe} {X : 𝓤 ̇ } → is-prop ∥ X ∥
  ∣_∣ : {𝓤 : Universe} {X : 𝓤 ̇ } → X → ∥ X ∥
  ∥∥-rec : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {P : 𝓥 ̇ } → is-prop P → (X → P) → ∥ X ∥ → P

module PropositionalTruncation (pt : propositional-truncations-exist) where

 open propositional-truncations-exist pt public

 exit-∥∥ : {P : 𝓤 ̇ } → is-prop P → ∥ P ∥ → P
 exit-∥∥ i = ∥∥-rec i id

 ∥∥-induction : {X : 𝓤 ̇ } {P : ∥ X ∥ → 𝓥 ̇ }
             → ((s : ∥ X ∥) → is-prop (P s))
             → ((x : X) → P ∣ x ∣)
             → (s : ∥ X ∥) → P s
 ∥∥-induction {𝓤} {𝓥} {X} {P} i f s = φ' s
  where
   φ : X → P s
   φ x = transport P (∥∥-is-prop ∣ x ∣ s) (f x)
   φ' : ∥ X ∥ → P s
   φ' = ∥∥-rec (i s) φ

 is-singleton'-is-prop : {X : 𝓤 ̇ } → funext 𝓤 𝓤 → is-prop (is-prop X × ∥ X ∥)
 is-singleton'-is-prop fe = Σ-is-prop (being-prop-is-prop fe) (λ _ → ∥∥-is-prop)

 the-singletons-are-the-inhabited-propositions
  : {X : 𝓤 ̇ }
  → is-singleton X ↔ is-prop X × ∥ X ∥
 the-singletons-are-the-inhabited-propositions {𝓤} {X} = f , g
  where
   f : is-singleton X → is-prop X × ∥ X ∥
   f (x , φ) = singletons-are-props (x , φ) , ∣ x ∣

   g : is-prop X × ∥ X ∥ → is-singleton X
   g (i , s) = exit-∥∥ i s , i (exit-∥∥ i s)

 ∥∥-functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → ∥ X ∥ → ∥ Y ∥
 ∥∥-functor f = ∥∥-rec ∥∥-is-prop (λ x → ∣ f x ∣)

 ∥∥-rec₂ : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {P : 𝓦 ̇ }
         → is-prop P → (X → Y → P) → ∥ X ∥ → ∥ Y ∥ → P
 ∥∥-rec₂ i f s t = ∥∥-rec i (λ x → ∥∥-rec i (f x) t) s

 ∥∥-functor₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
             → (X → Y → Z) → ∥ X ∥ → ∥ Y ∥ → ∥ Z ∥
 ∥∥-functor₂ f s t = ∥∥-rec ∥∥-is-prop (λ x → ∥∥-functor (f x) t) s

 ∥∥-functor₃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {T : 𝓣 ̇ }
             → (X → Y → Z → T) → ∥ X ∥ → ∥ Y ∥ → ∥ Z ∥ → ∥ T ∥
 ∥∥-functor₃ f s t u = ∥∥-rec ∥∥-is-prop (λ x → ∥∥-functor₂ (f x) t u) s

 ∃ : {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
 ∃ Y = ∥ Σ Y ∥

 ∃-is-prop : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → is-prop (∃ Y)
 ∃-is-prop = ∥∥-is-prop

 Exists : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
 Exists X Y = ∃ Y

 ¬Exists : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
 ¬Exists X Y = ¬ (∃ Y)

 syntax Exists A (λ x → b) = ∃ x ꞉ A , b
 syntax ¬Exists A (λ x → b) = ¬∃ x ꞉ A , b

 infixr -1 Exists
 infixr -1 ¬Exists

 remove-truncation-inside-∃ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                            → (∃ x ꞉ X , ∥ Y x ∥)
                            → (∃ x ꞉ X , Y x)
 remove-truncation-inside-∃ =
  ∥∥-rec ∃-is-prop
   (λ (x , s) → ∥∥-rec ∃-is-prop
                 (λ y → ∣ x , y ∣) s)

 Nat∃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ } → Nat A B → ∃ A → ∃ B
 Nat∃ ζ = ∥∥-functor (NatΣ ζ)

 _∨_  : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
 P ∨ Q = ∥ P + Q ∥

 ∨-is-prop  : {P : 𝓤 ̇ } {Q : 𝓥 ̇ } → is-prop (P ∨ Q)
 ∨-is-prop = ∥∥-is-prop

 ∨-elim : {P : 𝓤 ̇ } {Q : 𝓥 ̇ } {R : 𝓦 ̇ }
        → is-prop R
        → (P → R)
        → (Q → R)
        → P ∨ Q → R
 ∨-elim i f g = ∥∥-rec i (cases f g)

 ∨-functor : {P : 𝓤 ̇ } {Q : 𝓥 ̇ } {R : 𝓦 ̇ } {S : 𝓣 ̇ }
           → (P → R)
           → (Q → S)
           → P ∨ Q → R ∨ S
 ∨-functor f g = ∥∥-functor (+functor f g)

 ∨-flip : {P : 𝓤 ̇ } {Q : 𝓥 ̇ }
        → P ∨ Q → Q ∨ P
 ∨-flip = ∥∥-functor (cases inr inl)

 left-fails-gives-right-holds : {P : 𝓤 ̇ } {Q : 𝓥 ̇ }
                              → is-prop Q
                              → P ∨ Q
                              → ¬ P
                              → Q
 left-fails-gives-right-holds i d u =
  ∥∥-rec i (λ d → Left-fails-gives-right-holds d u) d

 right-fails-gives-left-holds : {P : 𝓤 ̇ } {Q : 𝓥 ̇ }
                              → is-prop P
                              → P ∨ Q
                              → ¬ Q → P
 right-fails-gives-left-holds i d u =
  ∥∥-rec i (λ d → Right-fails-gives-left-holds d u) d

 pt-gdn : {X : 𝓤 ̇ } → ∥ X ∥ → ∀ {𝓥} (P : 𝓥 ̇ ) → is-prop P → (X → P) → P
 pt-gdn {𝓤} {X} s {𝓥} P isp u = ∥∥-rec isp u s

 gdn-pt : {X : 𝓤 ̇ } → (∀ {𝓥} (P : 𝓥 ̇ ) → is-prop P → (X → P) → P) → ∥ X ∥
 gdn-pt {𝓤} {X} φ = φ ∥ X ∥ ∥∥-is-prop ∣_∣

 inhabited-is-nonempty : {X : 𝓤 ̇ } → ∥ X ∥ → ¬¬ X
 inhabited-is-nonempty s = pt-gdn s 𝟘 𝟘-is-prop

 uninhabited-is-empty : {X : 𝓤 ̇ } → ¬ ∥ X ∥ → ¬ X
 uninhabited-is-empty u x = u ∣ x ∣

 empty-is-uninhabited : {X : 𝓤 ̇ } → ¬ X → ¬ ∥ X ∥
 empty-is-uninhabited v = ∥∥-rec 𝟘-is-prop v

 binary-choice : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → ∥ X ∥ → ∥ Y ∥ → ∥ X × Y ∥
 binary-choice s t = ∥∥-rec
                      ∥∥-is-prop
                      (λ x → ∥∥-rec ∥∥-is-prop (λ y → ∣ x , y ∣) t)
                      s

 prop-is-equivalent-to-its-truncation : {X : 𝓤 ̇ } → is-prop X → ∥ X ∥ ≃ X
 prop-is-equivalent-to-its-truncation i =
  logically-equivalent-props-are-equivalent ∥∥-is-prop i (exit-∥∥ i) ∣_∣

 equiv-to-own-truncation-implies-prop : {X : 𝓤 ̇ } → X ≃ ∥ X ∥  → is-prop X
 equiv-to-own-truncation-implies-prop {𝓤} {X} e = equiv-to-prop e ∥∥-is-prop

 not-exists₀-implies-forall₁ : {X : 𝓤 ̇ } (p : X → 𝟚)
                             → ¬ (∃ x ꞉ X , p x ＝ ₀)
                             → ∀ (x : X) → p x ＝ ₁
 not-exists₀-implies-forall₁ p u x =
  different-from-₀-equal-₁ (not-Σ-implies-Π-not (u ∘ ∣_∣) x)

 forall₁-implies-not-exists₀ : {X : 𝓤 ̇ } (p : X → 𝟚)
                             → (∀ (x : X) → p x ＝ ₁)
                             → ¬ (∃ x ꞉ X , p x ＝ ₀)
 forall₁-implies-not-exists₀ {𝓤} {X} p α = ∥∥-rec 𝟘-is-prop h
  where
   h : (Σ x ꞉ X , p x ＝ ₀) → 𝟘
   h (x , r) = zero-is-not-one (r ⁻¹ ∙ α x)

 forall₀-implies-not-exists₁ : {X : 𝓤 ̇ } (p : X → 𝟚)
                             → (∀ (x : X) → p x ＝ ₀)
                             → ¬ (∃ x ꞉ X , p x ＝ ₁)
 forall₀-implies-not-exists₁ {𝓤} {X} p α = ∥∥-rec 𝟘-is-prop h
  where
   h : (Σ x ꞉ X , p x ＝ ₁) → 𝟘
   h (x , r) = one-is-not-zero (r ⁻¹ ∙ α x)

\end{code}

Added 19/12/2019 by Tom de Jong.

The following allows us to use Agda's do-notation with the ∥∥-monad.

Note that the Kleisli laws hold trivially, because ∥ X ∥ is a proposition for
any type X.

It is quite convenient when dealing with multiple, successive ∥∥-rec calls.

Agda's do-notation is powerful, because it can be combined with pattern
matching, i.e. if
  w ꞉ ∥ fiber f y ∥,
then
  x , p ← w
is allowed in the do-block.

(Note that in Haskell, you would write "return" for our function ∣_∣.)

\begin{code}

 _>>=_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → ∥ X ∥ → (X → ∥ Y ∥) → ∥ Y ∥
 s >>= f = ∥∥-rec ∥∥-is-prop f s

\end{code}

\begin{code}

 infixr 0 _∨_

\end{code}
