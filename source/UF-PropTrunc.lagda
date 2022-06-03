Martin Escardo

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module UF-PropTrunc where

open import SpartanMLTT

open import Plus-Properties
open import UF-Base
open import UF-Subsingletons
open import UF-FunExt
open import UF-Subsingletons-FunExt
open import UF-Equiv

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
 infix 0 ∥_∥
 infix 0 ∣_∣

module PropositionalTruncation (pt : propositional-truncations-exist) where

 open propositional-truncations-exist pt public

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

 the-singletons-are-the-inhabited-propositions : {X : 𝓤 ̇ } → is-singleton X ⇔ is-prop X × ∥ X ∥
 the-singletons-are-the-inhabited-propositions {𝓤} {X} = f , g
  where
   f : is-singleton X → is-prop X × ∥ X ∥
   f (x , φ) = singletons-are-props (x , φ) , ∣ x ∣

   g : is-prop X × ∥ X ∥ → is-singleton X
   g (i , s) = ∥∥-rec i id s , i (∥∥-rec i id s)

 ∥∥-functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → ∥ X ∥ → ∥ Y ∥
 ∥∥-functor f = ∥∥-rec ∥∥-is-prop (λ x → ∣ f x ∣)

 ∥∥-rec₂ : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {P : 𝓦 ̇ }
         → is-prop P → (X → Y → P) → ∥ X ∥ → ∥ Y ∥ → P
 ∥∥-rec₂ i f s t = ∥∥-rec i (λ x → ∥∥-rec i (f x) t) s

 ∥∥-functor₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
             → (X → Y → Z) → ∥ X ∥ → ∥ Y ∥ → ∥ Z ∥
 ∥∥-functor₂ f s t = ∥∥-rec ∥∥-is-prop (λ x → ∥∥-functor (f x) t) s

 ∃ : {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
 ∃ Y = ∥ Σ Y ∥

 ∃-is-prop : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → is-prop (∃ Y)
 ∃-is-prop = ∥∥-is-prop

 Exists : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
 Exists X Y = ∃ Y

 syntax Exists A (λ x → b) = ∃ x ꞉ A , b

 infixr -1 Exists

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

 left-fails-gives-right-holds : {P : 𝓤 ̇ } {Q : 𝓥 ̇ } → is-prop Q → P ∨ Q → ¬ P → Q
 left-fails-gives-right-holds i d u = ∥∥-rec i (λ d → Left-fails-gives-right-holds d u) d

 right-fails-gives-left-holds : {P : 𝓤 ̇ } {Q : 𝓥 ̇ } → is-prop P → P ∨ Q → ¬ Q → P
 right-fails-gives-left-holds i d u = ∥∥-rec i (λ d → Right-fails-gives-left-holds d u) d

 pt-gdn : {X : 𝓤 ̇ } → ∥ X ∥ → ∀ {𝓥} (P : 𝓥 ̇ ) → is-prop P → (X → P) → P
 pt-gdn {𝓤} {X} s {𝓥} P isp u = ∥∥-rec isp u s

 gdn-pt : {X : 𝓤 ̇ } → (∀ {𝓥} (P : 𝓥 ̇ ) → is-prop P → (X → P) → P) → ∥ X ∥
 gdn-pt {𝓤} {X} φ = φ ∥ X ∥ ∥∥-is-prop ∣_∣

 is-inhabited : {X : 𝓤 ̇ } → (X → Ω 𝓥) → 𝓤 ⊔ 𝓥 ̇
 is-inhabited {𝓤} {𝓥} {X} A = ∃ x ꞉ X , A x holds

 being-inhabited-is-prop : {X : 𝓤 ̇ } (A : X → Ω 𝓥) → is-prop (is-inhabited A)
 being-inhabited-is-prop {𝓤} {𝓥} {X} A = ∃-is-prop

 inhabited-is-nonempty : {X : 𝓤 ̇ } → ∥ X ∥ → ¬¬ X
 inhabited-is-nonempty s = pt-gdn s 𝟘 𝟘-is-prop

 uninhabited-is-empty : {X : 𝓤 ̇ } → ¬ ∥ X ∥ → ¬ X
 uninhabited-is-empty u x = u ∣ x ∣

 empty-is-uninhabited : {X : 𝓤 ̇ } → ¬ X → ¬ ∥ X ∥
 empty-is-uninhabited v = ∥∥-rec 𝟘-is-prop v

 binary-choice : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → ∥ X ∥ → ∥ Y ∥ → ∥ X × Y ∥
 binary-choice s t = ∥∥-rec ∥∥-is-prop (λ x → ∥∥-rec ∥∥-is-prop (λ y → ∣ x , y ∣) t) s

 prop-is-equivalent-to-its-truncation : {X : 𝓤 ̇ } → is-prop X → ∥ X ∥ ≃ X
 prop-is-equivalent-to-its-truncation i =
  logically-equivalent-props-are-equivalent ∥∥-is-prop i (∥∥-rec i id) ∣_∣

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
