Ian Ray, 2 June 2024

Modification by Martin Escardo and Tom de Jong 12th September 2024.

Minor modifications by Tom de Jong on 4 September 2024

We develop n-types, or n-truncated types, as defined in the HoTT book.

In this file we will assume function extensionality globally but not
univalence.  The final result of the file will be proved in the local
presence of univalence.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module UF.TruncatedTypes
        (fe : Fun-Ext)
       where

open import MLTT.Spartan hiding (_+_)

open import Naturals.Order
open import Notation.Order
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Retracts
open import UF.Singleton-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.TruncationLevels
open import UF.Univalence

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

_is_truncated : 𝓤 ̇ → ℕ₋₂ → 𝓤 ̇
X is −2 truncated       = is-contr X
X is (succ n) truncated = (x x' : X) → (x ＝ x') is n truncated

_is_truncated-map : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (f : X → Y) → ℕ₋₂ → 𝓤 ⊔ 𝓥 ̇
f is n truncated-map = each-fiber-of f (λ - → - is n truncated)

being-truncated-is-prop : {n : ℕ₋₂} {X : 𝓤 ̇ }
                        → is-prop (X is n truncated)
being-truncated-is-prop {_} {−2} = being-singleton-is-prop fe
being-truncated-is-prop {_} {succ n} =
 Π₂-is-prop fe (λ x x' → being-truncated-is-prop)

being-truncated-map-is-prop : {n : ℕ₋₂} {X : 𝓤 ̇ } {Y : 𝓥 ̇} {f : X → Y}
                            → is-prop (f is n truncated-map)
being-truncated-map-is-prop = Π-is-prop fe (λ y → being-truncated-is-prop)

\end{code}

Being -1-truncated is equivalent to being a proposition.

\begin{code}

is-prop' : (X : 𝓤 ̇) → 𝓤  ̇
is-prop' X = X is −1 truncated

being-prop'-is-prop : (X : 𝓤 ̇) → is-prop (is-prop' X)
being-prop'-is-prop X = being-truncated-is-prop

is-prop-implies-is-prop' : {X : 𝓤 ̇} → is-prop X → is-prop' X
is-prop-implies-is-prop' X-is-prop x x' =
 pointed-props-are-singletons (X-is-prop x x') (props-are-sets X-is-prop)

is-prop'-implies-is-prop : {X : 𝓤 ̇} → is-prop' X → is-prop X
is-prop'-implies-is-prop X-is-prop' x x' = center (X-is-prop' x x')

is-prop-equiv-is-prop' : {X : 𝓤 ̇} → is-prop X ≃ is-prop' X
is-prop-equiv-is-prop' {𝓤} {X} =
 logically-equivalent-props-are-equivalent (being-prop-is-prop fe)
                                           (being-prop'-is-prop X)
                                           is-prop-implies-is-prop'
                                           is-prop'-implies-is-prop

\end{code}

Truncation levels are upper closed.

\begin{code}

contractible-types-are-props' : {X : 𝓤 ̇} → is-contr X → is-prop' X
contractible-types-are-props' = is-prop-implies-is-prop' ∘ singletons-are-props

truncation-levels-are-upper-closed : {n : ℕ₋₂} {X : 𝓤 ̇ }
                                   → X is n truncated
                                   → X is (n + 1) truncated
truncation-levels-are-upper-closed {𝓤} {−2} = contractible-types-are-props'
truncation-levels-are-upper-closed {𝓤} {succ n} t x x' =
 truncation-levels-are-upper-closed (t x x')

truncation-levels-are-upper-closed-+ : {n : ℕ₋₂} {l : ℕ} {X : 𝓤 ̇ }
                                    → X is n truncated
                                    → X is n + l truncated
truncation-levels-are-upper-closed-+ {_} {n} {zero} {X} X-n-trunc = X-n-trunc
truncation-levels-are-upper-closed-+ {_} {n} {succ l} {X} X-n-trunc =
 truncation-levels-are-upper-closed
  (truncation-levels-are-upper-closed-+ X-n-trunc)

truncation-levels-are-upper-closed' : {n n' : ℕ₋₂} {X : 𝓤 ̇ }
                                    → n ≤ n'
                                    → X is n truncated
                                    → X is n' truncated
truncation-levels-are-upper-closed' {_} {n} {n'} {X} o X-n-trunc =
 transport (λ - → X is - truncated) p
           (truncation-levels-are-upper-closed-+ X-n-trunc) 
 where
  m : ℕ
  m = subtraction-ℕ₋₂-term n n' o
  p = n + m   ＝⟨ subtraction-ℕ₋₂-identification n n' o ⟩
      n'      ∎ 

truncation-levels-closed-under-Id : {n : ℕ₋₂} {X : 𝓤 ̇ }
                                  → X is n truncated
                                  → (x x' : X) → (x ＝ x') is n truncated
truncation-levels-closed-under-Id {𝓤} {−2} = contractible-types-are-props'
truncation-levels-closed-under-Id {𝓤} {succ n} t x x' =
 truncation-levels-are-upper-closed (t x x')

\end{code}

We will now give some closure results about truncation levels.

\begin{code}

truncated-types-are-closed-under-retracts : {n : ℕ₋₂} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                          → retract X of Y
                                          → Y is n truncated
                                          → X is n truncated
truncated-types-are-closed-under-retracts {𝓤} {𝓥} {−2} {X} {Y} =
 singleton-closed-under-retract X Y
truncated-types-are-closed-under-retracts {𝓤} {𝓥} {succ n} (r , s , H) t x x' =
 truncated-types-are-closed-under-retracts
  (＝-retract s (r , H) x x')
  (t (s x) (s x'))

truncated-types-closed-under-equiv : {n : ℕ₋₂} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                   → X ≃ Y
                                   → Y is n truncated
                                   → X is n truncated
truncated-types-closed-under-equiv e =
 truncated-types-are-closed-under-retracts (≃-gives-◁ e)

\end{code}

We can prove closure under embeddings as a consequence of the previous
result.

\begin{code}

truncated-types-closed-under-embedding⁺ : {n : ℕ₋₂} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                        → X ↪ Y
                                        → Y is (n + 1) truncated
                                        → X is (n + 1) truncated
truncated-types-closed-under-embedding⁺ {𝓤} {𝓥} (e , is-emb) t x x' =
 truncated-types-closed-under-equiv
  (ap e , embedding-gives-embedding' e is-emb x x')
  (t (e x) (e x'))

truncated-types-closed-under-embedding : {n : ℕ₋₂}
                                       → n ≥ −1
                                       → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                       → X ↪ Y
                                       → Y is n truncated
                                       → X is n truncated
truncated-types-closed-under-embedding {𝓤} {𝓥} {succ n} _ =
 truncated-types-closed-under-embedding⁺

\end{code}

Using closure under equivalence we can show closure under Σ and Π.

\begin{code}

truncated-types-closed-under-Σ : {n : ℕ₋₂} {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ )
                               → X is n truncated
                               → ((x : X) → (Y x) is n truncated)
                               → (Σ Y) is n truncated
truncated-types-closed-under-Σ {𝓤} {𝓥} {−2} Y = Σ-is-singleton
truncated-types-closed-under-Σ {𝓤} {𝓥} {succ n} Y l m (x , y) (x' , y') =
 truncated-types-closed-under-equiv Σ-＝-≃
  (truncated-types-closed-under-Σ
   (λ p → transport Y p y ＝ y')
   (l x x')
   (λ p → m x' (transport Y p y) y'))

truncated-types-closed-under-Π : {n : ℕ₋₂} {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ )
                               → ((x : X) → (Y x) is n truncated)
                               → (Π Y) is n truncated
truncated-types-closed-under-Π {𝓤} {𝓥} {−2} Y = Π-is-singleton fe
truncated-types-closed-under-Π {𝓤} {𝓥} {succ n} Y m f g =
 truncated-types-closed-under-equiv (happly-≃ fe)
  (truncated-types-closed-under-Π (λ x → f x ＝ g x)
  (λ x → m x (f x) (g x)))

truncated-types-closed-under-→ : {n : ℕ₋₂} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                               → Y is n truncated
                               → (X → Y) is n truncated
truncated-types-closed-under-→ {𝓤} {𝓥} {n} {X} {Y} m =
 truncated-types-closed-under-Π (λ - → Y) (λ - → m)

\end{code}

The subuniverse of types of n truncated types is defined as follows.

\begin{code}

𝕋 : ℕ₋₂ → (𝓤 : Universe) → 𝓤 ⁺ ̇
𝕋 n 𝓤 = Σ X ꞉ 𝓤 ̇ , X is n truncated

\end{code}

From univalence we can show that 𝕋 n is n + 1 truncated,
for all n : ℕ₋₂.

\begin{code}

truncation-levels-closed-under-≃⁺ : {n : ℕ₋₂} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                  → Y is (n + 1) truncated
                                  → (X ≃ Y) is (n + 1) truncated
truncation-levels-closed-under-≃⁺ {𝓤} {𝓥} {n} {X} {Y} tY =
 truncated-types-closed-under-embedding ⋆ (equiv-embeds-into-function fe')
  (truncated-types-closed-under-Π (λ _ → Y) (λ _ → tY))

truncation-levels-closed-under-≃ : {n : ℕ₋₂} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                 → X is n truncated
                                 → Y is n truncated
                                 → (X ≃ Y) is n truncated
truncation-levels-closed-under-≃ {𝓤} {𝓥} {−2} = ≃-is-singleton fe'
truncation-levels-closed-under-≃ {𝓤} {𝓥} {succ n} tX =
 truncation-levels-closed-under-≃⁺

𝕋-is-of-next-truncation-level : {n : ℕ₋₂} {𝓤 : Universe}
                              → is-univalent 𝓤
                              → (𝕋 n 𝓤) is (n + 1) truncated
𝕋-is-of-next-truncation-level ua (X , l) (Y , l') =
 truncated-types-closed-under-equiv I (truncation-levels-closed-under-≃ l l')
 where
  I = ((X , l) ＝ (Y , l')) ≃⟨ II ⟩
       (X ＝ Y)             ≃⟨ univalence-≃ ua X Y ⟩
       (X ≃ Y)              ■
   where
    II = ≃-sym (to-subtype-＝-≃ (λ _ → being-truncated-is-prop))

\end{code}
