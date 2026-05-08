Martin Escardo, January 2018

Two weak notions of compactness: ∃-compactness and Π-compactness. See
the module CompactTypes for the strong notion.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

open import CoNaturals.Type
open import MLTT.Two-Properties
open import Notation.Order
open import Taboos.WLPO
open import TypeTopology.CompactTypes
open import TypeTopology.DisconnectedTypes
open import TypeTopology.TotallySeparated
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Retracts
open import UF.Retracts-FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module TypeTopology.WeaklyCompactTypes
        (fe : FunExt)
        (pt : propositional-truncations-exist)
       where

private
 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open PropositionalTruncation pt
open import NotionsOfDecidability.Complemented

is-∃-compact : 𝓤 ̇ → 𝓤 ̇
is-∃-compact X = (p : X → 𝟚) → is-decidable (∃ x ꞉ X , p x ＝ ₀)

∃-compactness-is-prop : {X : 𝓤 ̇ } → is-prop (is-∃-compact X)
∃-compactness-is-prop {𝓤} {X} = Π-is-prop fe'
                                  (λ _ → decidability-of-prop-is-prop fe'
                                          ∃-is-prop)

∃-compactness-gives-Markov : {X : 𝓤 ̇ }
                           → is-∃-compact X
                           → (p : X → 𝟚)
                           → ¬¬ (∃ x ꞉ X , p x ＝ ₀)
                           → ∃ x ꞉ X , p x ＝ ₀
∃-compactness-gives-Markov {𝓤} {X} c p φ = g (c p)
 where
  g : is-decidable (∃ x ꞉ X , p x ＝ ₀) → ∃ x ꞉ X , p x ＝ ₀
  g (inl e) = e
  g (inr u) = 𝟘-elim (φ u)

\end{code}

The relation of ∃-compactness with compactness is the same as that of
LPO with WLPO.

\begin{code}

is-Π-compact : 𝓤 ̇ → 𝓤 ̇
is-Π-compact X = (p : X → 𝟚) → is-decidable ((x : X) → p x ＝ ₁)

Π-compactness-is-prop : {X : 𝓤 ̇ } → is-prop (is-Π-compact X)
Π-compactness-is-prop {𝓤} = Π-is-prop fe'
                              (λ _ → decidability-of-prop-is-prop fe'
                                       (Π-is-prop fe' (λ _ → 𝟚-is-set)))

∃-compact-types-are-Π-compact : {X : 𝓤 ̇ } → is-∃-compact X → is-Π-compact X
∃-compact-types-are-Π-compact {𝓤} {X} c p = f (c p)
 where
  f : is-decidable (∃ x ꞉ X , p x ＝ ₀) → is-decidable (Π x ꞉ X , p x ＝ ₁)
  f (inl s) = inr (λ α → ∥∥-rec 𝟘-is-prop (g α) s)
   where
    g : ((x : X) → p x ＝ ₁) → ¬ (Σ x ꞉ X , p x ＝ ₀)
    g α (x , r) = zero-is-not-one (r ⁻¹ ∙ α x)
  f (inr u) = inl (not-exists₀-implies-forall₁ p u)

empty-types-are-∃-compact : {X : 𝓤 ̇ } → is-empty X → is-∃-compact X
empty-types-are-∃-compact u p = inr (∥∥-rec 𝟘-is-prop λ σ → u (pr₁ σ))

empty-types-are-Π-compact : {X : 𝓤 ̇ } → is-empty X → is-Π-compact X
empty-types-are-Π-compact u p = inl (λ x → 𝟘-elim (u x))

\end{code}

The ∃-compactness, and hence Π-compactness, of compact sets (and hence
of ℕ∞, for example):

\begin{code}

compact-types-are-∃-compact : {X : 𝓤 ̇ } → is-compact X → is-∃-compact X
compact-types-are-∃-compact {𝓤} {X} φ p = g (φ p)
 where
  g : ((Σ x ꞉ X , p x ＝ ₀) + ((x : X) → p x ＝ ₁))
    → is-decidable (∃ x ꞉ X , p x ＝ ₀)
  g (inl (x , r)) = inl ∣ x , r ∣
  g (inr α)       = inr (forall₁-implies-not-exists₀ p α)

∥Compact∥-types-are-∃-compact : {X : 𝓤 ̇ } → ∥ is-Compact X ∥ → is-∃-compact X
∥Compact∥-types-are-∃-compact {𝓤} {X} =
 ∥∥-rec
  ∃-compactness-is-prop
  (compact-types-are-∃-compact ∘ Compact-types-are-compact)

\end{code}

But notice that the Π-compactness of ℕ is WLPO and its ∃-compactness
amounts to LPO.

The Π-compactness of X is equivalent to the isolatedness of the boolean
predicate λ x → ₁:

\begin{code}

is-Π-compact' : 𝓤 ̇ → 𝓤 ̇
is-Π-compact' X = is-isolated' (λ (x : X) → ₁)

being-Π-compact'-is-prop : {X : 𝓤 ̇ } → is-prop (is-Π-compact' X)
being-Π-compact'-is-prop {𝓤} = being-isolated'-is-prop fe (λ x → ₁)

Π-compact'-types-are-Π-compact : {X : 𝓤 ̇ } → is-Π-compact' X → is-Π-compact X
Π-compact'-types-are-Π-compact {𝓤} {X} c' p = g (c' p)
 where
  g : is-decidable (p ＝ λ x → ₁) → is-decidable ((x : X) → p x ＝ ₁)
  g (inl r) = inl (happly r)
  g (inr u) = inr (contrapositive (dfunext fe') u)

Π-compact-types-are-Π-compact' : {X : 𝓤 ̇ } → is-Π-compact X → is-Π-compact' X
Π-compact-types-are-Π-compact' {𝓤} {X} c p = g (c p)
 where
  g : is-decidable ((x : X) → p x ＝ ₁) → is-decidable (p ＝ λ x → ₁)
  g (inl α) = inl (dfunext fe' α)
  g (inr u) = inr (contrapositive happly u)

\end{code}

In classical topology, the Tychonoff Theorem gives that compact to the
power discrete is compact (where we read the function type X → Y as "Y
to the power X", with Y the base and X the exponent, and call it an
exponential). Here we don't have the Tychonoff Theorem (in the absence
of anti-classical intuitionistic assumptions).

It is less well-known that in classical topology we also have that
discrete to the power compact is discrete. This we do have here,
without the need of any assumption:

\begin{code}

Π-compact-indexed-product-of-discrete-types-is-discrete
 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
 → is-Π-compact X
 → ((x : X) → is-discrete (Y x))
 → is-discrete (Π Y)
Π-compact-indexed-product-of-discrete-types-is-discrete {𝓤} {𝓥} {X} {Y} c d f g
 = δ
 where
  p : X → 𝟚
  p = pr₁ (co-characteristic-function (λ x → d x (f x) (g x)))

  r : (x : X) → (p x ＝ ₀ → ¬ (f x ＝ g x)) × (p x ＝ ₁ → f x ＝ g x)
  r = pr₂ (co-characteristic-function λ x → d x (f x) (g x))

  φ : ((x : X) → p x ＝ ₁) → f ＝ g
  φ α = dfunext fe' (λ x → pr₂ (r x) (α x))

  γ : f ＝ g → (x : X) → p x ＝ ₁
  γ t x = different-from-₀-equal-₁ (λ u → pr₁ (r x) u (happly t x))

  h : is-decidable ((x : X) → p x ＝ ₁) → is-decidable (f ＝ g)
  h (inl α) = inl (φ α)
  h (inr u) = inr (contrapositive γ u)

  δ : is-decidable (f ＝ g)
  δ = h (c p)

discrete-to-power-Π-compact-is-discrete : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                        → is-Π-compact X
                                        → is-discrete Y
                                        → is-discrete (X → Y)
discrete-to-power-Π-compact-is-discrete {𝓤} {𝓥} {X} {Y} c d f g =
 Π-compact-indexed-product-of-discrete-types-is-discrete c (λ _ → d) f g

\end{code}

If an exponential with discrete base is discrete, then its exponent is
compact, provided the base has at least two points.

First, to decide Π (p : X → 𝟚), p x ＝ 1, decide p ＝ λ x → ₁:

\begin{code}

power-of-two-discrete-gives-compact-exponent : {X : 𝓤 ̇ }
                                             → is-discrete (X → 𝟚)
                                             → is-Π-compact X
power-of-two-discrete-gives-compact-exponent d =
 Π-compact'-types-are-Π-compact (λ p → d p (λ x → ₁))

discrete-power-of-disconnected-gives-compact-exponent : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                                      → is-disconnected Y
                                                      → is-discrete (X → Y)
                                                      → is-Π-compact X
discrete-power-of-disconnected-gives-compact-exponent {𝓤} {𝓥} {X} {Y} ρ d = γ
 where
  a : retract (X → 𝟚) of (X → Y)
  a = retract-contravariance fe' ρ

  b : is-discrete (X → 𝟚)
  b = retract-is-discrete a d

  γ : is-Π-compact X
  γ = power-of-two-discrete-gives-compact-exponent b

discrete-power-of-non-trivial-discrete-gives-compact-exponent'
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → (Σ y₀ ꞉ Y , Σ y₁ ꞉ Y , y₀ ≠ y₁)
 → is-discrete Y
 → is-discrete (X → Y)
 → is-Π-compact X
discrete-power-of-non-trivial-discrete-gives-compact-exponent' w d
 = discrete-power-of-disconnected-gives-compact-exponent
    (discrete-types-with-two-different-points-are-disconnected w d)

\end{code}

So, in summary, if Y is a non-trivial discrete type, then X is
Π-compact iff (X → Y) is discrete.

Compactness of images:

\begin{code}

open import UF.ImageAndSurjection pt

codomain-of-surjection-is-∃-compact : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                    → is-surjection f
                                    → is-∃-compact X
                                    → is-∃-compact Y
codomain-of-surjection-is-∃-compact {𝓤} {𝓥} {X} {Y} f su c q = g (c (q ∘ f))
 where
  h : (Σ x ꞉ X , q (f x) ＝ ₀) → Σ y ꞉ Y , q y ＝ ₀
  h (x , r) = (f x , r)

  l : (y : Y) → q y ＝ ₀ → (Σ x ꞉ X , f x ＝ y) → Σ x ꞉ X , q (f x) ＝ ₀
  l y r (x , s) = (x , (ap q s ∙ r))

  k : (Σ y ꞉ Y , q y ＝ ₀) → ∃ x ꞉ X , q (f x) ＝ ₀
  k (y , r) = ∥∥-functor (l y r) (su y)

  g : is-decidable (∃ x ꞉ X , q (f x) ＝ ₀) → is-decidable (∃ y ꞉ Y , q y ＝ ₀)
  g (inl s) = inl (∥∥-functor h s)
  g (inr u) = inr (contrapositive (∥∥-rec ∥∥-is-prop k) u)

image-is-∃-compact : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                   → is-∃-compact X
                   → is-∃-compact (image f)
image-is-∃-compact f = codomain-of-surjection-is-∃-compact (corestriction f) (corestrictions-are-surjections f)

codomain-of-surjection-is-Π-compact : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                    → is-surjection f
                                    → is-Π-compact X
                                    → is-Π-compact Y
codomain-of-surjection-is-Π-compact {𝓤} {𝓥} {X} {Y} f su c q = g (c (q ∘ f))
 where
  g : is-decidable ((x : X) → q (f x) ＝ ₁) → is-decidable ((x : Y) → q x ＝ ₁)
  g (inl s) = inl (surjection-induction f su (λ y → q y ＝ ₁) (λ _ → 𝟚-is-set) s)
  g (inr u) = inr (contrapositive (λ φ x → φ (f x)) u)

retract-∃-compact : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  → retract Y of X
                  → is-∃-compact X
                  → is-∃-compact Y
retract-∃-compact (f , hass) = codomain-of-surjection-is-∃-compact f
                                (retractions-are-surjections f hass)

retract-is-∃-compact' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                      → ∥ retract Y of X ∥
                      → is-∃-compact X
                      → is-∃-compact Y
retract-is-∃-compact' t c = ∥∥-rec
                             ∃-compactness-is-prop
                              (λ r → retract-∃-compact r c) t

image-is-Π-compact : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                   → is-Π-compact X
                   → is-Π-compact (image f)
image-is-Π-compact f = codomain-of-surjection-is-Π-compact
                        (corestriction f)
                        (corestrictions-are-surjections f)

retract-is-Π-compact : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                     → retract Y of X
                     → is-Π-compact X
                     → is-Π-compact Y
retract-is-Π-compact (f , hass) = codomain-of-surjection-is-Π-compact f
                                   (retractions-are-surjections f hass)

retract-is-Π-compact' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                      → ∥ retract Y of X ∥
                      → is-Π-compact X
                      → is-Π-compact Y
retract-is-Π-compact' t c = ∥∥-rec
                             Π-compactness-is-prop
                             (λ r → retract-is-Π-compact r c) t

Π-compact-exponential-with-pointed-domain-has-Π-compact-codomain
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → X
 → is-Π-compact (X → Y)
 → is-Π-compact Y
Π-compact-exponential-with-pointed-domain-has-Π-compact-codomain x
 = retract-is-Π-compact (codomain-is-retract-of-function-space-with-pointed-domain x)

\end{code}

A main reason to consider the notion of total separatedness is that
the totally separated reflection 𝕋 X of X has the same supply of
boolean-valued predicates as X, and hence X is ∃-compact (respectively
Π-compact) iff 𝕋 X is, as we show now.

\begin{code}

module _ (X : 𝓤 ̇ ) where

 open totally-separated-reflection fe pt

 private
  EP : (p : X → 𝟚) → ∃! p' ꞉ (𝕋 X → 𝟚) , p' ∘ ηᵀ ＝ p
  EP = totally-separated-reflection 𝟚-is-totally-separated

  extension : (X → 𝟚) → (𝕋 X → 𝟚)
  extension p = ∃!-witness (EP p)

  extension-property : (p : X → 𝟚) (x : X) → extension p (ηᵀ x) ＝ p x
  extension-property p = happly (∃!-is-witness (EP p))

 ∃-compact-types-are-∃-compact-𝕋 : is-∃-compact X → is-∃-compact (𝕋 X)
 ∃-compact-types-are-∃-compact-𝕋 = codomain-of-surjection-is-∃-compact
                                    ηᵀ ηᵀ-is-surjection

 ∃-compact-𝕋-types-are-∃-compact : is-∃-compact (𝕋 X) → is-∃-compact X
 ∃-compact-𝕋-types-are-∃-compact c p = h (c (extension p))
  where
   f : (Σ x' ꞉ 𝕋 X , extension p x' ＝ ₀) → ∃ x ꞉ X , p x ＝ ₀
   f (x' , r) = ∥∥-functor f' (ηᵀ-is-surjection x')
    where
     f' : (Σ x ꞉ X , ηᵀ x ＝ x') → Σ x ꞉ X , p x ＝ ₀
     f' (x , s) = x , ((extension-property p x) ⁻¹ ∙ ap (extension p) s ∙ r)

   g : (Σ x ꞉ X , p x ＝ ₀)
     → Σ x' ꞉ 𝕋 X , extension p x' ＝ ₀
   g (x , r) = ηᵀ x , (extension-property p x ∙ r)

   h : is-decidable (∃ x' ꞉ 𝕋 X , extension p x' ＝ ₀)
     → is-decidable (∃ x ꞉ X , p x ＝ ₀)
   h (inl x) = inl (∥∥-rec ∥∥-is-prop f x)
   h (inr u) = inr (contrapositive (∥∥-functor g) u)

 Π-compact-types-are-Π-compact-𝕋 : is-Π-compact X → is-Π-compact (𝕋 X)
 Π-compact-types-are-Π-compact-𝕋 = codomain-of-surjection-is-Π-compact
                                    ηᵀ (ηᵀ-is-surjection)

 Π-compact-𝕋-types-are-Π-compact : is-Π-compact (𝕋 X) → is-Π-compact X
 Π-compact-𝕋-types-are-Π-compact c p = h (c (extension p))
  where
   f : ((x' : 𝕋 X) → extension p x' ＝ ₁) → ((x : X) → p x ＝ ₁)
   f α x = (extension-property p x)⁻¹ ∙ α (ηᵀ x)

   g : (α : (x : X) → p x ＝ ₁)
     → ((x' : 𝕋 X) → extension p x' ＝ ₁)
   g α = ηᵀ-induction (λ x' → extension p x' ＝ ₁) (λ _ → 𝟚-is-set) g'
     where
      g' : (x : X) → extension p (ηᵀ x) ＝ ₁
      g' x = extension-property p x ∙ α x

   h : is-decidable ((x' : 𝕋 X) → extension p x' ＝ ₁)
     → is-decidable ((x : X) → p x ＝ ₁)
   h (inl α) = inl (f α)
   h (inr u) = inr (contrapositive g u)

\end{code}

If X is totally separated, and (X → 𝟚) is compact, then X is
discrete. More generally, if 𝟚 is a retract of Y and (X → Y) is
compact, then X is discrete if it is totally separated. This is a new
result as far as I know. I didn't know it before 12th January 2018.

The following proof works as follows. For any given x,y:X, define
q:(X→𝟚)→𝟚 such that q(p)=1 ↔ p(x) = p(y), which is possible because 𝟚
has decidable equality (it is discrete). By the Π-compactness of X→𝟚,
the condition (p:X→𝟚) → q(p)=1 is decidable, which amounts to saying
that (p:X→𝟚) → p (x)=p (y) is decidable. But because X is totally
separated, the latter is equivalent to x=y, which shows that X is
discrete.

\begin{code}

tscd : {X : 𝓤 ̇ }
     → is-totally-separated X
     → is-Π-compact (X → 𝟚)
     → is-discrete X
tscd {𝓤} {X} ts c x y = g (a s)
 where
  q : (X → 𝟚) → 𝟚
  q = pr₁ (co-characteristic-function (λ p → 𝟚-is-discrete (p x) (p y)))

  r : (p : X → 𝟚) → (q p ＝ ₀ → p x ≠ p y) × (q p ＝ ₁ → p x ＝ p y)
  r = pr₂ (co-characteristic-function (λ p → 𝟚-is-discrete (p x) (p y)))

  s : is-decidable ((p : X → 𝟚) → q p ＝ ₁)
  s = c q

  b : (p : X → 𝟚) → p x ＝ p y → q p ＝ ₁
  b p u = different-from-₀-equal-₁ (λ v → pr₁ (r p) v u)

  a : is-decidable ((p : X → 𝟚) → q p ＝ ₁)
    → is-decidable ((p : X → 𝟚) → p x ＝ p y)
  a (inl f) = inl (λ p → pr₂ (r p) (f p))
  a (inr φ) = inr h
   where
    h : ¬ ((p : X → 𝟚) → p x ＝ p y)
    h α = φ (λ p → b p (α p))

  g : is-decidable ((p : X → 𝟚) → p x ＝ p y) → is-decidable (x ＝ y)
  g (inl α) = inl (ts α)
  g (inr u) = inr (contrapositive (λ e p → ap p e) u)

\end{code}

We are interested in the following two generalizations, which arise as
corollaries:

\begin{code}

tscd₀ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
      → is-totally-separated X
      → is-disconnected Y
      → is-Π-compact (X → Y)
      → is-discrete X
tscd₀ {𝓤} {𝓥} {X} {Y} ts r c =
 tscd ts (retract-is-Π-compact (retract-contravariance fe' r) c)

open totally-separated-reflection fe pt

tscd₁ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
      → is-disconnected Y
      → is-Π-compact (X → Y)
      → is-discrete (𝕋 X)
tscd₁ {𝓤} {𝓥} {X} {Y} r c = f
 where
  z : retract (X → 𝟚) of (X → Y)
  z = retract-contravariance fe' r

  a : (𝕋 X → 𝟚) ≃ (X → 𝟚)
  a = totally-separated-reflection'' 𝟚-is-totally-separated

  b : retract (𝕋 X → 𝟚) of (X → 𝟚)
  b = ≃-gives-◁ a

  d : retract (𝕋 X → 𝟚) of (X → Y)
  d = retracts-compose z b

  e : is-Π-compact (𝕋 X → 𝟚)
  e = retract-is-Π-compact d c

  f : is-discrete (𝕋 X)
  f = tscd 𝕋-is-totally-separated e

\end{code}

In topological models, Π-compactness is the same as topological
compactness in the presence of total separatedness, at least for some
spaces, including the Kleene-Kreisel spaces, which model the simple
types (see the module SimpleTypes). Hence, for example, the
topological space (ℕ∞→𝟚) is not Π-compact because it is countably
discrete, as it is a theorem of topology that discrete to the power
compact is again discrete, which is compact iff it is finite. This
argument is both classical and external. But here we have that the
type (ℕ∞→𝟚) is "not" Π-compact, internally and constructively.

\begin{code}

[ℕ∞→𝟚]-compact-implies-WLPO : is-Π-compact (ℕ∞ → 𝟚) → WLPO
[ℕ∞→𝟚]-compact-implies-WLPO c = ℕ∞-discrete-gives-WLPO
                                 (tscd (ℕ∞-is-totally-separated fe') c)

\end{code}

Closure of compactness under sums (and hence binary products):

\begin{code}

Π-compact-closed-under-Σ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                         → is-Π-compact X
                         → ((x : X) → is-Π-compact (Y x))
                         → is-Π-compact (Σ Y)
Π-compact-closed-under-Σ {𝓤} {𝓥} {X} {Y} c d p = g e
 where
  f : ∀ x → is-decidable (∀ y → p (x , y) ＝ ₁)
  f x = d x (λ y → p (x , y))

  q : X → 𝟚
  q = pr₁ (co-characteristic-function f)

  q₀ : (x : X) → q x ＝ ₀ → ¬ ((y : Y x) → p (x , y) ＝ ₁)
  q₀ x = pr₁ (pr₂ (co-characteristic-function f) x)

  q₁ : (x : X) → q x ＝ ₁ → (y : Y x) → p (x , y) ＝ ₁
  q₁ x = pr₂ (pr₂ (co-characteristic-function f) x)

  e : is-decidable (∀ x → q x ＝ ₁)
  e = c q

  g : is-decidable (∀ x → q x ＝ ₁) → is-decidable (∀ σ → p σ ＝ ₁)
  g (inl α) = inl h
   where
    h : (σ : Σ Y) → p σ ＝ ₁
    h (x , y) = q₁ x (α x) y
  g (inr u) = inr (contrapositive h u)
   where
    h : ((σ : Σ Y) → p σ ＝ ₁) → (x : X) → q x ＝ ₁
    h β x = different-from-₀-equal-₁ (λ r → q₀ x r (λ y → β (x , y)))

\end{code}

TODO. Consider also other possible closure properties, and
∃-compactness.

We now turn to propositions. A proposition is ∃-compact iff it is
decidable. Regarding the compactness of propositions, we have partial
information for the moment.

\begin{code}

∃-compact-propositions-are-decidable : (X : 𝓤 ̇ )
                                     → is-prop X
                                     → is-∃-compact X
                                     → is-decidable X
∃-compact-propositions-are-decidable X isp c = f a
 where
  a : is-decidable ∥ X × (₀ ＝ ₀) ∥
  a = c (λ x → ₀)

  f : is-decidable ∥ X × (₀ ＝ ₀) ∥ → is-decidable X
  f (inl s) = inl (∥∥-rec isp pr₁ s)
  f (inr u) = inr (λ x → u ∣ x , refl ∣)

∃-compact-types-have-decidable-support : {X : 𝓤 ̇ }
                                       → is-∃-compact X
                                       → is-decidable ∥ X ∥
∃-compact-types-have-decidable-support {𝓤} {X} c =
 ∃-compact-propositions-are-decidable ∥ X ∥ ∥∥-is-prop
  (codomain-of-surjection-is-∃-compact ∣_∣ pt-is-surjection c)

∃-compact-non-empty-types-are-inhabited : {X : 𝓤 ̇ }
                                        → is-∃-compact X
                                        → ¬¬ X
                                        → ∥ X ∥
∃-compact-non-empty-types-are-inhabited {𝓤} {X} c φ =
 g (∃-compact-types-have-decidable-support c)
 where
  g : is-decidable ∥ X ∥ → ∥ X ∥
  g (inl s) = s
  g (inr u) = 𝟘-elim (φ (λ x → u ∣ x ∣))

decidable-propositions-are-∃-compact : (X : 𝓤 ̇ )
                                     → is-prop X
                                     → is-decidable X
                                     → is-∃-compact X
decidable-propositions-are-∃-compact X isp d p = g d
 where
  g : is-decidable X → is-decidable (∃ x ꞉ X , p x ＝ ₀)
  g (inl x) = 𝟚-equality-cases b c
   where
    b : p x ＝ ₀ → is-decidable (∃ x ꞉ X , p x ＝ ₀)
    b r = inl ∣ x , r ∣

    c : p x ＝ ₁ → is-decidable (∃ x ꞉ X , p x ＝ ₀)
    c r = inr (∥∥-rec (𝟘-is-prop) f)
     where
      f : ¬ (Σ y ꞉ X , p y ＝ ₀)
      f (y , q) = zero-is-not-one (transport (λ - → p - ＝ ₀) (isp y x) q ⁻¹ ∙ r)

  g (inr u) = inr (∥∥-rec 𝟘-is-prop (λ σ → u (pr₁ σ)))

negations-of-Π-compact-types-are-decidable : (X : 𝓤 ̇ )
                                           → is-Π-compact X
                                           → is-decidable (¬ X)
negations-of-Π-compact-types-are-decidable X c = f a
 where
  a : is-decidable (X → ₀ ＝ ₁)
  a = c (λ x → ₀)

  f : is-decidable (X → ₀ ＝ ₁) → is-decidable (¬ X)
  f (inl u) = inl (zero-is-not-one  ∘ u)
  f (inr φ) = inr (λ u → φ (λ x → 𝟘-elim (u x)))

negations-of-types-whose-decidability-is-Π-compact-are-decidable
 : (X : 𝓤 ̇ )
 → is-Π-compact (is-decidable X)
 → is-decidable (¬ X)
negations-of-types-whose-decidability-is-Π-compact-are-decidable X c
 = Cases a l m
 where
  p : X + ¬ X → 𝟚
  p (inl x) = ₀
  p (inr u) = ₁

  a : is-decidable ((z : X + ¬ X) → p z ＝ ₁)
  a = c p

  l : ((z : X + ¬ X) → p z ＝ ₁) → ¬ X + ¬¬ X
  l α = inl (λ x → 𝟘-elim (zero-is-not-one (α (inl x))))

  α : (u : X → 𝟘) (z : X + ¬ X) → p z ＝ ₁
  α u (inl x) = 𝟘-elim (u x)
  α u (inr v) = refl

  m : ¬ ((z : X + ¬ X) → p z ＝ ₁) → ¬ X + ¬¬ X
  m φ = inr (λ u → φ (α u))

\end{code}

8th Feb 2018: A pointed detachable subset of any type is a
retract. Hence any detachable (pointed or not) subset of a ∃-compact
type is compact. The first construction should probably go to another
module.

\begin{code}

detachable-subset-retract : {X : 𝓤 ̇ } {A : X → 𝟚}
                          → (Σ x ꞉ X , A x ＝ ₀)
                          → retract (Σ x ꞉ X , A x ＝ ₀) of X
detachable-subset-retract {𝓤} {X} {A} (x₀ , e₀) = r , pr₁ , rs
 where
  r : X → Σ x ꞉ X , A x ＝ ₀
  r x = 𝟚-equality-cases
         (λ (e : A x ＝ ₀) → (x , e))
         (λ (e : A x ＝ ₁) → (x₀ , e₀))

  rs : (σ : Σ x ꞉ X , A x ＝ ₀) → r (pr₁ σ) ＝ σ
  rs (x , e) = w
   where
    s : (b : 𝟚) → b ＝ ₀ → 𝟚-equality-cases
                           (λ (_ : b ＝ ₀) → (x , e))
                           (λ (_ : b ＝ ₁) → (x₀ , e₀)) ＝ (x , e)
    s ₀ refl = refl
    s ₁ r = 𝟘-elim (one-is-not-zero r)

    t : 𝟚-equality-cases
         (λ (_ : A x ＝ ₀) → x , e)
         (λ (_ : A x ＝ ₁) → x₀ , e₀)
      ＝ (x , e)
    t = s (A x) e

    u : (λ e' → x , e') ＝ (λ _ → x , e)
    u = dfunext fe' λ e' → ap (λ - → (x , -)) (𝟚-is-set e' e)

    v : r x ＝ 𝟚-equality-cases
               (λ (_ : A x ＝ ₀) → x , e)
               (λ (_ : A x ＝ ₁) → x₀ , e₀)
    v = ap (λ - → 𝟚-equality-cases - (λ (_ : A x ＝ ₁) → x₀ , e₀)) u

    w : r x ＝ x , e
    w = v ∙ t

\end{code}

Notice that in the above lemma we need to assume that the detachable
set is pointed. But its use below doesn't, because ∃-compactness
allows us to decide inhabitedness, and ∃-compactness is a proposition.

\begin{code}

detachable-subset-∃-compact : {X : 𝓤 ̇ } (A : X → 𝟚)
                            → is-∃-compact X
                            → is-∃-compact (Σ x ꞉ X , A x ＝ ₀)
detachable-subset-∃-compact {𝓤} {X} A c = g (c A)
 where
  g : is-decidable (∃ x ꞉ X , A x ＝ ₀) → is-∃-compact (Σ x ꞉ X , A (x) ＝ ₀)
  g (inl e) = retract-is-∃-compact' (∥∥-functor detachable-subset-retract e) c
  g (inr u) = empty-types-are-∃-compact (contrapositive ∣_∣ u)

\end{code}

For the compact case, the retraction method to prove the last theorem
is not available, but the conclusion holds, with some of the same
ingredients (and with a longer proof (is there a shorter one?)).

\begin{code}

complemented-subtype-is-Π-compact : {X : 𝓤 ̇ } (A : X → 𝟚)
                                  → is-Π-compact X
                                  → is-Π-compact (Σ x ꞉ X , A x ＝ ₁)
complemented-subtype-is-Π-compact {𝓤} {X} A c q = g (c p)
 where
  p₀ : (x : X) → A x ＝ ₀ → 𝟚
  p₀ x e = ₁

  p₁ : (x : X) → A x ＝ ₁ → 𝟚
  p₁ x e = q (x , e)

  p : X → 𝟚
  p x = 𝟚-equality-cases (p₀ x) (p₁ x)

  p-spec₀ : (x : X) → A x ＝ ₀ → p x ＝ ₁
  p-spec₀ x e = s (A x) e (p₁ x)
   where
    s : (b : 𝟚) → b ＝ ₀ → (f₁ : b ＝ ₁ → 𝟚)
      → 𝟚-equality-cases (λ (_ : b ＝ ₀) → ₁) f₁ ＝ ₁
    s ₀ refl = λ f₁ → refl
    s ₁ r = 𝟘-elim (one-is-not-zero r)

  p-spec₁ : (x : X) (e : A x ＝ ₁) → p x ＝ q (x , e)
  p-spec₁ x e = u ∙ t
   where
    y : A x ＝ ₁ → 𝟚
    y _ = q (x , e)

    r : p₁ x ＝ y
    r = dfunext fe' (λ e' → ap (p₁ x) (𝟚-is-set e' e))

    s : (b : 𝟚)
      → b ＝ ₁
      → 𝟚-equality-cases
         (λ (_ : b ＝ ₀) → ₁)
         (λ (_ : b ＝ ₁) → q (x , e))
      ＝ q (x , e)
    s ₀ r = 𝟘-elim (zero-is-not-one r)
    s ₁ refl = refl

    t : 𝟚-equality-cases (p₀ x) y ＝ q (x , e)
    t = s (A x) e

    u : p x ＝ 𝟚-equality-cases (p₀ x) y
    u = ap (𝟚-equality-cases (p₀ x)) r

  g : is-decidable ((x : X) → p x ＝ ₁)
    → is-decidable ((σ : Σ x ꞉ X , A x ＝ ₁) → q σ ＝ ₁)
  g (inl α) = inl h
   where
    h : (σ : Σ x ꞉ X , A x ＝ ₁) → q σ ＝ ₁
    h (x , e) = (p-spec₁ x e) ⁻¹ ∙ α x
  g (inr u) = inr (contrapositive h u)
   where
    h : ((σ : Σ x ꞉ X , A x ＝ ₁) → q σ ＝ ₁) → (x : X) → p x ＝ ₁
    h β x = 𝟚-equality-cases (p-spec₀ x) (λ e → p-spec₁ x e ∙ β (x , e))

\end{code}

20 Jan 2018.

We now consider a truncated version of pointed compactness (see the
module CompactTypes).

\begin{code}

is-∃-compact∙ : 𝓤 ̇ → 𝓤 ̇
is-∃-compact∙ X = (p : X → 𝟚) → ∃ x₀ ꞉ X , (p x₀ ＝ ₁ → (x : X) → p x ＝ ₁)

∃-compactness∙-is-prop : {X : 𝓤 ̇ } → is-prop (is-∃-compact∙ X)
∃-compactness∙-is-prop {𝓤} = Π-is-prop fe' (λ _ → ∥∥-is-prop)

\end{code}

Notice that, in view of the above results, inhabitedness can be
replaced by non-emptiness in the following results:

\begin{code}

∃-compact∙-types-are-inhabited-and-compact : {X : 𝓤 ̇ }
                                           → is-∃-compact∙ X
                                           → ∥ X ∥ × is-∃-compact X
∃-compact∙-types-are-inhabited-and-compact {𝓤} {X} c = γ
 where
  g₁ : ∥ Σ (λ x₀ → ₀ ＝ ₁ → (x : X) → ₀ ＝ ₁) ∥
  g₁ = c (λ x → ₀)

  g₂ : (p : X → 𝟚)
     → (Σ x₀ ꞉ X , (p x₀ ＝ ₁ → (x : X) → p x ＝ ₁))
     → is-decidable (∃ x ꞉ X , p x ＝ ₀)
  g₂ p (x₀ , φ) = h (𝟚-is-discrete (p x₀) ₁)
   where
    h : is-decidable (p x₀ ＝ ₁) → is-decidable (∃ x ꞉ X , p x ＝ ₀)
    h (inl r) = inr (∥∥-rec 𝟘-is-prop f)
     where
      f : ¬ (Σ x ꞉ X , p x ＝ ₀)
      f (x , s) = zero-is-not-one (s ⁻¹ ∙ φ r x)
    h (inr u) = inl ∣ x₀ , (different-from-₁-equal-₀ u) ∣

  γ : ∥ X ∥ × is-∃-compact X
  γ = ∥∥-functor pr₁ g₁ ,
      (λ p → ∥∥-rec (decidability-of-prop-is-prop fe' ∥∥-is-prop)
               (g₂ p) (c p))

inhabited-and-compact-types-are-∃-compact∙ : {X : 𝓤 ̇ }
                                           → ∥ X ∥ × is-∃-compact X
                                           → is-∃-compact∙ X
inhabited-and-compact-types-are-∃-compact∙ {𝓤} {X} (t , c) p = γ
 where
  f : X → ∃ x₀ ꞉ X , (p x₀ ＝ ₁ → (x : X) → p x ＝ ₁)
  f x₀ = g (𝟚-is-discrete (p x₀) ₀) (c p)
   where
    g : is-decidable (p x₀ ＝ ₀)
      → is-decidable (∃ x ꞉ X , p x ＝ ₀)
      → ∃ x₀ ꞉ X , (p x₀ ＝ ₁ → (x : X) → p x ＝ ₁)
    g (inl r) _       = ∣ x₀ , (λ s _ → 𝟘-elim (zero-is-not-one (r ⁻¹ ∙ s))) ∣
    g (inr _) (inl t) = ∥∥-functor h t
     where
      h : (Σ x ꞉ X , p x ＝ ₀) → Σ x₀ ꞉ X , (p x₀ ＝ ₁ → (x : X) → p x ＝ ₁)
      h (x , r) = x , λ s _ → 𝟘-elim (zero-is-not-one (r ⁻¹ ∙ s))
    g (inr _) (inr v) = ∣ x₀ , (λ _ → not-exists₀-implies-forall₁ p v) ∣

  γ : ∃ x₀ ꞉ X , (p x₀ ＝ ₁ → (x : X) → p x ＝ ₁)
  γ = ∥∥-rec ∥∥-is-prop f t

\end{code}

This characterizes the ∃-compact∙ types as those that are ∃-compact
and inhabited. We can also characterize the ∃-compact types as those
that are ∃-compact∙ or empty:

\begin{code}

being-∃-compact∙-and-empty-is-prop : {X : 𝓤 ̇ }
                                   → is-prop (is-∃-compact∙ X + is-empty X)
being-∃-compact∙-and-empty-is-prop {𝓤} {X} =
 sum-of-contradictory-props
  ∃-compactness∙-is-prop
  (Π-is-prop fe'
    (λ _ → 𝟘-is-prop))
  (λ c u → ∥∥-rec 𝟘-is-prop (contrapositive pr₁ u) (c (λ _ → ₀)))

∃-compact∙-or-empty-types-are-∃-compact : {X : 𝓤 ̇ }
                                        → is-∃-compact∙ X + is-empty X
                                        → is-∃-compact X
∃-compact∙-or-empty-types-are-∃-compact (inl c) =
 pr₂ (∃-compact∙-types-are-inhabited-and-compact c)
∃-compact∙-or-empty-types-are-∃-compact (inr u) =
 empty-types-are-∃-compact u

∃-compact-types-are-∃-compact∙-or-empty : {X : 𝓤 ̇ }
                                        → is-∃-compact X
                                        → is-∃-compact∙ X + is-empty X
∃-compact-types-are-∃-compact∙-or-empty {𝓤} {X} c = g
 where
  h : is-decidable (∃ x ꞉ X , ₀ ＝ ₀) → is-∃-compact∙ X + is-empty X
  h (inl t) = inl (inhabited-and-compact-types-are-∃-compact∙
                    (∥∥-functor pr₁ t , c))
  h (inr u) = inr (contrapositive (λ x → ∣ x , refl ∣) u)

  g : is-∃-compact∙ X + is-empty X
  g = h (c (λ _ → ₀))

\end{code}

8 Feb 2018: A type X is Π-compact iff every map X → 𝟚 has an infimum:

\begin{code}

_has-inf_ : {X : 𝓤 ̇ } → (X → 𝟚) → 𝟚 → 𝓤 ̇
p has-inf n = (∀ x → n ≤ p x) × (∀ (m : 𝟚) → (∀ x → m ≤ p x) → m ≤ n)

having-inf-is-prop : {X : 𝓤 ̇ } (p : X → 𝟚) (n : 𝟚) → is-prop (p has-inf n)
having-inf-is-prop {𝓤} {X} p n (f , g) (f' , g') = to-×-＝ r s
 where
  r : f ＝ f'
  r = dfunext fe' (λ x → ≤₂-is-prop-valued (f x) (f' x))
  s : g ＝ g'
  s = dfunext fe' (λ m → dfunext fe' (λ ϕ → ≤₂-is-prop-valued (g m ϕ) (g' m ϕ)))

at-most-one-inf : {X : 𝓤 ̇ } (p : X → 𝟚) → is-prop (Σ n ꞉ 𝟚 , p has-inf n)
at-most-one-inf p (n , f , g) (n' , f' , g') = to-Σ-＝ (≤₂-anti (g' n f) (g n' f') , having-inf-is-prop p n' _ _)

has-infs : 𝓤 ̇ → 𝓤 ̇
has-infs X = ∀ (p : X → 𝟚) → Σ n ꞉ 𝟚 , p has-inf n

having-infs-is-prop : {X : 𝓤 ̇ } → is-prop (has-infs X)
having-infs-is-prop {𝓤} {X} = Π-is-prop fe' at-most-one-inf

Π-compact-has-infs : {X : 𝓤 ̇ } → is-Π-compact X → has-infs X
Π-compact-has-infs c p = g (c p)
 where
  g : is-decidable (∀ x → p x ＝ ₁) → Σ n ꞉ 𝟚 , p has-inf n
  g (inl α) = ₁ , (λ x → transport⁻¹ (₁ ≤₂_) (α x) (≤₂-refl {₀})) , λ m ϕ → ₁-top
  g (inr u) = ₀ , (λ _ → ₀-bottom {₀}) , h
   where
    h : (m : 𝟚) → (∀ x → m ≤ p x) → m ≤ ₀
    h m φ = ≤₂-criterion f
     where
      f : m ＝ ₁ → ₀ ＝ ₁
      f r = 𝟘-elim (u α)
       where
        α : ∀ x → p x ＝ ₁
        α x = ₁-maximal (transport (_≤ p x) r (φ x))

has-infs-Π-compact : {X : 𝓤 ̇ } → has-infs X → is-Π-compact X
has-infs-Π-compact h p = f (h p)
 where
  f : (Σ n ꞉ 𝟚 , p has-inf n) → is-decidable (∀ x → p x ＝ ₁)
  f (₀ , _ , l) = inr u
   where
    u : ¬ ∀ x → p x ＝ ₁
    u α = l ₁ (λ x → ≤₂-criterion (λ _ → α x))
  f (₁ , g , _) = inl α
   where
    α : ∀ x → p x ＝ ₁
    α x = ₁-maximal (g x)

\end{code}

TODO. Show equivalence with existence of suprema. Is there a similar
characterization of ∃-compactness?

Implicit application of type-theoretical choice:

\begin{code}

inf : {X : 𝓤 ̇ } → is-Π-compact X → (X → 𝟚) → 𝟚
inf c p = pr₁ (Π-compact-has-infs c p)

inf-property : {X : 𝓤 ̇ } → (c : is-Π-compact X) (p : X → 𝟚) → p has-inf (inf c p)
inf-property c p = pr₂ (Π-compact-has-infs c p)

inf₁ : {X : 𝓤 ̇ } (c : is-Π-compact X) {p : X → 𝟚}
     → inf c p ＝ ₁ → ∀ x → p x ＝ ₁
inf₁ c {p} r x = ≤₂-criterion-converse (pr₁ (inf-property c p) x) r

inf₁-converse : {X : 𝓤 ̇ } (c : is-Π-compact X) {p : X → 𝟚}
              → (∀ x → p x ＝ ₁) → inf c p ＝ ₁
inf₁-converse c {p} α = ₁-maximal (h g)
 where
  h : (∀ x → ₁ ≤ p x) → ₁ ≤ inf c p
  h = pr₂ (inf-property c p) ₁

  g : ∀ x → ₁ ≤ p x
  g x = ₁-maximal-converse (α x)

\end{code}

21 Feb 2018.

It is well known that infima and suprema are characterized as
adjoints. TODO. Link the above development with the following (easy).

In synthetic topology with the dominance 𝟚, a type is called 𝟚-compact
if the map Κ : 𝟚 → (X → 𝟚) has a right adjoint A : (X → 𝟚) → 𝟚, with
respect to the natural ordering of 𝟚 and the pointwise order of the
function type (X → 𝟚), and 𝟚-overt if it has a left-adjoint
E : (X → 𝟚) → 𝟚.

Κ is the usual combinator (written Kappa rather than Kay here):

\begin{code}

Κ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → Y → (X → Y)
Κ y x = y

\end{code}

The pointwise order on boolean predicates:

\begin{code}

_≤̇_ : {X : 𝓤 ̇ } → (X → 𝟚) → (X → 𝟚) → 𝓤 ̇
p ≤̇ q = ∀ x → p x ≤ q x

\end{code}

We define adjunctions in the two special cases where one of the sides
is Κ with Y=𝟚, for simplicity, rather than in full generality:

\begin{code}

Κ⊣ : {X : 𝓤 ̇ } → ((X → 𝟚) → 𝟚) → 𝓤 ̇
Κ⊣ A = (n : 𝟚) (p : _ → 𝟚) → Κ n ≤̇ p ↔ n ≤ A p

_⊣Κ : {X : 𝓤 ̇ } → ((X → 𝟚) → 𝟚) → 𝓤 ̇
E ⊣Κ = (n : 𝟚) (p : _ → 𝟚) → E p ≤ n ↔ p ≤̇ Κ n

\end{code}

TODO: The types Κ⊣ A and E ⊣Κ are propositions, and so are the types
Σ A ꞉ ((X → 𝟚) → 𝟚) , Κ⊣ A (compactness) and
Σ E ꞉ (X → 𝟚) → 𝟚) , E ⊣Κ (overtness).

Right adjoints to Κ are characterized as follows:

\begin{code}

Κ⊣-charac : {X : 𝓤 ̇ } → (A : (X → 𝟚) → 𝟚)
          → Κ⊣ A ↔ ((p : X → 𝟚) → A p ＝ ₁ ↔ p ＝ (λ x → ₁))
Κ⊣-charac {𝓤} {X} A = f , g
 where
  f : Κ⊣ A → (p : X → 𝟚) → A p ＝ ₁ ↔ p ＝ (λ x → ₁)
  f φ p = f₀ , f₁
   where
    f₀ : A p ＝ ₁ → p ＝ (λ x → ₁)
    f₀ r = dfunext fe' l₃
     where
      l₀ : ₁ ≤ A p → Κ ₁ ≤̇ p
      l₀ = pr₂ (φ ₁ p)
      l₁ : Κ ₁ ≤̇ p
      l₁ = l₀ (₁-maximal-converse r)
      l₂ : (x : X) → ₁ ≤ p x
      l₂ = l₁
      l₃ : (x : X) → p x ＝ ₁
      l₃ x = ≤₂-criterion-converse (l₂ x) refl
    f₁ : p ＝ (λ x → ₁) → A p ＝ ₁
    f₁ s = ≤₂-criterion-converse l₀ refl
     where
      l₃ : (x : X) → p x ＝ ₁
      l₃ = happly s
      l₂ : (x : X) → ₁ ≤ p x
      l₂ x = ₁-maximal-converse (l₃ x)
      l₁ : Κ ₁ ≤̇ p
      l₁ = l₂
      l₀ : ₁ ≤ A p
      l₀ = pr₁ (φ ₁ p) l₁
  g : ((p : X → 𝟚) → A p ＝ ₁ ↔ p ＝ (λ x → ₁)) → Κ⊣ A
  g γ n p = (g₀ n refl , g₁ n refl)
   where
    g₀ : ∀ m → m ＝ n → Κ m ≤̇ p → m ≤ A p
    g₀ ₀ r l = ₀-bottom {₀}
    g₀ ₁ refl l = ₁-maximal-converse (pr₂ (γ p) l₁)
     where
      l₀ : (x : X) → p x ＝ ₁
      l₀ x = ₁-maximal (l x)
      l₁ : p ＝ (λ x → ₁)
      l₁ = dfunext fe' l₀

    g₁ : ∀ m → m ＝ n → m ≤ A p → Κ m ≤̇ p
    g₁ ₀ r l x = ₀-bottom {₀}
    g₁ ₁ refl l x = ₁-maximal-converse (l₀ x)
     where
      l₁ : p ＝ (λ x → ₁)
      l₁ = pr₁ (γ p) (₁-maximal l)
      l₀ : (x : X) → p x ＝ ₁
      l₀ = happly l₁

\end{code}

Using this as a lemma, we see that a type is Π-compact in the sense we
defined iff it is compact in the usual sense of synthetic topology for
the dominance 𝟚.

\begin{code}

Π-compact-iff-Κ-has-right-adjoint : {X : 𝓤 ̇ }
                                  → is-Π-compact X ↔ (Σ A ꞉ ((X → 𝟚) → 𝟚), Κ⊣ A)
Π-compact-iff-Κ-has-right-adjoint {𝓤} {X} = (f , g)
 where
  f : is-Π-compact X → Σ A ꞉ ((X → 𝟚) → 𝟚), Κ⊣ A
  f c = (A , pr₂ (Κ⊣-charac A) l₁)
   where
    c' : (p : X → 𝟚) → is-decidable (p ＝ (λ x → ₁))
    c' = Π-compact-types-are-Π-compact' c

    l₀ : (p : X → 𝟚)
       → is-decidable (p ＝ (λ x → ₁)) → Σ n ꞉ 𝟚 , (n ＝ ₁ ↔ p ＝ (λ x → ₁))
    l₀ p (inl r) = (₁ , ((λ _ → r) , λ _ → refl))
    l₀ p (inr u) = (₀ , ((λ s → 𝟘-elim (zero-is-not-one s)) , λ r → 𝟘-elim (u r)))

    A : (X → 𝟚) → 𝟚
    A p = pr₁ (l₀ p (c' p))

    l₁ : (p : X → 𝟚) → A p ＝ ₁ ↔ p ＝ (λ x → ₁)
    l₁ p = pr₂ (l₀ p (c' p))

  g : ((Σ A ꞉ ((X → 𝟚) → 𝟚), Κ⊣ A)) → is-Π-compact X
  g (A , φ) = Π-compact'-types-are-Π-compact c'
   where
    l₁ : (p : X → 𝟚) → A p ＝ ₁ ↔ p ＝ (λ x → ₁)
    l₁ = pr₁ (Κ⊣-charac A) φ

    l₀ : (p : X → 𝟚) → is-decidable (A p ＝ ₁) → is-decidable (p ＝ (λ x → ₁))
    l₀ p (inl r) = inl (pr₁ (l₁ p) r)
    l₀ p (inr u) = inr (contrapositive (pr₂ (l₁ p)) u)

    c' : (p : X → 𝟚) → is-decidable (p ＝ (λ x → ₁))
    c' p = l₀ p (𝟚-is-discrete (A p) ₁)

\end{code}

Next we show that κ has a right adjoint iff it has a left adjoint,
namely its De Morgan dual, which exists because 𝟚 is a boolean algebra
and hence so is the type (X → 𝟚) with the pointwise operations.

\begin{code}

𝟚-DeMorgan-dual : {X : 𝓤 ̇ } → ((X → 𝟚) → 𝟚) → ((X → 𝟚) → 𝟚)
𝟚-DeMorgan-dual φ p = complement (φ (λ x → complement (p x)))

𝟚-DeMorgan-dual-involutive : {X : 𝓤 ̇ } → (φ : (X → 𝟚) → 𝟚)
                           → 𝟚-DeMorgan-dual (𝟚-DeMorgan-dual φ) ＝ φ
𝟚-DeMorgan-dual-involutive {𝓤} φ = dfunext fe' h
 where
  f : ∀ p → complement (complement (φ (λ x → complement (complement (p x)))))
          ＝ φ (λ x → complement (complement (p x)))
  f p = complement-involutive (φ (λ x → complement (complement (p x))))

  g : ∀ p → φ (λ x → complement (complement (p x))) ＝ φ p
  g p = ap φ (dfunext fe' (λ x → complement-involutive (p x)))

  h : ∀ p → 𝟚-DeMorgan-dual (𝟚-DeMorgan-dual φ) p ＝ φ p
  h p = f p ∙ g p

Π-compact-is-𝟚-overt : {X : 𝓤 ̇ } → (A : (X → 𝟚) → 𝟚)
                     → Κ⊣ A → (𝟚-DeMorgan-dual A) ⊣Κ
Π-compact-is-𝟚-overt {𝓤} {X} A = f
 where
  E : (X → 𝟚) → 𝟚
  E = 𝟚-DeMorgan-dual A
  f : Κ⊣ A → E ⊣Κ
  f φ = γ
   where
     γ : (n : 𝟚) (p : X → 𝟚) → (E p ≤ n) ↔ (p ≤̇ Κ n)
     γ n p = (γ₀ , γ₁ )
      where
       γ₀ : E p ≤ n → p ≤̇ Κ n
       γ₀ l = m₃
        where
         m₀ : complement n ≤ A (λ x → complement (p x))
         m₀ = complement-left l
         m₁ : Κ (complement n) ≤̇ (λ x → complement (p x))
         m₁ = pr₂ (φ (complement n) (λ x → complement (p x))) m₀
         m₂ : (x : X) → complement n ≤ complement (p x)
         m₂ = m₁
         m₃ : (x : X) → p x ≤ n
         m₃ x = complement-both-left (m₂ x)

       γ₁ : p ≤̇ Κ n → E p ≤ n
       γ₁ l = complement-left m₀
        where
         m₃ : (x : X) → p x ≤ n
         m₃ = l
         m₂ : (x : X) → complement n ≤ complement (p x)
         m₂ x = complement-both-right (m₃ x)
         m₁ : Κ (complement n) ≤̇ (λ x → complement (p x))
         m₁ = m₂
         m₀ : complement n ≤ A (λ x → complement (p x))
         m₀ = pr₁ (φ (complement n) (λ x → complement (p x))) m₁

𝟚-overt-is-Π-compact : {X : 𝓤 ̇ } → (E : (X → 𝟚) → 𝟚)
                     → E ⊣Κ → Κ⊣ (𝟚-DeMorgan-dual E)
𝟚-overt-is-Π-compact {𝓤} {X} E = g
 where
  A : (X → 𝟚) → 𝟚
  A = 𝟚-DeMorgan-dual E
  g : E ⊣Κ → Κ⊣ A
  g γ = φ
   where
     φ : (n : 𝟚) (p : X → 𝟚) → Κ n ≤̇ p ↔ n ≤ A p
     φ n p = (φ₀ , φ₁ )
      where
       φ₀ : Κ n ≤̇ p → n ≤ A p
       φ₀ l = complement-right m₀
        where
         m₃ : (x : X) → n ≤ p x
         m₃ = l
         m₂ : (x : X) → complement (p x) ≤ complement n
         m₂ x = complement-both-right (m₃ x)
         m₁ : (λ x → complement (p x)) ≤̇ Κ (complement n)
         m₁ = m₂
         m₀ : E (λ x → complement (p x)) ≤ complement n
         m₀ = pr₂ (γ (complement n) (λ x → complement (p x))) m₂

       φ₁ : n ≤ A p → Κ n ≤̇ p
       φ₁ l = m₃
        where
         m₀ : E (λ x → complement (p x)) ≤ complement n
         m₀ = complement-right l
         m₁ : (λ x → complement (p x)) ≤̇ Κ (complement n)
         m₁ = pr₁ (γ (complement n) (λ x → complement (p x))) m₀
         m₂ : (x : X) → complement (p x) ≤ complement n
         m₂ = m₁
         m₃ : (x : X) → n ≤ p x
         m₃ x = complement-both-left (m₂ x)

\end{code}

We have the following corollaries:

\begin{code}

Π-compact-iff-𝟚-overt : {X : 𝓤 ̇ }
                      → (Σ A ꞉ ((X → 𝟚) → 𝟚), Κ⊣ A) ↔ (Σ E ꞉ ((X → 𝟚) → 𝟚), E ⊣Κ)
Π-compact-iff-𝟚-overt {𝓤} {X} = (f , g)
 where
  f : (Σ A ꞉ ((X → 𝟚) → 𝟚), Κ⊣ A) → (Σ E ꞉ ((X → 𝟚) → 𝟚), E ⊣Κ)
  f (A , φ) = (𝟚-DeMorgan-dual A , Π-compact-is-𝟚-overt A φ)

  g : (Σ E ꞉ ((X → 𝟚) → 𝟚), E ⊣Κ) → (Σ A ꞉ ((X → 𝟚) → 𝟚), Κ⊣ A)
  g (E , γ) = (𝟚-DeMorgan-dual E , 𝟚-overt-is-Π-compact E γ)

\end{code}

In this corollary we record explicitly that a type is Π-compact iff it
is 𝟚-overt:

\begin{code}

Π-compact-iff-Κ-has-left-adjoint : {X : 𝓤 ̇ }
                                 → is-Π-compact X ↔ (Σ E ꞉ ((X → 𝟚) → 𝟚), E ⊣Κ)
Π-compact-iff-Κ-has-left-adjoint {𝓤} {X} = (f , g)
 where
  f : is-Π-compact X → (Σ E ꞉ ((X → 𝟚) → 𝟚), E ⊣Κ)
  f c = pr₁ Π-compact-iff-𝟚-overt (pr₁ Π-compact-iff-Κ-has-right-adjoint c)

  g : (Σ E ꞉ ((X → 𝟚) → 𝟚), E ⊣Κ) → is-Π-compact X
  g o = pr₂ Π-compact-iff-Κ-has-right-adjoint (pr₂ Π-compact-iff-𝟚-overt o)

\end{code}

TODO. We get as a corollary that

      E ⊣Κ ↔ ((p : X → 𝟚) → E p ＝ ₀ ↔ p ＝ (λ x → ₀)).

TODO. Find the appropriate place in this file to remark that decidable
propositions are closed under Π-compact/overt meets and joins. And
then clopen sets (or 𝟚-open sets, or complemented subsets) are closed
under Π-compact/over unions and intersections.

20 Feb 2018. In classical topology, a space X is compact iff the
projection A × X → A is a closed map for every space A, meaning that
the image of every closed set is closed. In our case, because of the
use of decidable truth-values in the definition of Π-compactness, the
appropriate notion is that of clopen map, that is, a map that sends
clopen sets to clopen sets. As in our setup, clopen sets correspond to
decidable subsets, or sets with 𝟚-valued characteristic functions. In
our case, the clopeness of the projections characterize the notion of
∃-compactness, which is stronger than compactness.

There is a certain asymmetry in the following definition, in that the
input decidable predicate (or clopen subtype) is given as a 𝟚-valued
function, whereas instead of saying that the image predicate factors
through the embedding 𝟚 of into the type of truth values, we say that
it has decidable truth-values, which is equivalent. Such an asymmetry
is already present in our formulation of the notion of compactness.

We have defined image with lower case in the module UF. We now need
Images with upper case:

\begin{code}

Image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
     → (X → Y) → (X → 𝓦 ̇ ) → (Y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇ )
Image f A = λ y → ∃ x ꞉ domain f , A x × (f x ＝ y)

is-clopen-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-clopen-map {𝓤} {𝓥} {X} {Y} f = (p : X → 𝟚) (y : Y)
                                → is-decidable (Image f (λ x → p x ＝ ₀) y)

being-clopen-map-is-prop : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                           → (f : X → Y) → is-prop (is-clopen-map f)
being-clopen-map-is-prop {𝓤} {𝓥} f =
 Π₂-is-prop fe' (λ p y → decidability-of-prop-is-prop fe' ∥∥-is-prop)

fst : (A : 𝓤 ̇ ) (X : 𝓥 ̇ ) → A × X → A
fst _ _ = pr₁

∃-compact-clopen-projections : (X : 𝓤 ̇ )
                             → is-∃-compact X
                             → (∀ {𝓥} (A : 𝓥 ̇ ) → is-clopen-map (fst A X))
∃-compact-clopen-projections X c A p a = g (c (λ x → p (a , x)))
 where
  g : is-decidable (∃ x ꞉ X , p (a , x) ＝ ₀)
    → is-decidable (∃ z ꞉ A × X , (p z ＝ ₀) × (pr₁ z ＝ a))
  g (inl e) = inl ((∥∥-functor h) e)
   where
    h : (Σ x ꞉ X , p (a , x) ＝ ₀) → Σ z ꞉ A × X , (p z ＝ ₀) × (pr₁ z ＝ a)
    h (x , r) =  (a , x) , (r , refl)
  g (inr u) = inr (contrapositive (∥∥-functor h) u)
   where
    h : (Σ z ꞉ A × X , (p z ＝ ₀) × (pr₁ z ＝ a)) → Σ x ꞉ X , p (a , x) ＝ ₀
    h ((a' , x) , (r , s)) = x , transport (λ - → p (- , x) ＝ ₀) s r

clopen-projections-∃-compact : ∀ {𝓤 𝓦} (X : 𝓤 ̇ )
                             → (∀ {𝓥} (A : 𝓥 ̇ ) → is-clopen-map (fst A X))
                             → is-∃-compact X
clopen-projections-∃-compact {𝓤} {𝓦} X κ p = g (κ 𝟙 (λ z → p (pr₂ z)) ⋆)
 where
  g : is-decidable (∃ z ꞉ 𝟙 {𝓦} × X , (p (pr₂ z) ＝ ₀) × (pr₁ z ＝ ⋆))
    → is-decidable (∃ x ꞉ X , p x ＝ ₀)
  g (inl e) = inl (∥∥-functor h e)
   where
    h : (Σ z ꞉ 𝟙 × X , (p (pr₂ z) ＝ ₀) × (pr₁ z ＝ ⋆)) → Σ x ꞉ X , p x ＝ ₀
    h ((⋆ , x) , r , _) = x , r
  g (inr u) = inr (contrapositive (∥∥-functor h) u)
   where
    h : (Σ x ꞉ X , p x ＝ ₀) → Σ z ꞉ 𝟙 × X , (p (pr₂ z) ＝ ₀) × (pr₁ z ＝ ⋆)
    h (x , r) = (⋆ , x) , (r , refl)

\end{code}

TODO.

⋆ Consider 𝟚-perfect maps.

⋆ ∃-compactness: attainability of minima. Existence of potential
  maxima.

⋆ Relation of Π-compactness with finiteness and discreteness.

⋆ Non-classical cotaboos Every Π-compact subtype of ℕ is finite. Every
  Π-compact subtype of a discrete type is finite. What are the
  cotaboos necessary (and sufficient) to prove that the type of
  decidable subsingletons of ℕ∞→ℕ is Π-compact?  Continuity principles
  are enough.

⋆ 𝟚-subspace: e:X→Y such that every clopen X→𝟚 extends to some clopen
  Y→𝟚 (formulated with Σ and ∃). Or to a largest such clopen, or a
  smallest such clopen (right and left adjoints to the restriction map
  (Y→𝟚)→(X→𝟚) that maps v to v ∘ e and could be written e ⁻¹[ v ].  A
  𝟚-subspace-embedding of totally separated types should be a
  (homotopy) embedding, but not conversely (find a counter-example).

⋆ 𝟚-injective types (injectives wrt to 𝟚-subspace-embeddigs). They
  should be the retracts of powers of 𝟚. Try to characterize them
  "intrinsically".

⋆ Relation of 𝟚-subspaces with Π-compact subtypes.

⋆ 𝟚-Hofmann-Mislove theorem: clopen filters of clopens should
  correspond to Π-compact (𝟚-saturated) 𝟚-subspaces. Are cotaboos
  needed for this?

⋆ Which results here depend on the particular dominance 𝟚, and which
  ones generalize to any dominance, or to any "suitable" dominance? In
  particular, it is of interest to generalize this to "Sierpinki like"
  dominances. And what is "Sierpinski like" in precise (internal)
  terms? This should be formulated in terms of cotaboos.
