Martin Escardo 2011.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.DiscreteAndSeparated where

open import MLTT.Spartan

open import MLTT.Plus-Properties
open import MLTT.Two-Properties
open import Naturals.Properties
open import NotionsOfDecidability.Complemented
open import NotionsOfDecidability.Decidable
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.FunExt
open import UF.Hedberg
open import UF.HedbergApplications
open import UF.Retracts
open import UF.Sets
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

is-isolated : {X : 𝓤 ̇ } → X → 𝓤 ̇
is-isolated x = ∀ y → is-decidable (x ＝ y)

\end{code}

Notice that there is a different notion of being homotopy isolated
(abbreviated is-h-isolated) in the module UF.Sets. We show below that
isolated points are h-isolated.

A type is perfect if it has no isolated points.

\begin{code}

is-perfect : 𝓤 ̇ → 𝓤 ̇
is-perfect X = is-empty (Σ x ꞉ X , is-isolated x)

is-isolated' : {X : 𝓤 ̇ } → X → 𝓤 ̇
is-isolated' x = ∀ y → is-decidable (y ＝ x)

is-decidable-eq-sym : {X : 𝓤 ̇ } (x y : X)
                    → is-decidable (x ＝ y)
                    → is-decidable (y ＝ x)
is-decidable-eq-sym x y = cases
                           (λ (p : x ＝ y) → inl (p ⁻¹))
                           (λ (n : ¬ (x ＝ y)) → inr (λ (q : y ＝ x) → n (q ⁻¹)))

is-isolated'-gives-is-isolated : {X : 𝓤 ̇ } (x : X)
                               → is-isolated' x
                               → is-isolated x
is-isolated'-gives-is-isolated x i' y = is-decidable-eq-sym y x (i' y)

is-isolated-gives-is-isolated' : {X : 𝓤 ̇ } (x : X)
                               → is-isolated x
                               → is-isolated' x
is-isolated-gives-is-isolated' x i y = is-decidable-eq-sym x y (i y)

is-discrete : 𝓤 ̇ → 𝓤 ̇
is-discrete X = (x : X) → is-isolated x

\end{code}

Standard examples:

\begin{code}

props-are-discrete : {P : 𝓤 ̇ } → is-prop P → is-discrete P
props-are-discrete i x y = inl (i x y)

𝟘-is-discrete : is-discrete (𝟘 {𝓤})
𝟘-is-discrete = props-are-discrete 𝟘-is-prop

𝟙-is-discrete : is-discrete (𝟙 {𝓤})
𝟙-is-discrete = props-are-discrete 𝟙-is-prop

𝟚-is-discrete : is-discrete 𝟚
𝟚-is-discrete ₀ ₀ = inl refl
𝟚-is-discrete ₀ ₁ = inr (λ (p : ₀ ＝ ₁) → 𝟘-elim (zero-is-not-one p))
𝟚-is-discrete ₁ ₀ = inr (λ (p : ₁ ＝ ₀) → 𝟘-elim (zero-is-not-one (p ⁻¹)))
𝟚-is-discrete ₁ ₁ = inl refl

ℕ-is-discrete : is-discrete ℕ
ℕ-is-discrete 0 0 = inl refl
ℕ-is-discrete 0 (succ n) = inr (λ (p : zero ＝ succ n)
                                     → positive-not-zero n (p ⁻¹))
ℕ-is-discrete (succ m) 0 = inr (λ (p : succ m ＝ zero)
                                     → positive-not-zero m p)
ℕ-is-discrete (succ m) (succ n) =  step (ℕ-is-discrete m n)
  where
   step : (m ＝ n) + (m ≠ n) → (succ m ＝ succ n) + (succ m ≠ succ n)
   step (inl r) = inl (ap succ r)
   step (inr f) = inr (λ s → f (succ-lc s))

inl-is-isolated : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (x : X)
                → is-isolated x
                → is-isolated (inl x)
inl-is-isolated {𝓤} {𝓥} {X} {Y} x i = γ
 where
  γ : (z : X + Y) → is-decidable (inl x ＝ z)
  γ (inl x') = Cases (i x')
                (λ (p : x ＝ x') → inl (ap inl p))
                (λ (n : ¬ (x ＝ x')) → inr (contrapositive inl-lc n))
  γ (inr y)  = inr +disjoint

inr-is-isolated : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (y : Y)
                → is-isolated y
                → is-isolated (inr y)
inr-is-isolated {𝓤} {𝓥} {X} {Y} y i = γ
 where
  γ : (z : X + Y) → is-decidable (inr y ＝ z)
  γ (inl x)  = inr +disjoint'
  γ (inr y') = Cases (i y')
                (λ (p : y ＝ y') → inl (ap inr p))
                (λ (n : ¬ (y ＝ y')) → inr (contrapositive inr-lc n))

+-is-discrete : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
              → is-discrete X
              → is-discrete Y
              → is-discrete (X + Y)
+-is-discrete d e (inl x) = inl-is-isolated x (d x)
+-is-discrete d e (inr y) = inr-is-isolated y (e y)

\end{code}

Added by Tom de Jong on 15 December 2024.
Note that we could also derive this from Σ-is-discrete (see the comment below)
and props-are-discrete (as above).

\begin{code}

subtype-is-discrete : {X : 𝓤 ̇  } {P : X → 𝓥 ̇  }
                    → ((x : X) → is-prop (P x))
                    → is-discrete X
                    → is-discrete (Σ P)
subtype-is-discrete pv d (x , p) (y , q) = κ (d x y)
 where
  κ : is-decidable (x ＝ y) → is-decidable ((x , p) ＝ (y , q))
  κ (inl  e) = inl (to-subtype-＝ pv e)
  κ (inr ne) = inr (λ h → ne (ap pr₁ h))

\end{code}

The closure of discrete types under Σ is proved in the module
TypeTopology.SigmaDiscreteAndTotallySeparated (as this requires to
first prove that discrete types are sets).

General properties:

\begin{code}

discrete-types-are-cotransitive : {X : 𝓤 ̇ }
                                 → is-discrete X
                                 → {x y z : X}
                                 → x ≠ y
                                 → (x ≠ z) + (z ≠ y)
discrete-types-are-cotransitive d {x} {y} {z} φ = f (d x z)
 where
  f : (x ＝ z) + (x ≠ z) → (x ≠ z) + (z ≠ y)
  f (inl r) = inr (λ s → φ (r ∙ s))
  f (inr γ) = inl γ

discrete-types-are-cotransitive' : {X : 𝓤 ̇ }
                                 → is-discrete X
                                 → {x y z : X}
                                 → x ≠ y
                                 → (x ≠ z) + (y ≠ z)
discrete-types-are-cotransitive' d {x} {y} {z} φ = f (d x z)
 where
  f : (x ＝ z) + (x ≠ z) → (x ≠ z) + (y ≠ z)
  f (inl r) = inr (λ s → φ (r ∙ s ⁻¹))
  f (inr γ) = inl γ

retract-is-discrete : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                    → retract Y of X
                    → is-discrete X
                    → is-discrete Y
retract-is-discrete (f , (s , φ)) d y y' = g (d (s y) (s y'))
 where
  g : is-decidable (s y ＝ s y') → is-decidable (y ＝ y')
  g (inl p) = inl ((φ y) ⁻¹ ∙ ap f p ∙ φ y')
  g (inr u) = inr (contrapositive (ap s) u)

𝟚-retract-of-non-trivial-type-with-isolated-point
 : {X : 𝓤 ̇ }
   {x₀ x₁ : X}
 → x₀ ≠ x₁
 → is-isolated x₀
 → retract 𝟚 of X
𝟚-retract-of-non-trivial-type-with-isolated-point {𝓤} {X} {x₀} {x₁} ne d =
  r , (s , rs)
 where
  r : X → 𝟚
  r = pr₁ (characteristic-function d)

  φ : (x : X) → (r x ＝ ₀ → x₀ ＝ x) × (r x ＝ ₁ → ¬ (x₀ ＝ x))
  φ = pr₂ (characteristic-function d)

  s : 𝟚 → X
  s ₀ = x₀
  s ₁ = x₁

  rs : (n : 𝟚) → r (s n) ＝ n
  rs ₀ = different-from-₁-equal-₀ (λ p → pr₂ (φ x₀) p refl)
  rs ₁ = different-from-₀-equal-₁ λ p → 𝟘-elim (ne (pr₁ (φ x₁) p))

𝟚-retract-of-discrete : {X : 𝓤 ̇ }
                        {x₀ x₁ : X}
                      → x₀ ≠ x₁
                      → is-discrete X
                      → retract 𝟚 of X
𝟚-retract-of-discrete {𝓤} {X} {x₀} {x₁} ne d = 𝟚-retract-of-non-trivial-type-with-isolated-point ne (d x₀)

\end{code}

¬¬-Separated types form an exponential ideal, assuming
extensionality. More generally:

\begin{code}

is-¬¬-separated : 𝓤 ̇ → 𝓤 ̇
is-¬¬-separated X = (x y : X) → ¬¬-stable (x ＝ y)

Π-is-¬¬-separated : funext 𝓤 𝓥
                  → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                  → ((x : X) → is-¬¬-separated (Y x))
                  → is-¬¬-separated (Π Y)
Π-is-¬¬-separated fe s f g h = dfunext fe lemma₂
 where
  lemma₀ : f ＝ g → ∀ x → f x ＝ g x
  lemma₀ r x = ap (λ - → - x) r

  lemma₁ : ∀ x → ¬¬ (f x ＝ g x)
  lemma₁ = double-negation-unshift (¬¬-functor lemma₀ h)

  lemma₂ : ∀ x → f x ＝ g x
  lemma₂ x =  s x (f x) (g x) (lemma₁ x)

discrete-is-¬¬-separated : {X : 𝓤 ̇ } → is-discrete X → is-¬¬-separated X
discrete-is-¬¬-separated d x y = ¬¬-elim (d x y)

𝟚-is-¬¬-separated : is-¬¬-separated 𝟚
𝟚-is-¬¬-separated = discrete-is-¬¬-separated 𝟚-is-discrete

ℕ-is-¬¬-separated : is-¬¬-separated ℕ
ℕ-is-¬¬-separated = discrete-is-¬¬-separated ℕ-is-discrete

subtype-is-¬¬-separated : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (m : X → Y)
                                     → left-cancellable m
                                     → is-¬¬-separated Y
                                     → is-¬¬-separated X
subtype-is-¬¬-separated {𝓤} {𝓥} {X} m i s x x' e = i (s (m x) (m x') (¬¬-functor (ap m) e))

Cantor-is-¬¬-separated : funext₀ → is-¬¬-separated (ℕ → 𝟚)
Cantor-is-¬¬-separated fe = Π-is-¬¬-separated fe (λ _ → 𝟚-is-¬¬-separated)

\end{code}

The following is an apartness relation when Y is ¬¬-separated, but we
define it without this assumption. (Are all types ¬¬-separated? See
below.)

\begin{code}

infix 21 _♯_

_♯_ : {X : 𝓤 ̇ } → {Y : X → 𝓥 ̇ } → (f g : (x : X) → Y x) → 𝓤 ⊔ 𝓥 ̇
f ♯ g = Σ x ꞉ domain f , f x ≠ g x


apart-is-different : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                   → {f g : (x : X) → Y x} → f ♯ g → f ≠ g
apart-is-different (x , φ) r = φ (ap (λ - → - x) r)


apart-is-symmetric : {X : 𝓤 ̇ } → {Y : X → 𝓥 ̇ }
                   → {f g : (x : X) → Y x} → f ♯ g → g ♯ f
apart-is-symmetric (x , φ)  = (x , (φ ∘ _⁻¹))

apart-is-cotransitive : {X : 𝓤 ̇ } → {Y : X → 𝓥 ̇ }
                     → ((x : X) → is-discrete (Y x))
                     → (f g h : (x : X) → Y x)
                     → f ♯ g → f ♯ h  +  h ♯ g
apart-is-cotransitive d f g h (x , φ)  = lemma₁ (lemma₀ φ)
 where
  lemma₀ : f x ≠ g x → (f x ≠ h x)  +  (h x ≠ g x)
  lemma₀ = discrete-types-are-cotransitive (d x)

  lemma₁ : (f x ≠ h x) + (h x ≠ g x) → f ♯ h  +  h ♯ g
  lemma₁ (inl γ) = inl (x , γ)
  lemma₁ (inr δ) = inr (x , δ)

\end{code}

We now consider two cases which render the apartness relation ♯ tight,
assuming function extensionality:

\begin{code}

tight : {X : 𝓤 ̇ }
      → funext 𝓤 𝓥
      → {Y : X → 𝓥 ̇ }
      → ((x : X) → is-¬¬-separated (Y x))
      → (f g : (x : X) → Y x)
      → ¬ (f ♯ g) → f ＝ g
tight fe s f g h = dfunext fe lemma₁
 where
  lemma₀ : ∀ x → ¬¬ (f x ＝ g x)
  lemma₀ = not-Σ-implies-Π-not h

  lemma₁ : ∀ x → f x ＝ g x
  lemma₁ x = (s x (f x) (g x)) (lemma₀ x)

tight' : {X : 𝓤 ̇ }
       → funext 𝓤 𝓥
       → {Y : X → 𝓥 ̇ }
       → ((x : X) → is-discrete (Y x))
       → (f g : (x : X) → Y x)
       → ¬ (f ♯ g) → f ＝ g
tight' fe d = tight fe (λ x → discrete-is-¬¬-separated (d x))

\end{code}

What about sums? The special case they reduce to binary products is
easy:

\begin{code}

binary-product-is-¬¬-separated : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                               → is-¬¬-separated X
                               → is-¬¬-separated Y
                               → is-¬¬-separated (X × Y)
binary-product-is-¬¬-separated s t (x , y) (x' , y') φ =
 lemma (lemma₀ φ) (lemma₁ φ)
 where
  lemma₀ : ¬¬ ((x , y) ＝ (x' , y')) → x ＝ x'
  lemma₀ = (s x x') ∘ ¬¬-functor (ap pr₁)

  lemma₁ : ¬¬ ((x , y) ＝ (x' , y')) → y ＝ y'
  lemma₁ = (t y y') ∘ ¬¬-functor (ap pr₂)

  lemma : x ＝ x' → y ＝ y' → (x , y) ＝ (x' , y')
  lemma = ap₂ (_,_)

\end{code}

This proof doesn't work for general dependent sums, because, among
other things, (ap pr₁) doesn't make sense in that case.  A different
special case is also easy:

\begin{code}

binary-sum-is-¬¬-separated : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                           → is-¬¬-separated X
                           → is-¬¬-separated Y
                           → is-¬¬-separated (X + Y)
binary-sum-is-¬¬-separated {𝓤} {𝓥} {X} {Y} s t (inl x) (inl x') = lemma
 where
  claim : inl x ＝ inl x' → x ＝ x'
  claim = ap p
   where
    p : X + Y → X
    p (inl u) = u
    p (inr v) = x

  lemma : ¬¬ (inl x ＝ inl x') → inl x ＝ inl x'
  lemma = ap inl ∘ s x x' ∘ ¬¬-functor claim

binary-sum-is-¬¬-separated s t (inl x) (inr y) =
 λ φ → 𝟘-elim (φ +disjoint )
binary-sum-is-¬¬-separated s t (inr y) (inl x)  =
 λ φ → 𝟘-elim (φ (+disjoint ∘ _⁻¹))
binary-sum-is-¬¬-separated {𝓤} {𝓥} {X} {Y} s t (inr y) (inr y') =
  lemma
 where
  claim : inr y ＝ inr y' → y ＝ y'
  claim = ap q
   where
    q : X + Y → Y
    q (inl u) = y
    q (inr v) = v

  lemma : ¬¬ (inr y ＝ inr y') → inr y ＝ inr y'
  lemma = ap inr ∘ t y y' ∘ ¬¬-functor claim

\end{code}

Added 19th March 2021.

\begin{code}

equality-of-¬¬stable-propositions' : propext 𝓤
                                   → (P Q : 𝓤 ̇ )
                                   → is-prop P
                                   → is-prop Q
                                   → ¬¬-stable P
                                   → ¬¬-stable Q
                                   → ¬¬-stable (P ＝ Q)
equality-of-¬¬stable-propositions' pe P Q i j f g a = V
 where
  I : ¬¬ (P → Q)
  I = ¬¬-functor (transport id) a

  II : P → Q
  II = →-is-¬¬-stable g I

  III : ¬¬ (Q → P)
  III = ¬¬-functor (transport id ∘ _⁻¹) a

  IV : Q → P
  IV = →-is-¬¬-stable f III

  V : P ＝ Q
  V = pe i j II IV

equality-of-¬¬stable-propositions : funext 𝓤 𝓤
                                  → propext 𝓤
                                  → (p q : Ω 𝓤)
                                  → ¬¬-stable (p holds)
                                  → ¬¬-stable (q holds)
                                  → ¬¬-stable (p ＝ q)
equality-of-¬¬stable-propositions fe pe p q f g a = γ
 where
  δ : p holds ＝ q holds
  δ = equality-of-¬¬stable-propositions'
       pe (p holds) (q holds) (holds-is-prop p) (holds-is-prop q)
       f g (¬¬-functor (ap _holds) a)

  γ : p ＝ q
  γ = to-subtype-＝ (λ _ → being-prop-is-prop fe) δ

\end{code}

TODO. Find a better home for the following.

\begin{code}

⊥-⊤-density' : funext 𝓤 𝓤
             → propext 𝓤
             → ∀ {𝓥} {X : 𝓥 ̇ }
             → is-¬¬-separated X
             → (f : Ω 𝓤 → X)
             → f ⊥ ＝ f ⊤
             → wconstant f
⊥-⊤-density' fe pe s f r p q = g p ∙ (g q)⁻¹
  where
    a : ∀ p → ¬¬ (f p ＝ f ⊤)
    a p t = no-truth-values-other-than-⊥-or-⊤ fe pe (p , (b , c))
      where
        b : p ≠ ⊥
        b u = t (ap f u ∙ r)

        c : p ≠ ⊤
        c u = t (ap f u)

    g : ∀ p → f p ＝ f ⊤
    g p = s (f p) (f ⊤) (a p)

⊥-⊤-Density : funext 𝓤 𝓤
            → propext 𝓤
            → {X : 𝓥 ̇ }
              (f : Ω 𝓤 → X)
            → is-¬¬-separated X
            → f ⊥ ＝ f ⊤
            → (p : Ω 𝓤) → f p ＝ f ⊤
⊥-⊤-Density fe pe f s r p = ⊥-⊤-density' fe pe s f r p ⊤

⊥-⊤-density : funext 𝓤 𝓤
            → propext 𝓤
            → (f : Ω 𝓤 → 𝟚)
            → f ⊥ ＝ ₁
            → f ⊤ ＝ ₁
            → (p : Ω 𝓤) → f p ＝ ₁
⊥-⊤-density fe pe f r s p =
 ⊥-⊤-Density fe pe f 𝟚-is-¬¬-separated (r ∙ s ⁻¹) p ∙ s

\end{code}

21 March 2018.

\begin{code}

qinvs-preserve-isolatedness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                            → qinv f
                            → (x : X)
                            → is-isolated x
                            → is-isolated (f x)
qinvs-preserve-isolatedness {𝓤} {𝓥} {X} {Y} f (g , ε , η) x i y = h (i (g y))
 where
  h : is-decidable (x ＝ g y) → is-decidable (f x ＝ y)
  h (inl p) = inl (ap f p ∙ η y)
  h (inr u) = inr (contrapositive (λ (q : f x ＝ y) → (ε x)⁻¹ ∙ ap g q) u)

equivs-preserve-isolatedness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                             → is-equiv f
                             → (x : X)
                             → is-isolated x
                             → is-isolated (f x)
equivs-preserve-isolatedness f e = qinvs-preserve-isolatedness f (equivs-are-qinvs f e)

new-point-is-isolated : {X : 𝓤 ̇ } → is-isolated {𝓤 ⊔ 𝓥} {X + 𝟙 {𝓥}} (inr ⋆)
new-point-is-isolated {𝓤} {𝓥} {X} = h
 where
  h :  (y : X + 𝟙) → is-decidable (inr ⋆ ＝ y)
  h (inl x) = inr +disjoint'
  h (inr ⋆) = inl refl

\end{code}

Back to old stuff:

\begin{code}

＝-indicator : (m : ℕ)
            → Σ p ꞉ (ℕ → 𝟚) , ((n : ℕ) → (p n ＝ ₀ → m ≠ n)
                                       × (p n ＝ ₁ → m ＝ n))
＝-indicator m = co-characteristic-function (ℕ-is-discrete m)

χ＝ : ℕ → ℕ → 𝟚
χ＝ m = pr₁ (＝-indicator m)

χ＝-spec : (m n : ℕ) → (χ＝ m n ＝ ₀ → m ≠ n) × (χ＝ m n ＝ ₁ → m ＝ n)
χ＝-spec m = pr₂ (＝-indicator m)

_＝[ℕ]_ : ℕ → ℕ → 𝓤₀ ̇
m ＝[ℕ] n = (χ＝ m n) ＝ ₁

infix  30 _＝[ℕ]_

＝-agrees-with-＝[ℕ] : (m n : ℕ) → m ＝ n ↔ m ＝[ℕ] n
＝-agrees-with-＝[ℕ] m n =
 (λ r → different-from-₀-equal-₁ (λ s → pr₁ (χ＝-spec m n) s r)) ,
 pr₂ (χ＝-spec m n)

≠-indicator : (m : ℕ)
            → Σ p ꞉ (ℕ → 𝟚) , ((n : ℕ) → (p n ＝ ₀ → m ＝ n)
                                       × (p n ＝ ₁ → m ≠ n))
≠-indicator m = indicator (ℕ-is-discrete m)

χ≠ : ℕ → ℕ → 𝟚
χ≠ m = pr₁ (≠-indicator m)

χ≠-spec : (m n : ℕ) → (χ≠ m n ＝ ₀ → m ＝ n) × (χ≠ m n ＝ ₁ → m ≠ n)
χ≠-spec m = pr₂ (≠-indicator m)

_≠[ℕ]_ : ℕ → ℕ → 𝓤₀ ̇
m ≠[ℕ] n = (χ≠ m n) ＝ ₁

infix  30 _≠[ℕ]_

≠[ℕ]-agrees-with-≠ : (m n : ℕ) → m ≠[ℕ] n ↔ m ≠ n
≠[ℕ]-agrees-with-≠ m n =
 pr₂ (χ≠-spec m n) ,
 (λ d → different-from-₀-equal-₁ (contrapositive (pr₁ (χ≠-spec m n)) d))

\end{code}

We now show that discrete types are sets (Hedberg's Theorem).

\begin{code}

decidable-types-are-collapsible : {X : 𝓤 ̇ } → is-decidable X → collapsible X
decidable-types-are-collapsible (inl x) = pointed-types-are-collapsible x
decidable-types-are-collapsible (inr u) = empty-types-are-collapsible u

discrete-is-Id-collapsible : {X : 𝓤 ̇ } → is-discrete X → Id-collapsible X
discrete-is-Id-collapsible d = decidable-types-are-collapsible (d _ _)

discrete-types-are-sets : {X : 𝓤 ̇ } → is-discrete X → is-set X
discrete-types-are-sets d =
 Id-collapsibles-are-sets (discrete-is-Id-collapsible d)

being-isolated-is-prop : FunExt → {X : 𝓤 ̇ } (x : X) → is-prop (is-isolated x)
being-isolated-is-prop {𝓤} fe x = prop-criterion γ
 where
  γ : is-isolated x → is-prop (is-isolated x)
  γ i = Π-is-prop (fe 𝓤 𝓤)
         (λ x → sum-of-contradictory-props
                 (local-hedberg _
                   (λ y → decidable-types-are-collapsible (i y)) x)
                 (negations-are-props (fe 𝓤 𝓤₀))
                 (λ p n → n p))

being-isolated'-is-prop : FunExt → {X : 𝓤 ̇ } (x : X) → is-prop (is-isolated' x)
being-isolated'-is-prop {𝓤} fe x = prop-criterion γ
 where
  γ : is-isolated' x → is-prop (is-isolated' x)
  γ i = Π-is-prop (fe 𝓤 𝓤)
         (λ x → sum-of-contradictory-props
                 (local-hedberg' _
                   (λ y → decidable-types-are-collapsible (i y)) x)
                 (negations-are-props (fe 𝓤 𝓤₀))
                 (λ p n → n p))

being-discrete-is-prop : FunExt → {X : 𝓤 ̇ } → is-prop (is-discrete X)
being-discrete-is-prop {𝓤} fe = Π-is-prop (fe 𝓤 𝓤) (being-isolated-is-prop fe)

isolated-points-are-h-isolated : {X : 𝓤 ̇ } (x : X)
                               → is-isolated x
                               → is-h-isolated x
isolated-points-are-h-isolated {𝓤} {X} x i {y} = local-hedberg x (λ y → γ y (i y)) y
 where
  γ : (y : X) → is-decidable (x ＝ y) → Σ f ꞉ (x ＝ y → x ＝ y) , wconstant f
  γ y (inl p) = (λ _ → p) , (λ q r → refl)
  γ y (inr n) = id , (λ q r → 𝟘-elim (n r))

isolated-inl : {X : 𝓤 ̇ } (x : X) (i : is-isolated x) (y : X) (r : x ＝ y)
             → i y ＝ inl r
isolated-inl x i y r =
  equality-cases (i y)
   (λ (p : x ＝ y) (q : i y ＝ inl p)
      → q ∙ ap inl (isolated-points-are-h-isolated x i p r))
   (λ (h : x ≠ y) (q : i y ＝ inr h)
      → 𝟘-elim(h r))

isolated-inr : {X : 𝓤 ̇ }
             → funext 𝓤 𝓤₀
             → (x : X) (i : is-isolated x) (y : X) (n : x ≠ y) → i y ＝ inr n
isolated-inr fe x i y n =
  equality-cases (i y)
   (λ (p : x ＝ y) (q : i y ＝ inl p)
      → 𝟘-elim (n p))
   (λ (m : x ≠ y) (q : i y ＝ inr m)
      → q ∙ ap inr (dfunext fe (λ (p : x ＝ y) → 𝟘-elim (m p))))

\end{code}

The following variation of the above doesn't require function extensionality:

\begin{code}

isolated-inr' : {X : 𝓤 ̇ }
                (x : X)
                (i : is-isolated x)
                (y : X)
                (n : x ≠ y)
              → Σ m ꞉ x ≠ y , i y ＝ inr m
isolated-inr' x i y n =
  equality-cases (i y)
   (λ (p : x ＝ y) (q : i y ＝ inl p)
      → 𝟘-elim (n p))
   (λ (m : x ≠ y) (q : i y ＝ inr m)
      → m , q)

discrete-inl : {X : 𝓤 ̇ }
               (d : is-discrete X)
               (x y : X)
               (r : x ＝ y)
             → d x y ＝ inl r
discrete-inl d x = isolated-inl x (d x)

discrete-inl-refl : {X : 𝓤 ̇ }
                    (d : is-discrete X)
                    (x : X)
                  → d x x ＝ inl refl
discrete-inl-refl {𝓤} {X} d x = discrete-inl d x x refl

discrete-inr : funext 𝓤 𝓤₀
             → {X : 𝓤 ̇ }
               (d : is-discrete X)
               (x y : X)
               (n : ¬ (x ＝ y))
             → d x y ＝ inr n
discrete-inr fe d x = isolated-inr fe x (d x)

isolated-Id-is-prop : {X : 𝓤 ̇ } (x : X)
                    → is-isolated' x
                    → (y : X) → is-prop (y ＝ x)
isolated-Id-is-prop x i =
 local-hedberg' x (λ y → decidable-types-are-collapsible (i y))

lc-maps-reflect-isolatedness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                             → left-cancellable f
                             → (x : X)
                             → is-isolated (f x)
                             → is-isolated x
lc-maps-reflect-isolatedness f l x i y = γ (i (f y))
 where
  γ : (f x ＝ f y) + ¬ (f x ＝ f y) → (x ＝ y) + ¬ (x ＝ y)
  γ (inl p) = inl (l p)
  γ (inr n) = inr (contrapositive (ap f) n)

lc-maps-reflect-discreteness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                             → left-cancellable f
                             → is-discrete Y
                             → is-discrete X
lc-maps-reflect-discreteness f l d x =
 lc-maps-reflect-isolatedness f l x (d (f x))

embeddings-reflect-isolatedness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                → is-embedding f
                                → (x : X)
                                → is-isolated (f x)
                                → is-isolated x
embeddings-reflect-isolatedness f e x i y = lc-maps-reflect-isolatedness f
                                              (embeddings-are-lc f e) x i y

equivs-reflect-isolatedness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                            → is-equiv f
                            → (x : X)
                            → is-isolated (f x)
                            → is-isolated x
equivs-reflect-isolatedness f e = embeddings-reflect-isolatedness f
                                   (equivs-are-embeddings f e)

embeddings-reflect-discreteness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                → is-embedding f
                                → is-discrete Y
                                → is-discrete X
embeddings-reflect-discreteness f e = lc-maps-reflect-discreteness
                                       f
                                       (embeddings-are-lc f e)

equivs-preserve-discreteness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                             → is-equiv f
                             → is-discrete X
                             → is-discrete Y
equivs-preserve-discreteness f e = lc-maps-reflect-discreteness
                                     (inverse f e)
                                     (equivs-are-lc
                                        (inverse f e)
                                        (inverses-are-equivs f e))

equiv-to-discrete : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  → X ≃ Y
                  → is-discrete X
                  → is-discrete Y
equiv-to-discrete (f , e) = equivs-preserve-discreteness f e

𝟙-is-set : is-set (𝟙 {𝓤})
𝟙-is-set = discrete-types-are-sets 𝟙-is-discrete

𝟚-is-set : is-set 𝟚
𝟚-is-set = discrete-types-are-sets 𝟚-is-discrete

ℕ-is-set : is-set ℕ
ℕ-is-set = discrete-types-are-sets ℕ-is-discrete

\end{code}

Added 14th Feb 2020:

\begin{code}

discrete-exponential-has-decidable-emptiness-of-exponent
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → funext 𝓤 𝓥
 → has-two-distinct-points Y
 → is-discrete (X → Y)
 → is-decidable (is-empty X)
discrete-exponential-has-decidable-emptiness-of-exponent
  {𝓤} {𝓥} {X} {Y} fe ((y₀ , y₁) , ne) d = γ
 where
  a : is-decidable ((λ _ → y₀) ＝ (λ _ → y₁))
  a = d (λ _ → y₀) (λ _ → y₁)

  f : is-decidable ((λ _ → y₀) ＝ (λ _ → y₁)) → is-decidable (is-empty X)
  f (inl p) = inl g
   where
    g : is-empty X
    g x = ne q
     where
      q : y₀ ＝ y₁
      q = ap (λ - → - x) p

  f (inr ν) = inr (contrapositive g ν)
   where
    g : is-empty X → (λ _ → y₀) ＝ (λ _ → y₁)
    g ν = dfunext fe (λ x → 𝟘-elim (ν x))

  γ : is-decidable (is-empty X)
  γ = f a

\end{code}

Added 19th Feb 2020:

\begin{code}

maps-of-props-into-h-isolated-points-are-embeddings
 : {P : 𝓤 ̇ } {X : 𝓥 ̇ } (f : P → X)
 → is-prop P
 → ((p : P) → is-h-isolated (f p))
 → is-embedding f
maps-of-props-into-h-isolated-points-are-embeddings f i j q (p , s) (p' , s') =
 to-Σ-＝ (i p p' , j p' _ s')

maps-of-props-into-isolated-points-are-embeddings : {P : 𝓤 ̇ } {X : 𝓥 ̇ }
                                                    (f : P → X)
                                                  → is-prop P
                                                  → ((p : P) → is-isolated (f p))
                                                  → is-embedding f
maps-of-props-into-isolated-points-are-embeddings f i j =
 maps-of-props-into-h-isolated-points-are-embeddings f i
  (λ p → isolated-points-are-h-isolated (f p) (j p))

global-point-is-embedding : {X : 𝓤 ̇ } (f : 𝟙 {𝓥} → X)
                          → is-h-isolated (f ⋆)
                          → is-embedding f
global-point-is-embedding f h =
 maps-of-props-into-h-isolated-points-are-embeddings
  f 𝟙-is-prop h'
   where
    h' : (p : 𝟙) → is-h-isolated (f p)
    h' ⋆ = h

\end{code}

Added 1st May 2024. Wrapper for use with instance arguments:

\begin{code}

record is-discrete' {𝓤 : Universe} (X : 𝓤 ̇ ) : 𝓤 ̇ where
 constructor
  discrete-gives-discrete'
 field
  discrete'-gives-discrete : is-discrete X

open is-discrete' {{...}} public

\end{code}

Added 14th October 2024. We move the notion of weakly isolated point
from its original place FailureOfTotalSeparatedness (added there some
time in 2013 for a paper with Thomas Streicher on the indiscreteness
of the universe and related things). Then we add further properties of
this notion, used both in the module FailureOfTotalSeparatedness and
the module Ordinals.NotationInterpretation.

\begin{code}

is-weakly-isolated : {X : 𝓤 ̇ } (x : X) → 𝓤 ̇
is-weakly-isolated x = ∀ x' → is-decidable (x' ≠ x)

isolated-gives-weakly-isolated : {X : 𝓤 ̇ } (x : X)
                               → is-isolated x
                               → is-weakly-isolated x
isolated-gives-weakly-isolated x i y =
 Cases (i y)
  (λ (e : x ＝ y) → inr (λ (d : y ≠ x) → d (e ⁻¹)))
  (λ (d : x ≠ y) → inl (λ (e : y ＝ x) → d (e ⁻¹)))

equivs-preserve-weak-isolatedness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                    (f : X ≃ Y)
                                  → (x : X)
                                  → is-weakly-isolated x
                                  → is-weakly-isolated (⌜ f ⌝ x)
equivs-preserve-weak-isolatedness f x i y =
 Cases (i (⌜ f ⌝⁻¹ y))
  (λ (a : ⌜ f ⌝⁻¹ y ≠ x)
     → inl (λ (e : y ＝ ⌜ f ⌝ x)
            → a (⌜ f ⌝⁻¹ y         ＝⟨ ap ⌜ f ⌝⁻¹ e ⟩
                 ⌜ f ⌝⁻¹ (⌜ f ⌝ x) ＝⟨ inverses-are-retractions' f x ⟩
                 x                 ∎)))
  (λ (b : ¬ (⌜ f ⌝⁻¹ y ≠ x))
     → inr (λ (d : y ≠ ⌜ f ⌝ x)
            → b (λ (e : ⌜ f ⌝⁻¹ y ＝ x)
                 → d (y                 ＝⟨ (inverses-are-sections' f y)⁻¹ ⟩
                      ⌜ f ⌝ (⌜ f ⌝⁻¹ y) ＝⟨ ap ⌜ f ⌝ e ⟩
                      ⌜ f ⌝ x           ∎))))

equivs-reflect-weak-isolatedness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                 → (f : X ≃ Y)
                                 → (x : X) → is-weakly-isolated (⌜ f ⌝ x)
                                 → is-weakly-isolated x
equivs-reflect-weak-isolatedness f x i = II
 where
  I : is-weakly-isolated (⌜ f ⌝⁻¹ (⌜ f ⌝ x))
  I = equivs-preserve-weak-isolatedness (≃-sym f) (⌜ f ⌝ x) i

  II : is-weakly-isolated x
  II = transport is-weakly-isolated (inverses-are-retractions' f x) I

\end{code}

TODO (in another module). More generally, if an equivalence preserve
some property, it also reflects it.
