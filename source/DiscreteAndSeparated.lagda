Martin Escardo 2011.

(Totally separated types moved to the module TotallySeparated January
2018, and extended.)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module DiscreteAndSeparated where

open import SpartanMLTT

open import Two-Properties
open import Plus-Properties
open import NaturalNumbers-Properties
open import DecidableAndDetachable
open import Two-Prop-Density
open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-Retracts
open import UF-FunExt

is-isolated : {X : 𝓤 ̇ } → X → 𝓤 ̇
is-isolated x = ∀ y → decidable(x ≡ y)

is-perfect : 𝓤 ̇ → 𝓤 ̇
is-perfect X = ¬ Σ \(x : X) → is-isolated x

is-isolated' : {X : 𝓤 ̇ } → X → 𝓤 ̇
is-isolated' x = ∀ y → decidable(y ≡ x)

decidable-eq-sym : {X : 𝓤 ̇ } (x y : X) → decidable (x ≡ y) → decidable (y ≡ x)
decidable-eq-sym x y = cases
                        (λ (p : x ≡ y) → inl (p ⁻¹))
                        (λ (n : ¬(x ≡ y)) → inr (λ (q : y ≡ x) → n (q ⁻¹)))

-is-isolated'-gives-is-isolated : {X : 𝓤 ̇ } (x : X) → is-isolated' x → is-isolated x
-is-isolated'-gives-is-isolated x i' y = cases
                                   (λ (p : y ≡ x) → inl (p ⁻¹))
                                   (λ (n : ¬(y ≡ x)) → inr (λ (p : x ≡ y) → n (p ⁻¹)))
                                   (i' y)

is-isolated'-gives-is-isolated : {X : 𝓤 ̇ } (x : X) → is-isolated' x → is-isolated x
is-isolated'-gives-is-isolated x i' y = decidable-eq-sym y x (i' y)

is-isolated-gives-is-isolated' : {X : 𝓤 ̇ } (x : X) → is-isolated x → is-isolated' x
is-isolated-gives-is-isolated' x i y = decidable-eq-sym x y (i y)

is-discrete : 𝓤 ̇ → 𝓤 ̇
is-discrete X = (x : X) → is-isolated x

\end{code}

Standard examples:

\begin{code}

𝟘-is-discrete : is-discrete (𝟘 {𝓤})
𝟘-is-discrete x y = 𝟘-elim x

𝟙-is-discrete : is-discrete (𝟙 {𝓤})
𝟙-is-discrete * * = inl refl

𝟚-is-discrete : is-discrete 𝟚
𝟚-is-discrete ₀ ₀ = inl refl
𝟚-is-discrete ₀ ₁ = inr (λ (p : ₀ ≡ ₁) → 𝟘-elim (zero-is-not-one p))
𝟚-is-discrete ₁ ₀ = inr (λ (p : ₁ ≡ ₀) → 𝟘-elim (zero-is-not-one (p ⁻¹)))
𝟚-is-discrete ₁ ₁ = inl refl

ℕ-is-discrete : is-discrete ℕ
ℕ-is-discrete 0 0 = inl refl
ℕ-is-discrete 0 (succ n) = inr (λ (p : zero ≡ succ n) → positive-not-zero n (p ⁻¹))
ℕ-is-discrete (succ m) 0 = inr (λ (p : succ m ≡ zero) → positive-not-zero m p)
ℕ-is-discrete (succ m) (succ n) =  step(ℕ-is-discrete m n)
  where
   step : (m ≡ n) + (m ≢ n) → (succ m ≡ succ n) + (succ m ≢ succ n)
   step (inl r) = inl(ap succ r)
   step (inr f) = inr(λ s → f(succ-lc s))

+discrete : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
          → is-discrete X → is-discrete Y → is-discrete (X + Y)
+discrete d e (inl x) (inl x') =
    Cases (d x x')
     (λ (p : x ≡ x') → inl(ap inl p))
     (λ (n : ¬(x ≡ x')) → inr (contrapositive inl-lc n))
+discrete d e (inl x) (inr y) = inr +disjoint
+discrete d e (inr y) (inl x) = inr +disjoint'
+discrete d e (inr y) (inr y') =
    Cases (e y y')
     (λ (p : y ≡ y') → inl(ap inr p))
     (λ (n : ¬(y ≡ y')) → inr (contrapositive inr-lc n))

\end{code}

The closure of discrete types under Σ is proved in the module
UF-SetExamples (as this requires to first prove that discrete types
are sets).

General properties:

\begin{code}

discrete-is-cotransitive : {X : 𝓤 ̇ }
                         → is-discrete X → {x y z : X} → x ≢ y → (x ≢ z) + (z ≢ y)
discrete-is-cotransitive d {x} {y} {z} φ = f(d x z)
 where
  f : (x ≡ z) + (x ≢ z) → (x ≢ z) + (z ≢ y)
  f (inl r) = inr (λ s → φ(r ∙ s))
  f (inr γ) = inl γ

retract-discrete-discrete : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                         → retract Y of X → is-discrete X → is-discrete Y
retract-discrete-discrete (f , (s , φ)) d y y' = g (d (s y) (s y'))
 where
  g : decidable (s y ≡ s y') → decidable (y ≡ y')
  g (inl p) = inl ((φ y) ⁻¹ ∙ ap f p ∙ φ y')
  g (inr u) = inr (contrapositive (ap s) u)

𝟚-retract-of-discrete : {X : 𝓤 ̇ } {x₀ x₁ : X} → x₀ ≢ x₁ → is-discrete X → retract 𝟚 of X
𝟚-retract-of-discrete {𝓤} {X} {x₀} {x₁} ne d = r , (s , rs)
 where
  r : X → 𝟚
  r = pr₁ (characteristic-function (d x₀))
  φ : (x : X) → (r x ≡ ₀ → x₀ ≡ x) × (r x ≡ ₁ → ¬ (x₀ ≡ x))
  φ = pr₂ (characteristic-function (d x₀))
  s : 𝟚 → X
  s ₀ = x₀
  s ₁ = x₁
  rs : (n : 𝟚) → r (s n) ≡ n
  rs ₀ = different-from-₁-equal-₀ (λ p → pr₂ (φ x₀) p refl)
  rs ₁ = different-from-₀-equal-₁ λ p → 𝟘-elim (ne (pr₁ (φ x₁) p))

\end{code}

Separated types form an exponential ideal, assuming
extensionality. More generally:

\begin{code}

is-separated : 𝓤 ̇ → 𝓤 ̇
is-separated X = (x y : X) → ¬¬(x ≡ y) → x ≡ y

Π-is-separated : funext 𝓤 𝓥 → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
               → ((x : X) → is-separated(Y x)) → is-separated(Π Y)
Π-is-separated fe s f g h = dfunext fe lemma₂
 where
  lemma₀ : f ≡ g → ∀ x → f x ≡ g x
  lemma₀ r x = ap (λ - → - x) r
  lemma₁ : ∀ x → ¬¬(f x ≡ g x)
  lemma₁ = double-negation-unshift(¬¬-functor lemma₀ h)
  lemma₂ : ∀ x → f x ≡ g x
  lemma₂ x =  s x (f x) (g x) (lemma₁ x)

discrete-is-separated : {X : 𝓤 ̇ } → is-discrete X → is-separated X
discrete-is-separated d x y = ¬¬-elim(d x y)

𝟚-is-separated : is-separated 𝟚
𝟚-is-separated = discrete-is-separated 𝟚-is-discrete

subtype-of-separated-is-separated : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (m : X → Y)
                                  → left-cancellable m → is-separated Y → is-separated X
subtype-of-separated-is-separated {𝓤} {𝓥} {X} m i s x x' e = i (s (m x) (m x') (¬¬-functor (ap m) e))

\end{code}

The following is an apartness relation when Y is separated, but we
define it without this assumption. (Are all types separated? See
below.)

\begin{code}

infix 21 _♯_

_♯_ : {X : 𝓤 ̇ } → {Y : X → 𝓥 ̇ } → (f g : (x : X) → Y x) → 𝓤 ⊔ 𝓥 ̇
f ♯ g = Σ \x → f x ≢ g x


apart-is-different : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                   → {f g : (x : X) → Y x} → f ♯ g → f ≢ g
apart-is-different (x , φ) r = φ (ap (λ - → - x) r)


apart-is-symmetric : {X : 𝓤 ̇ } → {Y : X → 𝓥 ̇ }
                   → {f g : (x : X) → Y x} → f ♯ g → g ♯ f
apart-is-symmetric (x , φ)  = (x , (φ ∘ _⁻¹))

apart-is-cotransitive : {X : 𝓤 ̇ } → {Y : X → 𝓥 ̇ }
                     → ((x : X) → is-discrete(Y x))
                     → (f g h : (x : X) → Y x)
                     → f ♯ g → f ♯ h  +  h ♯ g
apart-is-cotransitive d f g h (x , φ)  = lemma₁(lemma₀ φ)
 where
  lemma₀ : f x ≢ g x → (f x ≢ h x)  +  (h x ≢ g x)
  lemma₀ = discrete-is-cotransitive (d x)
  lemma₁ : (f x ≢ h x) + (h x ≢ g x) → f ♯ h  +  h ♯ g
  lemma₁ (inl γ) = inl (x , γ)
  lemma₁ (inr δ) = inr (x , δ)

\end{code}

We now consider two cases which render the apartness relation ♯ tight,
assuming extensionality:

\begin{code}

tight : {X : 𝓤 ̇ } → funext 𝓤 𝓥 → {Y : X → 𝓥 ̇ }
      → ((x : X) → is-separated(Y x))
      → (f g : (x : X) → Y x)
      → ¬(f ♯ g) → f ≡ g
tight fe s f g h = dfunext fe lemma₁
 where
  lemma₀ : ∀ x → ¬¬(f x ≡ g x)
  lemma₀ = not-Σ-implies-Π-not h
  lemma₁ : ∀ x → f x ≡ g x
  lemma₁ x = (s x (f x) (g x)) (lemma₀ x)

tight' : {X : 𝓤 ̇ } → funext 𝓤 𝓥 → {Y : X → 𝓥 ̇ }
       → ((x : X) → is-discrete(Y x)) → (f g : (x : X) → Y x) → ¬(f ♯ g) → f ≡ g
tight' fe d = tight fe (λ x → discrete-is-separated(d x))

\end{code}

What about sums? The special case they reduce to binary products is
easy:

\begin{code}

binary-product-is-separated : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                            → is-separated X → is-separated Y → is-separated(X × Y)
binary-product-is-separated s t (x , y) (x' , y') φ =
 lemma(lemma₀ φ)(lemma₁ φ)
 where
  lemma₀ : ¬¬((x , y) ≡ (x' , y')) → x ≡ x'
  lemma₀ = (s x x') ∘ ¬¬-functor(ap pr₁)
  lemma₁ : ¬¬((x , y) ≡ (x' , y')) → y ≡ y'
  lemma₁ = (t y y') ∘ ¬¬-functor(ap pr₂)
  lemma : x ≡ x' → y ≡ y' → (x , y) ≡ (x' , y')
  lemma = ap₂ (_,_)

\end{code}

This proof doesn't work for general dependent sums, because, among
other things, (ap pr₁) doesn't make sense in that case.  A different
special case is also easy:

\begin{code}

binary-sum-is-separated : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                        → is-separated X → is-separated Y → is-separated(X + Y)
binary-sum-is-separated {𝓤} {𝓥} {X} {Y} s t (inl x) (inl x') = lemma
 where
  claim : inl x ≡ inl x' → x ≡ x'
  claim = ap p
   where
    p : X + Y → X
    p(inl u) = u
    p(inr v) = x
  lemma : ¬¬(inl x ≡ inl x') → inl x ≡ inl x'
  lemma = ap inl ∘ s x x' ∘ ¬¬-functor claim

binary-sum-is-separated s t (inl x) (inr y) =  λ φ → 𝟘-elim(φ +disjoint )
binary-sum-is-separated s t (inr y) (inl x)  = λ φ → 𝟘-elim(φ(+disjoint ∘ _⁻¹))
binary-sum-is-separated {𝓤} {𝓥} {X} {Y} s t (inr y) (inr y') = lemma
 where
  claim : inr y ≡ inr y' → y ≡ y'
  claim = ap q
   where
    q : X + Y → Y
    q(inl u) = y
    q(inr v) = v
  lemma : ¬¬(inr y ≡ inr y') → inr y ≡ inr y'
  lemma = (ap inr) ∘ (t y y') ∘ ¬¬-functor claim

⊥-⊤-density' : funext 𝓤 𝓤 → propext 𝓤
             → ∀ {𝓥} {X : 𝓥 ̇ }
             → is-separated X
             → (f : Ω 𝓤 → X) → f ⊥ ≡ f ⊤ → constant f
⊥-⊤-density' fe pe s f r p q = g p ∙ (g q)⁻¹
  where
    a : ∀ p → ¬¬(f p ≡ f ⊤)
    a p t = no-truth-values-other-than-⊥-or-⊤ fe pe (p , (b , c))
      where
        b : p ≢ ⊥
        b u = t (ap f u ∙ r)
        c : p ≢ ⊤
        c u = t (ap f u)
    g : ∀ p → f p ≡ f ⊤
    g p = s (f p) (f ⊤) (a p)

\end{code}

21 March 2018

\begin{code}

qinvs-preserve-isolatedness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → qinv f
                            → (x : X) → is-isolated x → is-isolated (f x)
qinvs-preserve-isolatedness {𝓤} {𝓥} {X} {Y} f (g , ε , η) x i y = h (i (g y))
 where
  h : decidable (x ≡ g y) → decidable (f x ≡ y)
  h (inl p) = inl (ap f p ∙ η y)
  h (inr u) = inr (contrapositive (λ (q : f x ≡ y) → (ε x)⁻¹ ∙ ap g q) u)

equivs-preserve-isolatedness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f
                             → (x : X) → is-isolated x → is-isolated (f x)
equivs-preserve-isolatedness f e = qinvs-preserve-isolatedness f (equivs-are-qinvs f e)

new-point-is-isolated : {X : 𝓤 ̇ } → is-isolated {𝓤 ⊔ 𝓥} {X + 𝟙 {𝓥}} (inr *)
new-point-is-isolated {𝓤} {𝓥} {X} = h
 where
  h :  (y : X + 𝟙) → decidable (inr * ≡ y)
  h (inl x) = inr +disjoint'
  h (inr *) = inl refl

\end{code}

Back to old stuff:

\begin{code}

≡-indicator :  (m : ℕ) → Σ \(p : ℕ → 𝟚) → (n : ℕ) → (p n ≡ ₀ → m ≢ n) × (p n ≡ ₁ → m ≡ n)
≡-indicator m = co-characteristic-function (ℕ-is-discrete m)

χ≡ : ℕ → ℕ → 𝟚
χ≡ m = pr₁ (≡-indicator m)

χ≡-spec : (m n : ℕ) → (χ≡ m n ≡ ₀ → m ≢ n) × (χ≡ m n ≡ ₁ → m ≡ n)
χ≡-spec m = pr₂ (≡-indicator m)

_≡[ℕ]_ : ℕ → ℕ → 𝓤₀ ̇
m ≡[ℕ] n = (χ≡ m n) ≡ ₁

infix  30 _≡[ℕ]_

≡-agrees-with-≡[ℕ] : (m n : ℕ) → m ≡ n ⇔ m ≡[ℕ] n
≡-agrees-with-≡[ℕ] m n = (λ r → different-from-₀-equal-₁ (λ s → pr₁(χ≡-spec m n) s r)) , pr₂(χ≡-spec m n)

≢-indicator :  (m : ℕ) → Σ \(p : ℕ → 𝟚) → (n : ℕ) → (p n ≡ ₀ → m ≡ n) × (p n ≡ ₁ → m ≢ n)
≢-indicator m = indicator(ℕ-is-discrete m)

χ≢ : ℕ → ℕ → 𝟚
χ≢ m = pr₁ (≢-indicator m)

χ≢-spec : (m n : ℕ) → (χ≢ m n ≡ ₀ → m ≡ n) × (χ≢ m n ≡ ₁ → m ≢ n)
χ≢-spec m = pr₂ (≢-indicator m)

_≠_ : ℕ → ℕ → 𝓤₀ ̇
m ≠ n = (χ≢ m n) ≡ ₁

infix  30 _≠_

≠-agrees-with-≢ : (m n : ℕ) → m ≠ n ⇔ m ≢ n
≠-agrees-with-≢ m n = pr₂(χ≢-spec m n) , (λ d → different-from-₀-equal-₁ (contrapositive(pr₁(χ≢-spec m n)) d))

\end{code}
