Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module MGS-hlevels where

open import MGS-Basic-UF public

_is-of-hlevel_ : 𝓤 ̇ → ℕ → 𝓤 ̇
X is-of-hlevel 0        = is-singleton X
X is-of-hlevel (succ n) = (x x' : X) → ((x ≡ x') is-of-hlevel n)

wconstant : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
wconstant f = (x x' : domain f) → f x ≡ f x'

wconstant-endomap : 𝓤 ̇ → 𝓤 ̇
wconstant-endomap X = Σ f ꞉ (X → X), wconstant f

wcmap : (X : 𝓤 ̇ ) → wconstant-endomap X → (X → X)
wcmap X (f , w) = f

wcmap-constancy : (X : 𝓤 ̇ ) (c : wconstant-endomap X)
                → wconstant (wcmap X c)
wcmap-constancy X (f , w) = w

Hedberg : {X : 𝓤 ̇ } (x : X)
        → ((y : X) → wconstant-endomap (x ≡ y))
        → (y : X) → is-subsingleton (x ≡ y)

Hedberg {𝓤} {X} x c y p q =

 p                         ≡⟨ a y p ⟩
 (f x (refl x))⁻¹ ∙ f y p  ≡⟨ ap (λ - → (f x (refl x))⁻¹ ∙ -) (κ y p q) ⟩
 (f x (refl x))⁻¹ ∙ f y q  ≡⟨ (a y q)⁻¹ ⟩
 q                         ∎

 where
  f : (y : X) → x ≡ y → x ≡ y
  f y = wcmap (x ≡ y) (c y)

  κ : (y : X) (p q : x ≡ y) → f y p ≡ f y q
  κ y = wcmap-constancy (x ≡ y) (c y)

  a : (y : X) (p : x ≡ y) → p ≡ (f x (refl x))⁻¹ ∙ f y p
  a x (refl x) = (⁻¹-left∙ (f x (refl x)))⁻¹

wconstant-≡-endomaps : 𝓤 ̇ → 𝓤 ̇
wconstant-≡-endomaps X = (x y : X) → wconstant-endomap (x ≡ y)

sets-have-wconstant-≡-endomaps : (X : 𝓤 ̇ ) → is-set X → wconstant-≡-endomaps X
sets-have-wconstant-≡-endomaps X s x y = (f , κ)
 where
  f : x ≡ y → x ≡ y
  f p = p

  κ : (p q : x ≡ y) → f p ≡ f q
  κ p q = s x y p q

types-with-wconstant-≡-endomaps-are-sets : (X : 𝓤 ̇ )
                                         → wconstant-≡-endomaps X → is-set X

types-with-wconstant-≡-endomaps-are-sets X c x = Hedberg x
                                                  (λ y → wcmap (x ≡ y) (c x y) ,
                                                   wcmap-constancy (x ≡ y) (c x y))

subsingletons-have-wconstant-≡-endomaps : (X : 𝓤 ̇ )
                                        → is-subsingleton X
                                        → wconstant-≡-endomaps X

subsingletons-have-wconstant-≡-endomaps X s x y = (f , κ)
 where
  f : x ≡ y → x ≡ y
  f p = s x y

  κ : (p q : x ≡ y) → f p ≡ f q
  κ p q = refl (s x y)

subsingletons-are-sets : (X : 𝓤 ̇ ) → is-subsingleton X → is-set X
subsingletons-are-sets X s = types-with-wconstant-≡-endomaps-are-sets X
                               (subsingletons-have-wconstant-≡-endomaps X s)

singletons-are-sets : (X : 𝓤 ̇ ) → is-singleton X → is-set X
singletons-are-sets X = subsingletons-are-sets X ∘ singletons-are-subsingletons X

𝟘-is-set : is-set 𝟘
𝟘-is-set = subsingletons-are-sets 𝟘 𝟘-is-subsingleton

𝟙-is-set : is-set 𝟙
𝟙-is-set = subsingletons-are-sets 𝟙 𝟙-is-subsingleton

subsingletons-are-of-hlevel-1 : (X : 𝓤 ̇ )
                              → is-subsingleton X
                              → X is-of-hlevel 1

subsingletons-are-of-hlevel-1 X = g
 where
  g : ((x y : X) → x ≡ y) → (x y : X) → is-singleton (x ≡ y)
  g t x y = t x y , subsingletons-are-sets X t x y (t x y)

types-of-hlevel-1-are-subsingletons : (X : 𝓤 ̇ )
                                    → X is-of-hlevel 1
                                    → is-subsingleton X

types-of-hlevel-1-are-subsingletons X = f
 where
  f : ((x y : X) → is-singleton (x ≡ y)) → (x y : X) → x ≡ y
  f s x y = center (x ≡ y) (s x y)

sets-are-of-hlevel-2 : (X : 𝓤 ̇ ) → is-set X → X is-of-hlevel 2
sets-are-of-hlevel-2 X = g
 where
  g : ((x y : X) → is-subsingleton (x ≡ y)) → (x y : X) → (x ≡ y) is-of-hlevel 1
  g t x y = subsingletons-are-of-hlevel-1 (x ≡ y) (t x y)

types-of-hlevel-2-are-sets : (X : 𝓤 ̇ ) → X is-of-hlevel 2 → is-set X
types-of-hlevel-2-are-sets X = f
 where
  f : ((x y : X) → (x ≡ y) is-of-hlevel 1) → (x y : X) → is-subsingleton (x ≡ y)
  f s x y = types-of-hlevel-1-are-subsingletons (x ≡ y) (s x y)

hlevel-upper : (X : 𝓤 ̇ ) (n : ℕ) → X is-of-hlevel n → X is-of-hlevel (succ n)
hlevel-upper X zero = γ
 where
  γ : is-singleton X → (x y : X) → is-singleton (x ≡ y)
  γ h x y = p , subsingletons-are-sets X k x y p
   where
    k : is-subsingleton X
    k = singletons-are-subsingletons X h

    p : x ≡ y
    p = k x y

hlevel-upper X (succ n) = λ h x y → hlevel-upper (x ≡ y) n (h x y)

_has-minimal-hlevel_ : 𝓤 ̇ → ℕ → 𝓤 ̇
X has-minimal-hlevel 0        = X is-of-hlevel 0
X has-minimal-hlevel (succ n) = (X is-of-hlevel (succ n)) × ¬ (X is-of-hlevel n)

_has-minimal-hlevel-∞ : 𝓤 ̇ → 𝓤 ̇
X has-minimal-hlevel-∞ = (n : ℕ) → ¬ (X is-of-hlevel n)

pointed-types-have-wconstant-endomap : {X : 𝓤 ̇ } → X → wconstant-endomap X
pointed-types-have-wconstant-endomap x = ((λ y → x) , (λ y y' → refl x))

empty-types-have-wconstant-endomap : {X : 𝓤 ̇ } → is-empty X → wconstant-endomap X
empty-types-have-wconstant-endomap e = (id , (λ x x' → !𝟘 (x ≡ x') (e x)))

decidable-has-wconstant-endomap : {X : 𝓤 ̇ } → decidable X → wconstant-endomap X
decidable-has-wconstant-endomap (inl x) = pointed-types-have-wconstant-endomap x
decidable-has-wconstant-endomap (inr e) = empty-types-have-wconstant-endomap e

hedberg-lemma : {X : 𝓤 ̇ } → has-decidable-equality X → wconstant-≡-endomaps X
hedberg-lemma {𝓤} {X} d x y = decidable-has-wconstant-endomap (d x y)

hedberg : {X : 𝓤 ̇ } → has-decidable-equality X → is-set X
hedberg {𝓤} {X} d = types-with-wconstant-≡-endomaps-are-sets X (hedberg-lemma d)

ℕ-is-set : is-set ℕ
ℕ-is-set = hedberg ℕ-has-decidable-equality

𝟚-is-set : is-set 𝟚
𝟚-is-set = hedberg 𝟚-has-decidable-equality

\end{code}
