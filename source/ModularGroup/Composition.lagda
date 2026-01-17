Lane Biocini 17 October 2023

Now we go on to define Composition and Inversion. We type '\bu' for
the compose operator and the inverse uses the regular minus.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module ModularGroup.Composition where

open import MLTT.Spartan
open import ModularGroup.Type
open import ModularGroup.Properties using (s-quotiented; r-quotiented;
 s-left-cancellable; r-left-cancellable; r²-left-cancellable)

open import UF.Base using (transport₂)

_•_ : 𝓜 → 𝓜 → 𝓜
E • b = b
S • b = s b
𝒔 x • b = s (θ x • b)
𝒓 x • b = r (η x • b)
𝒓² x • b = r² (η x • b)

infixr 31 _•_

_-¹ : 𝓜 → 𝓜
E -¹ = E
S -¹ = S
𝒔 x -¹ = θ x -¹ • S
𝒓 x -¹ = η x -¹ • R²
𝒓² x -¹ = η x -¹ • R

infix 32 _-¹

\end{code}

Proofs for composition

\begin{code}

head-tail : (λ x → head x • tail x) ∼ id
head-tail E = refl
head-tail S = refl
head-tail (𝒔 x) = refl
head-tail (𝒓 x) = refl
head-tail (𝒓² x) = refl

s-left : (a b : 𝓜) → s a • b ＝ s (a • b)
s-left E b = refl
s-left S b = s-quotiented b
s-left (𝒔 x) b = s-quotiented (θ x • b)
s-left (θ x) b = refl

r-left : (a b : 𝓜) → r a • b ＝ r (a • b)
r-left (η x) b = refl
r-left (𝒓 x) b = refl
r-left (𝒓² x) b = r-quotiented (η x • b)

r²-left : (a b : 𝓜) → r² a • b ＝ r² (a • b)
r²-left a b =
 r (r a) • b   ＝⟨ r-left (r a) b ⟩
 r (r a • b)   ＝⟨ ap r (r-left a b) ⟩
 r (r (a • b)) ∎

compose-associative : associative _•_
compose-associative E b c = refl
compose-associative S b c = s-left b c
compose-associative (𝒔 x) b c =
 s (θ x • b) • c   ＝⟨ s-left (θ x • b) c ⟩
 s ((θ x • b) • c) ＝⟨ ap s (compose-associative (θ x) b c) ⟩
 s (θ x • b • c)   ∎
compose-associative (𝒓 x) b c =
 r (η x • b) • c   ＝⟨ r-left (η x • b) c ⟩
 r ((η x • b) • c) ＝⟨ ap r (compose-associative (η x) b c) ⟩
 r (η x • b • c)   ∎
compose-associative (𝒓² x) b c =
 r (r (η x • b)) • c   ＝⟨ r²-left (η x • b) c ⟩
 r (r ((η x • b) • c)) ＝⟨ ap r² (compose-associative (η x) b c) ⟩
 r (r (η x • b • c))   ∎

compose-left-neutral : left-neutral E _•_
compose-left-neutral x = refl

compose-right-neutral : right-neutral E _•_
compose-right-neutral E = refl
compose-right-neutral S = refl
compose-right-neutral (𝒔 x) = ap s (compose-right-neutral (θ x))
compose-right-neutral (𝒓 x) = ap r (compose-right-neutral (η x))
compose-right-neutral (𝒓² x) = ap r² (compose-right-neutral (η x))

\end{code}

Proofs of properties for inversion

\begin{code}

s-inverse : (x : 𝓜) → (s x) -¹ ＝ x -¹ • S
s-inverse E = refl
s-inverse S = refl
s-inverse (𝒔 x) =
 θ x -¹           ＝⟨ compose-right-neutral (θ x -¹) ⁻¹ ⟩
 θ x -¹ • E       ＝⟨ compose-associative (θ x -¹) S S ⁻¹ ⟩
 (θ x -¹ • S) • S ∎
s-inverse (θ x) = refl

r-inverse : (x : 𝓜) → (r x) -¹ ＝ x -¹ • R²
r-inverse E = refl
r-inverse S = refl
r-inverse (𝒔 x) = refl
r-inverse (𝒓 x) = compose-associative (η x -¹) R² R² ⁻¹
r-inverse (𝒓² x) =
 η x -¹            ＝⟨ compose-right-neutral (η x -¹) ⁻¹ ⟩
 η x -¹ • E        ＝⟨ compose-associative (η x -¹) R R² ⁻¹ ⟩
 (η x -¹ • R) • R² ∎

r²-inverse : (x : 𝓜) → (r² x) -¹ ＝ x -¹ • R
r²-inverse x =
 r (r x) -¹       ＝⟨ r-inverse (r x) ⟩
 r x -¹ • R²      ＝⟨ ap (_• R²) (r-inverse x) ⟩
 (x -¹ • R²) • R² ＝⟨ compose-associative (x -¹) R² R² ⟩
 x -¹ • R         ∎

s-inverse-right : (x : 𝓜) → (x • S) -¹ ＝ s (x -¹)
s-inverse-right E = refl
s-inverse-right S = refl
s-inverse-right (𝒔 x) =
 s (θ x • S) -¹   ＝⟨ s-inverse (θ x • S) ⟩
 (θ x • S) -¹ • S ＝⟨ ap (_• S) (s-inverse-right (θ x)) ⟩
 s (θ x -¹) • S   ＝⟨ compose-associative S (θ x -¹) S ⟩
 s (θ x -¹ • S)   ∎
s-inverse-right (𝒓 x) =
 r (η x • S) -¹    ＝⟨ r-inverse (η x • S) ⟩
 (η x • S) -¹ • R² ＝⟨ ap (_• R²) (s-inverse-right (η x)) ⟩
 s (η x -¹) • R²   ＝⟨ compose-associative S (η x -¹) R² ⟩
 s (η x -¹ • R²)   ∎
s-inverse-right (𝒓² x) =
 r (r (η x • S)) -¹ ＝⟨ r²-inverse (η x • S) ⟩
 (η x • S) -¹ • R   ＝⟨ ap (_• R) (s-inverse-right (η x)) ⟩
 s (η x -¹) • R     ＝⟨ compose-associative S (η x -¹) R ⟩
 s (η x -¹ • R)     ∎

r-inverse-right : (x : 𝓜) → (x • R²) -¹ ＝ r (x -¹)
r-inverse-right E = refl
r-inverse-right S = refl
r-inverse-right (𝒔 x) =
 s (θ x • R²) -¹   ＝⟨ s-inverse (θ x • R²) ⟩
 (θ x • R²) -¹ • S ＝⟨ ap (_• S) (r-inverse-right (θ x)) ⟩
 r (θ x -¹) • S    ＝⟨ compose-associative R (θ x -¹) S ⟩
 r (θ x -¹ • S)    ∎
r-inverse-right (𝒓 x) =
 r (η x • R²) -¹    ＝⟨ r-inverse (η x • R²) ⟩
 (η x • R²) -¹ • R² ＝⟨ ap (_• R²) (r-inverse-right (η x)) ⟩
 r (η x -¹) • R²    ＝⟨ compose-associative R (η x -¹) R² ⟩
 r (η x -¹ • R²)    ∎
r-inverse-right (𝒓² x) =
 r (r (η x • R²)) -¹ ＝⟨ r²-inverse (η x • R²) ⟩
 (η x • R²) -¹ • R   ＝⟨ ap (_• R) (r-inverse-right (η x)) ⟩
 r (η x -¹) • R      ＝⟨ compose-associative R (η x -¹) R ⟩
 r (η x -¹ • R)      ∎

r²-inverse-right : (x : 𝓜) → (x • R) -¹ ＝ r² (x -¹)
r²-inverse-right E = refl
r²-inverse-right S = refl
r²-inverse-right (𝒔 x) =
 s (θ x • R) -¹     ＝⟨ s-inverse (θ x • R) ⟩
 (θ x • R) -¹ • S   ＝⟨ ap (_• S) (r²-inverse-right (θ x)) ⟩
 r (r (θ x -¹)) • S ＝⟨ compose-associative R² (θ x -¹) S ⟩
 r (r (θ x -¹ • S)) ∎
r²-inverse-right (𝒓 x) =
 r (η x • R) -¹      ＝⟨ r-inverse (η x • R) ⟩
 (η x • R) -¹ • R²   ＝⟨ ap (_• R²) (r²-inverse-right (η x)) ⟩
 r (r (η x -¹)) • R² ＝⟨ compose-associative R² (η x -¹) R² ⟩
 r (r (η x -¹ • R²)) ∎
r²-inverse-right (𝒓² x) =
 r (r (η x • R)) -¹ ＝⟨ r²-inverse (η x • R) ⟩
 (η x • R) -¹ • R   ＝⟨ ap (_• R) (r²-inverse-right (η x)) ⟩
 r (r (η x -¹)) • R ＝⟨ compose-associative R² (η x -¹) R ⟩
 r (r (η x -¹ • R)) ∎

inverse-involutive : involutive _-¹
inverse-involutive E = refl
inverse-involutive S = refl
inverse-involutive (𝒔 x) =
 (θ x -¹ • S) -¹ ＝⟨ s-inverse-right (θ x -¹) ⟩
 s ((θ x -¹) -¹) ＝⟨ ap s (inverse-involutive (θ x)) ⟩
 𝒔 x             ∎
inverse-involutive (𝒓 x) =
 (η x -¹ • R²) -¹ ＝⟨ r-inverse-right (η x -¹) ⟩
 r ((η x -¹) -¹)  ＝⟨ ap r (inverse-involutive (η x)) ⟩
 𝒓 x              ∎
inverse-involutive (𝒓² x) =
 (η x -¹ • R) -¹     ＝⟨ r²-inverse-right (η x -¹) ⟩
 r (r ((η x -¹) -¹)) ＝⟨ ap r² (inverse-involutive (η x)) ⟩
 𝒓² x                ∎

inversion-left-cancellable : left-cancellable _-¹
inversion-left-cancellable {x} {y} p =
 x         ＝⟨ inverse-involutive x ⁻¹ ⟩
 (x -¹) -¹ ＝⟨ ap _-¹ p ⟩
 (y -¹) -¹ ＝⟨ inverse-involutive y ⟩
 y         ∎

inverse-left-cancel : (x : 𝓜) → x -¹ • x ＝ E
inverse-left-cancel E = refl
inverse-left-cancel S = refl
inverse-left-cancel (𝒔 x) =
 (θ x -¹ • S) • 𝒔 x ＝⟨ compose-associative (θ x -¹) S (𝒔 x) ⟩
 θ x -¹ • θ x       ＝⟨ inverse-left-cancel (θ x) ⟩
 E                  ∎
inverse-left-cancel (𝒓 x) =
 (η x -¹ • R²) • 𝒓 x ＝⟨ compose-associative (η x -¹) (R²) (𝒓 x) ⟩
 η x -¹ • η x        ＝⟨ ap ((η x -¹) •_) (r-quotiented (η x) ⁻¹) ⟩
 η x -¹ • η x        ＝⟨ inverse-left-cancel (η x) ⟩
 E                   ∎
inverse-left-cancel (𝒓² x) =
 (η x -¹ • R) • 𝒓² x ＝⟨ compose-associative (η x -¹) R (𝒓² x) ⟩
 η x -¹ • η x        ＝⟨ inverse-left-cancel (η x) ⟩
 E                   ∎

inverse-right-cancel : (x : 𝓜) → x • x -¹ ＝ E
inverse-right-cancel E = refl
inverse-right-cancel S = refl
inverse-right-cancel (𝒔 x) =
 s (θ x • θ x -¹ • S)   ＝⟨ ap s (compose-associative (θ x) (θ x -¹) S ⁻¹) ⟩
 s ((θ x • θ x -¹) • S) ＝⟨ ap (λ u → s (u • S)) (inverse-right-cancel (θ x)) ⟩
 E                      ∎
inverse-right-cancel (𝒓 x) =
 r (η x • η x -¹ • R²)   ＝⟨ ap r (compose-associative (η x) (η x -¹) R² ⁻¹) ⟩
 r ((η x • η x -¹) • R²) ＝⟨ ap (λ u → r (u • R²)) (inverse-right-cancel (η x)) ⟩
 E                       ∎
inverse-right-cancel (𝒓² x) =
 r (r (η x • η x -¹ • R))   ＝⟨ ap r² (compose-associative (η x) (η x -¹) R ⁻¹) ⟩
 r (r ((η x • η x -¹) • R)) ＝⟨ ap (λ u → r² (u • R)) (inverse-right-cancel (η x)) ⟩
 E                          ∎

𝓜-invertible : (x : 𝓜) → Σ x' ꞉ 𝓜 , (x' • x ＝ E) × (x • x' ＝ E)
𝓜-invertible x = x -¹ , inverse-left-cancel x , inverse-right-cancel x

compose-left-cancellable : (a : 𝓜) → left-cancellable (a •_)
compose-left-cancellable a {x} {y} p =
 x                ＝⟨ ap (_• x) (inverse-left-cancel a ⁻¹) ⟩
 ((a -¹) • a) • x ＝⟨ compose-associative (a -¹) a x ⟩
 (a -¹) • a • x   ＝⟨ ap (a -¹ •_) p ⟩
 (a -¹) • a • y   ＝⟨ compose-associative (a -¹) a y ⁻¹ ⟩
 ((a -¹) • a) • y ＝⟨ ap (_• y) (inverse-left-cancel a) ⟩
 y                ∎

compose-left-cancellable' : (a : 𝓜) → left-cancellable (a •_)
compose-left-cancellable' E = id
compose-left-cancellable' S = s-left-cancellable
compose-left-cancellable' (𝒔 x) = compose-left-cancellable' (θ x)
                                ∘ s-left-cancellable
compose-left-cancellable' (𝒓 x) = compose-left-cancellable' (η x)
                                ∘ r-left-cancellable
compose-left-cancellable' (𝒓² x) = compose-left-cancellable' (η x)
                                 ∘ r²-left-cancellable

compose-right-cancellable : (a : 𝓜) → right-cancellable (_• a)
compose-right-cancellable a g h p y =
 g y                  ＝⟨ ap g (compose-right-neutral y) ⁻¹ ⟩
 g (y • E)            ＝⟨ ap (g ∘ (y •_)) (inverse-left-cancel a ⁻¹) ⟩
 g (y • (a -¹) • a)   ＝⟨ ap g (compose-associative y (a -¹) a) ⁻¹ ⟩
 g ((y • (a -¹)) • a) ＝⟨ p (y • a -¹) ⟩
 h ((y • (a -¹)) • a) ＝⟨ ap h (compose-associative y (a -¹) a) ⟩
 h (y • (a -¹) • a)   ＝⟨ ap (h ∘ y •_) (inverse-left-cancel a) ⟩
 h (y • E)            ＝⟨ ap h (compose-right-neutral y) ⟩
 h y                  ∎

compose-right-cancellable' : (a b x : 𝓜) → a • x ＝ b • x → a ＝ b
compose-right-cancellable' a b x p =
 a              ＝⟨ compose-right-neutral a ⁻¹ ⟩
 a • E          ＝⟨ ap (a •_) (inverse-right-cancel x ⁻¹) ⟩
 a • x • x -¹   ＝⟨ compose-associative a x (x -¹) ⁻¹ ⟩
 (a • x) • x -¹ ＝⟨ ap (_• x -¹) p ⟩
 (b • x) • x -¹ ＝⟨ compose-associative b x (x -¹) ⟩
 b • x • x -¹   ＝⟨ ap (b •_) (inverse-right-cancel x) ⟩
 b • E          ＝⟨ compose-right-neutral b ⟩
 b              ∎

\end{code}

Elementary proofs about the algebra of 𝓜

\begin{code}

id-is-inverse : (x y : 𝓜) → x • y ＝ E → y ＝ x -¹
id-is-inverse x y p =
 y              ＝⟨ ap (_• y) (inverse-left-cancel x) ⁻¹ ⟩
 (x -¹ • x) • y ＝⟨ compose-associative (x -¹) x y ⟩
 x -¹ • x • y   ＝⟨ ap (x -¹ •_) p ⟩
 x -¹ • E       ＝⟨ compose-right-neutral (x -¹) ⟩
 x -¹           ∎

compose-identifications : (a b c d : 𝓜)
                     → a ＝ b
                     → c ＝ d
                     → a • c ＝ b • d
compose-identifications a b c d p q = ap (_• c) p ∙ ap (b •_) q

compose-infer-left : (a x y : 𝓜) → a • x ＝ y → a ＝ y • x -¹
compose-infer-left a x y p = transport (λ u → a ＝ u • x -¹) p
 (a              ＝⟨ compose-right-neutral a ⁻¹ ⟩
  a • E          ＝⟨ ap (a •_) (inverse-right-cancel x ⁻¹) ⟩
  a • x • x -¹   ＝⟨ compose-associative a x (x -¹) ⁻¹ ⟩
  (a • x) • x -¹ ∎)

compose-infer-right : (a x y : 𝓜) → x • a ＝ y → a ＝ x -¹ • y
compose-infer-right a x y p = transport (λ u → a ＝ x -¹ • u ) p
 (a              ＝⟨ ap (_• a) (inverse-left-cancel x ⁻¹) ⟩
  (x -¹ • x) • a ＝⟨ compose-associative (x -¹) x a ⟩
  x -¹ • x • a   ∎)

left-is-id : (a x y : 𝓜) → a • x ＝ x → a ＝ E
left-is-id a x y p = transport₂ _＝_
 ((a • x) • x -¹ ＝⟨ compose-associative a x (x -¹) ⟩
  a • x • x -¹   ＝⟨ ap (a •_) (inverse-right-cancel x) ⟩
  a • E          ＝⟨ compose-right-neutral a ⟩
  a              ∎)
 (inverse-right-cancel x)
 (ap (_• x -¹) p)

right-is-id : (a x y : 𝓜) → x • a ＝ x → a ＝ E
right-is-id a x y p = transport (λ u → u • a ＝ u)
 (inverse-left-cancel x)
 (compose-associative (x -¹) x a ∙ ap (x -¹ •_) p)

inverse-product : (a b : 𝓜) → (a • b) -¹ ＝ b -¹ • a -¹
inverse-product E b = compose-right-neutral (b -¹) ⁻¹
inverse-product S b = s-inverse b
inverse-product (𝒔 x) b =
 s (θ x • b) -¹      ＝⟨ s-inverse (θ x • b) ⟩
 (θ x • b) -¹ • S    ＝⟨ ap (_• S) (inverse-product (θ x) b) ⟩
 (b -¹ • θ x -¹) • S ＝⟨ compose-associative (b -¹) (θ x -¹) S ⟩
 b -¹ • θ x -¹ • S   ∎
inverse-product (𝒓 x) b = 
 r (η x • b) -¹       ＝⟨ r-inverse (η x • b) ⟩
 (η x • b) -¹ • R²    ＝⟨ ap (_• R²) (inverse-product (η x) b) ⟩
 (b -¹ • η x -¹) • R² ＝⟨ compose-associative (b -¹) (η x -¹) R² ⟩
 b -¹ • η x -¹ • R²   ∎
inverse-product (𝒓² x) b = 
 r (r (η x • b)) -¹  ＝⟨ r²-inverse (η x • b) ⟩
 (η x • b) -¹ • R    ＝⟨ ap (_• R) (inverse-product (η x) b) ⟩
 (b -¹ • η x -¹) • R ＝⟨ compose-associative (b -¹) (η x -¹) R ⟩
 b -¹ • η x -¹ • R   ∎

\end{code}
