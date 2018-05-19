In univalent logic, as opposed to Curry-Howard logic, a proposition is
a subsingleton or a type such that any two of its elements are
identified.

https://www.newton.ac.uk/files/seminar/20170711100011001-1009756.pdf
https://unimath.github.io/bham2017/uf.pdf

About (sub)singletons using function extensionality.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Subsingletons-FunExt where

open import UF-Base
open import UF-Subsingletons
open import UF-FunExt
open import UF-LeftCancellable

isProp-exponential-ideal : ∀ {U V} → FunExt U V → {X : U ̇} {A : X → V ̇} 
                        → ((x : X) → isProp (A x)) → isProp (Π A) 
isProp-exponential-ideal fe {X} {A} isa f g = dfunext fe (λ x → isa x (f x) (g x))

isProp-isProp : ∀ {U} {X : U ̇} → FunExt U U → isProp (isProp X)
isProp-isProp {U} {X} fe f g = claim₁
 where
  lemma : isSet X
  lemma = prop-isSet f
  claim : (x y : X) → f x y ≡ g x y
  claim x y = lemma (f x y) (g x y)
  claim₀ : (x : X) → f x ≡ g x 
  claim₀ x = dfunext fe (claim x) 
  claim₁ : f ≡ g
  claim₁  = dfunext fe claim₀

isProp-isSingleton : ∀ {U} {X : U ̇} → FunExt U U → isProp(isSingleton X)
isProp-isSingleton {U} {X} fe (x , φ) (y , γ) = to-Σ-≡'' (φ y , dfunext fe λ z → iss {y} {z} _ _)
 where
  isp : isProp X
  isp = isSingleton-isProp (y , γ)
  iss : isSet X
  iss = prop-isSet isp

isSet-exponential-ideal : ∀ {U V} → FunExt U V → {X : U ̇} {A : X → V ̇} 
                        → ((x : X) → isSet(A x)) → isSet(Π A) 
isSet-exponential-ideal {U} {V} fe {X} {A} isa {f} {g} = b
 where
  a : isProp (f ∼ g)
  a p q = dfunext fe λ x → isa x (p x) (q x)
  b : isProp(f ≡ g)
  b = left-cancellable-reflects-isProp happly (section-lc happly (pr₂ (fe f g))) a


\end{code}

The following code is used to make Agda work with the constructions we
have given. We make the implicit arguments explicit in the definition
of isSet.

\begin{code}

isSet' : ∀ {U} → U ̇ → U ̇
isSet' X = (x y : X) → isProp(x ≡ y)

isSet'-isSet : ∀ {U} {X : U ̇} → isSet' X → isSet X
isSet'-isSet s {x} {y} = s x y

isSet-isSet' : ∀ {U} {X : U ̇} → isSet X → isSet' X
isSet-isSet' s x y = s {x} {y}

isProp-isSet' : ∀ {U} {X : U ̇} → FunExt U U → isProp (isSet' X)
isProp-isSet' fe = isProp-exponential-ideal fe
                    (λ x → isProp-exponential-ideal fe
                              (λ y → isProp-isProp fe))

\end{code}

\begin{code}

decidable-isProp : ∀ {U} {P : U ̇} → FunExt U U₀ → isProp P → isProp(P + ¬ P)
decidable-isProp fe₀ isp = sum-of-contradictory-props
                             isp
                             (isProp-exponential-ideal fe₀ λ _ → 𝟘-isProp)
                             (λ p u → u p)

PropExt : ∀ {U} → FunExt U U → propExt U → {p q : Ω {U}}
        → (p holds → q holds) → (q holds → p holds) → p ≡ q
PropExt {U} fe pe {p} {q} f g =
        to-Σ-≡'' ((pe (holdsIsProp p) (holdsIsProp q) f g) , isProp-isProp fe _ _)

Ω-isSet : ∀ {U} → FunExt U U → propExt U → isSet (Ω {U})
Ω-isSet {U} fe pe = path-collapsible-isSet pc
 where
  A : (p q : Ω) → U ̇
  A p q = (p holds → q holds) × (q holds → p holds) 
  A-isProp : (p q : Ω) → isProp(A p q)
  A-isProp p q = isProp-closed-under-Σ (isProp-exponential-ideal fe (λ _ → holdsIsProp q)) 
                                       (λ _ → isProp-exponential-ideal fe (λ _ → holdsIsProp p)) 
  g : (p q : Ω) → p ≡ q → A p q
  g p q e = (b , c)
   where
    a : p holds ≡ q holds
    a = ap _holds e
    b : p holds → q holds
    b = transport (λ X → X) a
    c : q holds → p holds
    c = transport (λ X → X) (a ⁻¹)
  h  : (p q : Ω) → A p q → p ≡ q 
  h p q (u , v) = PropExt fe pe u v
  f  : (p q : Ω) → p ≡ q → p ≡ q
  f p q e = h p q (g p q e)
  constant-f : (p q : Ω) (d e : p ≡ q) → f p q d ≡ f p q e 
  constant-f p q d e = ap (h p q) (A-isProp p q (g p q d) (g p q e))
  pc : {p q : Ω} → Σ \(f : p ≡ q → p ≡ q) → constant f
  pc {p} {q} = (f p q , constant-f p q)

neg-isProp : ∀ {U} {X : U ̇} → FunExt U U₀ → isProp(¬ X)
neg-isProp fe u v = dfunext fe (λ x → 𝟘-elim (u x)) 

\end{code}

For the moment we work with U₀ here because 𝟙 and ⊤ live in U₀:

\begin{code}

equal-⊤-is-true : (P : U₀ ̇) (hp : isProp P)
               → (P , hp) ≡ ⊤ → P
equal-⊤-is-true P hp r = f *
 where
  s : 𝟙 ≡ P
  s = (ap pr₁ r)⁻¹
  f : 𝟙 → P
  f = transport id s

true-is-equal-⊤ : propExt U₀ → FunExt U₀ U₀ → (P : U₀ ̇) (hp : isProp P)
                → P → (P , hp) ≡ ⊤
true-is-equal-⊤ pe fe P hp x = to-Σ-≡ P 𝟙 hp 𝟙-isProp (pe hp 𝟙-isProp unique-to-𝟙 λ _ → x)
                                                        (isProp-isProp fe _ _)

Ω-ext : propExt U₀ → FunExt U₀ U₀ → {p q : Ω}
      → (p ≡ ⊤ → q ≡ ⊤) → (q ≡ ⊤ → p ≡ ⊤) → p ≡ q
Ω-ext pe fe {(P , isp)} {(Q , isq)} f g = to-Σ-≡ P Q isp isq (pe isp isq I II) (isProp-isProp fe _ _ ) 
 where
  I : P → Q
  I x = equal-⊤-is-true Q isq (f (true-is-equal-⊤ pe fe P isp x))
  II : Q → P
  II y = equal-⊤-is-true P isp (g (true-is-equal-⊤ pe fe Q isq y))

\end{code}
