In univalent logic, as opposed to Curry-Howard logic, a proposition is
a subsingleton or a type such that any two of its elements are
identified.

https://www.newton.ac.uk/files/seminar/20170711100011001-1009756.pdf
https://unimath.github.io/bham2017/uf.pdf

About (sub)singletons using function extensionality.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Subsingletons-FunExt where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-FunExt
open import UF-LeftCancellable

Π-is-prop : ∀ {U V} → funext U V → {X : U ̇} {A : X → V ̇}
          → ((x : X) → is-prop (A x)) → is-prop (Π A)
Π-is-prop fe {X} {A} isa f g = dfunext fe (λ x → isa x (f x) (g x))

is-prop-is-prop : ∀ {U} {X : U ̇} → funext U U → is-prop (is-prop X)
is-prop-is-prop {U} {X} fe f g = claim₁
 where
  lemma : is-set X
  lemma = prop-is-set f
  claim : (x y : X) → f x y ≡ g x y
  claim x y = lemma (f x y) (g x y)
  claim₀ : (x : X) → f x ≡ g x
  claim₀ x = dfunext fe (claim x)
  claim₁ : f ≡ g
  claim₁  = dfunext fe claim₀

is-prop-is-singleton : ∀ {U} {X : U ̇} → funext U U → is-prop(is-singleton X)
is-prop-is-singleton {U} {X} fe (x , φ) (y , γ) = to-Σ-≡ (φ y , dfunext fe λ z → iss {y} {z} _ _)
 where
  isp : is-prop X
  isp = is-singleton-is-prop (y , γ)
  iss : is-set X
  iss = prop-is-set isp

Π-is-set : ∀ {U V} → funext U V → {X : U ̇} {A : X → V ̇}
         → ((x : X) → is-set(A x)) → is-set(Π A)
Π-is-set {U} {V} fe {X} {A} isa {f} {g} = b
 where
  a : is-prop (f ∼ g)
  a p q = dfunext fe λ x → isa x (p x) (q x)
  b : is-prop(f ≡ g)
  b = left-cancellable-reflects-is-prop happly (section-lc happly (pr₂ (fe f g))) a

\end{code}

The meat of the following proof is is-prop-is-set'. The rest of the
code is to deal with implicit arguments in conjunction with function
extensionality. The solution is not ideal. Ideally, functions with
implicit parameters should be the same as their versions with explicit
parameters.

\begin{code}

is-prop-is-set : ∀ {U} {X : U ̇} → funext U U → is-prop (is-set X)
is-prop-is-set {U} {X} fe = h
 where
  is-set' : ∀ {U} → U ̇ → U ̇
  is-set' X = (x y : X) → is-prop(x ≡ y)

  is-prop-is-set' : ∀ {U} {X : U ̇} → funext U U → is-prop (is-set' X)
  is-prop-is-set' fe = Π-is-prop fe
                         (λ x → Π-is-prop fe
                         (λ y → is-prop-is-prop fe))

  f : ∀ {U} {X : U ̇} → is-set' X → is-set X
  f s {x} {y} = s x y

  g : ∀ {U} {X : U ̇} → is-set X → is-set' X
  g s x y = s {x} {y}

  h : is-prop (is-set X)
  h = subtype-of-prop-is-prop g (ap f) (is-prop-is-set' fe)

\end{code}

\begin{code}

decidable-is-prop : ∀ {U} {P : U ̇} → funext U U₀ → is-prop P → is-prop(P + ¬ P)
decidable-is-prop fe₀ isp = sum-of-contradictory-props
                             isp
                             (Π-is-prop fe₀ λ _ → 𝟘-is-prop)
                             (λ p u → u p)

PropExt : ∀ {U} → funext U U → propext U → {p q : Ω U}
        → (p holds → q holds) → (q holds → p holds) → p ≡ q
PropExt {U} fe pe {p} {q} f g =
        to-Σ-≡ ((pe (holds-is-prop p) (holds-is-prop q) f g) , is-prop-is-prop fe _ _)

Ω-is-set : ∀ {U} → funext U U → propext U → is-set (Ω U)
Ω-is-set {U} fe pe = identification-collapsible-is-set pc
 where
  A : (p q : Ω U) → U ̇
  A p q = (p holds → q holds) × (q holds → p holds)
  A-is-prop : (p q : Ω U) → is-prop(A p q)
  A-is-prop p q = Σ-is-prop (Π-is-prop fe
                                   (λ _ → holds-is-prop q))
                                   (λ _ → Π-is-prop fe (λ _ → holds-is-prop p))
  g : (p q : Ω U) → p ≡ q → A p q
  g p q e = (b , c)
   where
    a : p holds ≡ q holds
    a = ap _holds e
    b : p holds → q holds
    b = transport (λ X → X) a
    c : q holds → p holds
    c = transport (λ X → X) (a ⁻¹)
  h  : (p q : Ω U) → A p q → p ≡ q
  h p q (u , v) = PropExt fe pe u v
  f  : (p q : Ω U) → p ≡ q → p ≡ q
  f p q e = h p q (g p q e)
  constant-f : (p q : Ω U) (d e : p ≡ q) → f p q d ≡ f p q e
  constant-f p q d e = ap (h p q) (A-is-prop p q (g p q d) (g p q e))
  pc : {p q : Ω U} → Σ \(f : p ≡ q → p ≡ q) → constant f
  pc {p} {q} = (f p q , constant-f p q)

powerset-is-set : ∀ {U V} {A : U ̇} → funext U (V ′) → funext V V → propext V
                → is-set (A → Ω V)
powerset-is-set {U} fe fe' pe = Π-is-set fe (λ x → Ω-is-set fe' pe)

neg-is-prop : ∀ {U} {X : U ̇} → funext U U₀ → is-prop(¬ X)
neg-is-prop fe u v = dfunext fe (λ x → 𝟘-elim (u x))

\end{code}

For the moment we work with U₀ here because 𝟙 and ⊤ live in U₀:

\begin{code}

equal-⊤-is-true : (P : U₀ ̇) (hp : is-prop P)
               → (P , hp) ≡ ⊤ → P
equal-⊤-is-true P hp r = f *
 where
  s : 𝟙 ≡ P
  s = (ap pr₁ r)⁻¹
  f : 𝟙 → P
  f = transport id s

true-is-equal-⊤ : propext U₀ → funext U₀ U₀ → (P : U₀ ̇) (hp : is-prop P)
                → P → (P , hp) ≡ ⊤
true-is-equal-⊤ pe fe P hp x = to-Σ-≡ (pe hp 𝟙-is-prop unique-to-𝟙 (λ _ → x) ,
                                        is-prop-is-prop fe _ _)

Ω-ext : propext U₀ → funext U₀ U₀ → {p q : Ω U₀}
      → (p ≡ ⊤ → q ≡ ⊤) → (q ≡ ⊤ → p ≡ ⊤) → p ≡ q
Ω-ext pe fe {(P , isp)} {(Q , isq)} f g = to-Σ-≡ (pe isp isq I II ,
                                                   is-prop-is-prop fe _ _ )
 where
  I : P → Q
  I x = equal-⊤-is-true Q isq (f (true-is-equal-⊤ pe fe P isp x))
  II : Q → P
  II y = equal-⊤-is-true P isp (g (true-is-equal-⊤ pe fe Q isq y))

not : ∀ {U} → funext U U₀ → Ω U → Ω U
not fe (P , i) = (¬ P , Π-is-prop fe λ x → 𝟘-is-prop)

\end{code}
