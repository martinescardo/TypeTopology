Properties of equivalences depending on function extensionality.

(Not included in UF-Equiv because the module funext defines function
extensionality as the equivalence of happly for suitable parameters.)

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Equiv-FunExt where

open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Retracts
open import UF-Subsingletons-Retracts
open import UF-FunExt
open import UF-Equiv

is-prop-is-vv-equiv : (∀ U V → funext U V) → ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
                        → is-prop(is-vv-equiv f)
is-prop-is-vv-equiv fe {U} {V} f = is-prop-exponential-ideal
                                         (fe V (U ⊔ V))
                                         (λ x → is-prop-is-singleton (fe (U ⊔ V) (U ⊔ V)))

qinv-post' : ∀ {U} {V} {W} {X : U ̇} {Y : V ̇} {A : W ̇} 
          → naive-funext W U → naive-funext W V
          → (f : X → Y) → qinv f → qinv (λ (h : A → X) → f ∘ h)
qinv-post' {U} {V} {W} {X} {Y} {A} nfe nfe' f (g , η , ε) = (g' , η' , ε')
 where
  f' : (A → X) → (A → Y)
  f' h = f ∘ h
  g' : (A → Y) → (A → X)
  g' k = g ∘ k
  η' : (h : A → X) → g' (f' h) ≡ h
  η' h = nfe (η ∘ h)
  ε' : (k : A → Y) → f' (g' k) ≡ k
  ε' k = nfe' (ε ∘ k)

qinv-post : (∀ U V → naive-funext U V) → ∀ {U} {V} {W} {X : U ̇} {Y : V ̇} {A : W ̇} (f : X → Y)
          → qinv f → qinv (λ (h : A → X) → f ∘ h)
qinv-post nfe {U} {V} {W} = qinv-post' (nfe W U) (nfe W V)

equiv-post : ∀ {U} {V} {W} {X : U ̇} {Y : V ̇} {A : W ̇} 
          → naive-funext W U → naive-funext W V
          → (f : X → Y) → is-equiv f → is-equiv (λ (h : A → X) → f ∘ h)
equiv-post nfe nfe' f e = qinv-is-equiv (λ h → f ∘ h) (qinv-post' nfe nfe' f (is-equiv-qinv f e))

qinv-pre : (∀ U V → funext U V) → ∀ {U} {V} {W} {X : U ̇} {Y : V ̇} {A : W ̇} (f : X → Y)
         → qinv f → qinv (λ (h : Y → A) → h ∘ f)
qinv-pre fe {U} {V} {W} {X} {Y} {A} f (g , η , ε) = (g' , η' , ε')
 where
  f' : (Y → A) → (X → A)
  f' h = h ∘ f
  g' : (X → A) → (Y → A)
  g' k = k ∘ g
  η' : (h : Y → A) → g' (f' h) ≡ h
  η' h = dfunext (fe V W) (λ y → ap h (ε y))
  ε' : (k : X → A) → f' (g' k) ≡ k
  ε' k = dfunext (fe U W) (λ x → ap k (η x))

hasr-is-prop-hass : (∀ U V → funext U V) → ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y)
                 → has-retraction f → is-prop(has-section f)
hasr-is-prop-hass fe {U} {V} {X} {Y} f (g , gf) (h , fh) = is-singleton-is-prop c (h , fh)
 where
  a : qinv f
  a = is-equiv-qinv f ((h , fh) , g , gf)
  b : is-singleton(fiber (λ h →  f ∘ h) id)
  b = qinv-is-vv-equiv (λ h →  f ∘ h) (qinv-post (λ U V → nfunext (fe U V)) f a) id
  r : fiber (λ h →  f ∘ h) id → has-section f
  r (h , p) = (h , happly' (f ∘ h) id p)
  s : has-section f → fiber (λ h →  f ∘ h) id
  s (h , η) = (h , dfunext (fe V V) η)
  rs : (σ : has-section f) → r (s σ) ≡ σ
  rs (h , η) = ap (λ η → (h , η)) q
   where
    q : happly' (f ∘ h) id (dfunext (fe V V) η) ≡ η
    q = happly-funext (fe V V) (f ∘ h) id η
  c : is-singleton (has-section f)
  c = retract-of-singleton r (s , rs) b

hass-is-prop-hasr : (∀ U V → funext U V) → ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y)
                 → has-section f → is-prop(has-retraction f)
hass-is-prop-hasr fe {U} {V} {X} {Y} f (g , fg) (h , hf) = is-singleton-is-prop c (h , hf)
 where
  a : qinv f
  a = is-equiv-qinv f ((g , fg) , (h , hf))
  b : is-singleton(fiber (λ h →  h ∘ f) id)
  b = qinv-is-vv-equiv (λ h →  h ∘ f) (qinv-pre fe f a) id
  r : fiber (λ h →  h ∘ f) id → has-retraction f
  r (h , p) = (h , happly' (h ∘ f) id p)
  s : has-retraction f → fiber (λ h →  h ∘ f) id
  s (h , η) = (h , dfunext (fe U U) η) 
  rs : (σ : has-retraction f) → r (s σ) ≡ σ
  rs (h , η) = ap (λ η → (h , η)) q
   where
    q : happly' (h ∘ f) id (dfunext (fe U U) η) ≡ η
    q = happly-funext (fe U U) (h ∘ f) id η
  c : is-singleton (has-retraction f)
  c = retract-of-singleton r (s , rs) b

is-equiv-is-prop : (∀ U V → funext U V) → ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y)
               → is-prop(is-equiv f)
is-equiv-is-prop fe f = ×-prop-criterion (hasr-is-prop-hass fe f , hass-is-prop-hasr fe f)

\end{code}

The so-called type-theoretic axiom of choice:

\begin{code}

tt-choice : ∀ {U V W} {X : U ̇} {Y : X → V ̇} {A : (x : X) → Y x → W ̇}
          → (Π \(x : X) → Σ \(y : Y x) → A x y)
          → Σ \(f : (x : X) → Y x) → Π \(x : X) → A x (f x)
tt-choice φ = (λ x → pr₁(φ x)) , (λ x → pr₂(φ x))

\end{code}

Its inverse:

\begin{code}

tt-unchoice : ∀ {U V W} {X : U ̇} {Y : X → V ̇} {A : (x : X) → Y x → W ̇}
           → (Σ \(f : (x : X) → Y x) → Π \(x : X) → A x (f x))
           → Π \(x : X) → Σ \(y : Y x) → A x y
tt-unchoice (f , g) x = (f x) , (g x)

\end{code}

The proof that they are mutually inverse, where one direction requires
function extensionality.

\begin{code}

tt-choice-unchoice : ∀ {U V W} {X : U ̇} {Y : X → V ̇} {A : (x : X) → Y x → W ̇}
                  → (t : Σ \(f : (x : X) → Y x) → Π \(x : X) → A x (f x))
                  → tt-choice (tt-unchoice {U} {V} {W} {X} {Y} {A} t) ≡ t
tt-choice-unchoice t = refl

tt-choice-has-section : ∀ {U V W} {X : U ̇} {Y : X → V ̇} {A : (x : X) → Y x → W ̇}
                    → has-section (tt-choice {U} {V} {W} {X} {Y} {A})
tt-choice-has-section {U} {V} {W} {X} {Y} {A} = tt-unchoice ,
                                                tt-choice-unchoice {U} {V} {W} {X} {Y} {A}

tt-unchoice-choice : ∀ {U V W} {X : U ̇} {Y : X → V ̇} {A : (x : X) → Y x → W ̇}
     → funext U (V ⊔ W)
     → (φ : Π \(x : X) → Σ \(y : Y x) → A x y)
     → tt-unchoice (tt-choice φ) ≡ φ
tt-unchoice-choice fe φ = dfunext fe (λ x → refl)

tt-choice-is-equiv : ∀ {U V W} {X : U ̇} {Y : X → V ̇} {A : (x : X) → Y x → W ̇}
                   → funext U (V ⊔ W)
                   → is-equiv tt-choice
tt-choice-is-equiv {U} {V} {W} {X} {Y} {A} fe = tt-choice-has-section {U} {V} {W} {X} {Y} {A} ,
                                                (tt-unchoice , tt-unchoice-choice fe)

tt-unchoice-is-equiv : ∀ {U V W} {X : U ̇} {Y : X → V ̇} {A : (x : X) → Y x → W ̇}
                    → funext U (V ⊔ W)
                    → is-equiv tt-unchoice
tt-unchoice-is-equiv {U} {V} {W} {X} {Y} {A} fe =
   (tt-choice , tt-unchoice-choice {U} {V} {W} {X} {Y} {A} fe) ,
   (tt-choice , tt-choice-unchoice {U} {V} {W} {X} {Y} {A}) 
                                        
\end{code}
