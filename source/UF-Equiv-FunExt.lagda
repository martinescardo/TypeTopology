Properties of equivalences depending on function extensionality.

(Not included in UF-Equiv because the module FunExt defines function
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

isProp-isVoevodskyEquiv : (∀ U V → FunExt U V) → ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
                        → isProp(isVoevodskyEquiv f)
isProp-isVoevodskyEquiv fe {U} {V} f = isProp-exponential-ideal
                                         (fe V (U ⊔ V))
                                         (λ x → isProp-isSingleton (fe (U ⊔ V) (U ⊔ V)))

qinv-post' : ∀ {U} {V} {W} {X : U ̇} {Y : V ̇} {A : W ̇} 
          → NaiveFunExt W U → NaiveFunExt W V
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

qinv-post : (∀ U V → NaiveFunExt U V) → ∀ {U} {V} {W} {X : U ̇} {Y : V ̇} {A : W ̇} (f : X → Y)
          → qinv f → qinv (λ (h : A → X) → f ∘ h)
qinv-post nfe {U} {V} {W} = qinv-post' (nfe W U) (nfe W V)

equiv-post : ∀ {U} {V} {W} {X : U ̇} {Y : V ̇} {A : W ̇} 
          → NaiveFunExt W U → NaiveFunExt W V
          → (f : X → Y) → isEquiv f → isEquiv (λ (h : A → X) → f ∘ h)
equiv-post nfe nfe' f e = qinv-isEquiv (λ h → f ∘ h) (qinv-post' nfe nfe' f (isEquiv-qinv f e))

qinv-pre : (∀ U V → FunExt U V) → ∀ {U} {V} {W} {X : U ̇} {Y : V ̇} {A : W ̇} (f : X → Y)
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

hasr-isprop-hass : (∀ U V → FunExt U V) → ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y)
                 → hasRetraction f → isProp(hasSection f)
hasr-isprop-hass fe {U} {V} {X} {Y} f (g , gf) (h , fh) = isSingleton-isProp c (h , fh)
 where
  a : qinv f
  a = isEquiv-qinv f ((h , fh) , g , gf)
  b : isSingleton(fiber (λ h →  f ∘ h) id)
  b = qinv-isVoevodsky (λ h →  f ∘ h) (qinv-post (λ U V → nfunext (fe U V)) f a) id
  r : fiber (λ h →  f ∘ h) id → hasSection f
  r (h , p) = (h , happly' (f ∘ h) id p)
  s : hasSection f → fiber (λ h →  f ∘ h) id
  s (h , η) = (h , dfunext (fe V V) η)
  rs : (σ : hasSection f) → r (s σ) ≡ σ
  rs (h , η) = ap (λ η → (h , η)) q
   where
    q : happly' (f ∘ h) id (dfunext (fe V V) η) ≡ η
    q = happly-funext (fe V V) (f ∘ h) id η
  c : isSingleton (hasSection f)
  c = retract-of-singleton r (s , rs) b

hass-isprop-hasr : (∀ U V → FunExt U V) → ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y)
                 → hasSection f → isProp(hasRetraction f)
hass-isprop-hasr fe {U} {V} {X} {Y} f (g , fg) (h , hf) = isSingleton-isProp c (h , hf)
 where
  a : qinv f
  a = isEquiv-qinv f ((g , fg) , (h , hf))
  b : isSingleton(fiber (λ h →  h ∘ f) id)
  b = qinv-isVoevodsky (λ h →  h ∘ f) (qinv-pre fe f a) id
  r : fiber (λ h →  h ∘ f) id → hasRetraction f
  r (h , p) = (h , happly' (h ∘ f) id p)
  s : hasRetraction f → fiber (λ h →  h ∘ f) id
  s (h , η) = (h , dfunext (fe U U) η) 
  rs : (σ : hasRetraction f) → r (s σ) ≡ σ
  rs (h , η) = ap (λ η → (h , η)) q
   where
    q : happly' (h ∘ f) id (dfunext (fe U U) η) ≡ η
    q = happly-funext (fe U U) (h ∘ f) id η
  c : isSingleton (hasRetraction f)
  c = retract-of-singleton r (s , rs) b

isEquiv-isProp : (∀ U V → FunExt U V) → ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y)
               → isProp(isEquiv f)
isEquiv-isProp fe f = ×-prop-criterion (hasr-isprop-hass fe f , hass-isprop-hasr fe f)

\end{code}

The so-called type-theoretic axiom of choice:

\begin{code}

πσ : ∀ {U V W} {X : U ̇} {Y : X → V ̇} {A : (x : X) → Y x → W ̇}
    → (Π \(x : X) → Σ \(y : Y x) → A x y)
    → Σ \(f : (x : X) → Y x) → Π \(x : X) → A x (f x)
πσ φ = (λ x → pr₁(φ x)) , (λ x → pr₂(φ x))

\end{code}

Its inverse:

\begin{code}

σπ : ∀ {U V W} {X : U ̇} {Y : X → V ̇} {A : (x : X) → Y x → W ̇}
    → (Σ \(f : (x : X) → Y x) → Π \(x : X) → A x (f x))
    → Π \(x : X) → Σ \(y : Y x) → A x y
σπ (f , g) x = (f x) , (g x)

\end{code}

The proof that they are mutually inverse, were one direction requires
function extensionality.

\begin{code}

πσσπ : ∀ {U V W} {X : U ̇} {Y : X → V ̇} {A : (x : X) → Y x → W ̇}
     → (t : Σ \(f : (x : X) → Y x) → Π \(x : X) → A x (f x))
     → πσ (σπ {U} {V} {W} {X} {Y} {A} t) ≡ t
πσσπ t = refl

πσ-hasSection : ∀ {U V W} {X : U ̇} {Y : X → V ̇} {A : (x : X) → Y x → W ̇}
              → hasSection (πσ {U} {V} {W} {X} {Y} {A})
πσ-hasSection {U} {V} {W} {X} {Y} {A} = σπ , πσσπ {U} {V} {W} {X} {Y} {A}

σππσ : ∀ {U V W} {X : U ̇} {Y : X → V ̇} {A : (x : X) → Y x → W ̇}
     → FunExt U (V ⊔ W)
     → (φ : Π \(x : X) → Σ \(y : Y x) → A x y)
     → σπ (πσ φ) ≡ φ
σππσ fe φ = dfunext fe (λ x → refl)

πσ-isEquiv : ∀ {U V W} {X : U ̇} {Y : X → V ̇} {A : (x : X) → Y x → W ̇}
           → FunExt U (V ⊔ W)
           → isEquiv πσ
πσ-isEquiv {U} {V} {W} {X} {Y} {A} fe = πσ-hasSection ,
                                        (σπ , σππσ {U} {V} {W} {X} {Y} {A} fe)

σπ-isEquiv : ∀ {U V W} {X : U ̇} {Y : X → V ̇} {A : (x : X) → Y x → W ̇}
           → FunExt U (V ⊔ W)
           → isEquiv σπ
σπ-isEquiv {U} {V} {W} {X} {Y} {A} fe = (πσ , σππσ {U} {V} {W} {X} {Y} {A} fe) ,
                                        (πσ , πσσπ {U} {V} {W} {X} {Y} {A}) 
                                        
\end{code}
