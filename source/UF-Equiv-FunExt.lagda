Properties of equivalences depending on function extensionality.

(Not included in UF-Equiv because the module funext defines function
extensionality as the equivalence of happly for suitable parameters.)

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Equiv-FunExt where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Retracts
open import UF-FunExt
open import UF-Equiv

is-vv-equiv-is-a-prop : (∀ U V → funext U V) → {X : U ̇} {Y : V ̇} (f : X → Y)
                   → is-prop(is-vv-equiv f)
is-vv-equiv-is-a-prop {U} {V} fe f = Π-is-prop
                                     (fe V (U ⊔ V))
                                     (λ x → is-singleton-is-a-prop (fe (U ⊔ V) (U ⊔ V)))

qinv-post' : {X : U ̇} {Y : V ̇} {A : W ̇}
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

qinv-post : (∀ U V → naive-funext U V) → {X : U ̇} {Y : V ̇} {A : W ̇} (f : X → Y)
          → qinv f → qinv (λ (h : A → X) → f ∘ h)
qinv-post {U} {V} {W} nfe = qinv-post' (nfe W U) (nfe W V)

equiv-post : {X : U ̇} {Y : V ̇} {A : W ̇}
           → naive-funext W U → naive-funext W V
           → (f : X → Y) → is-equiv f → is-equiv (λ (h : A → X) → f ∘ h)
equiv-post nfe nfe' f e = qinvs-are-equivs (λ h → f ∘ h) (qinv-post' nfe nfe' f (equivs-are-qinvs f e))

qinv-pre' : {X : U ̇} {Y : V ̇} {A : W ̇}
          → naive-funext V W → naive-funext U W
          → (f : X → Y) → qinv f → qinv (λ (h : Y → A) → h ∘ f)
qinv-pre' {U} {V} {W} {X} {Y} {A} nfe nfe' f (g , η , ε) = (g' , η' , ε')
 where
  f' : (Y → A) → (X → A)
  f' h = h ∘ f
  g' : (X → A) → (Y → A)
  g' k = k ∘ g
  η' : (h : Y → A) → g' (f' h) ≡ h
  η' h = nfe (λ y → ap h (ε y))
  ε' : (k : X → A) → f' (g' k) ≡ k
  ε' k = nfe' (λ x → ap k (η x))

qinv-pre : (∀ U V → naive-funext U V) → {X : U ̇} {Y : V ̇} {A : W ̇} (f : X → Y)
         → qinv f → qinv (λ (h : Y → A) → h ∘ f)
qinv-pre {U} {V} {W} nfe = qinv-pre' (nfe V W) (nfe U W)

retractions-have-at-most-one-section' : {X : U ̇} {Y : V ̇}
                                      → funext V U → funext V V
                                      → (f : X → Y) → has-retraction f → is-prop(has-section f)
retractions-have-at-most-one-section' {U} {V} {X} {Y} fe fe' f (g , gf) (h , fh) =
 singletons-are-propositions c (h , fh)
 where
  a : qinv f
  a = equivs-are-qinvs f ((h , fh) , g , gf)
  b : is-singleton(fiber (λ h →  f ∘ h) id)
  b = qinvs-are-vv-equivs (λ h →  f ∘ h) (qinv-post' (nfunext fe) (nfunext fe') f a) id
  r : fiber (λ h →  f ∘ h) id → has-section f
  r (h , p) = (h , happly' (f ∘ h) id p)
  s : has-section f → fiber (λ h →  f ∘ h) id
  s (h , η) = (h , nfunext fe' η)
  rs : (σ : has-section f) → r (s σ) ≡ σ
  rs (h , η) = ap (λ - → (h , -)) q
   where
    q : happly' (f ∘ h) id (nfunext fe' η) ≡ η
    q = happly-funext fe' (f ∘ h) id η
  c : is-singleton (has-section f)
  c = retract-of-singleton (r , s , rs) b

sections-have-at-most-one-retraction' : {X : U ̇} {Y : V ̇}
                                      → funext U U → funext V U
                                      → (f : X → Y) → has-section f → is-prop(has-retraction f)
sections-have-at-most-one-retraction' {U} {V} {X} {Y} fe fe' f (g , fg) (h , hf) =
 singletons-are-propositions c (h , hf)
 where
  a : qinv f
  a = equivs-are-qinvs f ((g , fg) , (h , hf))
  b : is-singleton(fiber (λ h →  h ∘ f) id)
  b = qinvs-are-vv-equivs (λ h →  h ∘ f) (qinv-pre' (nfunext fe') (nfunext fe) f a) id
  r : fiber (λ h →  h ∘ f) id → has-retraction f
  r (h , p) = (h , happly' (h ∘ f) id p)
  s : has-retraction f → fiber (λ h →  h ∘ f) id
  s (h , η) = (h , dfunext fe η)
  rs : (σ : has-retraction f) → r (s σ) ≡ σ
  rs (h , η) = ap (λ - → (h , -)) q
   where
    q : happly' (h ∘ f) id (dfunext fe η) ≡ η
    q = happly-funext fe (h ∘ f) id η
  c : is-singleton (has-retraction f)
  c = retract-of-singleton (r , s , rs) b

retractions-have-at-most-one-section : (∀ U V → funext U V) → {X : U ̇} {Y : V ̇} (f : X → Y)
                                     → has-retraction f → is-prop(has-section f)
retractions-have-at-most-one-section {U} {V} fe = retractions-have-at-most-one-section' (fe V U) (fe V V)

sections-have-at-most-one-retraction : (∀ U V → funext U V) → {X : U ̇} {Y : V ̇} (f : X → Y)
                                     → has-section f → is-prop(has-retraction f)
sections-have-at-most-one-retraction {U} {V} fe = sections-have-at-most-one-retraction' (fe U U) (fe V U)

is-equiv-is-a-prop : (∀ U V → funext U V) → {X : U ̇} {Y : V ̇} (f : X → Y)
                   → is-prop(is-equiv f)
is-equiv-is-a-prop fe f = ×-prop-criterion (retractions-have-at-most-one-section fe f , sections-have-at-most-one-retraction fe f)

is-equiv-is-a-prop' : {X : U ̇} {Y : V ̇}
                    → funext V U → funext V V → funext U U → funext V U
                    → (f : X → Y) → is-prop(is-equiv f)
is-equiv-is-a-prop' fe fe' fe'' fe''' f = ×-prop-criterion (retractions-have-at-most-one-section' fe fe' f ,
                                                            sections-have-at-most-one-retraction' fe'' fe''' f)

is-equiv-is-a-prop'' : {X Y : U ̇}
                     → funext U U
                     → (f : X → Y) → is-prop(is-equiv f)
is-equiv-is-a-prop'' fe = is-equiv-is-a-prop' fe fe fe fe

\end{code}

Propositional and functional extesionality give univalence for
propositions. Notice that P is assumed to be a proposition, but X
ranges over arbitrary types:

\begin{code}

propext-funext-gives-prop-ua : propext U → funext U U
                             → (P : U ̇) → is-prop P
                             → (X : U ̇) → is-equiv (idtoeq X P)
propext-funext-gives-prop-ua {U} pe fe P i X = (eqtoid , η) , (eqtoid , ε)
 where
  l : X ≃ P → is-prop X
  l (f , _ , (s , fs)) = retract-of-subsingleton (s , (f , fs)) i
  eqtoid : X ≃ P → X ≡ P
  eqtoid (f , (r , rf) , h) = pe (l (f , (r , rf) , h)) i f r
  m : is-prop (X ≃ P)
  m (f , e) (f' , e') = to-Σ-≡ (dfunext fe (λ x → i (f x) (f' x)) ,
                                is-equiv-is-a-prop'' fe f' _ e')
  η : (e : X ≃ P) → idtoeq X P (eqtoid e) ≡ e
  η e = m (idtoeq X P (eqtoid e)) e
  ε : (q : X ≡ P) → eqtoid (idtoeq X P q) ≡ q
  ε q = identifications-of-props-are-props pe fe P i X (eqtoid (idtoeq X P q)) q

\end{code}

The so-called type-theoretic axiom of choice (already defined in
SpartanMLTT with another name - TODO):

\begin{code}

TT-choice : {X : U ̇} {Y : X → V ̇} {A : (x : X) → Y x → W ̇}
          → (Π \(x : X) → Σ \(y : Y x) → A x y)
          → Σ \(f : (x : X) → Y x) → Π \(x : X) → A x (f x)
TT-choice φ = (λ x → pr₁(φ x)) , (λ x → pr₂(φ x))

\end{code}

Its inverse (also already defined - TODO):

\begin{code}

TT-unchoice : {X : U ̇} {Y : X → V ̇} {A : (x : X) → Y x → W ̇}
           → (Σ \(f : (x : X) → Y x) → Π \(x : X) → A x (f x))
           → Π \(x : X) → Σ \(y : Y x) → A x y
TT-unchoice (f , g) x = (f x) , (g x)

\end{code}

The proof that they are mutually inverse, where one direction requires
function extensionality (this already occurs in UF-EquivalenceExamples
- TODO):

\begin{code}

TT-choice-unchoice : {X : U ̇} {Y : X → V ̇} {A : (x : X) → Y x → W ̇}
                  → (t : Σ \(f : (x : X) → Y x) → Π \(x : X) → A x (f x))
                  → TT-choice (TT-unchoice {U} {V} {W} {X} {Y} {A} t) ≡ t
TT-choice-unchoice t = refl

TT-choice-has-section : {X : U ̇} {Y : X → V ̇} {A : (x : X) → Y x → W ̇}
                    → has-section (TT-choice {U} {V} {W} {X} {Y} {A})
TT-choice-has-section {U} {V} {W} {X} {Y} {A} = TT-unchoice ,
                                                TT-choice-unchoice {U} {V} {W} {X} {Y} {A}

TT-unchoice-choice : {X : U ̇} {Y : X → V ̇} {A : (x : X) → Y x → W ̇}
     → funext U (V ⊔ W)
     → (φ : Π \(x : X) → Σ \(y : Y x) → A x y)
     → TT-unchoice (TT-choice φ) ≡ φ
TT-unchoice-choice fe φ = dfunext fe (λ x → refl)

TT-choice-is-equiv : {X : U ̇} {Y : X → V ̇} {A : (x : X) → Y x → W ̇}
                   → funext U (V ⊔ W)
                   → is-equiv TT-choice
TT-choice-is-equiv {U} {V} {W} {X} {Y} {A} fe = TT-choice-has-section {U} {V} {W} {X} {Y} {A} ,
                                                (TT-unchoice , TT-unchoice-choice fe)

TT-unchoice-is-equiv : {X : U ̇} {Y : X → V ̇} {A : (x : X) → Y x → W ̇}
                    → funext U (V ⊔ W)
                    → is-equiv TT-unchoice
TT-unchoice-is-equiv {U} {V} {W} {X} {Y} {A} fe =
   (TT-choice , TT-unchoice-choice {U} {V} {W} {X} {Y} {A} fe) ,
   (TT-choice , TT-choice-unchoice {U} {V} {W} {X} {Y} {A})

\end{code}
