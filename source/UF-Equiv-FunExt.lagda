Properties of equivalences depending on function extensionality.

(Not included in UF-Equiv because the module funext defines function
extensionality as the equivalence of happly for suitable parameters.)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Equiv-FunExt where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Retracts
open import UF-FunExt
open import UF-Equiv

being-vv-equiv-is-a-prop : global-funext → {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
                         → is-prop(is-vv-equiv f)
being-vv-equiv-is-a-prop {𝓤} {𝓥} fe f = Π-is-prop
                                          (fe 𝓥 (𝓤 ⊔ 𝓥))
                                          (λ x → being-a-singleton-is-a-prop (fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)))

qinv-post' : {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : 𝓦 ̇}
          → naive-funext 𝓦 𝓤 → naive-funext 𝓦 𝓥
          → (f : X → Y) → qinv f → qinv (λ (h : A → X) → f ∘ h)
qinv-post' {𝓤} {𝓥} {𝓦} {X} {Y} {A} nfe nfe' f (g , η , ε) = (g' , η' , ε')
 where
  f' : (A → X) → (A → Y)
  f' h = f ∘ h
  g' : (A → Y) → (A → X)
  g' k = g ∘ k
  η' : (h : A → X) → g' (f' h) ≡ h
  η' h = nfe (η ∘ h)
  ε' : (k : A → Y) → f' (g' k) ≡ k
  ε' k = nfe' (ε ∘ k)

qinv-post : (∀ 𝓤 𝓥 → naive-funext 𝓤 𝓥) → {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : 𝓦 ̇} (f : X → Y)
          → qinv f → qinv (λ (h : A → X) → f ∘ h)
qinv-post {𝓤} {𝓥} {𝓦} nfe = qinv-post' (nfe 𝓦 𝓤) (nfe 𝓦 𝓥)

equiv-post : {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : 𝓦 ̇}
           → naive-funext 𝓦 𝓤 → naive-funext 𝓦 𝓥
           → (f : X → Y) → is-equiv f → is-equiv (λ (h : A → X) → f ∘ h)
equiv-post nfe nfe' f e = qinvs-are-equivs (λ h → f ∘ h) (qinv-post' nfe nfe' f (equivs-are-qinvs f e))

qinv-pre' : {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : 𝓦 ̇}
          → naive-funext 𝓥 𝓦 → naive-funext 𝓤 𝓦
          → (f : X → Y) → qinv f → qinv (λ (h : Y → A) → h ∘ f)
qinv-pre' {𝓤} {𝓥} {𝓦} {X} {Y} {A} nfe nfe' f (g , η , ε) = (g' , η' , ε')
 where
  f' : (Y → A) → (X → A)
  f' h = h ∘ f
  g' : (X → A) → (Y → A)
  g' k = k ∘ g
  η' : (h : Y → A) → g' (f' h) ≡ h
  η' h = nfe (λ y → ap h (ε y))
  ε' : (k : X → A) → f' (g' k) ≡ k
  ε' k = nfe' (λ x → ap k (η x))

qinv-pre : (∀ 𝓤 𝓥 → naive-funext 𝓤 𝓥) → {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : 𝓦 ̇} (f : X → Y)
         → qinv f → qinv (λ (h : Y → A) → h ∘ f)
qinv-pre {𝓤} {𝓥} {𝓦} nfe = qinv-pre' (nfe 𝓥 𝓦) (nfe 𝓤 𝓦)

retractions-have-at-most-one-section' : {X : 𝓤 ̇} {Y : 𝓥 ̇}
                                      → funext 𝓥 𝓤 → funext 𝓥 𝓥
                                      → (f : X → Y) → has-retraction f → is-prop(has-section f)
retractions-have-at-most-one-section' {𝓤} {𝓥} {X} {Y} fe fe' f (g , gf) (h , fh) =
 singletons-are-props c (h , fh)
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

sections-have-at-most-one-retraction' : {X : 𝓤 ̇} {Y : 𝓥 ̇}
                                      → funext 𝓤 𝓤 → funext 𝓥 𝓤
                                      → (f : X → Y) → has-section f → is-prop(has-retraction f)
sections-have-at-most-one-retraction' {𝓤} {𝓥} {X} {Y} fe fe' f (g , fg) (h , hf) =
 singletons-are-props c (h , hf)
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

retractions-have-at-most-one-section : global-funext → {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
                                     → has-retraction f → is-prop(has-section f)
retractions-have-at-most-one-section {𝓤} {𝓥} fe = retractions-have-at-most-one-section' (fe 𝓥 𝓤) (fe 𝓥 𝓥)

sections-have-at-most-one-retraction : global-funext → {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
                                     → has-section f → is-prop(has-retraction f)
sections-have-at-most-one-retraction {𝓤} {𝓥} fe = sections-have-at-most-one-retraction' (fe 𝓤 𝓤) (fe 𝓥 𝓤)

being-equiv-is-a-prop : global-funext → {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
                      → is-prop(is-equiv f)
being-equiv-is-a-prop fe f = ×-prop-criterion (retractions-have-at-most-one-section fe f , sections-have-at-most-one-retraction fe f)

being-equiv-is-a-prop' : {X : 𝓤 ̇} {Y : 𝓥 ̇}
                       → funext 𝓥 𝓤 → funext 𝓥 𝓥 → funext 𝓤 𝓤 → funext 𝓥 𝓤
                       → (f : X → Y) → is-prop(is-equiv f)
being-equiv-is-a-prop' fe fe' fe'' fe''' f = ×-prop-criterion (retractions-have-at-most-one-section' fe fe' f ,
                                                               sections-have-at-most-one-retraction' fe'' fe''' f)

being-equiv-is-a-prop'' : {X Y : 𝓤 ̇}
                        → funext 𝓤 𝓤
                        → (f : X → Y) → is-prop(is-equiv f)
being-equiv-is-a-prop'' fe = being-equiv-is-a-prop' fe fe fe fe

\end{code}

Propositional and functional extesionality give univalence for
propositions. Notice that P is assumed to be a proposition, but X
ranges over arbitrary types:

\begin{code}

propext-funext-give-prop-ua : propext 𝓤 → funext 𝓤 𝓤
                            → (P : 𝓤 ̇) → is-prop P
                            → (X : 𝓤 ̇) → is-equiv (idtoeq X P)
propext-funext-give-prop-ua {𝓤} pe fe P i X = (eqtoid , η) , (eqtoid , ε)
 where
  l : X ≃ P → is-prop X
  l (f , _ , (s , fs)) = retract-of-prop (s , (f , fs)) i
  eqtoid : X ≃ P → X ≡ P
  eqtoid (f , (r , rf) , h) = pe (l (f , (r , rf) , h)) i f r
  m : is-prop (X ≃ P)
  m (f , e) (f' , e') = to-Σ-≡ (dfunext fe (λ x → i (f x) (f' x)) ,
                                being-equiv-is-a-prop'' fe f' _ e')
  η : (e : X ≃ P) → idtoeq X P (eqtoid e) ≡ e
  η e = m (idtoeq X P (eqtoid e)) e
  ε : (q : X ≡ P) → eqtoid (idtoeq X P q) ≡ q
  ε q = identifications-of-props-are-props pe fe P i X (eqtoid (idtoeq X P q)) q

\end{code}

The so-called type-theoretic axiom of choice (already defined in
SpartanMLTT with another name - TODO):

\begin{code}

TT-choice : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {A : (x : X) → Y x → 𝓦 ̇}
          → (Π \(x : X) → Σ \(y : Y x) → A x y)
          → Σ \(f : (x : X) → Y x) → Π \(x : X) → A x (f x)
TT-choice φ = (λ x → pr₁(φ x)) , (λ x → pr₂(φ x))

\end{code}

Its inverse (also already defined - TODO):

\begin{code}

TT-unchoice : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {A : (x : X) → Y x → 𝓦 ̇}
            → (Σ \(f : (x : X) → Y x) → Π \(x : X) → A x (f x))
            → Π \(x : X) → Σ \(y : Y x) → A x y
TT-unchoice (f , g) x = (f x) , (g x)

\end{code}

The proof that they are mutually inverse, where one direction requires
function extensionality (this already occurs in UF-EquivalenceExamples
- TODO):

\begin{code}

TT-choice-unchoice : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {A : (x : X) → Y x → 𝓦 ̇}
                  → (t : Σ \(f : (x : X) → Y x) → Π \(x : X) → A x (f x))
                  → TT-choice (TT-unchoice {𝓤} {𝓥} {𝓦} {X} {Y} {A} t) ≡ t
TT-choice-unchoice t = refl

TT-choice-has-section : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {A : (x : X) → Y x → 𝓦 ̇}
                    → has-section (TT-choice {𝓤} {𝓥} {𝓦} {X} {Y} {A})
TT-choice-has-section {𝓤} {𝓥} {𝓦} {X} {Y} {A} = TT-unchoice ,
                                                TT-choice-unchoice {𝓤} {𝓥} {𝓦} {X} {Y} {A}

TT-unchoice-choice : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {A : (x : X) → Y x → 𝓦 ̇}
                   → funext 𝓤 (𝓥 ⊔ 𝓦)
                   → (φ : Π \(x : X) → Σ \(y : Y x) → A x y)
                   → TT-unchoice (TT-choice φ) ≡ φ
TT-unchoice-choice fe φ = dfunext fe (λ x → refl)

TT-choice-is-equiv : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {A : (x : X) → Y x → 𝓦 ̇}
                   → funext 𝓤 (𝓥 ⊔ 𝓦)
                   → is-equiv TT-choice
TT-choice-is-equiv {𝓤} {𝓥} {𝓦} {X} {Y} {A} fe = TT-choice-has-section {𝓤} {𝓥} {𝓦} {X} {Y} {A} ,
                                                (TT-unchoice , TT-unchoice-choice fe)

TT-unchoice-is-equiv : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {A : (x : X) → Y x → 𝓦 ̇}
                     → funext 𝓤 (𝓥 ⊔ 𝓦)
                     → is-equiv TT-unchoice
TT-unchoice-is-equiv {𝓤} {𝓥} {𝓦} {X} {Y} {A} fe =
   (TT-choice , TT-unchoice-choice {𝓤} {𝓥} {𝓦} {X} {Y} {A} fe) ,
   (TT-choice , TT-choice-unchoice {𝓤} {𝓥} {𝓦} {X} {Y} {A})

\end{code}
