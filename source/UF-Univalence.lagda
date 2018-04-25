Formulation of univalence.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Univalence where

open import UF-Base
open import UF-Subsingletons
open import UF-Equiv
open import UF-LeftCancellable

isUnivalent : ∀ U → U ′ ̇
isUnivalent U = (X Y : U ̇) → isEquiv(idtoeq X Y)

eqtoid : ∀ {U} → isUnivalent U → (X Y : U ̇) → X ≃ Y → X ≡ Y 
eqtoid ua X Y = pr₁(pr₁(ua X Y))

idtoeq-eqtoid : ∀ {U} (ua : isUnivalent U)
              → (X Y : U ̇) (e : X ≃ Y) → idtoeq X Y (eqtoid ua X Y e) ≡ e
idtoeq-eqtoid ua X Y = pr₂(pr₁(ua X Y))

eqtoid' : ∀ {U} → isUnivalent U → (X Y : U ̇) → X ≃ Y → X ≡ Y 
eqtoid' ua X Y = pr₁(pr₂(ua X Y))

eqtoid-idtoeq : ∀ {U} (ua : isUnivalent U)
              → (X Y : U ̇) (p : X ≡ Y) →  eqtoid' ua X Y (idtoeq X Y p) ≡ p
eqtoid-idtoeq ua X Y = pr₂(pr₂(ua X Y))

idtoeq' : ∀ {U} (X Y : U ̇) → X ≡ Y → X ≃ Y
idtoeq' X Y p = (pathtofun p , transport-isEquiv p)

idtoEqs-agree : ∀ {U} (X Y : U ̇) → idtoeq' X Y ∼ idtoeq X Y
idtoEqs-agree X _ refl = refl

idtoeq'-eqtoid : ∀ {U} (ua : isUnivalent U)
               → (X Y : U ̇) → idtoeq' X Y ∘ eqtoid ua X Y ∼ id
idtoeq'-eqtoid ua X Y e = idtoEqs-agree X Y (eqtoid ua X Y e) ∙ idtoeq-eqtoid ua X Y e

idtofun-isEquiv : ∀ {U} (X Y : U ̇) (p : X ≡ Y) → isEquiv(idtofun X Y p)
idtofun-isEquiv X Y p = pr₂(idtoeq X Y p)

isUnivalent-≃ : ∀ {U} → isUnivalent U → (X Y : U ̇) → (X ≡ Y) ≃ (X ≃ Y)
isUnivalent-≃ ua X Y = idtoeq X Y , ua X Y

back-transport-is-pre-comp' : ∀ {U} (ua : isUnivalent U)
                           → {X X' Y : U ̇} (e : X ≃ X') (g : X' → Y)
                           → back-transport (λ Z → Z → Y) (eqtoid ua X X' e) g ≡ g ∘ pr₁ e 
back-transport-is-pre-comp' ua {X} {X'} e g = back-transport-is-pre-comp (eqtoid ua X X' e) g ∙ q
 where
  q : g ∘ pathtofun (eqtoid ua X X' e) ≡ g ∘ (pr₁ e)
  q = ap (λ h → g ∘ h) (ap pr₁ (idtoeq'-eqtoid ua X X' e))

preComp-isEquiv : ∀ {U} (ua : isUnivalent U)
                → {X Y Z : U ̇} (f : X → Y) → isEquiv f → isEquiv (λ (g : Y → Z) → g ∘ f)
preComp-isEquiv ua {X} {Y} f ise = equiv-closed-under-∼' (back-transport-isEquiv (eqtoid ua X Y (f , ise)))
                                                          (back-transport-is-pre-comp' ua (f , ise))

\end{code}

Induction on equivalences is available in univalent universes: to
prove that all equivalences satisfy some property, it is enough to
show that the identity equivalences satisfy it.

\begin{code}

identity-data : ∀ {U} (X : U ̇) (i : X → X → U ̇) (r : (x : X) → i x x) → ∀ {V} → U ⊔ V ′ ̇
identity-data {U} X i r {V} =
 Σ \(j : (x : X) (A : (y : X) → i x y → V ̇)
    → A x (r x) → (y : X) (p : i x y) → A y p)
   → (x : X) (A : (y : X) → i x y → V ̇)
    → (b : A x (r x))
    → j x A b x (r x) ≡ b 

JEq : ∀ {U} → isUnivalent U
    → ∀ {V} (X : U ̇) (A : (Y : U ̇) → X ≃ Y → V ̇)
    → A X (ideq X) → (Y : U ̇) (e : X ≃ Y) → A Y e
JEq {U} ua {V} X A b Y e = transport (A Y) (idtoeq-eqtoid ua X Y e) g
 where
  A' : (Y : U ̇) → X ≡ Y → V ̇
  A' Y p = A Y (idtoeq X Y p)
  b' : A' X refl
  b' = b
  f' : (Y : U ̇) (p : X ≡ Y) → A' Y p
  f' = Jbased X A' b'
  g : A Y (idtoeq X Y (eqtoid ua X Y e))
  g = f' Y (eqtoid ua X Y e)

{- TODO:
JEq-comp : ∀ {U} (ua : isUnivalent U)
    → ∀ {V} (X : U ̇) (A : (Y : U ̇) → X ≃ Y → V ̇)
    → (b : A X (ideq X))
    → JEq ua X A b X (ideq X) ≡ b
JEq-comp ua X A b = ?
-}

\end{code}

Conversely, if the induction principle for equivalences with its
computation rule holds, then univalence follows:

\begin{code}

JEq-converse : ∀ {U}
             → (jeq : ∀ {V} (X : U ̇) (A : (Y : U ̇) → X ≃ Y → V ̇)
                → A X (ideq X) → (Y : U ̇) (e : X ≃ Y) → A Y e)
             → (∀ {V} (X : U ̇) (A : (Y : U ̇) → X ≃ Y → V ̇)
                → (b : A X (ideq X)) → jeq X A b X (ideq X) ≡ b)
             → isUnivalent U
JEq-converse {U} jeq jeq-comp X = g
 where
  φ : (Y : U ̇) → X ≃ Y → X ≡ Y
  φ = jeq X (λ Y p → X ≡ Y) refl
  φc : φ X (ideq X) ≡ refl
  φc = jeq-comp X (λ Y p → X ≡ Y) refl
  idtoeqφ : (Y : U ̇) (e : X ≃ Y) → idtoeq X Y (φ Y e) ≡ e
  idtoeqφ = jeq X (λ Y e → idtoeq X Y (φ Y e) ≡ e) (ap (idtoeq X X) φc)
  φidtoeq : (Y : U ̇) (p : X ≡ Y) → φ Y (idtoeq X Y p) ≡ p
  φidtoeq X refl = φc
  g : (Y : U ̇) → isEquiv(idtoeq X Y)
  g Y =  (φ Y , idtoeqφ Y) , (φ Y , φidtoeq Y)
  
isUnivalent-idtoeq-lc : ∀ {U} → isUnivalent U → (X Y : U ̇) → left-cancellable(idtoeq X Y)
isUnivalent-idtoeq-lc ua X Y = section-lc (idtoeq X Y) (pr₂ (ua X Y))

\end{code}

The following has a proof from function extensionality (see e.g. HoTT
Book), but it has a more direct proof from univalence (we also give a
proof without univalence elsewhere, of course):

\begin{code}

open import UF-Subsingletons-Equiv

isEquiv-isVoevodskyEquiv' : ∀ {U} → isUnivalent U → {X Y : U ̇} (f : X → Y)
                         → isEquiv f → isVoevodskyEquiv f
isEquiv-isVoevodskyEquiv' {U} ua {X} {Y} f ise = g Y (f , ise)
 where
  A : (Y : U ̇) → X ≃ Y → U ̇
  A Y (f , ise) = isVoevodskyEquiv f
  b : A X (ideq X)
  b = paths-to-singleton
  g :  (Y : U ̇) (e : X ≃ Y) → A Y e
  g = JEq ua X A b

\end{code}

We have the following characterization of univalence from the Yoneda
machinery.

The fact that this is the case was announced on 5th August
2014 with the techniques of the HoTT Book
(https://groups.google.com/forum/#!msg/homotopytypetheory/HfCB_b-PNEU/Ibb48LvUMeUJ)),
and the proof given here via Yoneda was announced on 12th May 2015
(http:/E/www.cs.bham.ac.uk/~mhe/yoneda/yoneda.html).

\begin{code}

open import UF-Yoneda

univalence-via-singletons : ∀ {U} → isUnivalent U ⇔ ((X : U ̇) → isSingleton (Σ \(Y : U ̇) → X ≃ Y))
univalence-via-singletons {U} = (f , g)
 where
  f : isUnivalent U → (X : U ̇) → isSingleton (Σ (Eq X))
  f ua X = representable-singleton (X , (idtoeq X , ua X))

  g : ((X : U ̇) → isSingleton (Σ (Eq X))) → isUnivalent U
  g φ X = universality-equiv X (ideq X)
                                (unique-element-is-universal-element
                                       (Eq X)
                                       (X , ideq X)
                                       (isSingleton-isProp (φ X) (X , ideq X)))

\end{code}
