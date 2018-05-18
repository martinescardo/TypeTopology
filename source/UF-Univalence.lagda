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

Eq-induction : (U V : Universe) → (U ⊔ V)′ ̇
Eq-induction U V = (X : U ̇) (A : (Y : U ̇) → X ≃ Y → V ̇)
                 → A X (ideq X) → (Y : U ̇) (e : X ≃ Y) → A Y e

JEq : ∀ {U} → isUnivalent U → ∀ {V} → Eq-induction U V
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

\end{code}

Conversely, if the induction principle for equivalences holds, then
univalence follows. In this construction, the parametric universe V is
instantiated to the universe U and its successor U ′ only. This was
produced 18th May 2018 while visiting the Hausdorff Research Institute
for Mathematics in Bonn.

\begin{code}

JEq-converse : ∀ {U} → (∀ {V} → Eq-induction U V) → isUnivalent U
JEq-converse {U} jeq' X = γ
 where

\end{code}

  The following is an adaptation of an 'improvement method' I learned
  from Peter Lumsdaine, 7 July 2017, when we were both visiting the
  Newton Institute. The adaptation is needed because our assumptions
  are not quite the same as Peter's. The main difference is that for
  the type of left-cancellable maps we use the native identity
  type. This is because he works with a global identity system on all
  types, whereas we consider an identity system on one type only,
  namely the universe U. His original version is here:
  http://www.cs.bham.ac.uk/~mhe/agda-new/Lumsdaine.html

\begin{code}

  module _ {V} (A : (Y : U ̇) → X ≃ Y → V ̇) where
   g : {Y Z : U ̇} (p : X ≃ Y) (q : X ≃ Z) → Σ \(f : A Y p → A Z q) → left-cancellable f
   g {Y} {Z} p q = jeq' X B b Z q
    where
     B : (T : U ̇) → X ≃ T → V ̇
     B T q = Σ \(f : A Y p → A T q) → left-cancellable f
     C : (T : U ̇) → X ≃ T → V ̇
     C T p = Σ \(f : A T p → A X (ideq X)) → left-cancellable f
     b : B X (ideq X)
     b = jeq' X C ((λ a → a) , λ p → p) _ p

   h : (b : A X (ideq X)) {Y : U ̇} (p : X ≃ Y)
     → Σ \(a : A Y p) → pr₁ (g p p) a ≡ pr₁ (g (ideq X) p) b
   h b p = jeq' X B (b , refl) _ p
    where
     B : (Y : U ̇) (p : X ≃ Y) → V ̇
     B Y p = Σ \(a : A Y p) → pr₁ (g p p) a ≡ pr₁ (g (ideq X) p) b
   
   jeq : A X (ideq X) → (Y : U ̇) (p : X ≃ Y) → A Y p
   jeq b Y p = pr₁ (h b p)

   jeq-comp : (b : A X (ideq X)) → jeq b X (ideq X) ≡ b
   jeq-comp b = pr₂ (g (ideq X) (ideq X)) (pr₂ (h b (ideq X)))

\end{code}

  This is the end of Peter's construction, which we apply to our
  problem as follows:
   
\begin{code}

  φ : (Y : U ̇) → X ≃ Y → X ≡ Y
  φ = jeq {U ′} (λ Y p → X ≡ Y) refl
  φc : φ X (ideq X) ≡ refl
  φc = jeq-comp {U ′} (λ Y p → X ≡ Y) refl
  idtoeqφ : (Y : U ̇) (e : X ≃ Y) → idtoeq X Y (φ Y e) ≡ e
  idtoeqφ = jeq {U} (λ Y e → idtoeq X Y (φ Y e) ≡ e) (ap (idtoeq X X) φc)
  φidtoeq : (Y : U ̇) (p : X ≡ Y) → φ Y (idtoeq X Y p) ≡ p
  φidtoeq X refl = φc
  γ : (Y : U ̇) → isEquiv(idtoeq X Y)
  γ Y =  (φ Y , idtoeqφ Y) , (φ Y , φidtoeq Y)

\end{code}

This completes the deduction of univalence from equivalence
induction. The following technical lemma is needed elsewhere.

\begin{code}

isUnivalent-idtoeq-lc : ∀ {U} → isUnivalent U → (X Y : U ̇) → left-cancellable(idtoeq X Y)
isUnivalent-idtoeq-lc ua X Y = section-lc (idtoeq X Y) (pr₂ (ua X Y))

\end{code}

The following has a proof from function extensionality, but it has a
more direct proof from equivalence induction (we also give a proof
without univalence elsewhere, of course):

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
