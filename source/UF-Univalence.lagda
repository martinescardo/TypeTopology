Formulation of univalence.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Univalence where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Equiv
open import UF-LeftCancellable

is-univalent : ∀ U → U ′ ̇
is-univalent U = (X Y : U ̇) → is-equiv(idtoeq X Y)

eqtoid : ∀ {U} → is-univalent U → (X Y : U ̇) → X ≃ Y → X ≡ Y
eqtoid ua X Y = pr₁(pr₁(ua X Y))

idtoeq-eqtoid : ∀ {U} (ua : is-univalent U)
              → (X Y : U ̇) (e : X ≃ Y) → idtoeq X Y (eqtoid ua X Y e) ≡ e
idtoeq-eqtoid ua X Y = pr₂(pr₁(ua X Y))

eqtoid' : ∀ {U} → is-univalent U → (X Y : U ̇) → X ≃ Y → X ≡ Y
eqtoid' ua X Y = pr₁(pr₂(ua X Y))

eqtoid-idtoeq : ∀ {U} (ua : is-univalent U)
              → (X Y : U ̇) (p : X ≡ Y) →  eqtoid' ua X Y (idtoeq X Y p) ≡ p
eqtoid-idtoeq ua X Y = pr₂(pr₂(ua X Y))

eqtoid-idtoeq' : ∀ {U} (ua : is-univalent U)
              → (X Y : U ̇) (p : X ≡ Y) →  eqtoid ua X Y (idtoeq X Y p) ≡ p
eqtoid-idtoeq' ua X Y = pr₁(pr₂ (is-equiv-qinv (idtoeq X Y) (ua X Y)))

idtoeq' : ∀ {U} (X Y : U ̇) → X ≡ Y → X ≃ Y
idtoeq' X Y p = (Idtofun p , transport-is-equiv p)

idtoEqs-agree : ∀ {U} (X Y : U ̇) → idtoeq' X Y ∼ idtoeq X Y
idtoEqs-agree X _ refl = refl

idtoeq'-eqtoid : ∀ {U} (ua : is-univalent U)
               → (X Y : U ̇) → idtoeq' X Y ∘ eqtoid ua X Y ∼ id
idtoeq'-eqtoid ua X Y e = idtoEqs-agree X Y (eqtoid ua X Y e) ∙ idtoeq-eqtoid ua X Y e

Idtofun-is-equiv : ∀ {U} (X Y : U ̇) (p : X ≡ Y) → is-equiv(idtofun X Y p)
Idtofun-is-equiv X Y p = pr₂(idtoeq X Y p)

is-univalent-≃ : ∀ {U} → is-univalent U → (X Y : U ̇) → (X ≡ Y) ≃ (X ≃ Y)
is-univalent-≃ ua X Y = idtoeq X Y , ua X Y

back-transport-is-pre-comp' : ∀ {U} (ua : is-univalent U)
                           → {X X' Y : U ̇} (e : X ≃ X') (g : X' → Y)
                           → back-transport (λ - → - → Y) (eqtoid ua X X' e) g ≡ g ∘ pr₁ e
back-transport-is-pre-comp' ua {X} {X'} e g = back-transport-is-pre-comp (eqtoid ua X X' e) g ∙ q
 where
  q : g ∘ Idtofun (eqtoid ua X X' e) ≡ g ∘ (pr₁ e)
  q = ap (λ - → g ∘ -) (ap pr₁ (idtoeq'-eqtoid ua X X' e))

preComp-is-equiv : ∀ {U} (ua : is-univalent U)
                → {X Y Z : U ̇} (f : X → Y) → is-equiv f → is-equiv (λ (g : Y → Z) → g ∘ f)
preComp-is-equiv ua {X} {Y} f ise =
 equiv-closed-under-∼' (back-transport-is-equiv (eqtoid ua X Y (f , ise)))
                        (back-transport-is-pre-comp' ua (f , ise))

\end{code}

Induction on equivalences is available in univalent universes: to
prove that all equivalences satisfy some property, it is enough to
show that the identity equivalences satisfy it.

\begin{code}

Eq-induction : (U V : Universe) → (U ⊔ V)′ ̇
Eq-induction U V = (X : U ̇) (A : (Y : U ̇) → X ≃ Y → V ̇)
                 → A X (ideq X) → (Y : U ̇) (e : X ≃ Y) → A Y e

JEq : ∀ {U} → is-univalent U → ∀ {V} → Eq-induction U V
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

Eq-transport : ∀ {U} → is-univalent U
            → ∀ {V} (A : U ̇ → V ̇) {X Y : U ̇} → X ≃ Y → A X → A Y
Eq-transport {U} ua {V} A {X} {Y} e a = JEq ua X (λ Z e → A Z) a Y e

Eq-induction' : (U V : Universe) → (U ⊔ V)′ ̇
Eq-induction' U V = (A : (X Y : U ̇) → X ≃ Y → V ̇)
                 → ((X : U ̇) → A X X (ideq X)) → (X Y : U ̇) (e : X ≃ Y) → A X Y e

JEq' : ∀ {U} → is-univalent U → ∀ {V} → Eq-induction' U V
JEq' ua A f X = JEq ua X (λ Y → A X Y) (f X)

\end{code}

Conversely, if the induction principle for equivalences holds, then
univalence follows. In this construction, the parametric universe V is
instantiated to the universe U and its successor U ′ only. This was
produced 18th May 2018 while visiting the Hausdorff Research Institute
for Mathematics in Bonn.

\begin{code}

JEq-converse : ∀ {U} → (∀ {V} → Eq-induction U V) → is-univalent U
JEq-converse {U} jeq' X = γ
 where

\end{code}

  The following is an adaptation of an 'improvement method' I learned
  from Peter Lumsdaine, 7 July 2017, when we were both visiting the
  Newton Institute. His original version translated to Agda is here:
  http://www.cs.bham.ac.uk/~mhe/agda-new/Lumsdaine.html

  Unfortunately, we couldn't use his result off-the-shelf. The main
  difference is that Peter works with a global identity system on all
  types (of a universe), whereas we work with an identity system on a
  single type, namely a universe. As a result, we can't define the
  type of left-cancellable maps using the notion of equality given by
  the identity system, as Peter does. Instead, we define it using the
  native (Martin-Loef) identity type, and with this little
  modification, Peter's argument goes through for the situation
  considered here.

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
  γ : (Y : U ̇) → is-equiv(idtoeq X Y)
  γ Y =  (φ Y , idtoeqφ Y) , (φ Y , φidtoeq Y)

\end{code}

This completes the deduction of univalence from equivalence
induction. The following technical lemma is needed elsewhere.

\begin{code}

is-univalent-idtoeq-lc : ∀ {U} → is-univalent U → (X Y : U ̇) → left-cancellable(idtoeq X Y)
is-univalent-idtoeq-lc ua X Y = section-lc (idtoeq X Y) (pr₂ (ua X Y))

\end{code}

The following has a proof from function extensionality, but it has a
more direct proof from equivalence induction (we also give a proof
without univalence elsewhere, of course):

\begin{code}

open import UF-Subsingletons-Equiv

is-equiv-is-vv-equiv' : ∀ {U} → is-univalent U → {X Y : U ̇} (f : X → Y)
                     → is-equiv f → is-vv-equiv f
is-equiv-is-vv-equiv' {U} ua {X} {Y} f ise = g Y (f , ise)
 where
  A : (Y : U ̇) → X ≃ Y → U ̇
  A Y (f , ise) = is-vv-equiv f
  b : A X (ideq X)
  b = identifications-to-singleton
  g : (Y : U ̇) (e : X ≃ Y) → A Y e
  g = JEq ua X A b


UA-gives-propext : ∀ {U} → is-univalent U → propext U
UA-gives-propext ua {P} {Q} i j f g = eqtoid ua P Q
                                       (f ,
                                       (g , (λ y → j (f (g y)) y)) ,
                                       (g , (λ x → i (g (f x)) x)))

\end{code}

If the identity function satisfies some property, then all
equivalences do, assuming univalence. This property need not be
subsingleton valued.

\begin{code}

ua-all-from-id : ∀ {U V} → is-univalent U
           → (X : U ̇)
           → (P : (Y : U ̇) → (X → Y) → V ̇)
           → P X id
           → (Y : U ̇) (f : X → Y) → is-equiv f → P Y f
ua-all-from-id {U} {V} ua X P b Y f e = JEq ua X A b Y (f , e)
 where
  A : (Y : U ̇) → X ≃ Y → V ̇
  A Y (f , _) = P Y f

\end{code}

TODO. The converse. From this we get univalence.
