Martin Escardo.

Formulation of univalence. Notice that this file doesn't postulate
univalence. It only defines the notion of univalent
universe. Univalence, when used, is taken as an explicit hypothesis.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module UF-Univalence where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Equiv
open import UF-LeftCancellable

is-univalent : ∀ 𝓤 → 𝓤 ⁺ ̇
is-univalent 𝓤 = (X Y : 𝓤 ̇ ) → is-equiv(idtoeq X Y)

Univalence : 𝓤ω
Univalence = (𝓤 : Universe) → is-univalent 𝓤

idtoeq' : (X Y : 𝓤 ̇ ) → X ≡ Y → X ≃ Y
idtoeq' X Y p = (Idtofun p , transports-are-equivs p)

idtoEqs-agree : (X Y : 𝓤 ̇ ) → idtoeq' X Y ∼ idtoeq X Y
idtoEqs-agree X _ refl = refl

Idtofun-is-equiv : (X Y : 𝓤 ̇ ) (p : X ≡ Y) → is-equiv(idtofun X Y p)
Idtofun-is-equiv X Y p = pr₂(idtoeq X Y p)

module _
        (ua : is-univalent 𝓤)
       where

 eqtoid : (X Y : 𝓤 ̇ ) → X ≃ Y → X ≡ Y
 eqtoid X Y = pr₁(pr₁(ua X Y))

 idtoeq-eqtoid : (X Y : 𝓤 ̇ ) (e : X ≃ Y) → idtoeq X Y (eqtoid X Y e) ≡ e
 idtoeq-eqtoid X Y = pr₂(pr₁(ua X Y))

 eqtoid-idtoeq : (X Y : 𝓤 ̇ ) (p : X ≡ Y) →  eqtoid X Y (idtoeq X Y p) ≡ p
 eqtoid-idtoeq X Y = pr₁(pr₂ (equivs-are-qinvs (idtoeq X Y) (ua X Y)))

 eqtoid-refl : (X : 𝓤 ̇ ) → eqtoid X X (≃-refl X) ≡ refl
 eqtoid-refl X = eqtoid-idtoeq X X refl

 idtoeq'-eqtoid : (X Y : 𝓤 ̇ ) → idtoeq' X Y ∘ eqtoid X Y ∼ id
 idtoeq'-eqtoid X Y e = idtoEqs-agree X Y (eqtoid X Y e) ∙ idtoeq-eqtoid X Y e

 idtofun-eqtoid : {X Y : 𝓤 ̇ } (e : X ≃ Y)
                → idtofun X Y (eqtoid X Y e) ≡ ⌜ e ⌝
 idtofun-eqtoid {X} {Y} e = ap pr₁ (idtoeq-eqtoid X Y e)

 Idtofun-eqtoid : {X Y : 𝓤 ̇ } (e : X ≃ Y)
                → Idtofun (eqtoid X Y e) ≡ ⌜ e ⌝
 Idtofun-eqtoid {X} {Y} e =
  (idtofun-agreement X Y (eqtoid X Y e)) ⁻¹ ∙ idtofun-eqtoid e

 Idtofun-∙ : {X Y Z : 𝓤 ̇ } (p : X ≡ Y) (q : Y ≡ Z)
           → Idtofun (p ∙ q) ≡ Idtofun q ∘ Idtofun p
 Idtofun-∙ refl refl = refl

 univalence-≃ : (X Y : 𝓤 ̇ ) → (X ≡ Y) ≃ (X ≃ Y)
 univalence-≃ X Y = idtoeq X Y , ua X Y

 back-transport-is-pre-comp' : {X X' Y : 𝓤 ̇ } (e : X ≃ X') (g : X' → Y)
                             → transport⁻¹ (λ - → - → Y) (eqtoid X X' e) g ≡ g ∘ ⌜ e ⌝
 back-transport-is-pre-comp' {X} {X'} e g = transport⁻¹-is-pre-comp (eqtoid X X' e) g ∙ q
  where
   q : g ∘ Idtofun (eqtoid X X' e) ≡ g ∘ ⌜ e ⌝
   q = ap (g ∘_) (ap ⌜_⌝ (idtoeq'-eqtoid X X' e))

 pre-comp-is-equiv : {X Y Z : 𝓤 ̇ } (f : X → Y)
                   → is-equiv f → is-equiv (λ (g : Y → Z) → g ∘ f)
 pre-comp-is-equiv {X} {Y} f ise =
  equiv-closed-under-∼' (back-transports-are-equivs (eqtoid X Y (f , ise)))
                        (back-transport-is-pre-comp' (f , ise))

\end{code}

Induction on equivalences is available in univalent universes: to
prove that all equivalences satisfy some property, it is enough to
show that the identity equivalences satisfy it.

\begin{code}

≃-induction : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
≃-induction 𝓤 𝓥 = (X : 𝓤 ̇ ) (A : (Y : 𝓤 ̇ ) → X ≃ Y → 𝓥 ̇ )
                 → A X (≃-refl X) → (Y : 𝓤 ̇ ) (e : X ≃ Y) → A Y e

private
 JEq' : is-univalent 𝓤 → ∀ {𝓥} → ≃-induction 𝓤 𝓥
 JEq' {𝓤} ua {𝓥} X A b Y e = transport (A Y) (idtoeq-eqtoid ua X Y e) g
  where
   A' : (Y : 𝓤 ̇ ) → X ≡ Y → 𝓥 ̇
   A' Y p = A Y (idtoeq X Y p)
   b' : A' X refl
   b' = b
   f' : (Y : 𝓤 ̇ ) (p : X ≡ Y) → A' Y p
   f' = Jbased X A' b'
   g : A Y (idtoeq X Y (eqtoid ua X Y e))
   g = f' Y (eqtoid ua X Y e)

eqtoid-inverse : (ua : is-univalent 𝓤) {X X' : 𝓤 ̇ } (e : X ≃ X')
               → (eqtoid ua X X' e)⁻¹ ≡ eqtoid ua X' X (≃-sym e)
eqtoid-inverse ua {X} {X'} = JEq' ua X (λ X' e → (eqtoid ua X X' e)⁻¹ ≡ eqtoid ua X' X (≃-sym e)) p X'
 where
  p : (eqtoid ua X X (≃-refl X))⁻¹ ≡ eqtoid ua X X (≃-sym (≃-refl X))
  p = ap _⁻¹ (eqtoid-refl ua X) ∙ (eqtoid-refl ua X)⁻¹

idtofun-eqtoid-⁻¹ : (ua : is-univalent 𝓤) {X Y : 𝓤 ̇ } (e : X ≃ Y)
                  → idtofun Y X ((eqtoid ua X Y e) ⁻¹) ≡ ⌜ e ⌝⁻¹
idtofun-eqtoid-⁻¹ ua {X} {Y} e =
 idtofun Y X ((eqtoid ua X Y e) ⁻¹)    ≡⟨ I  ⟩
 idtofun Y X (eqtoid ua Y X (≃-sym e)) ≡⟨ II ⟩
 ⌜ e ⌝⁻¹                               ∎
  where
   I  = ap (idtofun Y X) (eqtoid-inverse ua e)
   II = idtofun-eqtoid ua (≃-sym e)

Idtofun-eqtoid-⁻¹ : (ua : is-univalent 𝓤) {X Y : 𝓤 ̇ } (e : X ≃ Y)
                  → Idtofun ((eqtoid ua X Y e) ⁻¹) ≡ ⌜ e ⌝⁻¹
Idtofun-eqtoid-⁻¹ ua {X} {Y} e =
 (idtofun-agreement Y X ((eqtoid ua X Y e) ⁻¹)) ⁻¹ ∙ idtofun-eqtoid-⁻¹ ua e

transport-is-pre-comp' : (ua : is-univalent 𝓤)
                       → {X X' Y : 𝓤 ̇ } (e : X ≃ X') (g : X → Y)
                       → transport (λ - → - → Y) (eqtoid ua X X' e) g ≡ g ∘ ⌜ e ⌝⁻¹
transport-is-pre-comp' ua {X} {X'} e g = transport-is-pre-comp (eqtoid ua X X' e) g ∙ q
 where
  b : Idtofun ((eqtoid ua X X' e)⁻¹) ≡ Idtofun (eqtoid ua X' X (≃-sym e))
  b = ap Idtofun (eqtoid-inverse ua e)
  c : Idtofun (eqtoid ua X' X (≃-sym e)) ≡ pr₁ (≃-sym e)
  c = ap pr₁ (idtoeq'-eqtoid ua X' X (≃-sym e))
  q : g ∘ Idtofun ((eqtoid ua X X' e)⁻¹) ≡ g ∘ pr₁ (≃-sym e)
  q = ap (g ∘_) (b ∙ c)

\end{code}

A public, improved version JEq of JEq' is provided below.

Conversely, if the induction principle for equivalences holds, then
univalence follows. In this construction, the parametric universe V is
instantiated to the universe U and its successor 𝓤 ⁺ only. This was
produced 18th May 2018 while visiting the Hausdorff Research Institute
for Mathematics in Bonn.

The following is an adaptation of an 'improvement method' I learned
from Peter Lumsdaine, 7 July 2017, when we were both visiting the
Newton Institute. His original version translated to Agda is here:
http://www.cs.bham.ac.uk/~mhe/TypeTopology/Lumsdaine.html

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

JEq-improve : ∀ {𝓤 𝓥}
            → (jeq' : ≃-induction 𝓤 𝓥)
            → Σ jeq ꞉ ≃-induction 𝓤 𝓥 , ((X : 𝓤 ̇ ) (A : (Y : 𝓤 ̇ ) → X ≃ Y → 𝓥 ̇ ) (b : A X (≃-refl X))
                                      → jeq X A b X (≃-refl X) ≡ b)
JEq-improve {𝓤} {𝓥} jeq' = jeq , jeq-comp
 where
  module _ (X : 𝓤 ̇ ) (A : (Y : 𝓤 ̇ ) → X ≃ Y → 𝓥 ̇ ) where
   g : {Y Z : 𝓤 ̇ } (p : X ≃ Y) (q : X ≃ Z) → Σ f ꞉ (A Y p → A Z q) , left-cancellable f
   g {Y} {Z} p q = jeq' X B b Z q
    where
     B : (T : 𝓤 ̇ ) → X ≃ T → 𝓥 ̇
     B T q = Σ f ꞉ (A Y p → A T q) , left-cancellable f
     C : (T : 𝓤 ̇ ) → X ≃ T → 𝓥 ̇
     C T p = Σ f ꞉ (A T p → A X (≃-refl X)), left-cancellable f
     b : B X (≃-refl X)
     b = jeq' X C ((λ a → a) , λ p → p) _ p

   h : (b : A X (≃-refl X)) {Y : 𝓤 ̇ } (p : X ≃ Y)
     → Σ a ꞉ A Y p , pr₁ (g p p) a ≡ pr₁ (g (≃-refl X) p) b
   h b p = jeq' X B (b , refl) _ p
    where
     B : (Y : 𝓤 ̇ ) (p : X ≃ Y) → 𝓥 ̇
     B Y p = Σ a ꞉ A Y p , pr₁ (g p p) a ≡ pr₁ (g (≃-refl X) p) b

   jeq : A X (≃-refl X) → (Y : 𝓤 ̇ ) (p : X ≃ Y) → A Y p
   jeq b Y p = pr₁ (h b p)

   jeq-comp : (b : A X (≃-refl X)) → jeq b X (≃-refl X) ≡ b
   jeq-comp b = pr₂ (g (≃-refl X) (≃-refl X)) (pr₂ (h b (≃-refl X)))

\end{code}

This is the end of Peter's construction, which we apply to our problem
as follows:

\begin{code}

JEq-converse :(∀ {𝓥} → ≃-induction 𝓤 𝓥) → is-univalent 𝓤
JEq-converse {𝓤} jeq' X = γ
 where
  jeq : ∀ {𝓥} → ≃-induction 𝓤 𝓥
  jeq {𝓥} = pr₁ (JEq-improve (jeq' {𝓥}))
  jeq-comp : ∀ {𝓥} (X : 𝓤 ̇ ) (A : (Y : 𝓤 ̇ ) → X ≃ Y → 𝓥 ̇ ) (b : A X (≃-refl X))
          → jeq X A b X (≃-refl X) ≡ b
  jeq-comp {𝓥} = pr₂ (JEq-improve (jeq' {𝓥}))
  φ : (Y : 𝓤 ̇ ) → X ≃ Y → X ≡ Y
  φ = jeq X (λ Y p → X ≡ Y) refl
  φc : φ X (≃-refl X) ≡ refl
  φc = jeq-comp X (λ Y p → X ≡ Y) refl
  idtoeqφ : (Y : 𝓤 ̇ ) (e : X ≃ Y) → idtoeq X Y (φ Y e) ≡ e
  idtoeqφ = jeq X (λ Y e → idtoeq X Y (φ Y e) ≡ e) (ap (idtoeq X X) φc)
  φidtoeq : (Y : 𝓤 ̇ ) (p : X ≡ Y) → φ Y (idtoeq X Y p) ≡ p
  φidtoeq X refl = φc
  γ : (Y : 𝓤 ̇ ) → is-equiv(idtoeq X Y)
  γ Y =  (φ Y , idtoeqφ Y) , (φ Y , φidtoeq Y)

\end{code}

This completes the deduction of univalence from equivalence. Now we
improve our original JEq', to get the computation rule for free (even
if the computation rule holds for the original JEq').

\begin{code}

JEq : is-univalent 𝓤 → ∀ {𝓥} → ≃-induction 𝓤 𝓥
JEq ua = pr₁ (JEq-improve (JEq' ua))

JEq-comp : (ua : is-univalent 𝓤) (X : 𝓤 ̇ ) (A : (Y : 𝓤 ̇ ) → X ≃ Y → 𝓥 ̇ ) (b : A X (≃-refl X))
         → JEq ua X A b X (≃-refl X) ≡ b
JEq-comp ua = pr₂ (JEq-improve (JEq' ua))

\end{code}

A much more transparent and shorter construction of JEq and JEq-comp
is in my MGS'2019 lecture notes and in the module
MGS-Equivalence-induction.

\begin{code}

≃-transport : is-univalent 𝓤
            → ∀ {𝓥} (A : 𝓤 ̇ → 𝓥 ̇ ) {X Y : 𝓤 ̇ } → X ≃ Y → A X → A Y
≃-transport {𝓤} ua {𝓥} A {X} {Y} e a = JEq ua X (λ Z e → A Z) a Y e

≃-induction' : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
≃-induction' 𝓤  𝓥 = (A : (X Y : 𝓤 ̇ ) → X ≃ Y → 𝓥 ̇ )
                 → ((X : 𝓤 ̇ ) → A X X (≃-refl X)) → (X Y : 𝓤 ̇ ) (e : X ≃ Y) → A X Y e

JEqUnbased : is-univalent 𝓤 → ∀ {𝓥} → ≃-induction' 𝓤 𝓥
JEqUnbased ua A f X = JEq ua X (λ Y → A X Y) (f X)

\end{code}

The following technical lemma is needed elsewhere.

\begin{code}

is-univalent-idtoeq-lc : is-univalent 𝓤 → (X Y : 𝓤 ̇ ) → left-cancellable(idtoeq X Y)
is-univalent-idtoeq-lc ua X Y = section-lc (idtoeq X Y) (pr₂ (ua X Y))

\end{code}

The following has a proof from function extensionality, but it has a
more direct proof from equivalence induction (we also give a proof
without univalence elsewhere, of course):

\begin{code}

equivs-are-vv-equivs' : is-univalent 𝓤 → {X Y : 𝓤 ̇ } (f : X → Y)
                      → is-equiv f → is-vv-equiv f
equivs-are-vv-equivs' {𝓤} ua {X} {Y} f ise = g Y (f , ise)
 where
  A : (Y : 𝓤 ̇ ) → X ≃ Y → 𝓤 ̇
  A Y (f , ise) = is-vv-equiv f
  b : A X (≃-refl X)
  b = singleton-types'-are-singletons
  g : (Y : 𝓤 ̇ ) (e : X ≃ Y) → A Y e
  g = JEq ua X A b


univalence-gives-propext : is-univalent 𝓤 → propext 𝓤
univalence-gives-propext ua {P} {Q} i j f g = eqtoid ua P Q
                                       (f ,
                                       (g , (λ y → j (f (g y)) y)) ,
                                       (g , (λ x → i (g (f x)) x)))

Univalence-gives-PropExt : Univalence → PropExt
Univalence-gives-PropExt ua 𝓤 = univalence-gives-propext (ua 𝓤)

Univalence-gives-Prop-Ext : Univalence → Prop-Ext
Univalence-gives-Prop-Ext ua {𝓤} = univalence-gives-propext (ua 𝓤)

\end{code}

If the identity function satisfies some property, then all
equivalences do, assuming univalence. This property need not be
prop valued.

\begin{code}

equiv-induction : is-univalent 𝓤
               → (X : 𝓤 ̇ )
               → (P : (Y : 𝓤 ̇ ) → (X → Y) → 𝓥 ̇ )
               → P X id
               → (Y : 𝓤 ̇ ) (f : X → Y) → is-equiv f → P Y f
equiv-induction {𝓤} {𝓥} ua X P b Y f e = JEq ua X A b Y (f , e)
 where
  A : (Y : 𝓤 ̇ ) → X ≃ Y → 𝓥 ̇
  A Y (f , _) = P Y f

\end{code}
