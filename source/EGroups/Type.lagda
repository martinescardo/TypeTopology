Martin Escardo, July 2026.

The type of egroups.

An egroup is a setoid, in the sense of the module Setoid, equipped
with a compatible group structure, that is, an operation that is a
congruence for the equivalence relation and whose group laws hold up
to the equivalence relation rather than up to the identity type _＝_.

This is the analogue for setoids of the module Groups.Type. Compared
with Groups.Type:

 * The requirement that X be a set is removed, as all types play the
   role of sets in the setoid world.

 * The operation is required to be a congruence.

 * Every remaining occurrence of the identity type becomes the
   equivalence relation.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EGroups.Type where

open import MLTT.Spartan
open import EGroups.Setoid

\end{code}

We give the axioms of a compatible group structure on a setoid S, and
then the structure and type of egroups. As in Groups.Type, the inverse
is given existentially, as part of the axioms, where Σ is used for
existence in the setoid world.

\begin{code}

egroup-axioms : (S : Setoid 𝓤 𝓥) → (∣ S ∣ → ∣ S ∣ → ∣ S ∣) → 𝓤 ⊔ 𝓥 ̇
egroup-axioms S _·_ =
   is-econgruence  (setoid-relation S) _·_
 × is-eassociative (setoid-relation S) _·_
 × (Σ e ꞉ ∣ S ∣
        , is-eleft-neutral  (setoid-relation S) e _·_
        × is-eright-neutral (setoid-relation S) e _·_
        × ((x : ∣ S ∣)
              → Σ x' ꞉ ∣ S ∣ , ((x' · x) ≈∣ S ∣ e) × ((x · x') ≈∣ S ∣ e)))

egroup-structure : Setoid 𝓤 𝓥 → 𝓤 ⊔ 𝓥 ̇
egroup-structure S = Σ _·_ ꞉ (∣ S ∣ → ∣ S ∣ → ∣ S ∣) , (egroup-axioms S _·_)

EGroup : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
EGroup 𝓤 𝓥 = Σ S ꞉ Setoid 𝓤 𝓥 , egroup-structure S

\end{code}

We write ⟨ G ⟩ for the underlying type and x ≈⟨ G ⟩ y for the
equivalence relation.

\begin{code}

underlying-setoid : EGroup 𝓤 𝓥 → Setoid 𝓤 𝓥
underlying-setoid (S , str) = S

⟨_⟩ : EGroup 𝓤 𝓥 → 𝓤 ̇
⟨ G ⟩ = ∣ underlying-setoid G ∣

underlying-relation : (G : EGroup 𝓤 𝓥) → ⟨ G ⟩ → ⟨ G ⟩ → 𝓥 ̇
underlying-relation G = setoid-relation (underlying-setoid G)

syntax underlying-relation G x y = x ≈⟨ G ⟩ y

erefl : (G : EGroup 𝓤 𝓥) → reflexive (underlying-relation G)
erefl G = setoid-refl (underlying-setoid G)

esym : (G : EGroup 𝓤 𝓥) → symmetric (underlying-relation G)
esym G = setoid-sym (underlying-setoid G)

etrans : (G : EGroup 𝓤 𝓥) → transitive (underlying-relation G)
etrans G = setoid-trans (underlying-setoid G)

emultiplication-of : (G : EGroup 𝓤 𝓥) → ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
emultiplication-of (S , _·_ , _) = _·_

syntax emultiplication-of G x y = x ·⟨ G ⟩ y

econgruence-of : (G : EGroup 𝓤 𝓥)
               → is-econgruence (underlying-relation G) (emultiplication-of G)
econgruence-of (S , _·_ , cong , assoc , e , ln , rn , inverses) = cong

eassoc : (G : EGroup 𝓤 𝓥)
       → is-eassociative (underlying-relation G) (emultiplication-of G)
eassoc (S , _·_ , cong , assoc , e , ln , rn , inverses) = assoc

eunit-of : (G : EGroup 𝓤 𝓥) → ⟨ G ⟩
eunit-of (S , _·_ , cong , assoc , e , ln , rn , inverses) = e

eunit-left
 : (G : EGroup 𝓤 𝓥)
 → is-eleft-neutral (underlying-relation G) (eunit-of G) (emultiplication-of G)
eunit-left (S , _·_ , cong , assoc , e , ln , rn , inverses) = ln

eunit-right
 : (G : EGroup 𝓤 𝓥)
 → is-eright-neutral (underlying-relation G) (eunit-of G) (emultiplication-of G)
eunit-right (S , _·_ , cong , assoc , e , ln , rn , inverses) = rn

einv : (G : EGroup 𝓤 𝓥) → ⟨ G ⟩ → ⟨ G ⟩
einv (S , _·_ , cong , assoc , e , ln , rn , inverses) x = pr₁ (inverses x)

einv-left : (G : EGroup 𝓤 𝓥) (x : ⟨ G ⟩) → (einv G x ·⟨ G ⟩ x) ≈⟨ G ⟩ eunit-of G
einv-left (S , _·_ , cong , assoc , e , ln , rn , inverses) x =
 pr₁ (pr₂ (inverses x))

einv-right : (G : EGroup 𝓤 𝓥) (x : ⟨ G ⟩)
           → (x ·⟨ G ⟩ einv G x) ≈⟨ G ⟩ eunit-of G
einv-right (S , _·_ , cong , assoc , e , ln , rn , inverses) x
 = pr₂ (pr₂ (inverses x))

\end{code}

A homomorphism of egroups is a map of the underlying types that
respects the equivalence relations and is multiplicative up to the
equivalence relation of the codomain. As in Groups.Type, preservation
of the unit and of inverses is not required but is derivable.

\begin{code}

is-hom : (G : EGroup 𝓤 𝓥) (H : EGroup 𝓤' 𝓥')
       → (⟨ G ⟩ → ⟨ H ⟩) → 𝓤 ⊔ 𝓥 ⊔ 𝓥' ̇
is-hom G H f =
   ({x y : ⟨ G ⟩} → x ≈⟨ G ⟩ y → f x ≈⟨ H ⟩ f y)
 × ({x y : ⟨ G ⟩} → f (x ·⟨ G ⟩ y) ≈⟨ H ⟩ (f x ·⟨ H ⟩ f y))

\end{code}

We develop some minimal group theory up to the equivalence relation,
needed for the universal property of free egroups. This is a
transcription of the relevant parts of Groups.Type, with the identity
type replaced by the equivalence relation and with the congruence of
the operation used explicitly.

\begin{code}

module egroup-theory (G : EGroup 𝓤 𝓥) where

 private
  _≈_ = underlying-relation G
  _*_ = emultiplication-of G
  e   = eunit-of G
  inv = einv G

 open ≈-reasoning _≈_ (erefl G) (etrans G)

 ≈-inv-lemma : (x y z : ⟨ G ⟩) → (y * x) ≈ e → (x * z) ≈ e → y ≈ z
 ≈-inv-lemma x y z q p =
  y             ≈[ esym G _ _ (eunit-right G y) ]
  (y * e)       ≈[ econgruence-of G (erefl G y) (esym G _ _ p) ]
  (y * (x * z)) ≈[ esym G _ _ (eassoc G y x z) ]
  ((y * x) * z) ≈[ econgruence-of G q (erefl G z) ]
  (e * z)       ≈[ eunit-left G z ]
  z             ≈∎

 one-left-inv : (x y : ⟨ G ⟩) → (y * x) ≈ e → y ≈ inv x
 one-left-inv x y q = ≈-inv-lemma x y (inv x) q (einv-right G x)

 ≈-idempotent-is-unit : (x : ⟨ G ⟩) → (x * x) ≈ x → x ≈ e
 ≈-idempotent-is-unit x p =
  x                  ≈[ I ]
  (e * x)            ≈[ II ]
  ((inv x * x) * x)  ≈[ III ]
  (inv x * (x * x))  ≈[ IV ]
  (inv x * x)        ≈[ V ]
  e                  ≈∎
   where
    I   = esym G _ _ (eunit-left G x)
    II  = econgruence-of G (esym G _ _ (einv-left G x)) (erefl G x)
    III = eassoc G (inv x) x x
    IV  = econgruence-of G (erefl G (inv x)) p
    V   = einv-left G x

 ≈-inv-cong : (x y : ⟨ G ⟩) → x ≈ y → inv x ≈ inv y
 ≈-inv-cong x y p = one-left-inv y (inv x)
                     (inv x * y ≈[ I ]
                      inv x * x ≈[ II ]
                      e         ≈∎)
  where
   I  = econgruence-of G (erefl G (inv x)) (esym G _ _ p)
   II = einv-left G x

\end{code}

Homomorphisms preserve the unit and inverses. As in Groups.Type, these
are derived from the definition of homomorphism.

\begin{code}

homs-preserve-unit : (G : EGroup 𝓤 𝓥) (H : EGroup 𝓤' 𝓥')
                     (f : ⟨ G ⟩ → ⟨ H ⟩)
                   → is-hom G H f
                   → f (eunit-of G) ≈⟨ H ⟩ eunit-of H
homs-preserve-unit G H f (f-resp , f-mult) =
 ≈-idempotent-is-unit (f eG)
  (f eG ·⟨ H ⟩ f eG ≈[ esym H _ _ (f-mult {eG} {eG}) ]
   f (eG ·⟨ G ⟩ eG) ≈[ f-resp (eunit-left G eG) ]
   f eG             ≈∎)
 where
  open egroup-theory H
  open ≈-reasoning (underlying-relation H) (erefl H) (etrans H)
  eG = eunit-of G

homs-preserve-inv : (G : EGroup 𝓤 𝓥) (H : EGroup 𝓤' 𝓥')
                    (f : ⟨ G ⟩ → ⟨ H ⟩)
                  → is-hom G H f
                  → (x : ⟨ G ⟩) → f (einv G x) ≈⟨ H ⟩ einv H (f x)
homs-preserve-inv G H f fh@(f-resp , f-mult) x =
 one-left-inv (f x) (f (einv G x))
  (f (einv G x) ·⟨ H ⟩ f x ≈[ esym H _ _ (f-mult {einv G x} {x}) ]
   f (einv G x ·⟨ G ⟩ x)   ≈[ f-resp (einv-left G x) ]
   f (eunit-of G)          ≈[ homs-preserve-unit G H f fh ]
   eunit-of H              ≈∎)
 where
  open egroup-theory H
  open ≈-reasoning (underlying-relation H) (erefl H) (etrans H)

\end{code}

The identity is a homomorphism, and homomorphisms compose.

\begin{code}

id-is-hom : (G : EGroup 𝓤 𝓥) → is-hom G G id
id-is-hom G = (λ p → p) , (λ {x} {y} → erefl G (x ·⟨ G ⟩ y))

∘-is-hom : (F : EGroup 𝓤 𝓥) (G : EGroup 𝓤' 𝓥') (H : EGroup 𝓦 𝓦')
           (f : ⟨ F ⟩ → ⟨ G ⟩) (g : ⟨ G ⟩ → ⟨ H ⟩)
         → is-hom F G f
         → is-hom G H g
         → is-hom F H (g ∘ f)
∘-is-hom F G H f g (f-resp , f-mult) (g-resp , g-mult) =
   (λ p → g-resp (f-resp p))
 , (λ {x} {y} → etrans H _ _ _ (g-resp (f-mult {x} {y})) (g-mult {f x} {f y}))

\end{code}

An isomorphism of egroups is a homomorphism with a homomorphism
inverse, up to the equivalence relations.

\begin{code}

is-iso : (G : EGroup 𝓤 𝓥) (H : EGroup 𝓤' 𝓥')
       → (⟨ G ⟩ → ⟨ H ⟩) → 𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥' ̇
is-iso G H f = is-hom G H f
             × (Σ g ꞉ (⟨ H ⟩ → ⟨ G ⟩)
                    , is-hom H G g
                    × ((y : ⟨ H ⟩) → f (g y) ≈⟨ H ⟩ y)
                    × ((x : ⟨ G ⟩) → g (f x) ≈⟨ G ⟩ x))

_≅_ : EGroup 𝓤 𝓥 → EGroup 𝓤' 𝓥' → 𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥' ̇
G ≅ H = Σ f ꞉ (⟨ G ⟩ → ⟨ H ⟩) , is-iso G H f

≅-refl : (G : EGroup 𝓤 𝓥) → G ≅ G
≅-refl G = id , id-is-hom G , id , id-is-hom G , erefl G , erefl G

≅-sym : (G : EGroup 𝓤 𝓥) (H : EGroup 𝓤' 𝓥') → G ≅ H → H ≅ G
≅-sym G H (f , fhom , g , ghom , f-ε , f-θ) =
 g , ghom , f , fhom , f-θ , f-ε

≅-trans : (F : EGroup 𝓤 𝓥) (G : EGroup 𝓤' 𝓥') (H : EGroup 𝓦 𝓦')
        → F ≅ G → G ≅ H → F ≅ H
≅-trans F G H (f , fhom , f⁻ , f⁻hom@(f⁻-resp , _) , f-ε , f-θ)
              (g , ghom@(g-resp , _) , g⁻ , g⁻hom , g-ε , g-θ) =
   g ∘ f
 , ∘-is-hom F G H f g fhom ghom
 , f⁻ ∘ g⁻
 , ∘-is-hom H G F g⁻ f⁻ g⁻hom f⁻hom
 , (λ w → etrans H _ _ _ (g-resp (f-ε (g⁻ w))) (g-ε w))
 , (λ x → etrans F _ _ _ (f⁻-resp (g-θ (f x))) (f-θ x))

\end{code}

We form the setoid of homomorphisms between two egroups, with the
pointwise equivalence relation.

\begin{code}

hom-setoid : (G : EGroup 𝓤 𝓥) (H : EGroup 𝓤' 𝓥')
           → Setoid (𝓤 ⊔ 𝓤' ⊔ 𝓥 ⊔ 𝓥') (𝓤 ⊔ 𝓥')
hom-setoid G H =
   (Σ f ꞉ (⟨ G ⟩ → ⟨ H ⟩) , is-hom G H f)
 , (λ u v → (x : ⟨ G ⟩) → pr₁ u x ≈⟨ H ⟩ pr₁ v x)
 , (λ u x → erefl H (pr₁ u x))
 , (λ u v p x → esym H (pr₁ u x) (pr₁ v x) (p x))
 , (λ u v w p q x → etrans H (pr₁ u x) (pr₁ v x) (pr₁ w x) (p x) (q x))

\end{code}
