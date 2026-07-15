Martin Escardo, July 2026.

The type of egroups.

An egroup is a setoid (defined in EGroups.Setoid) equipped with a
compatible group structure, that is, an operation that is a congruence
for the equivalence relation, whose group laws hold up to the
equivalence relation rather than up to the identity type _＝_.

This is the analogue, for setoids, of the module Groups.Type. Compared
with Groups.Type:

 * The requirement "is-set X" is removed, as all types are considered
   to be sets in the setoid world.

 * The operation is required to be a congruence.

 * Every remaining occurrence of the identity type becomes the
   equivalence relation.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EGroups.Type where

open import MLTT.Spartan
open import EGroups.Setoid

\end{code}

The axioms of a compatible group structure on a setoid S, and the
structure and type of EGroups. As in Groups.Type, the inverse is given
existentially, as part of the axioms, where Σ is used for existence in
the setoid world.

\begin{code}

egroup-axioms : (S : Setoid 𝓤 𝓥) → (∣ S ∣ → ∣ S ∣ → ∣ S ∣) → 𝓤 ⊔ 𝓥 ̇
egroup-axioms S _·_ =
   is-congruence   (setoid-relation S) _·_
 × ≈-associative   (setoid-relation S) _·_
 × (Σ e ꞉ ∣ S ∣ , ≈-left-neutral  (setoid-relation S) e _·_
                × ≈-right-neutral (setoid-relation S) e _·_
                × ((x : ∣ S ∣) → Σ x' ꞉ ∣ S ∣ , ((x' · x) ≈⟦ S ⟧ e)
                                              × ((x · x') ≈⟦ S ⟧ e)))

egroup-structure : Setoid 𝓤 𝓥 → 𝓤 ⊔ 𝓥 ̇
egroup-structure S = Σ _·_ ꞉ (∣ S ∣ → ∣ S ∣ → ∣ S ∣) , (egroup-axioms S _·_)

EGroup : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
EGroup 𝓤 𝓥 = Σ S ꞉ Setoid 𝓤 𝓥 , egroup-structure S

\end{code}

We write ⟨ G ⟩ for the underlying type and x ≈⟨ G ⟩ y for the
equivalence relation.

\begin{code}

underlying-setoid : EGroup 𝓤 𝓥 → Setoid 𝓤 𝓥
underlying-setoid (S , _) = S

⟨_⟩ : EGroup 𝓤 𝓥 → 𝓤 ̇
⟨ G ⟩ = ∣ underlying-setoid G ∣

underlying-relation : (G : EGroup 𝓤 𝓥) → ⟨ G ⟩ → ⟨ G ⟩ → 𝓥 ̇
underlying-relation G = setoid-relation (underlying-setoid G)

syntax underlying-relation G x y = x ≈⟨ G ⟩ y

E-refl : (G : EGroup 𝓤 𝓥) → reflexive (underlying-relation G)
E-refl G = setoid-refl (underlying-setoid G)

E-sym : (G : EGroup 𝓤 𝓥) → symmetric (underlying-relation G)
E-sym G = setoid-sym (underlying-setoid G)

E-trans : (G : EGroup 𝓤 𝓥) → transitive (underlying-relation G)
E-trans G = setoid-trans (underlying-setoid G)

E-multiplication : (G : EGroup 𝓤 𝓥) → ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
E-multiplication (S , _·_ , _) = _·_

syntax E-multiplication G x y = x ·⟨ G ⟩ y

E-is-congruence : (G : EGroup 𝓤 𝓥)
                → is-congruence (underlying-relation G) (E-multiplication G)
E-is-congruence (S , _·_ , cong , _) = cong

E-assoc : (G : EGroup 𝓤 𝓥)
        → ≈-associative (underlying-relation G) (E-multiplication G)
E-assoc (S , _·_ , cong , assoc , _) = assoc

E-unit : (G : EGroup 𝓤 𝓥) → ⟨ G ⟩
E-unit (S , _·_ , cong , assoc , e , _) = e

E-unit-left : (G : EGroup 𝓤 𝓥)
            → ≈-left-neutral (underlying-relation G) (E-unit G) (E-multiplication G)
E-unit-left (S , _·_ , cong , assoc , e , ln , _) = ln

E-unit-right : (G : EGroup 𝓤 𝓥)
             → ≈-right-neutral (underlying-relation G) (E-unit G) (E-multiplication G)
E-unit-right (S , _·_ , cong , assoc , e , ln , rn , _) = rn

E-inv : (G : EGroup 𝓤 𝓥) → ⟨ G ⟩ → ⟨ G ⟩
E-inv (S , _·_ , cong , assoc , e , ln , rn , inverses) x = pr₁ (inverses x)

E-inv-left : (G : EGroup 𝓤 𝓥) (x : ⟨ G ⟩) → (E-inv G x ·⟨ G ⟩ x) ≈⟨ G ⟩ E-unit G
E-inv-left (S , _·_ , cong , assoc , e , ln , rn , inverses) x = pr₁ (pr₂ (inverses x))

E-inv-right : (G : EGroup 𝓤 𝓥) (x : ⟨ G ⟩) → (x ·⟨ G ⟩ E-inv G x) ≈⟨ G ⟩ E-unit G
E-inv-right (S , _·_ , cong , assoc , e , ln , rn , inverses) x = pr₂ (pr₂ (inverses x))

\end{code}

Homomorphisms of egroups: maps of the underlying types that respect the
equivalence relations and are multiplicative up to the equivalence
relation of the codomain. As in Groups.Type, preservation of the unit
and of inverses is not required but is derivable.

\begin{code}

is-hom : (G : EGroup 𝓤 𝓥) (H : EGroup 𝓤' 𝓥')
       → (⟨ G ⟩ → ⟨ H ⟩) → 𝓤 ⊔ 𝓥 ⊔ 𝓥' ̇
is-hom G H f =
   ({x y : ⟨ G ⟩} → x ≈⟨ G ⟩ y → f x ≈⟨ H ⟩ f y)
 × ({x y : ⟨ G ⟩} → f (x ·⟨ G ⟩ y) ≈⟨ H ⟩ (f x ·⟨ H ⟩ f y))

\end{code}

Some minimal group theory up to the equivalence relation, needed for
the universal property of free EGroups. This is a transcription of the
relevant parts of Groups.Type, with the identity type replaced by the
equivalence relation and with the congruence of the operation used
explicitly.

\begin{code}

module E-group-theory (G : EGroup 𝓤 𝓥) where

 private
  _≈_ = underlying-relation G
  _*_ = E-multiplication G
  e   = E-unit G
  inv = E-inv G

 open ≈-reasoning _≈_ (E-refl G) (E-trans G)

 ≈-inv-lemma : (x y z : ⟨ G ⟩) → (y * x) ≈ e → (x * z) ≈ e → y ≈ z
 ≈-inv-lemma x y z q p =
  y             ≈[ E-sym G _ _ (E-unit-right G y) ]
  (y * e)       ≈[ E-is-congruence G (E-refl G y) (E-sym G _ _ p) ]
  (y * (x * z)) ≈[ E-sym G _ _ (E-assoc G y x z) ]
  ((y * x) * z) ≈[ E-is-congruence G q (E-refl G z) ]
  (e * z)       ≈[ E-unit-left G z ]
  z             ≈∎

 one-left-inv : (x y : ⟨ G ⟩) → (y * x) ≈ e → y ≈ inv x
 one-left-inv x y q = ≈-inv-lemma x y (inv x) q (E-inv-right G x)

 ≈-idempotent-is-unit : (x : ⟨ G ⟩) → (x * x) ≈ x → x ≈ e
 ≈-idempotent-is-unit x p =
  x                  ≈[ E-sym G _ _ (E-unit-left G x) ]
  (e * x)            ≈[ E-is-congruence G (E-sym G _ _ (E-inv-left G x)) (E-refl G x) ]
  ((inv x * x) * x)  ≈[ E-assoc G (inv x) x x ]
  (inv x * (x * x))  ≈[ E-is-congruence G (E-refl G (inv x)) p ]
  (inv x * x)        ≈[ E-inv-left G x ]
  e                  ≈∎

 ≈-inv-cong : (x y : ⟨ G ⟩) → x ≈ y → inv x ≈ inv y
 ≈-inv-cong x y p = one-left-inv y (inv x)
                     (inv x * y ≈[ E-is-congruence G (E-refl G (inv x)) (E-sym G _ _ p) ]
                      inv x * x ≈[ E-inv-left G x ]
                      e         ≈∎)

\end{code}

Homomorphisms preserve the unit and inverses. As in Groups.Type, these
are derived from the definition of homomorphism.

\begin{code}

homs-preserve-unit : (G : EGroup 𝓤 𝓥) (H : EGroup 𝓤' 𝓥')
                     (f : ⟨ G ⟩ → ⟨ H ⟩)
                   → is-hom G H f
                   → f (E-unit G) ≈⟨ H ⟩ E-unit H
homs-preserve-unit G H f (f-resp , f-mult) =
 ≈-idempotent-is-unit (f eG)
  (f eG ·⟨ H ⟩ f eG ≈[ E-sym H _ _ (f-mult {eG} {eG}) ]
   f (eG ·⟨ G ⟩ eG) ≈[ f-resp (E-unit-left G eG) ]
   f eG             ≈∎)
 where
  open E-group-theory H
  open ≈-reasoning (underlying-relation H) (E-refl H) (E-trans H)
  eG = E-unit G

homs-preserve-inv : (G : EGroup 𝓤 𝓥) (H : EGroup 𝓤' 𝓥')
                    (f : ⟨ G ⟩ → ⟨ H ⟩)
                  → is-hom G H f
                  → (x : ⟨ G ⟩) → f (E-inv G x) ≈⟨ H ⟩ E-inv H (f x)
homs-preserve-inv G H f fh@(f-resp , f-mult) x =
 one-left-inv (f x) (f (E-inv G x))
  (f (E-inv G x) ·⟨ H ⟩ f x ≈[ E-sym H _ _ (f-mult {E-inv G x} {x}) ]
   f (E-inv G x ·⟨ G ⟩ x)   ≈[ f-resp (E-inv-left G x) ]
   f (E-unit G)             ≈[ homs-preserve-unit G H f fh ]
   E-unit H                 ≈∎)
 where
  open E-group-theory H
  open ≈-reasoning (underlying-relation H) (E-refl H) (E-trans H)

\end{code}

The identity is a homomorphism, and homomorphisms compose.

\begin{code}

id-is-hom : (G : EGroup 𝓤 𝓥) → is-hom G G id
id-is-hom G = (λ p → p) , (λ {x} {y} → E-refl G (x ·⟨ G ⟩ y))

∘-is-hom : (F : EGroup 𝓤 𝓥) (G : EGroup 𝓤' 𝓥') (H : EGroup 𝓦 𝓦')
           (f : ⟨ F ⟩ → ⟨ G ⟩) (g : ⟨ G ⟩ → ⟨ H ⟩)
         → is-hom F G f → is-hom G H g → is-hom F H (g ∘ f)
∘-is-hom F G H f g (f-resp , f-mult) (g-resp , g-mult) =
   (λ p → g-resp (f-resp p))
 , (λ {x} {y} → E-trans H _ _ _ (g-resp (f-mult {x} {y})) (g-mult {f x} {f y}))

\end{code}

An isomorphism of egroups is a homomorphism with a homomorphism
inverse, up to the equivalence relations.

\begin{code}

is-iso : (G : EGroup 𝓤 𝓥) (H : EGroup 𝓤' 𝓥')
       → (⟨ G ⟩ → ⟨ H ⟩) → 𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥' ̇
is-iso G H f = is-hom G H f
             × (Σ g ꞉ (⟨ H ⟩ → ⟨ G ⟩) , is-hom H G g
                 × ((y : ⟨ H ⟩) → f (g y) ≈⟨ H ⟩ y)
                 × ((x : ⟨ G ⟩) → g (f x) ≈⟨ G ⟩ x))

_≅_ : EGroup 𝓤 𝓥 → EGroup 𝓤' 𝓥' → 𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥' ̇
G ≅ H = Σ f ꞉ (⟨ G ⟩ → ⟨ H ⟩) , is-iso G H f

≅-refl : (G : EGroup 𝓤 𝓥) → G ≅ G
≅-refl G = id , id-is-hom G , id , id-is-hom G , E-refl G , E-refl G

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
 , (λ w → E-trans H _ _ _ (g-resp (f-ε (g⁻ w))) (g-ε w))
 , (λ x → E-trans F _ _ _ (f⁻-resp (g-θ (f x))) (f-θ x))

\end{code}

The setoid of homomorphisms between two egroups, with the pointwise
equivalence relation.

\begin{code}

hom-setoid : (G : EGroup 𝓤 𝓥) (H : EGroup 𝓤' 𝓥')
           → Setoid (𝓤 ⊔ 𝓤' ⊔ 𝓥 ⊔ 𝓥') (𝓤 ⊔ 𝓥')
hom-setoid G H =
   (Σ f ꞉ (⟨ G ⟩ → ⟨ H ⟩) , is-hom G H f)
 , (λ u v → (x : ⟨ G ⟩) → pr₁ u x ≈⟨ H ⟩ pr₁ v x)
 , (λ u x → E-refl H (pr₁ u x))
 , (λ u v p x → E-sym H (pr₁ u x) (pr₁ v x) (p x))
 , (λ u v w p q x → E-trans H (pr₁ u x) (pr₁ v x) (pr₁ w x) (p x) (q x))

\end{code}
