Martin Escardo, 13th February. Group basics.

There is another equivalent definition of group in the file
UF-SIP-Examples.

\begin{code}

{-# OPTIONS --without-K --safe --auto-inline --exact-split #-}

module Groups where
open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-FunExt
open import UF-Subsingletons-FunExt
open import UF-Equiv hiding (_≅_ ; ≅-refl)

\end{code}

Underlying type of a mathematical structure:

\begin{code}

⟨_⟩ : {S : 𝓤 ̇ → 𝓥 ̇ } → Σ S → 𝓤 ̇
⟨ X , s ⟩ = X

monoid-structure : 𝓤 ̇ → 𝓤 ̇
monoid-structure X = (X → X → X) × X

monoid-axioms : (X : 𝓤 ̇ ) → monoid-structure X → 𝓤 ̇
monoid-axioms X (_·_ , e) = is-set X
                          × left-neutral  e _·_
                          × right-neutral e _·_
                          × associative     _·_
\end{code}

We choose the unit and inverses to be part of the axioms rather than
part of the structure in the case of groups:

\begin{code}

group-structure : 𝓤 ̇ → 𝓤 ̇
group-structure X = X → X → X

group-axioms : (X : 𝓤 ̇ ) → group-structure X → 𝓤 ̇
group-axioms X _·_ = is-set X
                   × associative _·_
                   × (Σ e ꞉ X
                    , left-neutral  e _·_
                    × right-neutral e _·_
                    × ((x : X) → Σ x' ꞉ X , (x' · x ≡ e) × (x · x' ≡ e)))

Group-structure : 𝓤 ̇ → 𝓤 ̇
Group-structure X = Σ _·_ ꞉ group-structure X , (group-axioms X _·_)

Group : (𝓤 : Universe) → 𝓤 ⁺ ̇
Group 𝓤 = Σ X ꞉ 𝓤 ̇ , Group-structure X

monoid-structure-of : (G : Group 𝓤) → monoid-structure ⟨ G ⟩
monoid-structure-of (X , _·_ , i , a , e , l , r , ι) = (_·_ , e)

monoid-axioms-of : (G : Group 𝓤) → monoid-axioms ⟨ G ⟩ (monoid-structure-of G)
monoid-axioms-of (X , _·_ , i , a , e , l , r , ι) = i , l , r , a


inv-lemma : (X : 𝓤 ̇ ) (_·_ : X → X → X) (e : X)
          → monoid-axioms X (_·_ , e)
          → (x y z : X)
          → (y · x) ≡ e
          → (x · z) ≡ e
          → y ≡ z

inv-lemma X _·_  e (s , l , r , a) x y z q p =

   y             ≡⟨ (r y)⁻¹ ⟩
   (y · e)       ≡⟨ ap (y ·_) (p ⁻¹) ⟩
   (y · (x · z)) ≡⟨ (a y x z)⁻¹ ⟩
   ((y · x) · z) ≡⟨ ap (_· z) q ⟩
   (e · z)       ≡⟨ l z ⟩
   z             ∎

multiplication : (G : Group 𝓤) → ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
multiplication (X , _·_ , _) = _·_

syntax multiplication G x y = x ·⟨ G ⟩ y

group-is-set : (G : Group 𝓤) → is-set ⟨ G ⟩
group-is-set (X , _·_ , i , a , e , l , r , u) = i

unit : (G : Group 𝓤) → ⟨ G ⟩
unit (X , _·_ , i , a , e , l , r , u) = e

syntax unit G = e⟨ G ⟩

unit-left : (G : Group 𝓤) (x : ⟨ G ⟩)
          → unit G ·⟨ G ⟩ x ≡ x
unit-left (X , _·_ , i , a , e , l , r , u) = l


unit-right : (G : Group 𝓤) (x : ⟨ G ⟩)
           → x ·⟨ G ⟩ unit G ≡ x
unit-right (X , _·_ , i , a , e , l , r , u) = r


assoc : (G : Group 𝓤) (x y z : ⟨ G ⟩)
      → (x ·⟨ G ⟩ y) ·⟨ G ⟩ z ≡ x ·⟨ G ⟩ (y ·⟨ G ⟩ z)
assoc (X , _·_ , i , a , e , l , r , ι) = a

inv : (G : Group 𝓤) → ⟨ G ⟩ → ⟨ G ⟩
inv (X , _·_ , i , a , e , l , r , ι) x = pr₁ (ι x)

inv-left : (G : Group 𝓤) (x : ⟨ G ⟩)
         → inv G x ·⟨ G ⟩ x ≡ unit G
inv-left (X , _·_ , i , a , e , l , r , ι) x = pr₁ (pr₂ (ι x))

inv-right : (G : Group 𝓤) (x : ⟨ G ⟩)
          → x ·⟨ G ⟩ inv G x ≡ unit G
inv-right (X , _·_ , i , a , e , l , r , ι) x = pr₂ (pr₂ (ι x))

is-hom : (G : Group 𝓤) (H : Group 𝓥) → (⟨ G ⟩ → ⟨ H ⟩) → 𝓤 ⊔ 𝓥 ̇
is-hom G H f = ∀ {x y} → f (x ·⟨ G ⟩ y) ≡ f x ·⟨ H ⟩ f y

id-is-hom : (G : Group 𝓤) → is-hom G G id
id-is-hom G = refl

∘-is-hom : (F : Group 𝓤) (G : Group 𝓥) (H : Group 𝓦)
           (f : ⟨ F ⟩ → ⟨ G ⟩) (g : ⟨ G ⟩ → ⟨ H ⟩)
         → is-hom F G f → is-hom G H g → is-hom F H (g ∘ f)
∘-is-hom F G H f g h k {x} {y} = g (f (x ·⟨ F ⟩ y))     ≡⟨ ap g h ⟩
                                 g (f x ·⟨ G ⟩ f y)     ≡⟨ k ⟩
                                 g (f x) ·⟨ H ⟩ g (f y) ∎

being-hom-is-prop : Fun-Ext
                  → (G : Group 𝓤) (H : Group 𝓥) (f : ⟨ G ⟩ → ⟨ H ⟩)
                  → is-prop (is-hom G H f)
being-hom-is-prop fe G H f = Π-is-prop' fe
                              (λ x → Π-is-prop' fe
                                      (λ y → group-is-set H))

preserves-unit : (G : Group 𝓤) (H : Group 𝓥) → (⟨ G ⟩ → ⟨ H ⟩) → 𝓥 ̇
preserves-unit G H f = f (unit G) ≡ unit H

idempotent-is-unit : (G : Group 𝓤) (x : ⟨ G ⟩)
                   → x ·⟨ G ⟩ x ≡ x
                   → x ≡ unit G

idempotent-is-unit G x p = γ
 where
  x' = inv G x
  γ = x                        ≡⟨ (unit-left G x)⁻¹ ⟩
      unit G ·⟨ G ⟩ x          ≡⟨ (ap (λ - → - ·⟨ G ⟩ x) (inv-left G x))⁻¹ ⟩
      (x' ·⟨ G ⟩ x) ·⟨ G ⟩ x   ≡⟨ assoc G x' x x ⟩
      x' ·⟨ G ⟩ (x ·⟨ G ⟩ x)   ≡⟨ ap (λ - → x' ·⟨ G ⟩ -) p ⟩
      x' ·⟨ G ⟩ x              ≡⟨ inv-left G x ⟩
      unit G                   ∎

homs-preserve-unit : (G : Group 𝓤) (H : Group 𝓥) (f : ⟨ G ⟩ → ⟨ H ⟩)
                   → is-hom G H f
                   → preserves-unit G H f

homs-preserve-unit G H f m = idempotent-is-unit H e p
 where
  e = f (unit G)

  p = e ·⟨ H ⟩ e               ≡⟨ m ⁻¹ ⟩
      f (unit G ·⟨ G ⟩ unit G) ≡⟨ ap f (unit-left G (unit G)) ⟩
      e                        ∎

inv-Lemma : (G : Group 𝓤) (x y z : ⟨ G ⟩)
          → (y ·⟨ G ⟩ x) ≡ unit G
          → (x ·⟨ G ⟩ z) ≡ unit G
          → y ≡ z
inv-Lemma G = inv-lemma ⟨ G ⟩ (multiplication G) (unit G) (monoid-axioms-of G)


one-left-inv : (G : Group 𝓤) (x x' : ⟨ G ⟩)
             → (x' ·⟨ G ⟩ x) ≡ unit G
             → x' ≡ inv G x

one-left-inv G x x' p = inv-Lemma G x x' (inv G x) p (inv-right G x)

one-right-inv : (G : Group 𝓤) (x x' : ⟨ G ⟩)
              → (x ·⟨ G ⟩ x') ≡ unit G
              → x' ≡ inv G x

one-right-inv G x x' p = (inv-Lemma G x (inv G x) x' (inv-left G x) p)⁻¹

preserves-inv : (G : Group 𝓤) (H : Group 𝓥) → (⟨ G ⟩ → ⟨ H ⟩) → 𝓤 ⊔ 𝓥 ̇
preserves-inv G H f = (x : ⟨ G ⟩) → f (inv G x) ≡ inv H (f x)

homs-preserve-invs : (G : Group 𝓤) (H : Group 𝓥) (f : ⟨ G ⟩ → ⟨ H ⟩)
                   → is-hom G H f
                   → preserves-inv G H f
homs-preserve-invs G H f m x = γ
 where
  p = f (inv G x) ·⟨ H ⟩ f x ≡⟨ m ⁻¹ ⟩
      f (inv G x ·⟨ G ⟩ x)   ≡⟨ ap f (inv-left G x) ⟩
      f (unit G)             ≡⟨ homs-preserve-unit G H f m ⟩
      unit H                 ∎

  γ : f (inv G x) ≡ inv H (f x)
  γ = one-left-inv H (f x) (f (inv G x)) p


is-iso : (G : Group 𝓤) (H : Group 𝓥) → (⟨ G ⟩ → ⟨ H ⟩) → 𝓤 ⊔ 𝓥 ̇
is-iso G H f = is-equiv f × is-hom G H f

inverses-are-homs : (G : Group 𝓤) (H : Group 𝓥) (f : ⟨ G ⟩ → ⟨ H ⟩)
                  → (i : is-equiv f)
                  → is-hom G H f
                  → is-hom H G (inverse f i)
inverses-are-homs G H f i h {x} {y} = γ
 where
  g : ⟨ H ⟩ → ⟨ G ⟩
  g = inverse f i

  η : f ∘ g ∼ id
  η = inverses-are-sections f i

  ε : g ∘ f ∼ id
  ε = inverses-are-retractions f i

  γ = g (x ·⟨ H ⟩ y)             ≡⟨ ap₂ (λ x y → g (x ·⟨ H ⟩ y)) ((η x)⁻¹) ((η y)⁻¹) ⟩
      g (f (g x) ·⟨ H ⟩ f (g y)) ≡⟨ ap g (h ⁻¹) ⟩
      g (f (g x ·⟨ G ⟩ g y))     ≡⟨ ε _ ⟩
      g x ·⟨ G ⟩ g y             ∎

\end{code}

Users of this module may wish to rename the following symbol _≅_ for
group ismorphism when importing it.

\begin{code}

_≅_ : Group 𝓤 → Group 𝓥 → 𝓤 ⊔ 𝓥 ̇
G ≅ H = Σ f ꞉ (⟨ G ⟩ → ⟨ H ⟩) , is-iso G H f

≅-refl : (G : Group 𝓤) → G ≅ G
≅-refl G = id , id-is-equiv ⟨ G ⟩ , id-is-hom G

≅-sym : (G : Group 𝓤) (H : Group 𝓥) → G ≅ H → H ≅ G
≅-sym G H (f , e , h) = inverse f e ,
                        inverses-are-equivs f e ,
                        inverses-are-homs G H f e h

≅-trans : (F : Group 𝓤) (G : Group 𝓥) (H : Group 𝓦)
        → F ≅ G → G ≅ H → F ≅ H
≅-trans F G H (f , i , h) (g , j , k) = g ∘ f ,
                                        ∘-is-equiv i j ,
                                        ∘-is-hom F G H f g h k

isomorphic-groups-have-equivalent-carriers : (G : Group 𝓤)
                                             (H : Group 𝓥)
                                           → G ≅ H → ⟨ G ⟩ ≃ ⟨ H ⟩
isomorphic-groups-have-equivalent-carriers G H (f , e , h) = (f , e)

\end{code}

If G is a group in a universe 𝓤 whose underlying set has a copy in a
universe 𝓥, then G itself has a copy in the universe 𝓥.

\begin{code}

transport-Group-structure : (G : Group 𝓤) (Y : 𝓥 ̇ ) (f : Y → ⟨ G ⟩)
                          → is-equiv f
                          → Σ s ꞉ Group-structure Y , is-hom (Y , s) G f
transport-Group-structure {𝓤} {𝓥} (X , _·_ , i , a , e , l , r , ι)
                          Y  f f-is-equiv = γ
 where
  G : Group 𝓤
  G = X , _·_ , i , a , e , l , r , ι

  abstract
   g : X → Y
   g = inverse f f-is-equiv

   η : f ∘ g ∼ id
   η = inverses-are-sections f f-is-equiv

   ε : g ∘ f ∼ id
   ε = inverses-are-retractions f f-is-equiv

  f-is-hom : {y y' : Y} → f (g (f y · f y')) ≡ f y · f y'
  f-is-hom {y} {y'} = η (f y · f y')

  _•_ : Y → Y → Y
  y • y' = g (f y · f y')

  i' : is-set Y
  i' = equiv-to-set (f , f-is-equiv) i

  e' : Y
  e' = g e

  a' : associative _•_
  a' y₀ y₁ y₂ = g (f (g (f y₀ · f y₁)) · f y₂)         ≡⟨ ap g (f-is-hom ⁻¹) ⟩
                g (f (g (f (g (f y₀ · f y₁)) · f y₂))) ≡⟨ ε _ ⟩
                g (f (g (f y₀ · f y₁)) · f y₂)         ≡⟨ ap (λ - → g (- · f y₂)) (η _) ⟩
                g ((f y₀ · f y₁) · f y₂)               ≡⟨ ap g (a _ _ _) ⟩
                g (f y₀ · (f y₁ · f y₂))               ≡⟨ ap (λ - → g (f y₀ · -)) ((η _)⁻¹) ⟩
                g (f y₀ · f (g (f y₁ · f y₂)))         ∎

  l' : left-neutral e' _•_
  l' y = g (f (g e) · f y) ≡⟨ ap (λ - → g (- · f y)) (η e) ⟩
         g (e · f y)       ≡⟨ ap g (l (f y)) ⟩
         g (f y)           ≡⟨ ε y ⟩
         y                 ∎

  r' : right-neutral e' _•_
  r' y = g (f y · f (g e)) ≡⟨ ap (λ - → g (f y · -)) (η e) ⟩
         g (f y · e)       ≡⟨ ap g (r (f y)) ⟩
         g (f y)           ≡⟨ ε y ⟩
         y                 ∎


  ι' : (y : Y) → Σ y' ꞉ Y , (y' • y ≡ e') × (y • y' ≡ e')
  ι' y = g (pr₁ (ι (f y))) ,

        (g (f (g (pr₁ (ι (f y)))) · f y) ≡⟨ ap (λ - → g (- · f y)) (η _) ⟩
         g (pr₁ (ι (f y)) · f y)         ≡⟨ ap g (pr₁ (pr₂ (ι (f y)))) ⟩
         g e                             ∎) ,

        (g (f y · f (g (pr₁ (ι (f y))))) ≡⟨ ap (λ - → g (f y · -)) (η _) ⟩
         g (f y · id (pr₁ (ι (f y))))    ≡⟨ ap g (pr₂ (pr₂ (ι (f y)))) ⟩
         g e                             ∎)


  s : Group-structure Y
  s = _•_ , i' , a' , e' , l' , r' , ι'

  γ : Σ s ꞉ Group-structure Y , is-hom (Y , s) G f
  γ = s , f-is-hom

resized-group : (G : Group 𝓤)
              → (Σ Y ꞉ 𝓥 ̇ , Y ≃ ⟨ G ⟩)
              → Σ H ꞉ Group 𝓥 , H ≅ G
resized-group {𝓤} {𝓥} G (Y , f , f-is-equiv) = γ
 where
  δ : (Σ s ꞉ Group-structure Y , is-hom (Y , s) G f)
    → Σ H ꞉ Group 𝓥 , H ≅ G
  δ (s , f-is-hom) = (Y , s) , f , f-is-equiv , f-is-hom

  γ : codomain δ
  γ = δ (transport-Group-structure G Y f f-is-equiv)

open import UF-UniverseEmbedding

transport-Group-structure₁ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                          → X ≃ Y
                          → Group-structure X
                          → Group-structure Y
transport-Group-structure₁ {𝓤} {𝓥} {X} {Y} (f , f-is-equiv) s =
 pr₁ (transport-Group-structure (X , s) Y
       (inverse f f-is-equiv)
       (inverses-are-equivs f f-is-equiv))


Lift-Group : ∀ {𝓤} 𝓥 → Group 𝓤 → Group (𝓤 ⊔ 𝓥)
Lift-Group {𝓤} 𝓥 (X , s) = Lift 𝓥 X , transport-Group-structure₁ (≃-Lift 𝓥 X) s

Lifted-Group-is-isomorphic : ∀ {𝓤} {𝓥} (G : Group 𝓤) → Lift-Group 𝓥 G ≅ G
Lifted-Group-is-isomorphic {𝓤} {𝓥} G =
 pr₂ (resized-group G (Lift 𝓥 ⟨ G ⟩ , Lift-is-universe-embedding 𝓥 ⟨ G ⟩))

\end{code}

Boolean groups.

\begin{code}

boolean-groups-are-abelian' : {X : 𝓤 ̇ } (_·_ : X → X → X) (e : X)
                            → associative _·_
                            → left-neutral e _·_
                            → right-neutral e _·_
                            → ((x : X) → x · x ≡ e)
                            → commutative _·_
boolean-groups-are-abelian' _·_  e a ln rn b x y =
  xy                  ≡⟨ ap (x ·_) ((ln y)⁻¹) ⟩
  x · (e · y)         ≡⟨ ap (λ - → x · (- · y)) ((b xy)⁻¹) ⟩
  x · ((xy · xy) · y) ≡⟨ (a x (xy · xy) y)⁻¹ ⟩
  (x · (xy · xy)) · y ≡⟨ ap (_· y) ((a x xy xy)⁻¹) ⟩
  ((x · xy) · xy) · y ≡⟨ ap (λ - → (- · xy) · y) ((a x x y)⁻¹) ⟩
  ((xx · y) · xy) · y ≡⟨ ap (λ - → (( - · y) · xy) · y) (b x) ⟩
  ((e · y) · xy) · y  ≡⟨ ap (λ - → (- · xy) · y) (ln y) ⟩
  (y · xy) · y        ≡⟨ a y xy y ⟩
  y · (xy · y)        ≡⟨ ap (y ·_) (a x y y) ⟩
  y · (x · yy)        ≡⟨ ap (λ - → y · (x · -)) (b y) ⟩
  y · (x · e)         ≡⟨ ap (y ·_) (rn x) ⟩
  yx                  ∎

 where
  xx = x · x
  xy = x · y
  yx = y · x
  yy = y · y

is-boolean : Group 𝓤 → 𝓤 ̇
is-boolean G = (x : ⟨ G ⟩) → x ·⟨ G ⟩ x ≡ e⟨ G ⟩

is-abelian : Group 𝓤 → 𝓤 ̇
is-abelian G = (x y : ⟨ G ⟩) → x ·⟨ G ⟩ y ≡ y ·⟨ G ⟩ x

boolean-groups-are-abelian : (G : Group 𝓤)
                           → is-boolean G
                           → is-abelian G
boolean-groups-are-abelian (G , _·_ , _ , a , e , ln , rn , _) =
 boolean-groups-are-abelian' _·_ e a ln rn

\end{code}
