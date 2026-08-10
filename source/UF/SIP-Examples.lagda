Martin Escardo, 30 April 2020

This ports the structure identity principle examples formulated and proved in

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF.in-Agda-Lecture-Notes/index.html
 https://arxiv.org/abs/1911.00580
 https://github.com/martinescardo/HoTT-UF.Agda-Lecture-Notes

Each example is in a submodule:

  * ∞-magma
  * magma
  * pointed type
  * pointed-∞-magma
  * monoid
  * associative ∞-magma
  * group
  * subgroups of an ambient group
  * ring
  * slice
  * generalized metric space
  * generalized topological space
  * selection space
  * contrived example
  * generalized functor algebra
  * type-valued preorder
  * type-valued preorder with axioms
  * category

We also consider the following, which are not in the above lecture
notes:

  * universe à la Tarski
  * ∞-bigmagma
  * ∞-hugemagma

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.SIP-Examples where

open import MLTT.Spartan
open import Notation.Order
open import UF.Base
open import UF.Embeddings
open import UF.Equiv hiding (_≅_)
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.SIP
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import UF.Univalence
open import UF.Yoneda

module ∞-magma {𝓤 : Universe} where

 open sip

 ∞-magma-structure : 𝓤 ̇ → 𝓤 ̇
 ∞-magma-structure X = X → X → X

 ∞-Magma : 𝓤 ⁺ ̇
 ∞-Magma = Σ X ꞉ 𝓤 ̇ , ∞-magma-structure X

 sns-data : SNS ∞-magma-structure 𝓤
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : ∞-Magma) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ̇
   ι (X , _·_) (Y , _*_) (f , _) =
    (λ x x' → f (x · x')) ＝[ (X → X → Y) ] (λ x x' → f x * f x')

   ρ : (A : ∞-Magma) → ι A A (≃-refl ⟨ A ⟩)
   ρ (X , _·_) = 𝓻𝓮𝒻𝓵  _·_

   h : {X : 𝓤 ̇ } {_·_ _*_ : ∞-magma-structure X}
     → canonical-map ι ρ _·_ _*_ ∼ -id (_·_ ＝ _*_)

   h (refl {_·_}) = 𝓻𝓮𝒻𝓵 (𝓻𝓮𝒻𝓵 _·_)

   θ : {X : 𝓤 ̇ } (_·_ _*_ : ∞-magma-structure X)
     → is-equiv (canonical-map ι ρ _·_ _*_)

   θ _·_ _*_ = equiv-closed-under-∼ _ _ (id-is-equiv (_·_ ＝ _*_)) h

 _≅_ : ∞-Magma → ∞-Magma → 𝓤 ̇
 (X , _·_) ≅ (Y , _*_) =
           Σ f ꞉ (X → Y) , is-equiv f
                         × ((λ x x' → f (x · x')) ＝[ (X → X → Y) ]
                            (λ x x' → f x * f x'))

 characterization-of-∞-Magma-＝ : is-univalent 𝓤
                               → (A B : ∞-Magma)
                               → (A ＝ B) ≃ (A ≅ B)
 characterization-of-∞-Magma-＝ ua = characterization-of-＝ ua sns-data

 characterization-of-characterization-of-∞-Magma-＝
  : (ua : is-univalent 𝓤) (A : ∞-Magma)
  → ⌜ characterization-of-∞-Magma-＝ ua A A ⌝ (𝓻𝓮𝒻𝓵 A)
  ＝ (-id ⟨ A ⟩ , id-is-equiv ⟨ A ⟩ , refl)
 characterization-of-characterization-of-∞-Magma-＝ ua A = refl

module magma {𝓤 : Universe} where

 open sip-with-axioms

 Magma : 𝓤 ⁺ ̇
 Magma = Σ X ꞉ 𝓤 ̇ , (X → X → X) × is-set X

 _≅_ : Magma → Magma → 𝓤 ̇

 (X , _·_ , _) ≅ (Y , _*_ , _) =
               Σ f ꞉ (X → Y), is-equiv f
                            × ((λ x x' → f (x · x')) ＝[ (X → X → Y) ]
                               (λ x x' → f x * f x'))

 characterization-of-Magma-＝ : is-univalent 𝓤
                             → (A B : Magma)
                             → (A ＝ B) ≃ (A ≅ B)
 characterization-of-Magma-＝ ua =
   characterization-of-＝-with-axioms ua
     ∞-magma.sns-data
     (λ X s → is-set X)
     (λ X s → being-set-is-prop (univalence-gives-funext ua))

module pointed-type {𝓤 : Universe} where
 open sip

 Pointed : 𝓤 ̇ → 𝓤 ̇
 Pointed X = X

 sns-data : SNS Pointed 𝓤
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Σ Pointed) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ̇
   ι (X , x₀) (Y , y₀) (f , _) = (f x₀ ＝ y₀)

   ρ : (A : Σ Pointed) → ι A A (≃-refl ⟨ A ⟩)
   ρ (X , x₀) = 𝓻𝓮𝒻𝓵 x₀

   θ : {X : 𝓤 ̇ } (x₀ x₁ : Pointed X) → is-equiv (canonical-map ι ρ x₀ x₁)
   θ x₀ x₁ = equiv-closed-under-∼ _ _ (id-is-equiv (x₀ ＝ x₁)) h
    where
     h : canonical-map ι ρ x₀ x₁ ∼ -id (x₀ ＝ x₁)
     h (refl {x₀}) = 𝓻𝓮𝒻𝓵 (𝓻𝓮𝒻𝓵 x₀)

 _≅_ : Σ Pointed → Σ Pointed → 𝓤 ̇
 (X , x₀) ≅ (Y , y₀) = Σ f ꞉ (X → Y), is-equiv f × (f x₀ ＝ y₀)

 characterization-of-pointed-type-＝ : is-univalent 𝓤
                                    → (A B : Σ Pointed)
                                    → (A ＝ B) ≃ (A ≅ B)
 characterization-of-pointed-type-＝ ua = characterization-of-＝ ua sns-data

module pointed-∞-magma {𝓤 : Universe} where

 open sip-join

 ∞-Magma· : 𝓤 ⁺ ̇
 ∞-Magma· = Σ X ꞉ 𝓤 ̇ , (X → X → X) × X

 _≅_ : ∞-Magma· → ∞-Magma· → 𝓤 ̇
 (X ,  _·_ , x₀) ≅ (Y ,  _*_ , y₀) =
                 Σ f ꞉ (X → Y), is-equiv f
                              × ((λ x x' → f (x · x')) ＝[ (X → X → Y) ]
                                 (λ x x' → f x * f x'))
                              × (f x₀ ＝ y₀)

 characterization-of-pointed-magma-＝ : is-univalent 𝓤
                                     → (A B : ∞-Magma·)
                                     → (A ＝ B) ≃ (A ≅ B)
 characterization-of-pointed-magma-＝ ua = characterization-of-join-＝ ua
                                            ∞-magma.sns-data
                                            pointed-type.sns-data

module monoid {𝓤 : Universe} where

 open sip
 open sip-join
 open sip-with-axioms

 monoid-structure : 𝓤 ̇ → 𝓤 ̇
 monoid-structure X = (X → X → X) × X

 monoid-axioms : (X : 𝓤 ̇ ) → monoid-structure X → 𝓤 ̇
 monoid-axioms X (_·_ , e) = is-set X
                           × left-neutral  e _·_
                           × right-neutral e _·_
                           × associative     _·_

 Monoid : 𝓤 ⁺ ̇
 Monoid = Σ X ꞉ 𝓤 ̇ , Σ s ꞉ monoid-structure X , monoid-axioms X s

 monoid-axioms-is-prop : funext 𝓤 𝓤
                       → (X : 𝓤 ̇ ) (s : monoid-structure X)
                       → is-prop (monoid-axioms X s)

 monoid-axioms-is-prop fe X (_·_ , e) s = γ s
  where
   i : is-set X
   i = pr₁ s

   γ : is-prop (monoid-axioms X (_·_ , e))
   γ = ×₄-is-prop
        (being-set-is-prop fe)
        (Π-is-prop fe (λ x → i {e · x} {x}))
        (Π-is-prop fe (λ x → i {x · e} {x}))
        (Π-is-prop fe
          (λ x → Π-is-prop fe
          (λ y → Π-is-prop fe
          (λ z → i {(x · y) · z} {x · (y · z)}))))

 sns-data : funext 𝓤 𝓤
          → SNS (λ X → Σ s ꞉ monoid-structure X , monoid-axioms X s) 𝓤
 sns-data fe = add-axioms
                monoid-axioms (monoid-axioms-is-prop fe)
                (join
                   ∞-magma.sns-data
                   pointed-type.sns-data)

 _≅_ : Monoid → Monoid → 𝓤 ̇
 (X , (_·_ , d) , _) ≅ (Y , (_*_ , e) , _) =
    Σ f ꞉ (X → Y), is-equiv f
                 × ((λ x x' → f (x · x')) ＝[ (X → X → Y) ]
                    (λ x x' → f x * f x'))
                 × (f d ＝ e)

 characterization-of-monoid-＝ : is-univalent 𝓤
                              → (A B : Monoid)
                              → (A ＝ B) ≃ (A ≅ B)
 characterization-of-monoid-＝ ua = characterization-of-＝ ua
                                    (sns-data (univalence-gives-funext ua))

module associative-∞-magma
        {𝓤 : Universe}
        (ua : is-univalent 𝓤)
       where

 abstract
  fe : funext 𝓤 𝓤
  fe = univalence-gives-funext ua

 ∞-amagma-structure : 𝓤 ̇ → 𝓤 ̇
 ∞-amagma-structure X = Σ _·_ ꞉ (X → X → X), (associative _·_)

 ∞-aMagma : 𝓤 ⁺ ̇
 ∞-aMagma = Σ X ꞉ 𝓤 ̇ , ∞-amagma-structure X

 homomorphic : {X Y : 𝓤 ̇ } → (X → X → X) → (Y → Y → Y) → (X → Y) → 𝓤 ̇
 homomorphic {X} {Y} _·_ _*_ f =
  (λ x y → f (x · y)) ＝[ (X → X → Y) ] (λ x y → f x * f y)

 respect-assoc : {X A : 𝓤 ̇ } (_·_ : X → X → X) (_*_ : A → A → A)
               → associative _·_ → associative _*_
               → (f : X → A) → homomorphic _·_ _*_ f → 𝓤 ̇
 respect-assoc {X} {A} _·_ _*_ α β f h  =  fα ＝ βf
  where
   l : (x y z : X) → f ((x · y) · z) ＝ (f x * f y) * f z
   l x y z = f ((x · y) · z)   ＝⟨ ap (λ - → - (x · y) z) h ⟩
             f (x · y) * f z   ＝⟨ ap (λ - → - x y * f z) h ⟩
             (f x * f y) * f z ∎

   r : (x y z : X) → f (x · (y · z)) ＝ f x * (f y * f z)
   r x y z = f (x · (y · z))   ＝⟨ ap (λ - → - x (y · z)) h ⟩
             f x * f (y · z)   ＝⟨ ap (λ - → f x * - y z) h ⟩
             f x * (f y * f z) ∎

   fα βf : ∀ x y z → (f x * f y) * f z ＝ f x * (f y * f z)
   fα x y z = (l x y z)⁻¹ ∙ ap f (α x y z) ∙ r x y z
   βf x y z = β (f x) (f y) (f z)

 remark : {X : 𝓤 ̇ } (_·_ : X → X → X) (α β : associative _·_)
        → respect-assoc _·_ _·_ α β id (𝓻𝓮𝒻𝓵 _·_)
        ＝ ((λ x y z → 𝓻𝓮𝒻𝓵 ((x · y) · z) ∙ ap id (α x y z)) ＝ β)
 remark _·_ α β = refl

 open sip hiding (homomorphic)

 sns-data : SNS ∞-amagma-structure 𝓤
 sns-data = (ι , ρ , θ)
  where
   ι : (𝓧 𝓐 : ∞-aMagma) → ⟨ 𝓧 ⟩ ≃ ⟨ 𝓐 ⟩ → 𝓤 ̇
   ι (X , _·_ , α) (A , _*_ , β) (f , i) = Σ h ꞉ homomorphic _·_ _*_ f
                                               , respect-assoc _·_ _*_ α β f h

   ρ : (𝓧 : ∞-aMagma) → ι 𝓧 𝓧 (≃-refl ⟨ 𝓧 ⟩)
   ρ (X , _·_ , α) = h , p
    where
     h : homomorphic _·_ _·_ id
     h = 𝓻𝓮𝒻𝓵 _·_

     q : ∀ x y z → 𝓻𝓮𝒻𝓵 ((x · y) · z) ∙ ap id (α x y z) ＝ α x y z
     q x y z = refl-left-neutral ∙ ap-id-is-id (α x y z)

     p : (λ x y z → 𝓻𝓮𝒻𝓵 ((x · y) · z) ∙ ap id (α x y z)) ＝ α
     p =  dfunext fe (λ x → dfunext fe (λ y → dfunext fe (λ z → q x y z)))

   u : (X : 𝓤 ̇ )
     → ∀ s
     → ∃! t ꞉ ∞-amagma-structure X , ι (X , s) (X , t) (≃-refl X)
   u X (_·_ , α) = c , φ
    where
     c : Σ t ꞉ ∞-amagma-structure X , ι (X , _·_ , α) (X , t) (≃-refl X)
     c = (_·_ , α) , ρ (X , _·_ , α)

     φ : (σ : Σ t ꞉ ∞-amagma-structure X , ι (X , _·_ , α) (X , t) (≃-refl X))
       → c ＝ σ
     φ ((_·_ , β) , refl {_·_} , k) = γ
      where
       a : associative _·_
       a x y z = 𝓻𝓮𝒻𝓵 ((x · y) · z) ∙ ap id (α x y z)

       g : singleton-type a
         → Σ t ꞉ ∞-amagma-structure X , ι (X , _·_ , α) (X , t) (≃-refl X)
       g (β , k) = (_·_ , β) , (𝓻𝓮𝒻𝓵 _·_) , k

       i : is-prop (singleton-type a)
       i = singletons-are-props (singleton-types-are-singletons a)

       q : α , pr₂ (ρ (X , _·_ , α)) ＝ β , k
       q = i _ _

       γ : c ＝ (_·_ , β) , 𝓻𝓮𝒻𝓵 _·_ , k
       γ = ap g q

   θ : {X : 𝓤 ̇ } (s t : ∞-amagma-structure X) → is-equiv (canonical-map ι ρ s t)
   θ {X} s = Yoneda-Theorem-forth s (canonical-map ι ρ s) (u X s)

 _≅_ : ∞-aMagma → ∞-aMagma → 𝓤 ̇
 (X , _·_ , α) ≅ (Y , _*_ , β) = Σ f ꞉ (X → Y)
                                     , is-equiv f
                                     × (Σ h ꞉ homomorphic _·_ _*_ f
                                            , respect-assoc _·_ _*_ α β f h)

 characterization-of-∞-aMagma-＝ : (A B : ∞-aMagma) → (A ＝ B) ≃ (A ≅ B)
 characterization-of-∞-aMagma-＝ = characterization-of-＝ ua sns-data

module group {𝓤 : Universe} where
 open sip
 open sip-with-axioms
 open monoid {𝓤} hiding (sns-data ; _≅_)

 group-structure : 𝓤 ̇ → 𝓤 ̇
 group-structure X = Σ s ꞉ monoid-structure X , monoid-axioms X s

 group-axiom : (X : 𝓤 ̇ ) → monoid-structure X → 𝓤 ̇
 group-axiom X (_·_ , e) = (x : X) → Σ x' ꞉ X , (x · x' ＝ e) × (x' · x ＝ e)

 Group : 𝓤 ⁺ ̇
 Group = Σ X ꞉ 𝓤 ̇
       , Σ ((_·_ , e) , a) ꞉ group-structure X , group-axiom X (_·_ , e)

 inv-lemma : (X : 𝓤 ̇ ) (_·_ : X → X → X) (e : X)
           → monoid-axioms X (_·_ , e)
           → (x y z : X)
           → (y · x) ＝ e
           → (x · z) ＝ e
           → y ＝ z
 inv-lemma X _·_  e (s , l , r , a) x y z q p =
    y             ＝⟨ (r y)⁻¹ ⟩
    (y · e)       ＝⟨ ap (y ·_) (p ⁻¹) ⟩
    (y · (x · z)) ＝⟨ (a y x z)⁻¹ ⟩
    ((y · x) · z) ＝⟨ ap (_· z) q ⟩
    (e · z)       ＝⟨ l z ⟩
    z             ∎

 group-axiom-is-prop : funext 𝓤 𝓤
                     → (X : 𝓤 ̇ )
                     → (s : group-structure X)
                     → is-prop (group-axiom X (pr₁ s))
 group-axiom-is-prop fe X ((_·_ , e) , (s , l , r , a)) = γ
  where
   i : (x : X) → is-prop (Σ x' ꞉ X , (x · x' ＝ e) × (x' · x ＝ e))
   i x (y , _ , q) (z , p , _) = u
    where
     t : y ＝ z
     t = inv-lemma X _·_ e (s , l , r , a) x y z q p

     u : (y , _ , q) ＝ (z , p , _)
     u = to-subtype-＝ (λ x' → ×-is-prop s s) t

   γ : is-prop (group-axiom X (_·_ , e))
   γ = Π-is-prop fe i

 sns-data : funext 𝓤 𝓤
          → SNS (λ X → Σ s ꞉ group-structure X , group-axiom X (pr₁ s)) 𝓤
 sns-data fe = add-axioms
                (λ X s → group-axiom X (pr₁ s)) (group-axiom-is-prop fe)
                (monoid.sns-data fe)

 _≅_ : Group → Group → 𝓤 ̇
 (X , ((_·_ , d) , _) , _) ≅ (Y , ((_*_ , e) , _) , _) =
    Σ f ꞉ (X → Y), is-equiv f
                 × ((λ x x' → f (x · x')) ＝[ (X → X → Y) ]
                    (λ x x' → f x * f x'))
                 × (f d ＝ e)

 characterization-of-group-＝ : is-univalent 𝓤
                             → (A B : Group)
                             → (A ＝ B) ≃ (A ≅ B)
 characterization-of-group-＝ ua = characterization-of-＝ ua
                                   (sns-data (univalence-gives-funext ua))

 _≅'_ : Group → Group → 𝓤 ̇
 (X , ((_·_ , d) , _) , _) ≅' (Y , ((_*_ , e) , _) , _) =
    Σ f ꞉ (X → Y), is-equiv f
                 × ((λ x x' → f (x · x')) ＝[ (X → X → Y) ]
                    (λ x x' → f x * f x'))

 group-structure-of : (G : Group) → group-structure ⟨ G ⟩
 group-structure-of (X , ((_·_ , e) , i , l , r , a) , γ) =
  (_·_ , e) , i , l , r , a

 monoid-structure-of : (G : Group) → monoid-structure ⟨ G ⟩
 monoid-structure-of (X , ((_·_ , e) , i , l , r , a) , γ) = (_·_ , e)

 monoid-axioms-of : (G : Group) → monoid-axioms ⟨ G ⟩ (monoid-structure-of G)
 monoid-axioms-of (X , ((_·_ , e) , i , l , r , a) , γ) = i , l , r , a

 multiplication : (G : Group) → ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
 multiplication (X , ((_·_ , e) , i , l , r , a) , γ) = _·_

 syntax multiplication G x y = x ·⟨ G ⟩ y

 unit : (G : Group) → ⟨ G ⟩
 unit (X , ((_·_ , e) , i , l , r , a) , γ) = e

 group-is-set : (G : Group)
              → is-set ⟨ G ⟩
 group-is-set (X , ((_·_ , e) , i , l , r , a) , γ) = i

 unit-left : (G : Group) (x : ⟨ G ⟩)
           → unit G ·⟨ G ⟩ x ＝ x
 unit-left (X , ((_·_ , e) , i , l , r , a) , γ) x = l x

 unit-right : (G : Group) (x : ⟨ G ⟩)
            → x ·⟨ G ⟩ unit G ＝ x
 unit-right (X , ((_·_ , e) , i , l , r , a) , γ) x = r x

 assoc : (G : Group) (x y z : ⟨ G ⟩)
       → (x ·⟨ G ⟩ y) ·⟨ G ⟩ z ＝ x ·⟨ G ⟩ (y ·⟨ G ⟩ z)
 assoc (X , ((_·_ , e) , i , l , r , a) , γ) = a

 inv : (G : Group) → ⟨ G ⟩ → ⟨ G ⟩
 inv (X , ((_·_ , e) , i , l , r , a) , γ) x = pr₁ (γ x)

 inv-left : (G : Group) (x : ⟨ G ⟩)
          → inv G x ·⟨ G ⟩ x ＝ unit G
 inv-left (X , ((_·_ , e) , i , l , r , a) , γ) x = pr₂ (pr₂ (γ x))

 inv-right : (G : Group) (x : ⟨ G ⟩)
           → x ·⟨ G ⟩ inv G x ＝ unit G

 inv-right (X , ((_·_ , e) , i , l , r , a) , γ) x = pr₁ (pr₂ (γ x))

 preserves-multiplication : (G H : Group) → (⟨ G ⟩ → ⟨ H ⟩) → 𝓤 ̇
 preserves-multiplication G H f = (λ (x y : ⟨ G ⟩) → f (x ·⟨ G ⟩ y))
                                ＝ (λ (x y : ⟨ G ⟩) → f x ·⟨ H ⟩ f y)

 preserves-unit : (G H : Group) → (⟨ G ⟩ → ⟨ H ⟩) → 𝓤 ̇
 preserves-unit G H f = f (unit G) ＝ unit H

 idempotent-is-unit : (G : Group) (x : ⟨ G ⟩)
                    → x ·⟨ G ⟩ x ＝ x
                    → x ＝ unit G
 idempotent-is-unit G x p = γ
  where
   x' = inv G x
   γ = x                        ＝⟨ (unit-left G x)⁻¹ ⟩
       unit G ·⟨ G ⟩ x          ＝⟨ (ap (λ - → - ·⟨ G ⟩ x) (inv-left G x))⁻¹ ⟩
       (x' ·⟨ G ⟩ x) ·⟨ G ⟩ x   ＝⟨ assoc G x' x x ⟩
       x' ·⟨ G ⟩ (x ·⟨ G ⟩ x)   ＝⟨ ap (λ - → x' ·⟨ G ⟩ -) p ⟩
       x' ·⟨ G ⟩ x              ＝⟨ inv-left G x ⟩
       unit G                   ∎

 unit-preservation-lemma : (G H : Group) (f : ⟨ G ⟩ → ⟨ H ⟩)
                         → preserves-multiplication G H f
                         → preserves-unit G H f
 unit-preservation-lemma G H f m = idempotent-is-unit H e p
  where
   e  = f (unit G)

   p = e ·⟨ H ⟩ e               ＝⟨ ap (λ - → - (unit G) (unit G)) (m ⁻¹) ⟩
       f (unit G ·⟨ G ⟩ unit G) ＝⟨ ap f (unit-left G (unit G)) ⟩
       e                        ∎

 inv-Lemma : (G : Group) (x y z : ⟨ G ⟩)
           → (y ·⟨ G ⟩ x) ＝ unit G
           → (x ·⟨ G ⟩ z) ＝ unit G
           → y ＝ z
 inv-Lemma G = inv-lemma ⟨ G ⟩ (multiplication G) (unit G) (monoid-axioms-of G)

 one-left-inv : (G : Group) (x x' : ⟨ G ⟩)
              → (x' ·⟨ G ⟩ x) ＝ unit G
              → x' ＝ inv G x
 one-left-inv G x x' p = inv-Lemma G x x' (inv G x) p (inv-right G x)

 one-right-inv : (G : Group) (x x' : ⟨ G ⟩)
               → (x ·⟨ G ⟩ x') ＝ unit G
               → x' ＝ inv G x
 one-right-inv G x x' p = (inv-Lemma G x (inv G x) x' (inv-left G x) p)⁻¹

 preserves-inv : (G H : Group) → (⟨ G ⟩ → ⟨ H ⟩) → 𝓤 ̇
 preserves-inv G H f = (x : ⟨ G ⟩) → f (inv G x) ＝ inv H (f x)

 inv-preservation-lemma : (G H : Group) (f : ⟨ G ⟩ → ⟨ H ⟩)
                        → preserves-multiplication G H f
                        → preserves-inv G H f
 inv-preservation-lemma G H f m x = γ
  where
   p = f (inv G x) ·⟨ H ⟩ f x ＝⟨ (ap (λ - → - (inv G x) x) m)⁻¹ ⟩
       f (inv G x ·⟨ G ⟩ x)   ＝⟨ ap f (inv-left G x) ⟩
       f (unit G)             ＝⟨ unit-preservation-lemma G H f m ⟩
       unit H                 ∎

   γ : f (inv G x) ＝ inv H (f x)
   γ = one-left-inv H (f x) (f (inv G x)) p

 is-homomorphism : (G H : Group) → (⟨ G ⟩ → ⟨ H ⟩) → 𝓤 ̇
 is-homomorphism G H f = preserves-multiplication G H f
                       × preserves-unit G H f

 preservation-of-mult-is-prop : funext 𝓤 𝓤
                              → (G H : Group) (f : ⟨ G ⟩ → ⟨ H ⟩)
                              → is-prop (preserves-multiplication G H f)
 preservation-of-mult-is-prop fe G H f = j
  where
   j : is-prop (preserves-multiplication G H f)
   j = Π-is-set fe (λ _ → Π-is-set fe (λ _ → group-is-set H))

 being-homomorphism-is-prop : funext 𝓤 𝓤
                            → (G H : Group) (f : ⟨ G ⟩ → ⟨ H ⟩)
                            → is-prop (is-homomorphism G H f)
 being-homomorphism-is-prop fe G H f = i
  where

   i : is-prop (is-homomorphism G H f)
   i = ×-is-prop
        (preservation-of-mult-is-prop fe G H f)
        (group-is-set H)

 notions-of-homomorphism-agree : funext 𝓤 𝓤
                               → (G H : Group) (f : ⟨ G ⟩ → ⟨ H ⟩)
                               → is-homomorphism G H f
                               ≃ preserves-multiplication G H f
 notions-of-homomorphism-agree fe G H f = γ
  where
   α : is-homomorphism G H f → preserves-multiplication G H f
   α = pr₁

   β : preserves-multiplication G H f → is-homomorphism G H f
   β m = m , unit-preservation-lemma G H f m

   γ : is-homomorphism G H f ≃ preserves-multiplication G H f
   γ = logically-equivalent-props-are-equivalent
        (being-homomorphism-is-prop fe G H f)
        (preservation-of-mult-is-prop fe G H f)
        α
        β

 ≅-agreement : funext 𝓤 𝓤 → (G H : Group) → (G ≅ H) ≃ (G ≅' H)
 ≅-agreement fe G H = Σ-cong (λ f → Σ-cong (λ _ → notions-of-homomorphism-agree fe G H f))

 forget-unit-preservation : (G H : Group) → (G ≅ H) → (G ≅' H)
 forget-unit-preservation G H (f , e , m , _) = f , e , m

 NB : (fe : funext 𝓤 𝓤)
    → (G H : Group) → ⌜ ≅-agreement fe G H ⌝ ＝ forget-unit-preservation G H
 NB fe G H = refl

 forget-unit-preservation-is-equiv : funext 𝓤 𝓤
                                   → (G H : Group)
                                   → is-equiv (forget-unit-preservation G H)
 forget-unit-preservation-is-equiv fe G H = ⌜⌝-is-equiv (≅-agreement fe G H)

module subgroup
        (𝓤  : Universe)
        (ua : Univalence)
       where

 fe : ∀ {𝓥} {𝓦} → funext 𝓥 𝓦
 fe {𝓥} {𝓦} = univalence-gives-funext' 𝓥 𝓦 (ua 𝓥) (ua (𝓥 ⊔ 𝓦))

 open sip
 open monoid {𝓤} hiding (sns-data ; _≅_)
 open group {𝓤}

 open import UF.Powerset
 open import UF.Classifiers

 module ambient (G : Group) where

  _·_ : ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
  x · y = x ·⟨ G ⟩ y

  infixl 42 _·_

  group-closed : (⟨ G ⟩ → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
  group-closed 𝓐 = 𝓐 (unit G)
                 × ((x y : ⟨ G ⟩) → 𝓐 x → 𝓐 y → 𝓐 (x · y))
                 × ((x : ⟨ G ⟩) → 𝓐 x → 𝓐 (inv G x))

  Subgroups : 𝓤 ⁺ ̇
  Subgroups = Σ A ꞉ 𝓟 ⟨ G ⟩ , group-closed (_∈ A)

  ⟪_⟫ : Subgroups → 𝓟 ⟨ G ⟩
  ⟪ A , u , c , ι ⟫ = A

  being-group-closed-subset-is-prop : (A : 𝓟 ⟨ G ⟩)
                                    → is-prop (group-closed (_∈ A))
  being-group-closed-subset-is-prop A =
   ×₃-is-prop
    (∈-is-prop A (unit G))
    (Π₄-is-prop fe (λ x y _ _ → ∈-is-prop A (x · y)))
    (Π₂-is-prop fe (λ x _ → ∈-is-prop A (inv G x)))

  ⟪⟫-is-embedding : is-embedding ⟪_⟫
  ⟪⟫-is-embedding = pr₁-is-embedding being-group-closed-subset-is-prop

  ap-⟪⟫ : (S T : Subgroups) → S ＝ T → ⟪ S ⟫ ＝ ⟪ T ⟫
  ap-⟪⟫ S T = ap ⟪_⟫

  ap-⟪⟫-is-equiv : (S T : Subgroups) → is-equiv (ap-⟪⟫ S T)
  ap-⟪⟫-is-equiv = embedding-gives-embedding' ⟪_⟫ ⟪⟫-is-embedding

  subgroups-form-a-set : is-set Subgroups
  subgroups-form-a-set {S} {T} = equiv-to-prop
                                  (ap-⟪⟫ S T , ap-⟪⟫-is-equiv S T)
                                  (𝓟-is-set ua)

  subgroup-equality : (S T : Subgroups)
                    → (S ＝ T)
                    ≃ ((x : ⟨ G ⟩) → (x ∈ ⟪ S ⟫) ↔ (x ∈ ⟪ T ⟫))
  subgroup-equality S T = γ
   where
    f : S ＝ T → (x : ⟨ G ⟩) → x ∈ ⟪ S ⟫ ↔ x ∈ ⟪ T ⟫
    f p x = transport (λ - → x ∈ ⟪ - ⟫) p , transport (λ - → x ∈ ⟪ - ⟫) (p ⁻¹)

    h : ((x : ⟨ G ⟩) → x ∈ ⟪ S ⟫ ↔ x ∈ ⟪ T ⟫) → ⟪ S ⟫ ＝ ⟪ T ⟫
    h φ = subset-extensionality' ua α β
     where
      α : ⟪ S ⟫ ⊆ ⟪ T ⟫
      α x = lr-implication (φ x)

      β : ⟪ T ⟫ ⊆ ⟪ S ⟫
      β x = rl-implication (φ x)

    g : ((x : ⟨ G ⟩) → x ∈ ⟪ S ⟫ ↔ x ∈ ⟪ T ⟫) → S ＝ T
    g = inverse (ap-⟪⟫ S T) (ap-⟪⟫-is-equiv S T) ∘ h

    γ : (S ＝ T) ≃ ((x : ⟨ G ⟩) → x ∈ ⟪ S ⟫ ↔ x ∈ ⟪ T ⟫)
    γ = logically-equivalent-props-are-equivalent
         subgroups-form-a-set
         (Π-is-prop fe
           (λ x → ×-is-prop
                   (Π-is-prop fe (λ _ → ∈-is-prop ⟪ T ⟫ x))
                   (Π-is-prop fe (λ _ → ∈-is-prop ⟪ S ⟫ x)))) f g

  T : 𝓤 ̇ → 𝓤 ̇
  T X = Σ ((_·_ , e) , a) ꞉ group-structure X , group-axiom X (_·_ , e)

  module _ {X : 𝓤 ̇ } (h : X → ⟨ G ⟩) (e : is-embedding h) where

   private
    h-lc : left-cancellable h
    h-lc = embeddings-are-lc h e

   having-group-closed-fiber-is-prop : is-prop (group-closed (fiber h))
   having-group-closed-fiber-is-prop = being-group-closed-subset-is-prop
                                        (λ x → (fiber h x , e x))

   at-most-one-homomorphic-structure : is-prop (Σ τ ꞉ T X , is-homomorphism (X , τ) G h)
   at-most-one-homomorphic-structure
      ((((_*_ ,  unitH) ,  maxioms) ,  gaxiom) ,  (pmult ,  punit))
      ((((_*'_ , unitH') , maxioms') , gaxiom') , (pmult' , punit'))
    = γ
    where
     τ τ' : T X
     τ  = ((_*_ ,  unitH) ,  maxioms) ,  gaxiom
     τ' = ((_*'_ , unitH') , maxioms') , gaxiom'

     i :  is-homomorphism (X , τ)  G h
     i  = (pmult ,  punit)

     i' : is-homomorphism (X , τ') G h
     i' = (pmult' , punit')

     p : _*_ ＝ _*'_
     p = dfunext fe (λ x → dfunext fe (λ y →
          h-lc (h (x * y)  ＝⟨  ap (λ - → - x y) pmult ⟩
                h x · h y  ＝⟨ (ap (λ - → - x y) pmult')⁻¹ ⟩
                h (x *' y) ∎)))
     q : unitH ＝ unitH'
     q = h-lc (h unitH  ＝⟨  punit ⟩
               unit G   ＝⟨  punit' ⁻¹ ⟩
               h unitH' ∎)

     r : (_*_ , unitH) ＝ (_*'_ , unitH')
     r = to-×-＝ p q

     δ : τ ＝ τ'
     δ = to-subtype-＝
           (group-axiom-is-prop fe X)
           (to-subtype-＝ (monoid-axioms-is-prop fe X) r)

     γ : (τ  , i) ＝ (τ' , i')
     γ = to-subtype-＝ (λ τ → being-homomorphism-is-prop fe (X , τ) G h) δ

   group-closed-fiber-gives-homomorphic-structure
    : funext 𝓤 𝓤
    → group-closed (fiber h)
    → (Σ τ ꞉ T X , is-homomorphism (X , τ) G h)
   group-closed-fiber-gives-homomorphic-structure fe (unitc , mulc , invc) =
    τ , i
    where
     φ : (x : X) → fiber h (h x)
     φ x = (x , 𝓻𝓮𝒻𝓵 (h x))

     unitH : X
     unitH = fiber-point unitc

     _*_ : X → X → X
     x * y = fiber-point (mulc (h x) (h y) (φ x) (φ y))

     invH : X → X
     invH x = fiber-point (invc (h x) (φ x))

     pmul : (x y : X) → h (x * y) ＝ h x · h y
     pmul x y = fiber-identification (mulc (h x) (h y) (φ x) (φ y))

     punit : h unitH ＝ unit G
     punit = fiber-identification unitc

     pinv : (x : X) → h (invH x) ＝ inv G (h x)
     pinv x = fiber-identification (invc (h x) (φ x))

     unitH-left : (x : X) → unitH * x ＝ x
     unitH-left x = h-lc (h (unitH * x) ＝⟨ pmul unitH x ⟩
                          h unitH · h x ＝⟨ ap (_· h x) punit ⟩
                          unit G · h x  ＝⟨ unit-left G (h x) ⟩
                          h x           ∎)

     unitH-right : (x : X) → x * unitH ＝ x
     unitH-right x = h-lc (h (x * unitH) ＝⟨ pmul x unitH ⟩
                           h x · h unitH ＝⟨ ap (h x ·_) punit ⟩
                           h x · unit G  ＝⟨ unit-right G (h x) ⟩
                           h x           ∎)

     assocH : (x y z : X) → ((x * y) * z) ＝ (x * (y * z))
     assocH x y z = h-lc (h ((x * y) * z)   ＝⟨ pmul (x * y) z ⟩
                          h (x * y) · h z   ＝⟨ ap (_· h z) (pmul x y) ⟩
                          (h x · h y) · h z ＝⟨ assoc G (h x) (h y) (h z) ⟩
                          h x · (h y · h z) ＝⟨ (ap (h x ·_) (pmul y z))⁻¹ ⟩
                          h x · h (y * z)   ＝⟨ (pmul x (y * z))⁻¹ ⟩
                          h (x * (y * z))   ∎)

     group-axiomH : (x : X) → Σ x' ꞉ X , (x * x' ＝ unitH) × (x' * x ＝ unitH)
     group-axiomH x = invH x ,

                      h-lc (h (x * invH x)     ＝⟨ pmul x (invH x) ⟩
                            h x · h (invH x)   ＝⟨ ap (h x ·_) (pinv x) ⟩
                            h x · inv G (h x)  ＝⟨ inv-right G (h x) ⟩
                            unit G             ＝⟨ punit ⁻¹ ⟩
                            h unitH            ∎),

                      h-lc ((h (invH x * x)    ＝⟨ pmul (invH x) x ⟩
                             h (invH x) · h x  ＝⟨ ap (_· h x) (pinv x) ⟩
                             inv G (h x) · h x ＝⟨ inv-left G (h x) ⟩
                             unit G            ＝⟨ punit ⁻¹ ⟩
                             h unitH           ∎))

     j : is-set X
     j = subtypes-of-sets-are-sets' h h-lc (group-is-set G)

     τ : T X
     τ = ((_*_ , unitH) , (j , unitH-left , unitH-right , assocH)) , group-axiomH

     i : is-homomorphism (X , τ) G h
     i = dfunext fe (λ x → dfunext fe (pmul x)) , punit

   homomorphic-structure-gives-group-closed-fiber
    : (Σ τ ꞉ T X , is-homomorphism (X , τ) G h)
    → group-closed (fiber h)
   homomorphic-structure-gives-group-closed-fiber
       ((((_*_ , unitH) , maxioms) , gaxiom) , (pmult , punit))
     = (unitc , mulc , invc)
    where
     H : Group
     H = X , ((_*_ , unitH) , maxioms) , gaxiom

     unitc : fiber h (unit G)
     unitc = unitH , punit

     mulc : ((x y : ⟨ G ⟩) → fiber h x → fiber h y → fiber h (x · y))
     mulc x y (a , p) (b , q) = (a * b) ,
                                (h (a * b) ＝⟨ ap (λ - → - a b) pmult ⟩
                                 h a · h b ＝⟨ ap₂ (λ - -' → - · -') p q ⟩
                                 x · y     ∎)

     invc : ((x : ⟨ G ⟩) → fiber h x → fiber h (inv G x))
     invc x (a , p) = inv H a ,
                      (h (inv H a) ＝⟨ inv-preservation-lemma H G h pmult a ⟩
                       inv G (h a) ＝⟨ ap (inv G) p ⟩
                       inv G x     ∎)

   fiber-structure-lemma : funext 𝓤 𝓤
                         → group-closed (fiber h)
                         ≃ (Σ τ ꞉ T X , is-homomorphism (X , τ) G h)
   fiber-structure-lemma fe =
    logically-equivalent-props-are-equivalent
     having-group-closed-fiber-is-prop
     at-most-one-homomorphic-structure
     (group-closed-fiber-gives-homomorphic-structure fe)
     homomorphic-structure-gives-group-closed-fiber

\end{code}

TODO. I don't see how to respect the 80-character limit per line in
the following.

\begin{code}

  characterization-of-the-type-of-subgroups
   : Subgroups ≃ (Σ H ꞉ Group
                , Σ h ꞉ (⟨ H ⟩ → ⟨ G ⟩)
                , is-embedding h
                × is-homomorphism H G h)
  characterization-of-the-type-of-subgroups =
   Subgroups                                                                                       ≃⟨ i ⟩
   (Σ A ꞉ 𝓟 ⟨ G ⟩ , group-closed (_∈ A))                                                           ≃⟨ ii ⟩
   (Σ (X , h , e) ꞉ Subtype ⟨ G ⟩ , group-closed (fiber h))                                       ≃⟨ iii ⟩
   (Σ X ꞉ 𝓤 ̇ , Σ (h , e) ꞉ X ↪ ⟨ G ⟩ , group-closed (fiber h))                                     ≃⟨ iv ⟩
   (Σ X ꞉ 𝓤 ̇ , Σ (h , e) ꞉ X ↪ ⟨ G ⟩ , Σ τ ꞉ T X , is-homomorphism (X , τ) G h)                    ≃⟨ v ⟩
   (Σ X ꞉ 𝓤 ̇ , Σ h ꞉ (X → ⟨ G ⟩) , Σ e ꞉ is-embedding h , Σ τ ꞉ T X , is-homomorphism (X , τ) G h) ≃⟨ vi ⟩
   (Σ X ꞉ 𝓤 ̇ , Σ h ꞉ (X → ⟨ G ⟩) , Σ τ ꞉ T X , Σ e ꞉ is-embedding h , is-homomorphism (X , τ) G h) ≃⟨ vii ⟩
   (Σ X ꞉ 𝓤 ̇ , Σ τ ꞉ T X , Σ h ꞉ (X → ⟨ G ⟩) , is-embedding h × is-homomorphism (X , τ) G h)       ≃⟨ viii ⟩
   (Σ H ꞉ Group , Σ h ꞉ (⟨ H ⟩ → ⟨ G ⟩) , is-embedding h × is-homomorphism H G h)                  ■
      where
       open special-classifier-single-universe 𝓤

       φ : Subtype ⟨ G ⟩ → 𝓟 ⟨ G ⟩
       φ = χ-special is-prop ⟨ G ⟩

       j : is-equiv φ
       j = χ-special-is-equiv (ua 𝓤) fe is-prop ⟨ G ⟩

       i    = ≃-refl Subgroups
       ii   = ≃-sym (Σ-change-of-variable (λ (A : 𝓟 ⟨ G ⟩) → group-closed (_∈ A)) φ j)
       iii  = Σ-assoc
       iv   = Σ-cong (λ X → Σ-cong (λ (h , e) → fiber-structure-lemma h e fe))
       v    = Σ-cong (λ X → Σ-assoc)
       vi   = Σ-cong (λ X → Σ-cong (λ h → Σ-flip))
       vii  = Σ-cong (λ X → Σ-flip)
       viii = ≃-sym Σ-assoc

  induced-group : Subgroups → Group
  induced-group S = pr₁ (⌜ characterization-of-the-type-of-subgroups ⌝ S)

module ring {𝓤 : Universe} (ua : Univalence) where
 open sip hiding (⟨_⟩)
 open sip-with-axioms
 open sip-join

 fe : ∀ {𝓥} {𝓦} → funext 𝓥 𝓦
 fe {𝓥} {𝓦} = univalence-gives-funext' 𝓥 𝓦 (ua 𝓥) (ua (𝓥 ⊔ 𝓦))

 rng-structure : 𝓤 ̇ → 𝓤 ̇
 rng-structure X = (X → X → X) × (X → X → X)

 rng-axioms : (R : 𝓤 ̇ ) → rng-structure R → 𝓤 ̇
 rng-axioms R (_+_ , _·_) = I × II × III × IV × V × VI × VII
  where
    I   = is-set R
    II  = (x y z : R) → (x + y) + z ＝ x + (y + z)
    III = (x y : R) → x + y ＝ y + x
    IV  = Σ O ꞉ R , ((x : R) → x + O ＝ x) × ((x : R) → Σ x' ꞉ R , x + x' ＝ O)
    V   = (x y z : R) → (x · y) · z ＝ x · (y · z)
    VI  = (x y z : R) → x · (y + z) ＝ (x · y) + (x · z)
    VII = (x y z : R) → (y + z) · x ＝ (y · x) + (z · x)

 Rng : 𝓤 ⁺ ̇
 Rng = Σ R ꞉ 𝓤 ̇ , Σ s ꞉ rng-structure R , rng-axioms R s

 rng-axioms-is-prop : (R : 𝓤 ̇ ) (s : rng-structure R)
                    → is-prop (rng-axioms R s)
 rng-axioms-is-prop R (_+_ , _·_) = prop-criterion δ
  where
   δ : rng-axioms R (_+_ , _·_) → is-prop (rng-axioms R (_+_ , _·_))
   δ (i , ii , iii , iv-vii) = γ
    where
     A   = λ (O : R) → ((x : R) → x + O ＝ x)
                     × ((x : R) → Σ x' ꞉ R , x + x' ＝ O)

     IV  = Σ A

     a : (O O' : R) → ((x : R) → x + O ＝ x) → ((x : R) → x + O' ＝ x) → O ＝ O'
     a O O' f f' = O       ＝⟨ (f' O)⁻¹ ⟩
                  (O + O') ＝⟨ iii O O' ⟩
                  (O' + O) ＝⟨ f O' ⟩
                   O'      ∎

     b : (O : R) → is-prop ((x : R) → x + O ＝ x)
     b O = Π-is-prop fe (λ x → i {x + O} {x})

     c : (O : R)
       → ((x : R) → x + O ＝ x)
       → (x : R) → is-prop (Σ x' ꞉ R , x + x' ＝ O)
     c O f x (x' , p') (x'' , p'') = to-subtype-＝ (λ y → i {x + y} {O}) r
      where
       r : x' ＝ x''
       r = x'               ＝⟨ (f x')⁻¹ ⟩
           (x' + O)         ＝⟨ ap (x' +_) (p'' ⁻¹) ⟩
           (x' + (x + x'')) ＝⟨ (ii x' x x'')⁻¹ ⟩
           ((x' + x) + x'') ＝⟨ ap (_+ x'') (iii x' x) ⟩
           ((x + x') + x'') ＝⟨ ap (_+ x'') p' ⟩
           (O + x'')        ＝⟨ iii O x'' ⟩
           (x'' + O)        ＝⟨ f x'' ⟩
           x''              ∎

     d : (O : R) → is-prop (A O)
     d O (f , g) = φ (f , g)
      where
       φ : is-prop (A O)
       φ = ×-is-prop (b O) (Π-is-prop fe (λ x → c O f x))

     IV-is-prop : is-prop IV
     IV-is-prop (O , f , g) (O' , f' , g') = e
      where
       e : (O , f , g) ＝ (O' , f' , g')
       e = to-subtype-＝ d (a O O' f f')

     γ : is-prop (rng-axioms R (_+_ , _·_))
     γ = ×₇-is-prop
          (being-set-is-prop fe)
          (Π₃-is-prop fe
           (λ x y z → i {(x + y) + z} {x + (y + z)}))
          (Π₂-is-prop fe
            (λ x y → i {x + y} {y + x}))
          IV-is-prop
          (Π₃-is-prop fe
           (λ x y z → i {(x · y) · z} {x · (y · z)}))
          (Π₃-is-prop fe
           (λ x y z → i {x · (y + z)} {(x · y) + (x · z)}))
          (Π₃-is-prop fe
           (λ x y z → i {(y + z) · x} {(y · x) + (z · x)}))

 _≅[Rng]_ : Rng → Rng → 𝓤 ̇

 (R , (_+_ , _·_) , _) ≅[Rng] (R' , (_+'_ , _·'_) , _) =

                       Σ f ꞉ (R → R')
                           , is-equiv f
                           × ((λ x y → f (x + y)) ＝[ (R → R → R') ]
                              (λ x y → f x +' f y))
                           × ((λ x y → f (x · y)) ＝[ (R → R → R') ]
                              (λ x y → f x ·' f y))

 characterization-of-rng-＝ : (𝓡 𝓡' : Rng) → (𝓡 ＝ 𝓡') ≃ (𝓡 ≅[Rng] 𝓡')
 characterization-of-rng-＝ = characterization-of-＝ (ua 𝓤)
                              (add-axioms
                                rng-axioms
                                rng-axioms-is-prop
                                (join
                                  ∞-magma.sns-data
                                  ∞-magma.sns-data))

 ⟨_⟩ : (𝓡 : Rng) → 𝓤 ̇
 ⟨ R , _ ⟩ = R

 ring-structure : 𝓤 ̇ → 𝓤 ̇
 ring-structure X = X × rng-structure X

 ring-axioms : (R : 𝓤 ̇ ) → ring-structure R → 𝓤 ̇
 ring-axioms R (𝟏 , _+_ , _·_) = rng-axioms R (_+_ , _·_) × VIII
  where
   VIII = (x : R) → (x · 𝟏 ＝ x) × (𝟏 · x ＝ x)

 ring-axioms-is-prop : (R : 𝓤 ̇ ) (s : ring-structure R)
                             → is-prop (ring-axioms R s)
 ring-axioms-is-prop R (𝟏 , _+_ , _·_) ((i , ii-vii) , viii) =
  γ ((i , ii-vii) , viii)
  where
   γ : is-prop (ring-axioms R (𝟏 , _+_ , _·_))
   γ = ×-is-prop
         (rng-axioms-is-prop R (_+_ , _·_))
         (Π-is-prop fe (λ x → ×-is-prop (i {x · 𝟏} {x}) (i {𝟏 · x} {x})))

 Ring : 𝓤 ⁺ ̇
 Ring = Σ R ꞉ 𝓤 ̇ , Σ s ꞉ ring-structure R , ring-axioms R s

 _≅[Ring]_ : Ring → Ring → 𝓤 ̇

 (R , (𝟏 , _+_ , _·_) , _) ≅[Ring] (R' , (𝟏' , _+'_ , _·'_) , _) =

                           Σ f ꞉ (R → R')
                               , is-equiv f
                               × (f 𝟏 ＝ 𝟏')
                               × ((λ x y → f (x + y)) ＝[ (R → R → R') ]
                                  (λ x y → f x +' f y))
                               × ((λ x y → f (x · y)) ＝[ (R → R → R') ]
                                  (λ x y → f x ·' f y))

 characterization-of-ring-＝ : (𝓡 𝓡' : Ring) → (𝓡 ＝ 𝓡') ≃ (𝓡 ≅[Ring] 𝓡')
 characterization-of-ring-＝ = sip.characterization-of-＝ (ua 𝓤)
                                (sip-with-axioms.add-axioms
                                  ring-axioms
                                  ring-axioms-is-prop
                                  (sip-join.join
                                    pointed-type.sns-data
                                      (join
                                        ∞-magma.sns-data
                                        ∞-magma.sns-data)))

 is-commutative : Rng → 𝓤 ̇
 is-commutative (R , (_+_ , _·_) , _) = (x y : R) → x · y ＝ y · x

 being-commutative-is-prop : (𝓡 : Rng) → is-prop (is-commutative 𝓡)
 being-commutative-is-prop (R , (_+_ , _·_) , i , ii-vii) =
   Π₂-is-prop fe (λ x y → i {x · y} {y · x})

 open import UF.Powerset

 is-ideal : (𝓡 : Rng) → 𝓟 ⟨ 𝓡 ⟩ → 𝓤 ̇
 is-ideal (R , (_+_ , _·_) , _) I = (x y : R) → (x ∈ I → y ∈ I → (x + y) ∈ I)
                                              × (x ∈ I → (x · y) ∈ I)
                                              × (y ∈ I → (x · y) ∈ I)

 is-local : Rng → 𝓤 ⁺ ̇
 is-local 𝓡 = ∃! I ꞉ 𝓟 ⟨ 𝓡 ⟩ , (is-ideal 𝓡 I
                               → (J : 𝓟 ⟨ 𝓡 ⟩)
                               → is-ideal 𝓡 J
                               → J ⊆ I)

 being-local-is-prop : (𝓡 : Rng) → is-prop (is-local 𝓡)
 being-local-is-prop 𝓡 = ∃!-is-prop fe

 open import UF.PropTrunc

 module _ (pt : propositional-truncations-exist) where

  open propositional-truncations-exist pt public
  open PropositionalTruncation pt
  open import Naturals.Order

  is-noetherian : (𝓡 : Rng) → 𝓤 ⁺ ̇
  is-noetherian 𝓡 = (I : ℕ → 𝓟 ⟨ 𝓡 ⟩)
                  → ((n : ℕ) → is-ideal 𝓡 (I n))
                  → ((n : ℕ) → I n ⊆ I (succ n))
                  → ∃ m ꞉ ℕ , ((n : ℕ) → m ≤ n → I m ＝ I n)

  NoetherianRng : 𝓤 ⁺ ̇
  NoetherianRng = Σ 𝓡 ꞉ Rng , is-noetherian 𝓡

  being-noetherian-is-prop : (𝓡 : Rng) → is-prop (is-noetherian 𝓡)
  being-noetherian-is-prop 𝓡 = Π₃-is-prop fe (λ I _ _ → ∃-is-prop)

  forget-Noether : NoetherianRng → Rng
  forget-Noether (𝓡 , _) = 𝓡

  forget-Noether-is-embedding : is-embedding forget-Noether
  forget-Noether-is-embedding = pr₁-is-embedding being-noetherian-is-prop

  _≅[NoetherianRng]_ : NoetherianRng → NoetherianRng → 𝓤 ̇
  ((R , (_+_ , _·_) , _) , _) ≅[NoetherianRng] ((R' , (_+'_ , _·'_) , _) , _) =
      Σ f ꞉ (R → R')
          , is-equiv f
          × ((λ x y → f (x + y)) ＝[ (R → R → R') ] (λ x y → f x +' f y))
          × ((λ x y → f (x · y)) ＝[ (R → R → R') ] (λ x y → f x ·' f y))

  NB : (𝓡 𝓡' : NoetherianRng)
     → (𝓡 ≅[NoetherianRng] 𝓡') ＝ (forget-Noether 𝓡 ≅[Rng] forget-Noether 𝓡')
  NB 𝓡 𝓡' = refl

  characterization-of-nrng-＝ : (𝓡 𝓡' : NoetherianRng)
                             → (𝓡 ＝ 𝓡') ≃ (𝓡 ≅[NoetherianRng] 𝓡')
  characterization-of-nrng-＝ 𝓡 𝓡' =

    (𝓡 ＝ 𝓡')                               ≃⟨ i ⟩
    (forget-Noether 𝓡 ＝ forget-Noether 𝓡') ≃⟨ ii ⟩
    (𝓡 ≅[NoetherianRng] 𝓡')                ■
    where
     i = ≃-sym (embedding-criterion-converse forget-Noether
                  forget-Noether-is-embedding 𝓡 𝓡')
     ii = characterization-of-rng-＝ (forget-Noether 𝓡) (forget-Noether 𝓡')

  isomorphic-NoetherianRng-transport
   : (A : NoetherianRng → 𝓥 ̇ )
     (𝓡 𝓡' : NoetherianRng)
   → 𝓡 ≅[NoetherianRng] 𝓡'
   → A 𝓡
   → A 𝓡'
  isomorphic-NoetherianRng-transport A 𝓡 𝓡' i a = a'
   where
    p : 𝓡 ＝ 𝓡'
    p = ⌜ characterization-of-nrng-＝ 𝓡 𝓡' ⌝⁻¹ i

    a' : A 𝓡'
    a' = transport A p a

  is-CNL : Ring → 𝓤 ⁺ ̇
  is-CNL (R , (𝟏 , _+_ , _·_) , i-vii , viii) = is-commutative 𝓡
                                              × is-noetherian 𝓡
                                              × is-local 𝓡
   where
    𝓡 : Rng
    𝓡 = (R , (_+_ , _·_) , i-vii)

  being-CNL-is-prop : (𝓡 : Ring) → is-prop (is-CNL 𝓡)
  being-CNL-is-prop (R , (𝟏 , _+_ , _·_) , i-vii , viii) =
     ×₃-is-prop
      (being-commutative-is-prop 𝓡)
      (being-noetherian-is-prop 𝓡)
      (being-local-is-prop 𝓡)
   where
    𝓡 : Rng
    𝓡 = (R , (_+_ , _·_) , i-vii)

  CNL-Ring : 𝓤 ⁺ ̇
  CNL-Ring = Σ 𝓡 ꞉ Ring , is-CNL 𝓡

  _≅[CNL]_ : CNL-Ring → CNL-Ring → 𝓤 ̇

  ((R , (𝟏 , _+_ , _·_) , _) , _) ≅[CNL] ((R' , (𝟏' , _+'_ , _·'_) , _) , _) =

   Σ f ꞉ (R → R')
       , is-equiv f
       × (f 𝟏 ＝ 𝟏')
       × ((λ x y → f (x + y)) ＝[ (R → R → R') ] (λ x y → f x +' f y))
       × ((λ x y → f (x · y)) ＝[ (R → R → R') ] (λ x y → f x ·' f y))

  forget-CNL : CNL-Ring → Ring
  forget-CNL (𝓡 , _) = 𝓡

  forget-CNL-is-embedding : is-embedding forget-CNL
  forget-CNL-is-embedding = pr₁-is-embedding being-CNL-is-prop

  NB' : (𝓡 𝓡' : CNL-Ring)
      → (𝓡 ≅[CNL] 𝓡') ＝ (forget-CNL 𝓡 ≅[Ring] forget-CNL 𝓡')
  NB' 𝓡 𝓡' = refl

  characterization-of-CNL-ring-＝ : (𝓡 𝓡' : CNL-Ring)
                                 → (𝓡 ＝ 𝓡') ≃ (𝓡 ≅[CNL] 𝓡')
  characterization-of-CNL-ring-＝ 𝓡 𝓡' =
     (𝓡 ＝ 𝓡')                               ≃⟨ i ⟩
     (forget-CNL 𝓡 ＝ forget-CNL 𝓡')         ≃⟨ ii ⟩
     (𝓡 ≅[CNL] 𝓡')                          ■
     where
      i = ≃-sym (embedding-criterion-converse forget-CNL
                   forget-CNL-is-embedding 𝓡 𝓡')
      ii = characterization-of-ring-＝ (forget-CNL 𝓡) (forget-CNL 𝓡')

  isomorphic-CNL-Ring-transport
   : (A : CNL-Ring → 𝓥 ̇ )
     (𝓡 𝓡' : CNL-Ring)
   → 𝓡 ≅[CNL] 𝓡'
   → A 𝓡
   → A 𝓡'
  isomorphic-CNL-Ring-transport A 𝓡 𝓡' i a = a'
   where
    p : 𝓡 ＝ 𝓡'
    p = ⌜ characterization-of-CNL-ring-＝ 𝓡 𝓡' ⌝⁻¹ i

    a' : A 𝓡'
    a' = transport A p a

module slice
        {𝓤 𝓥 : Universe}
        (R : 𝓥 ̇ )
       where

 open sip

 S : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 S X = X → R

 sns-data : SNS S (𝓤 ⊔ 𝓥)
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ⊔ 𝓥 ̇
   ι (X , g) (Y , h) (f , _) = (g ＝ h ∘ f)

   ρ : (A : Σ S) → ι A A (≃-refl ⟨ A ⟩)
   ρ (X , g) = 𝓻𝓮𝒻𝓵 g

   k : {X : 𝓤 ̇ } {g h : S X} → canonical-map ι ρ g h ∼ -id (g ＝ h)
   k (refl {g}) = 𝓻𝓮𝒻𝓵 (𝓻𝓮𝒻𝓵 g)

   θ : {X : 𝓤 ̇ } (g h : S X) → is-equiv (canonical-map ι ρ g h)
   θ g h = equiv-closed-under-∼
            id
            (canonical-map ι ρ g h)
            (id-is-equiv (g ＝ h))
            k

 _/_ : (𝓤 : Universe) → 𝓥 ̇ → 𝓤 ⁺ ⊔ 𝓥 ̇
 𝓤 / Y = Σ X ꞉ 𝓤 ̇ , (X → Y)

 _≅_  : 𝓤 / R → 𝓤 / R → 𝓤 ⊔ 𝓥 ̇
 (X , g) ≅ (Y , h) = Σ f ꞉ (X → Y), is-equiv f × (g ＝ h ∘ f)

 characterization-of-/-＝ : is-univalent 𝓤 → (A B : 𝓤 / R) → (A ＝ B) ≃ (A ≅ B)
 characterization-of-/-＝ ua = characterization-of-＝ ua sns-data

module slice-variation
        {𝓤 𝓥 : Universe}
        (R : 𝓥 ̇ )
        (ua : is-univalent 𝓤)
        (fe : funext 𝓤 𝓥)
       where

 open sip

 S : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 S X = X → R

 sns-data : SNS S (𝓤 ⊔ 𝓥)
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ⊔ 𝓥 ̇
   ι (X , g) (Y , h) (f , _) = ((x : X) → g x ＝ h (f x))

   ρ : (A : Σ S) → ι A A (≃-refl ⟨ A ⟩)
   ρ (X , g) = λ x → 𝓻𝓮𝒻𝓵 (g x)

   k : {X : 𝓤 ̇ } {g h : S X} → canonical-map ι ρ g h ∼ happly' g h
   k (refl {g}) = 𝓻𝓮𝒻𝓵 (λ x → 𝓻𝓮𝒻𝓵 (g x))

   θ : {X : 𝓤 ̇ } (g h : S X) → is-equiv (canonical-map ι ρ g h)
   θ g h = equiv-closed-under-∼ (happly' g h) (canonical-map ι ρ g h) (fe g h) k

 _/_ : (𝓤 : Universe) → 𝓥 ̇ → 𝓤 ⁺ ⊔ 𝓥 ̇
 𝓤 / Y = Σ X ꞉ 𝓤 ̇ , (X → Y)

 _≅_  : 𝓤 / R → 𝓤 / R → 𝓤 ⊔ 𝓥 ̇
 (X , g) ≅ (Y , h) = Σ f ꞉ (X → Y), is-equiv f × ((x : X) → g x ＝ h (f x))

 characterization-of-/-＝ : (A B : 𝓤 / R) → (A ＝ B) ≃ (A ≅ B)
 characterization-of-/-＝ = characterization-of-＝ ua sns-data

module universe-a-la-tarski
        (𝓤 𝓥 : Universe)
        (ua : is-univalent 𝓤)
        (fe : funext 𝓤 (𝓥 ⁺))
       where

 TarskiUniverse : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
 TarskiUniverse 𝓤 𝓥 = Σ X ꞉ 𝓤 ̇ , (X → 𝓥 ̇ )

 _≅_  : TarskiUniverse 𝓤 𝓥 → TarskiUniverse 𝓤 𝓥 → 𝓤 ⊔ (𝓥 ⁺) ̇
 (X , T) ≅ (X' , T') = Σ f ꞉ (X → X'), is-equiv f × ((x : X) → T x ＝ T' (f x))

 characterization-of-Tarski-＝ : (A B : TarskiUniverse 𝓤 𝓥)
                              → (A ＝ B) ≃ (A ≅ B)
 characterization-of-Tarski-＝ =
  slice-variation.characterization-of-/-＝ (𝓥 ̇ ) ua fe

module universe-a-la-tarski-hSet-example
        (𝓤 : Universe)
        (ua : is-univalent (𝓤 ⁺))
       where

 fe : funext (𝓤 ⁺) (𝓤 ⁺)
 fe = univalence-gives-funext ua

 open universe-a-la-tarski (𝓤 ⁺) 𝓤 ua fe

 hset : TarskiUniverse (𝓤 ⁺) 𝓤
 hset = hSet 𝓤 , pr₁

 example : (X : 𝓤 ⁺ ̇ ) (T : X → 𝓤 ̇ )
         → ((X , T) ＝ hset) ≃ (Σ f ꞉ (X → hSet 𝓤) , is-equiv f
                                                  × ((x : X) → T x ＝ pr₁ (f x)))
 example X T = characterization-of-Tarski-＝ (X , T) hset

module generalized-metric-space
        {𝓤 𝓥 𝓦  : Universe}
        (R : 𝓥 ̇ )
        (axioms  : (X : 𝓤 ̇ ) → (X → X → R) → 𝓦 ̇ )
        (axiomss : (X : 𝓤 ̇ ) (d : X → X → R) → is-prop (axioms X d))
       where

 open sip
 open sip-with-axioms

 S : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 S X = X → X → R

 sns-data : SNS S (𝓤 ⊔ 𝓥)
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ⊔ 𝓥 ̇
   ι (X , d) (Y , e) (f , _) = (d ＝ λ x x' → e (f x) (f x'))

   ρ : (A : Σ S) → ι A A (≃-refl ⟨ A ⟩)
   ρ (X , d) = 𝓻𝓮𝒻𝓵 d

   h : {X : 𝓤 ̇ } {d e : S X} → canonical-map ι ρ d e ∼ -id (d ＝ e)
   h (refl {d}) = 𝓻𝓮𝒻𝓵 (𝓻𝓮𝒻𝓵 d)

   θ : {X : 𝓤 ̇ } (d e : S X) → is-equiv (canonical-map ι ρ d e)
   θ d e = equiv-closed-under-∼
            id
            (canonical-map ι ρ d e)
            (id-is-equiv (d ＝ e))
            h

 M : 𝓤 ⁺ ⊔ 𝓥 ⊔ 𝓦 ̇
 M = Σ X ꞉ 𝓤 ̇ , Σ d ꞉ (X → X → R) , axioms X d

 _≅_  : M → M → 𝓤 ⊔ 𝓥 ̇
 (X , d , _) ≅ (Y , e , _) = Σ f ꞉ (X → Y), is-equiv f
                                          × (d ＝ λ x x' → e (f x) (f x'))

 characterization-of-M-＝ : is-univalent 𝓤
                         → (A B : M)
                         → (A ＝ B) ≃ (A ≅ B)
 characterization-of-M-＝ ua = characterization-of-＝-with-axioms ua
                                sns-data
                                axioms
                                axiomss

 _≅'_  : M → M → 𝓤 ⊔ 𝓥 ̇
 (X , d , _) ≅' (Y , e , _)
             = Σ f ꞉ (X → Y), is-equiv f
                            × ((x x' : X) → d x x' ＝ e (f x) (f x'))


 characterization-of-M-＝'
  : Univalence
  → ((X , d , a) (Y , e , b) : M)
  → ((X , d , a) ＝ (Y , e , b))
                 ≃  (Σ f ꞉ (X → Y), is-equiv f
                                  × ((x x' : X) → d x x' ＝ e (f x) (f x')))
 characterization-of-M-＝' ua (X , d , a) (Y , e , b) =
     characterization-of-M-＝ (ua 𝓤) (X , d , a) (Y , e , b)
   ● Σ-cong (λ f → ×-cong (≃-refl (is-equiv f))
                         (≃-funext₂ (Univalence-gives-FunExt ua 𝓤 (𝓤 ⊔ 𝓥))
                                    (Univalence-gives-FunExt ua 𝓤 𝓥)
                                    (λ x y → d x y)
                                    (λ x x' → e (f x) (f x'))))

module generalized-topological-space
        (𝓤 𝓥 : Universe)
        (R : 𝓥 ̇ )
        (axioms  : (X : 𝓤 ̇ ) → ((X → R) → R) → 𝓤 ⊔ 𝓥 ̇ )
        (axiomss : (X : 𝓤 ̇ ) (𝓞 : (X → R) → R) → is-prop (axioms X 𝓞))
       where

 open sip
 open sip-with-axioms

 ℙ : 𝓦 ̇ → 𝓥 ⊔ 𝓦 ̇
 ℙ X = X → R

 _∊_ : {X : 𝓦 ̇ } → X → ℙ X → R
 x ∊ A = A x

 inverse-image : {X Y : 𝓤 ̇ } → (X → Y) → ℙ Y → ℙ X
 inverse-image f B = λ x → f x ∊ B

 ℙℙ : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 ℙℙ X = ℙ (ℙ X)

 Space : 𝓤 ⁺ ⊔ 𝓥 ̇
 Space = Σ X ꞉ 𝓤 ̇ , Σ 𝓞 ꞉ ℙℙ X , axioms X 𝓞

 sns-data : SNS ℙℙ (𝓤 ⊔ 𝓥)
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Σ ℙℙ) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ⊔ 𝓥 ̇
   ι (X , 𝓞X) (Y , 𝓞Y) (f , _) = (λ (V : ℙ Y) → inverse-image f V ∊ 𝓞X) ＝ 𝓞Y

   ρ : (A : Σ ℙℙ) → ι A A (≃-refl ⟨ A ⟩)
   ρ (X , 𝓞) = 𝓻𝓮𝒻𝓵 𝓞

   h : {X : 𝓤 ̇ } {𝓞 𝓞' : ℙℙ X} → canonical-map ι ρ 𝓞 𝓞' ∼ -id (𝓞 ＝ 𝓞')
   h (refl {𝓞}) = 𝓻𝓮𝒻𝓵 (𝓻𝓮𝒻𝓵 𝓞)

   θ : {X : 𝓤 ̇ } (𝓞 𝓞' : ℙℙ X) → is-equiv (canonical-map ι ρ 𝓞 𝓞')
   θ {X} 𝓞 𝓞' = equiv-closed-under-∼ id (canonical-map ι ρ 𝓞 𝓞') (id-is-equiv (𝓞 ＝ 𝓞')) h

 _≅_  : Space → Space → 𝓤 ⊔ 𝓥 ̇
 (X , 𝓞X , _) ≅ (Y , 𝓞Y , _) =

              Σ f ꞉ (X → Y), is-equiv f
                           × ((λ V → inverse-image f V ∊ 𝓞X) ＝ 𝓞Y)

 characterization-of-Space-＝ : is-univalent 𝓤
                             → (A B : Space)
                             → (A ＝ B) ≃ (A ≅ B)
 characterization-of-Space-＝ ua = characterization-of-＝-with-axioms ua
                                   sns-data axioms axiomss

 _≅'_  : Space → Space → 𝓤 ⊔ 𝓥 ̇
 (X , F , _) ≅' (Y , G , _) =
             Σ f ꞉ (X → Y), is-equiv f
                          × ((λ (v : Y → R) → F (v ∘ f)) ＝ G)

 characterization-of-Space-＝' : is-univalent 𝓤
                              → (A B : Space)
                              → (A ＝ B) ≃ (A ≅' B)
 characterization-of-Space-＝' = characterization-of-Space-＝

module selection-space
        (𝓤 𝓥 : Universe)
        (R : 𝓥 ̇ )
        (axioms  : (X : 𝓤 ̇ ) → ((X → R) → X) → 𝓤 ⊔ 𝓥 ̇ )
        (axiomss : (X : 𝓤 ̇ ) (ε : (X → R) → X) → is-prop (axioms X ε))
       where

 open sip
 open sip-with-axioms

 S : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 S X = (X → R) → X

 SelectionSpace : 𝓤 ⁺ ⊔ 𝓥 ̇
 SelectionSpace = Σ X ꞉ 𝓤 ̇ , Σ ε ꞉ S X , axioms X ε

 sns-data : SNS S (𝓤 ⊔ 𝓥)
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ⊔ 𝓥 ̇
   ι (X , ε) (Y , δ) (f , _) = (λ (q : Y → R) → f (ε (q ∘ f))) ＝ δ

   ρ : (A : Σ S) → ι A A (≃-refl ⟨ A ⟩)
   ρ (X , ε) = 𝓻𝓮𝒻𝓵 ε

   θ : {X : 𝓤 ̇ } (ε δ : S X) → is-equiv (canonical-map ι ρ ε δ)
   θ {X} ε δ = γ
    where
     h : canonical-map ι ρ ε δ ∼ -id (ε ＝ δ)
     h (refl {ε}) = 𝓻𝓮𝒻𝓵 (𝓻𝓮𝒻𝓵 ε)

     γ : is-equiv (canonical-map ι ρ ε δ)
     γ = equiv-closed-under-∼ id (canonical-map ι ρ ε δ) (id-is-equiv (ε ＝ δ)) h

 _≅_  :  SelectionSpace → SelectionSpace → 𝓤 ⊔ 𝓥 ̇
 (X , ε , _) ≅ (Y , δ , _) =
             Σ f ꞉ (X → Y), is-equiv f
                          × ((λ (q : Y → R) → f (ε (q ∘ f))) ＝ δ)

 characterization-of-selection-space-＝ : is-univalent 𝓤
                                       → (A B : SelectionSpace)
                                       → (A ＝ B) ≃ (A ≅ B)
 characterization-of-selection-space-＝ ua =
  characterization-of-＝-with-axioms ua sns-data axioms axiomss

module contrived-example (𝓤 : Universe) where

 open sip

 contrived-＝
  : is-univalent 𝓤
  → (X Y : 𝓤 ̇ ) (φ : (X → X) → X) (γ : (Y → Y) → Y)
  → ((X , φ) ＝ (Y , γ)) ≃ (Σ f ꞉ (X → Y)
                          , Σ i ꞉ is-equiv f
                          , (λ (g : Y → Y) → f (φ (inverse f i ∘ g ∘ f))) ＝ γ)
 contrived-＝ ua X Y φ γ =
   characterization-of-＝ ua
    ((λ (X , φ) (Y , γ) (f , i) → (λ (g : Y → Y) → f (φ (inverse f i ∘ g ∘ f))) ＝ γ) ,
     (λ (X , φ) → 𝓻𝓮𝒻𝓵 φ) ,
     (λ φ γ → equiv-closed-under-∼ _ _ (id-is-equiv (φ ＝ γ)) (λ {(refl {φ}) → 𝓻𝓮𝒻𝓵 (𝓻𝓮𝒻𝓵 φ)})))
    (X , φ) (Y , γ)

module generalized-functor-algebra
         {𝓤 𝓥 : Universe}
         (F : 𝓤 ̇ → 𝓥 ̇ )
         (𝓕 : {X Y : 𝓤 ̇ } → (X → Y) → F X → F Y)
         (𝓕-id : {X : 𝓤 ̇ } → 𝓕 (-id X) ＝ -id (F X))
       where

 open sip

 S : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 S X = F X → X

 sns-data : SNS S (𝓤 ⊔ 𝓥)
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ⊔ 𝓥 ̇
   ι (X , α) (Y , β) (f , _) = f ∘ α ＝ β ∘ 𝓕 f

   ρ : (A : Σ S) → ι A A (≃-refl ⟨ A ⟩)
   ρ (X , α) = α        ＝⟨ ap (α ∘_) (𝓕-id ⁻¹) ⟩
               α ∘ 𝓕 id ∎

   θ : {X : 𝓤 ̇ } (α β : S X) → is-equiv (canonical-map ι ρ α β)
   θ {X} α β = γ
    where
     c : α ＝ β → α ＝ β ∘ 𝓕 id
     c = transport (α ＝_) (ρ (X , β))

     i : is-equiv c
     i = transports-are-equivs (ρ (X , β))

     h : canonical-map ι ρ α β ∼ c
     h refl = ρ (X , α)           ＝⟨ refl-left-neutral ⁻¹ ⟩
              𝓻𝓮𝒻𝓵 α ∙ ρ (X , α) ∎

     γ : is-equiv (canonical-map ι ρ α β)
     γ = equiv-closed-under-∼ c (canonical-map ι ρ α β) i h

 characterization-of-functor-algebra-＝
  : is-univalent 𝓤
  → (X Y : 𝓤 ̇ ) (α : F X → X) (β : F Y → Y)
  → ((X , α) ＝ (Y , β)) ≃ (Σ f ꞉ (X → Y), is-equiv f × (f ∘ α ＝ β ∘ 𝓕 f))
 characterization-of-functor-algebra-＝ ua X Y α β =
   characterization-of-＝ ua sns-data (X , α) (Y , β)

type-valued-preorder-S : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ̇
type-valued-preorder-S {𝓤} {𝓥} X = Σ _≤_ ꞉ (X → X → 𝓥 ̇ )
                                         , ((x : X) → x ≤ x)
                                         × ((x y z : X) → x ≤ y → y ≤ z → x ≤ z)

module type-valued-preorder
        (𝓤 𝓥 : Universe)
        (ua : Univalence)
       where

 open sip

 fe : Fun-Ext
 fe {𝓤} {𝓥} = Univalence-gives-FunExt ua 𝓤 𝓥

 S : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ̇
 S = type-valued-preorder-S {𝓤} {𝓥}

 Type-valued-preorder : (𝓤 ⊔ 𝓥) ⁺ ̇
 Type-valued-preorder = Σ S

 Ob : Σ S → 𝓤 ̇
 Ob (X , homX , idX , compX) = X

 hom : (𝓧 : Σ S) → Ob 𝓧 → Ob 𝓧 → 𝓥 ̇
 hom (X , homX , idX , compX) = homX

 𝒾𝒹 : (𝓧 : Σ S) (x : Ob 𝓧) → hom 𝓧 x x
 𝒾𝒹 (X , homX , idX , compX) = idX

 comp : (𝓧 : Σ S) (x y z : Ob 𝓧) → hom 𝓧 x y → hom 𝓧 y z → hom 𝓧 x z
 comp (X , homX , idX , compX) = compX

 functorial : (𝓧 𝓐 : Σ S)
            → (F : Ob 𝓧 → Ob 𝓐)
            → ((x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
            → 𝓤 ⊔ 𝓥 ̇

 functorial 𝓧 𝓐 F 𝓕' = pidentity × pcomposition
  where

   _o_ : {x y z : Ob 𝓧} → hom 𝓧 y z → hom 𝓧 x y → hom 𝓧 x z
   g o f = comp 𝓧 _ _ _ f g

   _□_ : {a b c : Ob 𝓐} → hom 𝓐 b c → hom 𝓐 a b → hom 𝓐 a c
   g □ f = comp 𝓐 _ _ _ f g

   𝓕 : {x y : Ob 𝓧} → hom 𝓧 x y → hom 𝓐 (F x) (F y)
   𝓕 f = 𝓕' _ _ f

   pidentity = (λ x → 𝓕 (𝒾𝒹 𝓧 x)) ＝[ ((x : Ob 𝓧) → hom 𝓐 (F x) (F x)) ]
               (λ x → 𝒾𝒹 𝓐 (F x))

   pcomposition =
    (λ x y z (f : hom 𝓧 x y) (g : hom 𝓧 y z) → 𝓕 (g o f))
    ＝[ ((x y z : Ob 𝓧) (f : hom 𝓧 x y) (g : hom 𝓧 y z) → hom 𝓐 (F x) (F z)) ]
    (λ x y z (f : hom 𝓧 x y) (g : hom 𝓧 y z) → 𝓕 g □ 𝓕 f)

 sns-data : SNS S (𝓤 ⊔ (𝓥 ⁺))
 sns-data = (ι , ρ , θ)
  where
   ι : (𝓧 𝓐 : Σ S) → ⟨ 𝓧 ⟩ ≃ ⟨ 𝓐 ⟩ → 𝓤 ⊔ (𝓥 ⁺) ̇
   ι 𝓧 𝓐 (F , _) = Σ p ꞉ hom 𝓧 ＝ (λ x y → hom 𝓐 (F x) (F y))
                       , functorial 𝓧 𝓐 F (λ x y → transport (λ - → - x y) p)

   ρ : (𝓧 : Σ S) → ι 𝓧 𝓧 (≃-refl ⟨ 𝓧 ⟩)
   ρ 𝓧 = 𝓻𝓮𝒻𝓵 (hom 𝓧) , 𝓻𝓮𝒻𝓵 (𝒾𝒹 𝓧) , 𝓻𝓮𝒻𝓵 (comp 𝓧)

   θ : {X : 𝓤 ̇ } (s t : S X) → is-equiv (canonical-map ι ρ s t)
   θ {X} (homX , idX , compX) (homA , idA , compA) = g
    where
     φ = canonical-map ι ρ (homX , idX , compX) (homA , idA , compA)

     γ : codomain φ → domain φ
     γ (refl , refl , refl) = refl

     η : γ ∘ φ ∼ id
     η refl = refl

     ε : φ ∘ γ ∼ id
     ε (refl , refl , refl) = refl

     g : is-equiv φ
     g = qinvs-are-equivs φ (γ , η , ε)

 lemma : (𝓧 𝓐 : Σ S) (F : Ob 𝓧 → Ob 𝓐)
       →
         (Σ p ꞉ hom 𝓧 ＝ (λ x y → hom 𝓐 (F x) (F y))
              , functorial 𝓧 𝓐 F (λ x y → transport (λ - → - x y) p))
       ≃
         (Σ 𝓕 ꞉ ((x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
              , (∀ x y → is-equiv (𝓕 x y))
              × functorial 𝓧 𝓐 F 𝓕)

 lemma 𝓧 𝓐 F = γ
  where
   e = (hom 𝓧 ＝ λ x y → hom 𝓐 (F x) (F y))                            ≃⟨ i ⟩
       (∀ x y → hom 𝓧 x y ＝ hom 𝓐 (F x) (F y))                        ≃⟨ ii ⟩
       (∀ x y → hom 𝓧 x y ≃ hom 𝓐 (F x) (F y))                        ≃⟨ iii ⟩
       (∀ x → Σ φ ꞉ (∀ y → hom 𝓧 x y → hom 𝓐 (F x) (F y))
                  , ∀ y → is-equiv (φ y))                             ≃⟨ iv ⟩
       (Σ 𝓕 ꞉ ((x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
            , (∀ x y → is-equiv (𝓕 x y)))                             ■
    where
     i   = ≃-funext₂ fe fe (hom 𝓧)  λ x y → hom 𝓐 (F x) (F y)
     ii  = Π-cong fe fe
            (λ x → Π-cong fe fe
                    (λ y → univalence-≃ (ua 𝓥) (hom 𝓧 x y) (hom 𝓐 (F x) (F y))))
     iii = Π-cong fe fe (λ y → ΠΣ-distr-≃)
     iv  = ΠΣ-distr-≃

   v : (p : hom 𝓧 ＝ λ x y → hom 𝓐 (F x) (F y))
     → functorial 𝓧 𝓐 F (λ x y → transport (λ - → - x y) p)
     ≃ functorial 𝓧 𝓐 F (pr₁ (⌜ e ⌝ p))

   v refl = ≃-refl _

   γ =

    (Σ p ꞉ hom 𝓧 ＝ (λ x y → hom 𝓐 (F x) (F y))
         , functorial 𝓧 𝓐 F (λ x y → transport (λ - → - x y) p)) ≃⟨ vi ⟩

    (Σ p ꞉ hom 𝓧 ＝ (λ x y → hom 𝓐 (F x) (F y))
         , functorial 𝓧 𝓐 F (pr₁ (⌜ e ⌝ p)))                     ≃⟨ vii ⟩

    (Σ σ ꞉ (Σ 𝓕 ꞉ ((x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
                , (∀ x y → is-equiv (𝓕 x y)))
         , functorial 𝓧 𝓐 F (pr₁ σ))                             ≃⟨ viii ⟩

    (Σ 𝓕 ꞉ ((x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
                  , (∀ x y → is-equiv (𝓕 x y))
                  × functorial 𝓧 𝓐 F 𝓕)                          ■
    where
     vi   = Σ-cong v
     vii  = Σ-change-of-variable _ ⌜ e ⌝ (⌜⌝-is-equiv e)
     viii = Σ-assoc

 characterization-of-type-valued-preorder-＝
  : (𝓧 𝓐 : Σ S)
  → (𝓧 ＝ 𝓐)
  ≃ (Σ F ꞉ (Ob 𝓧 → Ob 𝓐)
         , is-equiv F
         × (Σ 𝓕 ꞉ ((x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
                , (∀ x y → is-equiv (𝓕 x y))
                × functorial 𝓧 𝓐 F 𝓕))

 characterization-of-type-valued-preorder-＝ 𝓧 𝓐 =
   (𝓧 ＝ 𝓐)                                                              ≃⟨ i ⟩
   (Σ F ꞉ (Ob 𝓧 → Ob 𝓐)
        , is-equiv F
        × (Σ p ꞉ hom 𝓧 ＝ (λ x y → hom 𝓐 (F x) (F y))
               , functorial 𝓧 𝓐 F (λ x y → transport (λ - → - x y) p))) ≃⟨ ii ⟩
   (Σ F ꞉ (Ob 𝓧 → Ob 𝓐)
     , is-equiv F
     × (Σ 𝓕 ꞉ ((x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
            , (∀ x y → is-equiv (𝓕 x y))
            × functorial 𝓧 𝓐 F 𝓕))                                      ■

  where
   i  = characterization-of-＝ (ua 𝓤) sns-data 𝓧 𝓐
   ii = Σ-cong (λ F → Σ-cong (λ _ → lemma 𝓧 𝓐 F))

module type-valued-preorder-with-axioms
        (𝓤 𝓥 𝓦 : Universe)
        (ua : Univalence)
        (axioms  : (X : 𝓤 ̇ ) → type-valued-preorder-S {𝓤} {𝓥} X → 𝓦 ̇ )
        (axiomss : (X : 𝓤 ̇ )
                   (s : type-valued-preorder-S X)
                 → is-prop (axioms X s))
       where

 open sip
 open sip-with-axioms
 open type-valued-preorder 𝓤 𝓥 ua

 S' : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦 ̇
 S' X = Σ s ꞉ S X , axioms X s

 sns-data' : SNS S' (𝓤 ⊔ (𝓥 ⁺))
 sns-data' = add-axioms axioms axiomss sns-data

 characterization-of-type-valued-preorder-＝-with-axioms
  : (𝓧' 𝓐' : Σ S')
  →
    (𝓧' ＝ 𝓐')
  ≃
    (Σ F ꞉ (Ob [ 𝓧' ] → Ob [ 𝓐' ])
         , is-equiv F
         × (Σ 𝓕 ꞉ ((x y : Ob [ 𝓧' ]) → hom [ 𝓧' ] x y → hom [ 𝓐' ] (F x) (F y))
                , (∀ x y → is-equiv (𝓕 x y))
                × functorial [ 𝓧' ] [ 𝓐' ] F 𝓕))
 characterization-of-type-valued-preorder-＝-with-axioms 𝓧' 𝓐' =
  (𝓧' ＝ 𝓐')                     ≃⟨ i ⟩
  ([ 𝓧' ] ≃[ sns-data ] [ 𝓐' ]) ≃⟨ ii ⟩
  _                              ■
  where
   i  = characterization-of-＝-with-axioms (ua 𝓤) sns-data axioms axiomss 𝓧' 𝓐'
   ii = Σ-cong (λ F → Σ-cong (λ _ → lemma [ 𝓧' ] [ 𝓐' ] F))

module category
        (𝓤 𝓥 : Universe)
        (ua : Univalence)
       where

 open type-valued-preorder-with-axioms 𝓤 𝓥 (𝓤 ⊔ 𝓥) ua

 fe : Fun-Ext
 fe {𝓤} {𝓥} = Univalence-gives-FunExt ua 𝓤 𝓥

 S : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ̇
 S = type-valued-preorder-S {𝓤} {𝓥}

 category-axioms : (X : 𝓤 ̇ ) → S X → 𝓤 ⊔ 𝓥 ̇
 category-axioms X (homX , idX , compX) =
  hom-sets × identityl × identityr × associativity
  where
   _o_ : {x y z : X} → homX y z → homX x y → homX x z
   g o f = compX _ _ _ f g

   hom-sets      = ∀ x y → is-set (homX x y)

   identityl     = ∀ x y (f : homX x y) → f o (idX x) ＝ f

   identityr     = ∀ x y (f : homX x y) → (idX y) o f ＝ f

   associativity = ∀ x y z t (f : homX x y) (g : homX y z) (h : homX z t)
                 → (h o g) o f ＝ h o (g o f)

 category-axioms-prop : (X : 𝓤 ̇ ) (s : S X) → is-prop (category-axioms X s)
 category-axioms-prop X (homX , idX , compX) ca = γ ca
  where
   i : ∀ x y → is-set (homX x y)
   i = pr₁ ca

   γ : is-prop (category-axioms X (homX , idX , compX))
   γ = ×₄-is-prop
        (Π₂-is-prop fe (λ x y → being-set-is-prop fe))
        (Π₃-is-prop fe (λ x y f → i x y))
        (Π₃-is-prop fe (λ x y f → i x y))
        (Π₇-is-prop fe (λ x y z t f g h → i x t))

 Cat : (𝓤 ⊔ 𝓥)⁺ ̇
 Cat = Σ X ꞉ 𝓤 ̇ , Σ s ꞉ S X , category-axioms X s

 Ob : Cat → 𝓤 ̇
 Ob (X , (homX , idX , compX) , _) = X

 hom : (𝓧 : Cat) → Ob 𝓧 → Ob 𝓧 → 𝓥 ̇
 hom (X , (homX , idX , compX) , _) = homX

 𝒾𝒹 : (𝓧 : Cat) (x : Ob 𝓧) → hom 𝓧 x x
 𝒾𝒹 (X , (homX , idX , compX) , _) = idX

 comp : (𝓧 : Cat) (x y z : Ob 𝓧) (f : hom 𝓧 x y) (g : hom 𝓧 y z) → hom 𝓧 x z
 comp (X , (homX , idX , compX) , _) = compX

 is-functorial : (𝓧 𝓐 : Cat)
               → (F : Ob 𝓧 → Ob 𝓐)
               → ((x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
               → 𝓤 ⊔ 𝓥 ̇

 is-functorial 𝓧 𝓐 F 𝓕' = pidentity × pcomposition
  where
   _o_ : {x y z : Ob 𝓧} → hom 𝓧 y z → hom 𝓧 x y → hom 𝓧 x z
   g o f = comp 𝓧 _ _ _ f g

   _□_ : {a b c : Ob 𝓐} → hom 𝓐 b c → hom 𝓐 a b → hom 𝓐 a c
   g □ f = comp 𝓐 _ _ _ f g

   𝓕 : {x y : Ob 𝓧} → hom 𝓧 x y → hom 𝓐 (F x) (F y)
   𝓕 f = 𝓕' _ _ f

   pidentity = (λ x → 𝓕 (𝒾𝒹 𝓧 x)) ＝[ ((x : Ob 𝓧) → hom 𝓐 (F x) (F x)) ]
               (λ x → 𝒾𝒹 𝓐 (F x))

   pcomposition =
    (λ x y z (f : hom 𝓧 x y) (g : hom 𝓧 y z) → 𝓕 (g o f))
    ＝[ ((x y z : Ob 𝓧) (f : hom 𝓧 x y) (g : hom 𝓧 y z) → hom 𝓐 (F x) (F z)) ]
    (λ x y z (f : hom 𝓧 x y) (g : hom 𝓧 y z) → 𝓕 g □ 𝓕 f)

 _⋍_ : Cat → Cat → 𝓤 ⊔ 𝓥 ̇

 𝓧 ⋍ 𝓐 = Σ F ꞉ (Ob 𝓧 → Ob 𝓐)
              , is-equiv F
              × (Σ 𝓕 ꞉ ((x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
                     , (∀ x y → is-equiv (𝓕 x y))
                     × is-functorial 𝓧 𝓐 F 𝓕)

 idtoeqCat : (𝓧 𝓐 : Cat) → 𝓧 ＝ 𝓐 → 𝓧 ⋍ 𝓐
 idtoeqCat 𝓧 𝓧 (refl {𝓧}) = -id (Ob 𝓧) ,
                              id-is-equiv (Ob 𝓧) ,
                              (λ x y → -id (hom 𝓧 x y)) ,
                              (λ x y → id-is-equiv (hom 𝓧 x y)) ,
                              𝓻𝓮𝒻𝓵 (𝒾𝒹 𝓧) ,
                              𝓻𝓮𝒻𝓵 (comp 𝓧)

 characterization-of-category-＝ : (𝓧 𝓐 : Cat) → (𝓧 ＝ 𝓐) ≃ (𝓧 ⋍ 𝓐)
 characterization-of-category-＝ =
  characterization-of-type-valued-preorder-＝-with-axioms
   category-axioms
   category-axioms-prop

 idtoeqCat-is-equiv : (𝓧 𝓐 : Cat) → is-equiv (idtoeqCat 𝓧 𝓐)
 idtoeqCat-is-equiv 𝓧 𝓐 = equiv-closed-under-∼ _ _
                           (⌜⌝-is-equiv (characterization-of-category-＝ 𝓧 𝓐))
                           (γ 𝓧 𝓐)
  where
   γ : (𝓧 𝓐 : Cat) → idtoeqCat 𝓧 𝓐 ∼ ⌜ characterization-of-category-＝ 𝓧 𝓐 ⌝
   γ 𝓧 𝓧 (refl {𝓧}) = 𝓻𝓮𝒻𝓵 (idtoeqCat 𝓧 𝓧 (𝓻𝓮𝒻𝓵 𝓧))

\end{code}

We now consider ∞-magmas with the binary operation generalized to an
operation of arbitrary arity. This is used to define σ-frames.

\begin{code}

module ∞-bigmagma {𝓤 𝓥 : Universe} (I : 𝓥 ̇ ) where

 open sip

 ∞-bigmagma-structure : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 ∞-bigmagma-structure A = (I → A) → A

 ∞-Bigmagma : 𝓤 ⁺ ⊔ 𝓥 ̇
 ∞-Bigmagma = Σ A ꞉ 𝓤 ̇ , ∞-bigmagma-structure A

 sns-data : SNS ∞-bigmagma-structure (𝓤 ⊔ 𝓥)
 sns-data = (ι , ρ , θ)
  where
   ι : (𝓐 𝓐' : ∞-Bigmagma) → ⟨ 𝓐 ⟩ ≃ ⟨ 𝓐' ⟩ → 𝓤 ⊔ 𝓥 ̇
   ι (A , sup) (A' , sup') (f , _) =
    (λ 𝕒 → f (sup 𝕒)) ＝[ ((I → A) → A') ] (λ 𝕒 → sup' (n ↦ f (𝕒 n)))

   ρ : (𝓐 : ∞-Bigmagma) → ι 𝓐 𝓐 (≃-refl ⟨ 𝓐 ⟩)
   ρ (A , sup) = 𝓻𝓮𝒻𝓵 sup

   h : {A : 𝓤 ̇ } {sup sup' : ∞-bigmagma-structure A}
     → canonical-map ι ρ sup sup' ∼ -id (sup ＝ sup')

   h (refl {sup}) = 𝓻𝓮𝒻𝓵 (𝓻𝓮𝒻𝓵 sup)

   θ : {A : 𝓤 ̇ } (sup sup' : ∞-bigmagma-structure A)
     → is-equiv (canonical-map ι ρ sup sup')

   θ sup sup' = equiv-closed-under-∼ _ _ (id-is-equiv (sup ＝ sup')) h

 _≅[∞-Bigmagma]_ : ∞-Bigmagma → ∞-Bigmagma → 𝓤 ⊔ 𝓥 ̇
 (A , sup) ≅[∞-Bigmagma] (A' , sup') =

           Σ f ꞉ (A → A'), is-equiv f
                         × ((λ 𝕒 → f (sup 𝕒)) ＝[ ((I → A) → A') ]
                            (λ 𝕒 → sup' (n ↦ f (𝕒 n))))

 characterization-of-∞-Bigmagma-＝ : is-univalent 𝓤
                                  → (A B : ∞-Bigmagma)
                                  → (A ＝ B) ≃ (A ≅[∞-Bigmagma] B)
 characterization-of-∞-Bigmagma-＝ ua = characterization-of-＝ ua sns-data

\end{code}

We use the above in another module to define σ-frames.

We now consider ∞-bigmagmas with all operations of all arities, which
we use in another module to define frames.

\begin{code}

module ∞-hugemagma {𝓤 𝓥 : Universe} where

 open sip

 ∞-hugemagma-structure : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ̇
 ∞-hugemagma-structure A = {N : 𝓥 ̇ } → (N → A) → A

 ∞-Hugemagma : (𝓤 ⊔ 𝓥)⁺ ̇
 ∞-Hugemagma = Σ A ꞉ 𝓤 ̇ , ∞-hugemagma-structure A

 sns-data : SNS ∞-hugemagma-structure (𝓤 ⊔ (𝓥 ⁺))
 sns-data = (ι , ρ , θ)
  where
   ι : (𝓐 𝓐' : ∞-Hugemagma) → ⟨ 𝓐 ⟩ ≃ ⟨ 𝓐' ⟩ → 𝓤 ⊔ (𝓥 ⁺) ̇
   ι (A , sup) (A' , sup') (f , _) =
    (λ {N} (𝕒 : N → A) → f (sup 𝕒)) ＝ (λ {N} 𝕒 → sup' (i ↦ f (𝕒 i)))

   ρ : (𝓐 : ∞-Hugemagma) → ι 𝓐 𝓐 (≃-refl ⟨ 𝓐 ⟩)
   ρ (A , sup) = refl

   h : {A : 𝓤 ̇ } {sup sup' : ∞-hugemagma-structure A}
     → canonical-map ι ρ sup sup' ∼ id

   h refl = refl

   θ : {A : 𝓤 ̇ } (sup sup' : ∞-hugemagma-structure A)
     → is-equiv (canonical-map ι ρ sup sup')

   θ sup sup' = equiv-closed-under-∼ _ _ (id-is-equiv _) h

 _≅[∞-Hugemagma]_ : ∞-Hugemagma → ∞-Hugemagma → 𝓤 ⊔ (𝓥 ⁺) ̇
 (A , sup) ≅[∞-Hugemagma] (A' , sup') =
   Σ f ꞉ (A → A'), is-equiv f
                 × ((λ {N} (𝕒 : N → A) → f (sup 𝕒))
                 ＝ (λ {N} (𝕒 : N → A) → sup' (i ↦ f (𝕒 i))))

 characterization-of-∞-Hugemagma-＝ : is-univalent 𝓤
                                   → (A B : ∞-Hugemagma)
                                   → (A ＝ B) ≃ (A ≅[∞-Hugemagma] B)
 characterization-of-∞-Hugemagma-＝ ua = characterization-of-＝ ua sns-data

\end{code}
