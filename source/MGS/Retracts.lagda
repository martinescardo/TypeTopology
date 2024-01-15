Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF.in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF.Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MGS.Retracts where

open import MGS.hlevels public

has-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
has-section r = Σ s ꞉ (codomain r → domain r), r ∘ s ∼ id

_◁_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ◁ Y = Σ r ꞉ (Y → X), has-section r

retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ◁ Y → Y → X
retraction (r , s , η) = r

section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ◁ Y → X → Y
section (r , s , η) = s

retract-equation : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (ρ : X ◁ Y)
                 → retraction ρ ∘ section ρ ∼ 𝑖𝑑 X

retract-equation (r , s , η) = η

retraction-has-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (ρ : X ◁ Y)
                       → has-section (retraction ρ)

retraction-has-section (r , h) = h

id-◁ : (X : 𝓤 ̇ ) → X ◁ X
id-◁ X = 𝑖𝑑 X , 𝑖𝑑 X , refl

_◁∘_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ◁ Y → Y ◁ Z → X ◁ Z

(r , s , η) ◁∘ (r' , s' , η') = (r ∘ r' , s' ∘ s , η'')
 where
  η'' = λ x → r (r' (s' (s x))) ＝⟨ ap r (η' (s x)) ⟩
              r (s x)           ＝⟨ η x ⟩
              x                 ∎

_◁⟨_⟩_ : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ◁ Y → Y ◁ Z → X ◁ Z
X ◁⟨ ρ ⟩ σ = ρ ◁∘ σ

_◀ : (X : 𝓤 ̇ ) → X ◁ X
X ◀ = id-◁ X

Σ-retract : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
          → ((x : X) → A x ◁  B x) → Σ A ◁ Σ B

Σ-retract {𝓤} {𝓥} {𝓦} {X} {A} {B} ρ = NatΣ r , NatΣ s , η'
 where
  r : (x : X) → B x → A x
  r x = retraction (ρ x)

  s : (x : X) → A x → B x
  s x = section (ρ x)

  η : (x : X) (a : A x) → r x (s x a) ＝ a
  η x = retract-equation (ρ x)

  η' : (σ : Σ A) → NatΣ r (NatΣ s σ) ＝ σ
  η' (x , a) = x , r x (s x a) ＝⟨ to-Σ-＝' (η x a) ⟩
               x , a           ∎

transport-is-retraction : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ＝ y)
                        → transport A p ∘ transport A (p ⁻¹) ∼ 𝑖𝑑 (A y)

transport-is-retraction A (refl x) = refl

transport-is-section : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ＝ y)
                     → transport A (p ⁻¹) ∘ transport A p ∼ 𝑖𝑑 (A x)

transport-is-section A (refl x) = refl

Σ-reindexing-retract : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : X → 𝓦 ̇ } (r : Y → X)
                     → has-section r
                     → (Σ x ꞉ X , A x) ◁ (Σ y ꞉ Y , A (r y))

Σ-reindexing-retract {𝓤} {𝓥} {𝓦} {X} {Y} {A} r (s , η) = γ , φ , γφ
 where
  γ : Σ (A ∘ r) → Σ A
  γ (y , a) = (r y , a)

  φ : Σ A → Σ (A ∘ r)
  φ (x , a) = (s x , transport A ((η x)⁻¹) a)

  γφ : (σ : Σ A) → γ (φ σ) ＝ σ
  γφ (x , a) = p
   where
    p : (r (s x) , transport A ((η x)⁻¹) a) ＝ (x , a)
    p = to-Σ-＝ (η x , transport-is-retraction A (η x) a)

singleton-type : {X : 𝓤 ̇ } → X → 𝓤 ̇
singleton-type {𝓤} {X} x = Σ y ꞉ X , y ＝ x

singleton-type-center : {X : 𝓤 ̇ } (x : X) → singleton-type x
singleton-type-center x = (x , refl x)

singleton-type-centered : {X : 𝓤 ̇ } (x : X) (σ : singleton-type x)
                        → singleton-type-center x ＝ σ

singleton-type-centered x (x , refl x) = refl (x , refl x)

singleton-types-are-singletons : (X : 𝓤 ̇ ) (x : X)
                               → is-singleton (singleton-type x)

singleton-types-are-singletons X x = singleton-type-center x ,
                                     singleton-type-centered x

retract-of-singleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                     → Y ◁ X → is-singleton X → is-singleton Y

retract-of-singleton (r , s , η) (c , φ) = r c , γ
 where
  γ = λ y → r c     ＝⟨ ap r (φ (s y)) ⟩
            r (s y) ＝⟨ η y ⟩
            y       ∎

singleton-type' : {X : 𝓤 ̇ } → X → 𝓤 ̇
singleton-type' {𝓤} {X} x = Σ y ꞉ X , x ＝ y

singleton-type'-center : {X : 𝓤 ̇ } (x : X) → singleton-type' x
singleton-type'-center x = (x , refl x)

singleton-type'-centered : {X : 𝓤 ̇ } (x : X) (σ : singleton-type' x)
                         → singleton-type'-center x ＝ σ

singleton-type'-centered x (x , refl x) = refl (x , refl x)

singleton-types'-are-singletons : (X : 𝓤 ̇ ) (x : X)
                                → is-singleton (singleton-type' x)

singleton-types'-are-singletons X x = singleton-type'-center x ,
                                      singleton-type'-centered x

infix  10 _◁_
infixr  0 _◁⟨_⟩_
infix   1 _◀

\end{code}
