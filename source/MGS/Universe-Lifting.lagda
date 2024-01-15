Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF.in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF.Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MGS.Universe-Lifting where

open import MGS.Equivalence-Constructions
open import MGS.Embeddings public

record Lift {𝓤 : Universe} (𝓥 : Universe) (X : 𝓤 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
 constructor
  lift
 field
  lower : X

open Lift public

type-of-Lift  :             type-of (Lift  {𝓤} 𝓥)       ＝ (𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇ )
type-of-lift  : {X : 𝓤 ̇ } → type-of (lift  {𝓤} {𝓥} {X}) ＝ (X → Lift 𝓥 X)
type-of-lower : {X : 𝓤 ̇ } → type-of (lower {𝓤} {𝓥} {X}) ＝ (Lift 𝓥 X → X)

type-of-Lift  = refl _
type-of-lift  = refl _
type-of-lower = refl _

Lift-induction : ∀ {𝓤} 𝓥 (X : 𝓤 ̇ ) (A : Lift 𝓥 X → 𝓦 ̇ )
               → ((x : X) → A (lift x))
               → (l : Lift 𝓥 X) → A l

Lift-induction 𝓥 X A φ (lift x) = φ x

Lift-recursion : ∀ {𝓤} 𝓥 {X : 𝓤 ̇ } {B : 𝓦 ̇ }
               → (X → B) → Lift 𝓥 X → B

Lift-recursion 𝓥 {X} {B} = Lift-induction 𝓥 X (λ _ → B)

lower-lift : {X : 𝓤 ̇ } (x : X) → lower {𝓤} {𝓥} (lift x) ＝ x
lower-lift = refl

lift-lower : {X : 𝓤 ̇ } (l : Lift 𝓥 X) → lift (lower l) ＝ l
lift-lower = refl

Lift-≃ : (X : 𝓤 ̇ ) → Lift 𝓥 X ≃ X
Lift-≃ {𝓤} {𝓥} X = invertibility-gives-≃ lower
                     (lift , lift-lower , lower-lift {𝓤} {𝓥})

≃-Lift : (X : 𝓤 ̇ ) → X ≃ Lift 𝓥 X
≃-Lift {𝓤} {𝓥} X = invertibility-gives-≃ lift
                     (lower , lower-lift {𝓤} {𝓥} , lift-lower)

lower-dfunext : ∀ 𝓦 𝓣 𝓤 𝓥 → dfunext (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓣) → dfunext 𝓤 𝓥
lower-dfunext 𝓦 𝓣 𝓤 𝓥 fe {X} {A} {f} {g} h = p
 where
  A' : Lift 𝓦 X → 𝓥 ⊔ 𝓣 ̇
  A' y = Lift 𝓣 (A (lower y))

  f' g' : Π A'
  f' y = lift (f (lower y))
  g' y = lift (g (lower y))

  h' : f' ∼ g'
  h' y = ap lift (h (lower y))

  p' : f' ＝ g'
  p' = fe h'

  p : f ＝ g
  p = ap (λ f' x → lower (f' (lift x))) p'

universe-embedding-criterion : is-univalent 𝓤
                             → is-univalent (𝓤 ⊔ 𝓥)
                             → (f : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇ )
                             → ((X : 𝓤 ̇ ) → f X ≃ X)
                             → is-embedding f

universe-embedding-criterion {𝓤} {𝓥} ua ua' f e = embedding-criterion f γ
 where
  fe : dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
  fe = univalence-gives-dfunext ua'

  fe₀ : dfunext 𝓤 𝓤
  fe₀ = lower-dfunext 𝓥 𝓥 𝓤 𝓤 fe

  fe₁ : dfunext 𝓤 (𝓤 ⊔ 𝓥)
  fe₁ = lower-dfunext 𝓥 𝓥 𝓤 (𝓤 ⊔ 𝓥) fe

  γ : (X X' : 𝓤 ̇ ) → (f X ＝ f X') ≃ (X ＝ X')
  γ X X' =  (f X ＝ f X')  ≃⟨ i ⟩
            (f X ≃ f X')  ≃⟨ ii ⟩
            (X ≃ X')      ≃⟨ iii ⟩
            (X ＝ X')      ■
   where
    i   = univalence-≃ ua' (f X) (f X')
    ii  = Eq-Eq-cong' fe fe fe fe fe fe₀ fe₁ fe fe₀ fe₀ fe₀ fe₀ (e X) (e X')
    iii = ≃-sym (univalence-≃ ua X X')

Lift-is-embedding : is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥)
                  → is-embedding (Lift {𝓤} 𝓥)

Lift-is-embedding {𝓤} {𝓥} ua ua' = universe-embedding-criterion {𝓤} {𝓥} ua ua'
                                    (Lift 𝓥) Lift-≃

module _ {𝓤 𝓥 : Universe}
         (ua : is-univalent 𝓥)
         (ua' : is-univalent (𝓤 ⊔ 𝓥))
 where

 private
  fe : dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
  fe = univalence-gives-dfunext ua'

  fe₀ : dfunext 𝓥 (𝓤 ⊔ 𝓥)
  fe₀ = lower-dfunext 𝓤 𝓤 𝓥 (𝓤 ⊔ 𝓥) fe

  fe₁ : dfunext 𝓤 (𝓤 ⊔ 𝓥)
  fe₁ = lower-dfunext (𝓤 ⊔ 𝓥) 𝓤 𝓤 (𝓤 ⊔ 𝓥) fe

  fe₂ : dfunext 𝓥 𝓥
  fe₂ = lower-dfunext 𝓤 𝓤 𝓥 𝓥 fe

  fe₃ : dfunext 𝓤 𝓤
  fe₃ = lower-dfunext 𝓥 𝓥 𝓤 𝓤 fe

 univalence→' : (X : 𝓤 ̇ ) → is-subsingleton (Σ Y ꞉ 𝓥 ̇ , X ≃ Y)
 univalence→' X = s
  where
   e : (Y : 𝓥 ̇ ) → (X ≃ Y) ≃ (Lift 𝓤 Y ＝ Lift 𝓥 X)
   e Y = (X ≃ Y)                 ≃⟨ i ⟩
         (Y ≃ X)                 ≃⟨ ii ⟩
         (Lift 𝓤 Y ≃ Lift 𝓥 X)   ≃⟨ iii ⟩
         (Lift 𝓤 Y ＝ Lift 𝓥 X)   ■
    where
     i   = ≃-Sym fe₀ fe₁ fe
     ii  = Eq-Eq-cong' fe₁ fe fe₂ fe₁ fe fe fe fe₃
             fe fe fe fe (≃-Lift Y) (≃-Lift X)
     iii = ≃-sym (univalence-≃ ua' (Lift 𝓤 Y) (Lift 𝓥 X))

   d : (Σ Y ꞉ 𝓥 ̇ , X ≃ Y) ≃ (Σ Y ꞉ 𝓥 ̇ , Lift 𝓤 Y ＝ Lift 𝓥 X)
   d = Σ-cong e

   j : is-subsingleton (Σ Y ꞉ 𝓥 ̇ , Lift 𝓤 Y ＝ Lift 𝓥 X)
   j = Lift-is-embedding ua ua' (Lift 𝓥 X)

   abstract
    s : is-subsingleton (Σ Y ꞉ 𝓥 ̇ , X ≃ Y)
    s = equiv-to-subsingleton d j

 univalence→'-dual : (Y : 𝓤 ̇ ) → is-subsingleton (Σ X ꞉ 𝓥 ̇ , X ≃ Y)
 univalence→'-dual Y = equiv-to-subsingleton e i
  where
   e : (Σ X ꞉ 𝓥 ̇ , X ≃ Y) ≃ (Σ X ꞉ 𝓥 ̇ , Y ≃ X)
   e = Σ-cong (λ X → ≃-Sym fe₁ fe₀ fe)

   i : is-subsingleton (Σ X ꞉ 𝓥 ̇ , Y ≃ X)
   i = univalence→' Y

univalence→'' : is-univalent (𝓤 ⊔ 𝓥)
              → (X : 𝓤 ̇ ) → is-subsingleton (Σ Y ꞉ 𝓤 ⊔ 𝓥 ̇ , X ≃ Y)

univalence→'' ua = univalence→' ua ua

univalence→''-dual : is-univalent (𝓤 ⊔ 𝓥)
                   → (Y : 𝓤 ̇ ) → is-subsingleton (Σ X ꞉ 𝓤 ⊔ 𝓥 ̇ , X ≃ Y)

univalence→''-dual ua = univalence→'-dual ua ua

G↑-≃ : is-univalent (𝓤 ⊔ 𝓥)
     → (X : 𝓤 ̇ ) (A : (Σ Y ꞉ 𝓤 ⊔ 𝓥 ̇ , X ≃ Y) → 𝓦 ̇ )
     → A (Lift 𝓥 X , ≃-Lift X) → (Y : 𝓤 ⊔ 𝓥 ̇ ) (e : X ≃ Y) → A (Y , e)

G↑-≃ {𝓤} {𝓥} ua X A a Y e = transport A p a
 where
  t : Σ Y ꞉ 𝓤 ⊔ 𝓥 ̇ , X ≃ Y
  t = (Lift 𝓥 X , ≃-Lift X)

  p : t ＝ (Y , e)
  p = univalence→'' {𝓤} {𝓥} ua X t (Y , e)

H↑-≃ : is-univalent (𝓤 ⊔ 𝓥)
     → (X : 𝓤 ̇ ) (A : (Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y → 𝓦 ̇ )
     → A (Lift 𝓥 X) (≃-Lift X) → (Y : 𝓤 ⊔ 𝓥 ̇ ) (e : X ≃ Y) → A Y e

H↑-≃ ua X A = G↑-≃ ua X (Σ-induction A)

J↑-≃ : is-univalent (𝓤 ⊔ 𝓥)
     → (A : (X : 𝓤 ̇ ) (Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y → 𝓦 ̇ )
     → ((X : 𝓤 ̇ ) → A X (Lift 𝓥 X) (≃-Lift X))
     → (X : 𝓤 ̇ ) (Y : 𝓤 ⊔ 𝓥 ̇ ) (e : X ≃ Y) → A X Y e

J↑-≃ ua A φ X = H↑-≃ ua X (A X) (φ X)

H↑-equiv : is-univalent (𝓤 ⊔ 𝓥)
         → (X : 𝓤 ̇ ) (A : (Y : 𝓤 ⊔ 𝓥 ̇ ) → (X → Y) → 𝓦 ̇ )
         → A (Lift 𝓥 X) lift → (Y : 𝓤 ⊔ 𝓥 ̇ ) (f : X → Y) → is-equiv f → A Y f

H↑-equiv {𝓤} {𝓥} {𝓦} ua X A a Y f i = γ (f , i)
 where
  B : (Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y → 𝓦 ̇
  B Y (f , i) = A Y f

  b : B (Lift 𝓥 X) (≃-Lift X)
  b = a

  γ : (e : X ≃ Y) → B Y e
  γ = H↑-≃ ua X B b Y

J↑-equiv : is-univalent (𝓤 ⊔ 𝓥)
         → (A : (X : 𝓤 ̇ ) (Y : 𝓤 ⊔ 𝓥 ̇ ) → (X → Y) → 𝓦 ̇ )
         → ((X : 𝓤 ̇ ) → A X (Lift 𝓥 X) lift)
         → (X : 𝓤 ̇ ) (Y : 𝓤 ⊔ 𝓥 ̇ ) (f : X → Y) → is-equiv f → A X Y f

J↑-equiv ua A φ X = H↑-equiv ua X (A X) (φ X)

J↑-invertible : is-univalent (𝓤 ⊔ 𝓥)
              → (A : (X : 𝓤 ̇ ) (Y : 𝓤 ⊔ 𝓥 ̇ ) → (X → Y) → 𝓦 ̇ )
              → ((X : 𝓤 ̇ ) → A X (Lift 𝓥 X) lift)
              → (X : 𝓤 ̇ ) (Y : 𝓤 ⊔ 𝓥 ̇ ) (f : X → Y) → invertible f → A X Y f

J↑-invertible ua A φ X Y f i = J↑-equiv ua A φ X Y f (invertibles-are-equivs f i)

lift-is-hae : (X : 𝓤 ̇ ) → is-hae {𝓤} {𝓤 ⊔ 𝓥} {X} {Lift 𝓥 X} (lift {𝓤} {𝓥})
lift-is-hae {𝓤} {𝓥} X = lower ,
                        lower-lift {𝓤} {𝓥} ,
                        lift-lower ,
                        λ x → refl (refl (lift x))

equivs-are-haes↑ : is-univalent (𝓤 ⊔ 𝓥)
                 → {X : 𝓤 ̇ } {Y : 𝓤 ⊔ 𝓥 ̇ } (f : X → Y)
                 → is-equiv f → is-hae f

equivs-are-haes↑ {𝓤} {𝓥} ua {X} {Y} = J↑-equiv {𝓤} {𝓥} ua (λ X Y f → is-hae f)
                                       lift-is-hae X Y

G↓-≃ : is-univalent (𝓤 ⊔ 𝓥)
     → (Y : 𝓤 ̇ ) (A : (Σ X ꞉ 𝓤 ⊔ 𝓥 ̇ , X ≃ Y) → 𝓦 ̇ )
     → A (Lift 𝓥 Y , Lift-≃ Y) → (X : 𝓤 ⊔ 𝓥 ̇ ) (e : X ≃ Y) → A (X , e)

G↓-≃ {𝓤} {𝓥} ua Y A a X e = transport A p a
 where
  t : Σ X ꞉ 𝓤 ⊔ 𝓥 ̇ , X ≃ Y
  t = (Lift 𝓥 Y , Lift-≃ Y)

  p : t ＝ (X , e)
  p = univalence→'-dual {𝓤} {𝓤 ⊔ 𝓥} ua ua Y t (X , e)

H↓-≃ : is-univalent (𝓤 ⊔ 𝓥)
     → (Y : 𝓤 ̇ ) (A : (X : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y → 𝓦 ̇ )
     → A (Lift 𝓥 Y) (Lift-≃ Y) → (X : 𝓤 ⊔ 𝓥 ̇ ) (e : X ≃ Y) → A X e

H↓-≃ ua Y A = G↓-≃ ua Y (Σ-induction A)

J↓-≃ : is-univalent (𝓤 ⊔ 𝓥)
     → (A : (X : 𝓤 ⊔ 𝓥 ̇ ) (Y : 𝓤 ̇ ) → X ≃ Y → 𝓦 ̇ )
     → ((Y : 𝓤 ̇ ) → A (Lift 𝓥 Y) Y (Lift-≃ Y))
     → (X : 𝓤 ⊔ 𝓥 ̇ ) (Y : 𝓤 ̇ ) (e : X ≃ Y) → A X Y e

J↓-≃ ua A φ X Y = H↓-≃ ua Y (λ X → A X Y) (φ Y) X

H↓-equiv : is-univalent (𝓤 ⊔ 𝓥)
         → (Y : 𝓤 ̇ ) (A : (X : 𝓤 ⊔ 𝓥 ̇ ) → (X → Y) → 𝓦 ̇ )
         → A (Lift 𝓥 Y) lower → (X : 𝓤 ⊔ 𝓥 ̇ ) (f : X → Y) → is-equiv f → A X f

H↓-equiv {𝓤} {𝓥} {𝓦} ua Y A a X f i = γ (f , i)
 where
  B : (X : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y → 𝓦 ̇
  B X (f , i) = A X f

  b : B (Lift 𝓥 Y) (Lift-≃ Y)
  b = a

  γ : (e : X ≃ Y) → B X e
  γ = H↓-≃ ua Y B b X

J↓-equiv : is-univalent (𝓤 ⊔ 𝓥)
         → (A : (X : 𝓤 ⊔ 𝓥 ̇ ) (Y : 𝓤 ̇ ) → (X → Y) → 𝓦 ̇ )
         → ((Y : 𝓤 ̇ ) → A (Lift 𝓥 Y) Y lower)
         → (X : 𝓤 ⊔ 𝓥 ̇ ) (Y : 𝓤 ̇ ) (f : X → Y) → is-equiv f → A X Y f

J↓-equiv ua A φ X Y = H↓-equiv ua Y (λ X → A X Y) (φ Y) X

J↓-invertible : is-univalent (𝓤 ⊔ 𝓥)
              → (A : (X : 𝓤 ⊔ 𝓥 ̇ ) (Y : 𝓤 ̇ ) → (X → Y) → 𝓦 ̇ )
              → ((Y : 𝓤 ̇ ) → A (Lift 𝓥 Y) Y lower)
              → (X : 𝓤 ⊔ 𝓥 ̇ ) (Y : 𝓤 ̇ ) (f : X → Y) → invertible f → A X Y f

J↓-invertible ua A φ X Y f i = J↓-equiv ua A φ X Y f (invertibles-are-equivs f i)

lower-is-hae : (X : 𝓤 ̇ ) → is-hae (lower {𝓤} {𝓥} {X})
lower-is-hae {𝓤} {𝓥} X = lift ,
                         lift-lower ,
                         lower-lift {𝓤} {𝓥} ,
                         (λ x → refl (refl (lower x)))

equivs-are-haes↓ : is-univalent (𝓤 ⊔ 𝓥)
                 → {X : 𝓤 ⊔ 𝓥 ̇ } {Y : 𝓤 ̇ } (f : X → Y)
                 → is-equiv f → is-hae f

equivs-are-haes↓ {𝓤} {𝓥} ua {X} {Y} = J↓-equiv {𝓤} {𝓥} ua (λ X Y f → is-hae f)
                                       lower-is-hae X Y

Id→Eq-is-hae' : is-univalent 𝓤 → is-univalent (𝓤 ⁺)
              → {X Y : 𝓤 ̇ } → is-hae (Id→Eq X Y)

Id→Eq-is-hae' ua ua⁺ {X} {Y} = equivs-are-haes↓ ua⁺ (Id→Eq X Y) (ua X Y)

Id→Eq-is-hae : is-univalent 𝓤
             → {X Y : 𝓤 ̇ } → is-hae (Id→Eq X Y)

Id→Eq-is-hae ua {X} {Y} = invertibles-are-haes (Id→Eq X Y)
                           (equivs-are-invertible (Id→Eq X Y) (ua X Y))

global-property-of-types : 𝓤ω
global-property-of-types = {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇

cumulative : global-property-of-types → 𝓤ω
cumulative A = {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) → A X ≃ A (Lift 𝓥 X)

global-≃-ap : Univalence
            → (A : global-property-of-types)
            → cumulative A
            → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → X ≃ Y → A X ≃ A Y

global-≃-ap' : Univalence
             → (F : Universe → Universe)
             → (A : {𝓤 : Universe} → 𝓤 ̇ → (F 𝓤) ̇ )
             → ({𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) → A X ≃ A (Lift 𝓥 X))
             → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → X ≃ Y → A X ≃ A Y

global-≃-ap' {𝓤} {𝓥} ua F A φ X Y e =

  A X          ≃⟨ φ X ⟩
  A (Lift 𝓥 X) ≃⟨ Id→Eq (A (Lift 𝓥 X)) (A (Lift 𝓤 Y)) q ⟩
  A (Lift 𝓤 Y) ≃⟨ ≃-sym (φ Y) ⟩
  A Y          ■
 where
  d : Lift 𝓥 X ≃ Lift 𝓤 Y
  d = Lift 𝓥 X ≃⟨ Lift-≃ X ⟩
      X        ≃⟨ e ⟩
      Y        ≃⟨ ≃-sym (Lift-≃ Y) ⟩
      Lift 𝓤 Y ■

  p : Lift 𝓥 X ＝ Lift 𝓤 Y
  p = Eq→Id (ua (𝓤 ⊔ 𝓥)) (Lift 𝓥 X) (Lift 𝓤 Y) d

  q : A (Lift 𝓥 X) ＝ A (Lift 𝓤 Y)
  q = ap A p

global-≃-ap ua = global-≃-ap' ua (λ 𝓤 → 𝓤)

\end{code}
