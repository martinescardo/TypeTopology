This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module MGS-Subsingleton-Truncation where

open import MGS-Powerset public
open import MGS-Embeddings public

is-inhabited : 𝓤 ̇ → 𝓤 ⁺ ̇
is-inhabited {𝓤} X = (P : 𝓤 ̇ ) → is-subsingleton P → (X → P) → P

inhabitation-is-subsingleton : global-dfunext → (X : 𝓤 ̇ )
                             → is-subsingleton (is-inhabited X)

inhabitation-is-subsingleton fe X =
 Π-is-subsingleton fe
   (λ P → Π-is-subsingleton fe
   (λ (s : is-subsingleton P) → Π-is-subsingleton fe
   (λ (f : X → P) → s)))

inhabited-intro : {X : 𝓤 ̇ } → X → is-inhabited X
inhabited-intro x = λ P s f → f x

inhabited-recursion : {X P : 𝓤 ̇ } → is-subsingleton P → (X → P) → is-inhabited X → P
inhabited-recursion s f φ = φ (codomain f) s f

inhabited-recursion-computation : {X P : 𝓤 ̇ }
                                  (i : is-subsingleton P)
                                  (f : X → P)
                                  (x : X)
                                → inhabited-recursion i f (inhabited-intro x) ≡ f x

inhabited-recursion-computation i f x = refl (f x)

inhabited-induction : global-dfunext
                    → {X : 𝓤 ̇ } {P : is-inhabited X → 𝓤 ̇ }
                      (i : (s : is-inhabited X) → is-subsingleton (P s))
                      (f : (x : X) → P (inhabited-intro x))
                    → (s : is-inhabited X) → P s

inhabited-induction fe {X} {P} i f s = φ' s
 where
  φ : X → P s
  φ x = transport P (inhabitation-is-subsingleton fe X (inhabited-intro x) s) (f x)

  φ' : is-inhabited X → P s
  φ' = inhabited-recursion (i s) φ

inhabited-computation : (fe : global-dfunext) {X : 𝓤 ̇ } {P : is-inhabited X → 𝓤 ̇ }
                        (i : (s : is-inhabited X) → is-subsingleton (P s))
                        (f : (x : X) → P (inhabited-intro x))
                        (x : X)
                      → inhabited-induction fe i f (inhabited-intro x) ≡ f x

inhabited-computation fe i f x = i (inhabited-intro x)
                                   (inhabited-induction fe i f (inhabited-intro x))
                                   (f x)

inhabited-subsingletons-are-pointed : (P : 𝓤 ̇ )
                                    → is-subsingleton P → is-inhabited P → P

inhabited-subsingletons-are-pointed P s = inhabited-recursion s (𝑖𝑑 P)

inhabited-functorial : global-dfunext → (X : 𝓤 ⁺ ̇ ) (Y : 𝓤 ̇ )
                     → (X → Y) → is-inhabited X → is-inhabited Y

inhabited-functorial fe X Y f = inhabited-recursion
                                  (inhabitation-is-subsingleton fe Y)
                                  (inhabited-intro ∘ f)

image' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (𝓤 ⊔ 𝓥)⁺ ̇
image' f = Σ y ꞉ codomain f , is-inhabited (Σ x ꞉ domain f , f x ≡ y)

restriction' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
             → image' f → Y

restriction' f (y , _) = y

corestriction' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
               → X → image' f

corestriction' f x = f x , inhabited-intro (x , refl (f x))

is-surjection' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (𝓤 ⊔ 𝓥)⁺ ̇
is-surjection' f = (y : codomain f) → is-inhabited (Σ x ꞉ domain f , f x ≡ y)

record subsingleton-truncations-exist : 𝓤ω where
 field
  ∥_∥                  : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇
  ∥∥-is-subsingleton   : {𝓤 : Universe} {X : 𝓤 ̇ } → is-subsingleton ∥ X ∥
  ∣_∣                  : {𝓤 : Universe} {X : 𝓤 ̇ } → X → ∥ X ∥
  ∥∥-recursion         : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {P : 𝓥 ̇ }
                       → is-subsingleton P → (X → P) → ∥ X ∥ → P
 infix 0 ∥_∥

module basic-truncation-development
        (pt  : subsingleton-truncations-exist)
        (hfe : global-hfunext)
       where

  open subsingleton-truncations-exist pt public

  hunapply : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {f g : Π A} → f ∼ g → f ≡ g
  hunapply = hfunext-gives-dfunext hfe

  ∥∥-recursion-computation : {X : 𝓤 ̇ } {P :  𝓥 ̇ }
                           → (i : is-subsingleton P)
                           → (f : X → P)
                           → (x : X)
                           → ∥∥-recursion i f ∣ x ∣ ≡ f x

  ∥∥-recursion-computation i f x = i (∥∥-recursion i f ∣ x ∣) (f x)

  ∥∥-induction : {X : 𝓤 ̇ } {P : ∥ X ∥ → 𝓥 ̇ }
              → ((s : ∥ X ∥) → is-subsingleton (P s))
              → ((x : X) → P ∣ x ∣)
              → (s : ∥ X ∥) → P s

  ∥∥-induction {𝓤} {𝓥} {X} {P} i f s = φ' s
   where
    φ : X → P s
    φ x = transport P (∥∥-is-subsingleton ∣ x ∣ s) (f x)
    φ' : ∥ X ∥ → P s
    φ' = ∥∥-recursion (i s) φ

  ∥∥-computation : {X : 𝓤 ̇ } {P : ∥ X ∥ → 𝓥 ̇ }
                 → (i : (s : ∥ X ∥) → is-subsingleton (P s))
                 → (f : (x : X) → P ∣ x ∣)
                 → (x : X)
                 → ∥∥-induction i f ∣ x ∣ ≡ f x

  ∥∥-computation i f x = i ∣ x ∣ (∥∥-induction i f ∣ x ∣) (f x)

  ∥∥-functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → ∥ X ∥ → ∥ Y ∥
  ∥∥-functor f = ∥∥-recursion ∥∥-is-subsingleton (λ x → ∣ f x ∣)

  ∥∥-agrees-with-inhabitation : (X : 𝓤 ̇ ) → ∥ X ∥ ⇔ is-inhabited X
  ∥∥-agrees-with-inhabitation X = a , b
   where
    a : ∥ X ∥ → is-inhabited X
    a = ∥∥-recursion (inhabitation-is-subsingleton hunapply X) inhabited-intro

    b : is-inhabited X → ∥ X ∥
    b = inhabited-recursion ∥∥-is-subsingleton ∣_∣

  _∨_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
  A ∨ B = ∥ A + B ∥

  infixl 20 _∨_

  ∃ : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
  ∃ A = (∥ Σ A ∥)

  -∃ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
  -∃ X Y = ∃ Y

  syntax -∃ A (λ x → b) = ∃ x ꞉ A , b

  infixr -1 -∃

  ∨-is-subsingleton : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → is-subsingleton (A ∨ B)
  ∨-is-subsingleton = ∥∥-is-subsingleton

  ∃-is-subsingleton : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → is-subsingleton (∃ A)
  ∃-is-subsingleton = ∥∥-is-subsingleton

  image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
  image f = Σ y ꞉ codomain f , ∃ x ꞉ domain f , f x ≡ y

  restriction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
              → image f → Y

  restriction f (y , _) = y

  corestriction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                → X → image f

  corestriction f x = f x , ∣ (x , refl (f x)) ∣

  is-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
  is-surjection f = (y : codomain f) → ∃ x ꞉ domain f , f x ≡ y

  being-surjection-is-subsingleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                   → is-subsingleton (is-surjection f)

  being-surjection-is-subsingleton f = Π-is-subsingleton hunapply
                                        (λ y → ∃-is-subsingleton)

  corestriction-is-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                           → is-surjection (corestriction f)

  corestriction-is-surjection f (y , s) = ∥∥-functor g s
   where
    g : (Σ x ꞉ domain f , f x ≡ y) → Σ x ꞉ domain f , corestriction f x ≡ (y , s)
    g (x , p) = x , to-subtype-≡ (λ _ → ∃-is-subsingleton) p

  surjection-induction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                       → is-surjection f
                       → (P : Y → 𝓦 ̇ )
                       → ((y : Y) → is-subsingleton (P y))
                       → ((x : X) → P (f x))
                       → (y : Y) → P y

  surjection-induction f i P j α y = ∥∥-recursion (j y) φ (i y)
   where
    φ : fiber f y → P y
    φ (x , r) = transport P r (α x)

  ∣∣-is-surjection : (X : 𝓤 ̇ ) → is-surjection (λ (x : X) → ∣ x ∣)
  ∣∣-is-surjection X s = γ
   where
    f : X → ∃ x ꞉ X , ∣ x ∣ ≡ s
    f x = ∣ (x , ∥∥-is-subsingleton ∣ x ∣ s) ∣

    γ : ∃ x ꞉ X , ∣ x ∣ ≡ s
    γ = ∥∥-recursion ∥∥-is-subsingleton f s

  singletons-are-inhabited : (X : 𝓤 ̇ )
                           → is-singleton X
                           → ∥ X ∥

  singletons-are-inhabited X s = ∣ center X s ∣

  inhabited-subsingletons-are-singletons : (X : 𝓤 ̇ )
                                         → ∥ X ∥
                                         → is-subsingleton X
                                         → is-singleton X

  inhabited-subsingletons-are-singletons X t i = c , φ
   where
    c : X
    c = ∥∥-recursion i (𝑖𝑑 X) t

    φ : (x : X) → c ≡ x
    φ = i c

  singleton-iff-inhabited-subsingleton : (X : 𝓤 ̇ )
                                       → is-singleton X
                                       ⇔ (∥ X ∥ × is-subsingleton X)

  singleton-iff-inhabited-subsingleton X =

    (λ (s : is-singleton X) → singletons-are-inhabited     X s ,
                              singletons-are-subsingletons X s) ,
    Σ-induction (inhabited-subsingletons-are-singletons X)

  equiv-iff-embedding-and-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                     →  is-equiv f
                                     ⇔ (is-embedding f × is-surjection f)

  equiv-iff-embedding-and-surjection f = (a , b)
   where
    a : is-equiv f → is-embedding f × is-surjection f
    a e = (λ y → singletons-are-subsingletons (fiber f y) (e y)) ,
          (λ y → singletons-are-inhabited     (fiber f y) (e y))

    b : is-embedding f × is-surjection f → is-equiv f
    b (e , s) y = inhabited-subsingletons-are-singletons (fiber f y) (s y) (e y)

  equiv-≡-embedding-and-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                   → propext (𝓤 ⊔ 𝓥)
                                   →  is-equiv f
                                   ≡ (is-embedding f × is-surjection f)

  equiv-≡-embedding-and-surjection f pe =
    pe (being-equiv-is-subsingleton hunapply hunapply f)
       (×-is-subsingleton
         (being-embedding-is-subsingleton hunapply f)
         (being-surjection-is-subsingleton f))
       (lr-implication (equiv-iff-embedding-and-surjection f))
       (rl-implication (equiv-iff-embedding-and-surjection f))

fix : {X : 𝓤 ̇ } → (X → X) → 𝓤 ̇
fix f = Σ x ꞉ domain f , f x ≡ x

from-fix : {X : 𝓤 ̇ } (f : X → X)
         → fix f → X

from-fix f = pr₁

to-fix : {X : 𝓤 ̇ } (f : X → X) → wconstant f
       → X → fix f

to-fix f κ x = f x , κ (f x) x

fix-is-subsingleton : {X : 𝓤 ̇ } (f : X → X)
                    → wconstant f → is-subsingleton (fix f)

fix-is-subsingleton {𝓤} {X} f κ = γ
 where
  a : (y x : X) → (f x ≡ x) ≃ (f y ≡ x)
  a y x = transport (_≡ x) (κ x y) , transport-is-equiv (_≡ x) (κ x y)

  b : (y : X) → fix f ≃ singleton-type' (f y)
  b y = Σ-cong (a y)

  c : X → is-singleton (fix f)
  c y = equiv-to-singleton (b y) (singleton-types'-are-singletons X (f y))

  d : fix f → is-singleton (fix f)
  d = c ∘ from-fix f

  γ : is-subsingleton (fix f)
  γ = subsingleton-criterion d

choice-function : 𝓤 ̇ → 𝓤 ⁺ ̇
choice-function X = is-inhabited X → X

wconstant-endomap-gives-choice-function : {X : 𝓤 ̇ }
                                        → wconstant-endomap X → choice-function X

wconstant-endomap-gives-choice-function {𝓤} {X} (f , κ) = from-fix f ∘ γ
 where
  γ : is-inhabited X → fix f
  γ = inhabited-recursion (fix-is-subsingleton f κ) (to-fix f κ)

choice-function-gives-wconstant-endomap : global-dfunext
                                        → {X : 𝓤 ̇ }
                                        → choice-function X → wconstant-endomap X

choice-function-gives-wconstant-endomap fe {X} c = f , κ
 where
  f : X → X
  f = c ∘ inhabited-intro

  κ : wconstant f
  κ x y = ap c (inhabitation-is-subsingleton fe X (inhabited-intro x)
                                                  (inhabited-intro y))

module find-hidden-root where

 open basic-arithmetic-and-order public

 μρ : (f : ℕ → ℕ) → root f → root f
 μρ f r = minimal-root-is-root f (root-gives-minimal-root f r)

 μρ-root : (f : ℕ → ℕ) → root f → ℕ
 μρ-root f r = pr₁ (μρ f r)

 μρ-root-is-root : (f : ℕ → ℕ) (r : root f) → f (μρ-root f r) ≡ 0
 μρ-root-is-root f r = pr₂ (μρ f r)

 μρ-root-minimal : (f : ℕ → ℕ) (m : ℕ) (p : f m ≡ 0)
                 → (n : ℕ) → f n ≡ 0 → μρ-root f (m , p) ≤ n

 μρ-root-minimal f m p n q = not-<-gives-≥ (μρ-root f (m , p)) n γ
  where
   φ : ¬ (f n ≢ 0) → ¬ (n < μρ-root f (m , p))
   φ = contrapositive (pr₂ (pr₂ (root-gives-minimal-root f (m , p))) n)

   γ : ¬ (n < μρ-root f (m , p))
   γ = φ (dni (f n ≡ 0) q)

 μρ-wconstant : (f : ℕ → ℕ) → wconstant (μρ f)
 μρ-wconstant f (n , p) (n' , p') = r
  where
   m m' : ℕ
   m  = μρ-root f (n , p)
   m' = μρ-root f (n' , p')

   l : m ≤ m'
   l = μρ-root-minimal f n p m' (μρ-root-is-root f (n' , p'))

   l' : m' ≤ m
   l' = μρ-root-minimal f n' p' m (μρ-root-is-root f (n , p))

   q : m ≡ m'
   q = ≤-anti _ _ l l'

   r : μρ f (n , p) ≡ μρ f (n' , p')
   r = to-subtype-≡ (λ _ → ℕ-is-set (f _) 0) q

 find-existing-root : (f : ℕ → ℕ) → is-inhabited (root f) → root f
 find-existing-root f = h ∘ g
   where
    γ : root f → fix (μρ f)
    γ = to-fix (μρ f) (μρ-wconstant f)

    g : is-inhabited (root f) → fix (μρ f)
    g = inhabited-recursion (fix-is-subsingleton (μρ f) (μρ-wconstant f)) γ

    h : fix (μρ f) → root f
    h = from-fix (μρ f)

 module find-existing-root-example where

  f : ℕ → ℕ
  f 0 = 1
  f 1 = 1
  f 2 = 0
  f 3 = 1
  f 4 = 0
  f 5 = 1
  f 6 = 1
  f 7 = 0
  f (succ (succ (succ (succ (succ (succ (succ (succ x)))))))) = x

  root-existence : is-inhabited (root f)
  root-existence = inhabited-intro (8 , refl 0)

  r : root f
  r = find-existing-root f root-existence

  x : ℕ
  x = pr₁ r

  x-is-root : f x ≡ 0
  x-is-root = pr₂ r

  p : x ≡ 2
  p = refl _

module exit-∥∥
        (pt  : subsingleton-truncations-exist)
        (hfe : global-hfunext)
       where

 open basic-truncation-development pt hfe
 open find-hidden-root

 find-∥∥-existing-root : (f : ℕ → ℕ)
                       → (∃ n ꞉ ℕ , f n ≡ 0)
                       →  Σ n ꞉ ℕ , f n ≡ 0

 find-∥∥-existing-root f = k
  where
   γ : root f → fix (μρ f)
   γ = to-fix (μρ f) (μρ-wconstant f)

   g : ∥ root f ∥ → fix (μρ f)
   g = ∥∥-recursion (fix-is-subsingleton (μρ f) (μρ-wconstant f)) γ

   h : fix (μρ f) → root f
   h = from-fix (μρ f)

   k : ∥ root f ∥ → root f
   k = h ∘ g

 module find-∥∥-existing-root-example where

  f : ℕ → ℕ
  f 0 = 1
  f 1 = 1
  f 2 = 0
  f 3 = 1
  f 4 = 0
  f 5 = 1
  f 6 = 1
  f 7 = 0
  f (succ (succ (succ (succ (succ (succ (succ (succ x)))))))) = x

  root-∥∥-existence : ∥ root f ∥
  root-∥∥-existence = ∣ 8 , refl 0 ∣

  r : root f
  r = find-∥∥-existing-root f root-∥∥-existence

  x : ℕ
  x = pr₁ r

  x-is-root : f x ≡ 0
  x-is-root = pr₂ r

  NB : find-∥∥-existing-root f
     ≡ from-fix (μρ f) ∘ ∥∥-recursion
                          (fix-is-subsingleton (μρ f) (μρ-wconstant f))
                          (to-fix (μρ f) (μρ-wconstant f))
  NB = refl _

  p : x ≡ 2
  p = ap (pr₁ ∘ from-fix (μρ f))
         (∥∥-recursion-computation
            (fix-is-subsingleton (μρ f) (μρ-wconstant f))
            (to-fix (μρ f) (μρ-wconstant f))
            (8 , refl _))

 wconstant-endomap-gives-∥∥-choice-function : {X : 𝓤 ̇ }
                                            → wconstant-endomap X
                                            → (∥ X ∥ → X)

 wconstant-endomap-gives-∥∥-choice-function {𝓤} {X} (f , κ) = from-fix f ∘ γ
  where
   γ : ∥ X ∥ → fix f
   γ = ∥∥-recursion (fix-is-subsingleton f κ) (to-fix f κ)

 ∥∥-choice-function-gives-wconstant-endomap : {X : 𝓤 ̇ }
                                            → (∥ X ∥ → X)
                                            → wconstant-endomap X

 ∥∥-choice-function-gives-wconstant-endomap {𝓤} {X} c = f , κ
  where
   f : X → X
   f = c ∘ ∣_∣

   κ : wconstant f
   κ x y = ap c (∥∥-is-subsingleton ∣ x ∣ ∣ y ∣)

 ∥∥-recursion-set : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                  → is-set Y
                  → (f : X → Y)
                  → wconstant f
                  → ∥ X ∥ → Y

 ∥∥-recursion-set {𝓤} {𝓥} X Y s f κ = f'
  where
   ψ : (y y' : Y) →  (Σ x ꞉ X , f x ≡ y) → (Σ x' ꞉ X , f x' ≡ y') → y ≡ y'
   ψ y y' (x , r) (x' , r') = y    ≡⟨ r ⁻¹ ⟩
                              f x  ≡⟨ κ x x' ⟩
                              f x' ≡⟨ r' ⟩
                              y'   ∎

   φ : (y y' : Y) → (∃ x ꞉ X , f x ≡ y) → (∃ x' ꞉ X , f x' ≡ y') → y ≡ y'
   φ y y' u u' = ∥∥-recursion (s y y') (λ - → ∥∥-recursion (s y y') (ψ y y' -) u') u

   P : 𝓤 ⊔ 𝓥 ̇
   P = image f

   i : is-subsingleton P
   i (y , u) (y' , u') = to-subtype-≡ (λ _ → ∃-is-subsingleton) (φ y y' u u')

   g : ∥ X ∥ → P
   g = ∥∥-recursion i (corestriction f)

   h : P → Y
   h = restriction f

   f' : ∥ X ∥ → Y
   f' = h ∘ g

\end{code}
