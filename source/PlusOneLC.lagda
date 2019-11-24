Martin Escardo, 21 March 2018

We prove the known (constructive) fact that

  X + 𝟙 ≃ Y + 𝟙 → X ≃ Y.

The proof may be new (or not).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

open import Plus-Properties
open import UF-Base
open import UF-Retracts
open import UF-Equiv
open import UF-FunExt
open import UF-Subsingletons-FunExt
open import UF-Miscelanea
open import DiscreteAndSeparated

module PlusOneLC (fe : FunExt) where

_∖_ : (X : 𝓤 ̇ ) (a : X) → 𝓤 ̇
X ∖ a = Σ \(x : X) → x ≢ a

add-and-remove-point : {X : 𝓤 ̇ } →  X ≃ (X + 𝟙) ∖ (inr *)
add-and-remove-point {𝓤} {X} = qinveq f (g , ε , η)
 where
  f : X → (X + 𝟙 {𝓤}) ∖ inr *
  f x = (inl x , λ ())
  g : (X + 𝟙) ∖ inr * → X
  g (inl x , u) = x
  g (inr * , u) = 𝟘-elim (u refl)
  η : f ∘ g ∼ id
  η (inl x , u) = to-Σ-≡' (negations-are-props (fe 𝓤 𝓤₀) _ _)
  η (inr * , u) = 𝟘-elim (u refl)
  ε : g ∘ f ∼ id
  ε x = refl

remove-points : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → qinv f → (a : X) → X ∖ a ≃ Y ∖ (f a)
remove-points {𝓤} {𝓥} {X} {Y} f (g , ε , η) a = qinveq f' (g' , ε' , η')
 where
  f' : X ∖ a → Y ∖ (f a)
  f' (x , u) = (f x , λ(p : f x ≡ f a) → u ((ε x)⁻¹ ∙ ap g p ∙ ε a))
  g' : Y ∖ (f a) → X ∖ a
  g' (y , v) = (g y , λ(p : g y ≡ a) → v ((η y) ⁻¹ ∙ ap f p))
  ε' : g' ∘ f' ∼ id
  ε' (x , _) = to-Σ-≡ (ε x , negations-are-props (fe 𝓤 𝓤₀) _ _)
  η' : f' ∘ g' ∼ id
  η' (y , _) = to-Σ-≡ (η y , negations-are-props (fe 𝓥 𝓤₀) _ _)

add-one-and-remove-isolated-point : {Y : 𝓥 ̇ } (z : Y + 𝟙) → is-isolated z → ((Y + 𝟙) ∖ z) ≃ Y
add-one-and-remove-isolated-point {𝓥} {Y} (inl b) i = qinveq f (g , ε , η)
 where
  f : (Y + 𝟙) ∖ (inl b) → Y
  f (inl y , u) = y
  f (inr * , u) = b
  g' : (y : Y) → decidable (inl b ≡ inl y) → (Y + 𝟙) ∖ (inl b)
  g' y (inl p) = (inr * , +disjoint')
  g' y (inr u) = (inl y , contrapositive (_⁻¹) u)
  g : Y → (Y + 𝟙) ∖ (inl b)
  g y = g' y (i (inl y))
  ε : g ∘ f ∼ id
  ε (inl y , u) = to-Σ-≡ (p , negations-are-props (fe 𝓥 𝓤₀) _ _)
   where
    φ : (p : inl b ≡ inl y) (q : i (inl y) ≡ inl p) → i (inl y) ≡ inr (≢-sym u)
    φ p q = 𝟘-elim (u (p ⁻¹))
    ψ : (v : inl b ≢ inl y) (q : i (inl y) ≡ inr v) → i (inl y) ≡ inr (≢-sym u)
    ψ v q = q ∙ ap inr (negations-are-props (fe 𝓥 𝓤₀) _ _)
    h : i (inl y) ≡ inr (≢-sym u)
    h = equality-cases (i (inl y)) φ ψ
    p : pr₁(g' y (i (inl y))) ≡ inl y
    p = ap (pr₁ ∘ (g' y)) h
  ε (inr * , u) = equality-cases (i (inl b)) φ ψ
   where
    φ : (p : inl b ≡ inl b) → i (inl b) ≡ inl p → g (f (inr * , u)) ≡ (inr * , u)
    φ p q = r ∙ to-Σ-≡ (refl , negations-are-props (fe 𝓥 𝓤₀) _ _)
     where
      r : g b ≡ (inr * , +disjoint')
      r = ap (g' b) q
    ψ : (v : inl b ≢ inl b) → i (inl b) ≡ inr v → g (f (inr * , u)) ≡ (inr * , u)
    ψ v q = 𝟘-elim (v refl)
  η : f ∘ g ∼ id
  η y = equality-cases (i (inl y)) φ ψ
   where
    φ : (p : inl b ≡ inl y) → i (inl y) ≡ inl p → f (g' y (i (inl y))) ≡ y
    φ p q = ap (λ - → f (g' y -)) q ∙ inl-lc p
    ψ : (u : inl b ≢ inl y) → i (inl y) ≡ inr u → f (g' y (i (inl y))) ≡ y
    ψ _ = ap ((λ d → f (g' y d)))

add-one-and-remove-isolated-point {𝓥} {Y} (inr *) _ = ≃-sym add-and-remove-point

+𝟙-cancellable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X + 𝟙) ≃ (Y + 𝟙) → X ≃ Y
+𝟙-cancellable {𝓤} {𝓥} {X} {Y} (φ , e) =
   X                  ≃⟨ add-and-remove-point                              ⟩
  (X + 𝟙) ∖ inr *     ≃⟨ remove-points φ (equivs-are-qinvs φ e) (inr *)    ⟩
  (Y + 𝟙) ∖ φ (inr *) ≃⟨ add-one-and-remove-isolated-point
                          (φ (inr *))
                          (equivalences-preserve-isolatedness φ e (inr *)
                            new-point-is-isolated)                         ⟩
   Y ■

\end{code}

Added Friday 8th November 2019.

\begin{code}

patch : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (a : X) (b : Y)
      → is-isolated a → (X → Y) → (X → Y)
patch a b i f x = Cases (i x)
                    (λ (_ : a ≡ x) → b)
                    (λ (_ : a ≢ x) → f x)

patch-equation₀ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (a : X) (b : Y)
                  (i : is-isolated a) (f : X → Y)
                → patch a b i f a ≡ b
patch-equation₀ a b i f = Cases-equality-l (λ _ → b) (λ _ → f a) (i a) refl γ
 where
  γ : i a ≡ inl refl
  γ = isolated-inl a i a refl

patch-equation₁ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (a : X) (b : Y)
                  (i : is-isolated a) (f : X → Y)
                → (x : X) → a ≢ x → patch a b i f x ≡ f x
patch-equation₁ {𝓤} {X} a b i f x n = Cases-equality-r (λ _ → b) (λ _ → f x) (i x) n γ
 where
  γ : i x ≡ inr n
  γ = isolated-inr (fe 𝓤 𝓤₀) a i x n

swap : {X : 𝓤 ̇ } (a b : X) → is-isolated a → is-isolated b → X → X
swap a b i j = patch a b i (patch b a j id)

swap-equation₀ : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b)
               → swap a b i j a ≡ b
swap-equation₀ a b i j = patch-equation₀ a b i (patch b a j id)

swap-equation₁ : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b)
               → swap a b i j b ≡ a
swap-equation₁ a b i j = γ (j a)
 where
  γ : (b ≡ a) + (b ≢ a) → swap a b i j b ≡ a
  γ (inl r) =
      swap a b i j b ≡⟨ ap (swap a b i j) r    ⟩
      swap a b i j a ≡⟨ swap-equation₀ a b i j ⟩
      b              ≡⟨ r                      ⟩
      a              ∎
  γ (inr n) =
      swap a b i j b                 ≡⟨ refl                                               ⟩
      patch a b i (patch b a j id) b ≡⟨ patch-equation₁ a b i (patch b a j id) b (≢-sym n) ⟩
      patch b a j id b               ≡⟨ patch-equation₀ b a j id                           ⟩
      a                              ∎

swap-equation₂ : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b)
               → (x : X) → a ≢ x → b ≢ x → swap a b i j x ≡ x
swap-equation₂ a b i j x m n =
  swap a b i j x                 ≡⟨ refl                                       ⟩
  patch a b i (patch b a j id) x ≡⟨ patch-equation₁ a b i (patch b a j id) x m ⟩
  patch b a j id x               ≡⟨ patch-equation₁ b a j id x n               ⟩
  x                              ∎

swap-symmetric : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b)
               → swap a b i j ∼ swap b a j i
swap-symmetric a b i j x = γ (i x) (j x)
 where
  γ : (a ≡ x) + (a ≢ x) → (b ≡ x) + (b ≢ x) → swap a b i j x ≡ swap b a j i x
  γ (inl p) _ =
    swap a b i j x ≡⟨ ap (swap a b i j) (p ⁻¹)         ⟩
    swap a b i j a ≡⟨ swap-equation₀ a b i j           ⟩
    b              ≡⟨ (swap-equation₁ b a j i)⁻¹       ⟩
    swap b a j i a ≡⟨ ap (swap b a j i) p              ⟩
    swap b a j i x ∎
  γ (inr _) (inl q) =
    swap a b i j x ≡⟨ ap (swap a b i j) (q ⁻¹)         ⟩
    swap a b i j b ≡⟨ swap-equation₁ a b i j           ⟩
    a              ≡⟨ (swap-equation₀ b a j i)⁻¹       ⟩
    swap b a j i b ≡⟨ ap (swap b a j i) q              ⟩
    swap b a j i x ∎
  γ (inr m) (inr n) =
    swap a b i j x ≡⟨ swap-equation₂ a b i j x m n     ⟩
    x              ≡⟨ (swap-equation₂ b a j i x n m)⁻¹ ⟩
    swap b a j i x ∎

swap-involutive : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b)
                → swap a b i j ∘ swap a b i j ∼ id
swap-involutive a b i j x = γ (i x) (j x)
 where
  γ : (a ≡ x) + (a ≢ x) → (b ≡ x) + (b ≢ x) → swap a b i j (swap a b i j x) ≡ x
  γ (inl p) _ =
    swap a b i j (swap a b i j x) ≡⟨ ap (λ - → swap a b i j (swap a b i j -)) (p ⁻¹)  ⟩
    swap a b i j (swap a b i j a) ≡⟨ ap (swap a b i j) (swap-equation₀ a b i j)       ⟩
    swap a b i j b                ≡⟨ swap-equation₁ a b i j                           ⟩
    a                             ≡⟨ p                                                ⟩
    x                             ∎
  γ (inr _) (inl q) =
    swap a b i j (swap a b i j x) ≡⟨ ap (λ - → swap a b i j (swap a b i j -)) (q ⁻¹)  ⟩
    swap a b i j (swap a b i j b) ≡⟨ ap (swap a b i j) (swap-equation₁ a b i j)       ⟩
    swap a b i j a                ≡⟨ swap-equation₀ a b i j                           ⟩
    b                             ≡⟨ q                                                ⟩
    x                             ∎
  γ (inr m) (inr n) =
    swap a b i j (swap a b i j x) ≡⟨ ap (swap a b i j) (swap-equation₂ a b i j x m n) ⟩
    swap a b i j x                ≡⟨ swap-equation₂ a b i j x m n                     ⟩
    x                             ∎

swap-is-equiv : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b)
              → is-equiv (swap a b i j)
swap-is-equiv a b i j = qinvs-are-equivs
                         (swap a b i j)
                         (swap a b i j , (swap-involutive a b i j , swap-involutive a b i j))

≃-swap : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b) → X ≃ X
≃-swap a b i j = swap a b i j , swap-is-equiv a b i j

open import UF-EquivalenceExamples

co-derived-set : 𝓤 ̇ → 𝓤 ̇
co-derived-set X = Σ \(x : X) → is-isolated x

module another-approach where

 back : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → (X ≃ Y) × co-derived-set (Y + 𝟙) → X + 𝟙 ≃ Y + 𝟙
 back {𝓤} {𝓥} X Y (e , (z , i)) =
    X + 𝟙   ≃⟨ +cong e (one-𝟙-only 𝓤 𝓥) ⟩
    Y + 𝟙   ≃⟨ ≃-swap z (inr *) i new-point-is-isolated ⟩
    (Y + 𝟙) ■

 lemma₀ : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (f : X + 𝟙 {𝓦} → Y + 𝟙 {𝓣})
        → f (inr *) ≡ inr *
        → is-section f
        → (x : X) → Σ \(y : Y) → f (inl x) ≡ inl y
 lemma₀ X Y f p (g , gf) x = γ x (f (inl x)) refl
  where
   γ : (x : X) (z : Y + 𝟙) → f (inl x) ≡ z → Σ \(y : Y) → z ≡ inl y
   γ x (inl y) q = y , refl
   γ x (inr *) q = 𝟘-elim (+disjoint (inl x         ≡⟨ (gf (inl x))⁻¹ ⟩
                                      g (f (inl x)) ≡⟨ ap g q         ⟩
                                      g (inr *)     ≡⟨ ap g (p ⁻¹)    ⟩
                                      g (f (inr *)) ≡⟨ gf (inr *)     ⟩
                                      inr *         ∎))

 lemma₁ : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (f : X + 𝟙 {𝓦} → Y + 𝟙 {𝓣})
        → f (inr *) ≡ inr *
        → is-equiv f
        → Σ \(f' : X → Y) → is-equiv f' × (f ∼ +functor f' unique-to-𝟙)
 lemma₁ {𝓤} {𝓥} X Y f p i = γ (equivs-are-qinvs f i)
  where
   γ : qinv f → Σ \(f' : X → Y) → is-equiv f' × (f ∼ +functor f' unique-to-𝟙)
   γ (g , η , ε) = f' , qinvs-are-equivs f' (g' , η' , ε') , h
    where
     f' : X → Y
     f' x = pr₁ (lemma₀ X Y f p (g , η) x)
     a : (x : X) → f (inl x) ≡ inl (f' x)
     a x = pr₂ (lemma₀ X Y f p (g , η) x)
     q = g (inr *)     ≡⟨ (ap g p)⁻¹ ⟩
         g (f (inr *)) ≡⟨ η (inr *)  ⟩
         inr *         ∎
     g' : Y → X
     g' x = pr₁ (lemma₀ Y X g q (f , ε) x)
     b : (y : Y) → g (inl y) ≡ inl (g' y)
     b y = pr₂ (lemma₀ Y X g q (f , ε) y)
     η' : g' ∘ f' ∼ id
     η' x = inl-lc (inl (g' (f' x)) ≡⟨ (b (f' x))⁻¹   ⟩
                    g (inl (f' x))  ≡⟨ (ap g (a x))⁻¹ ⟩
                    g (f (inl x))   ≡⟨ η (inl x)      ⟩
                    inl x           ∎)
     ε' : f' ∘ g' ∼ id
     ε' y = inl-lc (inl (f' (g' y)) ≡⟨ (a (g' y))⁻¹   ⟩
                    f (inl (g' y))  ≡⟨ (ap f (b y))⁻¹ ⟩
                    f (g (inl y))   ≡⟨ ε (inl y)      ⟩
                    inl y           ∎)

     h : f ∼ +functor f' unique-to-𝟙
     h (inl x) = a x
     h (inr *) = p

 forth : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
       → (X + 𝟙 {𝓦} ≃ Y + 𝟙 {𝓣}) → co-derived-set (Y + 𝟙) × (X ≃ Y)
 forth {𝓤} {𝓥} {𝓦} {𝓣} X Y (g , i) = (t₀ , a) , f' , l
  where
   t₀ : Y + 𝟙
   t₀ = g (inr *)

   a : is-isolated t₀
   a = equivalences-preserve-isolatedness g i (inr *) new-point-is-isolated

   b : is-isolated (inr * ∶ Y + 𝟙 {𝓣})
   b = new-point-is-isolated

   h : Y + 𝟙 → Y + 𝟙
   h = swap t₀ (inr *) a b

   j : h ∘ h ∼ id
   j = swap-involutive t₀ (inr *) a b

   k : is-equiv h
   k = swap-is-equiv t₀ (inr *) a b

   f : X + 𝟙 → Y + 𝟙
   f = h ∘ g

   p : f (inr *) ≡ inr *
   p = swap-equation₀ t₀ (inr *) a b

   f' : X → Y
   f' = pr₁ (lemma₁ X Y f p (∘-is-equiv i k))

   l : is-equiv f'
   l = pr₁ (pr₂ (lemma₁ X Y f p (∘-is-equiv i k)))

   m : f ∼ +functor f' unique-to-𝟙
   m = pr₂ (pr₂ (lemma₁ X Y f p (∘-is-equiv i k)))

\end{code}

These maps are mutually inverse (hopefully this will be included
soon).


Precedences:

\begin{code}

infix 2 _∖_

\end{code}
