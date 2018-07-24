\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Embedding where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-Equiv
open import UF-Subsingletons-Retracts
open import UF-Equiv
open import UF-LeftCancellable
open import UF-Yoneda
open import UF-Retracts

is-embedding : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
is-embedding f = ∀ y → is-prop(fiber f y)

embedding-lc : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) → is-embedding f → left-cancellable f
embedding-lc f e {x} {x'} p = ap pr₁ (e (f x) (x , refl) (x' , (p ⁻¹)))

is-embedding' : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
is-embedding' f = ∀ x x' → is-equiv (ap f {x} {x'})

embedding-embedding' : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) → is-embedding f → is-embedding' f
embedding-embedding' {U} {V} {X} {Y} f ise = g
 where
  b : (x : X) → is-singleton(fiber f (f x))
  b x = (x , refl) , ise (f x) (x , refl)
  c : (x : X) → is-singleton(fiber' f (f x))
  c x = retract-of-singleton (pr₁ (fiber-lemma f (f x))) (pr₁(pr₂(fiber-lemma f (f x)))) (b x)
  g : (x x' : X) → is-equiv(ap f {x} {x'})
  g x = universality-equiv x refl (unique-element-is-universal-element
                                         (λ x' → f x ≡ f x')
                                         (pr₁(c x))
                                         (pr₂(c x)))

embedding'-embedding : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) → is-embedding' f → is-embedding f
embedding'-embedding {U} {V} {X} {Y} f ise = g
 where
  e : (x x' : X) → is-the-only-element (x , refl)
  e x x' = universal-element-is-the-only-element
             (x , refl)
             (equiv-universality x refl (ise x))
  h : (x : X) → is-prop (fiber' f (f x))
  h x σ τ = σ ≡⟨ (e x (pr₁ σ) σ)⁻¹ ⟩ (x , refl) ≡⟨ e x (pr₁ τ) τ ⟩ τ ∎
  g' : (y : Y) → is-prop (fiber' f y)
  g' y (x , p) = transport (λ - → is-prop (Σ \(x' : X) → - ≡ f x')) (p ⁻¹) (h x) (x , p)
  g : (y : Y) → is-prop (fiber f y)
  g y = left-cancellable-reflects-is-prop
            (pr₁ (fiber-lemma f y))
            (section-lc _ (pr₂ (pr₂ (fiber-lemma f y)))) (g' y)

pr₁-embedding : ∀ {U V} {X : U ̇} {Y : X → V ̇}
              → ((x : X) → is-prop(Y x))
              → is-embedding (pr₁ {U} {V} {X} {Y})
pr₁-embedding f x ((.x , y') , refl) ((.x , y'') , refl) = g
 where
  g : (x , y') , refl ≡ (x , y'') , refl
  g = ap (λ - → (x , -) , refl) (f x y' y'')

pr₁-lc-bis : ∀ {U V} {X : U ̇} {Y : X → V ̇} → ({x : X} → is-prop(Y x)) → left-cancellable pr₁
pr₁-lc-bis f {u} {v} r = embedding-lc pr₁ (pr₁-embedding (λ x → f {x})) r

pr₁-embedding-converse : ∀ {U V} {X : U ̇} {Y : X → V ̇}
                       → is-embedding (pr₁ {U} {V} {X} {Y})
                       → ((x : X) → is-prop(Y x))
pr₁-embedding-converse {U} {V} {X} {Y} ie x = go
  where
    e : Σ Y → X
    e = pr₁ {U} {V} {X} {Y}
    isp : is-prop(fiber e x)
    isp = ie x
    s : Y x → fiber e x
    s y = (x , y) , refl
    r : fiber e x → Y x
    r ((x , y) , refl) = y
    rs : (y : Y x) → r(s y) ≡ y
    rs y = refl
    go : is-prop(Y x)
    go = left-cancellable-reflects-is-prop s (section-lc s (r , rs)) isp

K-idtofun-lc : ∀ {U} → K (U ′)
            → {X : U ̇} (x y : X) (A : X → U ̇) → left-cancellable(idtofun (Id x y) (A y))
K-idtofun-lc {U} k {X} x y A {p} {q} r = k (Set U) p q

left-cancellable-maps-into-sets-are-embeddings : ∀ {U V} → {X : U ̇} {Y : V ̇} (f : X → Y)
                                               → left-cancellable f → is-set Y → is-embedding f
left-cancellable-maps-into-sets-are-embeddings {U} {V} {X} {Y} f f-lc iss y (x , p) (x' , p') = to-Σ-Id (r , q)
 where
   r : x ≡ x'
   r = f-lc (p ∙ (p' ⁻¹))
   q : yoneda-nat x (λ x → f x ≡ y) p x' r ≡ p'
   q = iss (yoneda-nat x (λ x → f x ≡ y) p x' r) p'

left-cancellable-maps-are-embeddings-with-K : ∀ {U V} → {X : U ̇} {Y : V ̇} (f : X → Y)
                                            → left-cancellable f → K V → is-embedding f
left-cancellable-maps-are-embeddings-with-K {U} {V} {X} {Y} f f-lc k = left-cancellable-maps-into-sets-are-embeddings f f-lc (k Y)

id-is-embedding : ∀ {U} {X : U ̇} → is-embedding (id {U} {X})
id-is-embedding = identifications-to-is-prop

disjoint-images : ∀ {U V W} {X : U ̇} {Y : V ̇} {A : W ̇} → (X → A) → (Y → A) → U ⊔ V ⊔ W ̇
disjoint-images f g = ∀ x y → f x ≢ g y

disjoint-cases-embedding : ∀ {U V W} {X : U ̇} {Y : V ̇} {A : W ̇} (f : X → A) (g : Y → A)
                         → is-embedding f → is-embedding g → disjoint-images f g
                         → is-embedding (cases f g)
disjoint-cases-embedding {U} {V} {W} {X} {Y} {A} f g ef eg d = go
  where
   go : (a : A) (σ τ : Σ \(z : X + Y) → cases f g z ≡ a) → σ ≡ τ
   go a (inl x , p) (inl x' , p') = r
     where
       q : x , p ≡ x' , p'
       q = ef a (x , p) (x' , p')
       h : fiber f a → fiber (cases f g) a
       h (x , p) = inl x , p
       r : inl x , p ≡ inl x' , p'
       r = ap h q
   go a (inl x , p) (inr y  , q) = 𝟘-elim (d x y (p ∙ q ⁻¹))
   go a (inr y , q) (inl x  , p) = 𝟘-elim (d x y (p ∙ q ⁻¹))
   go a (inr y , q) (inr y' , q') = r
     where
       p : y , q ≡ y' , q'
       p = eg a (y , q) (y' , q')
       h : fiber g a → fiber (cases f g) a
       h (y , q) = inr y , q
       r : inr y , q ≡ inr y' , q'
       r = ap h p

\end{code}

TODO.
  (1) f : X → Y is an embedding iff fiber f (f x) is a singleton for every x : X.
  (2) f : X → Y is an embedding iff its corestriction to its image is an equivalence.

This can be deduced directly from Yoneda.

\begin{code}

is-full : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
is-full f = ¬ Σ \y → ¬(fiber f y)

\end{code}

We should find a better home for the above definition, which says that
the complement of the image of f is empty.

\begin{code}

module _ {U V W T}
         {X : U ̇}
         {A : X → V ̇}
         {Y : W ̇}
         {B : Y → T ̇}
         (f : X → Y)
         (g : (x : X) → A x → B (f x))
       where

 pair-fun : Σ A → Σ B
 pair-fun (x , a) = (f x , g x a)

 pair-fun-embedding : is-embedding f
                    → ((x : X) → is-embedding (g x))
                    → is-embedding pair-fun
 pair-fun-embedding e d (y , b) = h
  where
   Z : U ⊔ V ⊔ W ⊔ T ̇
   Z = Σ \(w : fiber f y) → fiber (g (pr₁ w)) (back-transport B (pr₂ w) b)
   Z-is-prop : is-prop Z
   Z-is-prop = subtype-of-prop-is-prop
                pr₁
                (pr₁-lc (λ {w} → d (pr₁ w) (back-transport B (pr₂ w) b)))
                (e y)
   φ : fiber pair-fun (y , b) → Z
   φ ((x , a) , refl) = (x , refl) , (a , refl)
   γ : Z → fiber pair-fun (y , b)
   γ ((x , refl) , (a , refl)) = (x , a) , refl
   γφ : (t : fiber pair-fun (y , b)) → γ (φ t) ≡ t
   γφ ((x , a) , refl) = refl
   h : is-prop (fiber pair-fun (y , b))
   h = subtype-of-prop-is-prop φ (has-retraction-lc φ (γ , γφ)) Z-is-prop

 pair-fun-full : is-full f
              → ((x : X) → is-full (g x))
              → is-full pair-fun
 pair-fun-full i j = contrapositive γ i
  where
   γ : (Σ \(w : Σ B) → ¬(fiber pair-fun w)) → Σ \(y : Y) → ¬(fiber f y)
   γ ((y , b) , n) = y , m
    where
     m : ¬(fiber f y)
     m (x , refl) = j x (b , l)
      where
       l : ¬(fiber (g x) b)
       l (a , refl) = n ((x , a) , refl)

\end{code}
