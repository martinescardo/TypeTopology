\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Embedding where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-Equiv
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-LeftCancellable
open import UF-Yoneda
open import UF-Retracts
open import UF-FunExt
open import UF-Subsingletons-FunExt
open import UF-Univalence
open import UF-UA-FunExt

is-embedding : {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
is-embedding f = ∀ y → is-prop(fiber f y)

is-embedding-is-prop : funext V (U ⊔ V) → funext (U ⊔ V) (U ⊔ V)
                     → {X : U ̇} {Y : V ̇} (f : X → Y)
                     → is-prop(is-embedding f)
is-embedding-is-prop {U} {V} fe fe' f = Π-is-prop
                                          fe
                                          (λ x → is-prop-is-a-prop fe')

embedding-criterion : {X : U ̇} {Y : V ̇} (f : X → Y)
                    → ((x : X) → is-prop (fiber f (f x)))
                    → is-embedding f
embedding-criterion f φ .(f x) (x , refl) = φ x (x , refl)

is-equiv-is-embedding : {X : U ̇} {Y : V ̇} (f : X → Y)
                      → is-equiv f → is-embedding f
is-equiv-is-embedding f e y = singletons-are-propositions (equivs-are-vv-equivs f e y)

_↪_ : U ̇ → V ̇ → U ⊔ V ̇
X ↪ Y = Σ \(f : X → Y) → is-embedding f

etofun : {X : U ̇} {Y : V ̇} → (X ↪ Y) → X → Y
etofun = pr₁

is-embedding-etofun : {X : U ̇} {Y : V ̇}
                    → (e : X ↪ Y) → is-embedding(etofun e)
is-embedding-etofun = pr₂

equiv-embedding : {X : U ̇} {Y : V ̇}
               → X ≃ Y → X ↪ Y
equiv-embedding e = eqtofun e ,
                    is-equiv-is-embedding
                     (eqtofun e)
                     (eqtofun-is-an-equiv e)

embedding-lc : {X : U ̇} {Y : V ̇} (f : X → Y)
             → is-embedding f → left-cancellable f
embedding-lc f e {x} {x'} p = ap pr₁ (e (f x) (x , refl) (x' , (p ⁻¹)))

is-embedding' : {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
is-embedding' f = ∀ x x' → is-equiv (ap f {x} {x'})

embedding-embedding' : {X : U ̇} {Y : V ̇} (f : X → Y)
                     → is-embedding f → is-embedding' f
embedding-embedding' {U} {V} {X} {Y} f ise = g
 where
  b : (x : X) → is-singleton(fiber f (f x))
  b x = (x , refl) , ise (f x) (x , refl)
  c : (x : X) → is-singleton(fiber' f (f x))
  c x = retract-of-singleton (pr₁ (fiber-lemma f (f x)) , pr₁(pr₂(fiber-lemma f (f x)))) (b x)
  g : (x x' : X) → is-equiv(ap f {x} {x'})
  g x = universality-equiv x refl (unique-element-is-universal-element
                                         (λ x' → f x ≡ f x')
                                         (pr₁(c x))
                                         (pr₂(c x)))

embedding'-embedding : {X : U ̇} {Y : V ̇} (f : X → Y) → is-embedding' f → is-embedding f
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

pr₁-embedding : {X : U ̇} {Y : X → V ̇}
              → ((x : X) → is-prop(Y x))
              → is-embedding (pr₁ {U} {V} {X} {Y})
pr₁-embedding f x ((.x , y') , refl) ((.x , y'') , refl) = g
 where
  g : (x , y') , refl ≡ (x , y'') , refl
  g = ap (λ - → (x , -) , refl) (f x y' y'')

pr₁-lc-bis : {X : U ̇} {Y : X → V ̇} → ({x : X} → is-prop(Y x)) → left-cancellable pr₁
pr₁-lc-bis f {u} {v} r = embedding-lc pr₁ (pr₁-embedding (λ x → f {x})) r

pr₁-embedding-converse : {X : U ̇} {Y : X → V ̇}
                       → is-embedding (pr₁ {U} {V} {X} {Y})
                       → ((x : X) → is-prop(Y x))
pr₁-embedding-converse {U} {V} {X} {Y} ie x = h
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
    h : is-prop(Y x)
    h = left-cancellable-reflects-is-prop s (section-lc s (r , rs)) isp

K-idtofun-lc : K (U ⁺) → {X : U ̇} (x y : X) (A : X → U ̇)
             → left-cancellable(idtofun (Id x y) (A y))
K-idtofun-lc {U} k {X} x y A {p} {q} r = k (Set U) p q

lc-embedding :{X : U ̇} {Y : V ̇} (f : X → Y)
             → left-cancellable f
             → is-set Y
             → is-embedding f
lc-embedding {U} {V} {X} {Y} f f-lc iss y (x , p) (x' , p') = to-Σ-Id (r , q)
 where
   r : x ≡ x'
   r = f-lc (p ∙ (p' ⁻¹))
   q : yoneda-nat x (λ x → f x ≡ y) p x' r ≡ p'
   q = iss (yoneda-nat x (λ x → f x ≡ y) p x' r) p'

lc-embedding-with-K : {X : U ̇} {Y : V ̇} (f : X → Y)
                    → left-cancellable f → K V → is-embedding f
lc-embedding-with-K {U} {V} {X} {Y} f f-lc k = lc-embedding f f-lc (k Y)

id-is-embedding : {X : U ̇} → is-embedding (id {U} {X})
id-is-embedding = identifications-to-is-prop

comp-embedding : {X : U ̇} {Y : V ̇} {Z : W ̇}
                {f : X → Y} {g : Y → Z}
               → is-embedding f
               → is-embedding g
               → is-embedding (g ∘ f)
comp-embedding {U} {V} {W} {X} {Y} {Z} {f} {g} e d = h
 where
  T : (z : Z) → U ⊔ V ⊔ W ̇
  T z = Σ \(w : fiber g z) → fiber f (pr₁ w)
  T-is-prop : (z : Z) → is-prop (T z)
  T-is-prop z = subtype-of-prop-is-prop pr₁ (pr₁-lc (λ {t} → e (pr₁ t))) (d z)
  φ : (z : Z) → fiber (g ∘ f) z → T z
  φ z (x , p) = (f x , p) , x , refl
  γ : (z : Z) → T z → fiber (g ∘ f) z
  γ z ((.(f x) , p) , x , refl) = x , p
  γφ : (z : Z) (t : fiber (g ∘ f) z) → γ z (φ z t) ≡ t
  γφ .(g (f x)) (x , refl) = refl
  h : (z : Z) → is-prop (fiber (g ∘ f) z)
  h z = subtype-of-prop-is-prop
         (φ z)
         (has-retraction-lc (φ z) (γ z , (γφ z)))
         (T-is-prop z)

disjoint-images : {X : U ̇} {Y : V ̇} {A : W ̇} → (X → A) → (Y → A) → U ⊔ V ⊔ W ̇
disjoint-images f g = ∀ x y → f x ≢ g y

disjoint-cases-embedding : {X : U ̇} {Y : V ̇} {A : W ̇} (f : X → A) (g : Y → A)
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

is-dense : {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
is-dense f = is-empty (Σ \y → ¬ fiber f y)

id-is-dense : {X : U ̇} → is-dense (id {U} {X})
id-is-dense (y , n) = n (y , refl)

comp-dense : {X : U ̇} {Y : V ̇} {Z : W ̇}
                {f : X → Y} {g : Y → Z}
           → is-dense f
           → is-dense g
           → is-dense (g ∘ f)
comp-dense {U} {V} {W} {X} {Y} {Z} {f} {g} e d = h
 where
  h : ¬ Σ \(z : Z) → ¬ fiber (g ∘ f) z
  h (z , n) = d (z , k)
   where
    k : ¬ fiber g z
    k (y , refl) = e (y , l)
     where
      l : ¬ fiber f y
      l (x , refl) = n (x , refl)

\end{code}

We should find a better home for the above definition, which says that
the complement of the image of f is empty. Perhaps a better
terminology would be ¬¬-dense.

\begin{code}

_↪ᵈ_ : U ̇ → V ̇ → U ⊔ V ̇
X ↪ᵈ Y = Σ \(f : X → Y) → is-embedding f × is-dense f

module _ {U V} {X : U ̇} {Y : V ̇} where

 retraction-is-dense : (r : X → Y) → has-section r → is-dense r
 retraction-is-dense r (s , rs) (y , n) = n (s y , rs y)

 is-equiv-is-dense : (f : X → Y) → is-equiv f → is-dense f
 is-equiv-is-dense f e = retraction-is-dense f (is-equiv-has-section f e)

 equiv-dense-embedding : X ≃ Y → X ↪ᵈ Y
 equiv-dense-embedding e = eqtofun e ,
                            is-equiv-is-embedding
                              (eqtofun e)
                              (eqtofun-is-an-equiv e),
                            is-equiv-is-dense
                              (eqtofun e)
                              (eqtofun-is-an-equiv e)

 detofun : (X ↪ᵈ Y) → X → Y
 detofun = pr₁

 is-embedding-detofun : (e : X ↪ᵈ Y) → is-embedding(detofun e)
 is-embedding-detofun e = pr₁ (pr₂ e)

 is-dense-detofun : (e : X ↪ᵈ Y) → is-dense(detofun e)
 is-dense-detofun e = pr₂ (pr₂ e)


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

 pair-fun-dense : is-dense f
               → ((x : X) → is-dense (g x))
               → is-dense pair-fun
 pair-fun-dense i j = contrapositive γ i
  where
   γ : (Σ \(w : Σ B) → ¬ fiber pair-fun w) → Σ \(y : Y) → ¬ fiber f y
   γ ((y , b) , n) = y , m
    where
     m : ¬ fiber f y
     m (x , refl) = j x (b , l)
      where
       l : ¬ fiber (g x) b
       l (a , refl) = n ((x , a) , refl)

inl-embedding : (X : U ̇) (Y : V ̇)
              → is-embedding (inl {U} {V} {X} {Y})
inl-embedding {U} {V} X Y (inl a) (.a , refl) (.a , refl) = refl
inl-embedding {U} {V} X Y (inr b) (x , p) (x' , p') = 𝟘-elim (+disjoint p)

inr-embedding : (X : U ̇) (Y : V ̇)
              → is-embedding (inr {U} {V} {X} {Y})
inr-embedding {U} {V} X Y (inl b) (x , p) (x' , p') = 𝟘-elim (+disjoint' p)
inr-embedding {U} {V} X Y (inr a) (.a , refl) (.a , refl) = refl

maps-of-props-are-embeddings : {P : U ̇} {Q : V ̇} (f : P → Q)
                             → is-prop P → is-prop Q → is-embedding f
maps-of-props-are-embeddings f i j q (p , s) (p' , s') = to-Σ-≡ (i p p' ,
                                                                props-are-sets j _ s')

×-embedding : ∀ {T} {X : U ̇} {Y : V ̇} {A : W ̇} {B : T ̇}
                (f : X → A ) (g : Y → B)
            → is-embedding f
            → is-embedding g
            → is-embedding (λ (z : X × Y) → (f (pr₁ z) , g (pr₂ z)))
×-embedding f g i j (a , b) = retract-of-subsingleton (r , (s , rs))
                                                      (×-is-prop (i a) (j b))
 where
  r : fiber f a × fiber g b → fiber (λ z → f (pr₁ z) , g (pr₂ z)) (a , b)
  r ((x , s) , (y , t)) = (x , y) , to-×-≡ s t
  s : fiber (λ z → f (pr₁ z) , g (pr₂ z)) (a , b) → fiber f a × fiber g b
  s ((x , y) , p) = (x , ap pr₁ p) , (y , ap pr₂ p)
  rs : (φ : fiber (λ z → f (pr₁ z) , g (pr₂ z)) (a , b)) → r (s φ) ≡ φ
  rs ((x , y) , refl) = refl

NatΣ-is-embedding : {X : U ̇} (A : X → V ̇) (B : X → W ̇) (ζ : Nat A B)
                  → ((x : X) → is-embedding(ζ x)) → is-embedding(NatΣ ζ)
NatΣ-is-embedding A B ζ i (x , b) = equiv-to-subsingleton
                                     (≃-sym (NatΣ-fiber-equiv A B ζ x b))
                                     (i x b)

NatΣ-is-embedding-converse : {X : U ̇} (A : X → V ̇) (B : X → W ̇) (ζ : Nat A B)
                           → is-embedding(NatΣ ζ) → ((x : X) → is-embedding(ζ x))
NatΣ-is-embedding-converse A B ζ e x b = equiv-to-subsingleton
                                          (NatΣ-fiber-equiv A B ζ x b)
                                          (e (x , b))

NatΠ-is-embedding : {X : U ̇} (A : X → V ̇) (B : X → W ̇) (ζ : Nat A B)
                  → funext U W → funext U (V ⊔ W)
                  → ((x : X) → is-embedding(ζ x)) → is-embedding(NatΠ ζ)
NatΠ-is-embedding A B ζ fe fe' i g = equiv-to-subsingleton
                                      (≃-sym (NatΠ-fiber-equiv A B ζ fe g))
                                      (Π-is-prop fe' (λ x → i x (g x)))

\end{code}
