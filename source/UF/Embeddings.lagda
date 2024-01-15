Martin Escardo

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.Embeddings where

open import MLTT.Spartan

open import MLTT.Plus-Properties
open import UF.Base
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.LeftCancellable
open import UF.Lower-FunExt
open import UF.Retracts
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.UA-FunExt
open import UF.Univalence
open import UF.Yoneda

is-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-embedding f = each-fiber-of f is-prop

being-embedding-is-prop : funext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
                        → {X : 𝓤 ̇ }
                          {Y : 𝓥 ̇ }
                          (f : X → Y)
                        → is-prop (is-embedding f)
being-embedding-is-prop {𝓤} {𝓥} fe f =
 Π-is-prop (lower-funext 𝓤 𝓤 fe) (λ x → being-prop-is-prop fe)

id-is-embedding : {X : 𝓤 ̇ } → is-embedding (id {𝓤} {X})
id-is-embedding = singleton-types'-are-props

∘-is-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                 {f : X → Y} {g : Y → Z}
               → is-embedding f
               → is-embedding g
               → is-embedding (g ∘ f)
∘-is-embedding {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {g} e d = h
 where
  T : (z : Z) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
  T z = Σ (y , _) ꞉ fiber g z , fiber f y

  T-is-prop : (z : Z) → is-prop (T z)
  T-is-prop z = subtypes-of-props-are-props' pr₁ (pr₁-lc (λ {t} → e (pr₁ t))) (d z)

  φ : (z : Z) → fiber (g ∘ f) z → T z
  φ z (x , p) = (f x , p) , x , refl

  γ : (z : Z) → T z → fiber (g ∘ f) z
  γ z ((.(f x) , p) , x , refl) = x , p

  γφ : (z : Z) (t : fiber (g ∘ f) z) → γ z (φ z t) ＝ t
  γφ .(g (f x)) (x , refl) = refl

  h : (z : Z) → is-prop (fiber (g ∘ f) z)
  h z = subtypes-of-props-are-props'
         (φ z)
         (sections-are-lc (φ z) (γ z , (γφ z)))
         (T-is-prop z)

_↪_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ↪ Y = Σ f ꞉ (X → Y) , is-embedding f

↪-refl : (X : 𝓤 ̇ ) → X ↪ X
↪-refl X = id , id-is-embedding

_∘↪_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
     → Y ↪ Z
     → X ↪ Y
     → X ↪ Z
(g , j) ∘↪ (f , i) = g ∘ f , ∘-is-embedding i j


⌊_⌋ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ↪ Y → X → Y
⌊ f , _ ⌋     = f

⌊_⌋-is-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (e : X ↪ Y)
                 → is-embedding ⌊ e ⌋
⌊ _ , i ⌋-is-embedding = i

_↪⟨_⟩_ : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ↪ Y → Y ↪ Z → X ↪ Z
_ ↪⟨ f , i ⟩ (g , j) = (g ∘ f) , (∘-is-embedding i j)

_□ : (X : 𝓤 ̇ ) → X ↪ X
_□ X = id , id-is-embedding

embedding-criterion : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                    → ((x : X) → is-prop (fiber f (f x)))
                    → is-embedding f
embedding-criterion f φ .(f x) (x , refl) = φ x (x , refl)

embedding-criterion' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                    → ((x x' : X) → (f x ＝ f x') ≃ (x ＝ x'))
                    → is-embedding f
embedding-criterion' {𝓤} {𝓥} {X} {Y} f e =
 embedding-criterion f
  (λ x' → equiv-to-prop (a x')
  (singleton-types'-are-props x'))
 where
  a : (x' : X) → fiber f (f x') ≃ (Σ x ꞉ X , x ＝ x')
  a x' = Σ-cong (λ x → e x x')

vv-equivs-are-embeddings : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                         → is-vv-equiv f
                         → is-embedding f
vv-equivs-are-embeddings f e y = singletons-are-props (e y)

equivs-are-embeddings : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → is-equiv f
                      → is-embedding f
equivs-are-embeddings f e = vv-equivs-are-embeddings f
                             (equivs-are-vv-equivs f e)

equivs-are-embeddings' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (𝕗 : X ≃ Y)
                      → is-embedding ⌜ 𝕗 ⌝
equivs-are-embeddings' (f , e) = equivs-are-embeddings f e

≃-gives-↪ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → X ↪ Y
≃-gives-↪ (f , i) = (f , equivs-are-embeddings f i)

embeddings-with-sections-are-vv-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                       → is-embedding f
                                       → has-section f
                                       → is-vv-equiv f
embeddings-with-sections-are-vv-equivs f i (g , η) y =
 pointed-props-are-singletons (g y , η y) (i y)

embeddings-with-sections-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                    → is-embedding f
                                    → has-section f
                                    → is-equiv f
embeddings-with-sections-are-equivs f i h =
 vv-equivs-are-equivs f (embeddings-with-sections-are-vv-equivs f i h)

Subtypes' : (𝓤 {𝓥} : Universe) → 𝓥 ̇ → 𝓤 ⁺ ⊔ 𝓥 ̇
Subtypes' 𝓤 {𝓥} Y = Σ X ꞉ 𝓤 ̇ , X ↪ Y

Subtypes : 𝓤 ̇ → 𝓤 ⁺ ̇
Subtypes {𝓤} Y = Subtypes' 𝓤 Y

etofun : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X ↪ Y) → (X → Y)
etofun = pr₁

is-embedding-etofun : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                    → (e : X ↪ Y)
                    → is-embedding (etofun e)
is-embedding-etofun = pr₂

equivs-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → X ↪ Y
equivs-embedding e = ⌜ e ⌝ , equivs-are-embeddings ⌜ e ⌝ (⌜⌝-is-equiv e)

embeddings-are-lc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                  → is-embedding f → left-cancellable f
embeddings-are-lc f e {x} {x'} p = ap pr₁ (e (f x) (x , refl) (x' , (p ⁻¹)))

subtypes-of-props-are-props : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (e : X → Y)
                             → is-embedding e
                             → is-prop Y
                             → is-prop X
subtypes-of-props-are-props e i =
 subtypes-of-props-are-props' e (embeddings-are-lc e i)

subtypes-of-sets-are-sets : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (e : X → Y)
                          → is-embedding e
                          → is-set Y
                          → is-set X
subtypes-of-sets-are-sets e i =
 subtypes-of-sets-are-sets' e (embeddings-are-lc e i)

is-embedding' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-embedding' f = ∀ x x' → is-equiv (ap f {x} {x'})

embedding-gives-embedding' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                           → is-embedding f
                           → is-embedding' f
embedding-gives-embedding' {𝓤} {𝓥} {X} {Y} f ise = g
 where
  b : (x : X) → is-singleton (fiber f (f x))
  b x = (x , refl) , ise (f x) (x , refl)

  c : (x : X) → is-singleton (fiber' f (f x))
  c x = retract-of-singleton
         (≃-gives-▷ (fiber-lemma f (f x)))
         (b x)

  g : (x x' : X) → is-equiv (ap f {x} {x'})
  g x = universality-equiv x refl
         (central-point-is-universal
         (λ x' → f x ＝ f x')
         (center (c x))
         (centrality (c x)))

embedding-criterion-converse' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                             → is-embedding f
                             → (x' x : X)
                             → (x' ＝ x) ≃ (f x' ＝ f x)
embedding-criterion-converse' f e x' x = ap f {x'} {x} ,
                                         embedding-gives-embedding' f e x' x

embedding-criterion-converse : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                             → is-embedding f
                             → (x' x : X)
                             → (f x' ＝ f x) ≃ (x' ＝ x)
embedding-criterion-converse f e x' x = ≃-sym (embedding-criterion-converse' f e x' x)

embedding'-gives-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                             (f : X → Y)
                           → is-embedding' f
                           → is-embedding f
embedding'-gives-embedding {𝓤} {𝓥} {X} {Y} f ise = g
 where
  e : (x : X) → is-central (Σ x' ꞉ X , f x ＝ f x') (x , refl)
  e x = universal-element-is-central
         (x , refl)
         (equiv-universality x refl (ise x))

  h : (x : X) → is-prop (fiber' f (f x))
  h x σ τ = σ          ＝⟨ (e x σ)⁻¹ ⟩
            (x , refl) ＝⟨ e x τ ⟩
            τ          ∎

  g' : (y : Y) → is-prop (fiber' f y)
  g' y (x , p) = transport
                  (λ - → is-prop (Σ x' ꞉ X , - ＝ f x'))
                  (p ⁻¹)
                  (h x)
                  (x , p)

  g : (y : Y) → is-prop (fiber f y)
  g y = left-cancellable-reflects-is-prop
         ⌜ fiber-lemma f y ⌝
         (section-lc _
           (equivs-are-sections _ (⌜⌝-is-equiv (fiber-lemma f y ))))
         (g' y)

pr₁-is-embedding : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                 → ((x : X) → is-prop (Y x))
                 → is-embedding (pr₁ {𝓤} {𝓥} {X} {Y})
pr₁-is-embedding f x ((x , y') , refl) ((x , y'') , refl) = g
 where
  g : (x , y') , refl ＝ (x , y'') , refl
  g = ap (λ - → (x , -) , refl) (f x y' y'')


to-subtype-＝-≃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                → ((x : X) → is-prop (A x))
                → {x y : X} {a : A x} {b : A y}
                → (x ＝ y) ≃ ((x , a) ＝ (y , b))
to-subtype-＝-≃ A-is-prop-valued {x} {y} {a} {b} =
 embedding-criterion-converse pr₁ (pr₁-is-embedding A-is-prop-valued) (x , a) (y , b)


pr₁-lc-bis : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
           → ({x : X} → is-prop (Y x))
           → left-cancellable pr₁
pr₁-lc-bis f {u} {v} r = embeddings-are-lc pr₁ (pr₁-is-embedding (λ x → f {x})) r

pr₁-is-embedding-converse : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                          → is-embedding (pr₁ {𝓤} {𝓥} {X} {Y})
                          → (x : X) → is-prop (Y x)
pr₁-is-embedding-converse {𝓤} {𝓥} {X} {Y} ie x = h
  where
    e : Σ Y → X
    e = pr₁ {𝓤} {𝓥} {X} {Y}

    i : is-prop (fiber e x)
    i = ie x

    s : Y x → fiber e x
    s y = (x , y) , refl

    r : fiber e x → Y x
    r ((x , y) , refl) = y

    rs : (y : Y x) → r (s y) ＝ y
    rs y = refl

    h : is-prop (Y x)
    h = left-cancellable-reflects-is-prop s (section-lc s (r , rs)) i

embedding-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
                         → is-embedding f
                         → g ∼ f
                         → is-embedding g
embedding-closed-under-∼ f g e H y = equiv-to-prop (∼-fiber-≃ H y) (e y)

K-idtofun-lc : K-axiom (𝓤 ⁺)
             → {X : 𝓤 ̇ } (x y : X) (A : X → 𝓤 ̇ )
             → left-cancellable (idtofun (Id x y) (A y))
K-idtofun-lc {𝓤} k {X} x y A {p} {q} r = k (𝓤 ̇ ) p q

lc-maps-into-sets-are-embeddings : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                 → left-cancellable f
                                 → is-set Y
                                 → is-embedding f
lc-maps-into-sets-are-embeddings {𝓤} {𝓥} {X} {Y} f f-lc iss y (x , p) (x' , p') = γ
 where
   r : x ＝ x'
   r = f-lc (p ∙ (p' ⁻¹))

   q : yoneda-nat x (λ x → f x ＝ y) p x' r ＝ p'
   q = iss (yoneda-nat x (λ x → f x ＝ y) p x' r) p'

   γ : x , p ＝ x' , p'
   γ = to-Σ-Id (r , q)

sections-into-sets-are-embeddings : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                  → is-section f
                                  → is-set Y
                                  → is-embedding f
sections-into-sets-are-embeddings f f-is-section Y-is-set =
 lc-maps-into-sets-are-embeddings f (sections-are-lc f f-is-section) Y-is-set

lc-maps-are-embeddings-with-K : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                              → left-cancellable f
                              → K-axiom 𝓥
                              → is-embedding f
lc-maps-are-embeddings-with-K {𝓤} {𝓥} {X} {Y} f f-lc k =
 lc-maps-into-sets-are-embeddings f f-lc (k Y)

factor-is-lc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
               (f : X → Y)
               (g : Y → Z)
             → left-cancellable (g ∘ f)
             → left-cancellable f
factor-is-lc f g gf-lc {x} {x'} p = gf-lc (ap g p)

factor-is-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                      (f : X → Y)
                      (g : Y → Z)
                    → is-embedding (g ∘ f)
                    → is-embedding g
                    → is-embedding f
factor-is-embedding {𝓤} {𝓥} {𝓦} {X} {Y} {Z} f g i j = γ
 where
  a : (x x' : X) → (x ＝ x') ≃ (g (f x) ＝ g (f x'))
  a x x' = ap (g ∘ f) {x} {x'} , embedding-gives-embedding' (g ∘ f) i x x'

  b : (y y' : Y) → (y ＝ y') ≃ (g y ＝ g y')
  b y y' = ap g {y} {y'} , embedding-gives-embedding' g j y y'

  c : (x x' : X) → (f x ＝ f x') ≃ (x ＝ x')
  c x x' = (f x ＝ f x')         ≃⟨ b (f x) (f x') ⟩
           (g (f x) ＝ g (f x')) ≃⟨ ≃-sym (a x x') ⟩
           (x ＝ x')             ■

  γ : is-embedding f
  γ = embedding-criterion' f c

is-essential : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (𝓦 : Universe) → 𝓤 ⊔ 𝓥 ⊔ (𝓦 ⁺) ̇
is-essential f 𝓦 = (Z : 𝓦 ̇) (g : codomain f → Z)
                 → is-embedding (g ∘ f)
                 → is-embedding g

postcomp-is-embedding : FunExt
                      → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } (f : X → Y)
                      → is-embedding f
                      → is-embedding (λ (φ : A → X) → f ∘ φ)
postcomp-is-embedding {𝓤} {𝓥} {𝓦} fe {X} {Y} {A} f i = γ
 where
  g : (φ φ' : A → X) (a : A) → (φ a ＝ φ' a) ≃ (f (φ a) ＝ f (φ' a))
  g φ φ' a = ap f {φ a} {φ' a} , embedding-gives-embedding' f i (φ a) (φ' a)

  h : (φ φ' : A → X) → φ ∼ φ' ≃ f ∘ φ ∼ f ∘ φ'
  h φ φ' = Π-cong (fe 𝓦 𝓤) (fe 𝓦 𝓥) (g φ φ')

  k : (φ φ' : A → X) → (f ∘ φ ＝ f ∘ φ') ≃ (φ ＝ φ')
  k φ φ' = (f ∘ φ ＝ f ∘ φ') ≃⟨ ≃-funext (fe 𝓦 𝓥) (f ∘ φ) (f ∘ φ') ⟩
           (f ∘ φ ∼ f ∘ φ') ≃⟨ ≃-sym (h φ φ') ⟩
           (φ ∼ φ')         ≃⟨ ≃-sym (≃-funext (fe 𝓦 𝓤) φ φ') ⟩
           (φ ＝ φ')         ■

  γ : is-embedding (f ∘_)
  γ = embedding-criterion' (f ∘_) k

disjoint-images : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } → (X → A) → (Y → A) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
disjoint-images f g = ∀ x y → f x ≠ g y

disjoint-cases-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ }
                           (f : X → A) (g : Y → A)
                         → is-embedding f
                         → is-embedding g
                         → disjoint-images f g
                         → is-embedding (cases f g)
disjoint-cases-embedding {𝓤} {𝓥} {𝓦} {X} {Y} {A} f g ef eg d = γ
  where
   γ : (a : A) (σ τ : Σ z ꞉ X + Y , cases f g z ＝ a) → σ ＝ τ
   γ a (inl x , p) (inl x' , p') = r
     where
       q : x , p ＝ x' , p'
       q = ef a (x , p) (x' , p')

       h : fiber f a → fiber (cases f g) a
       h (x , p) = inl x , p

       r : inl x , p ＝ inl x' , p'
       r = ap h q

   γ a (inl x , p) (inr y  , q) = 𝟘-elim (d x y (p ∙ q ⁻¹))

   γ a (inr y , q) (inl x  , p) = 𝟘-elim (d x y (p ∙ q ⁻¹))

   γ a (inr y , q) (inr y' , q') = r
     where
       p : y , q ＝ y' , q'
       p = eg a (y , q) (y' , q')

       h : fiber g a → fiber (cases f g) a
       h (y , q) = inr y , q

       r : inr y , q ＝ inr y' , q'
       r = ap h p

\end{code}

TODO.
  (1) f : X → Y is an embedding iff fiber f (f x) is a singleton for every x : X.
  (2) f : X → Y is an embedding iff its corestriction to its image is an equivalence.

This can be deduced directly from Yoneda.

\begin{code}

inl-is-embedding : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                 → is-embedding (inl {𝓤} {𝓥} {X} {Y})
inl-is-embedding {𝓤} {𝓥} X Y (inl a) (a , refl) (a , refl) = refl
inl-is-embedding {𝓤} {𝓥} X Y (inr b) (x , p) (x' , p') = 𝟘-elim (+disjoint p)

inr-is-embedding : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                 → is-embedding (inr {𝓤} {𝓥} {X} {Y})
inr-is-embedding {𝓤} {𝓥} X Y (inl b) (x , p) (x' , p') = 𝟘-elim (+disjoint' p)
inr-is-embedding {𝓤} {𝓥} X Y (inr a) (a , refl) (a , refl) = refl

maps-of-props-into-sets-are-embeddings : {P : 𝓤 ̇ } {X : 𝓥 ̇ } (f : P → X)
                                       → is-prop P
                                       → is-set X
                                       → is-embedding f
maps-of-props-into-sets-are-embeddings f i j q (p , s) (p' , s') =
 to-Σ-＝ (i p p' , j _ s')

maps-of-props-are-embeddings : {P : 𝓤 ̇ } {Q : 𝓥 ̇ } (f : P → Q)
                             → is-prop P
                             → is-prop Q
                             → is-embedding f
maps-of-props-are-embeddings f i j =
 maps-of-props-into-sets-are-embeddings f i (props-are-sets j)

×-is-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } {B : 𝓣 ̇ }
                 (f : X → A ) (g : Y → B)
               → is-embedding f
               → is-embedding g
               → is-embedding (λ ((x , y) : X × Y) → (f x , g y))
×-is-embedding f g i j (a , b) = retract-of-prop
                               (r , (s , rs))
                               (×-is-prop (i a) (j b))
 where
  r : fiber f a × fiber g b → fiber (λ (x , y) → f x , g y) (a , b)
  r ((x , s) , (y , t)) = (x , y) , to-×-＝ s t

  s : fiber (λ (x , y) → f x , g y) (a , b) → fiber f a × fiber g b
  s ((x , y) , p) = (x , ap pr₁ p) , (y , ap pr₂ p)

  rs : (φ : fiber (λ (x , y) → f x , g y) (a , b)) → r (s φ) ＝ φ
  rs ((x , y) , refl) = refl

NatΣ-is-embedding : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
                    (ζ : Nat A B)
                  → ((x : X) → is-embedding (ζ x))
                  → is-embedding (NatΣ ζ)
NatΣ-is-embedding A B ζ i (x , b) = equiv-to-prop
                                     (≃-sym (NatΣ-fiber-equiv A B ζ x b))
                                     (i x b)

NatΣ-embedding : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
               → ((x : X) → A x ↪ B x)
               → Σ A ↪ Σ B
NatΣ-embedding f = NatΣ (λ x → ⌊ f x ⌋) ,
                   NatΣ-is-embedding _ _
                    (λ x → ⌊ f x ⌋)
                    (λ x → ⌊ f x ⌋-is-embedding)

NatΣ-is-embedding-converse : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
                             (ζ : Nat A B)
                           → is-embedding (NatΣ ζ)
                           → ((x : X) → is-embedding (ζ x))
NatΣ-is-embedding-converse A B ζ e x b = equiv-to-prop
                                          (NatΣ-fiber-equiv A B ζ x b)
                                          (e (x , b))

NatΠ-is-embedding : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
                    (ζ : Nat A B)
                  → funext 𝓤 (𝓥 ⊔ 𝓦)
                  → ((x : X) → is-embedding (ζ x))
                  → is-embedding (NatΠ ζ)
NatΠ-is-embedding {𝓤} {𝓥} {𝓦} A B ζ fe i g =
 equiv-to-prop
   (≃-sym (NatΠ-fiber-equiv A B ζ (lower-funext 𝓤 𝓥 fe) g))
   (Π-is-prop fe (λ x → i x (g x)))

\end{code}

For any proposition P, the unique map P → 𝟙 is an embedding:

\begin{code}

prop-embedding : (P : 𝓤 ̇ )
               → is-prop P
               → ∀ 𝓥 → is-embedding (unique-to-𝟙 {𝓤} {𝓥})
prop-embedding P i 𝓥 * (p , r) (p' , r') = to-×-＝
                                             (i p p')
                                             (props-are-sets 𝟙-is-prop r r')
\end{code}

Added by Tom de Jong.

If a type X embeds into a proposition, then X is itself a proposition.

\begin{code}

embedding-into-prop : {X : 𝓤 ̇ } {P : 𝓥 ̇ }
                    → is-prop P
                    → X ↪ P
                    → is-prop X
embedding-into-prop i (f , e) x y = d
 where
   a : x ＝ y → f x ＝ f y
   a = ap f {x} {y}

   b : is-equiv a
   b = embedding-gives-embedding' f e x y

   c : f x ＝ f y
   c = i (f x) (f y)

   d : x ＝ y
   d = inverse a b c

\end{code}

Added by Martin Escardo 12th July 2023.

Assuming univalence, the canonical map of X = Y into X → Y is an
embedding.

\begin{code}

idtofun-is-embedding : is-univalent 𝓤
                     → {X Y : 𝓤 ̇ } → is-embedding (idtofun X Y)
idtofun-is-embedding ua {X} {Y} =
 ∘-is-embedding
  (equivs-are-embeddings (idtoeq X Y) (ua X Y))
  (pr₁-is-embedding (being-equiv-is-prop'' (univalence-gives-funext ua)))
 where
  remark : pr₁ ∘ idtoeq X Y ＝ idtofun X Y
  remark = refl

Idtofun-is-embedding : is-univalent 𝓤
                     → funext (𝓤 ⁺) 𝓤
                     → {X Y : 𝓤 ̇ } → is-embedding (Idtofun {𝓤} {X} {Y})
Idtofun-is-embedding ua fe {X} {Y} =
 transport
  is-embedding
  (dfunext fe (idtofun-agreement X Y))
  (idtofun-is-embedding ua)

unique-from-𝟘-is-embedding : {X : 𝓤 ̇ } → is-embedding (unique-from-𝟘 {𝓤} {𝓥} {X})
unique-from-𝟘-is-embedding x (y , p) = 𝟘-elim y

\end{code}

Added by Martin Escardo and Tom de Jong 10th October 2023.

\begin{code}

∘-is-essential : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                 {f : X → Y} {g : Y → Z}
               → is-essential f 𝓣
               → is-essential g 𝓣
               → is-essential (g ∘ f) 𝓣
∘-is-essential {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} {Z} {f} {g} f-ess g-ess W h ghf-emb = II
 where
  I : is-embedding (h ∘ g)
  I = f-ess W (h ∘ g) ghf-emb

  II : is-embedding h
  II = g-ess W h I

\end{code}

We originally hoped to prove that Idtofun was essential, but it's not:
while the composite

           Idtofun            evaluate at 0
  (𝟚 ≃ 𝟚) ---------→ (𝟚 → 𝟚) ---------------> 𝟚

is an embedding, the evaluation map isn't.


Fixities:

\begin{code}

infix  0 _↪_
infix  1 _□
infixr 0 _↪⟨_⟩_


\end{code}
