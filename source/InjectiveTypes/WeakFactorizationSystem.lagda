Tom de Jong, 22 May 2025.
Continued in June 2025.

An anonymous reviewer of our TYPES abstract [1] suggested that some of our
results could be generalized to weak factorization systems. Here we consider a
factorization system based on embeddings and maps whose fibers are all injective
types. We are also thinking about the connections to *algebraic* weak
factorization systems.

[1] Tom de Jong and Martı́n Hötzel Escardó.
    "Examples and counter-examples of injective types in univalent mathematics".
    Abstract for the 31st International Conference on Types for Proofs and
    Programs (TYPES). 2025.
    url: https://msp.cis.strath.ac.uk/types2025/abstracts/TYPES2025_paper6.pdf.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module InjectiveTypes.WeakFactorizationSystem
        (fe : FunExt)
       where

open import InjectiveTypes.Blackboard fe

open import MLTT.Spartan

open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.IdEmbedding
open import UF.Univalence

private
 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

\end{code}

We define a fiberwise algebraically injective map to be one whose fibers are all
algebraically injective types.

NB. It may be that fiberwise flabbiness is more convenient to work with.

\begin{code}

fiberwise-ainjective : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → (𝓦 𝓣 : Universe)
                     → ((𝓦 ⊔ 𝓣) ⁺ ⊔ 𝓤 ⊔ 𝓥) ̇
fiberwise-ainjective f 𝓦 𝓣 =
 each-fiber-of f (λ F → ainjective-type F 𝓦 𝓣)

\end{code}

Any map can be factored as an embedding followed by a fiberwise algebraically
injective map.

\begin{code}

embedding-fiberwise-ainjective-factorization
 : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
 → is-univalent (𝓤 ⊔ 𝓥)
 → (f : A → B)
 → Σ X ꞉ (𝓤 ⊔ 𝓥)⁺ ̇  ,
   Σ l ꞉ (A → X) ,
   Σ r ꞉ (X → B) , (f ＝ r ∘ l)
                 × is-embedding l
                 × fiberwise-ainjective r (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
embedding-fiberwise-ainjective-factorization {𝓤} {𝓥} {A} {B} ua f =
 X , l , r , refl , l-is-embedding , r-fiberwise-ainjective
  where
   X : (𝓤 ⊔ 𝓥) ⁺ ̇
   X = Σ b ꞉ B , (fiber f b → (𝓤 ⊔ 𝓥) ̇ )

   ι : (Y : 𝓤' ̇ ) → Y → (Y → 𝓤' ̇ )
   ι Y = Id

   ι-is-embedding : is-univalent 𝓤' → (Y : 𝓤' ̇ ) → is-embedding (ι Y)
   ι-is-embedding ua _ = UA-Id-embedding ua fe

   l : A → X
   l = NatΣ (λ b → ι (fiber f b)) ∘ ⌜ domain-is-total-fiber f ⌝

   l-is-embedding : is-embedding l
   l-is-embedding =
    ∘-is-embedding
     (equivs-are-embeddings' (domain-is-total-fiber f))
     (NatΣ-is-embedding
       (fiber f)
       (λ b → fiber f b → 𝓤 ⊔ 𝓥 ̇ )
       (λ b → ι (fiber f b))
       (λ b → ι-is-embedding ua (fiber f b)))

   r : X → B
   r = pr₁

   r-fiberwise-ainjective : fiberwise-ainjective r (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
   r-fiberwise-ainjective b =
    equiv-to-ainjective
     (fiber r b)
     (fiber f b → 𝓤 ⊔ 𝓥 ̇ )
     (power-of-ainjective (universes-are-ainjective-Π' ua))
     (pr₁-fiber-equiv b)

\end{code}

We have (specified) diagonal lifts of embeddings against fiberwise algebraically
injective maps.

We consider a commutative square with j an embedding and r fiberwise
algebraically injective and we look to find diagonal filler: a map e : Y → D
making the resulting triangles commute.

       f
  X ------> D
  |       ^ |
  |      /  |
j |  ∃e /   | r
  |    /    |
  |   /     |
  v  /      v
  Y ------> E
       g

Note that in our case we have a designated filler.

\begin{code}

module lifting-problem
        {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {D : 𝓦 ̇ } {E : 𝓣 ̇ }
        (j : X → Y) (f : X → D) (r : D → E) (g : Y → E)
        (j-is-embedding : is-embedding j)
        (r-fiberwise-ainjective : fiberwise-ainjective r (𝓤 ⊔ 𝓥) 𝓣')
        -- NB. The last universe parameter is arbitrary.
        (comm-sq : r ∘ f ∼ g ∘ j)
       where

 lifting-problem-has-a-solution : Σ e ꞉ (Y → D) , (e ∘ j ∼ f) × (r ∘ e ∼ g)
 lifting-problem-has-a-solution = e , e-upper-triangle , e-lower-triangle
  where
   module _ (y : Y) where

    f̅ : fiber j y → fiber r (g y)
    f̅ (x , e) = (f x , (r (f x) ＝⟨ comm-sq x ⟩
                        g (j x) ＝⟨ ap g e ⟩
                        g y     ∎))

    𝕖 : Σ e ꞉ fiber r (g y) , ((p : fiber j y) → e ＝ f̅ p)
    𝕖 = ainjective-types-are-aflabby
         (fiber r (g y))
         (r-fiberwise-ainjective (g y))
         (fiber j y)
         (j-is-embedding y)
         f̅

    eʸ = pr₁ 𝕖
    eʸ-extends : (p : fiber j y) → eʸ ＝ f̅ p
    eʸ-extends = pr₂ 𝕖

   e : Y → D
   e y = pr₁ (eʸ y)

   e-lower-triangle : r ∘ e ∼ g
   e-lower-triangle y = pr₂ (eʸ y)

   e-upper-triangle : e ∘ j ∼ f
   e-upper-triangle x = ap pr₁ I
    where
     I : eʸ (j x) ＝ f̅ (j x) (x , refl)
     I = eʸ-extends (j x) (x , refl)

\end{code}

In the above it is important to work with *algebraically* injective types: if we
instead had assumed that each fiber of r is only injective, then we would have
gotten for each y : Y an unspecified element of D only, which, in the absence of
choice, fails to produce a function.

Finally, since propositions and injective types are closed under retracts and
because retractions of maps induce retractions of their fibers [HoTTBook,
Lemma 4.7.3], the embeddings and the fiberwise injective maps are closed under
retracts, so that by the "retract argument" [Rie14, Lemma 11.2.3], the
embeddings and fiberwise injective maps indeed give rise to a weak factorization
system.

TODO. Formalize this and, as a preliminary, retracts of maps.

[Rie14] Emily Riehl. Categorical Homotopy Theory.
        New Mathematical Monographs 24.
        Cambridge University Press, 2014.
        doi: 10.1017/ CBO9781107261457.
        url: https://math.jhu.edu/~eriehl/cathtpy.pdf.

Added 9 June 2025.
Due to the contravariance of (-) → 𝓤, the above factorization does not appear to
be functorial. Therefore, for f : A → B, we instead consider
   A ↪ Σ b ꞉ B , 𝓛 (fiber f b) → B,
where 𝓛 takes the partial elements of an element.

\begin{code}

open ainjectivity-of-Lifting

embedding-fiberwise-ainjective-factorization'
 : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
 → is-univalent (𝓤 ⊔ 𝓥)
 → (f : A → B)
 → Σ X ꞉ (𝓤 ⊔ 𝓥)⁺ ̇  ,
   Σ l ꞉ (A → X) ,
   Σ r ꞉ (X → B) , (f ＝ r ∘ l)
                 × is-embedding l
                 × fiberwise-ainjective r (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
embedding-fiberwise-ainjective-factorization' {𝓤} {𝓥} {A} {B} ua f =
 X , l , r , refl , l-is-embedding , r-fiberwise-ainjective
  where
   X : (𝓤 ⊔ 𝓥)⁺ ̇
   X = Σ b ꞉ B , 𝓛 (𝓤 ⊔ 𝓥) (fiber f b)

   l : A → X
   l = NatΣ (λ b → η (𝓤 ⊔ 𝓥)) ∘ ⌜ domain-is-total-fiber f ⌝

   l-is-embedding : is-embedding l
   l-is-embedding =
    ∘-is-embedding
     (equivs-are-embeddings' (domain-is-total-fiber f))
      (NatΣ-is-embedding
       (fiber f)
       (λ b → 𝓛 (𝓤 ⊔ 𝓥) (fiber f b))
       (λ b → η (𝓤 ⊔ 𝓥))
       (λ b → η-is-embedding' _ _ (fiber f b) ua fe'))

   r : X → B
   r = pr₁

   r-fiberwise-ainjective : fiberwise-ainjective r (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
   r-fiberwise-ainjective b =
    equiv-to-ainjective
     (fiber r b)
     (𝓛 (𝓤 ⊔ 𝓥) (fiber f b))
     (free-𝓛-algebra-ainjective (𝓤 ⊔ 𝓥) ua (fiber f b))
     (pr₁-fiber-equiv b)

\end{code}

TODO. Formalize functoriality (easy consequence of the functoriality of Σ,
taking fibers and 𝓛).

TODO. Move the functoriality of fiber to a more appropriate place.

\begin{code}

record [_,_] {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓦 ̇ } {Y : 𝓣 ̇ }
             (f : A → B) (g : X → Y) : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇  where
 field
  top : A → X
  bottom : B → Y
  comm : g ∘ top ∼ bottom ∘ f

[,]-id : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) → [ f , f ]
[,]-id f = record { top = id ; bottom = id ; comm = λ _ → refl }

open [_,_]

module _ {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓦 ̇ } {Y : 𝓣 ̇ } {Z : 𝓤' ̇ } {W : 𝓥' ̇ }
         (f : A → B) (g : X → Y) (h : W → Z)
       where

 [,]-comp : [ f , g ] → [ g , h ] → [ f , h ]
 [,]-comp α β = record { top = top β ∘ top α ;
                         bottom = bottom β ∘ bottom α ;
                         comm = λ a → h (top β (top α a))       ＝⟨ comm β (top α a) ⟩
                                      bottom β (g (top α a))    ＝⟨ ap (bottom β) (comm α a) ⟩
                                      bottom β (bottom α (f a)) ∎ }

module _ {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓦 ̇ } {Y : 𝓣 ̇ }
         (f : A → B) (g : X → Y)
       where

 fiber-functor : (α : [ f , g ]) (b : B) → fiber f b → fiber g (bottom α b)
 fiber-functor α b (a , p) = top α a , (g (top α a)    ＝⟨ comm α a ⟩
                                        bottom α (f a) ＝⟨ ap (bottom α) p ⟩
                                        bottom α b     ∎)

fiber-functor-id : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) (b : B)
                 → fiber-functor f f ([,]-id f) b ∼ id
fiber-functor-id f b (a , refl) = refl

module _ {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓦 ̇ } {Y : 𝓣 ̇ } {Z : 𝓤' ̇ } {W : 𝓥' ̇ }
         (f : A → B) (g : X → Y) (h : W → Z)
       where

 fiber-functor-comp : (α : [ f , g ]) (β : [ g , h ]) (b : B)
                    → fiber-functor f h ([,]-comp f g h α β) b
                      ∼ fiber-functor g h β (bottom α b) ∘ fiber-functor f g α b
 fiber-functor-comp α β b (a , refl) = refl

Σfunctor : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : A → 𝓦 ̇ } {Y : B → 𝓣 ̇ }
         → (f : A → B) (g : (a : A) → X a → Y (f a))
         → Σ X → Σ Y
Σfunctor f g (a , x) = (f a , g a x)

Σfunctor-id : {A : 𝓤 ̇ } {X : A → 𝓥 ̇ }
              (g : (a : A) → X a → X a)
              (p : (a : A) → g a ∼ id)
            → Σfunctor id g ∼ id
Σfunctor-id g p (a , x) = to-Σ-＝ (refl , p a x)

Σfunctor-comp : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {C : 𝓦 ̇ }
                {X : A → 𝓤' ̇ } {Y : B → 𝓥' ̇ } {Z : C → 𝓦' ̇ }
                (f : A → B) (g : B → C)
                (α : (a : A) → X a → Y (f a))
                (β : (b : B) → Y b → Z (g b))
              → Σfunctor {Y = Z} (g ∘ f) (λ a x → β (f a) (α a x))
                ∼ Σfunctor g β ∘ Σfunctor f α
Σfunctor-comp f g α β (a , x) = refl

Σfunctor-comp' : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {C : 𝓦 ̇ }
                 {X : A → 𝓤' ̇ } {Y : B → 𝓥' ̇ } {Z : C → 𝓦' ̇ }
                 (f : A → B) (g : B → C) (h : A → C)
                 (p : g ∘ f ∼ h)
                 (α : (a : A) → X a → Y (f a))
                 (β : (b : B) → Y b → Z (g b))
                 (γ : (a : A) → X a → Z (h a))
                 (q : (a : A) (x : X a) → β (f a) (α a x) ＝ transport⁻¹ Z (p a) (γ a x))
               → Σfunctor {Y = Z} h γ ∼ Σfunctor g β ∘ Σfunctor f α
Σfunctor-comp' f g h p α β γ q (a , x) = to-Σ-＝ (((p a) ⁻¹) , ((q a x) ⁻¹))

Σfunctor-comp'' :  {A : 𝓤 ̇ } {B : 𝓥 ̇ } {C : 𝓦 ̇ }
                  {X : A → 𝓤' ̇ } {Y : B → 𝓥' ̇ } {Z : C → 𝓦' ̇ }
                  (f : A → B) (g : B → C)
                  (α : (a : A) → X a → Y (f a))
                  (β : (b : B) → Y b → Z (g b))
                  (γ : (a : A) → X a → Z (g (f a)))
                  (q : (a : A) (x : X a) → β (f a) (α a x) ＝ γ a x)
                → Σfunctor {Y = Z} (g ∘ f) γ ∼ Σfunctor g β ∘ Σfunctor f α
Σfunctor-comp'' f g = Σfunctor-comp' f g (g ∘ f) (λ _ → refl)

open import Lifting.Monad renaming (𝓛̇ to 𝓛-functor)
open import UF.Subsingletons-FunExt

𝓛-functor-id : {X : 𝓤 ̇ } (f : X → X) (H : f ∼ id) → 𝓛-functor 𝓥 f ∼ id
𝓛-functor-id f H (P , φ , i) =
 to-Σ-＝ (refl , to-Σ-＝ (dfunext fe' (λ p → H (φ p)) ,
                          being-prop-is-prop fe' _ i))

𝓛-functor-comp : {X Y Z : 𝓤 ̇ } (f : X → Y) (g : Y → Z) (h : X → Z)
                 (H : g ∘ f ∼ h)
               → 𝓛-functor 𝓥 h ∼ 𝓛-functor 𝓥 g ∘ 𝓛-functor 𝓥 f
𝓛-functor-comp f g h H (P , φ , i) = to-Σ-＝ (refl , (to-Σ-＝ ((dfunext fe' (λ p → H (φ p) ⁻¹)) , (being-prop-is-prop fe' _ _))))

module _ {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓦 ̇ } {Y : 𝓣 ̇ }
         (f : A → B) (g : X → Y)
       where

 -- The universes for lifting are forced to be the same, so it appears we are
 -- restricted to considering functorial factorizations of maps in a *single*
 -- universe
 factorization-functor : [ f , g ]
                       → (Σ b ꞉ B , 𝓛 𝓤' (fiber f b))
                       → (Σ y ꞉ Y , 𝓛 𝓤' (fiber g y))
 factorization-functor α =
  Σfunctor (bottom α) (λ b → 𝓛-functor _ (fiber-functor f g α b))

factorization-functor-id : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B)
                         → factorization-functor f f {𝓤'} ([,]-id f) ∼ id
factorization-functor-id f =
 Σfunctor-id
  (λ b → 𝓛-functor _ (fiber-functor f f ([,]-id f) b))
  (λ b → 𝓛-functor-id (fiber-functor f f ([,]-id f) b) (fiber-functor-id f b))

factorization-functor-comp : {A B X Y Z W : 𝓤 ̇ }
                             (f : A → B) (g : X → Y) (h : Z → W)
                             (α : [ f , g ]) (β : [ g , h ])
                           → factorization-functor f h {𝓤} ([,]-comp f g h α β)
                             ∼ factorization-functor g h β ∘ factorization-functor f g α
factorization-functor-comp {𝓤} f g h α β =
 Σfunctor-comp''
  (bottom α)
  (bottom β)
  (λ b → 𝓛-functor _ (fiber-functor f g α b))
  (λ y → 𝓛-functor _ (fiber-functor g h β y))
  (λ b → 𝓛-functor 𝓤 (fiber-functor f h ([,]-comp f g h α β) b))
  (λ b → ∼-sym (𝓛-functor-comp
                 (fiber-functor f g α b)
                 (fiber-functor g h β (bottom α b))
                 (fiber-functor f h ([,]-comp f g h α β) b)
                 (∼-sym (fiber-functor-comp f g h α β b))))

module _ (ua : Univalence)
        where

 record Factorization {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) : (𝓤 ⊔ 𝓥) ⁺⁺ ̇  where
  field
   factoring-type : (𝓤 ⊔ 𝓥) ⁺ ̇
   left-map : A → factoring-type
   right-map : factoring-type → B
   factors : right-map ∘ left-map ＝ f
   left-map-is-embedding : is-embedding left-map
   right-map-fiberwise-ainjective : fiberwise-ainjective right-map (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)

 factorization : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) → Factorization f
 factorization f = record
                     { factoring-type = pr₁ fac
                     ; left-map = pr₁ (pr₂ fac)
                     ; right-map = pr₁ (pr₂ (pr₂ fac))
                     ; factors = pr₁ (pr₂ (pr₂ (pr₂ (fac))))
                     ; left-map-is-embedding = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (fac)))))
                     ; right-map-fiberwise-ainjective = pr₂ (pr₂ (pr₂ (pr₂ (pr₂ fac))))
                     }
  where
   fac = embedding-fiberwise-ainjective-factorization' (ua _) f

 open Factorization

 module _ {A B X Y : 𝓤 ̇ } -- {B : 𝓥 ̇ } {X : 𝓦 ̇ } {Y : 𝓣 ̇ }
          (f : A → B) (g : X → Y)
        where

  factorization-functor-left-maps : (α : [ f , g ])
                                  → [ left-map (factorization f) , left-map (factorization g) ]
  factorization-functor-left-maps α =
   record { top = top α ;
            bottom = factorization-functor f g α ;
            comm = λ a → to-Σ-＝ (comm α a ,
                                   (h (comm α a) (top α a) refl
                                    ∙ ap (η 𝓤) (to-Σ-＝ (refl , refl-left-neutral)))) }
    where
     h : {y y' : Y} (p : y ＝ y') (x : X) (q : g x ＝ y)
       → transport (λ - → 𝓛 𝓤 (fiber g -)) p (η 𝓤 (x , q)) ＝ η 𝓤 (x , (q ∙ p))
     h refl x q = refl

  factorization-functor-right-maps : (α : [ f , g ])
                                   → [ right-map (factorization f) , right-map (factorization g) ]
  factorization-functor-right-maps α =
   record { top = factorization-functor f g α ;
            bottom = bottom α ;
            comm = λ _ → refl }

\end{code}