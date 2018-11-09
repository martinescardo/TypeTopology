Martin Escardo 25th October 2018.

The type of partial elements of a type (or lifting).
(Cf. my former student Cory Knapp's PhD thesis).

We focus, to begin with, on the fact that the canonical map into the
lifting is an embedding, which is easy for sets, but seems less easy for
arbitrary types.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT

module PartialElements where

open import UF-Base
open import UF-Subsingletons hiding (⊥)
open import UF-Embedding
open import UF-FunExt
open import UF-Equiv
open import UF-Subsingletons-FunExt
open import UF-Retracts

\end{code}

The domain of definition of a partial element is taken to be in an
arbitrary universe V.

\begin{code}

module _ (T : Universe) where

\end{code}

Te discuss the type 𝓛 X of partial elements of a type X, also called
the lifting of X.

\begin{code}

 𝓛 : U ̇ → U ⊔ T ⁺ ̇
 𝓛 X = Σ \(P : T ̇) → is-prop P × (P → X)

\end{code}

The "total" elements of 𝓛 X:

\begin{code}

 η : {X : U ̇} → X → 𝓛 X
 η x = 𝟙 , 𝟙-is-prop , (λ _ → x)

\end{code}

Its "undefined" element:

\begin{code}

 ⊥ : {X : U ̇} → 𝓛 X
 ⊥ = 𝟘 , 𝟘-is-prop , unique-from-𝟘

\end{code}

Our strategy to show that η is an embedding (has subsingleton fibers)
is to exhibit it as the composite of two embeddings (the first of
which is actually an equivalence).

\begin{code}

 𝓚 : U ̇ → U ⊔ T ⁺ ̇
 𝓚 X = Σ \(P : T ̇) → is-singleton P × (P → X)

 κ : {X : U ̇} → X → 𝓚 X
 κ x = 𝟙 , 𝟙-is-singleton , (λ _ → x)

 ζ : (X : U ̇) (P : T ̇) → is-singleton P × (P → X) → is-prop P × (P → X)
 ζ X P (i , φ) = singletons-are-props i , φ

 𝓚-to-𝓛 : (X : U ̇) → 𝓚 X → 𝓛 X
 𝓚-to-𝓛 X = NatΣ (ζ X)

 η-composite : funext T T → funext U (T ⁺ ⊔ U)
             → {X : U ̇} → η ≡ 𝓚-to-𝓛 X ∘ κ
 η-composite fe fe' {X} = dfunext fe' h
  where
   h : (x : X) → (𝟙 , 𝟙-is-prop ,                             λ _ → x)
               ≡ (𝟙 , singletons-are-props (𝟙-is-singleton) , λ _ → x)
   h x = to-Σ-≡ (refl , to-×-≡ (being-a-prop-is-a-prop fe _ _) refl)

\end{code}

The fact that 𝓚-to-𝓛 is an embedding can be proved by obtaining it as
a combination of maps that we already know to be embeddings, using
×-embedding, maps-of-props-are-embeddings, id-is-embedding, and
NatΣ-embedding.:

\begin{code}

 ζ-is-embedding : funext T T → (X : U ̇) (P : T ̇) → is-embedding (ζ X P)
 ζ-is-embedding fe X P = ×-embedding
                           singletons-are-props
                           id
                           (maps-of-props-are-embeddings
                              singletons-are-props
                              (is-singleton-is-a-prop fe)
                              (being-a-prop-is-a-prop fe))
                           id-is-embedding

 𝓚-to-𝓛-is-embedding : funext T T
                     → (X : U ̇) → is-embedding (𝓚-to-𝓛 X)
 𝓚-to-𝓛-is-embedding fe X = NatΣ-is-embedding
                                  (λ P → is-singleton P × (P → X))
                                  (λ P → is-prop P × (P → X))
                                  (ζ X)
                                  (ζ-is-embedding fe X)
\end{code}

That κ is an equivalence corresponds to the fact that the lifting of a
type X with respect to the dominance "is-singleton" is equivalent to X
itself.

\begin{code}

 κ-is-equiv : propext T → funext T T → funext T U
            → {X : U ̇} → is-equiv (κ {U} {X})
 κ-is-equiv {U} pe fe fe' {X} = qinvs-are-equivs κ (ν , (νκ , κν))
  where
   ν : {X : U ̇} → 𝓚 X → X
   ν (P , i , φ) = φ (is-singleton-pointed i)
   νκ : {X : U ̇} (x : X) → ν (κ x) ≡ x
   νκ x = refl
   κν : (m : 𝓚 X) → κ (ν m) ≡ m
   κν (P , i , φ) = u
    where
     t : 𝟙 ≡ P
     t = pe 𝟙-is-prop (singletons-are-props i) (λ _ → is-singleton-pointed i) unique-to-𝟙
     s : (t : 𝟙 ≡ P)
       → transport (λ - → is-singleton - × (- → X)) t (𝟙-is-singleton , (λ _ → φ (is-singleton-pointed i)))
       ≡ i , φ
     s refl = to-×-≡ a b
       where
        a : 𝟙-is-singleton ≡ i
        a = (singletons-are-props (pointed-props-are-singletons 𝟙-is-singleton (is-singleton-is-a-prop fe))
                                  𝟙-is-singleton i)
        b : (λ x → φ (is-singleton-pointed i)) ≡ φ
        b = dfunext fe' (λ x → ap φ (𝟙-is-prop (is-singleton-pointed i) x))
     u : 𝟙 , 𝟙-is-singleton , (λ _ → φ (is-singleton-pointed i)) ≡ P , i , φ
     u = to-Σ-≡ (t , s t)

 κ-is-embedding : propext T → funext T T → funext T U
                → {X : U ̇} → is-embedding (κ {U} {X})
 κ-is-embedding pe fe fe' = is-equiv-is-embedding κ (κ-is-equiv pe fe fe')

\end{code}

Finally, η is an embedding because it is equal to the composition of
two embeddings:

\begin{code}

 η-is-embedding : propext T → funext T T → funext T U → funext U (T ⁺ ⊔ U)
                → {X : U ̇} → is-embedding (η {U} {X})
 η-is-embedding pe fe fe' fe'' {X} =
   back-transport
    is-embedding
    (η-composite fe fe'')
    (comp-embedding (κ-is-embedding pe fe fe') (𝓚-to-𝓛-is-embedding fe X))
\end{code}

Te now give meaningful names to the projections:

\begin{code}

 is-defined : {X : U ̇} → 𝓛 X → T ̇
 is-defined (P , i , φ) = P

 being-defined-is-a-prop : {X : U ̇} (l : 𝓛  X) → is-prop (is-defined l)
 being-defined-is-a-prop (P , i , φ) = i

 value : {X : U ̇} (l : 𝓛  X) → is-defined l → X
 value (P , i , φ) = φ

\end{code}

Next we show that for any l : 𝓛 X,

 fiber η l ≃ is-defined l,

using the fact that the fiber is a proposition by virtue of η being an
embedding.

For this purpose, it is convenient to work with the information
"order" on 𝓛 X, which will really be a (partial) order only when X is
a set:

\begin{code}

 _⊑_ : {X : U ̇} → 𝓛 X → 𝓛 X → U ⊔ T ̇
 l ⊑ m = Σ \(f : is-defined l → is-defined m) → (d : is-defined l) → value l d ≡ value m (f d)

\end{code}

If X is a set, then 𝓛 X is a poset under _⊑_ (TODO). In the general
case, it should be some sort of univalent ∞-category with
hom-∞-groupoids x ⊑ y.

\begin{code}

 ⊑-id : {X : U ̇} (l : 𝓛 X) → l ⊑ l
 ⊑-id (P , i , φ) = id , (λ x → refl)

 ⊑-id' : {X : U ̇} (l m : 𝓛 X) → l ≡ m → l ⊑ m
 ⊑-id' l m p = transport (λ - → l ⊑ -) p (⊑-id l)

 ⊑-∘ : {X : U ̇} (l m n : 𝓛 X)
     → l ⊑ m → m ⊑ n → l ⊑ n
 ⊑-∘ l m n (f , δ) (g , ε) = g ∘ f , (λ d → δ d ∙ ε (f d))

 ⊑-anti : propext T → funext T T → funext T U
        → {X : U ̇} {l m : 𝓛 X}
        → (l ⊑ m) × (m ⊑ l) → l ≡ m
 ⊑-anti pe fe fe' {X} {Q , j , γ} {P , i , φ} ((f , δ) , (g , ε)) = e
  where
   a : Q ≡ P
   a = pe j i f g
   b : Idtofun (a ⁻¹) ≡ g
   b = dfunext fe (λ p → j (Idtofun (a ⁻¹) p) (g p))
   c : transport (λ - → is-prop - × (- → X)) a (j , γ)
     ≡ (transport is-prop a j , transport (λ - → - → X) a γ)
   c = transport-× is-prop (λ - → - → X) a
   d : pr₂ (transport (λ - → is-prop - × (- → X)) a (j , γ)) ≡ φ
   d = pr₂ (transport (λ - → is-prop - × (- → X)) a (j , γ))
             ≡⟨ ap pr₂ c ⟩
       transport (λ - → - → X) a γ
             ≡⟨ transport-is-pre-comp a γ ⟩
       γ ∘ Idtofun (a ⁻¹)
             ≡⟨ ap (λ - → γ ∘ -) b ⟩
       γ ∘ g
             ≡⟨ (dfunext fe' ε)⁻¹ ⟩
       φ     ∎
   e : Q , j , γ ≡ P , i , φ
   e = to-Σ-≡ (a , to-×-≡ (being-a-prop-is-a-prop fe _ i) d)

\end{code}

Te haven't used δ in the above proof. But we could use it instead of
ε, by defining ε' from δ as follows, and then using (dfunext fe' ε')
instead of (dfunext fe' ε)⁻¹ in the above proof:

\begin{code}

   ε' : (p : P) → γ (g p) ≡ φ p
   ε' p = δ (g p) ∙ ap φ (i (f (g p)) p)

\end{code}

Te can now establish the promised fact:

\begin{code}

 η-fiber-same-as-is-defined :
     propext T → funext T T → funext T U → funext U (T ⁺ ⊔ U)
   → {X : U ̇} (l : 𝓛 X)
   → (Σ \(x : X) → η x ≡ l) ≃ is-defined l
 η-fiber-same-as-is-defined pe fe fe' fe'' {X} l = f l , ((g l , fg) , (g l , gf))
  where
   f : (l : 𝓛 X) → fiber η l → is-defined l
   f (.𝟙 , .𝟙-is-prop , .(λ _ → x)) (x , refl) = *
   g : (l : 𝓛 X) → is-defined l → fiber η l
   g (P , i , φ) p = φ p , ⊑-anti pe fe fe' (a , b)
    where
     a : η (φ p) ⊑ (P , i , φ)
     a = (λ _ → p) , (λ _ → refl)
     b : (P , i , φ) ⊑ η (φ p)
     b = (λ _ → *) , (λ q → ap φ (i q p))
   fg : (d : is-defined l) → f l (g l d) ≡ d
   fg d = being-defined-is-a-prop l (f l (g l d)) d
   gf : (z : fiber η l) → g l (f l z) ≡ z
   gf z = η-is-embedding pe fe fe' fe'' l (g l (f l z)) z

\end{code}

They can't be equal, in the absence of cumulativity (and propositional
resizing), as the lhs lives in a universe higher than the rhs, and
equality is well-typed only for elements of the same type (here of the
same universe). This can be seen by adding type annotations to the
formulation of the above equivalence:

\begin{code}

 private
  η-fiber-same-as-is-defined' :
       propext T → funext T T → funext T U → funext U (T ⁺ ⊔ U)
    → {X : U ̇} (l : 𝓛 X)
    → (fiber η l ∶ T ⁺ ⊔ U ̇) ≃ (is-defined l ∶ T ̇)
  η-fiber-same-as-is-defined' = η-fiber-same-as-is-defined

\end{code}

For no choice of universes U and T can we have T ' ⊔ U to coincide
with T. However, for dominances other than is-prop, it is possible to
have the equality beyween the fiber of l and the definedness of l.

TODO: Could the map (anti l m) be an equivalence? No. Te should
instead have an equivalence (l ⊑ m) × (m ⊑ l) → (l ≡ m) × (l ≡ m),
reflecting the fact that there were two candidate proofs for the
equality, as discussed above.

But it is probably better to have the following version of ⊑-anti,
which should be an equivalence for each l and m:

\begin{code}

 ⊑-anti' : propext T → funext T T → funext T U
        → {X : U ̇} (l m : 𝓛 X) → (l ⊑ m) × (is-defined m → is-defined l) → l ≡ m
 ⊑-anti' pe fe fe' {X} (Q , j , γ) (P , i , φ) ((f , δ) , g) = e
  where
   ε' : (p : P) → γ (g p) ≡ φ p
   ε' p = δ (g p) ∙ ap φ (i (f (g p)) p)
   a : Q ≡ P
   a = pe j i f g
   b : Idtofun (a ⁻¹) ≡ g
   b = dfunext fe (λ p → j (Idtofun (a ⁻¹) p) (g p))
   c : transport (λ - → is-prop - × (- → X)) a (j , γ)
     ≡ (transport is-prop a j , transport (λ - → - → X) a γ)
   c = transport-× is-prop (λ - → - → X) a
   d : pr₂ (transport (λ - → is-prop - × (- → X)) a (j , γ)) ≡ φ
   d = pr₂ (transport (λ - → is-prop - × (- → X)) a (j , γ))
             ≡⟨ ap pr₂ c ⟩
       transport (λ - → - → X) a γ
             ≡⟨ transport-is-pre-comp a γ ⟩
       γ ∘ Idtofun (a ⁻¹)
             ≡⟨ ap (λ - → γ ∘ -) b ⟩
       γ ∘ g
             ≡⟨ dfunext fe' ε' ⟩
       φ     ∎
   e : Q , j , γ ≡ P , i , φ
   e = to-Σ-≡ (a , to-×-≡ (being-a-prop-is-a-prop fe _ i) d)


 ⊑-anti'-inverse :  {X : U ̇} (l m : 𝓛 X)
                 → l ≡ m → (l ⊑ m) × (is-defined m → is-defined l)
 ⊑-anti'-inverse l .l refl = ⊑-id l , id

 η-maximal : {X : U ̇} (x : X) (l : 𝓛 X) → η x ⊑ l → l ⊑ η x
 η-maximal x (P , i , γ) (f , δ) = (λ p → *) , (λ p → ap γ (i p (f *)) ∙ (δ *)⁻¹)

 ⊥-least : {X : U ̇} (x : X) → ⊥ ⊑ η x
 ⊥-least x = unique-from-𝟘 , λ z → unique-from-𝟘 z


 η-≡-gives-⊑ : {X : U ̇} {x y : X} → x ≡ y → η x ⊑ η y
 η-≡-gives-⊑ {U} {X} {x} {y} p = id , (λ d → p)

 η-⊑-gives-≡ : {X : U ̇} {x y : X} → η x ⊑ η y → x ≡ y
 η-⊑-gives-≡ (f , δ) = δ *

 η-≡-gives-⊑-is-equiv : funext T T → funext T U
                      → {X : U ̇} {x y : X}
                      → is-equiv (η-≡-gives-⊑ {U} {X} {x} {y})
 η-≡-gives-⊑-is-equiv {U} fe fe' {X} {x} {y} = qinvs-are-equivs η-≡-gives-⊑ (η-⊑-gives-≡ , α , β)
  where
   α : {x y : X} (p : x ≡ y) →  η-⊑-gives-≡ (η-≡-gives-⊑ p) ≡ p
   α p = refl

   β : {x y : X} (q : η x ⊑ η y) → η-≡-gives-⊑ (η-⊑-gives-≡ q) ≡ q
   β (f , δ) = to-×-≡ (dfunext fe (λ x → 𝟙-is-prop x (f x)))
                      (dfunext fe' (λ x → ap δ (𝟙-is-prop * x)))


{- TODO
⊑-directed-complete : {X I : U ̇} (l : I → 𝓛 X)
                    → ((i j : I) → Σ \(k : I) → (l i ⊑ l k) × (l j ⊑ l k))
                    → Σ \(m : 𝓛 X) → ((i : I) → l i ⊑ m)
                                   × ((n : 𝓛 X) → ((i : I) → l i ⊑ n) → m ⊑ n)
⊑-directed-complete = {!!}
-}

\end{code}

Te should also do least fixed points of continuous maps.

Added 7th November 2018. 'Monad' structure on 𝓛.

\begin{code}

private
 variable
  T T' : Universe

𝓛-lift : ∀ T {X : U ̇} {Y : V ̇} → (X → 𝓛 T Y) → (𝓛 T X → 𝓛 T Y)
𝓛-lift T f (P , i , φ) = (Σ \(p : P) → is-defined T (f (φ p))) ,
                          Σ-is-prop i (λ p → being-defined-is-a-prop T (f (φ p))) ,
                          λ σ → value T (f (φ (pr₁ σ))) (pr₂ σ)

𝓛- : ∀ T {X : U ̇} {Y : V ̇} → (X → Y) → 𝓛 T X → 𝓛 T Y
𝓛- T f (P , i , φ) = P , i , f ∘ φ

𝓛-id : ∀ T {X : U ̇} → 𝓛- T id ≡ id
𝓛-id {U} T {X} = refl {U ⊔ (T ⁺)} {𝓛 T X → 𝓛 T X}

𝓛-∘ : {X : U ̇} {Y : V ̇} {Z : W ̇} (f : X → Y) (g : Y → Z)
    → 𝓛- T (g ∘ f) ≡ 𝓛- T g ∘ 𝓛- T f
𝓛-∘ f g = refl

η-natural : {X : U ̇} {Y : V ̇} (f : X → Y) → η T ∘ f ≡ 𝓛- T f ∘ η T
η-natural f = refl

μ : (T : Universe) {X : U ̇} → 𝓛 T (𝓛 T X) → 𝓛 T X
μ {U} T {X} = 𝓛-lift T id

𝓛* : {X : U ̇} {Y : V ̇} (f : X → Y) → is-embedding f → 𝓛 T Y → 𝓛 (U ⊔ V ⊔ T) X
𝓛* f e (Q , j , γ) = (Σ \(q : Q) → fiber f (γ q)) ,
                      Σ-is-prop j (e ∘ γ) ,
                      λ p → pr₁ (pr₂ p)

μ* : (T T' : Universe) {X : U ̇} → funext T T → funext T' T' → funext T' U → funext U (U ⊔ (T' ⁺)) → propext T'
  → 𝓛 T (𝓛 T' X) → 𝓛 (U ⊔ T ⊔ (T' ⁺)) X
μ* {U} T T' {X} fe fe' fe'' fe''' pe = 𝓛* (η T') (η-is-embedding T' pe fe' fe'' fe''')

{-
μ-natural : (T T' : Universe) (fe : funext T T) (fe' : funext T' T') (fe'' : funext T' U) (fe''' : funext U (U ⊔ (T' ⁺))) (pe : propext T')
          → {X : U ̇} {Y : U ̇} (f : X → Y) → 𝓛- (U ⊔ T ⊔ (T' ⁺)) f ∘ μ T T' fe fe' fe'' fe''' pe
                                            ≡ μ T T' fe fe' fe'' fe''' pe ∘ 𝓛- T (𝓛- T' f)
μ-natural T T' fe fe' fe'' fe''' pe f = {!refl!}
-}

\end{code}

Lift monad to be continued in due course.

Added 8th November 2018.

\begin{code}

pus : (T : Universe) {X : U ̇} {P : T ̇} → 𝓛 T X → (P → 𝓛 T X)
pus T l p = l

sup : (T : Universe) {X : U ̇} {P : T ̇} → is-prop P → (P → 𝓛 T X) → 𝓛 T X
sup T {X} {P} i φ = μ T (P , i , φ)

{-
sup-adj : (T : Universe) {X : U ̇} (P : T ̇) (i : is-prop P) (φ : P → 𝓛 T X) (l : 𝓛 T X)
        → (_⊑_ T (sup T i φ) l) ≃ ((p : P) → _⊑_ T (φ p) l)
sup-adj = {!!}

sup-reflective : (T : Universe) {X : U ̇} (P : T ̇) (i : is-prop P) (φ : P → 𝓛 T X) (l : 𝓛 T X)
               → (p : P) → φ p ≡ sup T i φ
sup-reflective T P i φ l p = {!!}
-}

\end{code}

This has a connection with injectivity.
