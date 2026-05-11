Martin Escardo, 2017, written in Agda November 2019.

If X is discrete then

  (X + 𝟙) × Aut X ≃ Aut (X + 𝟙),

where

  Aut X := (X ≃ X)

is the type of automorphisms of the type X.

This is proved by Danielsson in

 http://www.cse.chalmers.se/~nad/listings/equality/Function-universe.html#[⊤⊎↔⊤⊎]⇔[⊤⊎×↔]

See also Coquand's

 https://github.com/simhu/cubical/blob/master/examples/finite.cub

and our

 https://www.cs.bham.ac.uk/~mhe/TypeTopology/PlusOneLC.html

More generally, for an arbitraty type X, we prove that

  co-derived-set (X + 𝟙) × Aut X ≃ Aut (X + 𝟙),

where the co-derived-set of a type is the subtype of isolated points.

In particular, if X is discrete (all its points are isolated), then we
get the "factorial equivalence"

  (X + 𝟙) × Aut X ≃ Aut (X + 𝟙).

On the other hand, if X is perfect (has no isolated points), then

  Aut X ≃ Aut (X + 𝟙),

This is the case, for example, if X is the circle S¹.

But if P is a proposition, then

  P + 𝟙 ≃ Aut (P + 𝟙).

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

\end{code}

We need functional extensionality (but not propositional
extensionality or univalence).

\begin{code}

module Factorial.Law (fe : FunExt) where

open import Factorial.Swap
open import MLTT.Plus-Properties
open import MLTT.Spartan
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.Retracts
open import UF.Subsingletons
open import UF.Sets

\end{code}

We refer to the set of isolated points as the co derived set (for
complement of the derived set, in the sense of Cantor, consisting of
the limit points, i.e. non-isolated points).

Recall that a point x : X is isolated if the identity type x ＝ y is
decidable for every y : X.

\begin{code}

co-derived-set : 𝓤 ̇ → 𝓤 ̇
co-derived-set X = Σ x ꞉ X , is-isolated x

cods-embedding : (X : 𝓤 ̇ ) → co-derived-set X → X
cods-embedding X = pr₁

cods-embedding-is-embedding : (X : 𝓤 ̇ ) → is-embedding (cods-embedding X)
cods-embedding-is-embedding X = pr₁-is-embedding (being-isolated-is-prop fe)

cods-embedding-is-equiv : (X : 𝓤 ̇ ) → is-discrete X → is-equiv (cods-embedding X)
cods-embedding-is-equiv X d = pr₁-is-equiv X is-isolated
                               (λ x → pointed-props-are-singletons (d x)
                                       (being-isolated-is-prop fe x))

≃-cods : (X : 𝓤 ̇ ) → is-discrete X → co-derived-set X ≃ X
≃-cods X d = cods-embedding X , cods-embedding-is-equiv X d

\end{code}

The co derived set of any type is indeed a set.

\begin{code}

cods-is-set : (X : 𝓤 ̇ ) → is-set (co-derived-set X)
cods-is-set X {x , i} = isolated-points-are-h-isolated
                         (x , i)
                         (embeddings-reflect-isolatedness
                           (cods-embedding X)
                           (cods-embedding-is-embedding X)
                           (x , i)
                           i)
\end{code}

Recall that a type is perfect if it has no isolated points.

\begin{code}

perfect-coderived-empty : (X : 𝓤 ̇ ) → is-perfect X → is-empty (co-derived-set X)
perfect-coderived-empty X i (x , j) = i (x , j)

perfect-coderived-singleton : (X : 𝓤 ̇ ) → is-perfect X → is-singleton (co-derived-set (X + 𝟙 {𝓥}))
perfect-coderived-singleton X i = (inr ⋆ , new-point-is-isolated) , γ
 where
  γ : (c : co-derived-set (X + 𝟙)) → inr ⋆ , new-point-is-isolated ＝ c
  γ (inl x , j) = 𝟘-elim (i (x , a))
   where
    a : is-isolated x
    a = embeddings-reflect-isolatedness inl (inl-is-embedding X 𝟙) x j
  γ (inr ⋆ , j) = to-Σ-＝' (being-isolated-is-prop fe (inr ⋆) new-point-is-isolated j)

\end{code}

For a type A, denote by A' the co-derived set of A.

Then we get a map

  (Y+𝟙)' × (X ≃ Y) → (X+𝟙 ≃ Y+𝟙),

where the choice of isolated point a:Y+𝟙 controls which equivalence
X+𝟙≃Y+𝟙 we get from the equivalence f: X≃Y:

       f+𝟙       swap (a , inr (⋆))
  X+𝟙 ----> Y+𝟙 --------------------> Y+𝟙

The claim is that the above map is an equivalence.

We construct/prove this in four steps:

(1)  (X ≃ Y)
    ≃ Σ f ꞉ X+𝟙 ≃ Y+𝟙 , f (inr ⋆) ＝ inr ⋆

Hence

(2) (Y+𝟙)' × (X ≃ Y)
  ≃ (Y+𝟙)' × Σ f ꞉ X+𝟙 ≃ Y+𝟙 , f (inr ⋆) ＝ inr ⋆

Also

(3) (Y+𝟙)' × (Σ f ꞉ X+𝟙 ≃ Y+𝟙 , f (inr ⋆) ＝ inr ⋆)
  ≃ (X+𝟙 ≃ Y+𝟙)

And therefore

(4) (Y+𝟙)' × (X ≃ Y)
  ≃ (X+𝟙 ≃ Y+𝟙)

\begin{code}

module factorial-steps
        {𝓤 𝓥 : Universe}
        (𝓦 𝓣 : Universe)
        (X : 𝓤 ̇ )
        (Y : 𝓥 ̇ )
       where

 X+𝟙 = X + 𝟙 {𝓦}
 Y+𝟙 = Y + 𝟙 {𝓣}

\end{code}

In the following, we use the fact that if f (inr ⋆) ＝ inr ⋆ for a
function, f : X+𝟙 → Y+𝟙, then f (inl x) is of the form inl y
(inl-preservation).

\begin{code}

 step₀ : (f : X+𝟙 → Y+𝟙)
       → f (inr ⋆) ＝ inr ⋆
       → is-equiv f
       → Σ f' ꞉ (X → Y), is-equiv f' × (f ∼ +functor f' unique-to-𝟙)
 step₀ f p i = γ (equivs-are-qinvs f i)
  where
   γ : qinv f → Σ f' ꞉ (X → Y), is-equiv f' × (f ∼ +functor f' unique-to-𝟙)
   γ (g , η , ε) = f' , qinvs-are-equivs f' (g' , η' , ε') , h
    where
     f' : X → Y
     f' x = pr₁ (inl-preservation f p (sections-are-lc f (g , η)) x)

     a : (x : X) → f (inl x) ＝ inl (f' x)
     a x = pr₂ (inl-preservation f p (sections-are-lc f (g , η)) x)

     q = g (inr ⋆)     ＝⟨ (ap g p)⁻¹ ⟩
         g (f (inr ⋆)) ＝⟨ η (inr ⋆) ⟩
         inr ⋆         ∎

     g' : Y → X
     g' x = pr₁ (inl-preservation g q (sections-are-lc g (f , ε)) x)

     b : (y : Y) → g (inl y) ＝ inl (g' y)
     b y = pr₂ (inl-preservation g q (sections-are-lc g (f , ε)) y)

     η' : g' ∘ f' ∼ id
     η' x = inl-lc (inl (g' (f' x)) ＝⟨ (b (f' x))⁻¹ ⟩
                    g (inl (f' x))  ＝⟨ (ap g (a x))⁻¹ ⟩
                    g (f (inl x))   ＝⟨ η (inl x) ⟩
                    inl x           ∎)

     ε' : f' ∘ g' ∼ id
     ε' y = inl-lc (inl (f' (g' y)) ＝⟨ (a (g' y))⁻¹ ⟩
                    f (inl (g' y))  ＝⟨ (ap f (b y))⁻¹ ⟩
                    f (g (inl y))   ＝⟨ ε (inl y) ⟩
                    inl y           ∎)

     h : f ∼ +functor f' unique-to-𝟙
     h (inl x) = a x
     h (inr ⋆) = p

 step₁ : (X ≃ Y) ≃ (Σ f ꞉ X+𝟙 ≃ Y+𝟙 , ⌜ f ⌝ (inr ⋆) ＝ inr ⋆)
 step₁ = qinveq φ (γ , η , ε)
  where
   a : (g : X → Y) → qinv g → Y+𝟙 → X+𝟙
   a g (g' , η , ε) = +functor g' unique-to-𝟙

   b : (g : X → Y) (q : qinv g) → a g q ∘ +functor g unique-to-𝟙 ∼ id
   b g (g' , η , ε) (inl x) = ap inl (η x)
   b g (g' , η , ε) (inr ⋆) = refl

   c : (g : X → Y) (q : qinv g) → +functor g unique-to-𝟙 ∘ a g q ∼ id
   c g (g' , η , ε) (inl y) = ap inl (ε y)
   c g (g' , η , ε) (inr ⋆) = refl

   d : (g : X → Y) → qinv g → is-equiv (+functor g unique-to-𝟙)
   d g q = qinvs-are-equivs (+functor g unique-to-𝟙) (a g q , b g q , c g q)

   φ : (X ≃ Y) → Σ e ꞉ X+𝟙 ≃ Y+𝟙 , ⌜ e ⌝ (inr ⋆) ＝ inr ⋆
   φ (g , i) = (+functor g unique-to-𝟙 , d g (equivs-are-qinvs g i)) , refl

   γ : (Σ e ꞉ X+𝟙 ≃ Y+𝟙 , ⌜ e ⌝ (inr ⋆) ＝ inr ⋆) → (X ≃ Y)
   γ ((f , i) , p) = pr₁ (step₀ f p i) , pr₁ (pr₂ (step₀ f p i))

   η : γ ∘ φ ∼ id
   η (g , i) = to-Σ-＝ (refl , being-equiv-is-prop fe g _ i)

   ε : φ ∘ γ ∼ id
   ε ((f , i) , p) = to-Σ-＝
                      (to-subtype-＝ (being-equiv-is-prop fe) r ,
                      isolated-points-are-h-isolated (f (inr ⋆))
                       (equivs-preserve-isolatedness f i (inr ⋆)
                         new-point-is-isolated) _ p)
    where
     s : f ∼ pr₁ (pr₁ ((φ ∘ γ) ((f , i) , p)))
     s (inl x) = pr₂ (pr₂ (step₀ f p i)) (inl x)
     s (inr ⋆) = p

     r : pr₁ (pr₁ ((φ ∘ γ) ((f , i) , p))) ＝ f
     r = dfunext (fe _ _) (λ z → (s z)⁻¹)

 step₂ : co-derived-set (Y+𝟙) × (X ≃ Y)
       ≃ co-derived-set (Y+𝟙) × (Σ e ꞉ X+𝟙 ≃ Y+𝟙 , ⌜ e ⌝ (inr ⋆) ＝ inr ⋆)
 step₂ = ×-cong (≃-refl (co-derived-set (Y+𝟙))) step₁

 step₃ : (co-derived-set (Y+𝟙) × (Σ e ꞉ X+𝟙 ≃ Y+𝟙 , ⌜ e ⌝ (inr ⋆) ＝ inr ⋆))
       ≃ (X+𝟙 ≃ Y+𝟙)
 step₃ = qinveq φ (γ , η , ε)
  where
   A = co-derived-set (Y+𝟙) × (Σ e ꞉ X+𝟙 ≃ Y+𝟙 , ⌜ e ⌝ (inr ⋆) ＝ inr ⋆)
   B = X+𝟙 ≃ Y+𝟙

   φ : A → B
   φ ((t , i) , ((f , j) , p)) = g , k
    where
     g : X+𝟙 → Y+𝟙
     g = swap t (inr ⋆) i new-point-is-isolated ∘ f

     k : is-equiv g
     k = ∘-is-equiv-abstract j (swap-is-equiv t (inr ⋆) i new-point-is-isolated)

   γ : B → A
   γ (g , k) = (t , i) , ((f , j) , p)
    where
     t : Y+𝟙
     t = g (inr ⋆)

     i : is-isolated t
     i = equivs-preserve-isolatedness g k (inr ⋆) new-point-is-isolated

     f : X+𝟙 → Y+𝟙
     f = swap t (inr ⋆) i new-point-is-isolated ∘ g

     j : is-equiv f
     j = ∘-is-equiv-abstract k (swap-is-equiv t (inr ⋆) i new-point-is-isolated)

     p : f (inr ⋆) ＝ inr ⋆
     p = swap-equation₀ t (inr ⋆) i new-point-is-isolated

   η : γ ∘ φ ∼ id
   η ((t , i) , ((f , j) , p)) = s
    where
     g : X+𝟙 → Y+𝟙
     g = swap t (inr ⋆) i new-point-is-isolated ∘ f

     k : is-equiv g
     k = ∘-is-equiv-abstract j (swap-is-equiv t (inr ⋆) i new-point-is-isolated)

     t' : Y+𝟙
     t' = g (inr ⋆)

     i' : is-isolated t'
     i' = equivs-preserve-isolatedness g k (inr ⋆) new-point-is-isolated

     q : t' ＝ t
     q = g (inr ⋆)                                      ＝⟨ a ⟩
         swap t (inr ⋆) i new-point-is-isolated (inr ⋆) ＝⟨ b ⟩
         t                                              ∎
      where
       a = ap (swap t (inr ⋆) i new-point-is-isolated) p
       b = swap-equation₁ t (inr ⋆) i new-point-is-isolated

     r : (t' , i') ＝ (t , i)
     r = to-subtype-＝ (being-isolated-is-prop fe) q

     f' : X+𝟙 → Y+𝟙
     f' = swap t' (inr ⋆) i' new-point-is-isolated ∘ g

     j' : is-equiv f'
     j' = ∘-is-equiv-abstract
           k
           (swap-is-equiv t' (inr ⋆) i' new-point-is-isolated)

     h : f' ∼ f
     h z = swap t' (inr ⋆) i' new-point-is-isolated
            (swap t (inr ⋆) i new-point-is-isolated (f z))  ＝⟨ a ⟩
           swap t (inr ⋆) i new-point-is-isolated
            (swap t (inr ⋆) i new-point-is-isolated (f z))  ＝⟨ b ⟩

           f z                                              ∎
      where
       ψ : co-derived-set (Y+𝟙) → Y+𝟙
       ψ (t' , i') = swap t' (inr ⋆) i' new-point-is-isolated
                      (swap t (inr ⋆) i new-point-is-isolated (f z))
       a = ap ψ r
       b = swap-involutive t (inr ⋆) i new-point-is-isolated (f z)

     m : is-isolated (f (inr ⋆))
     m = equivs-preserve-isolatedness f j (inr ⋆) new-point-is-isolated

     n : {t : Y+𝟙} → is-prop (f (inr ⋆) ＝ t)
     n = isolated-points-are-h-isolated (f (inr ⋆)) m

     o : f' , j' ＝ f , j
     o = to-subtype-＝ (being-equiv-is-prop fe) (dfunext (fe _ _) h)

     p' : f' (inr ⋆) ＝ inr ⋆
     p' = swap-equation₀ t' (inr ⋆) i' new-point-is-isolated

     s : ((t' , i') , ((f' , j') , p')) ＝ ((t , i) , ((f , j) , p))
     s = to-×-＝ r (to-Σ-＝ (o , n top' p))
      where
       top' = transport (λ - → ⌜ - ⌝ (inr ⋆) ＝ inr ⋆) o p'

   ε : φ ∘ γ ∼ id
   ε (g , k) = r
    where
     z : Y+𝟙
     z = g (inr ⋆)

     i : is-isolated z
     i = equivs-preserve-isolatedness g k (inr ⋆) new-point-is-isolated

     h : (swap (g (inr ⋆)) (inr ⋆) i new-point-is-isolated)
       ∘ (swap (g (inr ⋆)) (inr ⋆) i new-point-is-isolated)
       ∘ g
       ∼ g
     h = swap-involutive z (inr ⋆) i new-point-is-isolated ∘ g

     r : φ (γ (g , k)) ＝ (g , k)
     r = to-Σ-＝ (dfunext (fe _ _) h , being-equiv-is-prop fe g _ k)

 step₄ : co-derived-set (Y+𝟙) × (X ≃ Y) ≃ (X+𝟙 ≃ Y+𝟙)
 step₄ = step₂ ● step₃

\end{code}

This is the end of the submodule, which has the following corollaries:

\begin{code}

general-factorial : (X : 𝓤 ̇ ) → co-derived-set (X + 𝟙) × Aut X ≃ Aut (X + 𝟙)
general-factorial {𝓤} X = factorial-steps.step₄ 𝓤 𝓤 X X

discrete-factorial : (X : 𝓤 ̇ )
                   → is-discrete X
                   → (X + 𝟙) × Aut X ≃ Aut (X + 𝟙)
discrete-factorial X d = γ
 where
 i = ×-cong
      (≃-sym (≃-cods (X + 𝟙)
      ( +-is-discrete d 𝟙-is-discrete))) (≃-refl (Aut X))

 γ = (X + 𝟙) × Aut X                ≃⟨ i ⟩
     co-derived-set (X + 𝟙) × Aut X ≃⟨ general-factorial X ⟩
     Aut (X + 𝟙)                    ■

perfect-factorial : (X : 𝓤 ̇ )
                  → is-perfect X
                  → Aut X ≃ Aut (X + 𝟙)
perfect-factorial {𝓤} X i =
  Aut X                          ≃⟨ I ⟩
  𝟙 × Aut X                      ≃⟨ II ⟩
  co-derived-set (X + 𝟙) × Aut X ≃⟨ III ⟩
  Aut (X + 𝟙)                    ■
   where
    I   =  ≃-sym (𝟙-lneutral {𝓤} {𝓤})
    II  = ×-cong (≃-sym (singleton-≃-𝟙 (perfect-coderived-singleton X i))) (≃-refl (Aut X))
    III = general-factorial X

\end{code}

Exercise. Conclude that the map (-)+𝟙 : 𝓤 ̇ → 𝓤 ̇, although it is
left-cancellable, is not an embedding, but that it is an embedding
when restricted to perfect types.

We should not forget the (trivial) "base case":

\begin{code}

factorial-base : 𝟙 {𝓥} ≃ Aut (𝟘 {𝓤})
factorial-base = f , ((g , η) , (g , ε))
 where
  f : 𝟙 → Aut 𝟘
  f _ = id , ((id , (λ _ → refl)) , (id , (λ _ → refl)))

  g : Aut 𝟘 → 𝟙
  g = unique-to-𝟙

  η : (e : Aut 𝟘) → f (g e) ＝ e
  η _ = to-subtype-＝
         (being-equiv-is-prop fe)
         (dfunext (fe _ _) (λ y → 𝟘-elim y))

  ε : (x : 𝟙) → g (f x) ＝ x
  ε ⋆ = refl

\end{code}

Added 21st November 2022.

\begin{code}

Aut-of-prop-is-singleton : (P : 𝓤 ̇ )
                         → is-prop P
                         → is-singleton (Aut P)
Aut-of-prop-is-singleton P i = ≃-refl P , h
 where
  h : (e : P ≃ P) → ≃-refl P ＝ e
  h (f , _) = to-subtype-＝
                (being-equiv-is-prop fe)
                (dfunext (fe _ _) (λ p → i p (f p)))

factorial-base-generalized : (P : 𝓤 ̇ )
                           → is-prop P
                           → 𝟙 {𝓥} ≃ Aut P
factorial-base-generalized P i = 𝟙-≃-singleton (Aut-of-prop-is-singleton P i)

propositional-factorial : (P : 𝓤 ̇ )
                        → is-prop P
                        → (P + 𝟙) ≃ Aut (P + 𝟙)
propositional-factorial {𝓤} P i =
  P + 𝟙             ≃⟨ I ⟩
  (P + 𝟙) × (𝟙 {𝓤}) ≃⟨ II ⟩
  (P + 𝟙) × Aut P   ≃⟨ III ⟩
  Aut (P + 𝟙)       ■
   where
    I   = ≃-sym 𝟙-rneutral
    II  = ×-cong (≃-refl (P + 𝟙)) (factorial-base-generalized P i)
    III = discrete-factorial P (props-are-discrete i)

\end{code}

Is the converse also true?
