Martin Escardo 2012.

We investigate coinduction and corecursion on ℕ∞, the generic
convergent sequence.

We show that the set ℕ∞ satisfies the following universal property for
a suitable coalgebra PRED : ℕ∞ → 𝟙 + ℕ∞, where 𝟙 is the singleton type
with an element *.

For every type X and every κ : X → 𝟙 + X there is a unique h : X → ℕ∞
such that

                        κ
             X ------------------> 𝟙 + X
             |                       |
             |                       |
          h  |                       | 𝟙 + h
             |                       |
             |                       |
             v                       v
             ℕ∞ -----------------> 𝟙 + ℕ∞
                       PRED

The maps κ and PRED are called coalgebras for the functor 𝟙 + (-),
and the above diagram says that h is a coalgebra morphism from p to
PRED.

In equational form, this is

             PRED ∘ h ＝ (𝟙 + h) ∘ κ,

which can be considered as a corecursive definition of h.  The map
PRED (a sort of predecessor function) is an isomorphism with
inverse SUCC (a sort of successor function). This follows from
Lambek's Lemma once the above universal property is established, but
we actually need to know this first in order to prove the universal
property.

             SUCC : 𝟙 + ℕ∞ → ℕ∞
             SUCC (in₀ *) = Zero
             SUCC (in₁ u) = Succ u

Using this fact, the above corecursive definition of h is equivalent
to:

             h ＝ SUCC ∘ (𝟙 + h) ∘ κ

or

             h(x) ＝ SUCC((𝟙 + h)(κ x)).

Now κ x is either of the form in₀ * or in₁ x' for a unique x' : X, and
hence the above equation amounts to

             h(x) ＝ Zero,           if κ x ＝ in₀ *,
             h(x) ＝ Succ (h x'),    if κ x ＝ in₁ x',

once we know the definition of 𝟙 + h. This shows more clearly how the
diagram can be considered as a (co)recursive definition of h, and
indicates how h may be constructed.

In order to show that any two functions that make the above diagram
commute are equal, that is, that the above two conditional equations
uniquely determine h, we develop a coinduction principle based on
bisimulations. This gives a technique for establishing equalities on
ℕ∞.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module CoNaturals.UniversalProperty (fe : FunExt) where

open import CoNaturals.Type
open import MLTT.Plus-Properties
open import MLTT.Spartan
open import MLTT.Two-Properties
open import Notation.CanonicalMap
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons-Properties

private
 fe₀ : funext 𝓤₀ 𝓤₀
 fe₀ = fe 𝓤₀ 𝓤₀

ZERO : 𝟙 + ℕ∞
ZERO = inl {𝓤₀} {𝓤₀} ⋆

PRED' : ℕ∞ → 𝟙 + ℕ∞
PRED' u = inr {𝓤₀} {𝓤₀} (Pred u)

PRED : ℕ∞ → 𝟙 + ℕ∞
PRED u = 𝟚-Cases (positivity u) ZERO (PRED' u)

PRED-Zero : PRED Zero ＝ ZERO
PRED-Zero = refl

PRED-Succ : (u : ℕ∞) → PRED(Succ u) ＝ inr u
PRED-Succ u = ap inr Pred-Succ

SUCC : 𝟙 {𝓤₀} + ℕ∞ → ℕ∞
SUCC(inl ⋆) = Zero
SUCC(inr u) = Succ u

PRED-SUCC : {y : 𝟙 + ℕ∞} → PRED(SUCC y) ＝ y
PRED-SUCC{inl ⋆} = refl
PRED-SUCC{inr u} = refl

SUCC-lc : {y z : 𝟙 + ℕ∞} → SUCC y ＝ SUCC z → y ＝ z
SUCC-lc {y} {z} r = y             ＝⟨ PRED-SUCC ⁻¹ ⟩
                    PRED (SUCC y) ＝⟨ ap PRED r ⟩
                    PRED (SUCC z) ＝⟨ PRED-SUCC ⟩
                    z             ∎

SUCC-PRED : {u : ℕ∞} → SUCC(PRED u) ＝ u
SUCC-PRED {u} = 𝟚-equality-cases l₀ l₁
 where
  l₀ : positivity u ＝ ₀ → SUCC(PRED u) ＝ u
  l₀ r = SUCC(PRED u) ＝⟨ ap SUCC c₀ ⟩
         Zero         ＝⟨ (is-Zero-equal-Zero fe₀ r)⁻¹ ⟩
         u            ∎
    where
     c₀ : PRED u ＝ ZERO
     c₀ = ap (𝟚-cases ZERO (PRED' u)) r

  l₁ : positivity u ＝ ₁ → SUCC(PRED u) ＝ u
  l₁ r = SUCC (PRED u) ＝⟨ ap SUCC c₀ ⟩
         Succ (Pred u) ＝⟨ (not-Zero-is-Succ fe₀ c₁)⁻¹ ⟩
         u             ∎

   where
     c₀ : PRED u ＝ PRED' u
     c₀ = ap (𝟚-cases ZERO (PRED' u)) r
     c₁ : u ≠ Zero
     c₁ s = equal-₀-different-from-₁(ap positivity s) r

PRED-lc : {u v : ℕ∞} → PRED u ＝ PRED v → u ＝ v
PRED-lc {u} {v} r = u             ＝⟨ SUCC-PRED ⁻¹ ⟩
                    SUCC (PRED u) ＝⟨ ap SUCC r ⟩
                    SUCC (PRED v) ＝⟨ SUCC-PRED ⟩
                    v             ∎

𝟙+ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝟙 + X → 𝟙 + Y
𝟙+ f (inl s) = inl {𝓤₀} s
𝟙+ f (inr x) = inr(f x)

𝟙+id-is-id : {X : 𝓤 ̇ } → 𝟙+ id ∼ id {𝓤} {𝟙 + X}
𝟙+id-is-id {𝓤} {X} (inl ⋆) = refl
𝟙+id-is-id {𝓤} {X} (inr x) = refl

is-homomorphism : {X : 𝓤 ̇ } → (X → 𝟙 + X) → (X → ℕ∞) → 𝓤 ̇
is-homomorphism c h = (PRED ∘ h ＝ (𝟙+ h) ∘ c)

id-homomorphism : is-homomorphism PRED id
id-homomorphism = dfunext fe₀ (λ u → (𝟙+id-is-id (PRED u))⁻¹)

coalg-mophism→ : {X : 𝓤 ̇ } (κ : X → 𝟙 + X) (h : X → ℕ∞)
               → is-homomorphism κ h
               → h ＝ SUCC ∘ (𝟙+ h) ∘ κ
coalg-mophism→ {𝓤} κ h a = dfunext (fe 𝓤 𝓤₀)
                             (λ x → h x               ＝⟨ SUCC-PRED ⁻¹ ⟩
                                    SUCC (PRED (h x)) ＝⟨ ap (λ - → SUCC(- x)) a ⟩
                                    SUCC (𝟙+ h (κ x)) ∎)

coalg-mophism← : {X : 𝓤 ̇ } (κ : X → 𝟙 + X) (h : X → ℕ∞)
               → h ＝ SUCC ∘ (𝟙+ h) ∘ κ
               → is-homomorphism κ h
coalg-mophism← {𝓤} κ h b = dfunext (fe 𝓤 𝓤₀)
                            (λ x → PRED (h x)                 ＝⟨ ap (λ - → PRED(- x)) b ⟩
                                   PRED ((SUCC ∘ 𝟙+ h ∘ κ) x) ＝⟨ PRED-SUCC ⟩
                                   𝟙+ h (κ x)                 ∎)

homomorphism-existence : {X : 𝓤 ̇ } (κ : X → 𝟙 + X)
                       → Σ h ꞉ (X → ℕ∞), is-homomorphism κ h
homomorphism-existence {𝓤} {X} κ = h , dfunext (fe 𝓤 𝓤₀) h-spec
 where
  q : 𝟙 + X → 𝟙 + X
  q(inl s) = inl s
  q(inr x) = κ x

  Q : ℕ → 𝟙 + X → 𝟙 + X
  Q 0 z = z
  Q(succ n) z = q(Q n z)

  E : 𝟙 + X → 𝟚
  E(inl s) = ₀
  E(inr x) = ₁

  hl : (z : 𝟙 + X) → E(q z) ＝ ₁ → E z ＝ ₁
  hl (inl s) r = r
  hl (inr x) r = refl

  h : X → ℕ∞
  h x = (λ i → E(Q(succ i) (inr x))) ,
        (λ i → ≤₂-criterion (hl(Q(succ i) (inr x))))

  h-spec : (x : X) → PRED(h x) ＝ (𝟙+ h)(κ x)
  h-spec x = equality-cases (κ x) l₀ l₁
   where
    l₀ : (s : 𝟙) → κ x ＝ inl s → PRED(h x) ＝ (𝟙+ h)(κ x)
    l₀ ⋆ r = PRED (h x) ＝⟨ ap PRED c ⟩
             PRED Zero  ＝⟨ PRED-Zero ⟩
             ZERO      ＝⟨ (ap (𝟙+ h) r)⁻¹ ⟩
             𝟙+ h (κ x) ∎
     where
      c : h x ＝ Zero
      c = is-Zero-equal-Zero fe₀ (ap E r)


    l₁ : (x' : X) → κ x ＝ inr x' → PRED(h x) ＝ (𝟙+ h)(κ x)
    l₁ x' r = PRED (h x) ＝⟨ ap PRED c₅ ⟩
              inr (h x') ＝⟨ (ap (𝟙+ h) r)⁻¹ ⟩
              𝟙+ h (κ x) ∎
     where
      c₁ : (n : ℕ) → q(Q n (inr x)) ＝ Q n (κ x)
      c₁ 0 = refl
      c₁ (succ n) = ap q (c₁ n)
      c₂ : (n : ℕ) → q(Q n (inr x)) ＝ Q n (inr x')
      c₂ n = q (Q n (inr x)) ＝⟨ c₁ n ⟩
             Q n (κ x)       ＝⟨ ap (Q n) r ⟩
             Q n (inr x')    ∎
      c₃ : (n : ℕ) → E(q(Q n (inr x))) ＝ E(Q n (inr x'))
      c₃ n = ap E (c₂ n)
      c₄ : (i : ℕ) → ι (h x) i ＝ ι (Succ (h x')) i
      c₄ 0  = c₃ 0
      c₄ (succ i) = c₃(succ i)
      c₅ : h x ＝ Succ (h x')
      c₅ = ℕ∞-to-ℕ→𝟚-lc fe₀ (dfunext fe₀ c₄)

ℕ∞-corec  : {X : 𝓤 ̇ } → (X → 𝟙 + X) → (X → ℕ∞)
ℕ∞-corec c = pr₁(homomorphism-existence c)

ℕ∞-corec-homomorphism : {X : 𝓤 ̇ } (κ : X → 𝟙 + X)
                      → is-homomorphism κ (ℕ∞-corec κ)
ℕ∞-corec-homomorphism κ = pr₂(homomorphism-existence κ)

\end{code}

We now discuss coinduction. We first define bisimulations.

\begin{code}

ℕ∞-bisimulation :(ℕ∞ → ℕ∞ → 𝓤 ̇ ) → 𝓤 ̇
ℕ∞-bisimulation R = (u v : ℕ∞) → R u v
                                → (positivity u ＝ positivity v)
                                ×  R (Pred u) (Pred v)

ℕ∞-coinduction : (R : ℕ∞ → ℕ∞ → 𝓤 ̇ )
               → ℕ∞-bisimulation R
               → (u v : ℕ∞) → R u v → u ＝ v
ℕ∞-coinduction R b u v r = ℕ∞-to-ℕ→𝟚-lc fe₀ (dfunext fe₀ (l u v r))
 where
  l : (u v : ℕ∞) → R u v → (i : ℕ) → ι u i ＝ ι v i
  l u v r 0 =  pr₁(b u v r)
  l u v r (succ i) = l (Pred u) (Pred v) (pr₂(b u v r)) i

\end{code}

To be able to use it for our purpose, we need to investigate
coalgebra homomorphisms in more detail.

\begin{code}

coalg-morphism-Zero : {X : 𝓤 ̇ } (κ : X → 𝟙 + X) (h : X → ℕ∞)
                    → is-homomorphism κ h
                    → (x : X) (s : 𝟙) → κ x ＝ inl s → h x ＝ Zero
coalg-morphism-Zero p h a x ⋆ κ = h x               ＝⟨ SUCC-PRED ⁻¹ ⟩
                                  SUCC (PRED (h x)) ＝⟨ ap SUCC c ⟩
                                  SUCC (inl ⋆)      ∎
 where
  c : PRED(h x) ＝ inl ⋆
  c = PRED (h x) ＝⟨ ap (λ - → - x) a ⟩
      𝟙+ h (p x) ＝⟨ ap (𝟙+ h) κ ⟩
      inl ⋆      ∎

Coalg-morphism-Zero : {X : 𝓤 ̇ } (κ : X → 𝟙 + X)
                    → (x : X) (s : 𝟙) → κ x ＝ inl s → ℕ∞-corec κ x ＝ Zero
Coalg-morphism-Zero κ = coalg-morphism-Zero κ (ℕ∞-corec κ) (ℕ∞-corec-homomorphism κ)

coalg-morphism-Succ : {X : 𝓤 ̇ }
                      (κ : X → 𝟙 + X) (h : X → ℕ∞)
                    → is-homomorphism κ h
                    → (x x' : X) → κ x ＝ inr x' → h x ＝ Succ (h x')
coalg-morphism-Succ κ h a x x' q = h x               ＝⟨ SUCC-PRED ⁻¹ ⟩
                                   SUCC (PRED (h x)) ＝⟨ ap SUCC c ⟩
                                   SUCC (inr (h x')) ∎
 where
  c : PRED(h x) ＝ inr(h x')
  c = PRED (h x) ＝⟨ ap (λ - → - x) a ⟩
      𝟙+ h (κ x) ＝⟨ ap (𝟙+ h) q ⟩
      inr (h x') ∎

Coalg-morphism-Succ : {X : 𝓤 ̇ } (κ : X → 𝟙 + X)
                    → (x x' : X) → κ x ＝ inr x' → ℕ∞-corec κ x ＝ Succ (ℕ∞-corec κ x')
Coalg-morphism-Succ κ = coalg-morphism-Succ κ (ℕ∞-corec κ) (ℕ∞-corec-homomorphism κ)

\end{code}

The following two technical lemmas are used to construct a
bisimulation:

\begin{code}

coalg-morphism-positivity : {X : 𝓤 ̇ }
                            (κ : X → 𝟙 + X) (f g : X → ℕ∞)
                          → is-homomorphism κ f
                          → is-homomorphism κ g
                          → (x : X) → positivity(f x) ＝ positivity(g x)
coalg-morphism-positivity {𝓤} {X} κ f g a b x = equality-cases (κ x) l₀ l₁
 where
  l₀ : (s : 𝟙) → κ x ＝ inl s → positivity(f x) ＝ positivity(g x)
  l₀ s q = positivity (f x) ＝⟨ ap positivity(coalg-morphism-Zero κ f a x s q) ⟩
           ₀                ＝⟨ (ap positivity(coalg-morphism-Zero κ g b x s q))⁻¹ ⟩
           positivity (g x) ∎

  l₁ : (x' : X) → κ x ＝ inr x' → positivity(f x) ＝ positivity(g x)
  l₁ x' q = positivity (f x)         ＝⟨ ap positivity(coalg-morphism-Succ κ f a x x' q) ⟩
            positivity (Succ (f x')) ＝⟨ (ap positivity(coalg-morphism-Succ κ g b x x' q))⁻¹ ⟩
            positivity (g x)         ∎

coalg-morphism-Pred : {X : 𝓤 ̇ }
                      (κ : X → 𝟙 + X) (f g : X → ℕ∞)
                    → is-homomorphism κ f
                    → is-homomorphism κ g
                    → (x : X) (u v : ℕ∞)
                    → u ＝ f x
                    → v ＝ g x
                    → Σ x' ꞉ X , (Pred u ＝ f x') × (Pred v ＝ g x')
coalg-morphism-Pred {𝓤} {X} κ f g a b x u v d e =
 equality-cases (κ x) l₀ l₁
 where
  l₀ : (s : 𝟙) → κ x ＝ inl s
     → Σ x' ꞉ X , (Pred u ＝ f x') ×  (Pred v ＝ g x')
  l₀ s q = x , (l f a u d , l g b v e)
   where
    l : (h : X → ℕ∞) → PRED ∘ h ＝ (𝟙+ h) ∘ κ
      → (u : ℕ∞) → u ＝ h x → Pred u ＝ h x
    l h a u d = Pred u ＝⟨ c₁ ⟩
                Zero   ＝⟨ c₀ ⁻¹ ⟩
                h x    ∎
     where
      c₀ : h x ＝ Zero
      c₀ = coalg-morphism-Zero κ h a x s q
      c₁ : Pred u ＝ Zero
      c₁ = ap Pred (u    ＝⟨ d ⟩
                    h x  ＝⟨ c₀ ⟩
                    Zero ∎)

  l₁ : (x' : X) → κ x ＝ inr x'
     → Σ x' ꞉ X , (Pred u ＝ f x') × (Pred v ＝ g x')
  l₁ x' q = x' , (l f a u d , l g b v e)
   where
    l : (h : X → ℕ∞) → PRED ∘ h ＝ (𝟙+ h) ∘ κ
      → (u : ℕ∞) → u ＝ h x → Pred u ＝ h x'
    l h a u d = Pred u     ＝⟨ ap Pred d ⟩
                Pred (h x) ＝⟨ ap Pred(coalg-morphism-Succ κ h a x x' q) ⟩
                h x'       ∎

\end{code}

We are finally able to prove the uniqueness of coalgebra homomorphisms
from κ to PRED.

\begin{code}

homomorphism-uniqueness : {X : 𝓤 ̇ }
                          (κ : X → 𝟙 + X) (f g : X → ℕ∞)
                        → is-homomorphism κ f
                        → is-homomorphism κ g
                        → f ＝ g
homomorphism-uniqueness {𝓤} {X} κ f g a b = dfunext (fe 𝓤 𝓤₀) l
 where
  R : ℕ∞ → ℕ∞ → 𝓤 ̇
  R u v = Σ x ꞉ X , (u ＝ f x) × (v ＝ g x)

  r : (x : X) → R (f x) (g x)
  r x = (x , refl , refl)

  R-positivity : (u v : ℕ∞) → R u v → positivity u ＝ positivity v
  R-positivity u v (x , c , d) = positivity u     ＝⟨ ap positivity c ⟩
                                 positivity (f x) ＝⟨ coalg-morphism-positivity κ f g a b x ⟩
                                 positivity (g x) ＝⟨ ap positivity (d ⁻¹) ⟩
                                 positivity v ∎

  R-Pred : (u v : ℕ∞) → R u v → R (Pred u) (Pred v)
  R-Pred u v (x , c , d) =
   (pr₁ l , pr₁(pr₂ l) , pr₂(pr₂ l))
   where
    l : Σ x' ꞉ X , (Pred u ＝ f x') × (Pred v ＝ g x')
    l = coalg-morphism-Pred κ f g a b x u v c d

  R-bisimulation : ℕ∞-bisimulation R
  R-bisimulation u v r = (R-positivity u v r) , (R-Pred u v r)

  l : f ∼ g
  l x = ℕ∞-coinduction R R-bisimulation (f x) (g x) (r x)

\end{code}

Putting existence and uniqueness together, we get that PRED is the final
coalgebra, as claimed:

\begin{code}

PRED-is-the-final-coalgebra : {X : 𝓤 ̇ }
  → (κ : X → 𝟙 + X) → Σ! h ꞉ (X → ℕ∞ ), is-homomorphism κ h
PRED-is-the-final-coalgebra κ = homomorphism-existence κ , homomorphism-uniqueness κ

\end{code}

There is more formalization work to do (2017): By now we know that Σ!
(a form of unique existence) is better captured by the contractibility
of a Σ type (added 13th July 2018):

\begin{code}

open import UF.Base
open import UF.Subsingletons

PRED-is-the-homotopy-final-coalgebra : {X : 𝓤 ̇ } (κ : X → 𝟙 + X)
                                     → ∃! h ꞉ (X → ℕ∞), is-homomorphism κ h
PRED-is-the-homotopy-final-coalgebra {𝓤} {X} κ = homomorphism-existence κ , γ
 where
  γ : (e : Σ h' ꞉ (X → ℕ∞), is-homomorphism κ h') → homomorphism-existence κ ＝ e
  γ (h' , r) = to-Σ-＝
                (homomorphism-uniqueness κ (ℕ∞-corec κ) h' (ℕ∞-corec-homomorphism κ) r ,
                 Π-is-set (fe 𝓤 𝓤₀)
                   (λ _ → +-is-set 𝟙 ℕ∞
                           (props-are-sets 𝟙-is-prop)
                           (ℕ∞-is-set fe₀)) _ _)

\end{code}
