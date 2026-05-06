Martin Escardo 2011, 2017, 2018, 2020.

We define and study totally separated types (which could also have
been called 𝟚-separated types). Most of the material in this file is
from January 2018.

The terminology "totally separated" comes from topology, where it
means that the clopens separate the points. Here the maps into 𝟚
separate the points, formulated in a positive way.

Any type has a totally separated reflection, assuming function
extensionality and propositional truncations.

All the simple types (those obtained from 𝟚 and ℕ by iterating
function spaces) are totally separated (see the module
SimpleTypes). This is because the totally separated types form an
exponential ideal. Moreover, Π Y is totally separated for any family
Y : X → U provided Y x is totally separated for all x : X. This
assumes function extensionality.

In particular, the Cantor and Baire types ℕ → 𝟚 and ℕ → ℕ are totally
separated (like in topology).

Closure under Σ fails in general. However, we have closure under _×_,
and ℕ∞ (defined with Σ) is totally separated (proved in the module
GenericConvergentSequence).

A counter-example to closure under Σ (from 2012) is in the file
FailureOfTotalSeparatedness.

This is the "compactification" of ℕ with two points at infinity:

   Σ u ꞉ ℕ∞ , u ＝ ∞ → 𝟚.

If there is a 𝟚-valued function separating the two points at infinity,
then WLPO holds. (The totally separated reflection of this type should
be ℕ∞ if ¬ WLPO holds.)

(In the context of topology, I learned this example from the late
Klaus Keimel (but the rendering in type theory is mine), where it is a
T₁, non-T₂, and non totally separated space which is zero dimensional
(has a base of clopen sets), and where the intersection of two compact
subsets need not be compact. The failure of the Hausdorff property is
with the two points an infinity, which can't be separated by disjoint
open neighbourhoods.)

The total separatedness of the reals (of any kind) should also give a
taboo. All non-sets fail (without the need of taboos) to be totally
separated, because totally separated spaces are sets.

Total separatedness is also characterized as the tightness of a
certain apartness relation that can be defined in any type.

We also show how to construct the tight reflection of any type
equipped with an apartness relation, given by a universal strongly
extensional map into a tight apartness type. Any type with a tight
apartness relation is a set, and so this reflection is always a set.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module TypeTopology.TotallySeparated where

open import MLTT.Spartan
open import MLTT.Two-Properties
open import NotionsOfDecidability.Complemented
open import UF.Base
open import UF.DiscreteAndSeparated hiding (tight)
open import UF.Embeddings
open import UF.Equiv
open import UF.FunExt
open import UF.Hedberg
open import UF.LeftCancellable
open import UF.Lower-FunExt
open import UF.NotNotStablePropositions
open import UF.PropTrunc
open import UF.Retracts
open import UF.Sets
open import UF.Sets-Properties
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

An equality defined by a Leibniz principle with 𝟚-valued functions:

\begin{code}

_＝₂_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
x ＝₂ y = (p : type-of x → 𝟚) → p x ＝ p y

＝₂-is-prop-valued : funext 𝓤 𝓤₀
                  → (X : 𝓤 ̇ ) (x y : X) → is-prop (x ＝₂ y)
＝₂-is-prop-valued fe X x y = Π-is-prop fe (λ p → 𝟚-is-set)

\end{code}

In topological models, maps into 𝟚 classify clopens, and so total
separatedness amounts to "the clopens separate the points" in the
sense that any two points with the same clopen neighbourhoods are
equal. This notion in topology is called total separatedness. Notice
that we are not referring to homotopical models in this discussion.

\begin{code}

is-totally-separated : 𝓤 ̇ → 𝓤 ̇
is-totally-separated X = {x y : X} → x ＝₂ y → x ＝ y

\end{code}

Synonym, emphasizing that we can use other types as separators:

\begin{code}

𝟚-separated : 𝓤 ̇ → 𝓤 ̇
𝟚-separated = is-totally-separated

\end{code}

We now define an alternative characterization of total separatedness
(added December 11th 2020), still using the equivalence relation ＝₂,
and also motivated by topological considerations, namely that the
quasi component of a point of a topological space is the intersection
of all clopen sets containing x, and a space is totally separated if
the quasi-components are singletons:

\begin{code}

quasi-component : {X : 𝓤 ̇ } → X → 𝓤 ̇
quasi-component {𝓤} {X} x = Σ y ꞉ X , x ＝₂ y

quasi-component-canonical-point : {X : 𝓤 ̇ } (x : X) → quasi-component x
quasi-component-canonical-point {𝓤} {X} x = (x , λ p → refl)

\end{code}

The alternative characterization of total separatedness is that the
quasi-component of any point is a subsingleton, and hence a singleton:

\begin{code}

is-totally-separated₁ : 𝓤 ̇ → 𝓤 ̇
is-totally-separated₁ X = (x : X) → is-prop (quasi-component x)

totally-separated-gives-totally-separated₁ : funext 𝓤 𝓤₀
                                           → {X : 𝓤 ̇ }
                                           → is-totally-separated X
                                           → is-totally-separated₁ X
totally-separated-gives-totally-separated₁ fe {X} ts x (y , a) (z , b) = γ
 where
  c : y ＝₂ z
  c p = p y ＝⟨ (a p)⁻¹ ⟩
        p x ＝⟨ b p ⟩
        p z ∎

  q : y ＝ z
  q = ts c

  γ : (y , a) ＝ (z , b)
  γ = to-subtype-＝ (＝₂-is-prop-valued fe X x) q

totally-separated₁-types-are-totally-separated : {X : 𝓤 ̇ }
                                               → is-totally-separated₁ X
                                               → is-totally-separated X
totally-separated₁-types-are-totally-separated {𝓤} {X} τ {x} {y} ϕ = γ
 where
  a b : quasi-component x
  a = x , λ p → refl
  b = y , ϕ

  e : a ＝ b
  e = τ x a b

  γ : x ＝ y
  γ = ap pr₁ e

\end{code}

A third formulation of the notion of total separatedness, as the
tightness of a certain apartness relation, is given below.

Excluded middle implies that all sets are discrete and hence totally
separated:

\begin{code}

discrete-types-are-totally-separated : {X : 𝓤 ̇ }
                                     → is-discrete X
                                     → is-totally-separated X
discrete-types-are-totally-separated {𝓤} {X} d {x} {y} α = g
 where
  p : X → 𝟚
  p = pr₁ (characteristic-function (d x))

  φ : (y : X) → (p y ＝ ₀ → x ＝ y) × (p y ＝ ₁ → ¬ (x ＝ y))
  φ = pr₂ (characteristic-function (d x))

  b : p x ＝ ₀
  b = different-from-₁-equal-₀ (λ s → pr₂ (φ x) s refl)

  a : p y ＝ ₀
  a = p y ＝⟨ (α p)⁻¹ ⟩
      p x ＝⟨ b ⟩
      ₀   ∎

  g : x ＝ y
  g = pr₁ (φ y) a

\end{code}

The converse fails: by the results below, e.g. (ℕ → 𝟚) is totally
separated, but its discreteness amounts to WLPO.

Totally separated spaces are closed under retracts:

\begin{code}

retract-of-totally-separated : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                             → retract Y of X
                             → is-totally-separated X
                             → is-totally-separated Y
retract-of-totally-separated (r , s , rs) τ {y} {y'} α = section-lc s (r , rs) h
 where
  h : s y ＝ s y'
  h = τ (λ p → α (p ∘ s))

equiv-to-totally-separated : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                           → X ≃ Y
                           → is-totally-separated X
                           → is-totally-separated Y
equiv-to-totally-separated 𝕗 = retract-of-totally-separated (≃-gives-▷ 𝕗)

\end{code}

Recall that a type is called ¬¬-separated if the doubly negated equality
of any two element implies their equality, and that such a type is a
set.

\begin{code}

totally-separated-types-are-¬¬-separated : (X : 𝓤 ̇ )
                                         → is-totally-separated X
                                         → is-¬¬-separated X
totally-separated-types-are-¬¬-separated X τ = g
 where
  g : (x y : X) → ¬¬ (x ＝ y) → x ＝ y
  g x y φ  = τ h
   where
    a : (p : X → 𝟚) → ¬¬ (p x ＝ p y)
    a p = ¬¬-functor (ap p {x} {y}) φ

    h : (p : X → 𝟚) → p x ＝ p y
    h p = 𝟚-is-¬¬-separated (p x) (p y) (a p)

totally-separated-types-are-sets : funext 𝓤 𝓤₀
                                 → (X : 𝓤 ̇ )
                                 → is-totally-separated X
                                 → is-set X
totally-separated-types-are-sets fe X t =
 ¬¬-separated-types-are-sets fe (totally-separated-types-are-¬¬-separated X t)

being-totally-separated-is-prop : funext 𝓤 𝓤
                                → (X : 𝓤 ̇ )
                                → is-prop (is-totally-separated X)
being-totally-separated-is-prop {𝓤} fe X = γ
 where
  p : is-totally-separated X → is-prop (is-totally-separated X)
  p t = implicit-Π-is-prop fe (λ y →
        implicit-Π-is-prop fe (λ x →
        Π-is-prop          fe (λ p → totally-separated-types-are-sets
                                      (lower-funext 𝓤 𝓤 fe) X t)))

  γ : is-prop (is-totally-separated X)
  γ = prop-criterion p

\end{code}

The type of propositions is a set, but its total separatedness implies
excluded middle. In fact, its ¬¬-separatedness already implies
excluded middle:

\begin{code}

open import UF.ClassicalLogic

Ω-¬¬-separated-gives-DNE : propext 𝓤
                         → funext 𝓤 𝓤
                         → is-¬¬-separated (Ω 𝓤)
                         → DNE 𝓤
Ω-¬¬-separated-gives-DNE {𝓤} pe fe Ω-is-¬¬-separated P P-is-prop not-not-P = d
 where
  p : Ω 𝓤
  p = (P , P-is-prop)

  b : ¬¬ (p ＝ ⊤)
  b = ¬¬-functor (holds-gives-equal-⊤ pe fe p) not-not-P

  c : p ＝ ⊤
  c = Ω-is-¬¬-separated p ⊤ b

  d : P
  d = equal-⊤-gives-holds p c

Ω-¬¬-separated-gives-EM : propext 𝓤
                        → funext 𝓤 𝓤
                        → is-¬¬-separated (Ω 𝓤)
                        → EM 𝓤
Ω-¬¬-separated-gives-EM {𝓤} pe fe Ω-is-¬¬-separated =
  DNE-gives-EM
   (lower-funext 𝓤 𝓤 fe)
   (Ω-¬¬-separated-gives-DNE pe fe Ω-is-¬¬-separated)

Ω-totally-separated-gives-EM : propext 𝓤
                             → funext 𝓤 𝓤
                             → is-totally-separated (Ω 𝓤)
                             → EM 𝓤
Ω-totally-separated-gives-EM {𝓤} pe fe Ω-is-totally-separated =
 Ω-¬¬-separated-gives-EM pe fe
  (totally-separated-types-are-¬¬-separated (Ω 𝓤) Ω-is-totally-separated)

\end{code}

Old proof, which by-passes the step via ¬¬-separatedness and has a
different extensionality hypothesis:

\begin{code}

totally-separated-types-are-sets' : funext 𝓤 𝓤₀
                                  → (X : 𝓤 ̇ )
                                  → is-totally-separated X
                                  → is-set X
totally-separated-types-are-sets' fe X t = Id-collapsibles-are-sets h
 where
  f : {x y : X} → x ＝ y → x ＝ y
  f r = t(λ p → ap p r)

  b : {x y : X} (φ γ : (p : X → 𝟚) → p x ＝ p y) → φ ＝ γ
  b φ γ = dfunext fe (λ p → discrete-types-are-sets 𝟚-is-discrete (φ p) (γ p))

  c : {x y : X} (r s : x ＝ y) → (λ p → ap p r) ＝ (λ p → ap p s)
  c r s = b(λ p → ap p r) (λ p → ap p s)

  g : {x y : X} → wconstant(f {x} {y})
  g r s = ap t (c r s)

  h : Id-collapsible X
  h {x} {y} = f , g

\end{code}

As discussed above, we don't have general closure under Σ, but we have
the following particular cases:

\begin{code}

×-totally-separated : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                    → is-totally-separated X
                    → is-totally-separated Y
                    → is-totally-separated (X × Y)
×-totally-separated X Y t u {a , b} {x , y} φ =
 to-×-＝
   (t (λ (p : X → 𝟚) → φ (λ ((x , y) : X × Y) → p x)))
   (u (λ (q : Y → 𝟚) → φ (λ ((x , y) : X × Y) → q y)))

Σ-is-totally-separated-if-index-type-is-discrete
 : (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
 → is-discrete X
 → ((x : X) → is-totally-separated (Y x))
 → is-totally-separated (Σ Y)
Σ-is-totally-separated-if-index-type-is-discrete X Y d t {a , b} {x , y} φ
 = γ
 where
  r : a ＝ x
  r = discrete-types-are-totally-separated d (λ p → φ (λ z → p (pr₁ z)))

  s₂ : transport Y r b ＝₂ y
  s₂ q = g
   where
    f : {u : X} → (u ＝ x) + ¬ (u ＝ x) → Y u → 𝟚
    f (inl m) v = q (transport Y m v)
    f (inr _) v = ₀ --<-- What we choose here is irrelevant.

    p : Σ Y → 𝟚
    p (u , v) = f (d u x) v

    g = q (transport Y r b)    ＝⟨ (ap (λ - → f - b) (discrete-inl d a x r))⁻¹ ⟩
        p (a , b)              ＝⟨ φ p ⟩
        p (x , y)              ＝⟨ ap (λ - → f - y) (discrete-inl d x x refl) ⟩
        q (transport Y refl y) ∎

  s : transport Y r b ＝ y
  s = t x s₂

  γ : (a , b) ＝ (x , y)
  γ = to-Σ-＝ (r , s)

\end{code}

Maybe this can be further generalized by replacing the discreteness of X
with the assumption that

  (x : X) (q : Y x → 𝟚) → Σ p ꞉ Σ Y → 𝟚 , (y : Y x) → q y ＝ p (x , y).

Then the previous few functions would be a particular case of this.

See also the module SigmaDiscreteAndTotallySeparated.

The following can also be considered as a special case of Σ (indexed
by the type 𝟚):

\begin{code}

+-totally-separated : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                    → is-totally-separated X
                    → is-totally-separated Y
                    → is-totally-separated (X + Y)
+-totally-separated X Y t u {inl x} {inl x'} φ =
    ap inl (t (λ p → φ (cases p (λ (_ : Y) → ₀))))
+-totally-separated X Y t u {inl x} {inr y} φ =
    𝟘-elim (zero-is-not-one (φ (cases (λ _ → ₀) (λ _ → ₁))))
+-totally-separated X Y t u {inr y} {inl x} φ =
    𝟘-elim (zero-is-not-one (φ (cases (λ _ → ₁) (λ _ → ₀))))
+-totally-separated X Y t u {inr y} {inr y'} φ =
    ap inr (u (λ p → φ (cases (λ (_ : X) → ₀) p)))

\end{code}

The Cantor type ℕ → 𝟚 is totally separated:

\begin{code}

𝟚-is-totally-separated : is-totally-separated 𝟚
𝟚-is-totally-separated e = e id

Π-is-totally-separated : funext 𝓤 𝓥
                       → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                       → ((x : X) → is-totally-separated (Y x))
                       → is-totally-separated (Π Y)
Π-is-totally-separated fe {X} {Y} t {f} {g} e = dfunext fe h
 where
  P : (x : X) (p : Y x → 𝟚) → Π Y → 𝟚
  P x p f = p (f x)

  h : (x : X) → f x ＝ g x
  h x = t x (λ p → e (P x p))

Cantor-is-totally-separated : funext 𝓤₀ 𝓤₀ → is-totally-separated (ℕ → 𝟚)
Cantor-is-totally-separated fe =
 Π-is-totally-separated fe (λ n → 𝟚-is-totally-separated)

ℕ-is-totally-separated : is-totally-separated ℕ
ℕ-is-totally-separated = discrete-types-are-totally-separated ℕ-is-discrete

Baire-is-totally-separated : funext 𝓤₀ 𝓤₀ → is-totally-separated (ℕ → ℕ)
Baire-is-totally-separated fe =
 Π-is-totally-separated fe (λ n → ℕ-is-totally-separated)

\end{code}

More generally, all simple types are totally separated - see the
module SimpleTypes.

We now characterize the totally separated types X as those such that
the map eval X defined below is an embedding, in order to construct
totally separated reflections.

\begin{code}

eval : (X : 𝓤 ̇ ) → X → ((X → 𝟚) → 𝟚)
eval X = λ x p → p x

is-totally-separated₂ : 𝓤 ̇ → 𝓤 ̇
is-totally-separated₂ X = is-embedding (eval X)

totally-separated-gives-totally-separated₂ : funext 𝓤 𝓤₀
                                           → {X : 𝓤 ̇ }
                                           → is-totally-separated X
                                           → is-totally-separated₂ X
totally-separated-gives-totally-separated₂ fe {X} τ φ (x , p) (y , q) = γ
 where
  s : eval X x ＝ eval X y
  s = eval X x  ＝⟨ p ⟩
       φ        ＝⟨ q ⁻¹ ⟩
       eval X y ∎

  t : x ＝ y
  t = τ (happly s)

  r : transport (λ - → eval X - ＝ φ) t p ＝ q
  r = totally-separated-types-are-sets fe
       ((X → 𝟚) → 𝟚)
       (Π-is-totally-separated fe (λ p → 𝟚-is-totally-separated))
       (transport (λ - → eval X - ＝ φ) t p)
       q

  γ : (x , p) ＝ (y , q)
  γ = to-Σ-＝ (t , r)

totally-separated₂-gives-totally-separated : funext 𝓤 𝓤₀
                                           → {X : 𝓤 ̇ }
                                           → is-totally-separated₂ X
                                           → is-totally-separated X
totally-separated₂-gives-totally-separated fe {X} i {x} {y} e = ap pr₁ q
 where
  φ : (X → 𝟚) → 𝟚
  φ = eval X x

  h : is-prop (fiber (eval X) φ)
  h = i φ

  g : eval X y ＝ φ
  g = dfunext fe (λ p → (e p)⁻¹)

  q : x , refl ＝ y , g
  q = h (x , refl) (y , g)

\end{code}

Now, if a type X is not necessarily totally separated, we can
consider the image of the map eval X, and this gives the totally
separated reflection, with the corestriction of eval X to its image as
its reflector.

\begin{code}

module totally-separated-reflection
         (fe : FunExt)
         (pt : propositional-truncations-exist)
 where

 private
  fe' : Fun-Ext
  fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 open PropositionalTruncation pt
 open import UF.ImageAndSurjection pt

\end{code}

We construct the reflection as the image of the evaluation map.

\begin{code}

 𝕋 : 𝓤 ̇ → 𝓤 ̇
 𝕋 X = image (eval X)

 𝕋-is-totally-separated : {X : 𝓤 ̇ } → is-totally-separated (𝕋 X)
 𝕋-is-totally-separated {𝓤} {X} {φ , s} {γ , t} = g
  where
   f : (e : (q : 𝕋 X → 𝟚) → q (φ , s) ＝ q (γ , t)) (p : X → 𝟚) → φ p ＝ γ p
   f e p = e (λ (x' : 𝕋 X) → pr₁ x' p)

   g : (e : (q : 𝕋 X → 𝟚) → q (φ , s) ＝ q (γ , t)) → (φ , s) ＝ (γ , t)
   g e = to-subtype-＝ (λ _ → ∥∥-is-prop) (dfunext fe' (f e))

\end{code}

Then the reflector is the corestriction of the evaluation map. The
induction principle for surjections gives an induction principle for
the reflector.

\begin{code}

 ηᵀ : {X : 𝓤 ̇ } → X → 𝕋 X
 ηᵀ {𝓤} {X} = corestriction (eval X)

 ηᵀ-is-surjection : {X : 𝓤 ̇ } → is-surjection ηᵀ
 ηᵀ-is-surjection {𝓤} {X} = corestrictions-are-surjections (eval X)

 ηᵀ-induction :  {X : 𝓤 ̇ } (P : 𝕋 X → 𝓦 ̇ )
              → ((x' : 𝕋 X) → is-prop (P x'))
              → ((x : X) → P (ηᵀ x))
              → (x' : 𝕋 X) → P x'
 ηᵀ-induction = surjection-induction ηᵀ ηᵀ-is-surjection

\end{code}

Perhaps we could have used more induction in the following proof
rather than direct proofs (as in the proof of tight reflection below).

\begin{code}

 totally-separated-reflection : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                              → is-totally-separated A
                              → (f : X → A)
                              → ∃! f̅ ꞉ (𝕋 X → A) , f̅ ∘ ηᵀ ＝ f
 totally-separated-reflection {𝓤} {𝓥} {X} {A} τ f = δ
  where
   A-is-set : is-set A
   A-is-set = totally-separated-types-are-sets fe' A τ

   ie : (γ : (A → 𝟚) → 𝟚) → is-prop (Σ a ꞉ A , eval A a ＝ γ)
   ie = totally-separated-gives-totally-separated₂ fe' τ

   h : (φ : (X → 𝟚) → 𝟚)
     → (∃ x ꞉ X , eval X x ＝ φ)
     → Σ a ꞉ A , eval A a ＝ (λ q → φ (q ∘ f))
   h φ = ∥∥-rec (ie γ) u
    where
     γ : (A → 𝟚) → 𝟚
     γ q = φ (q ∘ f)

     u : (Σ x ꞉ X , (λ p → p x) ＝ φ) → Σ a ꞉ A , eval A a ＝ γ
     u (x , r) = f x , dfunext fe' (λ q → happly r (q ∘ f))

   h' : (x' : 𝕋 X) → Σ a ꞉ A , eval A a ＝ (λ q → pr₁ x' (q ∘ f))
   h' (φ , s) = h φ s

   f̅ : 𝕋 X → A
   f̅ (φ , s) = pr₁ (h φ s)

   b : (x' : 𝕋 X) (q : A → 𝟚) → q (f̅ x') ＝ pr₁ x' (q ∘ f)
   b (φ , s) = happly (pr₂ (h φ s))

   r : f̅ ∘ ηᵀ ＝ f
   r = dfunext fe' (λ x → τ (b (ηᵀ x)))

   c : (σ : Σ f⁺ ꞉ (𝕋 X → A) , f⁺ ∘ ηᵀ ＝ f) → (f̅ , r) ＝ σ
   c (f⁺ , s) = to-Σ-＝ (t , v)
    where
     w : f̅ ∘ ηᵀ ∼ f⁺ ∘ ηᵀ
     w = happly (f̅ ∘ ηᵀ ＝⟨ r ⟩
                 f       ＝⟨ s ⁻¹ ⟩
                 f⁺ ∘ ηᵀ ∎)

     t : f̅ ＝ f⁺
     t = dfunext fe' (ηᵀ-induction _ (λ _ → A-is-set) w)

     u : f⁺ ∘ ηᵀ ＝ f
     u = transport (λ - → - ∘ ηᵀ ＝ f) t r

     v : u ＝ s
     v = Π-is-set fe' (λ _ → A-is-set) u s

   δ : ∃! f̅ ꞉ (𝕋 X → A) , f̅ ∘ ηᵀ ＝ f
   δ = (f̅ , r) , c

\end{code}

We package the above as follows for convenient use elsewhere
(including the module CompactTypes).

\begin{code}

 totally-separated-reflection' : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                               → is-totally-separated A
                               → is-equiv (λ (f̅ : 𝕋 X → A) → f̅ ∘ ηᵀ)
 totally-separated-reflection' τ =
  vv-equivs-are-equivs _ (totally-separated-reflection τ)

 totally-separated-reflection'' : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                                → is-totally-separated A
                                → (𝕋 X → A) ≃ (X → A)
 totally-separated-reflection'' τ = (λ f̅ → f̅ ∘ ηᵀ) ,
                                    totally-separated-reflection' τ

\end{code}

In particular, because 𝟚 is totally separated, 𝕋 X and X have the same
boolean predicates (which we exploit in the module CompactTypes).

Added 21st July 2025.

\begin{code}

 extᵀ : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
      → is-totally-separated A
      → (X → A) → (𝕋 X → A)
 extᵀ τ = ⌜ totally-separated-reflection'' τ ⌝⁻¹

 ext-ηᵀ : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
          (τ : is-totally-separated A)
          (f : X → A) → extᵀ τ f ∘ ηᵀ ∼ f
 ext-ηᵀ τ f = happly
               (inverses-are-sections' (totally-separated-reflection'' τ) f)

 𝕋-functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (𝕋 X → 𝕋 Y)
 𝕋-functor f = extᵀ 𝕋-is-totally-separated (ηᵀ ∘ f)

 𝕋-natural : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
           → 𝕋-functor f ∘ ηᵀ ∼ ηᵀ ∘ f
 𝕋-natural f x = ext-ηᵀ 𝕋-is-totally-separated (ηᵀ ∘ f) x

 ηᵀ-relates-identified-points : {X : 𝓤 ̇ } {x y : X} → ηᵀ x ＝ ηᵀ y → x ＝₂ y
 ηᵀ-relates-identified-points e = happly (ap pr₁ e)

 ηᵀ-identifies-related-points : {X : 𝓤 ̇ } {x y : X} → x ＝₂ y → ηᵀ x ＝ ηᵀ y
 ηᵀ-identifies-related-points e = to-subtype-＝
                                   (λ ϕ → being-in-the-image-is-prop ϕ (eval _))
                                   (dfunext fe' e)
\end{code}

End of 21st July 2025 addition.

The notion of total separatedness (or 𝟚-separatedness) is analogous to
the T₀-separation axiom (which says that any two points with the same
open neighbourhoods are equal).

\begin{code}

𝟚-sober : 𝓦 ̇ → 𝓤 ⁺ ⊔ 𝓦 ̇
𝟚-sober {𝓦} {𝓤} A = 𝟚-separated A
                   × ((X : 𝓤 ̇ ) (e : A → X) → is-equiv (dual 𝟚 e) → is-equiv e)

\end{code}

TODO: example of 𝟚-separated type that fails to be 𝟚-sober, 𝟚-sober
reflection (or 𝟚-sobrification).

TODO: most of what we said doesn't depend on the type 𝟚, and total
separatedness can be generalized to S-separatedness for an arbitrary
type S, where 𝟚-separatedness is total separatedness. Then, for
example, Prop-separated is equivalent to is-set, all types in U are U
separated, Set-separatedness (where Set is the type of sets) should be
equivalent to is-1-groupoid, etc.

An interesting case is when S is (the total space of) a dominance,
generalizing the case S=Prop. Because the partial elements are defined
in terms of maps into S, the S-lifting of a type X should coincide
with the S-separated reflection of the lifting of X, and hence, in
this context, it makes sense to restrict our attention to S-separated
types.

Another useful thing is that in any type X we can define an apartness
relation x♯y by ∃ p : X→𝟚 , p x ‌≠p y, which is tight iff X is totally
separated, where tightness means ¬ (x ♯ y)→ x = y. Part of the following
should be moved to another module about apartness, but I keep it here
for the moment.

Added 26 January 2018.

We now show that a type is totally separated iff a particular
apartness relation _♯₂ is tight:

\begin{code}

module total-separatedness-via-apartness
        (pt : propositional-truncations-exist)
       where

 open PropositionalTruncation pt
 open import Apartness.Definition
 open Apartness pt

 _♯₂_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
 x ♯₂ y = ∃ p ꞉ (type-of x → 𝟚), p x ≠ p y

 ♯₂-is-apartness : {X : 𝓤 ̇ } → is-apartness (_♯₂_ {𝓤} {X})
 ♯₂-is-apartness {𝓤} {X} = a , b , c , d
  where
   a : is-prop-valued _♯₂_
   a x y = ∥∥-is-prop

   b : is-irreflexive _♯₂_
   b x = ∥∥-rec 𝟘-is-prop g
    where
     g : ¬ (Σ p ꞉ (X → 𝟚) , p x ≠ p x)
     g (p , u) = u refl

   c : is-symmetric _♯₂_
   c x y = ∥∥-functor g
    where
     g : (Σ p ꞉ (X → 𝟚) , p x ≠ p y) → Σ p ꞉ (X → 𝟚) , p y ≠ p x
     g (p , u) = p , ≠-sym u

   d : is-cotransitive _♯₂_
   d x y z = ∥∥-functor g
    where
     g : (Σ p ꞉ (X → 𝟚) , p x ≠ p y) → (x ♯₂ z) + (y ♯₂ z)
     g (p , u) =
       h (discrete-types-are-cotransitive 𝟚-is-discrete {p x} {p y} {p z} u)
      where
       h : (p x ≠ p z) + (p z ≠ p y) → (x ♯₂ z) + (y ♯₂ z)
       h (inl u) = inl ∣ p , u ∣
       h (inr v) = inr ∣ p , ≠-sym v ∣

 is-totally-separated₃ : 𝓤 ̇ → 𝓤 ̇
 is-totally-separated₃ {𝓤} X = is-tight (_♯₂_ {𝓤} {X})

 totally-separated₃-gives-totally-separated : {X : 𝓤 ̇ }
                                            → is-totally-separated₃ X
                                            → is-totally-separated X
 totally-separated₃-gives-totally-separated {𝓤} {X} τ {x} {y} α = γ
  where
   h : ¬ (Σ p ꞉ (X → 𝟚) , p x ≠ p y)
   h (p , u) = u (α p)

   γ : x ＝ y
   γ = τ x y (∥∥-rec 𝟘-is-prop h)

 totally-separated-gives-totally-separated₃ : {X : 𝓤 ̇ }
                                            → is-totally-separated X
                                            → is-totally-separated₃ X
 totally-separated-gives-totally-separated₃ {𝓤} {X} τ x y na = τ α
  where
   h : ¬ (Σ p ꞉ (X → 𝟚) , p x ≠ p y)
   h (p , u) = na ∣ p , u ∣

   α : (p : X → 𝟚) → p x ＝ p y
   α p = 𝟚-is-¬¬-separated (p x) (p y) (λ u → h (p , u))

 ♯₂-is-tight = totally-separated-gives-totally-separated₃

 tight-relation-contained-in-♯₂-gives-total-separatedness
  : {X : 𝓤 ̇ }
  → (_♯_ : X → X → 𝓥 ̇ )
  → ((x y : X) → x ♯ y → x ♯₂ y)
  → is-tight _♯_
  → is-totally-separated X
 tight-relation-contained-in-♯₂-gives-total-separatedness _♯_ ϕ t =
  totally-separated₃-gives-totally-separated
   (finner-than-tight-is-tight _♯_ _♯₂_ ϕ t)

 tight-apartness-contained-in-♯₂-gives-total-separatedness
  : {X : 𝓤 ̇ }
  → ((_♯_ , _) : Tight-Apartness X 𝓥)
  → ((x y : X) → x ♯ y → x ♯₂ y)
  → is-totally-separated X
 tight-apartness-contained-in-♯₂-gives-total-separatedness (_♯_ , _ , t) ϕ
  = tight-relation-contained-in-♯₂-gives-total-separatedness _♯_ ϕ t

\end{code}
