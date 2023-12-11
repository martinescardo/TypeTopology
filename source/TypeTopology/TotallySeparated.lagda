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
Y:X→U provided Y x is totally separated for all x:X. This assumes
function extensionality.

In particular, the Cantor and Baire types 𝟚^ℕ and ℕ^ℕ are totally
separated (like in topology).

Closure under Σ fails in general. However, we have closure under _×_,
and ℕ∞ (defined with Σ) is totally separated (proved in the module
GenericConvergentSequence).

A counter-example to closure under Σ (from 2012) is in the file
http://www.cs.bham.ac.uk/~mhe/TypeTopology/FailureOfTotalSeparatedness.html

This is the "compactification" of ℕ with two points at infinity:

   Σ u ꞉ ℕ∞ , u ＝ ∞ → 𝟚.

If there is a 𝟚-valued function separating the two points at infinity,
then WLPO holds. (The totally separated reflection of this type should
be ℕ∞ if ¬WLPO holds.)

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
open import UF.Powerset hiding (𝕋)
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
of all clopen sets containing x and a space is totally separated of
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

\end{code}

Recall that a type is called ¬¬-separated if the doubly negated equality
of any two element implies their equality, and that such a type is a
set.

\begin{code}

totally-separated-types-are-separated : (X : 𝓤 ̇ )
                                      → is-totally-separated X
                                      → is-¬¬-separated X
totally-separated-types-are-separated X τ = g
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
 ¬¬-separated-types-are-sets fe (totally-separated-types-are-separated X t)

\end{code}

The converse fails: the type of propositions is a set, but its total
separatedness implies excluded middle. In fact, its ¬¬-separatedness
already implies excluded middle:

\begin{code}

open import UF.ExcludedMiddle

Ω-separated-gives-DNE : propext 𝓤
                      → funext 𝓤 𝓤
                      → is-¬¬-separated (Ω 𝓤)
                      → DNE 𝓤
Ω-separated-gives-DNE {𝓤} pe fe Ω-is-¬¬-separated P P-is-prop not-not-P = d
 where
  p : Ω 𝓤
  p = (P , P-is-prop)

  b : ¬¬ (p ＝ ⊤)
  b = ¬¬-functor (holds-gives-equal-⊤ pe fe p) not-not-P

  c : p ＝ ⊤
  c = Ω-is-¬¬-separated p ⊤ b

  d : P
  d = equal-⊤-gives-holds p c

Ω-separated-gives-EM : propext 𝓤
                     → funext 𝓤 𝓤
                     → is-¬¬-separated (Ω 𝓤)
                     → EM 𝓤
Ω-separated-gives-EM {𝓤} pe fe Ω-is-¬¬-separated =
  DNE-gives-EM (lower-funext 𝓤 𝓤 fe) (Ω-separated-gives-DNE pe fe Ω-is-¬¬-separated)

Ω-totally-separated-gives-EM : propext 𝓤
                             → funext 𝓤 𝓤
                             → is-totally-separated (Ω 𝓤)
                             → EM 𝓤
Ω-totally-separated-gives-EM {𝓤} pe fe Ω-is-totally-separated =
 Ω-separated-gives-EM pe fe
  (totally-separated-types-are-separated (Ω 𝓤) Ω-is-totally-separated)

\end{code}

The need to define f and g in the following proof arises because the
function Π-is-prop requires a dependent function with explicit
arguments, but total separatedness is defined with implicit
arguments. The essence of the proof is that of p in the where clause.

\begin{code}

being-totally-separated-is-prop : funext 𝓤 𝓤
                                → (X : 𝓤 ̇ )
                                → is-prop (is-totally-separated X)
being-totally-separated-is-prop {𝓤} fe X = γ
 where
  T : 𝓤 ̇
  T = (x y : X) → x ＝₂ y → x ＝ y

  f : T → is-totally-separated X
  f t {x} {y} φ = t x y φ

  g : is-totally-separated X → T
  g t x y φ = t {x} {y} φ

  p : T → is-prop T
  p t = Π-is-prop fe (λ x →
        Π-is-prop fe (λ y →
        Π-is-prop fe (λ p → totally-separated-types-are-sets
                             (lower-funext 𝓤 𝓤 fe) X (f t))))
  l : left-cancellable g
  l = ap f

  γ : is-prop (is-totally-separated X)
  γ = subtypes-of-props-are-props' g l (prop-criterion p)

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

Σ-is-totally-separated-if-index-type-is-discrete :

    (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
  → is-discrete X
  → ((x : X) → is-totally-separated (Y x))
  → is-totally-separated (Σ Y)

Σ-is-totally-separated-if-index-type-is-discrete X Y d t {a , b} {x , y} φ = γ
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
                       → is-totally-separated(Π Y)
Π-is-totally-separated fe {X} {Y} t {f} {g} e = dfunext fe h
 where
   P : (x : X) (p : Y x → 𝟚) → Π Y → 𝟚
   P x p f = p (f x)

   h : (x : X) → f x ＝ g x
   h x = t x (λ p → e(P x p))

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

Closure under /-extensions defined in the module
InjectiveTypes. Notice that j doesn't need to be an embedding (in
which case the extension is merely a Kan extension rather than a
proper extension).

\begin{code}

module _ (fe : FunExt)  where

 private
  fe' : Fun-Ext
  fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 open import InjectiveTypes.Blackboard fe

 /-is-totally-separated : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                          (j : X → A)
                          (Y : X → 𝓦 ̇ )
                        → ((x : X) → is-totally-separated (Y x))
                        → (a : A) → is-totally-separated ((Y / j) a)
 /-is-totally-separated {𝓤} {𝓥} {𝓦} j Y t a =
  Π-is-totally-separated fe' (λ (σ : fiber j a) → t (pr₁ σ))

\end{code}

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

Now, if a type X is not (necessarily) totally separated, we can
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

 τ : {X : 𝓤 ̇ } → is-totally-separated (𝕋 X)
 τ {𝓤} {X} {φ , s} {γ , t} = g
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

 η : {X : 𝓤 ̇ } → X → 𝕋 X
 η {𝓤} {X} = corestriction (eval X)

 η-is-surjection : {X : 𝓤 ̇ } → is-surjection η
 η-is-surjection {𝓤} {X} = corestrictions-are-surjections (eval X)

 η-induction :  {X : 𝓤 ̇ } (P : 𝕋 X → 𝓦 ̇ )
             → ((x' : 𝕋 X) → is-prop (P x'))
             → ((x : X) → P (η x))
             → (x' : 𝕋 X) → P x'
 η-induction = surjection-induction η η-is-surjection

\end{code}

Perhaps we could have used more induction in the following proof
rather than direct proofs (as in the proof of tight reflection below).

\begin{code}

 totally-separated-reflection : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                              → is-totally-separated A
                              → (f : X → A)
                              → ∃! f⁻ ꞉ (𝕋 X → A) , f⁻ ∘ η ＝ f
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

   f⁻ : 𝕋 X → A
   f⁻ (φ , s) = pr₁ (h φ s)

   b : (x' : 𝕋 X) (q : A → 𝟚) → q (f⁻ x') ＝ pr₁ x' (q ∘ f)
   b (φ , s) = happly (pr₂ (h φ s))

   r : f⁻ ∘ η ＝ f
   r = dfunext fe' (λ x → τ (b (η x)))

   c : (σ : Σ f⁺ ꞉ (𝕋 X → A) , f⁺ ∘ η ＝ f) → (f⁻ , r) ＝ σ
   c (f⁺ , s) = to-Σ-＝ (t , v)
    where
     w : f⁻ ∘ η ∼ f⁺ ∘ η
     w = happly (f⁻ ∘ η  ＝⟨ r ⟩
                 f       ＝⟨ s ⁻¹ ⟩
                 f⁺ ∘ η ∎ )

     t : f⁻ ＝ f⁺
     t = dfunext fe' (η-induction _ (λ _ → A-is-set) w)

     u : f⁺ ∘ η ＝ f
     u = transport (λ - → - ∘ η ＝ f) t r

     v : u ＝ s
     v = Π-is-set fe' (λ _ → A-is-set) u s

   δ : ∃! f⁻ ꞉ (𝕋 X → A) , f⁻ ∘ η ＝ f
   δ = (f⁻ , r) , c

\end{code}

We package the above as follows for convenient use elsewhere
(including the module CompactTypes).

\begin{code}

 totally-separated-reflection' : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                               → is-totally-separated A
                               → is-equiv (λ (f⁻ : 𝕋 X → A) → f⁻ ∘ η)
 totally-separated-reflection' τ =
  vv-equivs-are-equivs _ (totally-separated-reflection τ)

 totally-separated-reflection'' : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                                → is-totally-separated A
                                → (𝕋 X → A) ≃ (X → A)
 totally-separated-reflection'' τ = (λ f⁻ → f⁻ ∘ η) ,
                                    totally-separated-reflection' τ

\end{code}

In particular, because 𝟚 is totally separated, 𝕋 X and X have the same
boolean predicates (which we exploit in the module CompactTypes).

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

26 January 2018.

\begin{code}

module Apartness
        (fe : FunExt)
        (pt : propositional-truncations-exist)
       where

 private
  fe' : Fun-Ext
  fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 open PropositionalTruncation pt
 open import UF.ImageAndSurjection pt

 is-prop-valued is-irreflexive is-symmetric is-cotransitive is-tight is-apartness
     : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇

 is-prop-valued  _♯_ = ∀ x y → is-prop (x ♯ y)
 is-irreflexive  _♯_ = ∀ x → ¬ (x ♯ x)
 is-symmetric    _♯_ = ∀ x y → x ♯ y → y ♯ x
 is-cotransitive _♯_ = ∀ x y z → x ♯ y → x ♯ z ∨ y ♯ z
 is-tight        _♯_ = ∀ x y → ¬ (x ♯ y) → x ＝ y
 is-apartness    _♯_ = is-prop-valued _♯_
                     × is-irreflexive _♯_
                     × is-symmetric _♯_
                     × is-cotransitive _♯_

 apartness-is-prop-valued : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
                          → is-apartness _♯_
                          → is-prop-valued _♯_
 apartness-is-prop-valued _♯_ (p , i , s , c) = p

 apartness-is-irreflexive : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
                          → is-apartness _♯_
                          → is-irreflexive _♯_
 apartness-is-irreflexive _♯_ (p , i , s , c) = i

 apartness-is-symmetric : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
                        → is-apartness _♯_
                        → is-symmetric _♯_
 apartness-is-symmetric _♯_ (p , i , s , c) = s

 apartness-is-cotransitive : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
                           → is-apartness _♯_
                           → is-cotransitive _♯_
 apartness-is-cotransitive _♯_ (p , i , s , c) = c

\end{code}

We now show that a type is totally separated iff a particular
apartness relation _♯₂ is tight:

\begin{code}

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
     g (p , u) = h (discrete-types-are-cotransitive 𝟚-is-discrete {p x} {p y} {p z} u)
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

\end{code}

 I don't think there is a tight apartness relation on Ω without
 constructive taboos. The natural apartness relation seems to be the
 following, but it isn't contrasitive unless excluded middle holds.

\begin{code}

 _♯Ω_ : Ω 𝓤 → Ω 𝓤 → 𝓤 ̇
 (P , i) ♯Ω (Q , j) = (P × ¬ Q) + (¬ P × Q)

 ♯Ω-irrefl : is-irreflexive (_♯Ω_ {𝓤})
 ♯Ω-irrefl (P , i) (inl (p , nq)) = nq p
 ♯Ω-irrefl (P , i) (inr (np , q)) = np q

 ♯Ω-sym : is-symmetric (_♯Ω_ {𝓤})
 ♯Ω-sym (P , i) (Q , j) (inl (p , nq)) = inr (nq , p)
 ♯Ω-sym (P , i) (Q , j) (inr (np , q)) = inl (q , np)

 ♯Ω-cotran-taboo : is-cotransitive (_♯Ω_ {𝓤})
                 → (p : Ω 𝓤) → p holds ∨ ¬ (p holds)
 ♯Ω-cotran-taboo c p = ∥∥-functor II I
  where
   I : (⊥ ♯Ω p) ∨ (⊤ ♯Ω p)
   I = c ⊥ ⊤ p (inr (𝟘-elim , ⋆))

   II : (⊥ ♯Ω p) + (⊤ ♯Ω p) → (p holds) + ¬ (p holds)
   II (inl (inr (a , b))) = inl b
   II (inr (inl (a , b))) = inr b
   II (inr (inr (a , b))) = inl b

\end{code}


 12 Feb 2018. The following was prompted by the discussion

https://nforum.ncatlab.org/discussion/8282/points-of-the-localic-quotient-with-respect-to-an-apartness-relation/

 But is clearly related to the above characterization of total
 separatedness.

\begin{code}

 is-reflexive is-transitive is-equivalence-rel
     : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇

 is-reflexive       _≈_ = ∀ x → x ≈ x
 is-transitive      _≈_ = ∀ x y z → x ≈ y → y ≈ z → x ≈ z
 is-equivalence-rel _≈_ = is-prop-valued _≈_
                        × is-reflexive _≈_
                        × is-symmetric _≈_
                        × is-transitive _≈_

\end{code}

 The following is the standard equivalence relation induced by an
 apartness relation. The tightness axiom defined above says that this
 equivalence relation is equality.

\begin{code}

 neg-apart-is-equiv : {X : 𝓤 ̇ }
                    → funext 𝓤 𝓤₀
                    → (_♯_ : X → X → 𝓤 ̇ )
                    → is-apartness _♯_
                    → is-equivalence-rel (λ x y → ¬ (x ♯ y))
 neg-apart-is-equiv {𝓤} {X} fe _♯_ (♯p , ♯i , ♯s , ♯c) = p , ♯i , s , t
  where
   p : (x y : X) → is-prop (¬ (x ♯ y))
   p x y = negations-are-props fe

   s : (x y : X) → ¬ (x ♯ y) → ¬ (y ♯ x)
   s x y u a = u (♯s y x a)

   t : (x y z : X) → ¬ (x ♯ y) → ¬ (y ♯ z) → ¬ (x ♯ z)
   t x y z u v a = v (♯s z y (left-fails-gives-right-holds (♯p z y) b u))
    where
     b : (x ♯ y) ∨ (z ♯ y)
     b = ♯c x z y a

 \end{code}

 The following positive formulation of ¬ (x ♯ y), which says that two
 elements have the same elements apart from them iff they are not
 apart, gives another way to see that it is an equivalence relation:

 \begin{code}

 not-apart-have-same-apart : {X : 𝓤 ̇ } (x y : X) (_♯_ : X → X → 𝓥 ̇ )
                           → is-apartness _♯_
                           → ¬ (x ♯ y)
                           → ((z : X) → x ♯ z ↔ y ♯ z)
 not-apart-have-same-apart {𝓤} {𝓥} {X} x y _♯_ (p , i , s , c) = g
  where
   g : ¬ (x ♯ y) → (z : X) → x ♯ z ↔ y ♯ z
   g n z = g₁ , g₂
    where
     g₁ : x ♯ z → y ♯ z
     g₁ a = s z y (left-fails-gives-right-holds (p z y) b n)
      where
       b : (x ♯ y) ∨ (z ♯ y)
       b = c x z y a

     n' : ¬ (y ♯ x)
     n' a = n (s y x a)

     g₂ : y ♯ z → x ♯ z
     g₂ a = s z x (left-fails-gives-right-holds (p z x) b n')
      where
       b : (y ♯ x) ∨ (z ♯ x)
       b = c y z x a

 have-same-apart-are-not-apart : {X : 𝓤 ̇ } (x y : X) (_♯_ : X → X → 𝓥 ̇ )
                               → is-apartness _♯_
                               → ((z : X) → x ♯ z ↔ y ♯ z)
                               → ¬ (x ♯ y)
 have-same-apart-are-not-apart {𝓤} {𝓥} {X} x y _♯_ (p , i , s , c) = f
  where
   f : ((z : X) → x ♯ z ↔ y ♯ z) → ¬ (x ♯ y)
   f φ a = i y (pr₁(φ y) a)

\end{code}

 As far as we know, the above observation that the negation of
 apartness can be characterized in positive terms is new.

 Not-not equal elements are not apart, and hence, in the presence of
 tightness, they are equal. It follows that tight apartness types are
 sets.

 TODO. We need better names for the following functions:

\begin{code}

 not-not-equal-not-apart' : {X : 𝓤 ̇ } (x y : X) (_♯_ : X → X → 𝓥 ̇ )
                          → is-irreflexive _♯_
                          → ¬¬ (x ＝ y)
                          → ¬ (x ♯ y)
 not-not-equal-not-apart' x y _♯_ i = contrapositive f
  where
   f : x ♯ y → ¬ (x ＝ y)
   f a p = i y (transport (λ - → - ♯ y) p a)

 tight-is-¬¬-separated' : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
                        → is-irreflexive _♯_
                        → is-tight _♯_
                        → is-¬¬-separated X
 tight-is-¬¬-separated' _♯_ i t = f
  where
   f : ∀ x y → ¬¬ (x ＝ y) → x ＝ y
   f x y φ = t x y (not-not-equal-not-apart' x y _♯_ i φ)

 tight-is-set' : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
               → funext 𝓤 𝓤₀
               → is-irreflexive _♯_
               → is-tight _♯_
               → is-set X
 tight-is-set' _♯_ fe i t = ¬¬-separated-types-are-sets fe
                             (tight-is-¬¬-separated' _♯_ i t)

 not-not-equal-not-apart : {X : 𝓤 ̇ } (x y : X) (_♯_ : X → X → 𝓥 ̇ )
                         → is-apartness _♯_
                         → ¬¬ (x ＝ y)
                         → ¬ (x ♯ y)
 not-not-equal-not-apart x y _♯_ (_ , i , _ , _) =
  not-not-equal-not-apart' x y _♯_ i

 tight-is-¬¬-separated : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
                       → is-apartness _♯_
                       → is-tight _♯_
                       → is-¬¬-separated X
 tight-is-¬¬-separated _♯_ (_ , i , _ , _) = tight-is-¬¬-separated' _♯_ i

 tight-is-set : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
              → funext 𝓤 𝓤₀
              → is-apartness _♯_
              → is-tight _♯_
              → is-set X
 tight-is-set _♯_ fe (_ , i , _ , _) = tight-is-set' _♯_ fe i

\end{code}

 The above use apartness data, but its existence is enough, because
 being a ¬¬-separated type and being a set are propositions.

\begin{code}

 tight-separated' : funext 𝓤 𝓤
                  → {X : 𝓤 ̇ }
                  → (∃ _♯_ ꞉ (X → X → 𝓤 ̇ ), is-apartness _♯_ × is-tight _♯_)
                  → is-¬¬-separated X
 tight-separated' {𝓤} fe {X} = ∥∥-rec (being-¬¬-separated-is-prop fe) f
   where
    f : (Σ _♯_ ꞉ (X → X → 𝓤 ̇ ), is-apartness _♯_ × is-tight _♯_)
      → is-¬¬-separated X
    f (_♯_ , a , t) = tight-is-¬¬-separated _♯_ a t

 tight-is-set'' : funext 𝓤 𝓤
                → {X : 𝓤 ̇ }
                → (∃ _♯_ ꞉ (X → X → 𝓤 ̇ ), is-apartness _♯_ × is-tight _♯_)
                → is-set X
 tight-is-set'' {𝓤} fe {X} = ∥∥-rec (being-set-is-prop fe) f
   where
    f : (Σ _♯_ ꞉ (X → X → 𝓤 ̇ ), is-apartness _♯_ × is-tight _♯_) → is-set X
    f (_♯_ , a , t) = tight-is-set _♯_ (lower-funext 𝓤 𝓤 fe) a t

\end{code}

 A map is called strongly extensional if it reflects apartness. In the
 category of apartness types, the morphisms are the strongly
 extensional maps.

\begin{code}

 is-strongly-extensional : ∀ {𝓣} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                         → (X → X → 𝓦 ̇ ) → (Y → Y → 𝓣 ̇ ) → (X → Y) → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
 is-strongly-extensional _♯_ _♯'_ f = ∀ x x' → f x ♯' f x' → x ♯ x'

 private
  is-se = is-strongly-extensional

 being-strongly-extensional-is-prop : ∀ {𝓣} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                    → (_♯_ : X → X → 𝓦 ̇ )
                                    → (_♯'_ : Y → Y → 𝓣 ̇ )
                                    → is-prop-valued _♯_
                                    → (f : X → Y)
                                    → is-prop (is-strongly-extensional _♯_ _♯'_ f)
 being-strongly-extensional-is-prop _♯_ _♯'_ ♯p f =
  Π₃-is-prop  fe' (λ x x' a → ♯p x  x')

 preserves : ∀ {𝓣} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
           → (X → X → 𝓦 ̇ ) → (Y → Y → 𝓣 ̇ ) → (X → Y) → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
 preserves R S f = ∀ {x x'} → R x x' → S (f x) (f x')

 module tight-reflection
          (pe : propext 𝓥)
          (X : 𝓤 ̇ )
          (_♯_ : X → X → 𝓥 ̇ )
          (♯p : is-prop-valued _♯_)
          (♯i : is-irreflexive _♯_)
          (♯s : is-symmetric _♯_)
          (♯c : is-cotransitive _♯_)
   where

\end{code}

  We now name the standard equivalence relation induced by _♯_.

\begin{code}

  _~_ : X → X → 𝓥 ̇
  x ~ y = ¬ (x ♯ y)

\end{code}

  For certain purposes we need the apartness axioms packed into a
  single axiom.

\begin{code}

  ♯a : is-apartness _♯_
  ♯a = (♯p , ♯i , ♯s , ♯c)

\end{code}

  Initially we tried to work with the function apart : X → (X → 𝓥 ̇ )
  defined by apart = _♯_. However, at some point in the development
  below it was difficult to proceed, when we need that the identity
  type apart x = apart y is a proposition. This should be the case
  because _♯_ is is-prop-valued. The most convenient way to achieve this
  is to restrict the codomain of apart from 𝓥 to Ω, so that the
  codomain of apart is a set.

\begin{code}

  α : X → (X → Ω 𝓥)
  α x y = x ♯ y , ♯p x y

\end{code}

  The following is an immediate consequence of the fact that two
  equivalent elements have the same apartness class, using functional
  and propositional extensionality.

\begin{code}

  α-lemma : (x y : X) → x ~ y → α x ＝ α y
  α-lemma x y na = dfunext fe' h
   where
    f : (z : X) → x ♯ z ↔ y ♯ z
    f = not-apart-have-same-apart x y _♯_ ♯a na

    g : (z : X) → x ♯ z ＝ y ♯ z
    g z = pe (♯p x z) (♯p y z) (pr₁ (f z)) (pr₂ (f z))

    h : (z : X) → α x z ＝ α y z
    h z = to-subtype-＝ (λ _ → being-prop-is-prop fe') (g z)

\end{code}

  We now construct the tight reflection of (X,♯) to get (X',♯')
  together with a universal strongly extensional map from X into tight
  apartness types. We take X' to be the image of the map α.

\begin{code}

  X' : 𝓤 ⊔ 𝓥 ⁺ ̇
  X' = image α

\end{code}

The type X may or may not be a set, but its tight reflection is
necessarily a set, and we can see this before we define a tight
apartness on it.

\begin{code}

  X'-is-set : is-set X'
  X'-is-set = subsets-of-sets-are-sets (X → Ω 𝓥) _
               (powersets-are-sets'' fe' fe' pe) ∥∥-is-prop

  η : X → X'
  η = corestriction α

\end{code}

  The following induction principle is our main tool. Its uses look
  convoluted at times by the need to show that the property one is
  doing induction over is proposition valued. Typically this involves
  the use of the fact the propositions form an exponential ideal, and,
  more generally, are closed under products.

\begin{code}

  η-is-surjection : is-surjection η
  η-is-surjection = corestrictions-are-surjections α

  η-induction : (P : X' → 𝓦 ̇ )
              → ((x' : X') → is-prop (P x'))
              → ((x : X) → P (η x))
              → (x' : X') → P x'
  η-induction = surjection-induction η η-is-surjection

\end{code}

  The apartness relation _♯'_ on X' is defined as follows.

\begin{code}

  _♯'_ : X' → X' → 𝓤 ⊔ 𝓥 ⁺ ̇
  (u , _) ♯' (v , _) = ∃ x ꞉ X , Σ y ꞉ X , (x ♯ y) × (α x ＝ u) × (α y ＝ v)

\end{code}

  Then η preserves and reflects apartness.

\begin{code}

  η-preserves-apartness : preserves _♯_ _♯'_ η
  η-preserves-apartness {x} {y} a = ∣ x , y , a , refl , refl ∣

  η-is-se : is-se _♯_ _♯'_ η
  η-is-se x y = ∥∥-rec (♯p x y) g
   where
    g : (Σ x' ꞉ X , Σ y' ꞉ X , (x' ♯ y') × (α x' ＝ α x) × (α y' ＝ α y))
      → x ♯ y
    g (x' , y' , a , p , q) = ♯s _ _ (j (♯s _ _ (i a)))
     where
      i : x' ♯ y' → x ♯ y'
      i = idtofun _ _ (ap pr₁ (happly p y'))

      j : y' ♯ x → y ♯ x
      j = idtofun _ _ (ap pr₁ (happly q x))

\end{code}

  Of course, we must check that _♯'_ is indeed an apartness
  relation. We do this by η-induction. These proofs by induction need
  routine proofs that some things are propositions.

\begin{code}

  ♯'p : is-prop-valued _♯'_
  ♯'p _ _ = ∥∥-is-prop

  ♯'i : is-irreflexive _♯'_
  ♯'i = by-induction
   where
    induction-step : ∀ x → ¬ (η x ♯' η x)
    induction-step x a = ♯i x (η-is-se x x a)

    by-induction = η-induction (λ x' → ¬ (x' ♯' x'))
                    (λ _ → Π-is-prop fe' (λ _ → 𝟘-is-prop))
                    induction-step

  ♯'s : is-symmetric _♯'_
  ♯'s = by-nested-induction
   where
    induction-step : ∀ x y → η x ♯' η y → η y ♯' η x
    induction-step x y a = η-preserves-apartness
                            (♯s x y (η-is-se x y a))

    by-nested-induction =
      η-induction (λ x' → ∀ y' → x' ♯' y' → y' ♯' x')
       (λ x' → Π₂-is-prop fe' (λ y' _ → ♯'p y' x'))
       (λ x → η-induction (λ y' → η x ♯' y' → y' ♯' η x)
                (λ y' → Π-is-prop fe' (λ _ → ♯'p y' (η x)))
                (induction-step x))

  ♯'c : is-cotransitive _♯'_
  ♯'c = by-nested-induction
   where
    induction-step : ∀ x y z → η x ♯' η y → η x ♯' η z ∨ η y ♯' η z
    induction-step x y z a = ∥∥-functor c b
     where
      a' : x ♯ y
      a' = η-is-se x y a

      b : x ♯ z ∨ y ♯ z
      b = ♯c x y z a'

      c : (x ♯ z) + (y ♯ z) → (η x ♯' η z) + (η y ♯' η z)
      c (inl e) = inl (η-preserves-apartness e)
      c (inr f) = inr (η-preserves-apartness f)

    by-nested-induction =
      η-induction (λ x' → ∀ y' z' → x' ♯' y' → (x' ♯' z') ∨ (y' ♯' z'))
       (λ _ → Π₃-is-prop fe' (λ _ _ _ → ∥∥-is-prop))
       (λ x → η-induction (λ y' → ∀ z' → η x ♯' y' → (η x ♯' z') ∨ (y' ♯' z'))
                (λ _ → Π₂-is-prop fe' (λ _ _ → ∥∥-is-prop))
                (λ y → η-induction (λ z' → η x ♯' η y → (η x ♯' z') ∨ (η y ♯' z'))
                         (λ _ → Π-is-prop fe' (λ _ → ∥∥-is-prop))
                         (induction-step x y)))

  ♯'a : is-apartness _♯'_
  ♯'a = (♯'p , ♯'i , ♯'s , ♯'c)

\end{code}

  The tightness of _♯'_ cannot by proved by induction by reduction to
  properties of _♯_, as above, because _♯_ is not (necessarily)
  tight. We need to work with the definitions of X' and _♯'_ directly.

\begin{code}

  ♯'t : is-tight _♯'_
  ♯'t (u , e) (v , f) n = ∥∥-rec X'-is-set (λ σ → ∥∥-rec X'-is-set (h σ) f) e
   where
    h : (Σ x ꞉ X , α x ＝ u) → (Σ y ꞉ X , α y ＝ v) → (u , e) ＝ (v , f)
    h (x , p) (y , q) = to-Σ-＝ (t , ∥∥-is-prop _ _)
     where
      remark : ¬∃ x ꞉ X , Σ y ꞉ X , (x ♯ y) × (α x ＝ u) × (α y ＝ v)
      remark = n

      r : ¬ (x ♯ y)
      r a = n ∣ x , y , a , p , q ∣

      t : u ＝ v
      t = u   ＝⟨ p ⁻¹ ⟩
          α x ＝⟨ α-lemma x y r ⟩
          α y ＝⟨ q ⟩
          v   ∎

\end{code}

  The tightness of _♯'_ gives that η maps equivalent elements to equal
  elements, and its irreflexity gives that elements with the same η
  image are equivalent.

\begin{code}

  η-equiv-gives-equal : {x y : X} → x ~ y → η x ＝ η y
  η-equiv-gives-equal = ♯'t _ _ ∘ contrapositive (η-is-se _ _)

  η-equal-gives-equiv : {x y : X} → η x ＝ η y → x ~ y
  η-equal-gives-equiv {x} {y} p a = ♯'i
                                     (η y)
                                     (transport (λ - → - ♯' η y)
                                     p
                                     (η-preserves-apartness a))

\end{code}

  We now show that the above data provide the tight reflection, or
  universal strongly extensional map from X to tight apartness types,
  where unique existence is expressed by saying that a Σ type is a
  singleton, as usual in univalent mathematics and homotopy type
  theory. Notice the use of η-induction to avoid dealing directly with
  the details of the constructions performed above.

\begin{code}

  module _
          {𝓦 𝓣 : Universe}
          (A : 𝓦 ̇ )
          (_♯ᴬ_ : A → A → 𝓣 ̇ )
          (♯ᴬa : is-apartness _♯ᴬ_)
          (♯ᴬt : is-tight _♯ᴬ_)
          (f : X → A)
          (f-is-se : is-se _♯_ _♯ᴬ_ f)
         where

   private
    A-is-set : is-set A
    A-is-set = tight-is-set _♯ᴬ_ fe' ♯ᴬa ♯ᴬt

    f-transforms-~-into-= : {x y : X} → x ~ y → f x ＝ f y
    f-transforms-~-into-= = ♯ᴬt _ _ ∘ contrapositive (f-is-se _ _)

   tr-lemma : (x' : X') → is-prop (Σ a ꞉ A , ∃ x ꞉ X , (η x ＝ x') × (f x ＝ a))
   tr-lemma = η-induction _ p induction-step
     where
      p : (x' : X')
        → is-prop (is-prop (Σ a ꞉ A , ∃ x ꞉ X , (η x ＝ x') × (f x ＝ a)))
      p x' = being-prop-is-prop fe'

      induction-step : (y : X)
                     → is-prop (Σ a ꞉ A , ∃ x ꞉ X , (η x ＝ η y) × (f x ＝ a))
      induction-step x (a , d) (b , e) = to-Σ-＝ (IV , ∥∥-is-prop _ _)
       where
        I : (Σ x' ꞉ X , (η x' ＝ η x) × (f x' ＝ a))
          → (Σ y' ꞉ X , (η y' ＝ η x) × (f y' ＝ b))
          → a ＝ b
        I (x' , r , s) (y' , t , u) =
         a    ＝⟨ s ⁻¹ ⟩
         f x' ＝⟨ f-transforms-~-into-= III ⟩
         f y' ＝⟨ u ⟩
         b    ∎
          where
            II : η x' ＝ η y'
            II = η x' ＝⟨ r ⟩
                 η x  ＝⟨ t ⁻¹ ⟩
                 η y' ∎

            III : x' ~ y'
            III = η-equal-gives-equiv II

        IV : a ＝ b
        IV = ∥∥-rec A-is-set (λ σ → ∥∥-rec A-is-set (I σ) e) d

   tr-construction : (x' : X') → Σ a ꞉ A , ∃ x ꞉ X , (η x ＝ x') × (f x ＝ a)
   tr-construction = η-induction _ tr-lemma induction-step
    where
     induction-step : (y : X) → Σ a ꞉ A , ∃ x ꞉ X , (η x ＝ η y) × (f x ＝ a)
     induction-step x = f x , ∣ x , refl , refl ∣

   mediating-map : X' → A
   mediating-map x' = pr₁ (tr-construction x')

   private
    f⁻ = mediating-map

   mediating-map-property : (y : X) → ∃ x ꞉ X , (η x ＝ η y) × (f x ＝ f⁻ (η y))
   mediating-map-property y = pr₂ (tr-construction (η y))

   mediating-triangle : f⁻ ∘ η ＝ f
   mediating-triangle = dfunext fe' II
    where
     I : (y : X) → (Σ x ꞉ X , (η x ＝ η y) × (f x ＝ f⁻ (η y))) → f⁻ (η y) ＝ f y
     I y (x , p , q) =
      f⁻ (η y) ＝⟨ q ⁻¹ ⟩
      f x      ＝⟨ f-transforms-~-into-= (η-equal-gives-equiv p) ⟩
      f y      ∎

     II : (y : X) → f⁻ (η y) ＝ f y
     II y = ∥∥-rec A-is-set (I y) (mediating-map-property y)

   private
    c' : is-central
           (Σ f⁻ ꞉ (X' → A) , (f⁻ ∘ η ＝ f))
           (f⁻ , mediating-triangle)
    c' (f⁺ , f⁺-triangle) = IV
      where
       I : f⁻ ∘ η ∼ f⁺ ∘ η
       I = happly (f⁻ ∘ η  ＝⟨ mediating-triangle ⟩
                   f       ＝⟨ f⁺-triangle ⁻¹ ⟩
                   f⁺ ∘ η  ∎)

       II : f⁻ ＝ f⁺
       II = dfunext fe' (η-induction _ (λ _ → A-is-set) I)

       triangle : f⁺ ∘ η ＝ f
       triangle = transport (λ - → - ∘ η ＝ f) II mediating-triangle

       III : triangle ＝ f⁺-triangle
       III = Π-is-set fe' (λ _ → A-is-set) triangle f⁺-triangle

       IV : (f⁻ , mediating-triangle) ＝ (f⁺ , f⁺-triangle)
       IV = to-subtype-＝ (λ h → Π-is-set fe' (λ _ → A-is-set)) II

   pre-tight-reflection : ∃! f⁻ ꞉ (X' → A) , (f⁻ ∘ η ＝ f)
   pre-tight-reflection = (f⁻ , mediating-triangle) , c'

   mediating-map-is-se : is-strongly-extensional _♯'_ _♯ᴬ_ f⁻
   mediating-map-is-se = V
    where
     I : (x y : X) → f⁻ (η x) ♯ᴬ f⁻ (η y) → η x ♯' η y
     I x y a = IV
      where
       II : f x ♯ᴬ f y
       II = transport₂ (_♯ᴬ_)
             (happly mediating-triangle x)
             (happly mediating-triangle y) a

       III : x ♯ y
       III = f-is-se x y II

       IV : η x ♯' η y
       IV = η-preserves-apartness III

     V : ∀ x' y' → f⁻ x' ♯ᴬ f⁻ y' → x' ♯' y'
     V = η-induction (λ x' → (y' : X') → f⁻ x' ♯ᴬ f⁻ y' → x' ♯' y')
           (λ x' → Π₂-is-prop fe' (λ y' _ → ♯'p x' y'))
           (λ x → η-induction (λ y' → f⁻ (η x) ♯ᴬ f⁻ y' → η x ♯' y')
                   (λ y' → Π-is-prop fe' (λ _ → ♯'p (η x) y'))
                   (I x))

   private
    c : is-central
         (Σ f⁻ ꞉ (X' → A) , (is-se _♯'_ _♯ᴬ_ f⁻) × (f⁻ ∘ η ＝ f))
         (f⁻ , mediating-map-is-se , mediating-triangle)
    c (f⁺ , f⁺-is-se , f⁺-triangle) =
     to-subtype-＝
       (λ h → ×-is-prop
                (being-strongly-extensional-is-prop _♯'_ _♯ᴬ_ ♯'p h)
                (Π-is-set fe' (λ _ → A-is-set)))
       (ap pr₁ (c' (f⁺ , f⁺-triangle)))


   tight-reflection : ∃! f⁻ ꞉ (X' → A)
                            , (is-strongly-extensional _♯'_ _♯ᴬ_ f⁻)
                            × (f⁻ ∘ η ＝ f)
   tight-reflection = (f⁻ , mediating-map-is-se , mediating-triangle) , c

\end{code}

  The following is an immediate consequence of the tight reflection,
  by the usual categorical argument, using the fact that the identity
  map is strongly extensional (with the identity function as the
  proof). Notice that our construction of the reflection produces a
  result in a universe higher than those where the starting data are,
  to avoid impredicativity (aka propositional resizing). Nevertheless,
  the usual categorical argument is applicable.

  A direct proof that doesn't rely on the tight reflection is equally
  short in this case, and is also included.

  What the following construction says is that if _♯_ is tight, then
  any element of X is uniquely determined by the set of elements apart
  from it.

\begin{code}

  tight-η-equiv-abstract-nonsense : is-tight _♯_ → X ≃ X'
  tight-η-equiv-abstract-nonsense ♯t = η , (θ , happly p₄) , (θ , happly p₀)
   where
    u : ∃! θ ꞉ (X' → X), θ ∘ η ＝ id
    u = pre-tight-reflection X _♯_ ♯a ♯t id (λ _ _ a → a)

    v : ∃! ζ ꞉ (X' → X'), ζ ∘ η ＝ η
    v = pre-tight-reflection X' _♯'_ ♯'a ♯'t η η-is-se

    θ : X' → X
    θ = ∃!-witness u

    ζ : X' → X'
    ζ = ∃!-witness v

    φ : (ζ' : X' → X') → ζ' ∘ η ＝ η → ζ ＝ ζ'
    φ ζ' p = ap pr₁ (∃!-uniqueness' v (ζ' , p))

    p₀ : θ ∘ η ＝ id
    p₀ = ∃!-is-witness u

    p₁ : η ∘ θ ∘ η ＝ η
    p₁ = ap (η ∘_) p₀

    p₂ : ζ ＝ η ∘ θ
    p₂ = φ (η ∘ θ) p₁

    p₃ : ζ ＝ id
    p₃ = φ id refl

    p₄ = η ∘ θ ＝⟨ p₂ ⁻¹ ⟩
         ζ     ＝⟨ p₃ ⟩
         id    ∎

  tight-η-equiv-direct : is-tight _♯_ → X ≃ X'
  tight-η-equiv-direct t = (η , vv-equivs-are-equivs η cm)
   where
    lc : left-cancellable η
    lc {x} {y} p = j h
     where
      j : ¬ (η x ♯' η y) → x ＝ y
      j = t x y ∘ contrapositive (η-preserves-apartness {x} {y})

      h : ¬ (η x ♯' η y)
      h a = ♯'i (η y) (transport (λ - → - ♯' η y) p a)

    e : is-embedding η
    e = lc-maps-into-sets-are-embeddings η lc X'-is-set

    cm : is-vv-equiv η
    cm = surjective-embeddings-are-vv-equivs η e η-is-surjection

\end{code}

TODO.

* The tight reflection has the universal property of the quotient by
  _~_. Conversely, the quotient by _~_ gives the tight reflection.

* The tight reflection of ♯₂ has the universal property of the totally
  separated reflection.
