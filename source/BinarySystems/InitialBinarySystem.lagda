Martin Escardo, 4th August 2020. (Going back to 1993 or earlier.)

A construction of the initial binary system in Spartan MLTT, without
HITs or quotients, or extensionality axioms.

A binary system is a set A with distinguished points a b : A and
functions f g : A → A such that

 (1) a = f a,
 (2) b = g b,
 (3) f b = g a.

The initial binary system is the closed interval of dyadic rationals
(see below for a picture).

We construct it as a quotient of the following type 𝔹, with L,R,l,r
corresponding to a,b,f,g, without assuming that our type theory has
quotients - it just happens to have the quotient we want.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module BinarySystems.InitialBinarySystem where

open import MLTT.Spartan
open import UF.Sets-Properties
open import UF.Subsingletons-Properties

data 𝔹 : 𝓤₀ ̇ where
 L R : 𝔹
 l r : 𝔹 → 𝔹

\end{code}

We want to perform the identifications

 (1) L = l L,
 (2) R = r R,
 (3) l R = C = r L,

so that l and r become congruences. We call C (for "center") the equal
points of (3).

Here is a pictorial illustration of what we have in mind:


    Left endpoint    center  right endpoint

    L                  C                  R
    [------------------+------------------]  (the dyadic closed interval)
                       |
    [ image of l       |       image of r ]
                       v
          common point of the images


Geometrically, the functions l and r are supposed to be affine
transformations that scale and translate the interval to two smaller
copies with a common overlapping point.

To perform the identifications, we could quotient or use a HIT (higher
inductive type). We instead take a retract, defined by the fixed
points of an idempotent normalization function.

We take the biased choice l R for C before we perform the
identification (3). This will be the canonical, or normal-form
representative of the common point of the images.

More generally, a binary system is a type A with distinguished points
a b : A and functions f g : A → A such that

 (1) a = f a,
 (2) b = g b,
 (3) f b = g a.

What we want to do is to quotient the type 𝔹, so that the quotient map
is retraction, to get the initial binary system.

\begin{code}

C : 𝔹
C = l R

is-normal : 𝔹 → 𝓤₀ ̇
is-normal L         = 𝟙
is-normal R         = 𝟙
is-normal (l L)     = 𝟘
is-normal (l R)     = 𝟙
is-normal (l (l x)) = is-normal (l x)
is-normal (l (r x)) = is-normal (r x)
is-normal (r L)     = 𝟘
is-normal (r R)     = 𝟘
is-normal (r (l x)) = is-normal (l x)
is-normal (r (r x)) = is-normal (r x)

\end{code}

The following can be proved directly, but it also follows from the
result proved below that we have an idempotent normalization function
with the normal elements as its fixed points, and from the fact that 𝔹
has decidable equality (not proved here).

\begin{code}

normality-is-decidable : (x : 𝔹) → is-normal x + ¬ is-normal x
normality-is-decidable L         = inl ⋆
normality-is-decidable R         = inl ⋆
normality-is-decidable (l L)     = inr id
normality-is-decidable (l R)     = inl ⋆
normality-is-decidable (l (l x)) = normality-is-decidable (l x)
normality-is-decidable (l (r x)) = normality-is-decidable (r x)
normality-is-decidable (r L)     = inr id
normality-is-decidable (r R)     = inr id
normality-is-decidable (r (l x)) = normality-is-decidable (l x)
normality-is-decidable (r (r x)) = normality-is-decidable (r x)

\end{code}

We don't use the fact that normality is decidable anywhere in this
file, but, because the proof is so easy, we couldn't resist including
it.

To define the normalization function, we define versions 𝕝 and 𝕣 of l
and r that preserve normality.

\begin{code}

𝕝 : 𝔹 → 𝔹
𝕝 L     = L
𝕝 R     = C
𝕝 (l x) = l (l x)
𝕝 (r x) = l (r x)

𝕣 : 𝔹 → 𝔹
𝕣 L         = C
𝕣 R         = R
𝕣 (l x)     = r (l x)
𝕣 (r L)     = r C
𝕣 (r R)     = R
𝕣 (r (l x)) = r (r (l x))
𝕣 (r (r x)) = r (r (r x))

\end{code}

The fact that the construction of 𝕣 is not the symmetric version of
that of 𝕝 (and that it is longer) corresponds to the fact that we made
a biased choice for the normal form of the center C, favouring l.

The preservation proofs are by case analysis without induction:

\begin{code}

𝕝-preserves-normality : (x : 𝔹) → is-normal x → is-normal (𝕝 x)
𝕝-preserves-normality L     i = ⋆
𝕝-preserves-normality R     i = ⋆
𝕝-preserves-normality (l x) i = i
𝕝-preserves-normality (r x) i = i

𝕣-preserves-normality : (x : 𝔹) → is-normal x → is-normal (𝕣 x)
𝕣-preserves-normality L         ⋆ = ⋆
𝕣-preserves-normality R         ⋆ = ⋆
𝕣-preserves-normality (l R)     ⋆ = ⋆
𝕣-preserves-normality (l (l x)) i = i
𝕣-preserves-normality (l (r x)) i = i
𝕣-preserves-normality (r (l x)) i = i
𝕣-preserves-normality (r (r x)) i = i

\end{code}

The normalization function replaces l and r by their "semantic"
versions 𝕝 and 𝕣:

\begin{code}

normalize : 𝔹 → 𝔹
normalize L     = L
normalize R     = R
normalize (l x) = 𝕝 (normalize x)
normalize (r x) = 𝕣 (normalize x)

\end{code}

By construction, the result of normalization is normal, with a direct
proof by induction:

\begin{code}

normalize-is-normal : (x : 𝔹) → is-normal (normalize x)
normalize-is-normal L     = ⋆
normalize-is-normal R     = ⋆
normalize-is-normal (l x) = 𝕝-preserves-normality (normalize x) (normalize-is-normal x)
normalize-is-normal (r x) = 𝕣-preserves-normality (normalize x) (normalize-is-normal x)

\end{code}

We now prove that normal points are fixed points of the normalization
function. We need a simple lemma for that purpose, proved by case
analysis.

\begin{code}

𝕣r-equation : (x : 𝔹) → is-normal (r x) → 𝕣 (r x) ＝ r (r x)
𝕣r-equation L     i = 𝟘-elim i
𝕣r-equation R     i = 𝟘-elim i
𝕣r-equation (l x) i = refl
𝕣r-equation (r x) i = refl

\end{code}

To prove that normal points are fixed points of the normalization
function, we need to simultaneously prove two lemmas by induction:

\begin{code}

nfp-lemma-l : (x : 𝔹) → is-normal (l x) → 𝕝 (normalize x) ＝ l x
nfp-lemma-r : (x : 𝔹) → is-normal (r x) → 𝕣 (normalize x) ＝ r x

nfp-lemma-l L     i = 𝟘-elim i
nfp-lemma-l R     ⋆ = refl
nfp-lemma-l (l x) i = ap 𝕝 (nfp-lemma-l x i)
nfp-lemma-l (r x) i = ap 𝕝 (nfp-lemma-r x i)

nfp-lemma-r L     i = 𝟘-elim i
nfp-lemma-r R     i = 𝟘-elim i
nfp-lemma-r (l x) i = ap 𝕣 (nfp-lemma-l x i)
nfp-lemma-r (r x) i = 𝕣 (𝕣 (normalize x)) ＝⟨ ap 𝕣 (nfp-lemma-r x i) ⟩
                      𝕣 (r x)             ＝⟨ 𝕣r-equation x i ⟩
                      r (r x)             ∎
\end{code}

Now the proof of the desired result is by cases (without induction),
using the above two lemmas.

\begin{code}

normals-are-fixed-points : (x : 𝔹) → is-normal x → normalize x ＝ x
normals-are-fixed-points L     ⋆ = refl
normals-are-fixed-points R     ⋆ = refl
normals-are-fixed-points (l x) i = nfp-lemma-l x i
normals-are-fixed-points (r x) i = nfp-lemma-r x i

\end{code}

We have the following two corollaries:

\begin{code}

fixed-points-are-normal : (x : 𝔹) → normalize x ＝ x → is-normal x
fixed-points-are-normal x p = transport is-normal p (normalize-is-normal x)

normalization-idemp : (x : 𝔹) → normalize (normalize x) ＝ normalize x
normalization-idemp x = normals-are-fixed-points (normalize x) (normalize-is-normal x)

\end{code}

We now show that 𝔹is a set in the sense of univalent mathematics and
that it has decidable equality. There are short proofs of some of the
following lemmas in Agda. But we are restricting ourselves to a
fragment of Agda corresponding to a spartan Martin-Löf type theory. In
particular, in MLTT, it is not possible to prove that L ≠ R without
using a universe, but Agda just gives this as a fact.

We want to show that the equality of 𝔹is truth valued, as opposed to
arbitrary-type valued, where a truth value, or proposition, is a type
with at most one element. For that purpose, we first define our own
truth valued equality, where Ω₀ is the type of truth values in the
first universe 𝓤₀.

\begin{code}

open import UF.Hedberg
open import UF.Sets
open import UF.SubtypeClassifier
open import UF.Subsingletons hiding (center)

χ : 𝔹 → 𝔹 → Ω₀
χ L    L      = ⊤
χ L    R      = ⊥
χ L    (l y)  = ⊥
χ L    (r y)  = ⊥
χ R    L      = ⊥
χ R    R      = ⊤
χ R    (l y)  = ⊥
χ R    (r y)  = ⊥
χ (l x) L     = ⊥
χ (l x) R     = ⊥
χ (l x) (l y) = χ x y
χ (l x) (r y) = ⊥
χ (r x) L     = ⊥
χ (r x) R     = ⊥
χ (r x) (l y) = ⊥
χ (r x) (r y) = χ x y

_＝[𝔹]_ : 𝔹 → 𝔹 → 𝓤₀ ̇
x ＝[𝔹] y = χ x y holds

＝[𝔹]-is-prop-valued : (x y : 𝔹) → is-prop (x ＝[𝔹] y)
＝[𝔹]-is-prop-valued x y = holds-is-prop (χ x y)

refl[𝔹] : (x : 𝔹) → x ＝[𝔹] x
refl[𝔹] L     = ⋆
refl[𝔹] R     = ⋆
refl[𝔹] (l x) = refl[𝔹] x
refl[𝔹] (r x) = refl[𝔹] x

\end{code}

The induction principle for our notion of equality:

\begin{code}

J𝔹 : (x : 𝔹) (A : (y : 𝔹) → x ＝[𝔹] y → 𝓥 ̇ )
    → A x (refl[𝔹] x) → (y : 𝔹) (r : x ＝[𝔹] y) → A y r
J𝔹 L     A b L     ⋆ = b
J𝔹 L     A b R     p = 𝟘-elim p
J𝔹 L     A b (l y) p = 𝟘-elim p
J𝔹 L     A b (r y) p = 𝟘-elim p
J𝔹 R     A b L     p = 𝟘-elim p
J𝔹 R     A b R     ⋆ = b
J𝔹 R     A b (l y) p = 𝟘-elim p
J𝔹 R     A b (r y) p = 𝟘-elim p
J𝔹 (l x) A b L     p = 𝟘-elim p
J𝔹 (l x) A b R     p = 𝟘-elim p
J𝔹 (l x) A b (l y) p = J𝔹 x (A ∘ l) b y p
J𝔹 (l x) A b (r y) p = 𝟘-elim p
J𝔹 (r x) A b L     p = 𝟘-elim p
J𝔹 (r x) A b R     p = 𝟘-elim p
J𝔹 (r x) A b (l y) p = 𝟘-elim p
J𝔹 (r x) A b (r y) p = J𝔹 x (A ∘ r) b y p

\end{code}

From this we get back and forth conversions between our notion of
equality and the one of MLTT, where Jbased is the "based" induction
principle for MLTT equality.

\begin{code}

from-＝[𝔹] : (x y : 𝔹) → x ＝[𝔹] y → x ＝ y
from-＝[𝔹] x = J𝔹 x (λ y p → x ＝ y) refl

to-＝[𝔹] : (x y : 𝔹) → x ＝ y → x ＝[𝔹] y
to-＝[𝔹] x = Jbased x (λ y p → x ＝[𝔹] y) (refl[𝔹] x)

\end{code}

To show that 𝔹is a set, it is enough to prove that the type x ＝ y has
a constant endomap. We construct it as the composition of our forth
and back conversions. It is constant because our notion of equality is
truth valued (any two elements of our equality type are equal).

\begin{code}

𝔹-is-set : is-set 𝔹
𝔹-is-set = Id-collapsibles-are-sets (f , κ)
 where
  f : {x y : 𝔹} → x ＝ y → x ＝ y
  f {x} {y} p = from-＝[𝔹] x y (to-＝[𝔹] x y p)

  κ : {x y : 𝔹} (p q : x ＝ y) → f p ＝ f q
  κ {x} {y} p q = u
   where
    t : to-＝[𝔹] x y p ＝ to-＝[𝔹] x y q
    t = ＝[𝔹]-is-prop-valued x y (to-＝[𝔹] x y p) (to-＝[𝔹] x y q)

    u : from-＝[𝔹] x y (to-＝[𝔹] x y p) ＝ from-＝[𝔹] x y (to-＝[𝔹] x y q)
    u = ap (from-＝[𝔹] x y) t

\end{code}

Another way to show that a type is a set is to show that it has
decidable equality, as is well known, which is the original version of
Hedberg's Theorem.

\begin{code}

＝[𝔹]-is-decidable : (x y : 𝔹) → (x ＝[𝔹] y) + ¬ (x ＝[𝔹] y)
＝[𝔹]-is-decidable L     L     = inl ⋆
＝[𝔹]-is-decidable L     R     = inr id
＝[𝔹]-is-decidable L     (l y) = inr id
＝[𝔹]-is-decidable L     (r y) = inr id
＝[𝔹]-is-decidable R     L     = inr id
＝[𝔹]-is-decidable R     R     = inl ⋆
＝[𝔹]-is-decidable R     (l y) = inr id
＝[𝔹]-is-decidable R     (r y) = inr id
＝[𝔹]-is-decidable (l x) L     = inr id
＝[𝔹]-is-decidable (l x) R     = inr id
＝[𝔹]-is-decidable (l x) (l y) = ＝[𝔹]-is-decidable x y
＝[𝔹]-is-decidable (l x) (r y) = inr id
＝[𝔹]-is-decidable (r x) L     = inr id
＝[𝔹]-is-decidable (r x) R     = inr id
＝[𝔹]-is-decidable (r x) (l y) = inr id
＝[𝔹]-is-decidable (r x) (r y) = ＝[𝔹]-is-decidable x y

𝔹-has-decidable-equality : (x y : 𝔹) → (x ＝ y) + ¬ (x ＝ y)
𝔹-has-decidable-equality x y = δ (＝[𝔹]-is-decidable x y)
 where
  δ : (x ＝[𝔹] y) + ¬ (x ＝[𝔹] y) → (x ＝ y) + ¬ (x ＝ y)
  δ (inl p) = inl (from-＝[𝔹] x y p)
  δ (inr ν) = inr (contrapositive (to-＝[𝔹] x y) ν)

\end{code}

So we get an alternative proof that normality is decidable: an element
x of 𝔹 is normal if and only if normalize x ＝ x.

But we actually don't need the normalization procedure to construct
the initial binary system, whose underlying type will be called 𝕄.
However, we will use some of the above machinery.

\begin{code}

𝕄 : 𝓤₀ ̇
𝕄 = Σ x ꞉ 𝔹 , is-normal x

being-normal-is-prop : (x : 𝔹) → is-prop (is-normal x)
being-normal-is-prop L         = 𝟙-is-prop
being-normal-is-prop R         = 𝟙-is-prop
being-normal-is-prop (l L)     = 𝟘-is-prop
being-normal-is-prop (l R)     = 𝟙-is-prop
being-normal-is-prop (l (l x)) = being-normal-is-prop (l x)
being-normal-is-prop (l (r x)) = being-normal-is-prop (r x)
being-normal-is-prop (r L)     = 𝟘-is-prop
being-normal-is-prop (r R)     = 𝟘-is-prop
being-normal-is-prop (r (l x)) = being-normal-is-prop (l x)
being-normal-is-prop (r (r x)) = being-normal-is-prop (r x)

𝕄-is-set : is-set 𝕄
𝕄-is-set = subsets-of-sets-are-sets 𝔹 is-normal 𝔹-is-set
             (λ {x} → being-normal-is-prop x)

Left Center Right : 𝕄
Left   = L , ⋆
Center = C , ⋆
Right  = R , ⋆

left right : 𝕄 → 𝕄
left  (x , i) = 𝕝 x , 𝕝-preserves-normality x i
right (x , i) = 𝕣 x , 𝕣-preserves-normality x i

𝕄-eq-lR-C : left Right ＝ Center
𝕄-eq-lR-C = refl

𝕄-eq-rL-C : right Left ＝ Center
𝕄-eq-rL-C = refl

𝕄-eq-l : Left ＝ left Left
𝕄-eq-l = refl

𝕄-eq-r : Right ＝ right Right
𝕄-eq-r = refl

𝕄-eq-lr : left Right ＝ right Left
𝕄-eq-lr = refl

𝕄-eq-lm : left Right ＝ Center
𝕄-eq-lm = refl

𝕄-eq-rm : right Left ＝ Center
𝕄-eq-rm = refl

\end{code}

We now use the above to show that 𝕄 is the initial binary system.

\begin{code}

binary-system-structure : 𝓤 ̇ → 𝓤 ̇
binary-system-structure A = A × A × (A → A) × (A → A)

binary-system-axioms : (A : 𝓤 ̇ ) → binary-system-structure A → 𝓤 ̇
binary-system-axioms A (a , b , f , g) = is-set A × (a ＝ f a) × (f b ＝ g a) × (b ＝ g b)

BS : (𝓤 : Universe) → 𝓤 ⁺ ̇
BS 𝓤 = Σ A ꞉ 𝓤 ̇ , Σ s ꞉ binary-system-structure A , binary-system-axioms A s

𝓜 : BS 𝓤₀
𝓜 = (𝕄 , (Left , Right , left , right) , (𝕄-is-set , 𝕄-eq-l , 𝕄-eq-lr , 𝕄-eq-r))

open import UF.SIP
open sip

\end{code}

The notion of homomorphism of binary systems is the expected one:

\begin{code}

is-hom : (𝓐 : BS 𝓤) (𝓐' : BS 𝓥) → (⟨ 𝓐 ⟩ → ⟨ 𝓐' ⟩) → 𝓤 ⊔ 𝓥 ̇
is-hom (A , (a , b , f , g) , _) (A' , (a' , b' , f' , g') , _) h =
   (h a ＝ a')
 × (h b ＝ b')
 × (h ∘ f ∼ f' ∘ h)
 × (h ∘ g ∼ g' ∘ h)

\end{code}

In order to show that 𝓜 is the initial binary system, we first prove
(the expected) induction principle for its underlying type 𝕄 (with a
perhaps unexpected proof):

\begin{code}

𝕄-inductive : (P : 𝕄 → 𝓤 ̇ )
            → P Left
            → P Right
            → ((x : 𝕄) → P x → P (left x))
            → ((x : 𝕄) → P x → P (right x))
            → 𝓤 ̇
𝕄-inductive P a b f g = ((x : 𝕄) → is-set (P x))
                       × (a ＝ f Left a)
                       × (f Right b ＝ g Left a)
                       × (b ＝ g Right b)


𝕄-induction : (P : 𝕄 → 𝓤 ̇ )
            → (a : P Left)
            → (b : P Right)
            → (f : (x : 𝕄) → P x → P (left x))
            → (g : (x : 𝕄) → P x → P (right x))
            → 𝕄-inductive P a b f g
            → (x : 𝕄) → P x

𝕄-induction P a b f g ι (L ,           ⋆) = a
𝕄-induction P a b f g ι (R ,           ⋆) = b
𝕄-induction P a b f g ι (l R ,         i) = f (R , ⋆) b
𝕄-induction P a b f g ι (l (l x) ,     i) = f (l x , i) (𝕄-induction P a b f g ι (l x , i))
𝕄-induction P a b f g ι (l (r x) ,     i) = f (r x , i) (𝕄-induction P a b f g ι (r x , i))
𝕄-induction P a b f g ι (r (l R) ,     i) = g (l R , ⋆) (f (R , ⋆) b)
𝕄-induction P a b f g ι (r (l (l x)) , i) = g (l (l x) , i) (𝕄-induction P a b f g ι (l (l x) , i))
𝕄-induction P a b f g ι (r (l (r x)) , i) = g (l (r x) , i) (𝕄-induction P a b f g ι (l (r x) , i))
𝕄-induction P a b f g ι (r (r (l x)) , i) = g (r (l x) , i) (𝕄-induction P a b f g ι (r (l x) , i))
𝕄-induction P a b f g ι (r (r (r x)) , i) = g (r (r x) , i) (𝕄-induction P a b f g ι (r (r x) , i))

\end{code}

In MLTT, induction principles come with equations. In our case they
are the expected ones.

\begin{code}

𝕄-induction-eq-Left : (P : 𝕄 → 𝓤 ̇ )
                      (a : P Left)
                      (b : P Right)
                      (f : (x : 𝕄) → P x → P (left x))
                      (g : (x : 𝕄) → P x → P (right x))
                      (ι : 𝕄-inductive P a b f g)
                    → 𝕄-induction P a b f g ι Left ＝ a

𝕄-induction-eq-Left P a b f g _ = refl


𝕄-induction-eq-Right : (P : 𝕄 → 𝓤 ̇ )
                      (a : P Left)
                      (b : P Right)
                      (f : (x : 𝕄) → P x → P (left x))
                      (g : (x : 𝕄) → P x → P (right x))
                      (ι : 𝕄-inductive P a b f g)
                     → 𝕄-induction P a b f g ι Right ＝ b

𝕄-induction-eq-Right P a b f g _ = refl

\end{code}

For the next equation for the induction principle, we need the
assumption a ＝ f Left a:

\begin{code}

𝕄-induction-eq-left : (P : 𝕄 → 𝓤 ̇ )
                      (a : P Left)
                      (b : P Right)
                      (f : (x : 𝕄) → P x → P (left x))
                      (g : (x : 𝕄) → P x → P (right x))
                    → (ι : 𝕄-inductive P a b f g)
                    → (x : 𝕄) → 𝕄-induction P a b f g ι (left x) ＝ f x (𝕄-induction P a b f g ι x)

𝕄-induction-eq-left P a b f g ι (L ,   ⋆) = pr₁ (pr₂ ι)
𝕄-induction-eq-left P a b f g ι (R ,   ⋆) = refl
𝕄-induction-eq-left P a b f g ι (l x , i) = refl
𝕄-induction-eq-left P a b f g ι (r x , i) = refl

\end{code}

And for the last equation for the induction principle, we need the two
equations f Right b ＝ g Left a and b ＝ g Right b as assumptions:

\begin{code}

𝕄-induction-eq-right : (P : 𝕄 → 𝓤 ̇ )
                      (a : P Left)
                      (b : P Right)
                      (f : (x : 𝕄) → P x → P (left x))
                      (g : (x : 𝕄) → P x → P (right x))
                    → (ι : 𝕄-inductive P a b f g)
                    → (x : 𝕄) → 𝕄-induction P a b f g ι (right x) ＝ g x (𝕄-induction P a b f g ι x)

𝕄-induction-eq-right P a b f g ι (L ,       ⋆) = pr₁ (pr₂ (pr₂ ι))
𝕄-induction-eq-right P a b f g ι (R ,       ⋆) = pr₂ (pr₂ (pr₂ ι))
𝕄-induction-eq-right P a b f g ι (l R ,     i) = refl
𝕄-induction-eq-right P a b f g ι (l (l x) , i) = refl
𝕄-induction-eq-right P a b f g ι (l (r x) , i) = refl
𝕄-induction-eq-right P a b f g ι (r (l x) , i) = refl
𝕄-induction-eq-right P a b f g ι (r (r x) , i) = refl

\end{code}

From now on we don't rely on the particular construction of 𝕄. We only
use the induction principle and its equations.

As usual, the recursion principle is a particular case of the
induction principle:

\begin{code}

𝓜-rec : (𝓐 : BS 𝓤) → (𝕄 → ⟨ 𝓐 ⟩)
𝓜-rec (A , (a , b , f , g) , (ι₁ , ι')) = 𝕄-induction (λ _ → A) a b (λ _ → f) (λ _ → g) ((λ _ → ι₁) , ι')

\end{code}

And so are its equations, which amount to the fact that 𝓜-rec
constructs a homomorphism:

\begin{code}

𝓜-rec-is-hom : (𝓐 : BS 𝓤)
              → is-hom 𝓜 𝓐 (𝓜-rec 𝓐)
𝓜-rec-is-hom (A , (a , b , f , g) , ι) = i , ii , iii , iv
 where
  𝓐 = (A , (a , b , f , g) , ι)

  i : 𝓜-rec 𝓐 Left ＝ a
  i = 𝕄-induction-eq-Left (λ _ → A) a b (λ _ → f) (λ _ → g) ((λ _ → pr₁ ι) , pr₂ ι)

  ii : 𝓜-rec 𝓐 Right ＝ b
  ii = 𝕄-induction-eq-Right (λ _ → A) a b (λ _ → f) (λ _ → g) ((λ _ → pr₁ ι) , pr₂ ι)

  iii : (x : 𝕄) → 𝓜-rec 𝓐 (left x) ＝ f (𝓜-rec 𝓐 x)
  iii = 𝕄-induction-eq-left (λ _ → A) a b (λ _ → f) (λ _ → g) ((λ _ → pr₁ ι) , pr₂ ι)

  iv : (x : 𝕄) → 𝓜-rec 𝓐 (right x) ＝ g (𝓜-rec 𝓐 x)
  iv = 𝕄-induction-eq-right (λ _ → A) a b (λ _ → f) (λ _ → g) ((λ _ → pr₁ ι) , pr₂ ι)

\end{code}

Some boiler plate code to name the projections follows:

\begin{code}

⟨_⟩-Left : (𝓐 : BS 𝓤) → ⟨ 𝓐 ⟩
⟨ (A , (a , b , f , g) , ι) ⟩-Left = a


⟨_⟩-Right : (𝓐 : BS 𝓤) → ⟨ 𝓐 ⟩
⟨ (A , (a , b , f , g) , ι) ⟩-Right = b


⟨_⟩-left : (𝓐 : BS 𝓤) → ⟨ 𝓐 ⟩ → ⟨ 𝓐 ⟩
⟨ (A , (a , b , f , g) , ι) ⟩-left = f


⟨_⟩-right : (𝓐 : BS 𝓤) → ⟨ 𝓐 ⟩ → ⟨ 𝓐 ⟩
⟨ (A , (a , b , f , g) , ι) ⟩-right = g

⟨_⟩-is-set : (𝓐 : BS 𝓤) → is-set ⟨ 𝓐 ⟩
⟨ (A , (a , b , f , g) , ι) ⟩-is-set = pr₁ ι


is-hom-L : (𝓐 : BS 𝓤) (𝓑 : BS 𝓥) (h : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
            → is-hom 𝓐 𝓑 h → h (⟨ 𝓐 ⟩-Left) ＝ ⟨ 𝓑 ⟩-Left
is-hom-L 𝓐 𝓑 h (i , ii , iii , iv) = i


is-hom-R : (𝓐 : BS 𝓤) (𝓑 : BS 𝓥) (h : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
             → is-hom 𝓐 𝓑 h → h (⟨ 𝓐 ⟩-Right) ＝ ⟨ 𝓑 ⟩-Right
is-hom-R 𝓐 𝓑 h (i , ii , iii , iv) = ii


is-hom-l : (𝓐 : BS 𝓤) (𝓑 : BS 𝓥) (h : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
            → is-hom 𝓐 𝓑 h → h ∘ ⟨ 𝓐 ⟩-left ∼ ⟨ 𝓑 ⟩-left ∘ h
is-hom-l 𝓐 𝓑 h (i , ii , iii , iv) = iii


is-hom-r : (𝓐 : BS 𝓤) (𝓑 : BS 𝓥) (h : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
             → is-hom 𝓐 𝓑 h → h ∘ ⟨ 𝓐 ⟩-right ∼ ⟨ 𝓑 ⟩-right ∘ h
is-hom-r 𝓐 𝓑 h (i , ii , iii , iv) = iv

\end{code}

This is the end of the boiler plate code.

To conclude that 𝓜 is the initial binary system, it remains to prove
that there is at most one homomorphism from it to any other binary
system.

\begin{code}

𝓜-at-most-one-hom : (𝓐 : BS 𝓤) (h k : 𝕄 → ⟨ 𝓐 ⟩)
                 → is-hom 𝓜 𝓐 h
                 → is-hom 𝓜 𝓐 k
                 → h ∼ k
𝓜-at-most-one-hom 𝓐 h k u v = 𝕄-induction (λ x → h x ＝ k x) α β ϕ γ
                                 ((λ x → props-are-sets ⟨ 𝓐 ⟩-is-set) ,
                                  ⟨ 𝓐 ⟩-is-set α (ϕ Left α) ,
                                  ⟨ 𝓐 ⟩-is-set (ϕ Right β) (γ Left α) ,
                                  ⟨ 𝓐 ⟩-is-set β (γ Right β))
 where
  α = h Left       ＝⟨ is-hom-L 𝓜 𝓐 h u ⟩
      ⟨ 𝓐 ⟩-Left   ＝⟨ (is-hom-L 𝓜 𝓐 k v)⁻¹ ⟩
      k Left ∎

  β = h Right       ＝⟨ is-hom-R 𝓜 𝓐 h u ⟩
       ⟨ 𝓐 ⟩-Right   ＝⟨ (is-hom-R 𝓜 𝓐 k v)⁻¹ ⟩
       k Right ∎

  ϕ : (x : 𝕄) → h x ＝ k x → h (left x) ＝ k (left x)
  ϕ x p = h (left x)       ＝⟨ is-hom-l 𝓜 𝓐 h u x ⟩
          ⟨ 𝓐 ⟩-left (h x) ＝⟨ ap ⟨ 𝓐 ⟩-left p ⟩
          ⟨ 𝓐 ⟩-left (k x) ＝⟨ (is-hom-l 𝓜 𝓐 k v x)⁻¹ ⟩
          k (left x)       ∎

  γ : (x : 𝕄) → h x ＝ k x → h (right x) ＝ k (right x)
  γ x p =  h (right x)       ＝⟨ is-hom-r 𝓜 𝓐 h u x ⟩
           ⟨ 𝓐 ⟩-right (h x) ＝⟨ ap ⟨ 𝓐 ⟩-right p ⟩
           ⟨ 𝓐 ⟩-right (k x) ＝⟨ (is-hom-r 𝓜 𝓐 k v x)⁻¹ ⟩
           k (right x)       ∎


𝓜-rec-unique : (𝓐 : BS 𝓤) (h : 𝕄 → ⟨ 𝓐 ⟩)
             → is-hom 𝓜 𝓐 h
             → h ∼ 𝓜-rec 𝓐
𝓜-rec-unique 𝓐 h u = 𝓜-at-most-one-hom 𝓐 h (𝓜-rec 𝓐) u (𝓜-rec-is-hom 𝓐)

\end{code}

Primitive (or parametric) recursion, which has the above as a special
case:

\begin{code}

𝕄-pinductive : {A : 𝓤 ̇ } → A → A → (𝕄 → A → A) → (𝕄 → A → A) → 𝓤 ̇
𝕄-pinductive {𝓤} {A} a b f g = 𝕄-inductive (λ _ → A) a b f g

𝕄-primrec : {A : 𝓤 ̇ } (a b : A) (f g : 𝕄 → A → A) → 𝕄-pinductive a b f g → 𝕄 → A
𝕄-primrec {𝓤} {A} a b f g = 𝕄-induction (λ _ → A) a b f g

primitive-recursive : {A : 𝓤 ̇ } → A → A → (𝕄 → A → A) → (𝕄 → A → A) → (𝕄 → A) → 𝓤 ̇
primitive-recursive a b f g h =

         (h Left  ＝ a)
       × (h Right ＝ b)
       × ((x : 𝕄) → h (left x)  ＝ f x (h x))
       × ((x : 𝕄) → h (right x) ＝ g x (h x))



𝕄-primrec-primitive-recursive : {A : 𝓤 ̇ }
                    (a b : A)
                    (f g : 𝕄 → A → A)
                  → (ι : 𝕄-pinductive a b f g)
                  → primitive-recursive a b f g (𝕄-primrec a b f g ι)

𝕄-primrec-primitive-recursive {𝓤} {A} a b f g ι =

   𝕄-induction-eq-Left (λ _ → A) a b f g ι ,
   𝕄-induction-eq-Right (λ _ → A) a b f g ι ,
   𝕄-induction-eq-left (λ _ → A) a b f g ι ,
   𝕄-induction-eq-right (λ _ → A) a b f g ι


𝕄-at-most-one-primrec : {A : 𝓤 ̇ }
                    (a b : A)
                    (f g : 𝕄 → A → A)
                   → 𝕄-pinductive a b f g
                   → (h k : 𝕄 → A)
                   → primitive-recursive a b f g h
                   → primitive-recursive a b f g k
                   → h ∼ k

𝕄-at-most-one-primrec {𝓤} {A} a b f g (ι₁ , ι')  h k (hL , hR , hl , hr) (kL , kR , kl , kr) = δ
 where
  arbitrary-element-of-𝕄 = Left

  A-is-set : is-set A
  A-is-set = ι₁ arbitrary-element-of-𝕄

  α = h Left ＝⟨ hL ⟩
      a      ＝⟨ kL ⁻¹ ⟩
      k Left ∎

  β = h Right ＝⟨ hR ⟩
      b       ＝⟨ kR ⁻¹ ⟩
      k Right ∎

  ϕ : (x : 𝕄) → h x ＝ k x → h (left x) ＝ k (left x)
  ϕ x p = h (left x) ＝⟨ hl x ⟩
          f x (h x)  ＝⟨ ap (f x) p ⟩
          f x (k x)  ＝⟨ (kl x)⁻¹ ⟩
          k (left x) ∎

  γ : (x : 𝕄) → h x ＝ k x → h (right x) ＝ k (right x)
  γ x p =  h (right x) ＝⟨ hr x ⟩
           g x (h x)   ＝⟨ ap (g x) p ⟩
           g x (k x)   ＝⟨ (kr x)⁻¹ ⟩
           k (right x) ∎

  set-condition : (x : 𝕄) → is-set (h x ＝ k x)
  set-condition x = props-are-sets A-is-set

  eql : α ＝ ϕ Left α
  eql = A-is-set α (ϕ Left α)

  eqlr : ϕ Right β ＝ γ Left α
  eqlr = A-is-set (ϕ Right β) (γ Left α)

  eqr : β ＝ γ Right β
  eqr = A-is-set β (γ Right β)

  δ : h ∼ k
  δ = 𝕄-induction (λ x → h x ＝ k x) α β ϕ γ (set-condition , eql , eqlr , eqr)


𝕄-primrec-uniqueness : {A : 𝓤 ̇ }
                    (a b : A)
                    (f g : 𝕄 → A → A)
                   → (ι : 𝕄-pinductive a b f g)
                   → (h : 𝕄 → A)
                   → primitive-recursive a b f g h
                   → h ∼ 𝕄-primrec a b f g ι

𝕄-primrec-uniqueness a b f g ι h hph = 𝕄-at-most-one-primrec a b f g ι
                                            h (𝕄-primrec a b f g ι)
                                            hph (𝕄-primrec-primitive-recursive a b f g ι)

\end{code}

Under some special conditions that often hold in practice, we can
remove the "base" case in the uniqueness theorem.

\begin{code}

is-wprimrec : {A : 𝓤 ̇ } → (𝕄 → A → A) → (𝕄 → A → A) → (𝕄 → A) → 𝓤 ̇
is-wprimrec f g h = ((x : 𝕄) → h (left x)  ＝ f x (h x))
                  × ((x : 𝕄) → h (right x) ＝ g x (h x))


primrec-is-wprimrec : {A : 𝓤 ̇ } (a b : A) (f g : 𝕄 → A → A) (h : 𝕄 → A)
                    → primitive-recursive a b f g h → is-wprimrec f g h
primrec-is-wprimrec a b f g h (hL , hR , hl , hr) = (hl , hr)


fixed-point-conditions : {A : 𝓤 ̇ } → A → A → (𝕄 → A → A) → (𝕄 → A → A) → 𝓤 ̇
fixed-point-conditions a b f g = (∀ a' → a' ＝ f Left  a' → a' ＝ a)
                              × (∀ b' → b' ＝ g Right b' → b' ＝ b)

wprimrec-primitive-recursive : {A : 𝓤 ̇ } (a b : A) (f g : 𝕄 → A → A) (h : 𝕄 → A)
                             → fixed-point-conditions a b f g
                             → is-wprimrec f g h → primitive-recursive a b f g h
wprimrec-primitive-recursive a b f g h (fixa , fixb) (hl , hr) = (hL , hR , hl , hr)
 where
  hL' = h Left          ＝⟨refl⟩
        h (left Left)   ＝⟨ hl Left ⟩
        f Left (h Left) ∎

  hL = h Left ＝⟨ fixa (h Left) hL' ⟩
       a      ∎

  hR : h Right ＝ b
  hR = fixb (h Right) (hr Right)


𝕄-at-most-one-wprimrec : {A : 𝓤 ̇ }
                    (a b : A)
                    (f g : 𝕄 → A → A)
                   → (ι : 𝕄-pinductive a b f g)
                   → fixed-point-conditions a b f g
                   → (h k : 𝕄 → A)
                   → is-wprimrec f g h
                   → is-wprimrec f g k
                   → h ∼ k

𝕄-at-most-one-wprimrec a b f g ι fixc h k (hl , hr) (kl , kr) =

  𝕄-at-most-one-primrec a b f g ι h k
    (wprimrec-primitive-recursive a b f g h fixc (hl , hr))
    (wprimrec-primitive-recursive a b f g k fixc (kl , kr))


𝕄-wprimrec-uniqueness : {A : 𝓤 ̇ }
                    (a b : A)
                    (f g : 𝕄 → A → A)
                   → (ι : 𝕄-pinductive a b f g)
                   → fixed-point-conditions a b f g
                   → (h : 𝕄 → A)
                   → is-wprimrec f g h
                   → h ∼ 𝕄-primrec a b f g ι

𝕄-wprimrec-uniqueness a b f g ι fixc h hph =
  𝕄-at-most-one-wprimrec a b f g ι fixc h
   (𝕄-primrec a b f g ι) hph
   (primrec-is-wprimrec a b f g ( 𝕄-primrec a b f g ι) (𝕄-primrec-primitive-recursive a b f g ι))

\end{code}

Definition by cases of functions 𝕄 → A is a particular case of
parametric recursion.

Given a b : A and f g : 𝕄 → A, we want to define h : 𝕄 → A by cases as
follows:

      h Left      ＝ a
      h Right     ＝ b
      h (left x)  = f x
      h (right x) = g x

For this to be well defined we need the following endpoint agreement
conditions:

  (1) a ＝ f Left,
  (2) f Right ＝ g Left,
  (3) b ＝ g Right.

If we take a = f Left and b = g Left, so that (1) and (2) hold, we are
left with condition (3) as the only assumption, and the condition on h
becomes

      h Left      ＝ f Left,
      h Right     ＝ g Right,
      h (left x)  = f x,
      h (right x) = g x.

But also the first two equations follow from the second two, since

     h Left  = h (left Left)   = f Left,
     h Right = h (right Right) = g right.

Hence it is enough to consider the endpoint agreement condition (3)
and work with the equations

      h (left x)  = f x,
      h (right x) = g x.

Hence 𝕄-cases gives the mediating map of a pushout diagram that glues
two copies of the dyadic interval, identifying the end of one with the
beginning of the other, so that 𝕄 is equivalent to the pushout 𝕄 +₁ 𝕄:

      𝕄 ≃ 𝕄 +₁ 𝕄

when f = left and g = right. The function 𝕄-cases defined below
produces the mediating map of the pushout:

The following constructions and facts are all particular cases of
those for 𝕄-primrec.

\begin{code}

𝕄-caseable : (A : 𝓤 ̇ ) → (𝕄 → A) → (𝕄 → A) → 𝓤 ̇
𝕄-caseable A f g = is-set A × (f Right ＝ g Left)

𝕄-caseable-gives-pinductive : (A : 𝓤 ̇ ) (f g : 𝕄 → A)
                             → 𝕄-caseable A f g
                             → 𝕄-pinductive (f Left) (g Right) (λ x _ → f x) (λ x _ → g x)
𝕄-caseable-gives-pinductive A f g (A-is-set , p) = (λ _ → A-is-set) , refl , p , refl

𝕄-cases : {A : 𝓤 ̇ } (f g : 𝕄 → A) → 𝕄-caseable A f g → 𝕄 → A
𝕄-cases f g ι = 𝕄-primrec (f Left) (g Right) (λ x _ → f x) (λ x _ → g x) (𝕄-caseable-gives-pinductive _ f g ι)


case-equations : {A : 𝓤 ̇ } → (𝕄 → A) → (𝕄 → A) → (𝕄 → A) → 𝓤 ̇
case-equations f g h = (h ∘ left  ∼ f)
                     × (h ∘ right ∼ g)

𝕄-cases-redundant-equations : {A : 𝓤 ̇ }
                    (f g : 𝕄 → A)
                  → (p : 𝕄-caseable A f g)
                  → (𝕄-cases f g p Left    ＝ f Left)
                  × (𝕄-cases f g p Right   ＝ g Right)
                  × (𝕄-cases f g p ∘ left  ∼ f)
                  × (𝕄-cases f g p ∘ right ∼ g)

𝕄-cases-redundant-equations f g ι = 𝕄-primrec-primitive-recursive
                                      (f Left) (g Right)
                                      (λ x _ → f x)
                                      (λ x _ → g x)
                                      (𝕄-caseable-gives-pinductive _ f g ι)


𝕄-cases-equations : {A : 𝓤 ̇ }
                    (f g : 𝕄 → A)
                  → (p : 𝕄-caseable A f g)
                  → case-equations f g (𝕄-cases f g p)

𝕄-cases-equations f g p = primrec-is-wprimrec (f Left) (g Right) (λ x _ → f x) (λ x _ → g x) (𝕄-cases f g p)
                           (𝕄-cases-redundant-equations f g p)

𝕄-at-most-one-cases : {A : 𝓤 ̇ }
                    (f g : 𝕄 → A)
                   → 𝕄-caseable A f g
                   → (h k : 𝕄 → A)
                   → case-equations f g h
                   → case-equations f g k
                   → h ∼ k

𝕄-at-most-one-cases f g ι = 𝕄-at-most-one-wprimrec
                              (f Left)
                              (g Right)
                              (λ x _ → f x)
                              (λ x _ → g x)
                              (𝕄-caseable-gives-pinductive _ f g ι)
                              (u , v)
  where
   u : ∀ a' → a' ＝ f Left → a' ＝ f Left
   u a' p = p

   v : ∀ b' → b' ＝ g Right → b' ＝ g Right
   v a' p = p

𝕄-cases-uniqueness : {A : 𝓤 ̇ }
                 (f g : 𝕄 → A)
                → (p : 𝕄-caseable A f g)
                → (h : 𝕄 → A)
                → case-equations f g h
                → h ∼ 𝕄-cases f g p

𝕄-cases-uniqueness f g p h he = 𝕄-at-most-one-cases f g p h (𝕄-cases f g p) he (𝕄-cases-equations f g p)

𝕄-cases-L : {A : 𝓤 ̇ } (f g : 𝕄 → A) (p : 𝕄-caseable A f g)
          → 𝕄-cases f g p Left ＝ f Left
𝕄-cases-L f g p = pr₁ (𝕄-cases-redundant-equations f g p)

𝕄-cases-R : {A : 𝓤 ̇ } (f g : 𝕄 → A) (p : 𝕄-caseable A f g)
          → 𝕄-cases f g p Right ＝ g Right
𝕄-cases-R f g p = pr₁ (pr₂ (𝕄-cases-redundant-equations f g p))

𝕄-cases-l : {A : 𝓤 ̇ } (f g : 𝕄 → A) (p : 𝕄-caseable A f g)
          → 𝕄-cases f g p ∘ left ∼ f
𝕄-cases-l f g p = pr₁ (pr₂ (pr₂ ((𝕄-cases-redundant-equations f g p))))

𝕄-cases-r : {A : 𝓤 ̇ } (f g : 𝕄 → A) (p : 𝕄-caseable A f g)
          → 𝕄-cases f g p ∘ right ∼ g
𝕄-cases-r f g p = pr₂ (pr₂ (pr₂ ((𝕄-cases-redundant-equations f g p))))

\end{code}

We now specialize to A = 𝕄 for notational convenience:

\begin{code}

𝕄𝕄-caseable : (f g : 𝕄 → 𝕄) → 𝓤₀ ̇
𝕄𝕄-caseable f g = f Right ＝ g Left

𝕄𝕄-cases : (f g : 𝕄 → 𝕄) → 𝕄𝕄-caseable f g → (𝕄 → 𝕄)
𝕄𝕄-cases f g p = 𝕄-cases f g (𝕄-is-set , p)

\end{code}

Here are some examples:

\begin{code}

center : 𝕄 → 𝕄
center = 𝕄𝕄-cases (left ∘ right) (right ∘ left) refl

center-l : (x : 𝕄) → center (left x) ＝ left (right x)
center-l = 𝕄-cases-l _ _ (𝕄-is-set , refl)

center-r : (x : 𝕄) → center (right x) ＝ right (left x)
center-r = 𝕄-cases-r _ _ (𝕄-is-set , refl)

left-by-cases : left ∼ 𝕄𝕄-cases (left ∘ left) (center ∘ left) refl
left-by-cases = 𝕄-cases-uniqueness _ _
                  (𝕄-is-set , refl) left ((λ x → refl) , λ x → (center-l x)⁻¹)

right-by-cases : right ∼ 𝕄𝕄-cases (center ∘ right) (right ∘ right) refl
right-by-cases = 𝕄-cases-uniqueness _ _
                   (𝕄-is-set , refl) right ((λ x → (center-r x)⁻¹) , (λ x → refl))

\end{code}

We now define the midpoint operation _⊕_ : 𝕄 → (𝕄 → 𝕄) by
initiality. We will work with a subset of the function type 𝕄 → 𝕄 and
make it into a binary system.

\begin{code}

is-𝓛-function : (𝕄 → 𝕄) → 𝓤₀ ̇
is-𝓛-function f = 𝕄𝕄-caseable (left ∘ f) (center ∘ f)

is-𝓡-function : (𝕄 → 𝕄) → 𝓤₀ ̇
is-𝓡-function f = 𝕄𝕄-caseable (center ∘ f) (right ∘ f)

𝓛 : (f : 𝕄 → 𝕄) → is-𝓛-function f → (𝕄 → 𝕄)
𝓛 f = 𝕄𝕄-cases (left ∘ f) (center ∘ f)

𝓡 : (f : 𝕄 → 𝕄) → is-𝓡-function f → (𝕄 → 𝕄)
𝓡 f = 𝕄𝕄-cases (center ∘ f) (right ∘ f)

preservation-𝓛𝓛 : (f : 𝕄 → 𝕄) (𝓵 : is-𝓛-function f) (𝓻 : is-𝓡-function f) → is-𝓛-function (𝓛 f 𝓵)
preservation-𝓛𝓛 f 𝓵 𝓻 =
  left (𝓛 f 𝓵 Right)      ＝⟨ ap left (𝕄-cases-R (left ∘ f) (center ∘ f) (𝕄-is-set , 𝓵)) ⟩
  left (center (f Right)) ＝⟨ ap left 𝓻 ⟩
  left (right (f Left))   ＝⟨ (center-l (f Left))⁻¹ ⟩
  center (left (f Left))  ＝⟨ (ap center (𝕄-cases-L (left ∘ f) (center ∘ f) (𝕄-is-set , 𝓵)))⁻¹ ⟩
  center (𝓛 f 𝓵 Left)     ∎

preservation-𝓛𝓡 : (f : 𝕄 → 𝕄) (𝓵 : is-𝓛-function f) (𝓻 : is-𝓡-function f) → is-𝓡-function (𝓛 f 𝓵)
preservation-𝓛𝓡 f 𝓵 𝓻 =
  center (𝓛 f 𝓵 Right)      ＝⟨ ap center (𝕄-cases-R (left ∘ f) (center ∘ f) (𝕄-is-set , 𝓵)) ⟩
  center (center (f Right)) ＝⟨ ap center 𝓻 ⟩
  center (right (f Left))   ＝⟨ center-r (f Left) ⟩
  right (left (f Left))     ＝⟨ ap right ((𝕄-cases-L (left ∘ f) (center ∘ f) (𝕄-is-set , 𝓵))⁻¹) ⟩
  right (𝓛 f 𝓵 Left)        ∎

preservation-𝓡𝓛 : (f : 𝕄 → 𝕄) (𝓵 : is-𝓛-function f) (𝓻 : is-𝓡-function f) → is-𝓛-function (𝓡 f 𝓻)
preservation-𝓡𝓛 f 𝓵 𝓻 =
  left (𝓡 f 𝓻 Right)       ＝⟨ ap left (𝕄-cases-R (center ∘ f) (right ∘ f) (𝕄-is-set , 𝓻)) ⟩
  left (right (f Right))   ＝⟨ (center-l (f Right))⁻¹ ⟩
  center (left (f Right))  ＝⟨ ap center 𝓵 ⟩
  center (center (f Left)) ＝⟨ ap center ((𝕄-cases-L (center ∘ f) (right ∘ f) (𝕄-is-set , 𝓻))⁻¹) ⟩
  center (𝓡 f 𝓻 Left)      ∎

preservation-𝓡𝓡 : (f : 𝕄 → 𝕄) (𝓵 : is-𝓛-function f) (𝓻 : is-𝓡-function f) → is-𝓡-function (𝓡 f 𝓻)
preservation-𝓡𝓡 f 𝓵 𝓻 =
  center (𝓡 f 𝓻 Right)     ＝⟨ ap center (𝕄-cases-R (center ∘ f) (right ∘ f) (𝕄-is-set , 𝓻)) ⟩
  center (right (f Right)) ＝⟨ 𝕄-cases-r (left ∘ right) (right ∘ left) (𝕄-is-set , refl) (f Right) ⟩
  right (left (f Right))   ＝⟨ ap right 𝓵 ⟩
  right (center (f Left))  ＝⟨ ap right ((𝕄-cases-L (center ∘ f) (right ∘ f) (𝕄-is-set , 𝓻))⁻¹) ⟩
  right (𝓡 f 𝓻 Left)       ∎

is-𝓛𝓡-function : (𝕄 → 𝕄) → 𝓤₀ ̇
is-𝓛𝓡-function f = is-𝓛-function f × is-𝓡-function f

being-𝓛𝓡-function-is-prop : (f : 𝕄 → 𝕄) → is-prop (is-𝓛𝓡-function f)
being-𝓛𝓡-function-is-prop f = ×-is-prop 𝕄-is-set 𝕄-is-set

\end{code}

The desired subset of the function type 𝕄 → 𝕄 is this:

\begin{code}

F : 𝓤₀ ̇
F = Σ f ꞉ (𝕄 → 𝕄) , is-𝓛𝓡-function f

\end{code}

We now need to assume function extensionality.

\begin{code}

open import UF.Base
open import UF.FunExt

module _ (fe  : Fun-Ext) where

 F-is-set : is-set F
 F-is-set = subsets-of-sets-are-sets (𝕄 → 𝕄) is-𝓛𝓡-function
             (Π-is-set fe (λ _ → 𝕄-is-set))
             (λ {f} → being-𝓛𝓡-function-is-prop f)

 𝑙𝑒𝑓𝑡 𝑟𝑖𝑔ℎ𝑡 : F → F
 𝑙𝑒𝑓𝑡 (f , (𝓵 , 𝓻))  = 𝓛 f 𝓵 , preservation-𝓛𝓛 f 𝓵 𝓻 , preservation-𝓛𝓡 f 𝓵 𝓻
 𝑟𝑖𝑔ℎ𝑡 (f , (𝓵 , 𝓻)) = 𝓡 f 𝓻 , preservation-𝓡𝓛 f 𝓵 𝓻 , preservation-𝓡𝓡 f 𝓵 𝓻

 𝐿𝑒𝑓𝑡 𝑅𝑖𝑔ℎ𝑡 : F
 𝐿𝑒𝑓𝑡  = left , refl , refl
 𝑅𝑖𝑔ℎ𝑡 = right , refl , refl

 F-eq-l : 𝐿𝑒𝑓𝑡 ＝ 𝑙𝑒𝑓𝑡 𝐿𝑒𝑓𝑡
 F-eq-l = to-subtype-＝ being-𝓛𝓡-function-is-prop γ
  where
   δ : left ∼ 𝓛 left refl
   δ = left-by-cases

   γ : left ＝ 𝓛 left refl
   γ = dfunext fe δ


 F-eq-lr : 𝑙𝑒𝑓𝑡 𝑅𝑖𝑔ℎ𝑡 ＝ 𝑟𝑖𝑔ℎ𝑡 𝐿𝑒𝑓𝑡
 F-eq-lr = to-subtype-＝ being-𝓛𝓡-function-is-prop v
  where
   i = λ (x : 𝕄) → 𝕄𝕄-cases (left ∘ right) (center ∘ right) refl (left x) ＝⟨ 𝕄-cases-l _ _ (𝕄-is-set , refl) x ⟩
                   left (right x)                                           ＝⟨ (center-l x)⁻¹ ⟩
                   center (left x)                                          ∎

   ii =  λ (x : 𝕄) → 𝕄𝕄-cases (left ∘ right) (center ∘ right) refl (right x)   ＝⟨ 𝕄-cases-r _ _ (𝕄-is-set , refl) x ⟩
                     center (right x)                                          ＝⟨ center-r x ⟩
                     right (left x)                                            ∎

   iii : 𝕄𝕄-cases (left ∘ right)  (center ∘ right) refl
       ∼ 𝕄𝕄-cases (center ∘ left) (right ∘ left)   refl
   iii = 𝕄-cases-uniqueness _ _ (𝕄-is-set , refl) (𝕄𝕄-cases _ _ refl) (i , ii)

   iv : 𝓛 right refl ∼ 𝓡 left refl
   iv = iii

   v : 𝓛 right refl ＝ 𝓡 left refl
   v = dfunext fe iv


 F-eq-r : 𝑅𝑖𝑔ℎ𝑡 ＝ 𝑟𝑖𝑔ℎ𝑡 𝑅𝑖𝑔ℎ𝑡
 F-eq-r = to-subtype-＝ being-𝓛𝓡-function-is-prop γ
  where
   δ : right ∼ 𝓡 right refl
   δ = right-by-cases

   γ : right ＝ 𝓡 right refl
   γ = dfunext fe δ


 𝓕 : BS 𝓤₀
 𝓕 = (F , (𝐿𝑒𝑓𝑡 , 𝑅𝑖𝑔ℎ𝑡 , 𝑙𝑒𝑓𝑡 , 𝑟𝑖𝑔ℎ𝑡) , (F-is-set , F-eq-l , F-eq-lr , F-eq-r))

 mid : 𝕄 → F
 mid = 𝓜-rec 𝓕

 _⊕_ : 𝕄 → 𝕄 → 𝕄
 x ⊕ y = pr₁ (mid x) y

 ⊕-property : (x : 𝕄)
            → (left   (x ⊕ Right) ＝ center (x ⊕ Left))
            × (center (x ⊕ Right) ＝ right  (x ⊕ Left))
 ⊕-property x = pr₂ (mid x)

 mid-is-hom : is-hom 𝓜 𝓕 (𝓜-rec 𝓕)
 mid-is-hom = 𝓜-rec-is-hom 𝓕

 mid-is-hom-L : mid Left ＝ 𝐿𝑒𝑓𝑡
 mid-is-hom-L = is-hom-L 𝓜 𝓕 mid mid-is-hom

 mid-is-hom-L' : (y : 𝕄) → Left ⊕ y ＝ left y
 mid-is-hom-L' y = ap (λ - → pr₁ - y) mid-is-hom-L

 mid-is-hom-R : mid Right ＝ 𝑅𝑖𝑔ℎ𝑡
 mid-is-hom-R = is-hom-R 𝓜 𝓕 mid mid-is-hom

 mid-is-hom-R' : (y : 𝕄) → Right ⊕ y ＝ right y
 mid-is-hom-R' y = ap (λ - → pr₁ - y) mid-is-hom-R

 mid-is-hom-l : (x : 𝕄) → mid (left x) ＝ 𝑙𝑒𝑓𝑡 (mid x)
 mid-is-hom-l = is-hom-l 𝓜 𝓕 mid mid-is-hom

 mid-is-hom-l' : (x y : 𝕄)
               → (left x ⊕ Left    ＝ left   (x ⊕ Left))
               × (left x ⊕ Right   ＝ center (x ⊕ Right))
               × (left x ⊕ left y  ＝ left   (x ⊕ y))
               × (left x ⊕ right y ＝ center (x ⊕ y))
 mid-is-hom-l' x y = u , v , w , t
  where
   α : (y : 𝕄)
     → left x ⊕ y
       ＝ 𝕄𝕄-cases (left ∘ (x ⊕_)) (center ∘ (x ⊕_)) (pr₁ (⊕-property x)) y
   α y = left x ⊕ y           ＝⟨refl⟩
         pr₁ (mid (left x)) y ＝⟨ happly (ap pr₁ (mid-is-hom-l x)) y ⟩
         pr₁ (𝑙𝑒𝑓𝑡 (mid x)) y   ＝⟨refl⟩
         𝕄𝕄-cases (left ∘ (x ⊕_)) (center ∘ (x ⊕_)) (pr₁ (⊕-property x)) y ∎

   u = α Left      ∙ 𝕄-cases-L (left ∘ (x ⊕_)) (center ∘ (x ⊕_)) (𝕄-is-set , pr₁ (⊕-property x))
   v = α Right     ∙ 𝕄-cases-R (left ∘ (x ⊕_)) (center ∘ (x ⊕_)) (𝕄-is-set , pr₁ (⊕-property x))
   w = α (left y)  ∙ 𝕄-cases-l (left ∘ (x ⊕_)) (center ∘ (x ⊕_)) (𝕄-is-set , pr₁ (⊕-property x)) y
   t = α (right y) ∙ 𝕄-cases-r (left ∘ (x ⊕_)) (center ∘ (x ⊕_)) (𝕄-is-set , pr₁ (⊕-property x)) y

 mid-is-hom-r : (x : 𝕄) → mid (right x) ＝ 𝑟𝑖𝑔ℎ𝑡 (mid x)
 mid-is-hom-r = is-hom-r 𝓜 𝓕 mid mid-is-hom

 mid-is-hom-r' : (x y : 𝕄)
               → (right x ⊕ Right   ＝ right  (x ⊕ Right))
               × (right x ⊕ Left    ＝ center (x ⊕ Left))
               × (right x ⊕ left y  ＝ center (x ⊕ y))
               × (right x ⊕ right y ＝ right  (x ⊕ y))
 mid-is-hom-r' x y = u , v , w , t
  where
   α : (y : 𝕄)
     → right x ⊕ y
       ＝ 𝕄𝕄-cases (center ∘ (x ⊕_)) (right ∘ (x ⊕_)) (pr₂ (⊕-property x)) y
   α y = right x ⊕ y           ＝⟨refl⟩
         pr₁ (mid (right x)) y ＝⟨ happly (ap pr₁ (mid-is-hom-r x)) y ⟩
         pr₁ (𝑟𝑖𝑔ℎ𝑡 (mid x)) y   ＝⟨refl⟩
         𝕄𝕄-cases (center ∘ (x ⊕_)) (right ∘ (x ⊕_)) (pr₂ (⊕-property x)) y ∎

   u = α Right ∙ 𝕄-cases-R (center ∘ (x ⊕_)) (right ∘ (x ⊕_)) (𝕄-is-set , pr₂ (⊕-property x))
   v = α Left ∙ 𝕄-cases-L (center ∘ (x ⊕_)) (right ∘ (x ⊕_)) (𝕄-is-set , pr₂ (⊕-property x))
   w = α (left y)  ∙ 𝕄-cases-l (center ∘ (x ⊕_)) (right ∘ (x ⊕_)) (𝕄-is-set , pr₂ (⊕-property x)) y
   t = α (right y) ∙ 𝕄-cases-r (center ∘ (x ⊕_)) (right ∘ (x ⊕_)) (𝕄-is-set , pr₂ (⊕-property x)) y

\end{code}

So, the set of defining equations is the following, where it can be
seen that there is some redundancy:

     (  left   (x ⊕ Right) ＝ center (x ⊕ Left)  )
   × (  center (x ⊕ Right) ＝ right  (x ⊕ Left)  )

   × (  Left    ⊕ y        ＝ left y             )
   × (  Right   ⊕ y        ＝ right y            )
   × (  left x  ⊕ Left     ＝ left (x ⊕ Left)    )
   × (  left x  ⊕ Right    ＝ center (x ⊕ Right) )
   × (  left x  ⊕ left y   ＝ left (x ⊕ y)       )
   × (  left x  ⊕ right y  ＝ center (x ⊕ y)     )
   × (  right x ⊕ Right    ＝ right (x ⊕ Right)  )
   × (  right x ⊕ Left     ＝ center (x ⊕ Left)  )
   × (  right x ⊕ left y   ＝ center (x ⊕ y)     )
   × (  right x ⊕ right y  ＝ right (x ⊕ y)      )

The first two come from the binary system F and the remaining ones from the homomorphism condition and cases analysis.

Next we want to show that

  _⊕_ : 𝕄 → 𝕄 → 𝕄

makes the initial binary system into the free midpoint algebra over
two generators (taken to be Left and Right, as expected), where the
midpoint axioms are

   (idempotency)    x ⊕ x ＝ x,
   (commutativity)  x ⊕ y ＝ y ⊕ x,
   (transposition)  (u ⊕ v) ⊕ (x ⊕ y) ＝ (u ⊕ x) ⊕ (v ⊕ y).

In fact, in the initial binary system, there is a unique midpoint
operation _⊕_ such that

   L ⊕ x = left x,
   R ⊕ x = right x.

To be continued.
