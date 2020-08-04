Martin Escardo, 4th August 2020. (Going back to 1993 or earlier.)

A construction of the initial binary system in Spartan MLTT, without
HITs or quotients, or extensionality axioms.

A binary system is a type A with distinguished points a b : A and
functions f g : A → A such that

 (1) a = f a,
 (2) b = g b,
 (3) f b = g a.

We don't require the type A to be a set in the sense of univalent
mathematics.

The initial binary system is the closed interval of dyadic rationals
(see below for a picture).

We construct it as a quotient of the following type 𝔹, with L,R,l,r
corresponding to a,b,f,g, without assuming that our type theory has
quotients - it just happens to have the quotient we want.

\begin{code}

{-# OPTIONS --without-K --safe --exact-split #-}

module InitialBinarySystem where

open import SpartanMLTT

data 𝔹 : 𝓤₀ ̇ where
 L R : 𝔹
 l r : 𝔹 → 𝔹

\end{code}

We want to perform the identifications

 (1) L = l L,
 (2) R = r R,
 (3) l R = r L,

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
normality-is-decidable L         = inl *
normality-is-decidable R         = inl *
normality-is-decidable (l L)     = inr id
normality-is-decidable (l R)     = inl *
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
𝕝-preserves-normality L     i = *
𝕝-preserves-normality R     i = *
𝕝-preserves-normality (l x) i = i
𝕝-preserves-normality (r x) i = i

𝕣-preserves-normality : (x : 𝔹) → is-normal x → is-normal (𝕣 x)
𝕣-preserves-normality L         * = *
𝕣-preserves-normality R         * = *
𝕣-preserves-normality (l R)     * = *
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
normalize-is-normal L     = *
normalize-is-normal R     = *
normalize-is-normal (l x) = 𝕝-preserves-normality (normalize x) (normalize-is-normal x)
normalize-is-normal (r x) = 𝕣-preserves-normality (normalize x) (normalize-is-normal x)

\end{code}

We now prove that normal points are fixed points of the normalization
function. We need a simple lemma for that purpose, proved by case
analysis.

\begin{code}

𝕣r-equation : (x : 𝔹) → is-normal (r x) → 𝕣 (r x) ≡ r (r x)
𝕣r-equation L     i = 𝟘-elim i
𝕣r-equation R     i = 𝟘-elim i
𝕣r-equation (l x) i = refl
𝕣r-equation (r x) i = refl

\end{code}

To prove that normal points are fixed points of the normalization
function, we need to simultaneously prove two lemmas by induction:

\begin{code}

nfp-lemma-l : (x : 𝔹) → is-normal (l x) → 𝕝 (normalize x) ≡ l x
nfp-lemma-r : (x : 𝔹) → is-normal (r x) → 𝕣 (normalize x) ≡ r x

nfp-lemma-l L     i = 𝟘-elim i
nfp-lemma-l R     * = refl
nfp-lemma-l (l x) i = ap 𝕝 (nfp-lemma-l x i)
nfp-lemma-l (r x) i = ap 𝕝 (nfp-lemma-r x i)

nfp-lemma-r L     i = 𝟘-elim i
nfp-lemma-r R     i = 𝟘-elim i
nfp-lemma-r (l x) i = ap 𝕣 (nfp-lemma-l x i)
nfp-lemma-r (r x) i = 𝕣 (𝕣 (normalize x)) ≡⟨ ap 𝕣 (nfp-lemma-r x i) ⟩
                      𝕣 (r x)                 ≡⟨ 𝕣r-equation x i                             ⟩
                      r (r x)                 ∎
\end{code}

Now the proof of the desired result is by cases (without induction),
using the above two lemmas.

\begin{code}

normals-are-fixed-points : (x : 𝔹) → is-normal x → normalize x ≡ x
normals-are-fixed-points L     * = refl
normals-are-fixed-points R     * = refl
normals-are-fixed-points (l x) i = nfp-lemma-l x i
normals-are-fixed-points (r x) i = nfp-lemma-r x i

\end{code}

We have the following two corollaries:

\begin{code}

fixed-points-are-normal : (x : 𝔹) → normalize x ≡ x → is-normal x
fixed-points-are-normal x p = transport is-normal p (normalize-is-normal x)

normalization-idemp : (x : 𝔹) → normalize (normalize x) ≡ normalize x
normalization-idemp x = normals-are-fixed-points (normalize x) (normalize-is-normal x)

\end{code}

But we actually don't need the normalization procedure to construct
the initial binary system, whose underlying type will be called 𝕄.
However, we will use some of the above machinery.

\begin{code}

𝕄 = Σ x ꞉ 𝔹 , is-normal x

Left Center Right : 𝕄
Left   = L , *
Center = C , *
Right  = R , *

left right : 𝕄 → 𝕄
left  (x , i) = 𝕝 x , 𝕝-preserves-normality x i
right (x , i) = 𝕣 x , 𝕣-preserves-normality x i

𝕄-eq-l : Left ≡ left Left
𝕄-eq-l = refl

𝕄-eq-r : Right ≡ right Right
𝕄-eq-r = refl

𝕄-eq-lr : left Right ≡ right Left
𝕄-eq-lr = refl

𝕄-eq-lm : left Right ≡ Center
𝕄-eq-lm = refl

𝕄-eq-rm : right Left ≡ Center
𝕄-eq-rm = refl

\end{code}

We now use the above to show that 𝕄 is the initial binary system.

\begin{code}

binary-system-structure : 𝓤 ̇ → 𝓤 ̇
binary-system-structure A = A × A × (A → A) × (A → A)

binary-system-axioms : (A : 𝓤 ̇ ) → binary-system-structure A → 𝓤 ̇
binary-system-axioms A (a , b , f , g) = (a ≡ f a) × (f b ≡ g a) × (b ≡ g b)

BS : (𝓤 : Universe) → 𝓤 ⁺ ̇
BS 𝓤 = Σ A ꞉ 𝓤 ̇ , Σ s ꞉ binary-system-structure A , binary-system-axioms A s

𝓜 : BS 𝓤₀
𝓜 = (𝕄 , (Left , Right , left , right) , (𝕄-eq-l , 𝕄-eq-lr , 𝕄-eq-r))

open import UF-SIP
open sip

\end{code}

The notion of homomorphism of binary systems is the expected one:

\begin{code}

is-hom : (𝓐 : BS 𝓤) (𝓐' : BS 𝓥) → (⟨ 𝓐 ⟩ → ⟨ 𝓐' ⟩) → 𝓤 ⊔ 𝓥 ̇
is-hom (A , (a , b , f , g) , _) (A' , (a' , b' , f' , g') , _) h =
   (h a ≡ a')
 × (h b ≡ b')
 × (h ∘ f ∼ f' ∘ h)
 × (h ∘ g ∼ g' ∘ h)

\end{code}

In order to show that 𝓜 is the initial binary system, we first prove
(the expected) induction principle for its underlying type 𝕄 (with a
perhaps unexpected proof):

\begin{code}

𝕄-induction : (P : 𝕄 → 𝓤 ̇ )
            → P Left
            → P Right
            → ((x : 𝕄) → P x → P (left x))
            → ((x : 𝕄) → P x → P (right x))
            → (x : 𝕄) → P x

𝕄-induction P a b f g (L ,           *) = a
𝕄-induction P a b f g (R ,           *) = b
𝕄-induction P a b f g (l R ,         i) = f (R , *) b
𝕄-induction P a b f g (l (l x) ,     i) = f (l x , i) (𝕄-induction P a b f g (l x , i))
𝕄-induction P a b f g (l (r x) ,     i) = f (r x , i) (𝕄-induction P a b f g (r x , i))
𝕄-induction P a b f g (r (l R) ,     i) = g (l R , *) (f (R , *) b)
𝕄-induction P a b f g (r (l (l x)) , i) = g (l (l x) , i) (𝕄-induction P a b f g (l (l x) , i))
𝕄-induction P a b f g (r (l (r x)) , i) = g (l (r x) , i) (𝕄-induction P a b f g (l (r x) , i))
𝕄-induction P a b f g (r (r (l x)) , i) = g (r (l x) , i) (𝕄-induction P a b f g (r (l x) , i))
𝕄-induction P a b f g (r (r (r x)) , i) = g (r (r x) , i) (𝕄-induction P a b f g (r (r x) , i))

\end{code}

In MLTT, induction principles come with equations. In our case they
are the expected ones. But notice that some of these equations require
(expected) binary-system-like equations in their premises. Only the
first two don't, and they hold by construction:

\begin{code}

𝕄-induction-eq-Left : (P : 𝕄 → 𝓤 ̇ )
                      (a : P Left)
                      (b : P Right)
                      (f : (x : 𝕄) → P x → P (left x))
                      (g : (x : 𝕄) → P x → P (right x))
                    → 𝕄-induction P a b f g Left ≡ a

𝕄-induction-eq-Left P a b f g = refl

𝕄-induction-eq-Right : (P : 𝕄 → 𝓤 ̇ )
                      (a : P Left)
                      (b : P Right)
                      (f : (x : 𝕄) → P x → P (left x))
                      (g : (x : 𝕄) → P x → P (right x))
                     → 𝕄-induction P a b f g Right ≡ b

𝕄-induction-eq-Right P a b f g = refl

\end{code}

For the next equation for the induction principle, we need the
assumption a ≡ f Left a:

\begin{code}

𝕄-induction-eq-left : (P : 𝕄 → 𝓤 ̇ )
                      (a : P Left)
                      (b : P Right)
                      (f : (x : 𝕄) → P x → P (left x))
                      (g : (x : 𝕄) → P x → P (right x))
                    → a ≡ f Left a
                    → (x : 𝕄) → 𝕄-induction P a b f g (left x) ≡ f x (𝕄-induction P a b f g x)

𝕄-induction-eq-left P a b f g p (L ,   *) = p
𝕄-induction-eq-left P a b f g p (R ,   *) = refl
𝕄-induction-eq-left P a b f g p (l x , i) = refl
𝕄-induction-eq-left P a b f g p (r x , i) = refl

\end{code}

And for the last equation for the induction principle, we need the two
equations f Right b ≡ g Left a and b ≡ g Right b as assumptions:

\begin{code}

𝕄-induction-eq-right : (P : 𝕄 → 𝓤 ̇ )
                      (a : P Left)
                      (b : P Right)
                      (f : (x : 𝕄) → P x → P (left x))
                      (g : (x : 𝕄) → P x → P (right x))
                    → f Right b ≡ g Left a
                    → b ≡ g Right b
                    → (x : 𝕄) → 𝕄-induction P a b f g (right x) ≡ g x (𝕄-induction P a b f g x)

𝕄-induction-eq-right P a b f g p q (L ,       *) = p
𝕄-induction-eq-right P a b f g p q (R ,       *) = q
𝕄-induction-eq-right P a b f g p q (l R ,     i) = refl
𝕄-induction-eq-right P a b f g p q (l (l x) , i) = refl
𝕄-induction-eq-right P a b f g p q (l (r x) , i) = refl
𝕄-induction-eq-right P a b f g p q (r (l x) , i) = refl
𝕄-induction-eq-right P a b f g p q (r (r x) , i) = refl

\end{code}

So the complete set of required equational assumptions for the
equations for the induction principle are

 (1) a ≡ f Left a,
 (2) b ≡ g Right b,
 (3) f Right b ≡ g Left a,

which correspond to the equations for binary systems.

As usual, the recursion principle is a particular case of the
induction principle:

\begin{code}

𝕄-rec : (A : 𝓤 ̇ ) → binary-system-structure A → (𝕄 → A)
𝕄-rec A (a , b , f , g) = 𝕄-induction (λ _ → A) a b (λ _ → f) (λ _ → g)

\end{code}

And so are its equations, which amount to the fact that 𝕄-rec
constructs a homomorphism:

\begin{code}

𝕄-rec-is-hom : (A : 𝓤 ̇ ) (s : binary-system-structure A) (a : binary-system-axioms A s)
              → is-hom 𝓜 (A , s , a) (𝕄-rec A s)
𝕄-rec-is-hom A (a , b , f , g) (eql , eqlr , eqr) = i , ii , iii , iv
 where
  i : 𝕄-rec A (a , b , f , g) Left ≡ a
  i = 𝕄-induction-eq-Left (λ _ → A) a b (λ _ → f) (λ _ → g)

  ii : 𝕄-rec A (a , b , f , g) Right ≡ b
  ii = 𝕄-induction-eq-Right (λ _ → A) a b (λ _ → f) (λ _ → g)

  iii : (x : 𝕄) → 𝕄-rec A (a , b , f , g) (left x) ≡ f (𝕄-rec A (a , b , f , g) x)
  iii = 𝕄-induction-eq-left (λ _ → A) a b (λ _ → f) (λ _ → g) eql

  iv : (x : 𝕄) → 𝕄-rec A (a , b , f , g) (right x) ≡ g (𝕄-rec A (a , b , f , g) x)
  iv = 𝕄-induction-eq-right (λ _ → A) a b (λ _ → f) (λ _ → g) eqlr eqr

\end{code}

We reformulate this as a recursion principle for the binary system 𝓜:

\begin{code}

𝓜-rec : (𝓐 : BS 𝓤)  → 𝕄 → ⟨ 𝓐 ⟩
𝓜-rec (A , s , _) = 𝕄-rec A s

\end{code}

Which is then automatically a homomorphism:

\begin{code}

𝓜-rec-is-hom : (𝓐 : BS 𝓤)
             → is-hom 𝓜 𝓐 (𝓜-rec 𝓐)
𝓜-rec-is-hom (A , s , α) = 𝕄-rec-is-hom A s α

\end{code}

Some boiler plate code to name the projections follows:

\begin{code}

⟨_⟩-Left : (𝓐 : BS 𝓤) → ⟨ 𝓐 ⟩
⟨ (A , (a , b , f , g) , (eql , eqlr , eqr)) ⟩-Left = a


⟨_⟩-Right : (𝓐 : BS 𝓤) → ⟨ 𝓐 ⟩
⟨ (A , (a , b , f , g) , (eql , eqlr , eqr)) ⟩-Right = b


⟨_⟩-left : (𝓐 : BS 𝓤) → ⟨ 𝓐 ⟩ → ⟨ 𝓐 ⟩
⟨ (A , (a , b , f , g) , (eql , eqlr , eqr)) ⟩-left = f


⟨_⟩-right : (𝓐 : BS 𝓤) → ⟨ 𝓐 ⟩ → ⟨ 𝓐 ⟩
⟨ (A , (a , b , f , g) , (eql , eqlr , eqr)) ⟩-right = g


⟨_⟩-eql : (𝓐 : BS 𝓤) → ⟨ 𝓐 ⟩-Left ≡ ⟨ 𝓐 ⟩-left ⟨ 𝓐 ⟩-Left
⟨ (A , (a , b , f , g) , (eql , eqlr , eqr)) ⟩-eql = eql


⟨_⟩-eqr : (𝓐 : BS 𝓤) → ⟨ 𝓐 ⟩-Right ≡ ⟨ 𝓐 ⟩-right ⟨ 𝓐 ⟩-Right
⟨ (A , (a , b , f , g) , (eql , eqlr , eqr)) ⟩-eqr = eqr


⟨_⟩-eqlr : (𝓐 : BS 𝓤) → ⟨ 𝓐 ⟩-left ⟨ 𝓐 ⟩-Right ≡ ⟨ 𝓐 ⟩-right ⟨ 𝓐 ⟩-Left
⟨ (A , (a , b , f , g) , (eql , eqlr , eqr)) ⟩-eqlr = eqlr


is-hom-Left : (𝓐 : BS 𝓤) (𝓑 : BS 𝓥) (h : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
            → is-hom 𝓐 𝓑 h → h (⟨ 𝓐 ⟩-Left) ≡ ⟨ 𝓑 ⟩-Left
is-hom-Left 𝓐 𝓑 h (i , ii , iii , iv) = i


is-hom-Right : (𝓐 : BS 𝓤) (𝓑 : BS 𝓥) (h : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
             → is-hom 𝓐 𝓑 h → h (⟨ 𝓐 ⟩-Right) ≡ ⟨ 𝓑 ⟩-Right
is-hom-Right 𝓐 𝓑 h (i , ii , iii , iv) = ii


is-hom-left : (𝓐 : BS 𝓤) (𝓑 : BS 𝓥) (h : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
            → is-hom 𝓐 𝓑 h → h ∘ ⟨ 𝓐 ⟩-left ∼ ⟨ 𝓑 ⟩-left ∘ h
is-hom-left 𝓐 𝓑 h (i , ii , iii , iv) = iii


is-hom-right : (𝓐 : BS 𝓤) (𝓑 : BS 𝓥) (h : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
             → is-hom 𝓐 𝓑 h → h ∘ ⟨ 𝓐 ⟩-right ∼ ⟨ 𝓑 ⟩-right ∘ h
is-hom-right 𝓐 𝓑 h (i , ii , iii , iv) = iv

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
𝓜-at-most-one-hom 𝓐 h k u v = 𝕄-induction (λ x → h x ≡ k x) i ii iii iv
 where
  i :  h Left ≡ k Left
  i = is-hom-Left 𝓜 𝓐 h u ∙ (is-hom-Left 𝓜 𝓐 k v)⁻¹

  ii : h Right ≡ k Right
  ii = is-hom-Right 𝓜 𝓐 h u ∙ (is-hom-Right 𝓜 𝓐 k v)⁻¹

  iii : (x : 𝕄) → h x ≡ k x → h (left x) ≡ k (left x)
  iii x p = h (left x)       ≡⟨ is-hom-left 𝓜 𝓐 h u x ⟩
            ⟨ 𝓐 ⟩-left (h x) ≡⟨ ap ⟨ 𝓐 ⟩-left p ⟩
            ⟨ 𝓐 ⟩-left (k x) ≡⟨ (is-hom-left 𝓜 𝓐 k v x)⁻¹ ⟩
            k (left x)       ∎

  iv : (x : 𝕄) → h x ≡ k x → h (right x) ≡ k (right x)
  iv x p =  h (right x)       ≡⟨ is-hom-right 𝓜 𝓐 h u x ⟩
            ⟨ 𝓐 ⟩-right (h x) ≡⟨ ap ⟨ 𝓐 ⟩-right p ⟩
            ⟨ 𝓐 ⟩-right (k x) ≡⟨ (is-hom-right 𝓜 𝓐 k v x)⁻¹ ⟩
            k (right x)       ∎

\end{code}

Notice that we didn't require binary systems to have underlying types
that are sets (in the sense of univalent mathematics) as their
underlying objects, but that the underlying type of the initial binary
system, having decidable equality, is a set. This is similar to what
happens with the unary system (ℕ , zero, succ) of natural numbers.

In another file, we will define the midpoint operation

  _⊕_ : 𝕄 → 𝕄 → 𝕄

and show that it makes the initial binary system into the free
midpoint algebra over two generators (taken to be Left and Right, as
expected), where the midpoint algebra axioms are

   (idempotency)    x ⊕ x ≡ x,
   (commutativity)  x ⊕ y ≡ y ⊕ x,
   (transposition)  (u ⊕ v) ⊕ (x ⊕ y) ≡ (u ⊕ x) ⊕ (v ⊕ y).
