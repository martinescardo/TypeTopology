Andrew Swan, February 7th 2024

This is a generalisation of some of the results by Martín Escardó in
TypeTopology.PropTychonoff, based on the observation that for
propositions P, the functor sending A to P → A is a
modality. Modalities of this form are an important special case and
they have a name; they are *open modalities* (Example 1.7 in
[1]). However, we will show a version of the theorem is not only true
for open modalities, but for all modalities.

For another example, let ∇ be the modality of double negation sheaves
(Example 3.41 of [1]). The internal logic in this reflective universe
is boolean. It follows that ∇ (is-compact∙ A) holds for all types A,
and so we can deduce that ∇ A is always compact.

TODO: add double negation sheaves to the library

We can also see as a special case that truncation preserves
compactness, although it seems unlikely there are any good examples of
compact higher types where it isn't already clear that the
0-truncation is compact.

When formulated in terms of modalities, the result is best thought of
as an "absoluteness result." When working in models of some theory, a
logical formula might make sense stated both internally in the model
and for the same object viewed externally from outside the
model. Absoluteness says that these two statements are equivalent.

In this case we are thinking of reflective subuniverses as models of
type theory sitting inside some larger "external" model of type
theory. We will show that compactness is an upwards absolute
notion. That is, if a type inside the reflective subuniverse is
compact with respect to the internal logic of the subuniverse then it
is compact viewed outside the subuniverse as just a type. The converse
does not quite hold, so potentially there could be compact types where
the internal statement of compactness is not true, and we don't get
full absoluteness.

We note that the result holds for all modalities with no further
conditions and in particular the modality is not required to be lex,
or to preserve 𝟘. For the main theorem, we don't even need a full
modality, and the weaker notion of reflective subuniverse suffices.

[1] Rijke, Shulman, Spitters, Modalities in homotopy type theory,
https://doi.org/10.23638/LMCS-16(1:2)2020

\begin{code}
{-# OPTIONS --safe --without-K --exact-split --auto-inline #-}
open import MLTT.Spartan
open import MLTT.Two-Properties

open import UF.Base
open import UF.Univalence
open import UF.UA-FunExt
open import UF.UniverseEmbedding
open import UF.Equiv

open import Modal.Subuniverse
import Modal.SigmaClosedReflectiveSubuniverse

open import TypeTopology.CompactTypes
\end{code}

Throughout we are going to assume that we are given a reflective
subuniverse. We import some notation and lemmas from
Modal.ReflectiveSubuniverse. In particular, we write ○ for the
modality corresponding to the reflective subuniverse.

\begin{code}
module TypeTopology.AbsolutenessOfCompactness
 (P : subuniverse 𝓤 𝓥)
 (P-is-reflective : subuniverse-is-reflective P)
 where

open import Modal.ReflectiveSubuniverse P P-is-reflective
\end{code}

We now give some statements related to compactness. We first consider
what it means for a type in the reflective subuniverse to be compact
according to the internal logic. We recall that when we interpret type
theory in a reflective subuniverse, this is done by induction on the
structure of types. Dependent functions, Σ-types and identity types
are the same as externally, whereas whenever we see an inductive type
(such as 𝟚) we need to apply the modality.

Unwinding all this, gives the following internal definition of
compactness for the reflective subuniverse.

\begin{code}
is-internal-compact∙ : 𝓤 ̇ → 𝓤 ̇
is-internal-compact∙ A =
 (F : A → ○ (Lift _ 𝟚))
 → Σ a₀ ꞉ A , (F a₀ ＝ η _ (lift 𝓤 ₁)
 → (a : A)
 → F a ＝ η _ (lift 𝓤 ₁))
\end{code}

It turns out that in addition to internal compactness, it's also
useful to consider the weaker notion below. The reason for this is
that although we can show internal compact implies compact, we don't
have the converse direction. However, we will be able to show that
compact implies weak internal compact.

This weaker notion will also be useful for making the connection with
the results of TypeTopology.PropTychonoff clear. To do this, we will
also look at the type obtained by simply applying the modality to the
statement that A is compact. We will be able to show ○ (is-compact∙ A)
→ is-weak-internal-compact∙, but not the same implication for just
internal compact.

\begin{code}
is-weak-internal-compact∙ : 𝓤 ̇ → 𝓤 ̇
is-weak-internal-compact∙ A =
 (F : A → 𝟚)
   → Σ a₀ ꞉ A , (F a₀ ＝ ₁ → (a : A) → η _ (lift 𝓤 (F a)) ＝ η _ (lift 𝓤 ₁))
\end{code}

We check that weak internal compactness actually is weaker.

\begin{code}
internal-compact-implies-weak-internal-compact
 : (A : 𝓤 ̇ )
 → is-internal-compact∙ A
 → is-weak-internal-compact∙ A

internal-compact-implies-weak-internal-compact A c F =
 (pr₁ weak-internal-instance) ,
 (λ p → pr₂ weak-internal-instance (ap (η _ ∘ lift _) p))

 where
  F' : A → ○ (Lift _ 𝟚)
  F' = η _ ∘ (lift _) ∘ F

  weak-internal-instance
   : Σ a₀ ꞉ A , (F' a₀ ＝ η _ (lift 𝓤 ₁) → (a : A) → F' a ＝ η _ (lift 𝓤 ₁))

  weak-internal-instance = c F'
\end{code}

Note that we defined weak internal compactness so that it is also
implied by compactness.

\begin{code}
compact-implies-weak-internal-compact
 : (A : 𝓤 ̇ )
 → is-compact∙ A
 → is-weak-internal-compact∙ A

compact-implies-weak-internal-compact A c F =
 (pr₁ (c F)) , (λ p a → ap (η _ ∘ lift _) (pr₂ (c F) p a))

\end{code}

We can now prove the main theorem: whenever a modal type is weak
internal compact, it is (externally) compact.

Although it looks a bit different, this is the argument that most
closely follows the original theorem prop-tychonoff.

\begin{code}
weak-internal-compact-implies-compact
 : (A : 𝓤 ̇ )
 → (A-modal : is-modal A)
 → is-weak-internal-compact∙ A
 → is-compact∙ A
weak-internal-compact-implies-compact A A-modal c F = a₀ , a₀-works
 where
\end{code}

Constructing a candidate universal witness is very easy. We just use
the same one given by weak internal compactness.

\begin{code}
  internal-compactness-instance :
   Σ a₀ ꞉ A , (F a₀ ＝ ₁ → (a : A) → η _ (lift 𝓤 (F a)) ＝ η _ (lift 𝓤 ₁))
  internal-compactness-instance = c F

  a₀ = pr₁ internal-compactness-instance
\end{code}

To show that the candidate universal witness actually works, we need
to check that the boolean F a is 1, whenever F a₀ is. We will split
into two cases depending on the value of F a. If F a = 1, then we are
already done. The tricky case, which we deal with in the lemma below
is getting a proof F a = 1 out of a proof of F a = 0. We would like to
argue by contradiction from the fact that F a₀ = 1, but F a =
0. However, all that weak internal compactness tells us is that η(F a)
= η(1) as elements of ○ 𝟚.  This is actually consistant with F a = 0:
consider the open modality on the empty type.

The idea of the lemma is as follows: given η(F a) = η(1), we can
derive a proof that η(0) = η(1). We define a map 𝟚 → A sending 0 to a
and 1 to a₀. Since A is modal, this map must factor through ○ 𝟚, and
so we can apply ap to our path to get the required path a = a₀.

\begin{code}
  lemma
   : (F a₀ ＝ ₁)
   → (a : A)
   → (F a ＝ ₀)
   → (a ＝ a₀)
  lemma p a q =
   a ＝⟨ by-construction ⟩
   t (lift _ ₀) ＝⟨ ○-rec-compute _ _ _ _ _ ⁻¹ ⟩
   t' (η _ (lift _ ₀)) ＝⟨ ap t' modal-zero-is-modal-one ⟩
   t' (η _ (lift _ ₁)) ＝⟨ ○-rec-compute _ _ _ _ _ ⟩
   t (lift _ ₁) ＝⟨ by-construction ⟩
   a₀ ∎

   where
    t : Lift _ 𝟚 → A
    t = 𝟚-cases a a₀ ∘ lower

    t' : ○ (Lift _ 𝟚) → A
    t' = ○-rec _ _ A-modal t

    modal-zero-is-modal-one : η _ (lift _ ₀) ＝ η _ (lift _ ₁)
    modal-zero-is-modal-one =
     η _ (lift _ ₀) ＝⟨ ap (η _ ∘ lift _) (q ⁻¹) ⟩
     η _ (lift _ (F a)) ＝⟨ pr₂ internal-compactness-instance p a ⟩
     η _ (lift _ ₁) ∎

  a₀-works : F a₀ ＝ ₁ → (a : A) → F a ＝ ₁
  a₀-works p a = 𝟚-equality-cases (λ q → ap F (lemma p a q) ∙ p) id
\end{code}

As a corollary we can combine the main theorem with our proposition
that internal compact implies weak internal compact, to show that if
a type is compact according to the internal logic of a reflective
subuniverse, then it is compact externally. That is, compactness is
upwards absolute for reflective subuniverses.

\begin{code}
internal-compact-implies-compact
 : (A : 𝓤 ̇ )
 → (A-modal : is-modal A)
 → is-internal-compact∙ A
 → is-compact∙ A
internal-compact-implies-compact A A-modal c =
 weak-internal-compact-implies-compact
  _
  A-modal
  (internal-compact-implies-weak-internal-compact _ c)
\end{code}

The remaining theorems in this module all require a couple of extra
assumptions: the universe needs to be univalent, and the subuniverse
needs to be Σ-closed, making it an actual modality.

\begin{code}
module WithUnivalenceAndSigmaClosedness
 (ua : is-univalent 𝓤)
 (P-is-sigma-closed : subuniverse-is-sigma-closed P)
 where
\end{code}

We import some theorems about Σ-closed reflective subuniverses, and
recall proofs of the two ways that we will use univalence: function
extensionality and repleteness of the subuniverse.

\begin{code}
 module S =
  Modal.SigmaClosedReflectiveSubuniverse
   P P-is-reflective P-is-sigma-closed

 fe = univalence-gives-funext ua
 repleteness = univalence-implies-subuniverse-is-replete ua P
\end{code}

The next two lemmas get quite technical. In both cases the ideas are
simple, but we require constructing terms by by ○-induction or
recursion. This requires proving that certain types are ○-modal, which
requires some care with universe levels, as well as the application of
several lemmas using function extensionality and repleteness of P.

We first show that if A is weak internal compact, then so is ○ A.
\begin{code}
 ○-preserves-wi-compact
  : (A : 𝓤 ̇ )
  → is-weak-internal-compact∙ A
  → is-weak-internal-compact∙ (○ A)
 ○-preserves-wi-compact A c F = α₀ , α₀-works
  where
   F' : A → 𝟚
   F' = F ∘ η _

   compactness-instance
    : Σ a₀ ꞉ A ,
    (F' a₀ ＝ ₁ → (a : A) → η _ (lift _ (F' a)) ＝ η _ (lift _ ₁))
   compactness-instance = c F'

   α₀ = η _ (pr₁ compactness-instance)

   α₀-works
    : (p : F α₀ ＝ ₁)
    → (α : ○ A)
    → η _ (lift _ (F α)) ＝ η _ (lift _ ₁)
   α₀-works p =
    S.○-induction
     fe
     _ _
     (λ _ →
      id-types-of-modal-types-are-modal
       fe
       repleteness
       _ _
       _
       (○-is-modal _))
     (pr₂ compactness-instance p)
\end{code}

In the second technical lemma we strengthen the above result. We
derive the same conclusion as before, but we weaken the assumption by
putting it inside the modality.

\begin{code}
 ○-compact-implies-weak-internal-compact
  : (A : 𝓤 ̇ )
  → ○ (is-weak-internal-compact∙ A)
  → is-weak-internal-compact∙ (○ A)

 ○-compact-implies-weak-internal-compact A c F =
  demodify-wic-instance
   (○-rec
    _
    _
    modified-wic-is-modal
    (λ c' → modify-wic-instance (○-preserves-wi-compact A c' F))
    c)

  where
   modified-wic-instance : 𝓤 ̇
   modified-wic-instance =
    Σ α₀ ꞉ ○ A ,
    (lift 𝓤 (F α₀) ＝ lift 𝓤 ₁ →
     (α : ○ A) → η _ (lift 𝓤 (F α)) ＝ η _ (lift 𝓤 ₁))

   demodify-wic-instance
    : modified-wic-instance
    → Σ α₀ ꞉ ○ A ,
    (F α₀ ＝ ₁ → (α : ○ A) → η _ (lift 𝓤 (F α)) ＝ η _ (lift 𝓤 ₁))
   demodify-wic-instance (α₀ , f) = α₀ , (λ p α → f (ap (lift _) p) α)

   modify-wic-instance
    : Σ α₀ ꞉ ○ A ,
    (F α₀ ＝ ₁ → (α : ○ A) → η _ (lift 𝓤 (F α)) ＝ η _ (lift 𝓤 ₁))
    → modified-wic-instance
   modify-wic-instance (α₀ , f) =
    α₀ , (λ p α → f (equivs-are-lc _ lift-is-equiv p) α)

   modified-wic-is-modal : is-modal modified-wic-instance
   modified-wic-is-modal =
    P-is-sigma-closed
     _ _
     (○-is-modal A)
     (λ _ →
      products-of-modal-types-are-modal
       fe
       repleteness
       _
       _
       λ _ →
        products-of-modal-types-are-modal
         fe
         repleteness
         _ _
         (λ _ →
           id-types-of-modal-types-are-modal
           fe
           repleteness
           _ _ _
           (○-is-modal _)))
\end{code}

Finally, we can use the lemmas together with the main theorem to get a
result which is closer to the statement of prop-tychonoff. This says ○
"preserves compactness" in the sense that if ○ (A is compact), then
(○ A) is compact.

We note that the arguments in prop-tychonoff show that we can think of
the family of types Y : X → 𝓥 ̇  without loss of generality as a
constant family. Aside from that and the assumption here of
univalence, we can view the remainder of theorem prop-tychonoff as a
special case of the one below. To see this, note that when X is a
proposition the functor X → - is a modality, and so can derive
is-compact∙ (X → A) from X → is-compact∙ A.

\begin{code}
 modalities-preserve-compact
  : (A : 𝓤 ̇  )
  → ○ (is-compact∙ A)
  → is-compact∙ (○ A)
 modalities-preserve-compact A c =
  weak-internal-compact-implies-compact
   _
   (○-is-modal _)
   (○-compact-implies-weak-internal-compact A
    (○-rec
     _ _
     (○-is-modal _)
     (λ c' → η _ (compact-implies-weak-internal-compact _ c'))
     c))
\end{code}
