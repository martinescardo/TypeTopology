Martin Escardo, 4th October 2018

We worked with ordinals with top in order to be able to construct the
sum of an ordinal-indexed family of ordinals, with the lexicographic
order. Here we justify that some such restriction is needed.

This implements the following email communication:

On 22/07/18 06:17, Michael Shulman wrote:
> Ah, I see.  In fact I think "every subset of an ordinal is an
> ordinal" is equivalent to LEM as follows: consider the ordinal Prop,
> with (P < Q) = (~P /\ Q) as before, and consider the subset A of all
> P such that ~~P is true.  Then False \notin A, so given any Q \in A,
> we cannot have any P \in A with P < Q.  Thus the hypothesis of
> extensionality for A is vacuous, so to say that A is extensional is
> to say that it is a prop.  But True \in A, so this is to say
> that ~~P -> (P = True), i.e. DNE holds, hence LEM.
>
> On Fri, Jul 20, 2018 at 3:42 PM, Martin Escardo <m.escardo@cs.bham.ac.uk> wrote:
>> On 20/07/18 23:31, Michael Shulman wrote:
>>> Do you know of a model in which preservation of extensionality
>>> definitely fails (or a proof of a taboo from it)?
>>
>> No. But here is an idea that made me to give up trying to prove
>> extensionality of the lexicographic order on Sigma.
>>
>> Any prop is an ordinal in a unique way (with the empty order).
>>
>> Now suppose that X is an ordinal, and consider P:X->U prop
>> valued.  Then the lexicographic order on the sum Sigma (x:X),P (x) is
>> nothing but a subset of X. While classically the subset will remain
>> extensional (for if we have x and y not equal, then either x<y or
>> y<x, and hence they will not have the same lower set),
>> constructively this seems very dubious.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

open import UF.FunExt
open import UF.Subsingletons

module Ordinals.ShulmanTaboo
       (fe : FunExt)
       (pe : propext 𝓤₀)
       where

open import Ordinals.Type
open import Ordinals.OrdinalOfTruthValues fe 𝓤₀ pe
open import Ordinals.Notions
open import Ordinals.Underlying

open import UF.Base
open import UF.ExcludedMiddle
open import UF.SubtypeClassifier
open import UF.Subsingletons-FunExt

fe₀ : funext 𝓤₀ 𝓤₀
fe₀ = fe 𝓤₀ 𝓤₀

\end{code}

The type of truth values is Ω, following topos-theoretic notation, and
the ordinal of truth values, ordered by p < q iff p ＝ ⊥ and q ＝ ⊤, is
denoted by Ωₒ (the subscript is the letter "o", for "ordinal", and not
the number zero). This is parametrized by an arbitrary universe, which
in this module is instantiated to 𝓤₀.

\begin{code}

X : 𝓤₁ ̇
X = Σ p ꞉ ⟨ Ωₒ ⟩ , ¬ (p ＝ ⊥)

recall-that : is-extensional (underlying-order Ωₒ)
recall-that = Extensionality Ωₒ

\end{code}

However, the extensionality of the restriction of the underlying order
of the ordinal Ωₒ of truth values to X is a constructive taboo (it
implies excluded middle), as shown by Shulman in the message quoted
above:

\begin{code}

_≺_ : X → X → 𝓤₁ ̇
(p , _) ≺ (q , _) = p ≺⟨ Ωₒ ⟩ q

shulmans-taboo : is-extensional _≺_ → EM 𝓤₀
shulmans-taboo e = DNE-gives-EM fe₀ δ
 where
  i : is-prop X
  i x y = e x y f g
   where
    f : (z : X) → z ≺ x → z ≺ y
    f (p , φ) (a , _) = 𝟘-elim (φ a)

    g : (z : X) → z ≺ y → z ≺ x
    g (q , ψ) (b , _) = 𝟘-elim (ψ b)

  δ : (P : 𝓤₀ ̇ ) → is-prop P → ¬¬ P → P
  δ P j φ = Idtofun s φ
   where
    p q : X
    p = (¬¬ P , negations-are-props fe₀) ,
        (λ r → Idtofun (ap pr₁ r) φ)
    q = (P , j) ,
        (λ r → φ (Idtofun (ap pr₁ r)))

    r : p ＝ q
    r = i p q

    s : ¬¬ P ＝ P
    s = ap (pr₁ ∘ pr₁) r

\end{code}

TODO: Use this to show that if the sum of any ordinal-indexed family
of ordinals is an ordinal under the lexicographic ordering, then
excluded middle holds, as explained in the message quoted
above. (Routine, tedious.)
