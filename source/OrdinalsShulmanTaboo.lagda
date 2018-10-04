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
> to say that it is a subsingleton.  But True \in A, so this is to say
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
>> Any subsingleton is an ordinal in a unique way (with the empty order).
>>
>> Now suppose that X is an ordinal, and consider P:X->U subsingleton
>> valued.  Then the lexicographic order on the sum Sigma(x:X),P(x) is
>> nothing but a subset of X. While classically the subset will remain
>> extensional (for if we have x and y not equal, then either x<y or
>> y<x, and hence they will not have the same lower set),
>> constructively this seems very dubious.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt
open import UF-Subsingletons

module OrdinalsShulmanTaboo
       (fe : ∀ U V → funext U V)
       (pe : propext U₀)
       where

open import Ordinals fe
open import OrdinalOmega fe U₀ pe
open import OrdinalNotions
open import UF-Base
open import UF-Subsingletons-FunExt
open import UF-ExcludedMiddle

fe₀ : funext U₀ U₀
fe₀ = fe U₀ U₀

X : U₁ ̇
X = Σ \(p : ⟨ Ωₒ ⟩) → ¬(p ≡ ⊥)

\end{code}

We restrict the order of the ordinal Ωₒ of truth-values to X:

\begin{code}

_≺_ : X → X → U₁ ̇
(p , _) ≺ (q , _) = p ≺⟨ Ωₒ ⟩ q

shulmans-taboo : is-extensional _≺_ → EM U₀
shulmans-taboo e = DNE-EM fe₀ dne
 where
  i : is-prop X
  i x y = e x y f g
   where
    f : (z : X) → z ≺ x → z ≺ y
    f (p , φ) (a , _) = 𝟘-elim (φ a)
    g : (z : X) → z ≺ y → z ≺ x
    g (q , ψ) (b , _) = 𝟘-elim (ψ b)

  dne : (P : U₀ ̇) → is-prop P → ¬¬ P → P
  dne P j φ = Idtofun s φ
   where
    p q : X
    p = (¬¬ P , neg-is-prop fe₀) ,
        (λ r → Idtofun (ap pr₁ r) φ)
    q = (P , j) ,
        (λ r → φ (Idtofun (ap pr₁ r)))
    r : p ≡ q
    r = i p q
    s : ¬¬ P ≡ P
    s = ap (pr₁ ∘ pr₁) r

\end{code}

TODO: Use this to show that if the sum of any ordinal-indexed family
of ordinals is an ordinal under the lexicographic ordering, then
excluded middle holds, as explained in the message quoted
above. (Routine, tedious.)
