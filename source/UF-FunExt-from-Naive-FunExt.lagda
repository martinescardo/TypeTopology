Martin Escardo, 19th May 2018

Vladimir Voevodsky proved in Coq that naive function extensionality
(any two pointwise equal non-dependent functions are equal) implies
function extensionality (happly is an equivalence, for dependent
functions):

  https://github.com/vladimirias/Foundations/blob/master/Generalities/uu0.v

Mike Shulman (13th April 2018) translated the Coq code to English
prose for me:

"
We prove that Pi of a family of contractible types is contractible;
this is well-known to imply full dependent funext.

 This is funext-via-contractibility in the module UF-Yoneda.lagda

1. If each P(x) is contractible, then the projection pr1 : Sigma{x:X}
P(x) --> X is an equivalence.  This requires no funext.

 This is pr₁-equivalence from UF-Equiv

2. If (f : A -> B) is an equivalence, then so is postcomposition with
it (X -> A) -> (X -> B).  This requires only non-dependent funext.

 This is qinv-post in UF-Equiv-FunExt
 
3. Thus, postcomposition with pr1 is an equivalence (X -> Sigma{x:X}
P(x)) --> (X -> X).

 This is just an immediate consequence.
 
4. Therefore, the fiber of "postcomposition with pr1" over idmap : X
-> X is contractible.  (This is VV's *definition* of equivalence, but
all notions of equivalence are *logically* equivalent without any
funext, so it doesn't matter which we use.)

 This is just an immediate consequence.

5. The latter fiber is "the type of sections of pr1", so it is
equivalent to Pi(x:X) P(x).  Proving this requires full funext, but
without any funext we can prove that Pi(x:X) P(x) is a *retract* of
this fiber, and hence inherits contractibility from it.
"

Here I translate Mike's translation to Agda.

\begin{code}

open import UF-Base
open import UF-FunExt
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-Yoneda
open import UF-Subsingletons
open import UF-Subsingletons-Retracts

NFunExt-gives-FunExt : ∀ {U} {V} → NFunExt U (U ⊔ V) → NFunExt U U → FunExt U V
NFunExt-gives-FunExt {U} {V} nfe nfe' = funext-via-contractibility γ
 where
  γ : (X : U ̇) (A : X → V ̇) →
      ((x : X) → isSingleton (A x)) → isSingleton (Π A)
  γ X A φ = retract-of-singleton r (s , rs) iss
   where
    f : Σ A → X
    f = pr₁
    eqf : isEquiv f
    eqf = pr₁-equivalence X A φ
    g : (X → Σ A) → (X → X)
    g h = pr₁ ∘ h
    eqg : isEquiv g
    eqg = equiv-post nfe nfe' f eqf
    iss : isSingleton (Σ \(h : X → Σ A) →  pr₁ ∘ h ≡ id)
    iss = isEquiv-isVoevodskyEquiv g eqg id
    r : (Σ \(h : X → Σ A) →  pr₁ ∘ h ≡ id) → Π A
    r (h , p) x = transport A (happly p x) (pr₂ (h x))
    s : Π A → (Σ \(h : X → Σ A) →  pr₁ ∘ h ≡ id)
    s φ = (λ x → x , φ x) , refl
    rs : ∀ φ → r (s φ) ≡ φ
    rs φ = refl

NFunExt-gives-FunExt' : ∀ {U} → NFunExt U U → FunExt U U
NFunExt-gives-FunExt' fe = NFunExt-gives-FunExt fe fe

\end{code}
