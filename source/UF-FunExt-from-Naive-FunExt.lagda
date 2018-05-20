Martin Escardo, 19th May 2018

Vladimir Voevodsky proved in Coq that naive function extensionality
(any two pointwise equal non-dependent functions are equal) implies
function extensionality (happly is an equivalence, for dependent
functions):

  https://github.com/vladimirias/Foundations/blob/master/Generalities/uu0.v

Here is an Agda version.

\begin{code}

open import UF-Base
open import UF-FunExt
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-Yoneda
open import UF-Subsingletons
open import UF-Subsingletons-Retracts

NaiveFunExt-gives-FunExt : ∀ {U} {V} → NaiveFunExt U (U ⊔ V) → NaiveFunExt U U → FunExt U V
NaiveFunExt-gives-FunExt {U} {V} nfe nfe' = funext-via-contractibility γ
 where
  γ : (X : U ̇) (A : X → V ̇) → ((x : X) → isSingleton (A x)) → isSingleton (Π A)
  γ X A φ = retract-of-singleton r (s , rs) iss
   where
    f : Σ A → X
    f = pr₁
    eqf : isEquiv f
    eqf = pr₁-equivalence X A φ
    g : (X → Σ A) → (X → X)
    g h = f ∘ h
    eqg : isEquiv g
    eqg = equiv-post nfe nfe' f eqf
    iss : isSingleton (Σ \(h : X → Σ A) →  f ∘ h ≡ id)
    iss = isEquiv-isVoevodskyEquiv g eqg id
    r : (Σ \(h : X → Σ A) → f ∘ h ≡ id) → Π A
    r (h , p) x = transport A (happly p x) (pr₂ (h x))
    s : Π A → (Σ \(h : X → Σ A) →  f ∘ h ≡ id)
    s φ = (λ x → x , φ x) , refl
    rs : ∀ φ → r (s φ) ≡ φ
    rs φ = refl

NaiveFunExt-gives-FunExt' : ∀ {U} → NaiveFunExt U U → FunExt U U
NaiveFunExt-gives-FunExt' fe = NaiveFunExt-gives-FunExt fe fe

\end{code}
