Martin Escardo, 26 January 2018.

Moved from the file TypeTopology.TotallySeparated 22 August 2024.

Definition of apartness relation and basic general facts.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Apartness.Definition where

open import MLTT.Spartan
open import UF.DiscreteAndSeparated hiding (tight)
open import UF.FunExt
open import UF.Lower-FunExt
open import UF.NotNotStablePropositions
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

is-prop-valued
 is-irreflexive
 is-symmetric
 is-strongly-cotransitive
 is-tight
 is-strong-apartness
  : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇

is-prop-valued           _♯_ = ∀ x y → is-prop (x ♯ y)
is-irreflexive           _♯_ = ∀ x → ¬ (x ♯ x)
is-symmetric             _♯_ = ∀ x y → x ♯ y → y ♯ x
is-strongly-cotransitive _♯_ = ∀ x y z → x ♯ y → (x ♯ z) + (y ♯ z)
is-tight                 _♯_ = ∀ x y → ¬ (x ♯ y) → x ＝ y
is-strong-apartness      _♯_ = is-prop-valued _♯_
                             × is-irreflexive _♯_
                             × is-symmetric _♯_
                             × is-strongly-cotransitive _♯_

Strong-Apartness : 𝓤 ̇ → (𝓥 : Universe) → 𝓥 ⁺ ⊔ 𝓤 ̇
Strong-Apartness X 𝓥 = Σ _♯_ ꞉ (X → X → 𝓥 ̇ ) , is-strong-apartness _♯_

\end{code}

Not-not equal elements are not apart, and hence, in the presence of
tightness, they are equal. It follows that tight apartness types are
sets.

\begin{code}

double-negation-of-equality-gives-negation-of-apartness
 : {X : 𝓤 ̇ } (x y : X) (_♯_ : X → X → 𝓥 ̇ )
 → is-irreflexive _♯_
 → ¬¬ (x ＝ y)
 → ¬ (x ♯ y)
double-negation-of-equality-gives-negation-of-apartness x y _♯_ i
 = contrapositive f
 where
  f : x ♯ y → ¬ (x ＝ y)
  f a refl = i y a

tight-types-are-¬¬-separated' : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
                              → is-irreflexive _♯_
                              → is-tight _♯_
                              → is-¬¬-separated X
tight-types-are-¬¬-separated' _♯_ i t = f
 where
  f : ∀ x y → ¬¬ (x ＝ y) → x ＝ y
  f x y φ = t x y (double-negation-of-equality-gives-negation-of-apartness
                    x y _♯_ i φ)

tight-types-are-sets' : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
                      → funext 𝓤 𝓤₀
                      → is-irreflexive _♯_
                      → is-tight _♯_
                      → is-set X
tight-types-are-sets' _♯_ fe i t =
 ¬¬-separated-types-are-sets fe (tight-types-are-¬¬-separated' _♯_ i t)

\end{code}

To define apartness we need to define (weak) cotransitivity, and for
this we need to assume the existence of propositional truncations.

\begin{code}

module Apartness (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 is-cotransitive is-apartness : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇

 is-cotransitive _♯_ = ∀ x y z → x ♯ y → x ♯ z ∨ y ♯ z
 is-apartness    _♯_ = is-prop-valued _♯_
                     × is-irreflexive _♯_
                     × is-symmetric _♯_
                     × is-cotransitive _♯_

 Apartness : 𝓤 ̇ → (𝓥 : Universe) → 𝓥 ⁺ ⊔ 𝓤 ̇
 Apartness X 𝓥 = Σ _♯_ ꞉ (X → X → 𝓥 ̇ ) , is-apartness _♯_

 cotransitive-if-strongly-cotransitive : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
                                       → is-strongly-cotransitive _♯_
                                       → is-cotransitive _♯_
 cotransitive-if-strongly-cotransitive _♯_ sc x y z a = ∣ sc x y z a ∣

 strong-apartness-is-apartness : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
                               → is-strong-apartness _♯_
                               → is-apartness _♯_
 strong-apartness-is-apartness _♯_ (p , i , s , c) =
  p , i , s , cotransitive-if-strongly-cotransitive _♯_ c

 Tight-Apartness : 𝓤 ̇  → (𝓥 : Universe) → 𝓥 ⁺ ⊔ 𝓤 ̇
 Tight-Apartness X 𝓥 = Σ _♯_ ꞉ (X → X → 𝓥 ̇ ) , is-apartness _♯_ × is-tight _♯_

 apartness-is-prop-valued : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
                          → is-apartness _♯_
                          → is-prop-valued _♯_
 apartness-is-prop-valued _♯_ (p , i , s , c) = p

 apartness-is-irreflexive : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
                          → is-apartness _♯_
                          → is-irreflexive _♯_
 apartness-is-irreflexive _♯_ (p , i , s , c) = i

 apartness-is-irreflexive' : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
                           → is-apartness _♯_
                           → (x y : X) → x ♯ y → x ≠ y
 apartness-is-irreflexive' _♯_ (p , i , s , c) x y a refl = i x a

 apartness-is-symmetric : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
                        → is-apartness _♯_
                        → is-symmetric _♯_
 apartness-is-symmetric _♯_ (p , i , s , c) = s

 apartness-is-cotransitive : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
                           → is-apartness _♯_
                           → is-cotransitive _♯_
 apartness-is-cotransitive _♯_ (p , i , s , c) = c

 strong-apartness-is-prop-valued : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
                                 → is-strong-apartness _♯_
                                 → is-prop-valued _♯_
 strong-apartness-is-prop-valued _♯_ (p , i , s , c) = p

 strong-apartness-is-irreflexive : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
                                 → is-strong-apartness _♯_
                                 → is-irreflexive _♯_
 strong-apartness-is-irreflexive _♯_ (p , i , s , c) = i

 strong-apartness-is-irreflexive' : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
                                  → is-strong-apartness _♯_
                                  → (x y : X) → x ♯ y → x ≠ y
 strong-apartness-is-irreflexive' _♯_ (p , i , s , c) x y a refl = i x a

 strong-apartness-is-symmetric : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
                               → is-strong-apartness _♯_
                               → is-symmetric _♯_
 strong-apartness-is-symmetric _♯_ (p , i , s , c) = s

 strong-apartness-is-cotransitive : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
                                  → is-strong-apartness _♯_
                                  → is-strongly-cotransitive _♯_
 strong-apartness-is-cotransitive _♯_ (p , i , s , c) = c

 not-equal-if-apart : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
                    → is-apartness _♯_
                    → {x y : X} → x ♯ y → x ≠ y
 not-equal-if-apart _♯_ a {x} {y} h refl = apartness-is-irreflexive _♯_ a x h

 not-not-equal-not-apart : {X : 𝓤 ̇ } (x y : X) (_♯_ : X → X → 𝓥 ̇ )
                         → is-apartness _♯_
                         → ¬¬ (x ＝ y)
                         → ¬ (x ♯ y)
 not-not-equal-not-apart x y _♯_ (_ , i , _ , _) =
  double-negation-of-equality-gives-negation-of-apartness x y _♯_ i

 tight-types-are-¬¬-separated : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
                              → is-apartness _♯_
                              → is-tight _♯_
                              → is-¬¬-separated X
 tight-types-are-¬¬-separated _♯_ (_ , i , _ , _) =
  tight-types-are-¬¬-separated' _♯_ i

 tight-types-are-sets : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
                      → funext 𝓤 𝓤₀
                      → is-apartness _♯_
                      → is-tight _♯_
                      → is-set X
 tight-types-are-sets _♯_ fe (_ , i , _ , _) = tight-types-are-sets' _♯_ fe i

 finner-than-tight-is-tight
  : {X : 𝓤 ̇ }
  → (_♯_  : X → X → 𝓥 ̇ )
  → (_♯'_ : X → X → 𝓥' ̇ )
  → ((x y : X) → x ♯ y → x ♯' y)
  → is-tight _♯_
  → is-tight _♯'_
 finner-than-tight-is-tight _♯_ _♯'_ ϕ t = II
  where
   I : ∀ x y → ¬ (x ♯' y) → ¬ (x ♯ y)
   I x y = contrapositive (ϕ x y)

   II : ∀ x y → ¬ (x ♯' y) → x ＝ y
   II x y = t x y ∘ I x y

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
    f (_♯_ , a , t) = tight-types-are-¬¬-separated _♯_ a t

 tight-types-are-sets'' : funext 𝓤 𝓤
                        → {X : 𝓤 ̇ }
                        → (∃ _♯_ ꞉ (X → X → 𝓤 ̇ ), is-apartness _♯_ × is-tight _♯_)
                        → is-set X
 tight-types-are-sets'' {𝓤} fe {X} = ∥∥-rec (being-set-is-prop fe) f
   where
    f : (Σ _♯_ ꞉ (X → X → 𝓤 ̇ ), is-apartness _♯_ × is-tight _♯_) → is-set X
    f (_♯_ , a , t) = tight-types-are-sets _♯_ (lower-funext 𝓤 𝓤 fe) a t

\end{code}

The following is the standard equivalence relation induced by an
apartness relation. The tightness axiom defined above says that this
equivalence relation is equality.

\begin{code}

 is-equiv-rel : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
 is-equiv-rel _≈_ = is-prop-valued _≈_
                  × reflexive _≈_
                  × symmetric _≈_
                  × transitive _≈_

 negation-of-apartness-is-equiv-rel : {X : 𝓤 ̇ }
                                    → funext 𝓤 𝓤₀
                                    → (_♯_ : X → X → 𝓤 ̇ )
                                    → is-apartness _♯_
                                    → is-equiv-rel (λ x y → ¬ (x ♯ y))
 negation-of-apartness-is-equiv-rel {𝓤} {X} fe _♯_ (♯p , ♯i , ♯s , ♯c)
  = p , ♯i , s , t
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
