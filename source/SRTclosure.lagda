Martin Escardo, 3 February 2021.

⋆ Symmetric closure of a relation.

⋆ Iteration of a relation.

⋆ Reflexive-transitive closure of a relation.

⋆ Symmetric-reflexive-transitive closure of a relation.

⋆ propositional, symmetric-reflexive-transitive closure of a relation.

⋆ A special kind of Church-Rosser property.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT hiding (_^_)

module SRTclosure where

open import UF-Subsingletons
open import UF-PropTrunc

open import NaturalsAddition renaming (_+_ to right-addition)

\end{code}

We work with addition defined by induction on the left argument:

\begin{code}

_∔_ : ℕ → ℕ → ℕ
m ∔ n = right-addition n m

_⊑_ : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → (X → X → 𝓦 ̇ ) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
R ⊑ S = ∀ x y → R x y → S x y

is-prop-valued-rel is-equiv-rel : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
is-prop-valued-rel A = ∀ x y → is-prop (A x y)
is-equiv-rel       A = is-prop-valued-rel A
                     × reflexive A
                     × symmetric A
                     × transitive A
\end{code}

The symmetric closure of a relation A:

\begin{code}

module _ {𝓤 : Universe}
         {X : 𝓤 ̇ }
         (A : X → X → 𝓥 ̇ )
       where

 s-closure : X → X → 𝓥 ̇
 s-closure x y = A x y + A y x

 s-symmetric : symmetric s-closure
 s-symmetric x y (inl a) = inr a
 s-symmetric x y (inr a) = inl a

 s-extension : A ⊑ s-closure
 s-extension x y = inl

 s-induction : (R : X → X → 𝓦 ̇ )
             → symmetric R
             → A ⊑ R
             → s-closure ⊑ R
 s-induction R s A-included-in-R x y (inl a) = A-included-in-R x y a
 s-induction R s A-included-in-R x y (inr a) = s y x (A-included-in-R y x a)

\end{code}

To define the reflexive-transitive closure, we first consider the
iteration of a relation B:

\begin{code}

module _ {𝓤 : Universe}
         {X : 𝓤 ̇ }
         (B : X → X → 𝓤 ̇ )
       where

 iteration : ℕ → X → X → 𝓤 ̇
 iteration 0        x y = x ≡ y
 iteration (succ n) x y = Σ z ꞉ X , B x z × iteration n z y

 iteration-reflexive : (x : X) → iteration 0 x x
 iteration-reflexive x = refl

 iteration-transitive' : (n : ℕ) (x y z : X) → iteration n x y → B y z → iteration (succ n) x z
 iteration-transitive' 0        x x z refl        b  = z , b , refl
 iteration-transitive' (succ n) x y z (t , b , c) b' = t , b , iteration-transitive' n t y z c b'

 iteration-transitive'-converse : (n : ℕ) (x z : X)
                                → iteration (succ n) x z
                                → Σ y ꞉ X , iteration n x y × B y z
 iteration-transitive'-converse 0        x z (z , b , refl)       = x , refl , b
 iteration-transitive'-converse (succ n) x z (y , b , t , b' , i) = γ
  where
   IH : Σ u ꞉ X , iteration n y u × B u z
   IH = iteration-transitive'-converse n y z (t , b' , i)

   u : X
   u = pr₁ IH

   i' : iteration n y u
   i' = pr₁ (pr₂ IH)

   b'' : B u z
   b'' = pr₂ (pr₂ IH)

   γ : Σ u ꞉ X , iteration (succ n) x u × B u z
   γ = u , (y , b , i') , b''

 iteration-symmetric : symmetric B → (m : ℕ) → symmetric (iteration m)
 iteration-symmetric sym 0        x x refl        = refl
 iteration-symmetric sym (succ m) x y (z , b , c) = γ
   where
    c' : iteration m y z
    c' = iteration-symmetric sym m z y c

    γ : iteration (succ m) y x
    γ = iteration-transitive' m y z x c' (sym x z b)

 iteration-transitive : (m n : ℕ) (x y z : X) → iteration m x y → iteration n y z → iteration (m ∔ n) x z
 iteration-transitive 0        n x x z refl        c' = c'
 iteration-transitive (succ m) n x y z (t , b , c) c' = t , b , iteration-transitive m n t y z c c'

\end{code}

This is regarding the above anonymous module but needs to be outside it:

\begin{code}

private
 _^_ : {X : 𝓤 ̇ } → (X → X → 𝓤 ̇ ) → ℕ → (X → X → 𝓤 ̇ )
 _^_ = iteration

\end{code}

The reflexive-transitive closure of a relation B:

\begin{code}

module _ {𝓤 : Universe}
         {X : 𝓤 ̇ }
         (B : X → X → 𝓤 ̇ )
       where

 rt-closure : X → X → 𝓤 ̇
 rt-closure x y = Σ n ꞉ ℕ , (B ^ n) x y

 rt-reflexive : reflexive rt-closure
 rt-reflexive x = 0 , refl

 rt-symmetric : symmetric B → symmetric rt-closure
 rt-symmetric s x y (m , c) = m , iteration-symmetric B s m x y c

 rt-transitive : transitive rt-closure
 rt-transitive x y z (m , c) (m' , c') = (m ∔ m') , iteration-transitive B m m' x y z c c'

 rt-extension : B ⊑ rt-closure
 rt-extension x y b = 1 , y , b , refl

 rt-induction : (R : X → X → 𝓥 ̇ )
              → reflexive R
              → transitive R
              → B ⊑ R
              → rt-closure ⊑ R
 rt-induction R r t B-included-in-R = γ
  where
   γ : (x y : X) → rt-closure x y → R x y
   γ x x (0      , refl)      = r x
   γ x y (succ n , z , b , c) = t x z y (B-included-in-R x z b) (γ z y (n , c))

\end{code}

By combining the symmetric closure with the reflective-transitive
closure, we get the symmetric-reflexive-transitive-closure:

\begin{code}

module _ {𝓤 : Universe}
         {X : 𝓤 ̇ }
         (A : X → X → 𝓤 ̇ )
       where

 srt-closure : X → X → 𝓤 ̇
 srt-closure = rt-closure (s-closure A)

 srt-symmetric : symmetric srt-closure
 srt-symmetric = rt-symmetric (s-closure A) (s-symmetric A)

 srt-reflexive : reflexive srt-closure
 srt-reflexive = rt-reflexive (s-closure A)

 srt-transitive : transitive srt-closure
 srt-transitive = rt-transitive (s-closure A)

 srt-extension'' : s-closure A ⊑ srt-closure
 srt-extension'' = rt-extension (s-closure A)

 srt-extension' : A ⊑ s-closure A
 srt-extension' = s-extension A

 srt-extension : A ⊑ srt-closure
 srt-extension x y = srt-extension'' x y ∘ srt-extension' x y

 rt-gives-srt : (x y : X) → rt-closure A x y → srt-closure x y
 rt-gives-srt x y (m , i) = g m x y i
  where
   f : (n : ℕ) (x y : X) → iteration A n x y → iteration (s-closure A) n x y
   f 0        x x refl        = refl
   f (succ n) x y (z , e , i) = z , inl e , (f n z y i)

   g : (n : ℕ) (x y : X) → iteration A n x y → srt-closure x y
   g 0        x x refl        = srt-reflexive x
   g (succ n) x y (z , e , i) = succ n , z , inl e , f n z y i

 srt-induction : (R : X → X → 𝓥 ̇ )
               → symmetric R
               → reflexive R
               → transitive R
               → A ⊑ R
               → srt-closure ⊑ R
 srt-induction R s r t A-included-in-R x y = γ
  where
   δ : s-closure A ⊑ R
   δ = s-induction A R s A-included-in-R

   γ : srt-closure x y → R x y
   γ = rt-induction (s-closure A) R r t δ x y


\end{code}

The proposition-valued, symmetric-reflexive-transitive closure of a
relation A:

\begin{code}

module psrt
        (pt : propositional-truncations-exist)
        {𝓤 : Universe}
        {X : 𝓤 ̇ }
        (A : X → X → 𝓤 ̇ )
       where

 open PropositionalTruncation pt

 psrt-closure : X → X → 𝓤 ̇
 psrt-closure x y = ∥ srt-closure A x y ∥

 psrt-is-prop-valued : (x y : X) → is-prop (psrt-closure x y)
 psrt-is-prop-valued x y = ∥∥-is-prop

 psrt-symmetric : symmetric psrt-closure
 psrt-symmetric x y = ∥∥-functor (srt-symmetric A x y)

 psrt-reflexive : reflexive psrt-closure
 psrt-reflexive x = ∣ srt-reflexive A x ∣

 psrt-transitive : transitive psrt-closure
 psrt-transitive x y z = ∥∥-functor₂ (srt-transitive A x y z)

 psrt-extension : A ⊑ psrt-closure
 psrt-extension x y a = ∥∥-functor (srt-extension A x y) ∣ a ∣

 psrt-induction : (R : X → X → 𝓥 ̇ )
                → ((x y : X) → is-prop (R x y))
                → reflexive R
                → symmetric R
                → transitive R
                → A ⊑ R
                → psrt-closure ⊑ R
 psrt-induction R p r s t A-included-in-R x y =
  ∥∥-rec (p x y) (srt-induction A R s r t A-included-in-R x y)

 psrt-is-equiv-rel : is-equiv-rel psrt-closure
 psrt-is-equiv-rel = psrt-is-prop-valued ,
                     psrt-reflexive ,
                     psrt-symmetric ,
                     psrt-transitive
\end{code}

Any proposition-valued relation that is logically equivalent to an
equivalence relation is itself an equivalence relation. Unfortunately,
we cannot use univalence to perform this transport as the types live
in different universes.

\begin{code}

is-equiv-rel-transport : {X : 𝓤 ̇ }
                         (A : X → X → 𝓥 ̇ )
                         (B : X → X → 𝓦 ̇ )
                       → is-prop-valued-rel B
                       → ((x y : X) → A x y ⇔ B x y)
                       → is-equiv-rel A
                       → is-equiv-rel B
is-equiv-rel-transport {X} A B p' e (p , r , s , t) = (p' , r' , s' , t')
 where
  r' : reflexive B
  r' x = lr-implication (e x x) (r x)

  s' : symmetric B
  s' x y b = lr-implication (e y x) (s x y (rl-implication (e x y) b))

  t' : transitive B
  t' x y z b b' = lr-implication (e x z)
                    (t x y z (rl-implication (e x y) b)
                             (rl-implication (e y z) b'))
\end{code}

We consider one special kind of Church-Rosser property motivated by our applications of this module for other purposes.

\begin{code}

module Church-Rosser-consequences
         {𝓤 𝓥 : Universe}
         {X : 𝓤 ̇ }
         (_▷_ : X → X → 𝓤 ̇ )
       where

  infix 1 _◁▷_
  infix 1 _◁▷[_]_
  infix 1 _▷⋆_
  infix 1 _▷[_]_
  infix 1 _∿_
  _◁▷_ : X → X → 𝓤 ̇
  _◁▷_ = s-closure _▷_

  _◁▷[_]_ : X → ℕ → X → 𝓤 ̇
  x ◁▷[ n ] y = iteration _◁▷_ n x y

  _∿_ : X → X → 𝓤 ̇
  _∿_ = srt-closure _▷_

  _▷⋆_ : X → X → 𝓤 ̇
  _▷⋆_ = rt-closure _▷_

  _▷[_]_ : X → ℕ → X → 𝓤 ̇
  x ▷[ n ] y = iteration _▷_ n x y

  to-∿ : (x y : X)
       → (Σ z ꞉ X , (x ▷⋆ z) × (y ▷⋆ z))
       → x ∿ y
  to-∿ x y (z , r , s) = srt-transitive _▷_ x z y
                          (rt-gives-srt _▷_ x z r)
                          (srt-symmetric _▷_ y z (rt-gives-srt _▷_ y z s))

  module _ (Church-Rosser : (x y₀ y₁ : X)
                          → x ▷ y₀
                          → x ▷ y₁
                          → (y₀ ≡ y₁) + (Σ y ꞉ X , (y₀ ▷ y) × (y₁ ▷ y)))
         where

   Church-Rosser⋆ : (x y₀ y₁ : X)
                  → x ▷⋆ y₀
                  → x ▷  y₁
                  → Σ y ꞉ X , (y₀ ▷⋆ y) × (y₁ ▷⋆ y)
   Church-Rosser⋆ x y₀ y₁ (m , i) b = f m x y₀ y₁ i b
    where
     f : (m : ℕ) (x y₀ y₁ : X)
       → x ▷[ m ] y₀
       → x ▷  y₁
       → Σ y ꞉ X , (y₀ ▷⋆ y) × (y₁ ▷⋆ y)
     f 0        x x  y₁ refl        e = y₁ , rt-extension _▷_ x y₁ e , rt-reflexive _▷_ y₁
     f (succ m) x y₀ y₁ (t , d , i) e = γ c
      where
       c : (y₁ ≡ t) + (Σ y ꞉ X , (y₁ ▷ y) × (t ▷ y))
       c = Church-Rosser x y₁ t e d

       γ : type-of c → Σ u ꞉ X , (y₀ ▷⋆ u) × (y₁ ▷⋆ u)
       γ (inl refl) = y₀ , rt-reflexive _▷_ y₀ , m , i
       γ (inr (y , a , b)) = δ IH
        where
         IH : Σ u ꞉ X , (y₀ ▷⋆ u) × (y ▷⋆ u)
         IH = f m t y₀ y i b

         δ : type-of IH → Σ u ꞉ X , (y₀ ▷⋆ u) × (y₁ ▷⋆ u)
         δ (u , b , n , j) = u , b , succ n , y , a , j

   from-∿ : (x y : X) → x ∿ y → Σ z ꞉ X , (x ▷⋆ z) × (y ▷⋆ z)
   from-∿ x y (m , e) = f m x y e
    where
     f : (m : ℕ) (x y : X) → x ◁▷[ m ] y → Σ z ꞉ X , (x ▷⋆ z) × (y ▷⋆ z)
     f 0        x x refl        = x , rt-reflexive _▷_ x , rt-reflexive _▷_ x
     f (succ m) x y (z , d , i) = γ IH d
      where
       IH : Σ t ꞉ X , (z ▷⋆ t) × (y ▷⋆ t)
       IH = f m z y i

       γ : type-of IH → x ◁▷ z → Σ u ꞉ X , (x ▷⋆ u) × (y ▷⋆ u)
       γ (t , (n , i) , a) (inl c) = t , (succ n , z , c , i) , a
       γ (t , (n , i) , a) (inr c) = δ σ
        where
         σ : Σ u ꞉ X , (t ▷⋆ u) × (x ▷⋆ u)
         σ = Church-Rosser⋆ z t x (n , i) c

         δ : type-of σ → Σ u ꞉ X , (x ▷⋆ u) × (y ▷⋆ u)
         δ (u , d , e) = u , e , rt-transitive _▷_ y t u a d

\end{code}
