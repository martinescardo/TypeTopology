# Search over uniformly continuous decidable predicates on infinite collections of types. (Part II)

Todd Waugh Ambridge, 1st February 2022

## Table of Contents:
 1. [Overview](#overview)
 1. [A closeness function for Π-types](#closeness)
 1. [Tychonoff theorem - first attempt](#tychonoff1)
 1. [Agreeable searchers](#agreeable)
 1. [Tychonoff theorem - second attempt](#tychonoff2)
 1. [Corollaries](#corollaries)

## Overview <a name="overview"></a>

In my [previous blog post](InfiniteSearch1.html), I layed the groundwork necessary to
safely formalise the Tychonoff theorem in constructive type theory.

I re-introduced the notion of searchable types ─ types `X` that exhibit a selection
function that, given any predicate, return an element of `X` satisfying the predicate
if at least one such element exists. I also introduced the notion of closeness
functions; our version of metrics that allow us to define uniformly continuous
decidable predicates. A type is continuously searchable if we can exhibit a selection
function that works on all uniformly continuous predicates.

I then proved that sequence types of discrete, continuously searchable types
— for example, the Cantor type `ℕ → 𝟚` — are continuously searchable. 
We now turn our attention to generalising this proof, by removing
the requirement of discreteness, in order to formalise the Tychonoff
theorem for continuously searchable types. This will allow us to prove,
for example, that the type of Cantor sequences `ℕ → (ℕ → 𝟚)` is
continuously searchable.

Another version of the Tychonoff theorem for searchable types
has been [previously formalised](CountableTychonoff.html)
by Martín Escardó with Agda’s termination checker turned off;
the addition of closeness functions allows the proof to terminate, but adds extra
steps to it as we must prove that everything is continuous.

```agda
{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT hiding (decidable)
open import Two-Properties hiding (zero-is-not-one)
open import NaturalsOrder

module InfiniteSearch2 (fe : {𝓤 𝓥 : Universe} → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {f g : Π Y}
                           → f ∼ g → f ≡ g) where

open import InfiniteSearch1 fe public
  hiding ( _::_ ; head ; tail ; head-tail-eta
         ; build-up
         ; 𝟚-is-c-searchable
         ; tail-predicate ; tail-predicate-reduce-mod
         ; head-predicate)
```
## A closeness function for `Π`-types <a name="closeness"></a>

In topology, the Tychonoff theorem states that arbitrary products of compact spaces
are themselves compact. As searchable types coincide with the concept of compactness,
and infinite products are constructed using the `Π`-type, we restate the Tychonoff theorem
using our two key notions of continuous searchability and closeness functions:

***Theorem (Tychonoff).*** Given a family of types indexed by the natural numbers `T : ℕ → 𝓤`,
such that every `(T n) : 𝓤` is continuously searchable and is equipped with a closeness
function of type `T n × T n → ℕ∞`, the type `Π T : 𝓤` is continuously searchable.

Of course, in order to prove `Π T` can be continuously searchable, we must first
provide a closeness function for `Π`-types.

An infinite sequence of types, each with a closeness function, is defined
as follows.

```agda
sequence-of-clofun-types : (𝓤 : Universe) → 𝓤 ⁺ ̇ 
sequence-of-clofun-types 𝓤
 = Σ T ꞉ (ℕ → 𝓤 ̇ ) , Π n ꞉ ℕ , (T n × T n → ℕ∞)
```

We generalise the composition, head and tail operations to infinite sequence of types.

```agda
_::_ : {T : ℕ → 𝓤 ̇ } → T 0 → Π (T ∘ succ) → Π T
(x :: xs) 0 = x
(x :: xs) (succ n) = xs n

head : {T : ℕ → 𝓤 ̇ } → Π T → T 0
head α = α 0

tail : {T : ℕ → 𝓤 ̇ } → Π T → Π (T ∘ succ)
tail α = α ∘ succ

head-tail-eta : {T : ℕ → 𝓤 ̇ } → (α : Π T) → α ≡ head α :: tail α
head-tail-eta α = fe γ where
  γ : α ∼ (head α :: tail α)
  γ 0 = refl
  γ (succ n) = refl
```

We want to determine the closeness `c (α , β) : ℕ∞` of two infinite sequences `α,β : Π T`.

It is straightforward to define this where each type `(T n) : 𝓤` is discrete
(i.e. each closeness function `cₙ : T n × T n → ℕ∞` is the discrete closeness function).

    c (α , β) n ≡ ₁,    if x ≡⟦ n ⟧ y,
                  ₀,    otherwise.

This is the "discrete-sequence" closeness function defined in the previous blog post.

But how can we determine `c(α , β) : ℕ∞` when nothing is assumed about each `cₙ`, apart
from that they satisfy the four properties of closeness functions?

First, note that we can compute `cₙ(α n , β n) : ℕ∞` for every `n : ℕ`.
The following illustrates some potential values of a prefix of these
closeness functions.

For example, the asterisk `* : 𝟚` is defined `* ≔ c₂ (α  2 , β 2) 3`.
Of course, `* ≡ ₀`, because the previous value in the sequence is `₀`, and
every `ℕ∞` is decreasing.

        0  1  2  3  4  5  ⋯
    c₀  ₁  ₁  ₁  ₁  ₁  ₀  ⋯
    c₁  ₁  ₁  ₁  ₁  ₁  ₁  ⋯
    c₂  ₁  ₁  ₀  *  ₀  ₀  ⋯
    c₃  ₀  ₀  ₀  ₀  ₀  ₀  ⋯
    ⋯   ⋯  ⋯  ⋯  ⋯  ⋯  ⋯

This 'square' of binary values is infinite in both directions; and we in
fact use the minimum values of this square's diagonals to determine the
value `c (α , β) : ℕ∞`.

Using this illustration, `c (α , β) 0 ≡ ₁` as it is the single element of
the first diagonal. `c (α , β) 1` and `c (α , β) 2` are also `₁` because the
second and third diagonals only feature `₁`s. However, `c (α , β) 3` is
`₀`, because the fourth diagonal features a `₀` ─ we take the minimum value
of each diagonal. We know that `c (α , β) n ≡ ₀` for all `n > 3`, because
`c₃ (α 3 , β 3)` will appear in every following diagonal, always contributing
a `₀`. This means that our determined closeness value is decreasing.

Therefore, we can express the closeness value as follows.

    c (α , β) 0
     ≡       c₀ (α 0 , β 0) 0
    c (α , β) 1
     ≡ min𝟚 (c₀ (α 0 , β 0) 1)       (c₁ (α 1 , β 1) 0)
    c (α , β) 2
     ≡ min𝟚 (c₀ (α 0 , β 0) 2) (min𝟚 (c₁ (α 1 , β 1) 1) (c₂ (α 2 , β 2) 0))
    ⋯

This can be expressed recursively:

    c (α , β) 0
     ≡ c₀ (α 0 , β 0) 0
    c (α , β) (succ n)
     ≡ min𝟚 (c₀ (α 0 , β 0) (succ n)) (c  (tail α , tail β) n)

```agda
Π-clofun' : ((T , cs) : sequence-of-clofun-types 𝓤) → Π T × Π T → (ℕ → 𝟚)
Π-clofun' (T , cs) (A , B) 0 = pr₁ (cs 0 (A 0 , B 0)) 0
Π-clofun' (T , cs) (A , B) (succ n)
 = min𝟚 (pr₁ (cs 0 (A 0 , B 0)) (succ n))
        (Π-clofun' (T ∘ succ , cs ∘ succ) (tail A , tail B) n)
```

We prove this is decreasing by induction.

(1) In the base case, we wish to show that,

        min𝟚 (c₀ (α 0 , β 0) 1) (c  (tail α , tail β) 0) ≡ ₁  
        ⇒  c₀ (α 0 , β 0) 0 ≡ ₁.

    Assume we have

        r : min𝟚 (c₀ (α 0 , β 0) 1) (c  (tail α , tail β) 0) ≡ ₁.

    From the fact c₀ is decreasing, we construct,

        f : c₀ (α 0 , β 0) 1 ≡ ₁ ⇒ c₀ (α 0 , β 0) 0 ≡ ₁.

    We use the following lemma,

        Lemma[min𝟚ab≡₁→a≡₁] : (a b : 𝟚) → min𝟚 a b ≡ ₁ → a ≡ ₁,

    where `a ≔ c₀ (α 0 , β 0) 1`,
      and `b ≔ c  (tail α , tail β) 0`.
           
    By applying this lemma to `r : min𝟚 a b ≡ ₁`, we
    construct `s : c₀ (α 0 , β 0) 1 ≡ ₁`.

    We apply `f` to `s` to complete the proof.

(2) In the inductive case we wish to show that,

        min𝟚 (c₀ (α 0 , β 0) (succ (succ n)) (c (tail α , tail β) (succ n)) ≡ ₁
        ⇒ min𝟚 (c₀ (α 0 , β 0) (succ n)) (c  (tail α , tail β) n)  ≡ ₁.

    From the fact `c₀` is decreasing, we construct,

        f : c₀ (α 0 , β 0) (succ (succ n)) ≡ ₁ ⇒ c₀ (α 0 , β 0) (succ n) ≡ ₁.

    By the inductive hypothesis, we construct,
    
        g : c (tail α , tail β) (succ n) ⇒ c (tail α , tail β) n.

    Assume we have

        r : min𝟚 (c₀ (α 0 , β 0) (succ (succ n)) (c (tail α , tail β) (succ n)) ≡ ₁

    We use the following lemmas,

        Lemma[min𝟚ab≡₁→a≡₁] : (a b : 𝟚) → min𝟚 a b ≡ ₁ → a ≡ ₁,
        Lemma[min𝟚ab≡₁→b≡₁] : (a b : 𝟚) → min𝟚 a b ≡ ₁ → b ≡ ₁.

    By applying these to `r`, we construct,
        `s : c₀ (α 0 , β 0) (succ (succ n)) ≡ ₁`
    and `t : c (tail α , tail β) (succ n)   ≡ ₁`.

    We apply `f` to `s` and `g` to `t` to construct,
        `u : c₀ (α 0 , β 0) (succ n) ≡ ₁`
    and `v : c (tail α , tail β) n   ≡ ₁`.

    We use the following lemma,

        Lemma[a≡₁→b≡₁→min𝟚ab≡₁] : (a b : 𝟚) → a ≡ ₁ → b ≡ ₁ → min𝟚 a b ≡ ₁.

    where `a ≔ c₀ (α 0 , β 0) (succ n)`,
      and `b ≔ c (tail α , tail β) n`.

    By applying this lemma to `u` and `v`, we complete the proof.  

```agda
Π-clofun'-dec : ((T , cs) : sequence-of-clofun-types 𝓤)
              → ((A , B) : Π T × Π T)
              → decreasing-binary-seq (Π-clofun' (T , cs) (A , B))
Π-clofun'-dec (T , cs) (A , B) 0        r =
 pr₂ (cs 0 (A 0 , B 0)) 0 (Lemma[min𝟚ab≡₁→a≡₁] r)
Π-clofun'-dec (T , cs) (A , B) (succ n) r
 = Lemma[a≡₁→b≡₁→min𝟚ab≡₁]
     (pr₂ (cs 0 (A 0 , B 0)) (succ n) (Lemma[min𝟚ab≡₁→a≡₁] r))
     (Π-clofun'-dec (T ∘ succ , cs ∘ succ) (A ∘ succ , B ∘ succ) n
       (Lemma[min𝟚ab≡₁→b≡₁] {pr₁ (cs 0 (A 0 , B 0)) (succ (succ n))} r))

Π-clofun : ((T , cs) : sequence-of-clofun-types 𝓤) → Π T × Π T → ℕ∞
Π-clofun (T , cs) (A , B) = Π-clofun'     (T , cs) (A , B)
                          , Π-clofun'-dec (T , cs) (A , B)
```

When every `cₙ` used is the discrete closeness function, the value of `Π-clofun`
is equivalent to that of `discrete-seq-clofun` defined in the previous blog post.
We leave this as an exercise for the reader.

Furthermore, we can show that, if every underlying `cₙ` satisfies the four properties
of a closeness function, then so does `Π-clofun`. The details of this are in the
following hidden module.

```agda
module hidden-module where

 Π-clofun'-eic : ((T , cs) : sequence-of-clofun-types 𝓤)
               → ((n : ℕ) (α : T n) → cs n (α , α) ≡ ∞)
               → (A : Π T) → Π-clofun (T , cs) (A , A) ≡ ∞
 Π-clofun'-eic (T , cs) eics A
  = ℕ∞-equals (γ (T , cs) eics A)
  where
    γ : ((T , cs) : sequence-of-clofun-types 𝓤)
      → ((n : ℕ) (α : T n) → cs n (α , α) ≡ ∞)
      → (A : Π T) → Π-clofun' (T , cs) (A , A) ∼ (λ _ → ₁)
    γ (T , cs) eics A 0 = ap (λ - → pr₁ - 0) (eics 0 (A 0))
    γ (T , cs) eics A (succ i)
     = Lemma[a≡₁→b≡₁→min𝟚ab≡₁]
         (ap (λ - → pr₁ - (succ i)) (eics 0 (A 0)))
         (γ (T ∘ succ , cs ∘ succ) (eics ∘ succ) (A ∘ succ) i)

 Π-clofun'-all : ((T , cs) : sequence-of-clofun-types 𝓤)
               → ((A , B) : Π T × Π T)
               → Π-clofun (T , cs) (A , B) ≡ ∞
               → (n : ℕ) → cs n (A n , B n) ≡ ∞
 Π-clofun'-all (T , cs) (A , B) cAB≡∞ n
  = ℕ∞-equals (γ (T , cs) (A , B)
      (λ i → ap (λ - → pr₁ - i) cAB≡∞) n)
  where
   γ : ((T , cs) : sequence-of-clofun-types 𝓤)
     → ((A , B) : Π T × Π T)
     → Π-clofun' (T , cs) (A , B) ∼ (pr₁ ∞)
     → (n : ℕ) → pr₁ (cs n (A n , B n)) ∼ pr₁ ∞
   γ (T , cs) (A , B) cAB∼∞ 0    0
    = cAB∼∞ 0
   γ (T , cs) (A , B) cAB∼∞ 0    (succ i)
    = Lemma[min𝟚ab≡₁→a≡₁] (cAB∼∞ (succ i))
   γ (T , cs) (A , B) cAB∼∞ (succ n)
    = γ (T ∘ succ , cs ∘ succ) (A ∘ succ , B ∘ succ)
        (λ i → Lemma[min𝟚ab≡₁→b≡₁] (cAB∼∞ (succ i)))
        n

 Π-clofun'-ice : ((T , cs) : sequence-of-clofun-types 𝓤)
               → ((n : ℕ) ((α , β) : T n × T n) → cs n (α , β) ≡ ∞ → α ≡ β)
               → ((A , B) : Π T × Π T)
               → Π-clofun (T , cs) (A , B) ≡ ∞
               → A ≡ B
 Π-clofun'-ice (T , cs) ices (A , B) cAB∼∞
  = fe (λ i → ices i (A i , B i) (Π-clofun'-all (T , cs) (A , B) cAB∼∞ i))

 Π-clofun'-sym : ((T , cs) : sequence-of-clofun-types 𝓤)
               → ((n : ℕ) ((α , β) : T n × T n) → cs n (α , β) ≡ cs n (β , α))
               → ((A , B) : Π T × Π T)
               → Π-clofun (T , cs) (A , B) ≡ Π-clofun (T , cs) (B , A)
 Π-clofun'-sym (T , cs) syms (A , B)
  = ℕ∞-equals (γ (T , cs)
      (λ n (α , β) i → ap (λ - → pr₁ - i) (syms n (α , β))) (A , B))
  where
   γ : ((T , cs) : sequence-of-clofun-types 𝓤)
     → ((n : ℕ) ((α , β) : T n × T n) → pr₁ (cs n (α , β)) ∼ pr₁ (cs n (β , α)))
     → ((A , B) : Π T × Π T)
     → Π-clofun' (T , cs) (A , B) ∼ Π-clofun' (T , cs) (B , A)
   γ (T , cs) syms (A , B) 0 = syms 0 (A 0 , B 0) 0
   γ (T , cs) syms (A , B) (succ i)
    = ap (λ - → min𝟚 - (Π-clofun' (T ∘ succ , cs ∘ succ) (A ∘ succ , B ∘ succ) i))
        (syms 0 (A 0 , B 0) (succ i))
    ∙ ap (λ - → min𝟚 (pr₁ (cs 0 (B 0 , A 0)) (succ i)) -)
        (γ (T ∘ succ , cs ∘ succ) (syms ∘ succ) (A ∘ succ , B ∘ succ) i)

 Lemma[min𝟚abcd≡₁→min𝟚ac≡₁] : {a b c d : 𝟚}
                            → min𝟚 (min𝟚 a b) (min𝟚 c d) ≡ ₁
                            → min𝟚 a c ≡ ₁
 Lemma[min𝟚abcd≡₁→min𝟚ac≡₁] {₁} {₁} {₁} {₁} e = refl
 
 Lemma[min𝟚abcd≡₁→min𝟚bd≡₁] : {a b c d : 𝟚}
                            → min𝟚 (min𝟚 a b) (min𝟚 c d) ≡ ₁
                            → min𝟚 b d ≡ ₁
 Lemma[min𝟚abcd≡₁→min𝟚bd≡₁] {₁} {₁} {₁} {₁} e = refl

 Π-clofun'-ult : ((T , cs) : sequence-of-clofun-types 𝓤)
               → ((n : ℕ) ((α , β , ζ) : T n × T n × T n)
               → min (cs n (α , β)) (cs n (β , ζ)) ≼ cs n (α , ζ))
               → ((A , B , C) : Π T × Π T × Π T)
               → min (Π-clofun (T , cs) (A , B)) (Π-clofun (T , cs) (B , C))
                   ≼ Π-clofun (T , cs) (A , C)
 Π-clofun'-ult (T , cs) ults (A , B , C) 0        r
  = ults 0 (A 0 , B 0 , C 0) 0 r
 Π-clofun'-ult (T , cs) ults (A , B , C) (succ n) r
  = Lemma[a≡₁→b≡₁→min𝟚ab≡₁]
      (ults 0 (A 0 , B 0 , C 0) (succ n)
      (Lemma[min𝟚abcd≡₁→min𝟚ac≡₁]
         {pr₁ (cs 0 (A 0 , B 0)) (succ n)}
         {Π-clofun' (T ∘ succ , cs ∘ succ) (A ∘ succ , B ∘ succ) n}
         {pr₁ (cs 0 (B 0 , C 0)) (succ n)}
         {Π-clofun' (T ∘ succ , cs ∘ succ) (B ∘ succ , C ∘ succ) n}
      r))
      (Π-clofun'-ult (T ∘ succ , cs ∘ succ) (ults ∘ succ)
         (A ∘ succ , B ∘ succ , C ∘ succ) n
      ((Lemma[min𝟚abcd≡₁→min𝟚bd≡₁] 
         {pr₁ (cs 0 (A 0 , B 0)) (succ n)}
         {Π-clofun' (T ∘ succ , cs ∘ succ) (A ∘ succ , B ∘ succ) n}
         {pr₁ (cs 0 (B 0 , C 0)) (succ n)}
         {Π-clofun' (T ∘ succ , cs ∘ succ) (B ∘ succ , C ∘ succ) n}
      r)))

 Π-is-clofun : ((T , cs) : sequence-of-clofun-types 𝓤)
             → (is : (n : ℕ) → is-clofun (cs n))
             → is-clofun (Π-clofun (T , cs))                           
 is-clofun.equal→inf-close
  (Π-is-clofun (T , cs) is)
  = Π-clofun'-eic (T , cs)
      (λ n → is-clofun.equal→inf-close (is n))
     
 is-clofun.inf-close→equal
  (Π-is-clofun (T , cs) is)
  = λ A B f → Π-clofun'-ice (T , cs)
      (λ n (α , β) → is-clofun.inf-close→equal (is n) α β)
      (A , B) f
 
 is-clofun.symmetricity
  (Π-is-clofun (T , cs) is)
  = λ A B → Π-clofun'-sym (T , cs)
      (λ n (α , β) → is-clofun.symmetricity (is n) α β)
      (A , B)

 is-clofun.ultrametric
  (Π-is-clofun (T , cs) is)
  = λ A B C → Π-clofun'-ult (T , cs)
      (λ n (α , β , ζ) → is-clofun.ultrametric (is n) α β ζ)
      (A , B , C)

Π-is-clofun : ((T , cs) : sequence-of-clofun-types 𝓤)
            → (is : (n : ℕ) → is-clofun (cs n))
            → is-clofun (Π-clofun (T , cs))                           
Π-is-clofun = hidden-module.Π-is-clofun
```

We re-formulate the `build-up` little lemma from the previous
blog post.
  
This now states that, given any sequence type `T : ℕ → 𝓤` of types
with closeness functions, any two head elements `x,y : T 0`, any
two tail elements `xs,ys : Π (T ∘ succ)`, and some `δ : ℕ` such
that `x` and `y` are `(δ+1)`-close and `xs` and `ys` are `δ`-close, then
the sequences `(x :: xs)` and `(y :: ys)` are `(δ+1)`-close.

```agda
build-up : ((T , cs) : sequence-of-clofun-types 𝓤)
         → (x y : T 0)
         → (xs ys : Π (T ∘ succ))
         → (δ : ℕ)
         → (succ δ ↑) ≼ cs 0 (x , y)
         → (     δ ↑) ≼ Π-clofun (T ∘ succ , cs ∘ succ) (xs , ys)
         → (succ δ ↑) ≼ Π-clofun (T , cs) (x :: xs , y :: ys)
build-up (T , cs) x y xs ys δ δ≼cxy δ≼cxsys 0 refl
 = δ≼cxy 0 refl
build-up (T , cs) x y xs ys δ δ≼cxy δ≼cxsys (succ n) r
 = Lemma[a≡₁→b≡₁→min𝟚ab≡₁] (δ≼cxy (succ n) r) (δ≼cxsys n r)
```

We also use the following two transports repeatedly, and so
write them in shorthand for easy reuse.

```agda
≼-clofun-refl : {X : 𝓤 ̇ } → (c : X × X → ℕ∞) → is-clofun c
              → (δ : ℕ) → (x : X) → (δ ↑) ≼ c (x , x)
≼-clofun-refl c i δ x
 = transport ((δ ↑) ≼_) (is-clofun.equal→inf-close i x ⁻¹) (∞-maximal (δ ↑))

≼-clofun-sym : {X : 𝓤 ̇ } → (c : X × X → ℕ∞) → is-clofun c
             → (δ : ℕ) → (x y : X) → (δ ↑) ≼ c (x , y) → (δ ↑) ≼ c (y , x)
≼-clofun-sym c i δ x y
 = transport ((δ ↑) ≼_) (is-clofun.symmetricity i x y)
```

## Tychonff theorem - first attempt <a name="tychonoff1"></a>

We can now state the Tychonoff theorem in Agda.

```agda
tychonoff-attempt : ((T , cs) : sequence-of-clofun-types 𝓤)
                  → ((n : ℕ) → is-clofun (cs n))
                  → (𝓔s : (n : ℕ) → c-searchable (T n) (cs n))
                  → c-searchable (Π T) (Π-clofun (T , cs))
```

We develop the searcher and the proof that the searcher
satisfies the search condition separately via
mutual recursion.

```agda
Searcher-attempt : ((T , cs) : sequence-of-clofun-types 𝓤)
                 → ((n : ℕ) → is-clofun (cs n))
                 → (𝓔s : (n : ℕ) → c-searchable (T n) (cs n))
                 → ((p , d) : d-predicate (Π T))
                 → (δ : ℕ)
                 → δ is-u-mod-of p on Π-clofun (T , cs)
                 → Π T

Condition-attempt : ((T , cs) : sequence-of-clofun-types 𝓤)
                  → (is : (n : ℕ) → is-clofun (cs n))
                  → (𝓔s : (n : ℕ) → c-searchable (T n) (cs n))
                  → ((p , d) : d-predicate (Π T))
                  → (δ : ℕ)
                  → (ϕ : δ is-u-mod-of p on Π-clofun (T , cs))
                  → Σ p → p (Searcher-attempt (T , cs) is 𝓔s (p , d) δ ϕ)

tychonoff-attempt (T , cs) is 𝓔s ((p , d) , δ , ϕ)
 = Searcher-attempt  (T , cs) is 𝓔s (p , d) δ ϕ
 , Condition-attempt (T , cs) is 𝓔s (p , d) δ ϕ
```

Eagle-eyed readers will notice the word "attempt" in
these definitions. We expect that our proof to the
Tychonoff theorem for continuously searchable types
will have some subtleties that the proof from the
previous blog post (that sequence types of discrete,
searchable types are continuously searchable) did
not have.

However, for now, we proceed along the same lines as
our previous proof; and wait for these subtleties to
appear.

Firstly, we can still use **Lemma 1** in the base case;
i.e. when the modulus of continuity of the predicate
being searched is `0`. **Lemma 1** stated that any uniformly
continuous discrete predicate `p : uc-d-predicate X c`,
for any closeness function `c : X × X → ℕ∞`, with modulus
of uniform continuity `0 : ℕ` is satisfied by any
construction of `X`. This, coupled with the fact that every
continuously searchable type is inhabited, provides
our base case.

```agda
{-
Searcher-attempt  (T , cs) is Is (p , d) 0  ϕ
 = λ n → c-searchable-types-are-inhabited (cs n) (Is n)

Condition-attempt (T , cs) is Is (p , d) 0 ϕ (α , pα)
 = 0-mod-always-satisfied (Π-clofun (T , cs)) (p , d) ϕ (α , pα)
     (Searcher-attempt (T , cs) is Is (p , d) 0 ϕ)
-}
```

Secondly, we generalise our previous **Lemma 2** for our inductive case.

**Lemma 2** now states that, given any uniformly continuous
discrete predicate `p : uc-d-predicate (Π T)`, with
modulus of uniform continuity `(succ δ) : ℕ`, we can construct
the predicate `(pₜ x) ≔ (λ xs → x :: xs) : uc-d-predicate (Π T)`,
for any given `x : T 0`, which has modulus of uniform continuity `δ : ℕ`.

Recall that we call `(pₜ x)` the "`tail-predicate` for `p` via `x`".

```agda
tail-predicate : {T : ℕ → 𝓤 ̇ }
               → ((p , d) : d-predicate (Π T))
               → (x : T 0) → d-predicate (Π (T ∘ succ))
tail-predicate (p , d) x
 = (λ xs → p (x :: xs)) , (λ xs → d (x :: xs))

tail-predicate-reduce-mod
  : ((T , cs) : sequence-of-clofun-types 𝓤)
  → (is : (n : ℕ) → is-clofun (cs n))
  → ((p , d) : d-predicate (Π T))
  → (x : T 0) → (δ : ℕ)
  → (succ δ) is-u-mod-of p on Π-clofun (T , cs)
  →       δ  is-u-mod-of (pr₁ (tail-predicate (p , d) x))
                      on Π-clofun ((T ∘ succ) , (cs ∘ succ))
tail-predicate-reduce-mod (T , cs) is p x δ ϕ (xs , ys) δ≼cxsys
 = ϕ (x :: xs , x :: ys)
     (build-up (T , cs) x x xs ys δ (≼-clofun-refl (cs 0) (is 0) (succ δ) x) δ≼cxsys)
```

As before, given `(pₜ x)` for any `x : T 0`, we can construct
the "head predicate" `pₕ ≔ (λ x → x :: 𝓔xs x) : d-predicate X`
where `𝓔xs x : ℕ → X` is the sequence that satisfies `(pₜ x)`.

```agda
head-predicate-attempt : ((T , cs) : sequence-of-clofun-types 𝓤)
                       → ((n : ℕ) → is-clofun (cs n))
                       → (𝓔s : (n : ℕ) → c-searchable (T n) (cs n))
                       → ((p , d) : d-predicate (Π T))
                       → (δ : ℕ) → succ δ is-u-mod-of p on (Π-clofun (T , cs))
                       → d-predicate (T 0)
head-predicate-attempt (T , cs) is 𝓔s (p , d) δ ϕ
 = (λ x → p (x :: 𝓔xs x)) , (λ x → d (x :: 𝓔xs x))
 where
   𝓔xs : T 0 → Π (T ∘ succ)
   𝓔xs x = Searcher-attempt (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ)
             (tail-predicate (p , d) x)
             δ (tail-predicate-reduce-mod (T , cs) is (p , d) x δ ϕ)
```

This is where the subtle difference between our Tychonoff
proof and our previous proof appears. Last time, because the
domain of our streams — and hence, the type on which the
head predicate is tested on — were only ever discrete types,
we did not have to prove that the head predicate itself is
continuous. This is because any decidable predicate on a
discrete type is automatically continuous.

This time, however, the head predicate is defined on `(T 0) : 𝓤`;
any continuously searchable type. Thus, we must prove that it
has a modulus of continuity. Specifically, the `head-predicate`
`pₕ : d-predicate (T 0)` for a predicate
`p : uc-d-predicate (Π T) (Π-clofun (T , cs))`
should have the same modulus of continuity as `p`.

```agda
postulate lol : {A : 𝓤 ̇ } → A

head-predicate-same-mod-attempt
  : ((T , cs) : sequence-of-clofun-types 𝓤)
  → (is : (n : ℕ) → is-clofun (cs n))
  → (𝓔s : (n : ℕ) → c-searchable (T n) (cs n))
  → ((p , d) : d-predicate (Π T))
  → (δ : ℕ) → (ϕ : succ δ is-u-mod-of p on (Π-clofun (T , cs)))
  → succ δ is-u-mod-of pr₁ (head-predicate-attempt (T , cs) is 𝓔s (p , d) δ ϕ) on (cs 0)
head-predicate-same-mod-attempt (T , cs) is 𝓔s (p , d) δ ϕ (x , y) δ≼cxy
 = ϕ (x :: 𝓔xs x , y :: 𝓔xs y)
     (build-up (T , cs) x y (𝓔xs x) (𝓔xs y) δ δ≼cxy gap)
  where
    𝓔xs : T 0 → Π (T ∘ succ)
    𝓔xs x = Searcher-attempt (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ)
              (tail-predicate (p , d) x)
              δ (tail-predicate-reduce-mod (T , cs) is (p , d) x δ ϕ)
    gap : (δ ↑) ≼ Π-clofun (T ∘ succ , cs ∘ succ) (𝓔xs x , 𝓔xs y)
    gap = lol
```

Note that we have a hole labelled `gap`. We will consider this shortly,
but for now we wish to see if the rest of the proof follows.

We combine the previous two definitions to form
the full head predicate `pₕ : uc-d-predicate (T 0) (cs 0)`.

```agda
head-predicate-full-attempt
  : ((T , cs) : sequence-of-clofun-types 𝓤)
  → ((n : ℕ) → is-clofun (cs n))
  → (𝓔s : (n : ℕ) → c-searchable (T n) (cs n))
  → ((p , d) : d-predicate (Π T))
  → (δ : ℕ) → succ δ is-u-mod-of p on (Π-clofun (T , cs))
  → uc-d-predicate (T 0) (cs 0)
head-predicate-full-attempt (T , cs) is 𝓔s (p , d) δ ϕ
 = head-predicate-attempt (T , cs) is 𝓔s (p , d) δ ϕ
 , succ δ
 , head-predicate-same-mod-attempt (T , cs) is 𝓔s (p , d) δ ϕ
```

We attempt to define the `Searcher` and `Condition` as before...

```agda
Searcher-attempt  (T , cs) is 𝓔s (p , d) 0        ϕ
 = λ n → c-searchable-types-are-inhabited (cs n) (𝓔s n)

Searcher-attempt  (T , cs) is 𝓔s (p , d) (succ δ) ϕ
 = x :: 𝓔xs x
 where
   pₕ = pr₁ (head-predicate-attempt (T , cs) is 𝓔s (p , d) δ ϕ)

   S-head : Σ x₀ ꞉ T 0 , (Σ pₕ → pₕ x₀)
   S-head = 𝓔s 0 (head-predicate-full-attempt (T , cs) is 𝓔s (p , d) δ ϕ)

   x : T 0
   x = pr₁ S-head

   𝓔xs : T 0 → Π (T ∘ succ)
   𝓔xs x' = Searcher-attempt (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ)
              (tail-predicate (p , d) x')
              δ (tail-predicate-reduce-mod (T , cs) is (p , d) x' δ ϕ)

Condition-attempt (T , cs) is Is (p , d) 0        ϕ (α , pα)
 = 0-mod-always-satisfied (Π-clofun (T , cs)) (p , d) ϕ (α , pα)
     (Searcher-attempt (T , cs) is Is (p , d) 0 ϕ)
     
Condition-attempt (T , cs) is Is (p , d) (succ δ) ϕ (α , pα)
 = γ (α , pα)
 where
   pₕ = pr₁ (head-predicate-attempt (T , cs) is Is (p , d) δ ϕ)
   pₜ = λ x' → pr₁ (tail-predicate (p , d) x')

   S-head : Σ x₀ ꞉ T 0 , (Σ pₕ → pₕ x₀)
   S-head = Is 0 (head-predicate-full-attempt (T , cs) is Is (p , d) δ ϕ)

   x : T 0
   x = pr₁ S-head

   γₕ : Σ pₕ → pₕ x
   γₕ = pr₂ S-head

   𝓔xs : T 0 → Π (T ∘ succ)
   𝓔xs x' = Searcher-attempt (T ∘ succ , cs ∘ succ) (is ∘ succ) (Is ∘ succ)
              (tail-predicate (p , d) x')
              δ (tail-predicate-reduce-mod (T , cs) is (p , d) x' δ ϕ)
               
   γₜ : (x' : T 0) → Σ (pₜ x') → pₜ x' (𝓔xs x')
   γₜ x' = Condition-attempt (T ∘ succ , cs ∘ succ) (is ∘ succ) (Is ∘ succ)
               (tail-predicate (p , d) x')
               δ (tail-predicate-reduce-mod (T , cs) is (p , d) x' δ ϕ)

   γ : Σ p → p (x :: 𝓔xs x)
   γ (α₀ , pα₀) = step₆ where
     x₀  = head α₀
     xs₀ = tail α₀

     step₁ : p (x₀ :: xs₀)
     step₁ = transport p (head-tail-eta α₀) pα₀

     step₂ : (pₜ x₀) xs₀
     step₂ = step₁
    
     step₃ : (pₜ x₀) (𝓔xs x₀)
     step₃ = γₜ x₀ (xs₀ , step₂)
 
     step₄ : pₕ x₀
     step₄ = step₃
    
     step₅ : pₕ x
     step₅ = γₕ (x₀ , step₄)

     step₆ : p (x :: 𝓔xs x)
     step₆ = step₅
```
...and it turns out that we are able to!

So our overall proof works exactly the same for sequences of continuously
searchable as it did for discrete-sequence types in the last blog post;
apart from one key difference ─ the `gap` in our proof.

Unlike last time, we have to prove that the head predicate is continuous.
We avoided this last time by using the fact that every predicate on a discrete
type is trivially continuous. It turns out, however, that
filling this hole is not straightforward.

## Agreeable searchers <a name="agreeable"></a>

The hole asks us to prove that `(𝓔xs x) , (𝓔xs y) : Π (T ∘ succ)`
─ i.e. the results of the searcher applied to (i) the `tail-predicate`
for `p` via `x` and (ii) the `tail-predicate` for `p` via `y` ─ are at least
`δ`-close.

This is a reasonable conjecture. Intuitively, our searchers follow some
form of search strategy, and we expect the results of the searcher applied
to two predicates, `p₁` and `p₂`, that agree everywhere, i.e. both `p₁(x) ⇒ p₂(y)`
and `p₂(x) ⇒ p₁(y)`), to be the same.

To fill our hole, we do not *require* the results of the searcher in
such a situation to be *the same* ─ only that they are at least `δ`-close,
where `δ` is a modulus of continuity shared by `p₁` and `p₂`.

Effectively, our intuition tells us that the searcher itself is a
continuous function.

We call such a 'continuous searcher' that matches our intuition 'agreeable'.

```agda
agree-everywhere : {X : 𝓤 ̇ } → d-predicate X → d-predicate X → 𝓤 ̇
agree-everywhere {𝓤} {X} (p₁ , d₁) (p₂ , d₂) = ((x : X) → p₁ x → p₂ x)
                                             × ((x : X) → p₂ x → p₁ x)


agree-everywhere-self : {X : 𝓤 ̇ } → ((p , d) : d-predicate X)
                      → agree-everywhere (p , d) (p , d)
agree-everywhere-self (p , d) = (λ x px → px) , (λ x px → px)

agreeable : {X : 𝓤 ̇ } → (c : X × X → ℕ∞) → c-searchable X c → (𝓤₀ ⁺) ⊔ 𝓤 ̇ 
agreeable {𝓤} {X} c S = ((p₁ , d₁) (p₂ , d₂) : d-predicate X)
                      → (δ : ℕ)
                      → agree-everywhere (p₁ , d₁) (p₂ , d₂)
                      → (ϕ₁ : δ is-u-mod-of p₁ on c)
                      → (ϕ₂ : δ is-u-mod-of p₂ on c)
                      → (δ ↑) ≼ c (pr₁ (S ((p₁ , d₁) , δ , ϕ₁))
                                 , pr₁ (S ((p₂ , d₂) , δ , ϕ₂)))
```

As an example, the searcher for `𝟚` is agreeable.
In order to prove this with assistance from the
type checker, we reformulate the proof that 𝟚
is continuously searchable. This proof is identical to
that seen in the previous blog post, but the sub-proof
`𝟚-is-c-searchable'` has been brought outside of the
scope of `𝟚-is-c-searchable`.

```agda
𝟚-is-c-searchable' : (p : 𝟚 → 𝓤 ̇ )
                   → decidable (p ₁)
                   → Σ x₀ ꞉ 𝟚 , (Σ p → p x₀)
𝟚-is-c-searchable' p (inl  p₁)
 = ₁ , (λ _ → p₁)
𝟚-is-c-searchable' p (inr ¬p₁)
 = ₀ , γ
 where
   γ : Σ p → p ₀
   γ (₀ , p₀) = p₀
   γ (₁ , p₁) = 𝟘-elim (¬p₁ p₁)

𝟚-is-c-searchable : c-searchable 𝟚 (discrete-clofun 𝟚-is-discrete)
𝟚-is-c-searchable ((p , d) , _) = 𝟚-is-c-searchable' p (d ₁)
```

We then show that the searcher as defined above, when given
two predicates that agree everywhere, always returns the same answer for `x₀`.

Therefore, the searcher for `𝟚` is agreeable.

```agda
𝟚-is-c-searchable'-agree-eq : ((p₁ , d₁) (p₂ , d₂) : d-predicate 𝟚)
                            → agree-everywhere (p₁ , d₁) (p₂ , d₂)
                            → pr₁ (𝟚-is-c-searchable' p₁ (d₁ ₁))
                            ≡ pr₁ (𝟚-is-c-searchable' p₂ (d₂ ₁))
𝟚-is-c-searchable'-agree-eq (p₁ , d₁) (p₂ , d₂) (f , g) = γ (d₁ ₁) (d₂ ₁)
 where
   γ : (d₁₁ : decidable (p₁ ₁)) (d₂₁ : decidable (p₂ ₁))
     → pr₁ (𝟚-is-c-searchable' p₁ d₁₁) ≡ pr₁ (𝟚-is-c-searchable' p₂ d₂₁)
   γ (inl  _ ) (inl  _ ) = refl
   γ (inr  _ ) (inr  _ ) = refl
   γ (inl  p₁) (inr ¬p₁) = 𝟘-elim (¬p₁ (f ₁ p₁))
   γ (inr ¬p₁) (inl  p₁) = 𝟘-elim (¬p₁ (g ₁ p₁))
   
𝟚-has-agreeable-searcher : agreeable (discrete-clofun 𝟚-is-discrete)
                             𝟚-is-c-searchable
𝟚-has-agreeable-searcher (p₁ , d₁) (p₂ , d₂) δ (f , g) ϕ₁ ϕ₂
 = transport (λ - → (δ ↑) ≼ discrete-clofun 𝟚-is-discrete
               (pr₁ (𝟚-is-c-searchable' p₁ (d₁ ₁)) , -))
     (𝟚-is-c-searchable'-agree-eq (p₁ , d₁) (p₂ , d₂) (f , g))
     (≼-clofun-refl (discrete-clofun 𝟚-is-discrete)
       (discrete-is-clofun 𝟚-is-discrete)
       δ (pr₁ (𝟚-is-c-searchable' p₁ (d₁ ₁))))
```

## Tychonoff theorem - second attempt <a name="tychonoff2"></a>

Let's try this again.

We restate our Tychonoff theorem, with the assumption
that each of the continuously searchable types that make up
T yields an agreeable searcher.

```agda
tychonoff : ((T , cs) : sequence-of-clofun-types 𝓤)
          → ((n : ℕ) → is-clofun (cs n))
          → (Is : (n : ℕ) → c-searchable (T n) (cs n))
          → ((n : ℕ) → agreeable (cs n) (Is n))       -- New!
          → c-searchable (Π T) (Π-clofun (T , cs))    

Searcher : ((T , cs) : sequence-of-clofun-types 𝓤)
         → ((n : ℕ) → is-clofun (cs n))
         → (Is : (n : ℕ) → c-searchable (T n) (cs n))
         → ((n : ℕ) → agreeable (cs n) (Is n))        -- New!
         → ((p , d) : d-predicate (Π T))
         → (δ : ℕ)
         → δ is-u-mod-of p on Π-clofun (T , cs)
         → Π T

Condition : ((T , cs) : sequence-of-clofun-types 𝓤)
          → (is : (n : ℕ) → is-clofun (cs n))
          → (𝓔s : (n : ℕ) → c-searchable (T n) (cs n))
          → (as : (n : ℕ) → agreeable (cs n) (𝓔s n))  -- New!
          → ((p , d) : d-predicate (Π T))
          → (δ : ℕ)
          → (ϕ : δ is-u-mod-of p on Π-clofun (T , cs))
          → Σ p → p (Searcher (T , cs) is 𝓔s as (p , d) δ ϕ)

tychonoff (T , cs) is 𝓔s as ((p , d) , δ , ϕ)
 = Searcher  (T , cs) is 𝓔s as (p , d) δ ϕ
 , Condition (T , cs) is 𝓔s as (p , d) δ ϕ
```

Furthermore, as part of our mutually recursive proof, we
must prove that the Tychonoff searcher that we build in `Searcher`
is itself agreeable.

This specifically is what allows us to fill the `gap`.

```agda
Agreeable : ((T , cs) : sequence-of-clofun-types 𝓤)
          → (is : (n : ℕ) → is-clofun (cs n))
          → (𝓔s : (n : ℕ) → c-searchable (T n) (cs n))
          → (as : (n : ℕ) → agreeable (cs n) (𝓔s n))
          → ((p₁ , d₁) (p₂ , d₂) : d-predicate (Π T))
          → (δ : ℕ)
          → agree-everywhere (p₁ , d₁) (p₂ , d₂)
          → (ϕ₁ : δ is-u-mod-of p₁ on (Π-clofun (T , cs)))
          → (ϕ₂ : δ is-u-mod-of p₂ on (Π-clofun (T , cs)))
          → (δ ↑) ≼ Π-clofun (T , cs)
                      (Searcher (T , cs) is 𝓔s as (p₁ , d₁) δ ϕ₁
                     , Searcher (T , cs) is 𝓔s as (p₂ , d₂) δ ϕ₂)
```

We show that, given two predicates `p₁,p₂ : d-prediate (Π T)` that
agree everywhere, some `δ : ℕ` such that `(δ+1)` is a modulus of
uniform continuity for both `p₁` and `p₂`, and two head elements
`x,y : T 0` that are `(δ+1)`-close, then the `tail-predicate` for `p₁`
via `x` agrees everywhere with the `tail-predicate` for `p₂` via `y`.

```agda
tail-predicate-agree : ((T , cs) : sequence-of-clofun-types 𝓤)
                     → (is : (n : ℕ) → is-clofun (cs n))
                     → ((p₁ , d₁) (p₂ , d₂) : d-predicate (Π T))
                     → (δ : ℕ)
                     → (x y : T 0)
                     → (succ δ ↑) ≼ cs 0 (x , y)
                     → agree-everywhere (p₁ , d₁) (p₂ , d₂)
                     → (ϕ₁ : succ δ is-u-mod-of p₁ on (Π-clofun (T , cs)))
                     → (ϕ₂ : succ δ is-u-mod-of p₂ on (Π-clofun (T , cs)))
                     → agree-everywhere (tail-predicate (p₁ , d₁) x)
                                        (tail-predicate (p₂ , d₂) y)
tail-predicate-agree (T , cs) is (p₁ , d₁) (p₂ , d₂) δ x y δ≼cxy (f , g) ϕ₁ ϕ₂
 = (λ xs pₜ₁xs → ϕ₂ (x :: xs , y :: xs)
                    (build-up (T , cs) x y xs xs δ δ≼cxy (δ≼cxsxs xs))
                    (f (x :: xs) pₜ₁xs))
 , (λ xs pₜ₂xs → ϕ₁ (y :: xs , x :: xs)
                    (build-up (T , cs) y x xs xs δ δ≼cyx (δ≼cxsxs xs))
                    (g (y :: xs) pₜ₂xs))
 where
   δ≼cxsxs = ≼-clofun-refl (Π-clofun (T ∘ succ , cs ∘ succ))
                        (Π-is-clofun (T ∘ succ , cs ∘ succ) (is ∘ succ)) δ
   δ≼cyx   = ≼-clofun-sym (cs 0) (is 0) (succ δ) x y δ≼cxy
```

We redefine the head predicate, this time filling the `gap`.

```agda
head-predicate : ((T , cs) : sequence-of-clofun-types 𝓤)
               → ((n : ℕ) → is-clofun (cs n))
               → (Is : (n : ℕ) → c-searchable (T n) (cs n))
               → ((n : ℕ) → agreeable (cs n) (Is n))
               → ((p , d) : d-predicate (Π T))
               → (δ : ℕ) → succ δ is-u-mod-of p on (Π-clofun (T , cs))
               → d-predicate (T 0)
head-predicate (T , cs) is 𝓔s as (p , d) δ ϕ
 = (λ x → p (x :: 𝓔xs x)) , (λ x → d (x :: 𝓔xs x))
 where
   𝓔xs : T 0 → Π (T ∘ succ)
   𝓔xs x = Searcher (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
               (tail-predicate (p , d) x)
               δ (tail-predicate-reduce-mod (T , cs) is (p , d) x δ ϕ)

head-predicate-same-mod
  : ((T , cs) : sequence-of-clofun-types 𝓤)
  → (is : (n : ℕ) → is-clofun (cs n))
  → (𝓔s : (n : ℕ) → c-searchable (T n) (cs n))
  → (as : (n : ℕ) → agreeable (cs n) (𝓔s n))
  → ((p , d) : d-predicate (Π T))
  → (δ : ℕ) → (ϕ : succ δ is-u-mod-of p on (Π-clofun (T , cs)))
  → succ δ is-u-mod-of pr₁ (head-predicate (T , cs) is 𝓔s as (p , d) δ ϕ) on (cs 0)
head-predicate-same-mod (T , cs) is 𝓔s as (p , d) δ ϕ (x , y) δ≼cxy
 = ϕ (x :: 𝓔xs x , y :: 𝓔xs y)
     (build-up (T , cs) x y (𝓔xs x) (𝓔xs y) δ δ≼cxy gap)
  where
    𝓔xs : T 0 → Π (T ∘ succ)
    𝓔xs x = Searcher (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
              (tail-predicate (p , d) x)
              δ (tail-predicate-reduce-mod (T , cs) is (p , d) x δ ϕ)
    gap : (δ ↑) ≼ Π-clofun (T ∘ succ , cs ∘ succ) (𝓔xs x , 𝓔xs y)
    gap = Agreeable (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
           (tail-predicate (p , d) x)
           (tail-predicate (p , d) y)
           δ
           (tail-predicate-agree (T , cs) is (p , d) (p , d) δ x y δ≼cxy
             (agree-everywhere-self (p , d)) ϕ ϕ)
           (tail-predicate-reduce-mod (T , cs) is (p , d) x δ ϕ)
           (tail-predicate-reduce-mod (T , cs) is (p , d) y δ ϕ)

head-predicate-full : ((T , cs) : sequence-of-clofun-types 𝓤)
                    → ((n : ℕ) → is-clofun (cs n))
                    → (Is : (n : ℕ) → c-searchable (T n) (cs n))
                    → ((n : ℕ) → agreeable (cs n) (Is n))
                    → ((p , d) : d-predicate (Π T))
                    → (δ : ℕ) → succ δ is-u-mod-of p on (Π-clofun (T , cs))
                    → uc-d-predicate (T 0) (cs 0)
head-predicate-full (T , cs) is 𝓔s as (p , d) δ ϕ
 = head-predicate (T , cs) is 𝓔s as (p , d) δ ϕ
 , succ δ
 , head-predicate-same-mod (T , cs) is 𝓔s as (p , d) δ ϕ
```

We also show that the head predicates for `p₁` and `p₂` — two
predicates that agree everywhere and have shared modulus
of uniform continuity `δ` — themselves agree everywhere.

```agda
head-predicate-agree
  : ((T , cs) : sequence-of-clofun-types 𝓤)
  → (is : (n : ℕ) → is-clofun (cs n))
  → (𝓔s : (n : ℕ) → c-searchable (T n) (cs n))
  → (as : (n : ℕ) → agreeable (cs n) (𝓔s n))
  → ((p₁ , d₁) (p₂ , d₂) : d-predicate (Π T))
  → (δ : ℕ)
  → agree-everywhere (p₁ , d₁) (p₂ , d₂)
  → (ϕ₁ : succ δ is-u-mod-of p₁ on (Π-clofun (T , cs)))
  → (ϕ₂ : succ δ is-u-mod-of p₂ on (Π-clofun (T , cs)))
  → agree-everywhere
      (head-predicate (T , cs) is 𝓔s as (p₁ , d₁) δ ϕ₁)
      (head-predicate (T , cs) is 𝓔s as (p₂ , d₂) δ ϕ₂)
head-predicate-agree (T , cs) is 𝓔s as (p₁ , d₁) (p₂ , d₂) δ (f , g) ϕ₁ ϕ₂
 = (λ x pₕ₁x → ϕ₂ (x :: 𝓔xs₁ x , x :: 𝓔xs₂ x) (γ  x) (f (x :: 𝓔xs₁ x) pₕ₁x))
 , (λ x pₕ₂x → ϕ₁ (x :: 𝓔xs₂ x , x :: 𝓔xs₁ x) (γ' x) (g (x :: 𝓔xs₂ x) pₕ₂x))
 where
   𝓔xs₁ 𝓔xs₂ : T 0 → Π (T ∘ succ)
   𝓔xs₁ x = Searcher (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
               (tail-predicate (p₁ , d₁) x)
               δ (tail-predicate-reduce-mod (T , cs) is (p₁ , d₁) x δ ϕ₁)
   𝓔xs₂ x = Searcher (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
               (tail-predicate (p₂ , d₂) x)
               δ (tail-predicate-reduce-mod (T , cs) is (p₂ , d₂) x δ ϕ₂)
   γ : (x : T 0) → (succ δ ↑) ≼ Π-clofun (T , cs) (x :: 𝓔xs₁ x , x :: 𝓔xs₂ x)
   γ x = build-up (T , cs) x x (𝓔xs₁ x) (𝓔xs₂ x) δ δ≼cxx
           (Agreeable (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
             (tail-predicate (p₁ , d₁) x) (tail-predicate (p₂ , d₂) x)
             δ
             (tail-predicate-agree (T , cs) is (p₁ , d₁) (p₂ , d₂)
               δ x x δ≼cxx (f , g) ϕ₁ ϕ₂)
             (tail-predicate-reduce-mod (T , cs) is (p₁ , d₁) x δ ϕ₁)
             (tail-predicate-reduce-mod (T , cs) is (p₂ , d₂) x δ ϕ₂))
    where
      δ≼cxx = ≼-clofun-refl (cs 0) (is 0) (succ δ) x
   γ' : (x : T 0) → (succ δ ↑) ≼ Π-clofun (T , cs) (x :: 𝓔xs₂ x , x :: 𝓔xs₁ x)
   γ' x = ≼-clofun-sym (Π-clofun (T , cs)) (Π-is-clofun (T , cs) is)
            (succ δ) (x :: 𝓔xs₁ x) (x :: 𝓔xs₂ x) (γ x)
```

We now provide the `Searcher` and `Condition` in the same way as before.

```agda
Searcher  (T , cs) is 𝓔s as (p , d) 0        ϕ
 = λ n → c-searchable-types-are-inhabited (cs n) (𝓔s n)

Searcher  (T , cs) is 𝓔s as (p , d) (succ δ) ϕ
 = x :: 𝓔xs x
 where
   pₕ = pr₁ (head-predicate (T , cs) is 𝓔s as (p , d) δ ϕ)

   S-head : Σ x₀ ꞉ T 0 , (Σ pₕ → pₕ x₀)
   S-head = 𝓔s 0 (head-predicate-full (T , cs) is 𝓔s as (p , d) δ ϕ)

   x : T 0
   x = pr₁ S-head

   𝓔xs : T 0 → Π (T ∘ succ)
   𝓔xs x = Searcher (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
               (tail-predicate (p , d) x)
               δ (tail-predicate-reduce-mod (T , cs) is (p , d) x δ ϕ)

Condition (T , cs) is 𝓔s as (p , d) 0        ϕ (α , pα)
 = 0-mod-always-satisfied (Π-clofun (T , cs)) (p , d) ϕ (α , pα)
     (Searcher (T , cs) is 𝓔s as (p , d) 0 ϕ)
     
Condition (T , cs) is 𝓔s as (p , d) (succ δ) ϕ (α , pα)
 = γ (α , pα)
 where
   pₕ = pr₁ (head-predicate (T , cs) is 𝓔s as (p , d) δ ϕ)
   pₜ = λ x' → pr₁ (tail-predicate (p , d) x')

   S-head : Σ x₀ ꞉ T 0 , (Σ pₕ → pₕ x₀)
   S-head = 𝓔s 0 (head-predicate-full (T , cs) is 𝓔s as (p , d) δ ϕ)

   x : T 0
   x = pr₁ S-head

   γₕ : Σ pₕ → pₕ x
   γₕ = pr₂ S-head

   𝓔xs : T 0 → Π (T ∘ succ)
   𝓔xs x = Searcher (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
               (tail-predicate (p , d) x)
               δ (tail-predicate-reduce-mod (T , cs) is (p , d) x δ ϕ)
               
   γₜ : (x' : T 0) → Σ (pₜ x') → pₜ x' (𝓔xs x')
   γₜ x = Condition (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
               (tail-predicate (p , d) x)
               δ (tail-predicate-reduce-mod (T , cs) is (p , d) x δ ϕ)

   γ : Σ p → p (x :: 𝓔xs x)
   γ (α₀ , pα₀) = step₆ where
     x₀  = head α₀
     xs₀ = tail α₀

     step₁ : p (x₀ :: xs₀)
     step₁ = transport p (head-tail-eta α₀) pα₀

     step₂ : (pₜ x₀) xs₀
     step₂ = step₁
    
     step₃ : (pₜ x₀) (𝓔xs x₀)
     step₃ = γₜ x₀ (xs₀ , step₂)
 
     step₄ : pₕ x₀
     step₄ = step₃
    
     step₅ : pₕ x
     step₅ = γₕ (x₀ , step₄)

     step₆ : p (x :: 𝓔xs x)
     step₆ = step₅
```

Finally, we prove that the Tychonoff searcher is agreeable.
This is also by induction: on the modulus of continuity of the
two predicates that agree everywhere.

```agda
Agreeable (T , cs) is 𝓔s as (p₁ , d₁) (p₂ , d₂) 0        (f , g) ϕ₁ ϕ₂
  = ≼-clofun-refl (Π-clofun (T , cs)) (Π-is-clofun (T , cs) is)
      0 (Searcher (T , cs) is 𝓔s as (p₁ , d₁) 0 ϕ₁)

Agreeable (T , cs) is 𝓔s as (p₁ , d₁) (p₂ , d₂) (succ δ) (f , g) ϕ₁ ϕ₂
 = build-up (T , cs) x y (𝓔xs₁ x) (𝓔xs₂ y) δ γ₁ γ₂
 where
   x y : T 0
   x = pr₁ (𝓔s 0 (head-predicate-full (T , cs) is 𝓔s as (p₁ , d₁) δ ϕ₁))
   y = pr₁ (𝓔s 0 (head-predicate-full (T , cs) is 𝓔s as (p₂ , d₂) δ ϕ₂))
   𝓔xs₁ 𝓔xs₂ : T 0 → Π (T ∘ succ)
   𝓔xs₁ x' = Searcher (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
               (tail-predicate (p₁ , d₁) x')
               δ (tail-predicate-reduce-mod (T , cs) is (p₁ , d₁) x' δ ϕ₁)
   𝓔xs₂ x' = Searcher (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
               (tail-predicate (p₂ , d₂) x')
               δ (tail-predicate-reduce-mod (T , cs) is (p₂ , d₂) x' δ ϕ₂)
   γ₁ : (succ δ ↑) ≼ cs 0 (x , y)
   γ₁ = as 0
          (head-predicate (T , cs) is 𝓔s as (p₁ , d₁) δ ϕ₁)
          (head-predicate (T , cs) is 𝓔s as (p₂ , d₂) δ ϕ₂)
          (succ δ)
          (head-predicate-agree (T , cs) is 𝓔s as (p₁ , d₁) (p₂ , d₂)
            δ (f , g) ϕ₁ ϕ₂)
          (head-predicate-same-mod (T , cs) is 𝓔s as (p₁ , d₁) δ ϕ₁)
          (head-predicate-same-mod (T , cs) is 𝓔s as (p₂ , d₂) δ ϕ₂)
   γ₂ : (δ ↑) ≼ Π-clofun (T ∘ succ , cs ∘ succ) (𝓔xs₁ x , 𝓔xs₂ y)
   γ₂ = Agreeable (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
          (tail-predicate (p₁ , d₁) x)
          (tail-predicate (p₂ , d₂) y)
          δ
          (tail-predicate-agree (T , cs) is (p₁ , d₁) (p₂ , d₂)
             δ x y γ₁ (f , g) ϕ₁ ϕ₂)
          (tail-predicate-reduce-mod (T , cs) is (p₁ , d₁) x δ ϕ₁)
          (tail-predicate-reduce-mod (T , cs) is (p₂ , d₂) y δ ϕ₂)
```

This completes our formalised proof of the Tychonoff theorem
for continuously searchable types.

## Corollaries <a name="corollaries"></a>

In line with our motivations, we prove that the Cantor type `ℕ → 𝟚`
is searchable. This was proved in the previous blog
post, but this time we use our general Tychonoff theorem.

```agda
ℕ→𝟚-is-c-searchable'
 : c-searchable (ℕ → 𝟚)
     (Π-clofun ((λ _ → 𝟚) , (λ _ → discrete-clofun 𝟚-is-discrete)))
ℕ→𝟚-is-c-searchable'
 = tychonoff
     ((λ _ → 𝟚)
       , (λ _ → discrete-clofun 𝟚-is-discrete))
     (λ _ → discrete-is-clofun 𝟚-is-discrete)
     (λ _ → 𝟚-is-c-searchable)
     (λ _ → 𝟚-has-agreeable-searcher)
```

Furthermore, we prove something that we couldn't last time:
that the type of Cantor sequences `ℕ → (ℕ → 𝟚)`, is
continuously searchable.

```agda
ℕ→ℕ→𝟚-is-c-searchable' : c-searchable (ℕ → (ℕ → 𝟚))
                           (Π-clofun ((λ _ → ℕ → 𝟚)
                           , (λ _ → Π-clofun ((λ _ → 𝟚)
                           , (λ _ → discrete-clofun 𝟚-is-discrete)))))
ℕ→ℕ→𝟚-is-c-searchable'
 = tychonoff
   ((λ _ → ℕ → 𝟚) , (λ _ → Π-clofun ((λ _ → 𝟚)
     , (λ _ → discrete-clofun 𝟚-is-discrete))))
   (λ _ → Π-is-clofun ((λ _ → 𝟚)
     , (λ _ → discrete-clofun 𝟚-is-discrete))
   (λ _ → discrete-is-clofun 𝟚-is-discrete))
   (λ _ → ℕ→𝟚-is-c-searchable')
   (λ _ → Agreeable ((λ _ → 𝟚)
       , (λ _ → discrete-clofun 𝟚-is-discrete))
     (λ _ → discrete-is-clofun 𝟚-is-discrete)
     (λ _ → 𝟚-is-c-searchable)
     (λ _ → 𝟚-has-agreeable-searcher))
```
