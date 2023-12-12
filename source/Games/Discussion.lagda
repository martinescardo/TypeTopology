Martin Escardo, Paulo Oliva, 7-22 June 2023

We relate our game trees to Aczel's W type of CZF sets in various ways.

Peter Aczel. "The Type Theoretic Interpretation of Constructive Set
Theory". Studies in Logic and the Foundations of Mathematics, Volume
96, 1978, Pages 55-66.  https://doi.org/10.1016/S0049-237X(08)71989-X

This type was previously studied by his student Leversha for the
purpose of encoding ordinals in dependent type theory.

Gerald Leversha. "Formal Systems for Constructive Mathematics".  PhD
Thesis, 1976, The University of Manchester (United
Kingdom). Department of Pure and Applied Mathematics.
https://www.sciencedirect.com/science/article/abs/pii/S0049237X0871989X

More references are given below.

We also briefly discuss Conway's games.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc
open import UF.Univalence

\end{code}

In our development of games we worked with pure Martin-Löf type theory
(in Agda notation) for our constructions, sometimes assuming function
extensionality for proving properties of the constructions. For the
purposes of this discussion we further assume univalence and the
existence of propositional truncations (https://homotopytypetheory.org/book/).

\begin{code}

module Games.Discussion
        (ua : Univalence)
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

\end{code}

We get function extensionality from univalence:

\begin{code}

open import UF.FunExt
open import UF.UA-FunExt

fe : Fun-Ext
fe = Univalence-gives-Fun-Ext ua

\end{code}

To make this file self-contained, we will repeat some definitions of
the module Games.TypeTrees. We import the module here, but using
nothing, so that the reader can click at the link to see what is
there.

\begin{code}

open import Games.TypeTrees using ()
open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.PropIndexedPiSigma
open import UF.Subsingletons
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import NotionsOfDecidability.Decidable
\end{code}

The following is the type of type trees, whose nodes X represent the
available moves at some stage of the game, and whose leaves "[]"
represent the endings of the game.

\begin{code}

data 𝕋 : Type₁ where
 []  : 𝕋
 _∷_ : (X : Type) (Xf : X → 𝕋) → 𝕋

\end{code}

The following is the type of paths in a type tree, which represent
full plays in a game.

\begin{code}

Path : 𝕋 → Type
Path []       = 𝟙
Path (X ∷ Xf) = Σ x ꞉ X , Path (Xf x)

⟨⟩ : Path []
⟨⟩ = ⋆

\end{code}

Another view of the type Path Xt for a type tree Xt : 𝕋 is as the
cardinality of the occurrences of leaves in Xt. Under this view, the
type ∥ Path Xt ∥ expresses that there is at least one leaf [] in the
tree Xt.

The type X may well be empty (there are no moves left to play) and
hence the addition of leaves [] seems superfluous.

\begin{code}

[]' : 𝕋
[]' = 𝟘 ∷ unique-from-𝟘

\end{code}

So we don't seem to need [] as we could just use []'. However, if we
adopt this definition, we clearly need to modify our definition of path.

To begin with, there are no paths with the original definition in
[]-free trees.

\begin{code}

is-[]-free : 𝕋 → Type
is-[]-free []       = 𝟘
is-[]-free (X ∷ Xf) = (x : X) → is-[]-free (Xf x)

[]-free-trees-have-no-paths : (Xt : 𝕋) → is-[]-free Xt → is-empty (Path Xt)
[]-free-trees-have-no-paths []       φ ⟨⟩        = φ
[]-free-trees-have-no-paths (X ∷ Xf) φ (x , xs) = []-free-trees-have-no-paths (Xf x) (φ x) xs

\end{code}

However, it is possible to modify the notion of path so that, in some
precise sense, established below, it agrees with the original
definition of path. For that purpose, we consider type trees defined
without the "superfluous" base case [].

\begin{code}

data 𝔸 : Type₁ where
 _∷_ : (X : Type) (Xf : X → 𝔸) → 𝔸

\end{code}

This definition is due to Aczel, who used it to give a model of CZF
(constructive Zermelo-Frankel set theory), as in the reference given
at the top of this file.

Their paths can be defined as follows.

\begin{code}

𝔸-Path : 𝔸 → Type
𝔸-Path (X ∷ Xf) = is-empty X + (Σ x ꞉ X , 𝔸-Path (Xf x))

\end{code}

So there is a path when X is empty, which ends, or there is a path
starting with a move x : X, followed, recursively, by a path in the
tree Xf x of the forest Xf.

We'll come back to this alternative notion of path in a moment. First
we want to explore our original definition of type tree a bit more.

Of course, the type 𝔸 is isomorphic to the subtype of 𝕋 consisting of
[]-free trees.

\begin{code}

𝔽 : Type₁
𝔽 = Σ Xt ꞉ 𝕋 , is-[]-free Xt

\end{code}

To know that this is really a subtype, we need to know that
[]-freeness is property rather than data:

\begin{code}

being-[]-free-is-prop : (Xt : 𝕋) → is-prop (is-[]-free Xt)
being-[]-free-is-prop []       = 𝟘-is-prop
being-[]-free-is-prop (X ∷ Xf) = Π-is-prop fe (λ x → being-[]-free-is-prop (Xf x))

\end{code}

The following should be obvious, but nevertheless we include a proof
because it will serve as a prototype for more sophisticated proofs to
come later.

\begin{code}

af : 𝔸 ≃ 𝔽
af = qinveq f (g , gf , fg)
 where
  f : 𝔸 → 𝔽
  f (X ∷ Xf) = (X ∷ (pr₁ ∘ f ∘ Xf)) , pr₂ ∘ f ∘ Xf

  g : 𝔽 → 𝔸
  g ((X ∷ Xf) , φ) = X ∷ (λ x → g (Xf x , φ x))

  fg' : (Xt : 𝕋) (φ : is-[]-free Xt) → f (g (Xt , φ)) ＝ (Xt , φ)
  fg' (X ∷ Xf) φ =
   (f ∘ g) ((X ∷ Xf) , φ)    ＝⟨ refl ⟩
   (X ∷ (pr₁ ∘ h)) , pr₂ ∘ h ＝⟨ I ⟩
   (X ∷ Xf) , φ              ∎
    where
     h : X → 𝔽
     h x = f (g (Xf x , φ x))

     IH : (x : X) → h x ＝ (Xf x , φ x)
     IH x = fg' (Xf x) (φ x)

     I = ap (λ - → (X ∷ (pr₁ ∘ -)) , pr₂ ∘ -) (dfunext fe IH)

  fg : f ∘ g ∼ id
  fg (Xt , φ) = fg' Xt φ

  gf : g ∘ f ∼ id
  gf (X ∷ Xf) = ap (X ∷_) (dfunext fe (λ x → gf (Xf x)))

\end{code}

Now suppose we insist, for the purposes of game theory, as we will, on
working with 𝕋 rather than 𝔸, with our original definition of path,
and with [] to indicate the end of a play in a game.

Then we should better rule out subtrees whose roots are empty.

In constructive mathematics it is usual to regard a type X to be
inhabited if we can exhibit some x : X. But this is *data* rather than
*property*. Following the philosophy of univalent foundations and
homotopy type theory, we will instead say that X is inhabited if we
can exibit a point of its propositional truncation ∥ X ∥, which is
property. (In the case where we can exhibit some x : X, we say that X
is pointed.)

So we consider trees whose internal nodes are all inhabited. We call
them *hereditarily inhabited*.

\begin{code}

is-hereditarily-inhabited : 𝕋 → Type
is-hereditarily-inhabited []       = 𝟙
is-hereditarily-inhabited (X ∷ Xf) =
 ∥ X ∥ × ((x : X) → is-hereditarily-inhabited (Xf x))

being-hereditarily-inhabited-is-prop : (Xt : 𝕋)
                                     → is-prop (is-hereditarily-inhabited Xt)
being-hereditarily-inhabited-is-prop []       = 𝟙-is-prop
being-hereditarily-inhabited-is-prop (X ∷ Xf) =
 ×-is-prop
  ∥∥-is-prop
  (Π-is-prop fe (λ x → being-hereditarily-inhabited-is-prop (Xf x)))

\end{code}

The good game trees, when we adopt [] to indicate the end of a play in
a game, are those that are hereditarily inhabited.

We define a subtype of 𝕋 with such good game trees, with 𝔾 ambiguously
standing for "good" or "game".

\begin{code}

𝔾 : Type₁
𝔾 = Σ Xt ꞉ 𝕋 , is-hereditarily-inhabited Xt

\end{code}

This type is isomorphic to a subtype ℍ of 𝔸 defined as follows.

\begin{code}

is-hereditarily-decidable : 𝔸 → Type
is-hereditarily-decidable (X ∷ Xf) = (is-decidable ∥ X ∥)
                                   × ((x : X) → is-hereditarily-decidable (Xf x))

being-hereditarily-decidable-is-prop : (Xt : 𝔸)
                                     → is-prop (is-hereditarily-decidable Xt)
being-hereditarily-decidable-is-prop (X ∷ Xf) =
 ×-is-prop
  (+-is-prop ∥∥-is-prop (negations-are-props fe) ¬¬-intro)
  (Π-is-prop fe (λ x → being-hereditarily-decidable-is-prop (Xf x)))

ℍ : Type₁
ℍ = Σ Xt ꞉ 𝔸 , is-hereditarily-decidable Xt

\end{code}

In order to show that 𝔾 ≃ ℍ we need some preparation.

First we define the leaves of 𝔸 trees.

\begin{code}

[]ᴬ : 𝔸
[]ᴬ = 𝟘 ∷ unique-from-𝟘

[]ᴬ-is-hd : is-hereditarily-decidable []ᴬ
[]ᴬ-is-hd = inr (∥∥-rec 𝟘-is-prop id) , (λ x → 𝟘-elim x)

\end{code}

Then the leaves of ℍ trees are defined as follows.

\begin{code}

[]ᴴ : ℍ
[]ᴴ = []ᴬ , []ᴬ-is-hd

\end{code}

We now need a lemma for establishing equality in 𝔸, where Idtofun p
converts a type identification p : X ＝ Y of two types X and Y into a
function X → Y (which is automatically an isomorphism).

\begin{code}

to-𝔸-＝ : {X Y : Type}
          (Xf : X → 𝔸) (Yf : Y → 𝔸)
          (p : X ＝ Y)
        → Xf ＝ Yf ∘ Idtofun p
        → (X ∷ Xf) ＝[ 𝔸 ] (Y ∷ Yf)
to-𝔸-＝ Xf Xf refl refl = refl

\end{code}

With this, using univalence, we see that if X is empty then
[]ᴬ ＝ (X ∷ Xf) for any forest Xf : X → 𝔸. (This is actually the only
use of univalence in this file.)

\begin{code}

[]ᴬ-＝ : {X : Type} (Xf : X → 𝔸) → is-empty X → []ᴬ ＝ (X ∷ Xf)
[]ᴬ-＝ {X} Xf e =
 []ᴬ               ＝⟨ refl ⟩
 𝟘 ∷ unique-from-𝟘 ＝⟨ to-𝔸-＝ 𝟘-elim Xf I II ⟩
 (X ∷ Xf)          ∎
  where
   I : 𝟘 ＝ X
   I = eqtoid (ua 𝓤₀) 𝟘 X (≃-sym (empty-≃-𝟘 e))

   II : unique-from-𝟘 ＝ Xf ∘ Idtofun I
   II = dfunext fe (λ (x : 𝟘) → 𝟘-elim x)

\end{code}

And with this we can prove that the hereditarily decidable 𝔸 trees
form a type isomorphic to that of hereditarily inhabited 𝕋 trees.

 1. The idea of the construction of the isomorphism is to replace
    every subtree X ∷ Xf of the given tree, with X empty, by []. This
    is possible because we assumed that the internal nodes are
    decidable. And then it is clear that the resulting internal nodes
    are all inhabited.

    This construction is given by the function f of the isomorphism hg
    defined below.

 2. In the other direction, we replace [] by []ᴬ := 𝟘 : unique-from-𝟘,
    whose root decidable because it is empty. And also the resulting
    internal nodes are decible because they are inhabited.

    This construction is given by the function g of the isomorphism hg
    defined below.

There is minor technical inconvenience in the construction, which is
that Agda is unable to check that f and g defined directly as sketched
above are structuraly recursive, and so we have to work with their
curried versions, which we call f' and g' respectively.

\begin{code}

hg : ℍ ≃ 𝔾
hg = qinveq f (g , gf , fg)
 where
  f' : (Xt : 𝔸) → is-hereditarily-decidable Xt → 𝔾
  f' (X ∷ Xf) (inl s , d) = (X ∷ (pr₁ ∘ φ)) , s , pr₂ ∘ φ
   where
    have-s : ∥ X ∥
    have-s = s

    have-d : (x : X) → is-hereditarily-decidable (Xf x)
    have-d = d

    φ : X → 𝔾
    φ x = f' (Xf x) (d x)

  f' (X ∷ Xf) (inr e , _) = [] , ⟨⟩
   where
    have-e : is-empty ∥ X ∥
    have-e = e

  f : ℍ → 𝔾
  f = uncurry f'

  g' : (Xt : 𝕋) → is-hereditarily-inhabited Xt → ℍ
  g' []       _       = []ᴴ
  g' (X ∷ Xf) (s , i) = (X ∷ (pr₁ ∘ γ)) , inl s , pr₂ ∘ γ
   where
    have-s : ∥ X ∥
    have-s = s

    have-i : (x : X) → is-hereditarily-inhabited (Xf x)
    have-i = i

    γ : X → ℍ
    γ x = g' (Xf x) (i x)

  g : 𝔾 → ℍ
  g = uncurry g'

  fg' : (Xt : 𝕋) (i : is-hereditarily-inhabited Xt)
      → f (g (Xt , i)) ＝ (Xt , i)
  fg' []       ⟨⟩      = refl
  fg' (X ∷ Xf) (s , i) =
   f (g ((X ∷ Xf) , s , i))      ＝⟨ refl ⟩
   (X ∷ (pr₁ ∘ h)) , s , pr₂ ∘ h ＝⟨ I ⟩
   ((X ∷ Xf) , s , i)            ∎
    where
     h : X → 𝔾
     h x = f (g (Xf x , i x))

     IH : (x : X) → h x ＝ (Xf x , i x)
     IH x = fg' (Xf x) (i x)

     I = ap (λ - → (X ∷ (pr₁ ∘ -)) , s , pr₂ ∘ -)
            (dfunext fe IH)

  fg : f ∘ g ∼ id
  fg (Xt , i) = fg' Xt i

  gf' : (Xt : 𝔸) (d : is-hereditarily-decidable Xt)
      → g (f (Xt , d)) ＝ (Xt , d)
  gf' (X ∷ Xf) (inl s , d) =
   g (f ((X ∷ Xf) , inl s , d))      ＝⟨ refl ⟩
   (X ∷ (pr₁ ∘ h)) , inl s , pr₂ ∘ h ＝⟨ I ⟩
   (X ∷ Xf) , inl s , d              ∎
   where
    h : X → ℍ
    h x = g (f (Xf x , d x))

    IH : (x : X) → h x ＝ (Xf x , d x)
    IH x = gf' (Xf x) (d x)

    I = ap (λ - → (X ∷ (pr₁ ∘ -)) , inl s , pr₂ ∘ -)
           (dfunext fe IH)

  gf' (X ∷ Xf) (inr e , d) =
   g (f ((X ∷ Xf) , inr e , d)) ＝⟨ refl ⟩
   []ᴬ , []ᴬ-is-hd              ＝⟨ II ⟩
   (X ∷ Xf) , inr e , d         ∎
    where
     I : []ᴬ ＝ (X ∷ Xf)
     I = []ᴬ-＝ Xf (λ x → e ∣ x ∣)

     II = to-subtype-＝ being-hereditarily-decidable-is-prop I

  gf : g ∘ f ∼ id
  gf (Xt , i) = gf' Xt i

\end{code}

Not only do we have an isomorphism hg : ℍ ≃ 𝔾, but also an isomorphism
ℍ-Path h ≃ 𝔾-Path (⌜ hg ⌝ h), for each h : ℍ, of type of ℍ-paths of h
and the type of 𝔾-paths along hg, where ⌜ hg ⌝ : ℍ → 𝔾 is the forward
direction of the isomosphism (the function f in the above
construction).

\begin{code}

ℍ-Path : ℍ → Type
ℍ-Path (Xt , _) = 𝔸-Path Xt

𝔾-Path : 𝔾 → Type
𝔾-Path (Xt , _) = Path Xt

hg-path : (h : ℍ) → ℍ-Path h ≃ 𝔾-Path (⌜ hg ⌝ h)
hg-path (Xt , d) = γ Xt d
 where
  γ : (Xt : 𝔸) (d : is-hereditarily-decidable Xt)
    → 𝔸-Path Xt ≃ 𝔾-Path (⌜ hg ⌝ (Xt , d))
  γ (X ∷ Xf) (inl s , d) =
   𝔸-Path (X ∷ Xf)                              ≃⟨ ≃-refl _ ⟩
   is-empty X + (Σ x ꞉ X , 𝔸-Path (Xf x))       ≃⟨ II ⟩
   𝟘 + (Σ x ꞉ X , 𝔸-Path (Xf x))               ≃⟨ 𝟘-lneutral {𝓤₀} {𝓤₀} ⟩
   (Σ x ꞉ X , 𝔸-Path (Xf x))                    ≃⟨ Σ-cong IH ⟩
   (Σ x ꞉ X , Path (pr₁ (⌜ hg ⌝ (Xf x , d x)))) ≃⟨ ≃-refl _ ⟩
   𝔾-Path (⌜ hg ⌝ ((X ∷ Xf) , inl s , d))       ■
   where
    have-s : ∥ X ∥
    have-s = s

    I : is-empty X ≃ 𝟘
    I = empty-≃-𝟘 (λ e → ∥∥-rec 𝟘-is-prop e s)

    IH : (x : X) → 𝔸-Path (Xf x) ≃ Path (pr₁ (⌜ hg ⌝ (Xf x , d x)))
    IH x = γ (Xf x) (d x)

    II = +-cong I (≃-refl _)

  γ (X ∷ Xf) (inr e , d) =
   𝔸-Path (X ∷ Xf)                        ≃⟨ ≃-refl _ ⟩
   is-empty X + (Σ x ꞉ X , 𝔸-Path (Xf x)) ≃⟨ III ⟩
   𝟙 + 𝟘                                  ≃⟨ 𝟘-rneutral' {𝓤₀} {𝓤₀}⟩
   𝟙                                      ≃⟨ ≃-refl _ ⟩
   Path []                                ■
    where
     have-e : is-empty ∥ X ∥
     have-e = e

     I : is-empty X ≃ 𝟙
     I = prop-indexed-product-one fe (λ x → e ∣ x ∣)

     II : (Σ x ꞉ X , 𝔸-Path (Xf x)) ≃ 𝟘
     II = prop-indexed-sum-zero (λ x → e ∣ x ∣)

     III = +-cong I II

gh-path : (g : 𝔾) → 𝔾-Path g ≃ ℍ-Path (⌜ hg ⌝⁻¹ g)
gh-path g = ≃-sym I
 where
  I = ℍ-Path (⌜ hg ⌝⁻¹ g)          ≃⟨ hg-path (⌜ hg ⌝⁻¹ g) ⟩
      𝔾-Path (⌜ hg ⌝ (⌜ hg ⌝⁻¹ g)) ≃⟨ II ⟩
      𝔾-Path g                     ■
        where
         II = idtoeq _ _
               (ap 𝔾-Path
                   (inverses-are-sections ⌜ hg ⌝ ⌜ hg ⌝-is-equiv g))

\end{code}

So the above justifies working with 𝕋 rather than 𝔸, but it also shows
that we could have worked with 𝔸 if we wished. In practice, it is more
convenient to work with 𝕋, but the difference is only convenience.

As we have seen above, 𝕋 contains trees with empty internal nodes,
which don't occur in our work, because we assume, in our main results
on games, that the types X of moves have selection functions (X → R) →
X, with R pointed in the examples, the types of moves are pointed and
hence inhabited. More importantly, the whole point of our work is to
compute optimal strategies, but if there is any strategy at all, the
tree must be hereditarily inhabited.

\begin{code}

Strategy : 𝕋 -> Type
Strategy [] = 𝟙
Strategy (X ∷ Xf) = X × ((x : X) → Strategy (Xf x))

trees-with-strategies-are-hereditarily-inhabited : (Xt : 𝕋)
                                                 → Strategy Xt
                                                 → is-hereditarily-inhabited Xt
trees-with-strategies-are-hereditarily-inhabited []       ⟨⟩ = ⟨⟩
trees-with-strategies-are-hereditarily-inhabited (X ∷ Xf) (x₀ , σf) =
 ∣ x₀ ∣ , λ x → trees-with-strategies-are-hereditarily-inhabited (Xf x) (σf x)

\end{code}

However, it is possible to define a correct notion of strategy for the
isomorphic copy ℍ of 𝔾.

\begin{code}

Strategy' : ℍ -> Type
Strategy' ((X ∷ Xf) , inr _ , _) = 𝟙
Strategy' ((X ∷ Xf) , inl _ , h) = X × ((x : X) → Strategy' (Xf x , h x))

\end{code}
NoNo
Given any tree Xt : 𝕋, we can prune away the subtrees, to get a tree
that has the same paths as Xt, and which is hereditarily inhabited as
soon as there is at least one path in Xt (see further discussion
below).

\begin{code}

prune : 𝕋 → 𝕋
prune []       = []
prune (X ∷ Xf) = (Σ x ꞉ X , ∥ Path (Xf x) ∥)
               ∷ (λ (x , _) → prune (Xf x))

prune-path : (Xt : 𝕋) → Path Xt ≃ Path (prune Xt)
prune-path Xt = qinveq (f Xt) (g Xt , gf Xt , fg Xt)
 where
  f : (Xt : 𝕋) → Path Xt → Path (prune Xt)
  f []       ⟨⟩       = ⟨⟩
  f (X ∷ Xf) (x , xs) = (x , ∣ xs ∣) , f (Xf x) xs

  g : (Xt : 𝕋) → Path (prune Xt) → Path Xt
  g []       ⟨⟩             = ⟨⟩
  g (X ∷ Xf) ((x , _) , xs) = x , g (Xf x) xs

  gf : (Xt : 𝕋) → g Xt ∘ f Xt ∼ id
  gf []       ⟨⟩       = refl
  gf (X ∷ Xf) (x , xs) = ap (x ,_) (gf (Xf x) xs)

  fg : (Xt : 𝕋) → f Xt ∘ g Xt ∼ id
  fg []       ⟨⟩             = refl
  fg (X ∷ Xf) ((x , p) , xs) =
   (f (X ∷ Xf) ∘ g (X ∷ Xf)) ((x , p) , xs)        ＝⟨ refl ⟩
   ((x , ∣ g (Xf x) xs ∣) , f (Xf x) (g (Xf x) xs)) ＝⟨ I ⟩
   ((x , p) , f (Xf x) (g (Xf x) xs))              ＝⟨ II ⟩
   (x , p) , xs                                    ∎
    where
     have-p : ∥ Path (Xf x) ∥
     have-p = p

     I = ap (λ - →  ((x , -) , f (Xf x) (g (Xf x) xs)))
            (∥∥-is-prop ∣ g (Xf x) xs ∣ p)
     II = ap ((x , p) ,_)
             (fg (Xf x) xs)

\end{code}

We would like the tree prune Xt to be hereditarily inhabited, but this
is not possible, constructively, as e.g. the root may be empty but
emptiness is not decidable in general. However, if there is at least
one path in Xt, then this holds:

\begin{code}

prune-is-hereditarily-inhabited : (Xt : 𝕋)
                                → ∥ Path Xt ∥
                                → is-hereditarily-inhabited (prune Xt)
prune-is-hereditarily-inhabited []       _ = ⟨⟩
prune-is-hereditarily-inhabited (X ∷ Xf) p = γ , ϕ
 where
  γ : ∥(Σ x ꞉ X , ∥ Path (Xf x) ∥)∥
  γ = ∥∥-functor (λ (x , xs) → x , ∣ xs ∣) p

  ϕ : ((x , p) : (Σ x ꞉ X , ∥ Path (Xf x) ∥))
    → is-hereditarily-inhabited (prune (Xf x))
  ϕ (x , p) = prune-is-hereditarily-inhabited (Xf x) p

\end{code}

Notice that the type Path Xt is inhabited if there is at least one
leaf [] in the tree Xt.

\begin{code}

has-at-least-one-[] : 𝕋 → Type
has-at-least-one-[] []       = 𝟙
has-at-least-one-[] (X ∷ Xf) = ∃ x ꞉ X , has-at-least-one-[] (Xf x)

having-at-least-one-[]-is-prop : (Xt : 𝕋) → is-prop (has-at-least-one-[] Xt)
having-at-least-one-[]-is-prop []       = 𝟙-is-prop
having-at-least-one-[]-is-prop (X ∷ Xf) = ∃-is-prop

path-gives-at-least-one-[] : (Xt : 𝕋) → ∥ Path Xt ∥ → has-at-least-one-[] Xt
path-gives-at-least-one-[] []       s = ⟨⟩
path-gives-at-least-one-[] (X ∷ Xf) s = γ
 where
  IH : (x : X) → ∥ Path (Xf x) ∥ → has-at-least-one-[] (Xf x)
  IH x = path-gives-at-least-one-[] (Xf x)

  γ : ∃ x ꞉ X , has-at-least-one-[] (Xf x)
  γ = ∥∥-functor (λ (x , xs) → x , IH x ∣ xs ∣) s

at-least-one-[]-gives-path : (Xt : 𝕋) → has-at-least-one-[] Xt → ∥ Path Xt ∥
at-least-one-[]-gives-path []       h = ∣ ⟨⟩ ∣
at-least-one-[]-gives-path (X ∷ Xf) h = γ
 where
  IH : (x : X) → has-at-least-one-[] (Xf x) → ∥ Path (Xf x) ∥
  IH x = at-least-one-[]-gives-path (Xf x)

  γ : ∃ x ꞉ X , Path (Xf x)
  γ = ∥∥-rec ∃-is-prop (λ (x , g) → remove-truncation-inside-∃ ∣ x , IH x g ∣) h

\end{code}

And, of course:

\begin{code}

[]-property : (Xt : 𝕋) → is-[]-free Xt → ¬ has-at-least-one-[] Xt
[]-property (X ∷ Xf) f h = ∥∥-rec 𝟘-is-prop (λ (x , g) → IH x (f x) g) h
 where
  IH : (x : X) → is-[]-free (Xf x) → ¬ has-at-least-one-[] (Xf x)
  IH x = []-property (Xf x)

[]-property₂ : (Xt : 𝕋) → is-[]-free Xt → ¬ ∥ Path Xt ∥
[]-property₂ Xt f = contrapositive (path-gives-at-least-one-[] Xt) ([]-property Xt f)

\end{code}

We remark that the developent of game theory here using 𝕋 doesn't
actually require us to restrict to hereditarily inhabited
trees. However, empty internal nodes play no role, because, as we have
discussed, if we prune them away we obtain a tree with the same paths,
and all that matters about a tree, for the purposes of game theory,
are its paths, which correspond to full plays in a game. One advantage
of the original development using 𝕋 is that it works in pure MLTT,
whereas the approach using 𝔾 or ℍ requires propositional truncation
and function extensionality.

We now show how the file Games.FiniteHistoryDependent could have been
written using ℍ instead of 𝕋, for the sake of illustration, including
a few of the original definitions with 𝕋 alongside the required
modification needed to use ℍ instead:

\begin{code}

module illustration (R : Type) where

 open import Games.FiniteHistoryDependent using ()
 open import Games.K

 open K-definitions R

 Path' : ℍ → Type
 Path' ((X ∷ Xf) , inr _ , _) = 𝟙
 Path' ((X ∷ Xf) , inl _ , h) = Σ x ꞉ X , Path' (Xf x , h x)

 𝓚 : 𝕋 → Type
 𝓚 []       = 𝟙
 𝓚 (X ∷ Xf) = K X × ((x : X) → 𝓚 (Xf x))

 𝓚' : ℍ → Type
 𝓚' ((X ∷ Xf) , inr _ , _) = 𝟙
 𝓚' ((X ∷ Xf) , inl _ , h) = K X × ((x : X) → 𝓚' (Xf x , h x))

 K-sequence : {Xt : 𝕋} → 𝓚 Xt → K (Path Xt)
 K-sequence {[]}     ⟨⟩       = λ q → q ⟨⟩
 K-sequence {X ∷ Xf} (ϕ , ϕf) = ϕ ⊗ᴷ (λ x → K-sequence {Xf x} (ϕf x))

 K-sequence' : {Xt : ℍ} → 𝓚' Xt → K (Path' Xt)
 K-sequence' {(X ∷ Xf) , inr _ , h} ⟨⟩        = λ q → q ⟨⟩
 K-sequence' {(X ∷ Xf) , inl _ , h} (ϕ , ϕf) = ϕ ⊗ᴷ (λ x → K-sequence' {Xf x , h x} (ϕf x))

 strategic-path : {Xt : 𝕋} → Strategy Xt → Path Xt
 strategic-path {[]}     ⟨⟩       = ⟨⟩
 strategic-path {X ∷ Xf} (x , σf) = x , strategic-path {Xf x} (σf x)

 strategic-path' : {Xt : ℍ} → Strategy' Xt → Path' Xt
 strategic-path' {(X ∷ Xf) , inr _ , h} ⟨⟩       = ⟨⟩
 strategic-path' {(X ∷ Xf) , inl _ , h} (x , σf) = x , strategic-path' {Xf x , h x} (σf x)

\end{code}

The above illustrates that the definitions are almost the same, but
more cumbersome in terms of the patterns for case analysis. So we
prefer to work with 𝕋 in practice.

To illustrate the richness of 𝔸 and 𝕋, we now show how to embed the
type of all ordinals into 𝔸, and then some kinds of ordinals in 𝔾, following

   Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg and Chuangjie
   Xu. *Set-Theoretic and Type-Theoretic Ordinals Coincide.*
   To appear at LICS 2023, June 2023.

   https://arxiv.org/abs/2301.10696

This paper is formalized in Ordinals.CumulativeHierarchy. We redefine
the function Ord-to-𝔸 below.

\begin{code}

open import Ordinals.CumulativeHierarchy using ()
open import Ordinals.Type
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Underlying

Ord-to-𝔸 : Ordinal 𝓤₀ → 𝔸
Ord-to-𝔸 = transfinite-recursion-on-OO 𝔸 (λ α f → ⟨ α ⟩ ∷ f)

Ord-to-𝔸-behaviour : (α : Ordinal 𝓤₀)
                   → Ord-to-𝔸 α ＝ (⟨ α ⟩ ∷ λ (a : ⟨ α ⟩) → Ord-to-𝔸 (α ↓ a))
Ord-to-𝔸-behaviour = transfinite-recursion-on-OO-behaviour 𝔸 (λ α f → ⟨ α ⟩ ∷ f)

\end{code}

Which ordinals produce hereditarily decidable trees? The ones that are
hereditarily decidable in the following sense.

\begin{code}

is-hereditarily-decidableₒ : Ordinal 𝓤₀ → Type
is-hereditarily-decidableₒ α = is-decidable ∥ ⟨ α ⟩ ∥
                             × ((a : ⟨ α ⟩) → is-decidable ∥ ⟨ α ↓ a ⟩ ∥)
\end{code}

Notice that the above definition doesn't use induction.

\begin{code}

hereditarily-decidable→ : (α : Ordinal 𝓤₀)
                        → is-hereditarily-decidableₒ α
                        → is-hereditarily-decidable (Ord-to-𝔸 α)
hereditarily-decidable→ = transfinite-induction-on-OO _ ϕ
 where
  ϕ : (α : Ordinal 𝓤₀)
    → ((a : ⟨ α ⟩) → is-hereditarily-decidableₒ (α ↓ a)
                   → is-hereditarily-decidable (Ord-to-𝔸 (α ↓ a)))
    → is-hereditarily-decidableₒ α → is-hereditarily-decidable (Ord-to-𝔸 α)
  ϕ α f (d , e) = IV
   where
    g : (a b : ⟨ α ⟩)
      → b ≺⟨ α ⟩ a
      → (Σ x ꞉ ⟨ α ⟩ , x ≺⟨ α ⟩ b)
      → (Σ (x , m) ꞉ ⟨ α ↓ a ⟩ , x ≺⟨  α ⟩ b)
    g a b l (x , m) = (x , Transitivity α x b a m l) , m

    h : (a b : ⟨ α ⟩)
      → (Σ (x , m) ꞉ ⟨ α ↓ a ⟩ , x ≺⟨  α ⟩ b)
      → (Σ x ꞉ ⟨ α ⟩ , x ≺⟨ α ⟩ b)
    h a b ((x , m) , n) = x , n

    I : (a : ⟨ α ⟩)
        ((b , l) : ⟨ α ↓ a ⟩)
      → is-decidable (∃ (x , m) ꞉ ⟨ α ↓ a ⟩ , x ≺⟨ α ⟩ b )
    I a (b , l) = map-is-decidable (∥∥-functor (g a b l)) (∥∥-functor (h a b)) (e b)

    II : (a : ⟨ α ⟩) → is-hereditarily-decidable (Ord-to-𝔸 (α ↓ a))
    II a = f a (e a , I a)

    III : is-hereditarily-decidable (⟨ α ⟩ ∷ λ (a : ⟨ α ⟩) → Ord-to-𝔸 (α ↓ a))
    III = d , II

    IV : is-hereditarily-decidable (Ord-to-𝔸 α)
    IV = transport is-hereditarily-decidable ((Ord-to-𝔸-behaviour α)⁻¹) III

hereditarily-decidable← : (α : Ordinal 𝓤₀)
                        → is-hereditarily-decidable (Ord-to-𝔸 α)
                        → is-hereditarily-decidableₒ α
hereditarily-decidable← = transfinite-induction-on-OO _ ϕ
 where
  ϕ : (α : Ordinal 𝓤₀)
    → ((a : ⟨ α ⟩) → is-hereditarily-decidable (Ord-to-𝔸 (α ↓ a))
                   → is-hereditarily-decidableₒ (α ↓ a))
    → is-hereditarily-decidable (Ord-to-𝔸 α) → is-hereditarily-decidableₒ α
  ϕ α f h = II , V
   where
    I : is-hereditarily-decidable (⟨ α ⟩ ∷ λ (a : ⟨ α ⟩) → Ord-to-𝔸 (α ↓ a))
    I = transport is-hereditarily-decidable (Ord-to-𝔸-behaviour α) h

    II : is-decidable ∥ ⟨ α ⟩ ∥
    II = pr₁ I

    III : (a : ⟨ α ⟩) → is-hereditarily-decidable (Ord-to-𝔸 (α ↓ a))
    III = pr₂ I

    IV : (a : ⟨ α ⟩) → is-hereditarily-decidableₒ (α ↓ a)
    IV a = f a (III a)

    V : (a : ⟨ α ⟩) → is-decidable ∥ ⟨ α ↓ a ⟩ ∥
    V a = pr₁ (IV a)

\end{code}

So every hereditarily-decidable ordinal gives rise to a
hereditarily-decidableₒ game tree. Plays in the game are
(automatically finite) decreasing sequences that end with the least
element.

\begin{code}

Ord-to-𝔾 : (α : Ordinal 𝓤₀) → is-hereditarily-decidableₒ α → 𝔾
Ord-to-𝔾 α g = ⌜ hg ⌝ (Ord-to-𝔸 α , hereditarily-decidable→ α g)

\end{code}

We now discuss the relation to Conway's games.

As preparation, let's look at the type 𝔸 set-theoretically, as
intended by Aczel. An 𝔸 tree X ∷ Xf represents a set whose members are
the sets represented by Xf x, for each x : X. This is an inductive
definition of "representation".

So, in our encoding of game trees as suitable 𝔸 trees, a game tree is
just a set. The first move, if any move is available, is an element of
that set, which is itself a set and so a game tree. The second move is
in that set, and so on, until we reach the empty set (by the axiom of
foundation), which is when the game ends.

Conway defines two-person games inductively, in set theory rather than
type theory, inductively as follows: a game is a pair (L,R) where L
and R are two sets of games.

https://en.wikipedia.org/wiki/On_Numbers_and_Games
https://en.wikipedia.org/wiki/Surreal_number

Our definition, corresponding to 𝔸, can be restated as follows: a game
is a set G, where each g : G is a game. But this is just the inductive
definition of (material) set.

\begin{code}

data ℂ : Type₁ where
 conway : (L R : Type) (Lf : L → ℂ) (Rf : R → ℂ) → ℂ

\end{code}

Here L is the type of available moves (also called "options") for the
left player, R is the type of available moves for the right player,
and Lf and Rf respectively say which subgame the game transitions to
after a move has been played.

So Conway's games allow only win-or-lose. In particular, there is no
draw, such as in tic-tac-toe or chess. Or outcomes more general than
win, draw or lose, such as in poker.

Our conception of game, defined in Games.FiniteHistoryDependent,
allows for two-person games of the above kind, but in general is
defined for multiple-person games, with outcomes (or "pay offs") in
any type, for example the real numbes.

In the following paper the author shows that shows that Aczel and
Leversha's original W-type gives a model of multisets.

Håkon Gylterud. Multisets in type theory.  Mathematical Proceedings of
the Cambridge Philosophical Society , Volume 169 , Issue 1 , July
2020, pp. 1-18. https://doi.org/10.1017/S0305004119000045

The idea of carving out the sets (or the cumulative hierarchy) from
Aczel's 𝕎-type using hereditary embeddings is due to Håkon Gylterud.

  H. R. Gylterud, "From multisets to sets in homotopy type theory," The
  Journal of Symbolic Logic, vol. 83, no. 3, pp. 1132–1146, 2018.
  https://doi.org/10.1017/jsl.2017.84

\begin{code}

open import UF.Embeddings

is-CZF-set : 𝔸 → Type₁
is-CZF-set (X ∷ Xf) = is-embedding Xf × ((x : X) → is-CZF-set (Xf x))

\end{code}

Aczel instead considers, in the reference at the top of this file, an
equivalence relation to identify repetitions in multisets to get sets.

The abstract https://hott-uf.github.io/2023/HoTTUF_2023_paper_1981.pdf
by Håkon, Elisabeth Bonnevier, Anders Mörtberg and Daniel Gratzer is
also worth mentioning.

We thank Tom de Jong for discussions and bibliographic references. He
also asks: can we embed ℂ into 𝔸? We leave this for further thought.
