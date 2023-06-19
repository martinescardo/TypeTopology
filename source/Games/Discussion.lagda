Martin Escardo, Paulo Oliva, 9-17 June 2023

We relate our game trees to Aczel's W type of CZF sets in various ways.
https://www.sciencedirect.com/science/article/abs/pii/S0049237X0871989X

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

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
the module Games.TypeTrees, and hence we hide them from the present
file.

\begin{code}

open import Games.TypeTrees hiding (𝕋 ; Path ; _::_ ; ⟨⟩)
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

\end{code}

The following is the type of type trees, whose nodes X represent the
available moves at some stage of the game, and whose leafs "[]"
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
cardinality of the occurrences of leafs in Xt. Under this view, the
type ∥ Path Xt ∥ expresses that there is at least one leaf [] in the
tree Xt.

The type X may well be empty (there are no moves left to play) and
hence the addition of leafs [] seems superfluous.

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

Then we should better disregard subtrees whose roots are empty.

In constructive mathematics it is usual to regard a type X to be
inhabited if we can exhibit some x : X. But this is data rather than
property. Following the philosophy of univalent foundations and
homotopy type theory, we will instead say that X is inhabited if we
can exibit a point of its propositional truncation ∥ X ∥. (In the case
where we can exhibit some x : X, we say that X is pointed.)

So we consider trees with the property that the root of each subtree
is inhabited. We call them *hereditarily inhabited*.

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

First we define the leafs of 𝔸 trees.

\begin{code}

[]ᴬ : 𝔸
[]ᴬ = 𝟘 ∷ unique-from-𝟘

[]ᴬ-is-hd : is-hereditarily-decidable []ᴬ
[]ᴬ-is-hd = inr (∥∥-rec 𝟘-is-prop id) , (λ x → 𝟘-elim x)

\end{code}

Then the leafs of ℍ trees are defined as follows.

\begin{code}

[]ᴴ : ℍ
[]ᴴ = []ᴬ , []ᴬ-is-hd

\end{code}

We now need a lemma for establishing equality in 𝔸, where Idtofun p
converts a type identification p : X ＝ Y into a function X → Y.

\begin{code}

to-𝔸-＝ : {X Y : Type}
          (Xf : X → 𝔸) (Yf : Y → 𝔸)
          (p : X ＝ Y)
        → Xf ＝ Yf ∘ Idtofun p
        → (X ∷ Xf) ＝[ 𝔸 ] (Y ∷ Yf)
to-𝔸-＝ Xf Xf refl refl = refl

\end{code}

With this, using univalence, we see that if X is empty then
[]ᴬ ＝ (X ∷ Xf) for any forest Xf : X → 𝔸.

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
   II = dfunext fe (λ x → 𝟘-elim x)

\end{code}

And with this we can prove that the hereditarily decidable 𝔸 trees
form a type isomorphic to that of hereditarily inhabited 𝕋 trees.

\begin{code}

hg : ℍ ≃ 𝔾
hg = qinveq f (g , gf , fg)
 where
  f' : (Xt : 𝔸) → is-hereditarily-decidable Xt → 𝔾
  f' (X ∷ Xf) (inl s , k) = (X ∷ (pr₁ ∘ φ)) , s , pr₂ ∘ φ
   where
    φ : X → 𝔾
    φ x = f' (Xf x) (k x)

  f' (X ∷ Xf) (inr _ , _) = [] , ⟨⟩

  f : ℍ → 𝔾
  f = uncurry f'

  g' : (Xt : 𝕋) → is-hereditarily-inhabited Xt → ℍ
  g' []       _       = []ᴴ
  g' (X ∷ Xf) (s , k) = (X ∷ (pr₁ ∘ γ)) , inl s , pr₂ ∘ γ
   where
    γ : X → ℍ
    γ x = g' (Xf x) (k x)

  g : 𝔾 → ℍ
  g = uncurry g'

  fg' : (Xt : 𝕋) (i : is-hereditarily-inhabited Xt)
      → f (g (Xt , i)) ＝ (Xt , i)
  fg' []       ⟨⟩      = refl
  fg' (X ∷ Xf) (s , k) =
   f (g ((X ∷ Xf) , s , k))      ＝⟨ refl ⟩
   (X ∷ (pr₁ ∘ h)) , s , pr₂ ∘ h ＝⟨ I ⟩
   ((X ∷ Xf) , s , k)            ∎
    where
     h : X → 𝔾
     h x = f (g (Xf x , k x))

     IH : (x : X) → h x ＝ (Xf x , k x)
     IH x = fg' (Xf x) (k x)

     I = ap (λ - → (X ∷ (pr₁ ∘ -)) , s , pr₂ ∘ -)
            (dfunext fe IH)

  fg : f ∘ g ∼ id
  fg (Xt , i) = fg' Xt i

  gf' : (Xt : 𝔸) (d : is-hereditarily-decidable Xt)
      → g (f (Xt , d)) ＝ (Xt , d)
  gf' (X ∷ Xf) (inl s , k) =
   g (f ((X ∷ Xf) , inl s , k))      ＝⟨ refl ⟩
   (X ∷ (pr₁ ∘ h)) , inl s , pr₂ ∘ h ＝⟨ I ⟩
   (X ∷ Xf) , inl s , k              ∎
   where
    h : X → ℍ
    h x = g (f (Xf x , k x))

    IH : (x : X) → h x ＝ (Xf x , k x)
    IH x = gf' (Xf x) (k x)

    I = ap (λ - → (X ∷ (pr₁ ∘ -)) , inl s , pr₂ ∘ -)
           (dfunext fe IH)

  gf' (X ∷ Xf) (inr n , k) =
   g (f ((X ∷ Xf) , inr n , k)) ＝⟨ refl ⟩
   []ᴴ                          ＝⟨ I ⟩
   (X ∷ Xf) , inr n , k         ∎
    where
     I = to-subtype-＝
          being-hereditarily-decidable-is-prop
          ([]ᴬ-＝ Xf (λ x → n ∣ x ∣))

  gf : g ∘ f ∼ id
  gf (Xt , i) = gf' Xt i

\end{code}

Not only do we have an isomorphism ℍ ≃ 𝔾, but also so are the types of ℍ-paths
and 𝔾-paths along this isomorphism.

\begin{code}

ℍ-Path : ℍ → Type
ℍ-Path (Xt , _) = 𝔸-Path Xt

𝔾-Path : 𝔾 → Type
𝔾-Path (Xt , _) = Path Xt

hg-path : (h : ℍ) → ℍ-Path h ≃ 𝔾-Path (⌜ hg ⌝ h)
hg-path (Xt , d) = γ Xt d
 where
  γ : (Xt : 𝔸) (i : is-hereditarily-decidable Xt)
    → 𝔸-Path Xt ≃ 𝔾-Path (⌜ hg ⌝ (Xt , i))
  γ (X ∷ Xf) (inl s , k) =
   𝔸-Path (X ∷ Xf)                              ≃⟨ ≃-refl _ ⟩
   is-empty X + (Σ x ꞉ X , 𝔸-Path (Xf x))       ≃⟨ I ⟩
   𝟘 + (Σ x ꞉ X , 𝔸-Path (Xf x))               ≃⟨ 𝟘-lneutral {𝓤₀} {𝓤₀} ⟩
   (Σ x ꞉ X , 𝔸-Path (Xf x))                    ≃⟨ Σ-cong IH ⟩
   (Σ x ꞉ X , Path (pr₁ (⌜ hg ⌝ (Xf x , k x)))) ≃⟨ ≃-refl _ ⟩
   𝔾-Path (⌜ hg ⌝ ((X ∷ Xf) , inl s , k))       ■
   where
    IH : (x : X) → 𝔸-Path (Xf x) ≃ Path (pr₁ (⌜ hg ⌝ (Xf x , k x)))
    IH x = γ (Xf x) (k x)

    I = +-cong
        (empty-≃-𝟘 (λ e → ∥∥-rec 𝟘-is-prop e s))
        (≃-refl _)

  γ (X ∷ Xf) (inr n , i) =
   𝔸-Path (X ∷ Xf)                        ≃⟨ ≃-refl _ ⟩
   is-empty X + (Σ x ꞉ X , 𝔸-Path (Xf x)) ≃⟨ I ⟩
   𝟙 + 𝟘                                  ≃⟨ 𝟘-rneutral' {𝓤₀} {𝓤₀}⟩
   𝟙                                      ≃⟨ ≃-refl _ ⟩
   Path []                                ■
    where
     I = +-cong
          (prop-indexed-product-one fe (λ x → n ∣ x ∣))
          (prop-indexed-sum-zero (λ x → n ∣ x ∣))

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
which are useless as they are useless, and play no role, if we use []
to indicate the end of a path.

Given any tree Xt : 𝕋, we can prune away such useless subtrees, to get
a tree that has the same paths as Xt.

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
  g (X ∷ Xf) ((x , p) , xs) = x , g (Xf x) xs

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

A last remark is that the developent of game theory here using 𝕋
doesn't actually require us to restrict to hereditarily inhabited
trees. However, empty internal nodes play no role, because, as we have
discussed, if we prune them away we obtain a tree with the same paths,
and all that matters about a tree, for the purposes of game theory,
are its paths, which correspond to full plays in a game. One advantage
of the the original development using 𝕋 is that it works in pure MLTT,
whereas the approach using 𝔾 or ℍ requires propositional truncation
and function extensionality.
