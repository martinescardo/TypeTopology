Alice Laroche, the 18th of September 2023,
using ideas and notations from Ayberk Tosun.

This file is a formalisation of Kirby-Paris Hydra game.  We show that
every battle eventually ends, and use this fact to compute the first
terms of Hydra(n).

[1] https://en.wikipedia.org/wiki/Hydra_game

[2] Kirby, Laurie; Paris, Jeff. Bull. Accessible independence results
    for Peano arithmetic.  London Math. Soc, 14 (1982), 285-293.
    http://logic.amu.edu.pl/images/3/3c/Kirbyparis.pdf

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.Hydra where

open import MLTT.Spartan
open import MLTT.List
open import Ordinals.Notions

\end{code}

The type of Hydra is defined inductively: It is a list of subhydras
where empty list represent heads.

\begin{code}

data Hydra : 𝓤₀ ̇ where
 Node : List Hydra → Hydra

pattern Head = Node []

heads : Hydra → List Hydra
heads (Node hs) = hs

example₁ : Hydra
example₁ = Node (Node [] ∷ [])

example₂ : Hydra
example₂ = Node (Node [] ∷ Node [] ∷ [])

defeated : Hydra
defeated = Node []

\end{code}

We define the type of head's locations using two inductive type.  This
is to know if the head is a child or a grandchild, to help
implementing hydra regeneration mechanism.

\begin{code}

data HeadLocation₀ : List Hydra → 𝓤₀ ̇ where
 here : {hs : List Hydra}
      → HeadLocation₀ (Head ∷ hs)
 next : {h : Hydra} {hs : List Hydra}
      → HeadLocation₀ hs → HeadLocation₀ (h ∷ hs)

data HeadLocation₁ : List Hydra → 𝓤₀ ̇ where
 here₀ : {hs hs' : List Hydra}
       → HeadLocation₀ hs → HeadLocation₁ (Node hs ∷ hs')
 here₁ : {hs hs' : List Hydra}
       → HeadLocation₁ hs → HeadLocation₁ (Node hs ∷ hs')
 next  : {h : Hydra} {hs : List Hydra}
       → HeadLocation₁ hs → HeadLocation₁ (h ∷ hs)

HeadLocation : Hydra → 𝓤₀ ̇
HeadLocation (Node hs) = HeadLocation₀ hs + HeadLocation₁ hs

\end{code}

Similarly, we define two cutting functions, one for cutting child head
and for cutting a grand-child head and regrowing subheads.

\begin{code}

cons-mult : {X : 𝓤 ̇ } → X → ℕ → List X → List X
cons-mult x 0 xs = xs
cons-mult x (succ n) xs = x ∷ (cons-mult x n xs)

HeadLocation₀-gives-is-non-empty : {hs : List Hydra}
                                 → HeadLocation₀ hs
                                 → is-non-empty hs
HeadLocation₀-gives-is-non-empty here     = ⋆
HeadLocation₀-gives-is-non-empty (next l) = ⋆

HeadLocation₁-gives-is-non-empty : {hs : List Hydra}
                                 → HeadLocation₁ hs
                                 → is-non-empty hs
HeadLocation₁-gives-is-non-empty (here₀ l) = ⋆
HeadLocation₁-gives-is-non-empty (here₁ l) = ⋆
HeadLocation₁-gives-is-non-empty (next  l) = ⋆

cut₀ : (hs : List Hydra) → HeadLocation₀ hs → List Hydra
cut₀ []       l         = 𝟘-elim (HeadLocation₀-gives-is-non-empty l)
cut₀ (h ∷ hs) (here)    = hs
cut₀ (h ∷ hs) (next l)  = h ∷ (cut₀ hs l)

cut₁ : ℕ → (hs : List Hydra) → HeadLocation₁ hs → List Hydra
cut₁ n []                l         =
 𝟘-elim (HeadLocation₁-gives-is-non-empty l)
cut₁ n (h ∷ hs')         (next  l) = h ∷ (cut₁ n hs' l)
cut₁ n ((Node hs) ∷ hs') (here₀ l) = cons-mult (Node (cut₀ hs l)) (succ n) hs'
cut₁ n ((Node hs) ∷ hs') (here₁ l) = Node (cut₁ n hs l) ∷ hs'

cut : ℕ → (h : Hydra) → HeadLocation h → Hydra
cut n (Node hs) (inl l) = Node (cut₀ hs l)
cut n (Node hs) (inr l) = Node (cut₁ n hs l)

\end{code}

To prove that the process of cutting hydra's heads always end, we
define a relation between hydras and prove it's well founded.

\begin{code}

_⊲_ : Hydra → Hydra → 𝓤₀ ̇
h ⊲ h' = Σ n ꞉ ℕ , Σ l ꞉ HeadLocation h' , h ＝ cut n h' l

pattern step n l eq = (n , l , eq)

_⊲'_ : List Hydra → List Hydra → 𝓤₀ ̇
hs ⊲' hs' = Σ n ꞉ ℕ , ( ( Σ l ꞉ HeadLocation₀ hs' , hs ＝ cut₀ hs' l)
                      + ( Σ l ꞉ HeadLocation₁ hs' , hs ＝ cut₁ n hs' l))

pattern step₀ n l eq = (n , inl (l , eq))
pattern step₁ n l eq = (n , inr (l , eq))

⊲⇒⊲' : {hs hs' : List Hydra} → Node hs ⊲ Node hs' → hs ⊲' hs'
⊲⇒⊲' (step n (inl l) refl) = step₀ n l refl
⊲⇒⊲' (step n (inr l) refl) = step₁ n l refl

[]-is-minimum : (hs : List Hydra) → ¬(hs ⊲' [])
[]-is-minimum h (step₀ _ l _) = 𝟘-elim (HeadLocation₀-gives-is-non-empty l)
[]-is-minimum h (step₁ _ l _) = 𝟘-elim (HeadLocation₁-gives-is-non-empty l)

⊲-is-well-founded : is-well-founded _⊲_
⊲'-is-well-founded : is-well-founded _⊲'_

⊲-is-well-founded (Node hs) = acc (recurs (⊲'-is-well-founded hs))
 where
  recurs : {hs : List Hydra}
         → is-accessible (_⊲'_) hs
         → (h' : Hydra) → h' ⊲ Node hs
         → is-accessible (_⊲_) h'
  recurs (acc rec₁) (Node hs') r = acc (recurs (rec₁ hs' (⊲⇒⊲' r)))

⊲'-is-well-founded [] = acc (λ h r → 𝟘-elim ([]-is-minimum h r))
⊲'-is-well-founded (h ∷ hs) =
 acc (recurs (⊲-is-well-founded h) (⊲'-is-well-founded hs))
 where
  recurs : {h : Hydra} {hs : List Hydra}
         → is-accessible _⊲_ h
         → is-accessible _⊲'_ hs
         → (hs' : List Hydra) → hs' ⊲' (h ∷ hs)
         → is-accessible _⊲'_ hs'
  recurs (acc rec₁) (acc rec₂) hs' (step₀ n here refl)      = acc rec₂
  recurs (acc rec₁) (acc rec₂) hs' (step₀ n (next l) refl)  =
   acc (recurs (acc rec₁) (rec₂ _ (step₀ n l refl)))
  recurs (acc rec₁) (acc rec₂) hs' (step₁ n (next l) refl)  =
   acc (recurs (acc rec₁) (rec₂ _ (step₁ n l refl)))
  recurs (acc rec₁) (acc rec₂) hs' (step₁ n (here₁ l) refl) =
   acc (recurs (rec₁ _ (step n (inr l) refl)) (acc rec₂))
  recurs (acc rec₁) (acc rec₂) hs' (step₁ n (here₀ l) refl) = recurs' n
   where
    recurs' : (n : ℕ) → is-accessible _⊲'_ (cons-mult _ (succ n) _)
    recurs' 0        = acc (recurs (rec₁ _ (step 0 (inl l) refl)) (acc rec₂))
    recurs' (succ n) = acc (recurs (rec₁ _ (step 0 (inl l) refl)) (recurs' n))

\end{code}

We can now define Hydra(n) and compute its four first terms.

\begin{code}

leftmost-head₀ : (hs : List Hydra) → hs ≠ []
               → HeadLocation₀ hs + HeadLocation₁ hs
leftmost-head₀ []                    neq = 𝟘-elim (neq refl)
leftmost-head₀ (Head ∷ _)            neq = inl here
leftmost-head₀ ((Node (h ∷ hs)) ∷ _) neq =
 leftmost-head₀' (leftmost-head₀ (h ∷ hs) (λ p → []-is-not-cons h hs (p ⁻¹)))
 where
  leftmost-head₀' : HeadLocation₀ (h ∷ hs) + HeadLocation₁ (h ∷ hs)
                  → HeadLocation₀ _ + HeadLocation₁ _
  leftmost-head₀' (inl l) = inr (here₀ l)
  leftmost-head₀' (inr l) = inr (here₁ l)

leftmost-head : (h : Hydra) → h ≠ Head → HeadLocation h
leftmost-head Head            neq = 𝟘-elim (neq refl)
leftmost-head (Node (h ∷ hs)) neq =
 leftmost-head₀ (h ∷ hs) (λ p → []-is-not-cons h hs (p ⁻¹))

f-Hydra : (n : ℕ) → ℕ
f-Hydra n = battle 1 (tall-hydra n) (⊲-is-well-founded _)
 where
  tall-hydra : (n : ℕ) → Hydra
  tall-hydra 0 = Node []
  tall-hydra (succ n) = Node (tall-hydra n ∷ [])

  battle : ℕ → (h : Hydra) → is-accessible _⊲_ h → ℕ
  battle turn Head            (acc rec₁) = 0
  battle turn (Node (h ∷ hs)) (acc rec₁) =
   succ (battle (succ turn) cut-hydra (rec₁ cut-hydra (turn , cut-head , refl)))
   where
    cut-head : HeadLocation (Node (h ∷ hs))
    cut-head = leftmost-head _
                (λ p → []-is-not-cons h hs ((ap heads p) ⁻¹))

    cut-hydra : Hydra
    cut-hydra = cut turn (Node (h ∷ hs)) cut-head

f-Hydra0 : f-Hydra 0 ＝ 0
f-Hydra0 = refl

f-Hydra1 : f-Hydra 1 ＝ 1
f-Hydra1 = refl

f-Hydra2 : f-Hydra 2 ＝ 3
f-Hydra2 = refl

f-Hydra3 : f-Hydra 3 ＝ 37
f-Hydra3 = refl

\end{code}
