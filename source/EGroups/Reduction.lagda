Martin Escardo, July 2026.

The reduction underlying the free egroup on a setoid.

A word over an alphabet A is a list of letters, each an element of A
tagged with a sign that marks whether it is formally inverted, as in
Groups.Free. Two adjacent letters cancel when the second is the
inverse of the first up to the setoid relation _≈_, rather than only
when they are equal. As a consequence the reducts of a word agree only
up to the letter-wise relation _≈[FA]_, so that confluence becomes
confluence modulo _≈_ in the sense of the module ChurchRosserModulo.

We define the reduction relation, prove local confluence and hence,
via that module, the Church-Rosser property, and then adapt the
size-reduction of Groups.Free. The idea there is to keep redexes and
reducts structural, so that the type of generators of a word stays
𝓤-small even when the underlying type A of generators is large. The
type A lives in 𝓤⁺ and its relation _≈_ is valued in 𝓤, as needed for
the universe setoid formed by 𝓤 and type equivalence.

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split #-}

open import MLTT.Spartan

module EGroups.Reduction
        {𝓤 : Universe}
        (A : 𝓤 ⁺ ̇ )
        (_≈_ : A → A → 𝓤 ̇ )
        (≈r : reflexive  _≈_)
        (≈s : symmetric  _≈_)
        (≈t : transitive _≈_)
       where

open import MLTT.Two-Properties
open import MLTT.List renaming (_∷_ to _•_ ; _++_ to _◦_ ; ++-assoc to ◦-assoc)
open import UF.Embeddings
open import UF.Size
open import UF.SmallnessProperties
open import Relations.SRTclosure

\end{code}

The letters and their formal inverse are exactly as in Groups.Free.

\begin{code}

X : 𝓤 ⁺ ̇
X = 𝟚 × A

_⁻ : X → X
(n , a) ⁻ = (complement n , a)

FA : 𝓤 ⁺ ̇
FA = List X

η : A → FA
η a = (₀ , a) • []

\end{code}

We define the relation on letters and extend it to words.

\begin{code}

_≈[X]_ : X → X → 𝓤 ̇
(m , a) ≈[X] (n , b) = (m ＝ n) × (a ≈ b)

≈[X]-refl : (x : X) → x ≈[X] x
≈[X]-refl (m , a) = refl , ≈r a

≈[X]-sym : (x y : X) → x ≈[X] y → y ≈[X] x
≈[X]-sym (m , a) (n , b) (p , q) = (p ⁻¹) , ≈s a b q

≈[X]-trans : (x y z : X) → x ≈[X] y → y ≈[X] z → x ≈[X] z
≈[X]-trans (m , a) (n , b) (k , c) (p , q) (p' , q') = (p ∙ p') , ≈t a b c q q'

⁻-cong : (x y : X) → x ≈[X] y → (x ⁻) ≈[X] (y ⁻)
⁻-cong (m , a) (n , b) (p , q) = ap complement p , q

_≈[FA]_ : FA → FA → 𝓤 ̇
[]      ≈[FA] []      = 𝟙
[]      ≈[FA] (y • t) = 𝟘
(x • s) ≈[FA] []      = 𝟘
(x • s) ≈[FA] (y • t) = (x ≈[X] y) × (s ≈[FA] t)

≈[FA]-refl : (s : FA) → s ≈[FA] s
≈[FA]-refl []      = ⋆
≈[FA]-refl (x • s) = ≈[X]-refl x , ≈[FA]-refl s

≈[FA]-sym : (s t : FA) → s ≈[FA] t → t ≈[FA] s
≈[FA]-sym []      []      ⋆       = ⋆
≈[FA]-sym (x • s) (y • t) (p , q) = ≈[X]-sym x y p , ≈[FA]-sym s t q

≈[FA]-trans : (s t u : FA) → s ≈[FA] t → t ≈[FA] u → s ≈[FA] u
≈[FA]-trans []      []      []      ⋆       ⋆         = ⋆
≈[FA]-trans (x • s) (y • t) (z • u) (p , q) (p' , q') =
 ≈[X]-trans x y z p p' , ≈[FA]-trans s t u q q'

\end{code}

_≈[FA]_ is a congruence for concatenation, and it reflects the list
structure, via cons-split and left-split below, which allows us to
transport a redex along an ≈[FA]-related word.

\begin{code}

◦-cong : (s s' t t' : FA) → s ≈[FA] s' → t ≈[FA] t' → (s ◦ t) ≈[FA] (s' ◦ t')
◦-cong []      []       t t' ⋆        q = q
◦-cong (x • s) (y • s') t t' (p , r)  q = p , ◦-cong s s' t t' r q

cons-split : (a : X) (s w : FA)
           → (a • s) ≈[FA] w
           → Σ b ꞉ X , Σ w₀ ꞉ FA , (w ＝ b • w₀) × (a ≈[X] b) × (s ≈[FA] w₀)
cons-split a s []       ()
cons-split a s (b • w₀) (p , q) = b , w₀ , refl , p , q

left-split : (u v w : FA)
           → (u ◦ v) ≈[FA] w
           → Σ u' ꞉ FA , Σ v' ꞉ FA , (w ＝ u' ◦ v')
                                    × (u ≈[FA] u')
                                    × (v ≈[FA] v')
left-split []       v w p = [] , w , refl , ⋆ , p
left-split (a • u₀) v w p = γ (cons-split a (u₀ ◦ v) w p)
 where
  γ : (Σ b ꞉ X , Σ w₀ ꞉ FA , (w ＝ b • w₀) × (a ≈[X] b) × ((u₀ ◦ v) ≈[FA] w₀))
    → Σ u' ꞉ FA , Σ v' ꞉ FA , (w ＝ u' ◦ v')
                             × ((a • u₀) ≈[FA] u')
                             × (v ≈[FA] v')
  γ (b , w₀ , refl , ab , q) = δ (left-split u₀ v w₀ q)
   where
    δ : (Σ u₀' ꞉ FA , Σ v' ꞉ FA ,
          (w₀ ＝ u₀' ◦ v') × (u₀ ≈[FA] u₀') × (v ≈[FA] v'))
      → Σ u' ꞉ FA , Σ v' ꞉ FA ,
         (b • w₀ ＝ u' ◦ v') × ((a • u₀) ≈[FA] u') × (v ≈[FA] v')
    δ (u₀' , v' , refl , uu , rr) = (b • u₀') , v' , refl , (ab , uu) , rr

\end{code}

We reduce s to t when s has two adjacent letters x and y with y
≈-inverse to x, and t is s with that pair deleted.

\begin{code}

_▷_ : FA → FA → 𝓤 ⁺ ̇
s ▷ t = Σ u ꞉ FA , Σ v ꞉ FA , Σ x ꞉ X , Σ y ꞉ X , (s ＝ u ◦ x • y • v)
                                                × (t ＝ u ◦ v)
                                                × (y ≈[X] (x ⁻))

\end{code}

Coherence of _≈_ with reduction says that an ≈[FA]-equivalent of a
reducible word is reducible to an ≈[FA]-equivalent of its reduct,
which is the second hypothesis of confluence modulo _≈_.

\begin{code}

▷-respects-≈ : (s s' t : FA)
             → s ≈[FA] s'
             → s ▷ t
             → Σ t' ꞉ FA , (s' ▷ t') × (t ≈[FA] t')
▷-respects-≈ s s' t e (u , v , x , y , refl , refl , yx) =
 I (left-split u (x • y • v) s' e)
 where
  I : (Σ u' ꞉ FA , Σ z' ꞉ FA ,
        (s' ＝ u' ◦ z') × (u ≈[FA] u') × ((x • y • v) ≈[FA] z'))
    → Σ t' ꞉ FA , (s' ▷ t') × ((u ◦ v) ≈[FA] t')
  I (u' , z' , refl , uu , exyv) =
   II (cons-split x (y • v) z' exyv)
   where
    II : (Σ x' ꞉ X , Σ w ꞉ FA , (z' ＝ x' • w)
                              × (x ≈[X] x')
                              × ((y • v) ≈[FA] w))
       → Σ t' ꞉ FA , ((u' ◦ z') ▷ t') × ((u ◦ v) ≈[FA] t')
    II (x' , w , refl , xx , eyv) =
     III (cons-split y v w eyv)
     where
      III : (Σ y' ꞉ X , Σ v' ꞉ FA , (w ＝ y' • v')
                                 × (y ≈[X] y')
                                 × (v ≈[FA] v'))
          → Σ t' ꞉ FA , ((u' ◦ x' • w) ▷ t') × ((u ◦ v) ≈[FA] t')
      III (y' , v' , refl , yy , vv) =
       (u' ◦ v') , IV , ◦-cong u u' v v' uu vv
       where
        y'x' : y' ≈[X] (x' ⁻)
        y'x' = ≈[X]-trans y' (x ⁻) (x' ⁻)
                (≈[X]-trans y' y (x ⁻) (≈[X]-sym y y' yy) yx)
                (⁻-cong x x' xx)

        IV : (u' ◦ x' • y' • v') ▷ (u' ◦ v')
        IV = u' , v' , x' , y' , refl , refl , y'x'

\end{code}

We collect some further letter and word algebra used by local
confluence.

\begin{code}

inv-invol : (x : X) → (x ⁻) ⁻ ＝ x
inv-invol (n , a) = ap (_, a) (complement-involutive n)

to-≈[X] : {x y : X} → x ＝ y → x ≈[X] y
to-≈[X] {x} refl = ≈[X]-refl x

to-≈[FA] : {s t : FA} → s ＝ t → s ≈[FA] t
to-≈[FA] {s} refl = ≈[FA]-refl s

•-▷ : (x : X) {s t : FA} → s ▷ t → (x • s) ▷ (x • t)
•-▷ x (u , v , a , b , ps , pt , ba) =
 (x • u) , v , a , b , ap (x •_) ps , ap (x •_) pt , ba

redex-sym : (x y : X) → x ≈[X] (y ⁻) → y ≈[X] (x ⁻)
redex-sym x y c =
 ≈[X]-sym (x ⁻) y
  (≈[X]-trans (x ⁻) ((y ⁻) ⁻) y (⁻-cong x (y ⁻) c) (to-≈[X] (inv-invol y)))

\end{code}

We prove local confluence modulo _≈_, the setoid counterpart of
Lemma[Church-Rosser] of Groups.Free. Two redexes of a common word
either collapse to ≈[FA]-related contractums, when they coincide or
overlap, or have a common reduct, when they are disjoint.

\begin{code}

are-joinable : FA → FA → 𝓤 ⁺ ̇
are-joinable r₀ r₁ = (r₀ ≈[FA] r₁)
                   + (Σ z₀ ꞉ FA , Σ z₁ ꞉ FA , (r₀ ▷ z₀)
                                            × (r₁ ▷ z₁)
                                            × (z₀ ≈[FA] z₁))

Lemma[Church-Rosser≈]
 : (u₀ v₀ u₁ v₁ : FA) (a₀ b₀ a₁ b₁ : X)
 → b₀ ≈[X] (a₀ ⁻)
 → b₁ ≈[X] (a₁ ⁻)
 → u₀ ◦ a₀ • b₀ • v₀ ＝ u₁ ◦ a₁ • b₁ • v₁
 → are-joinable (u₀ ◦ v₀) (u₁ ◦ v₁)
Lemma[Church-Rosser≈] u₀ v₀ u₁ v₁ a₀ b₀ a₁ b₁ cb₀ cb₁ = f u₀ u₁
 where
  f : (u₀ u₁ : FA)
    → u₀ ◦ a₀ • b₀ • v₀ ＝ u₁ ◦ a₁ • b₁ • v₁
    → are-joinable (u₀ ◦ v₀) (u₁ ◦ v₁)

  f [] [] p = inl (to-≈[FA] (equal-tails (equal-tails p)))

  f [] (y₁ • []) p = inl e
   where
    b₁≈y₁ : b₁ ≈[X] y₁
    b₁≈y₁ = ≈[X]-trans b₁ (b₀ ⁻) y₁
             (transport (λ - → b₁ ≈[X] (- ⁻))
               ((equal-heads (equal-tails p)) ⁻¹) cb₁)
             (≈[X]-trans (b₀ ⁻) a₀ y₁
               (≈[X]-sym a₀ (b₀ ⁻) (redex-sym b₀ a₀ cb₀))
               (to-≈[X] (equal-heads p)))

    e : v₀ ≈[FA] (y₁ • v₁)
    e = ≈[FA]-trans v₀ (b₁ • v₁) (y₁ • v₁)
         (to-≈[FA] (equal-tails (equal-tails p)))
         (b₁≈y₁ , ≈[FA]-refl v₁)

  f [] (y₁ • z₁ • u₁) p =
   inr ((u₁ ◦ v₁) , (u₁ ◦ v₁) , d , e , ≈[FA]-refl (u₁ ◦ v₁))
   where
    d : v₀ ▷ (u₁ ◦ v₁)
    d = transport (_▷ (u₁ ◦ v₁)) ((equal-tails (equal-tails p)) ⁻¹)
         (u₁ , v₁ , a₁ , b₁ , refl , refl , cb₁)

    z₁y₁ : z₁ ≈[X] (y₁ ⁻)
    z₁y₁ = transport (λ - → z₁ ≈[X] (- ⁻)) (equal-heads p)
            (transport (λ - → - ≈[X] (a₀ ⁻)) (equal-heads (equal-tails p)) cb₀)

    e : (y₁ • z₁ • (u₁ ◦ v₁)) ▷ (u₁ ◦ v₁)
    e = [] , (u₁ ◦ v₁) , y₁ , z₁ , refl , refl , z₁y₁

  f (y₀ • []) [] p = inl e
   where
    y₀≈b₀ : y₀ ≈[X] b₀
    y₀≈b₀ = ≈[X]-trans y₀ a₁ b₀
             (to-≈[X] (equal-heads p))
             (≈[X]-trans a₁ (a₀ ⁻) b₀
               (≈[X]-trans a₁ (b₁ ⁻) (a₀ ⁻)
                 (redex-sym b₁ a₁ cb₁)
                 (to-≈[X] (ap (_⁻) ((equal-heads (equal-tails p)) ⁻¹))))
               (≈[X]-sym b₀ (a₀ ⁻) cb₀))

    e : (y₀ • v₀) ≈[FA] v₁
    e = ≈[FA]-trans (y₀ • v₀) (b₀ • v₀) v₁
         (y₀≈b₀ , ≈[FA]-refl v₀)
         (to-≈[FA] (equal-tails (equal-tails p)))

  f (y₀ • z₀ • u₀) [] p =
   inr ((u₀ ◦ v₀) , (u₀ ◦ v₀) , d , e , ≈[FA]-refl (u₀ ◦ v₀))
   where
    z₀y₀ : z₀ ≈[X] (y₀ ⁻)
    z₀y₀ = transport (λ - → z₀ ≈[X] (- ⁻)) ((equal-heads p) ⁻¹)
            (transport (λ - → - ≈[X] (a₁ ⁻))
              ((equal-heads (equal-tails p)) ⁻¹) cb₁)

    d : (y₀ • z₀ • (u₀ ◦ v₀)) ▷ (u₀ ◦ v₀)
    d = [] , (u₀ ◦ v₀) , y₀ , z₀ , refl , refl , z₀y₀

    e : v₁ ▷ (u₀ ◦ v₀)
    e = transport (_▷ (u₀ ◦ v₀)) (equal-tails (equal-tails p))
         (u₀ , v₀ , a₀ , b₀ , refl , refl , cb₀)

  f (y₀ • u₀) (y₁ • u₁) p = g (f u₀ u₁ (equal-tails p))
   where
    g : are-joinable (u₀ ◦ v₀) (u₁ ◦ v₁)
      → are-joinable (y₀ • (u₀ ◦ v₀)) (y₁ • (u₁ ◦ v₁))
    g (inl e) = inl (to-≈[X] (equal-heads p) , e)
    g (inr (z₀ , z₁ , d₀ , d₁ , ez)) =
     inr ((y₀ • z₀) , (y₁ • z₁) ,
          •-▷ y₀ d₀ , •-▷ y₁ d₁ , (to-≈[X] (equal-heads p) , ez))

\end{code}

We repackage this as the local-confluence hypothesis of the module
ChurchRosserModulo, on two reductions of a common word.

\begin{code}

Theorem[Church-Rosser≈]
 : (s t₀ t₁ : FA)
 → s ▷ t₀
 → s ▷ t₁
 → (t₀ ≈[FA] t₁)
 + (Σ z₀ ꞉ FA , Σ z₁ ꞉ FA , (t₀ ▷ z₀) × (t₁ ▷ z₁) × (z₀ ≈[FA] z₁))
Theorem[Church-Rosser≈] s t₀ t₁ (u₀ , v₀ , a₀ , b₀ , p₀ , q₀ , cb₀)
                                (u₁ , v₁ , a₁ , b₁ , p₁ , q₁ , cb₁) = γ δ
 where
  δ : are-joinable (u₀ ◦ v₀) (u₁ ◦ v₁)
  δ = Lemma[Church-Rosser≈] u₀ v₀ u₁ v₁ a₀ b₀ a₁ b₁ cb₀ cb₁
       (u₀ ◦ a₀ • b₀ • v₀ ＝⟨ p₀ ⁻¹ ⟩
        s                 ＝⟨ p₁ ⟩
        u₁ ◦ a₁ • b₁ • v₁ ∎)

  γ : are-joinable (u₀ ◦ v₀) (u₁ ◦ v₁)
    → (t₀ ≈[FA] t₁)
    + (Σ z₀ ꞉ FA , Σ z₁ ꞉ FA , (t₀ ▷ z₀) × (t₁ ▷ z₁) × (z₀ ≈[FA] z₁))
  γ (inl e) = inl (≈[FA]-trans t₀ (u₀ ◦ v₀) t₁
                    (to-≈[FA] q₀)
                    (≈[FA]-trans (u₀ ◦ v₀) (u₁ ◦ v₁) t₁ e (to-≈[FA] (q₁ ⁻¹))))
  γ (inr (z₀ , z₁ , d₀ , d₁ , ez)) =
   inr (z₀ , z₁ ,
        transport (_▷ z₀) (q₀ ⁻¹) d₀ ,
        transport (_▷ z₁) (q₁ ⁻¹) d₁ ,
        ez)

\end{code}

Instantiating the module ChurchRosserModulo with the reduction and the
two hypotheses just proved gives the setoid Church-Rosser property
and its consequence for generators.

\begin{code}

open import EGroups.ChurchRosserModulo
             _▷_ _≈[FA]_ ≈[FA]-refl ≈[FA]-sym ≈[FA]-trans public

Church-Rosser≈
 : (s t : FA)
 → s ∿ t
 → Σ z₀ ꞉ FA , Σ z₁ ꞉ FA , (s ▷⋆ z₀) × (t ▷⋆ z₁) × (z₀ ≈[FA] z₁)
Church-Rosser≈ = Church-Rosser-modulo Theorem[Church-Rosser≈] ▷-respects-≈

η-irreducible : (a : A) → does-not-reduce (η a)
η-irreducible a z ([]           , v , x , y , p , q , c) =
 []-is-not-cons y v                (equal-tails p)
η-irreducible a z ((w • [])     , v , x , y , p , q , c) =
 []-is-not-cons x (y • v)          (equal-tails p)
η-irreducible a z ((w • w₀ • u) , v , x , y , p , q , c) =
 []-is-not-cons w₀ (u ◦ x • y • v) (equal-tails p)

η-identifies-∿-related-points : (a b : A) → η a ∿ η b → η a ≈[FA] η b
η-identifies-∿-related-points a b =
 irreducibles-related-by-∿-are-≈ Theorem[Church-Rosser≈] ▷-respects-≈
  (η a) (η b) (η-irreducible a) (η-irreducible b)

\end{code}

We adapt the size-reduction of Groups.Free to the setoid reduction.

\begin{code}

redex : FA → 𝓤 ̇
redex []          = 𝟘
redex (x • [])    = 𝟘
redex (x • y • s) = (y ≈[X] (x ⁻)) + redex (y • s)

reduct : (s : FA) → redex s → FA
reduct (x • y • s) (inl p) = s
reduct (x • y • s) (inr r) = x • reduct (y • s) r

reduct-gives-▷ : (s : FA) (r : redex s) → s ▷ reduct s r
reduct-gives-▷ (x • y • s) (inl c) = [] , s , x , y , refl , refl , c
reduct-gives-▷ (x • y • s) (inr r) = •-▷ x (reduct-gives-▷ (y • s) r)

redex-chain : ℕ → FA → 𝓤 ̇
redex-chain 0        s = 𝟙
redex-chain (succ n) s = Σ r ꞉ redex s , redex-chain n (reduct s r)

chain-reduct : (s : FA) (n : ℕ) → redex-chain n s → FA
chain-reduct s 0        ρ       = s
chain-reduct s (succ n) (r , ρ) = chain-reduct (reduct s r) n ρ

chain-lemma→ : (s : FA) (n : ℕ) (ρ : redex-chain n s)
             → iteration _▷_ n s (chain-reduct s n ρ)
chain-lemma→ s 0        ρ       = refl
chain-lemma→ s (succ n) (r , ρ) = reduct s r ,
                                  reduct-gives-▷ s r ,
                                  chain-lemma→ (reduct s r) n ρ

\end{code}

The following also mimics the development of Groups.Free.

\begin{code}

_◗_ : FA → FA → 𝓤 ⁺ ̇
[]          ◗ t = 𝟘
(x • [])    ◗ t = 𝟘
(x • y • s) ◗ t = (y ≈[X] (x ⁻)) × (s ＝ t)

_▶_ : FA → FA → 𝓤 ⁺ ̇
[]      ▶ t       = 𝟘
(x • s) ▶ []      = (x • s) ◗ []
(x • s) ▶ (y • t) = ((x • s) ◗ (y • t)) + ((x ＝ y) × (s ▶ t))

▷-gives-▶ : {s t : FA} → s ▷ t → s ▶ t
▷-gives-▶ (u , v , x , y , refl , refl , c) = f u v x y c
 where
  f : (u v : FA) (x y : X) → y ≈[X] (x ⁻) → (u ◦ x • y • v) ▶ (u ◦ v)
  f []      []      x y c = c , refl
  f []      (z • v) x y c = inl (c , refl)
  f (w • u) v       x y c = inr (refl , f u v x y c)

lemma-reduct← : (s t : FA) → s ▶ t → Σ r ꞉ redex s , reduct s r ＝ t
lemma-reduct← []          t       ()
lemma-reduct← (x • [])    []      ()
lemma-reduct← (x • [])    (z • t) (inl ())
lemma-reduct← (x • [])    (z • t) (inr (p , ()))
lemma-reduct← (x • y • s) []      (p , q)       = inl p , q
lemma-reduct← (x • y • s) (z • t) (inl (p , q)) = inl p , q
lemma-reduct← (x • y • s) (z • t) (inr (p , r)) =
 inr (pr₁ IH) , (ap (x •_) (pr₂ IH) ∙ ap (_• t) p)
 where
  IH : Σ r ꞉ redex (y • s) , reduct (y • s) r ＝ t
  IH = lemma-reduct← (y • s) t r

▷-gives-redex : (s t : FA) → s ▷ t → Σ r ꞉ redex s , reduct s r ＝ t
▷-gives-redex s t d = lemma-reduct← s t (▷-gives-▶ d)

chain-lemma← : (s t : FA) (n : ℕ)
             → iteration _▷_ n s t
             → Σ ρ ꞉ redex-chain n s , chain-reduct s n ρ ＝ t
chain-lemma← s t 0        r           = ⋆ , r
chain-lemma← s t (succ n) (z , b , c) = γ (▷-gives-redex s z b)
 where
  γ : (Σ r ꞉ redex s , reduct s r ＝ z)
    → Σ ρ ꞉ redex-chain (succ n) s , chain-reduct s (succ n) ρ ＝ t
  γ (r , refl) = δ (chain-lemma← (reduct s r) t n c)
   where
    δ : (Σ ρ ꞉ redex-chain n (reduct s r) , chain-reduct (reduct s r) n ρ ＝ t)
      → Σ ρ ꞉ redex-chain (succ n) s , chain-reduct s (succ n) ρ ＝ t
    δ (ρ , q) = (r , ρ) , q

generator : FA → 𝓤 ⁺ ̇
generator s = Σ n ꞉ ℕ , Σ ρ ꞉ redex-chain n s , fiber η (chain-reduct s n ρ)

underlying-generator : {s : FA} → generator s → A
underlying-generator (n , ρ , a , p) = a

\end{code}

Unlike in Groups.Free, we don't assume that A is a set, and, like in
Groups.Free, we don't assume decidable equality on it. But η is the
composite of pairing with the sign ₀ and the formation of a singleton
list, and hence a decidable embedding, so that its fibers have any
size, which is what keeps generator s small when A is large.

\begin{code}

η-is-embedding : is-embedding η
η-is-embedding = ∘-is-embedding pair₀-is-embedding []-is-embedding

η-is-decidable : each-fiber-of η is-decidable
η-is-decidable = ∘-decidable-embeddings []-is-embedding
                  pair₀-is-decidable []-is-decidable

η-has-any-size : (𝓦 : Universe) → η is 𝓦 small-map
η-has-any-size 𝓦 = decidable-embeddings-have-any-size 𝓦
                    η-is-embedding η-is-decidable

generator-is-small : (s : FA) → generator s is 𝓤 small
generator-is-small s =
 Σ-is-small
  (native-size ℕ)
  (λ n → Σ-is-small
          (native-size (redex-chain n s))
          (λ ρ → η-has-any-size 𝓤 (chain-reduct s n ρ)))

\end{code}

An ≈[FA]-equivalent of a generator is again a generator, up to _≈_.
This is the setoid replacement for the injectivity of η after quotienting.

\begin{code}

≈[FA]-η→ : {a : A} (z : FA) → η a ≈[FA] z → Σ c ꞉ A , (z ＝ η c) × (c ≈ a)
≈[FA]-η→ []                ()
≈[FA]-η→ ((m , c) • [])      ((p , q) , ⋆) =
 c , ap (λ n → (n , c) • []) (p ⁻¹) , ≈s _ c q
≈[FA]-η→ ((m , c) • (x • t)) (_ , ())

\end{code}

If η a is convertible to s, then s is a generator whose underlying
element is equivalent to a. This uses the setoid Church-Rosser
property and the irreducibility of η a.

\begin{code}

∿→generator⁺ : {a : A} {s : FA}
             → η a ∿ s
             → Σ γ ꞉ generator s , (underlying-generator γ ≈ a)
∿→generator⁺ {a} {s} e = γ (Church-Rosser≈ (η a) s e)
 where
  γ : (Σ z₀ ꞉ FA , Σ z₁ ꞉ FA , (η a ▷⋆ z₀) × (s ▷⋆ z₁) × (z₀ ≈[FA] z₁))
    → Σ g ꞉ generator s , (underlying-generator g ≈ a)
  γ (z₀ , z₁ , r₀ , r₁ , ez) = δ (≈[FA]-η→ z₁ I₁)
   where
    I₀ : η a ＝ z₀
    I₀ = ▷⋆-from-irreducible (η a) z₀ (η-irreducible a) r₀

    I₁ : η a ≈[FA] z₁
    I₁ = transport (_≈[FA] z₁) (I₀ ⁻¹) ez

    δ : (Σ c ꞉ A , (z₁ ＝ η c) × (c ≈ a))
      → Σ g ꞉ generator s , (underlying-generator g ≈ a)
    δ (c , ezc , eca) = ε (transport (s ▷⋆_) ezc r₁)
     where
      ε : s ▷⋆ (η c) → Σ g ꞉ generator s , (underlying-generator g ≈ a)
      ε (n , it) = ζ (chain-lemma← s (η c) n it)
       where
        ζ : (Σ ρ ꞉ redex-chain n s , chain-reduct s n ρ ＝ η c)
          → Σ g ꞉ generator s , (underlying-generator g ≈ a)
        ζ (ρ , q) = (n , ρ , c , (q ⁻¹)) , eca

∿→generator : {a : A} {s : FA} → η a ∿ s → generator s
∿→generator e = pr₁ (∿→generator⁺ e)

underlying-generator-∿→generator : {a : A} {s : FA} (e : η a ∿ s)
                                 → underlying-generator (∿→generator e) ≈ a
underlying-generator-∿→generator e = pr₂ (∿→generator⁺ e)

◦-▷-left : {s s' : FA} → s ▷ s' → (t : FA) → (s ◦ t) ▷ (s' ◦ t)
◦-▷-left (u , v , x , y , refl , refl , c) t =
 u , (v ◦ t) , x , y , ◦-assoc u (x • y • v) t , ◦-assoc u v t , c

◦-▷-right : (s : FA) {t t' : FA} → t ▷ t' → (s ◦ t) ▷ (s ◦ t')
◦-▷-right s (u , v , x , y , refl , refl , c) =
 (s ◦ u) , v , x , y , ((◦-assoc s u (x • y • v)) ⁻¹) , ((◦-assoc s u v) ⁻¹) , c

\end{code}

Hence convertibility _∿_ is a congruence for concatenation, so _◦_ is
a well-defined operation on the setoid of words up to _∿_, with no
quotient taken. This is the setoid, together with its operation, from
which the free egroup is built in the next module.

\begin{code}

∿-◦-left : {s s' : FA} → s ∿ s' → (t : FA) → (s ◦ t) ∿ (s' ◦ t)
∿-◦-left {s} {s'} e t = srt-induction _▷_ R R-sym R-refl R-trans R-base s s' e
 where
  R : FA → FA → 𝓤 ⁺ ̇
  R p q = (p ◦ t) ∿ (q ◦ t)

  R-refl : reflexive R
  R-refl p = srt-reflexive _▷_ (p ◦ t)

  R-sym : symmetric R
  R-sym p q = srt-symmetric _▷_ (p ◦ t) (q ◦ t)

  R-trans : transitive R
  R-trans p q r = srt-transitive _▷_ (p ◦ t) (q ◦ t) (r ◦ t)

  R-base : _▷_ ⊑ R
  R-base p q d = srt-extension _▷_ (p ◦ t) (q ◦ t) (◦-▷-left d t)

∿-◦-right : (s : FA) {t t' : FA} → t ∿ t' → (s ◦ t) ∿ (s ◦ t')
∿-◦-right s {t} {t'} e = srt-induction _▷_ R R-sym R-refl R-trans R-base t t' e
 where
  R : FA → FA → 𝓤 ⁺ ̇
  R p q = (s ◦ p) ∿ (s ◦ q)

  R-refl : reflexive R
  R-refl p = srt-reflexive _▷_ (s ◦ p)

  R-sym : symmetric R
  R-sym p q = srt-symmetric _▷_ (s ◦ p) (s ◦ q)

  R-trans : transitive R
  R-trans p q r = srt-transitive _▷_ (s ◦ p) (s ◦ q) (s ◦ r)

  R-base : _▷_ ⊑ R
  R-base p q d = srt-extension _▷_ (s ◦ p) (s ◦ q) (◦-▷-right s d)

◦-cong-∿ : {s s' t t' : FA} → s ∿ s' → t ∿ t' → (s ◦ t) ∿ (s' ◦ t')
◦-cong-∿ {s} {s'} {t} {t'} es et =
 srt-transitive _▷_ (s ◦ t) (s' ◦ t) (s' ◦ t') (∿-◦-left es t) (∿-◦-right s' et)

\end{code}
