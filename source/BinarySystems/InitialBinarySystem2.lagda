Martin Escardo, 7th August 2020.

This file improves the file InitialBinarySystem.lagda, which gives the
background for this file.

Modified 2nd May 2025 to remove the requirement that the underlying
types of binary systems are sets, and also to remove some unused
hypotheses. But it is still the case that the initial binary system is
a set.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module BinarySystems.InitialBinarySystem2 where

open import MLTT.Spartan
open import UF.DiscreteAndSeparated
open import UF.Sets
open import UF.Sets-Properties

data 𝔹 :  𝓤₀ ̇ where
 center : 𝔹
 left   : 𝔹 → 𝔹
 right  : 𝔹 → 𝔹

data 𝕄 : 𝓤₀ ̇ where
 L : 𝕄
 R : 𝕄
 η : 𝔹 → 𝕄

pattern C = η center

l : 𝕄 → 𝕄
l L     = L
l R     = C
l (η x) = η (left x)

r : 𝕄 → 𝕄
r L     = C
r R     = R
r (η x) = η (right x)

𝕄-eq-l : L ＝ l L
𝕄-eq-l = refl

𝕄-eq-r : R ＝ r R
𝕄-eq-r = refl

𝕄-eq-lr : l R ＝ r L
𝕄-eq-lr = refl

\end{code}

We now show that 𝕄 is a set.

\begin{code}

left-lc : (x y : 𝔹) → left x ＝ left y → x ＝ y
left-lc x x refl = refl

right-lc : (x y : 𝔹) → right x ＝ right y → x ＝ y
right-lc x x refl = refl

𝔹-is-discrete : (x y : 𝔹) → (x ＝ y) + (x ≠ y)
𝔹-is-discrete center   center     = inl refl
𝔹-is-discrete center   (left y)   = inr (λ ())
𝔹-is-discrete center   (right y)  = inr (λ ())
𝔹-is-discrete (left x) center     = inr (λ ())
𝔹-is-discrete (left x) (left y)   =
 Cases (𝔹-is-discrete x y)
  (λ (p : x ＝ y) → inl (ap left p))
  (λ (ν : x ≠ y) → inr (contrapositive (left-lc x y) ν))
𝔹-is-discrete (left x)  (right y) = inr (λ ())
𝔹-is-discrete (right x) center    = inr (λ ())
𝔹-is-discrete (right x) (left y)  = inr (λ ())
𝔹-is-discrete (right x) (right y) =
 Cases (𝔹-is-discrete x y)
  (λ (p : x ＝ y) → inl (ap right p))
  (λ (ν : x ≠ y) → inr (contrapositive (right-lc x y) ν))
η-lc : (x y : 𝔹) → η x ＝ η y → x ＝ y
η-lc x x refl = refl

𝕄-is-discrete : (x y : 𝕄) → (x ＝ y) + (x ≠ y)
𝕄-is-discrete L     L     = inl refl
𝕄-is-discrete L     R     = inr (λ ())
𝕄-is-discrete L     (η x) = inr (λ ())
𝕄-is-discrete R     L     = inr (λ ())
𝕄-is-discrete R     R     = inl refl
𝕄-is-discrete R     (η x) = inr (λ ())
𝕄-is-discrete (η x) L     = inr (λ ())
𝕄-is-discrete (η x) R     = inr (λ ())
𝕄-is-discrete (η x) (η y) = Cases (𝔹-is-discrete x y)
                              (λ (p : x ＝ y) → inl (ap η p))
                              (λ (ν : x ≠ y) → inr (contrapositive (η-lc x y) ν))

𝕄-is-set : is-set 𝕄
𝕄-is-set = discrete-types-are-sets 𝕄-is-discrete

\end{code}

It turns out that we don't need to know that 𝕄 is a set. But it is
interesting to know that the initial binary system is a set, even
though we don't require the underlying types of binary systems to be
sets.

We now prove a general induction principle for 𝕄 and a particular case
of interest.

\begin{code}

open import UF.Subsingletons hiding (center)

𝕄-induction : (P : 𝕄 → 𝓤 ̇ )
            → (a : P L)
            → (b : P R)
            → (f : (x : 𝕄) → P x → P (l x))
            → (g : (x : 𝕄) → P x → P (r x))
            → (x : 𝕄) → P x
𝕄-induction P a b f g L             = a
𝕄-induction P a b f g R             = b
𝕄-induction P a b f g C             = f R b -- (*)
𝕄-induction P a b f g (η (left x))  = f (η x) (𝕄-induction P a b f g (η x))
𝕄-induction P a b f g (η (right x)) = g (η x) (𝕄-induction P a b f g (η x))

\end{code}

(*) Alternatively, here we can take g L a, but then the proofs below
change.

In MLTT, induction principles come with equations. In our case they
are the expected ones.

\begin{code}

𝕄-inductive : (P : 𝕄 → 𝓤 ̇ )
             → P L
             → P R
             → ((x : 𝕄) → P x → P (l x))
             → ((x : 𝕄) → P x → P (r x))
             → 𝓤 ̇
𝕄-inductive P a b f g = (a ＝ f L a)
                      × (f R b ＝ g L a)
                      × (b ＝ g R b)

𝕄-induction-L
  : (P : 𝕄 → 𝓤 ̇ )
    (a : P L)
    (b : P R)
    (f : (x : 𝕄) → P x → P (l x))
    (g : (x : 𝕄) → P x → P (r x))
    (ι : 𝕄-inductive P a b f g)
  → 𝕄-induction P a b f g L ＝ a
𝕄-induction-L P a b f g _ = refl

𝕄-induction-R
  : (P : 𝕄 → 𝓤 ̇ )
    (a : P L)
    (b : P R)
    (f : (x : 𝕄) → P x → P (l x))
    (g : (x : 𝕄) → P x → P (r x))
    (ι : 𝕄-inductive P a b f g)
   → 𝕄-induction P a b f g R ＝ b
𝕄-induction-R P a b f g _ = refl

\end{code}

For the next equation for the induction principle, we need the
assumption a ＝ f L a:

\begin{code}

𝕄-induction-l
  : (P : 𝕄 → 𝓤 ̇ )
    (a : P L)
    (b : P R)
    (f : (x : 𝕄) → P x → P (l x))
    (g : (x : 𝕄) → P x → P (r x))
  → (ι : 𝕄-inductive P a b f g)
  → (x : 𝕄) → 𝕄-induction P a b f g (l x) ＝ f x (𝕄-induction P a b f g x)
𝕄-induction-l P a b f g ι L     = pr₁ ι
𝕄-induction-l P a b f g ι R     = refl
𝕄-induction-l P a b f g ι (η x) = refl

\end{code}

And for the last equation for the induction principle, we need the two
equations f R b ＝ g L a and b ＝ g R b as assumptions:

\begin{code}

𝕄-induction-r
  : (P : 𝕄 → 𝓤 ̇ )
    (a : P L)
    (b : P R)
    (f : (x : 𝕄) → P x → P (l x))
    (g : (x : 𝕄) → P x → P (r x))
  → (ι : 𝕄-inductive P a b f g)
  → (x : 𝕄) → 𝕄-induction P a b f g (r x) ＝ g x (𝕄-induction P a b f g x)
𝕄-induction-r P a b f g ι L     = pr₁ (pr₂ ι)
𝕄-induction-r P a b f g ι R     = pr₂ (pr₂ ι)
𝕄-induction-r P a b f g ι (η x) = refl

\end{code}

We now give 𝕄 the structure of a binary system.

\begin{code}

binary-system-structure : 𝓤 ̇ → 𝓤 ̇
binary-system-structure A = A × A × (A → A) × (A → A)

binary-system-axioms : (A : 𝓤 ̇ ) → binary-system-structure A → 𝓤 ̇
binary-system-axioms A (a , b , f , g) = (a ＝ f a)
                                       × (f b ＝ g a)
                                       × (b ＝ g b)

BS : (𝓤 : Universe) → 𝓤 ⁺ ̇
BS 𝓤 = Σ A ꞉ 𝓤 ̇ , Σ s ꞉ binary-system-structure A , binary-system-axioms A s

𝓜 : BS 𝓤₀
𝓜 = (𝕄 , (L , R , l , r) , (𝕄-eq-l , 𝕄-eq-lr , 𝕄-eq-r))

open import UF.SIP
open sip

is-hom : (𝓐 : BS 𝓤) (𝓐' : BS 𝓥) → (⟨ 𝓐 ⟩ → ⟨ 𝓐' ⟩) → 𝓤 ⊔ 𝓥 ̇
is-hom (A , (a , b , f , g) , _) (A' , (a' , b' , f' , g') , _) h =
   (h a ＝ a')
 × (h b ＝ b')
 × (h ∘ f ∼ f' ∘ h)
 × (h ∘ g ∼ g' ∘ h)

\end{code}

As usual, the recursion principle is a particular case of the
induction principle:

\begin{code}

𝓜-rec : (𝓐 : BS 𝓤) → (𝕄 → ⟨ 𝓐 ⟩)
𝓜-rec (A , (a , b , f , g) , _) =
 𝕄-induction (λ _ → A) a b (λ _ → f) (λ _ → g)

\end{code}

And so are its equations, which amount to the fact that 𝓜-rec
constructs a homomorphism:

\begin{code}

𝓜-rec-is-hom : (𝓐 : BS 𝓤)
              → is-hom 𝓜 𝓐 (𝓜-rec 𝓐)
𝓜-rec-is-hom (A , (a , b , f , g) , ι) = i , ii , iii , iv
 where
  𝓐 = (A , (a , b , f , g) , ι)

  i : 𝓜-rec 𝓐 L ＝ a
  i = refl

  ii : 𝓜-rec 𝓐 R ＝ b
  ii = refl

  iii : (x : 𝕄) → 𝓜-rec 𝓐 (l x) ＝ f (𝓜-rec 𝓐 x)
  iii = 𝕄-induction-l (λ _ → A) a b (λ _ → f) (λ _ → g) ι

  iv : (x : 𝕄) → 𝓜-rec 𝓐 (r x) ＝ g (𝓜-rec 𝓐 x)
  iv = 𝕄-induction-r (λ _ → A) a b (λ _ → f) (λ _ → g) ι

\end{code}

Some boiler plate code to name the projections follows:

\begin{code}

⟨_⟩-L : (𝓐 : BS 𝓤) → ⟨ 𝓐 ⟩
⟨ (A , (a , b , f , g) , ι) ⟩-L = a


⟨_⟩-R : (𝓐 : BS 𝓤) → ⟨ 𝓐 ⟩
⟨ (A , (a , b , f , g) , ι) ⟩-R = b


⟨_⟩-l : (𝓐 : BS 𝓤) → ⟨ 𝓐 ⟩ → ⟨ 𝓐 ⟩
⟨ (A , (a , b , f , g) , ι) ⟩-l = f


⟨_⟩-r : (𝓐 : BS 𝓤) → ⟨ 𝓐 ⟩ → ⟨ 𝓐 ⟩
⟨ (A , (a , b , f , g) , ι) ⟩-r = g

is-hom-L : (𝓐 : BS 𝓤) (𝓑 : BS 𝓥) (h : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
            → is-hom 𝓐 𝓑 h → h (⟨ 𝓐 ⟩-L) ＝ ⟨ 𝓑 ⟩-L
is-hom-L 𝓐 𝓑 h (i , ii , iii , iv) = i


is-hom-R : (𝓐 : BS 𝓤) (𝓑 : BS 𝓥) (h : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
             → is-hom 𝓐 𝓑 h → h (⟨ 𝓐 ⟩-R) ＝ ⟨ 𝓑 ⟩-R
is-hom-R 𝓐 𝓑 h (i , ii , iii , iv) = ii


is-hom-l : (𝓐 : BS 𝓤) (𝓑 : BS 𝓥) (h : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
            → is-hom 𝓐 𝓑 h → h ∘ ⟨ 𝓐 ⟩-l ∼ ⟨ 𝓑 ⟩-l ∘ h
is-hom-l 𝓐 𝓑 h (i , ii , iii , iv) = iii


is-hom-r : (𝓐 : BS 𝓤) (𝓑 : BS 𝓥) (h : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
             → is-hom 𝓐 𝓑 h → h ∘ ⟨ 𝓐 ⟩-r ∼ ⟨ 𝓑 ⟩-r ∘ h
is-hom-r 𝓐 𝓑 h (i , ii , iii , iv) = iv

\end{code}

This is the end of the boiler plate code.

To conclude that 𝓜 is the initial binary system, it remains to prove
that there is at most one homomorphism from it to any other binary
system.

\begin{code}

𝓜-at-most-one-hom : (𝓐 : BS 𝓤) (h k : 𝕄 → ⟨ 𝓐 ⟩)
                 → is-hom 𝓜 𝓐 h
                 → is-hom 𝓜 𝓐 k
                 → h ∼ k
𝓜-at-most-one-hom 𝓐 h k u v = 𝕄-induction (λ x → h x ＝ k x) α β ϕ γ
 where
  α = h L      ＝⟨ is-hom-L 𝓜 𝓐 h u ⟩
      ⟨ 𝓐 ⟩-L  ＝⟨ (is-hom-L 𝓜 𝓐 k v)⁻¹ ⟩
      k L ∎

  β = h R      ＝⟨ is-hom-R 𝓜 𝓐 h u ⟩
      ⟨ 𝓐 ⟩-R  ＝⟨ (is-hom-R 𝓜 𝓐 k v)⁻¹ ⟩
      k R ∎

  ϕ : (x : 𝕄) → h x ＝ k x → h (l x) ＝ k (l x)
  ϕ x p = h (l x)       ＝⟨ is-hom-l 𝓜 𝓐 h u x ⟩
          ⟨ 𝓐 ⟩-l (h x) ＝⟨ ap ⟨ 𝓐 ⟩-l p ⟩
          ⟨ 𝓐 ⟩-l (k x) ＝⟨ (is-hom-l 𝓜 𝓐 k v x)⁻¹ ⟩
          k (l x)       ∎

  γ : (x : 𝕄) → h x ＝ k x → h (r x) ＝ k (r x)
  γ x p =  h (r x)       ＝⟨ is-hom-r 𝓜 𝓐 h u x ⟩
           ⟨ 𝓐 ⟩-r (h x) ＝⟨ ap ⟨ 𝓐 ⟩-r p ⟩
           ⟨ 𝓐 ⟩-r (k x) ＝⟨ (is-hom-r 𝓜 𝓐 k v x)⁻¹ ⟩
           k (r x)       ∎

𝓜-rec-unique : (𝓐 : BS 𝓤) (h : 𝕄 → ⟨ 𝓐 ⟩)
             → is-hom 𝓜 𝓐 h
             → h ∼ 𝓜-rec 𝓐
𝓜-rec-unique 𝓐 h u = 𝓜-at-most-one-hom 𝓐 h (𝓜-rec 𝓐) u (𝓜-rec-is-hom 𝓐)

\end{code}

TODO. Now that we have removed the sethood requirement for the
underlying type of a binary system we need to prove unique existence
as contractibility (as done for nno's in the MGS'2019 lecture notes).

Primitive (or parametric) recursion, which has the above as a special
case:

\begin{code}

𝕄-primrec : {A : 𝓤 ̇ } (a b : A) (f g : 𝕄 → A → A) → 𝕄 → A
𝕄-primrec {𝓤} {A} a b f = 𝕄-induction (λ _ → A) a b f

primitive-recursive : {A : 𝓤 ̇ } → A → A → (𝕄 → A → A) → (𝕄 → A → A) → (𝕄 → A) → 𝓤 ̇
primitive-recursive a b f g h =

         (h L ＝ a)
       × (h R ＝ b)
       × ((x : 𝕄) → h (l x) ＝ f x (h x))
       × ((x : 𝕄) → h (r x) ＝ g x (h x))

𝕄-pinductive : {A : 𝓤 ̇ } → A → A → (𝕄 → A → A) → (𝕄 → A → A) → 𝓤 ̇
𝕄-pinductive {𝓤} {A} a b f g = 𝕄-inductive (λ _ → A) a b f g

𝕄-primrec-primitive-recursive
  : {A : 𝓤 ̇ }
    (a b : A)
    (f g : 𝕄 → A → A)
  → (ι : 𝕄-pinductive a b f g)
  → primitive-recursive a b f g (𝕄-primrec a b f g)
𝕄-primrec-primitive-recursive {𝓤} {A} a b f g ι =
   refl ,
   refl ,
   𝕄-induction-l (λ _ → A) a b f g ι ,
   𝕄-induction-r (λ _ → A) a b f g ι

𝕄-at-most-one-primrec : {A : 𝓤 ̇ }
    (a b : A)
    (f g : 𝕄 → A → A)
  → 𝕄-pinductive a b f g
  → (h k : 𝕄 → A)
  → primitive-recursive a b f g h
  → primitive-recursive a b f g k
  → h ∼ k

𝕄-at-most-one-primrec {𝓤} {A} a b f g (ι₁ , ι')  h k
                       (hL , hR , hl , hr) (kL , kR , kl , kr) = δ
 where
  α = h L ＝⟨ hL ⟩
      a   ＝⟨ kL ⁻¹ ⟩
      k L ∎

  β = h R ＝⟨ hR ⟩
      b   ＝⟨ kR ⁻¹ ⟩
      k R ∎

  ϕ : (x : 𝕄) → h x ＝ k x → h (l x) ＝ k (l x)
  ϕ x p = h (l x)   ＝⟨ hl x ⟩
          f x (h x) ＝⟨ ap (f x) p ⟩
          f x (k x) ＝⟨ (kl x)⁻¹ ⟩
          k (l x)   ∎

  γ : (x : 𝕄) → h x ＝ k x → h (r x) ＝ k (r x)
  γ x p =  h (r x)   ＝⟨ hr x ⟩
           g x (h x) ＝⟨ ap (g x) p ⟩
           g x (k x) ＝⟨ (kr x)⁻¹ ⟩
           k (r x)   ∎

  δ : h ∼ k
  δ = 𝕄-induction (λ x → h x ＝ k x) α β ϕ γ

𝕄-primrec-uniqueness
  : {A : 𝓤 ̇ }
    (a b : A)
    (f g : 𝕄 → A → A)
  → (ι : 𝕄-pinductive a b f g)
  → (h : 𝕄 → A)
  → primitive-recursive a b f g h
  → h ∼ 𝕄-primrec a b f g
𝕄-primrec-uniqueness a b f g ι h hph =
 𝕄-at-most-one-primrec a b f g ι
   h (𝕄-primrec a b f g)
   hph (𝕄-primrec-primitive-recursive a b f g ι)

\end{code}

Under some special conditions that often hold in practice, we can
remove the base case in the uniqueness theorem.

\begin{code}

is-wprimrec : {A : 𝓤 ̇ } → (𝕄 → A → A) → (𝕄 → A → A) → (𝕄 → A) → 𝓤 ̇
is-wprimrec f g h = ((x : 𝕄) → h (l x) ＝ f x (h x))
                  × ((x : 𝕄) → h (r x) ＝ g x (h x))


primrec-is-wprimrec : {A : 𝓤 ̇ } (a b : A) (f g : 𝕄 → A → A) (h : 𝕄 → A)
                    → primitive-recursive a b f g h → is-wprimrec f g h
primrec-is-wprimrec a b f g h (hL , hR , hl , hr) = (hl , hr)


fixed-point-conditions : {A : 𝓤 ̇ } → A → A → (𝕄 → A → A) → (𝕄 → A → A) → 𝓤 ̇
fixed-point-conditions a b f g = (∀ a' → a' ＝ f L a' → a' ＝ a)
                               × (∀ b' → b' ＝ g R b' → b' ＝ b)

wprimrec-primitive-recursive
 : {A : 𝓤 ̇ }
   (a b : A)
   (f g : 𝕄 → A → A)
   (h : 𝕄 → A)
 → fixed-point-conditions a b f g
 → is-wprimrec f g h
 → primitive-recursive a b f g h
wprimrec-primitive-recursive a b f g h (fixa , fixb) (hl , hr)
 = (hL , hR , hl , hr)
 where
  hL' = h L       ＝⟨refl⟩
        h (l L)   ＝⟨ hl L ⟩
        f L (h L) ∎

  hL = h L ＝⟨ fixa (h L) hL' ⟩
       a   ∎

  hR : h R ＝ b
  hR = fixb (h R) (hr R)

𝕄-at-most-one-wprimrec
  : {A : 𝓤 ̇ }
    (a b : A)
    (f g : 𝕄 → A → A)
  → (ι : 𝕄-pinductive a b f g)
  → fixed-point-conditions a b f g
  → (h k : 𝕄 → A)
  → is-wprimrec f g h
  → is-wprimrec f g k
  → h ∼ k
𝕄-at-most-one-wprimrec a b f g ι fixc h k (hl , hr) (kl , kr) =
  𝕄-at-most-one-primrec a b f g ι h k
    (wprimrec-primitive-recursive a b f g h fixc (hl , hr))
    (wprimrec-primitive-recursive a b f g k fixc (kl , kr))

𝕄-wprimrec-uniqueness
 : {A : 𝓤 ̇ }
   (a b : A)
   (f g : 𝕄 → A → A)
  → (ι : 𝕄-pinductive a b f g)
  → fixed-point-conditions a b f g
  → (h : 𝕄 → A)
  → is-wprimrec f g h
  → h ∼ 𝕄-primrec a b f g
𝕄-wprimrec-uniqueness a b f g ι fixc h hph =
  𝕄-at-most-one-wprimrec a b f g ι fixc h
   (𝕄-primrec a b f g) hph
   (primrec-is-wprimrec a b f g
     ( 𝕄-primrec a b f g)
     (𝕄-primrec-primitive-recursive a b f g ι))

\end{code}

Definition by cases of functions 𝕄 → A is a particular case of
parametric recursion.

Given a b : A and f g : 𝕄 → A, we want to define h : 𝕄 → A by cases as
follows:

      h L     = a
      h R     = b
      h (l x) = f x
      h (r x) = g x

For this to be well defined we need the following endpoint agreement
conditions:

  (1) a ＝ f L,
  (2) f R ＝ g L,
  (3) b ＝ g R.

If we take a = f L and b = g L, so that (1) and (3) hold, we are left
with condition (2) as the only assumption, and the condition on h
becomes

      h L     = f L,
      h R     = g R,
      h (l x) = f x,
      h (r x) = g x.

But also the first two equations follow from the second two, since

     h L = h (l L) = f L,
     h R = h (r R) = g r.

Hence it is enough to consider the endpoint agreement condition (2)
and work with the equations

      h (l x) = f x,
      h (r x) = g x.

Hence the function 𝕄-cases defined belowgives the mediating map of a
pushout diagram that glues two copies of the dyadic interval,
identifying the end of one with the beginning of the other, so that 𝕄
is equivalent to the pushout 𝕄 +₁ 𝕄:

      𝕄 ≃ 𝕄 +₁ 𝕄

when f = l and g = r.

The following constructions and facts are all particular cases of
those for 𝕄-primrec.

\begin{code}

𝕄-caseable : (A : 𝓤 ̇ ) → (𝕄 → A) → (𝕄 → A) → 𝓤 ̇
𝕄-caseable A f g = (f R ＝ g L)

𝕄-caseable-gives-pinductive
 : (A : 𝓤 ̇ )
   (f g : 𝕄 → A)
  → 𝕄-caseable A f g
  → 𝕄-pinductive (f L) (g R) (λ x _ → f x) (λ x _ → g x)
𝕄-caseable-gives-pinductive A f g p
 = refl , p , refl

𝕄-cases : {A : 𝓤 ̇ } (f g : 𝕄 → A) → 𝕄-caseable A f g → 𝕄 → A
𝕄-cases f g ι = 𝕄-primrec (f L) (g R) (λ x _ → f x) (λ x _ → g x)

case-equations : {A : 𝓤 ̇ } → (𝕄 → A) → (𝕄 → A) → (𝕄 → A) → 𝓤 ̇
case-equations f g h = (h ∘ l ∼ f)
                     × (h ∘ r ∼ g)

𝕄-cases-redundant-equations
  : {A : 𝓤 ̇ }
    (f g : 𝕄 → A)
  → (p : 𝕄-caseable A f g)
  → (𝕄-cases f g p L   ＝ f L)
  × (𝕄-cases f g p R   ＝ g R)
  × (𝕄-cases f g p ∘ l ∼ f)
  × (𝕄-cases f g p ∘ r ∼ g)
𝕄-cases-redundant-equations f g ι
  = 𝕄-primrec-primitive-recursive
     (f L) (g R)
     (λ x _ → f x) (λ x _ → g x)
     (𝕄-caseable-gives-pinductive _ f g ι)

𝕄-cases-equations
  : {A : 𝓤 ̇ }
    (f g : 𝕄 → A)
  → (p : 𝕄-caseable A f g)
  → case-equations f g (𝕄-cases f g p)
𝕄-cases-equations f g p
  = primrec-is-wprimrec
     (f L) (g R)
     (λ x _ → f x) (λ x _ → g x)
     (𝕄-cases f g p)
     (𝕄-cases-redundant-equations f g p)

𝕄-at-most-one-cases
 : {A : 𝓤 ̇ }
   (f g : 𝕄 → A)
  → 𝕄-caseable A f g
  → (h k : 𝕄 → A)
  → case-equations f g h
  → case-equations f g k
  → h ∼ k
𝕄-at-most-one-cases f g ι
  = 𝕄-at-most-one-wprimrec
     (f L) (g R)
     (λ x _ → f x) (λ x _ → g x)
     (𝕄-caseable-gives-pinductive _ f g ι)
     (u , v)
  where
   u : ∀ a' → a' ＝ f L → a' ＝ f L
   u a' p = p

   v : ∀ b' → b' ＝ g R → b' ＝ g R
   v a' p = p

𝕄-cases-uniqueness
  : {A : 𝓤 ̇ }
    (f g : 𝕄 → A)
  → (p : 𝕄-caseable A f g)
  → (h : 𝕄 → A)
  → case-equations f g h
  → h ∼ 𝕄-cases f g p
𝕄-cases-uniqueness f g p h he
  = 𝕄-at-most-one-cases f g p h
     (𝕄-cases f g p) he (𝕄-cases-equations f g p)

𝕄-cases-L : {A : 𝓤 ̇ } (f g : 𝕄 → A) (p : 𝕄-caseable A f g)
          → 𝕄-cases f g p L ＝ f L
𝕄-cases-L f g p = refl

𝕄-cases-R : {A : 𝓤 ̇ } (f g : 𝕄 → A) (p : 𝕄-caseable A f g)
          → 𝕄-cases f g p R ＝ g R
𝕄-cases-R f g p = refl

𝕄-cases-l : {A : 𝓤 ̇ } (f g : 𝕄 → A) (p : 𝕄-caseable A f g)
          → 𝕄-cases f g p ∘ l ∼ f
𝕄-cases-l f g p = pr₁ (𝕄-cases-equations f g p)

𝕄-cases-r : {A : 𝓤 ̇ } (f g : 𝕄 → A) (p : 𝕄-caseable A f g)
          → 𝕄-cases f g p ∘ r ∼ g
𝕄-cases-r f g p = pr₂ (𝕄-cases-equations f g p)

\end{code}

Here are some examples:

\begin{code}

m : 𝕄 → 𝕄
m = 𝕄-cases (l ∘ r) (r ∘ l) refl

m-L : m L ＝ l C
m-L = refl

m-R : m R ＝ r C
m-R = refl

m-l : (x : 𝕄) → m (l x) ＝ l (r x)
m-l = 𝕄-cases-l _ _ refl

m-r : (x : 𝕄) → m (r x) ＝ r (l x)
m-r = 𝕄-cases-r _ _ refl

l-by-cases : l ∼ 𝕄-cases (l ∘ l) (m ∘ l) refl
l-by-cases = 𝕄-cases-uniqueness _ _
              refl l ((λ x → refl) , λ x → (m-l x)⁻¹)

r-by-cases : r ∼ 𝕄-cases (m ∘ r) (r ∘ r) refl
r-by-cases = 𝕄-cases-uniqueness _ _
              refl r ((λ x → (m-r x)⁻¹) , (λ x → refl))

\end{code}

We now define the midpoint operation _⊕_ : 𝕄 → (𝕄 → 𝕄) by
initiality. We will work with a subset of the function type 𝕄 → 𝕄 and
make it into a binary system.

\begin{code}

is-𝓛-function : (𝕄 → 𝕄) → 𝓤₀ ̇
is-𝓛-function f = 𝕄-caseable 𝕄 (l ∘ f) (m ∘ f)

is-𝓡-function : (𝕄 → 𝕄) → 𝓤₀ ̇
is-𝓡-function f = 𝕄-caseable 𝕄 (m ∘ f) (r ∘ f)

𝓛 : (f : 𝕄 → 𝕄) → is-𝓛-function f → (𝕄 → 𝕄)
𝓛 f = 𝕄-cases (l ∘ f) (m ∘ f)

𝓡 : (f : 𝕄 → 𝕄) → is-𝓡-function f → (𝕄 → 𝕄)
𝓡 f = 𝕄-cases (m ∘ f) (r ∘ f)

preservation-𝓛𝓛 : (f : 𝕄 → 𝕄) (𝓵 : is-𝓛-function f) (𝓻 : is-𝓡-function f)
                → is-𝓛-function (𝓛 f 𝓵)
preservation-𝓛𝓛 f 𝓵 𝓻 =
  l (𝓛 f 𝓵 R)  ＝⟨refl⟩
  l (m (f R))  ＝⟨ ap l 𝓻 ⟩
  l (r (f L))  ＝⟨ (m-l (f L))⁻¹ ⟩
  m (l (f L))  ＝⟨refl⟩
  m (𝓛 f 𝓵 L)  ∎

preservation-𝓛𝓡 : (f : 𝕄 → 𝕄) (𝓵 : is-𝓛-function f) (𝓻 : is-𝓡-function f)
                → is-𝓡-function (𝓛 f 𝓵)
preservation-𝓛𝓡 f 𝓵 𝓻 =
  m (𝓛 f 𝓵 R) ＝⟨refl⟩
  m (m (f R)) ＝⟨ ap m 𝓻 ⟩
  m (r (f L)) ＝⟨ m-r (f L) ⟩
  r (l (f L)) ＝⟨refl⟩
  r (𝓛 f 𝓵 L) ∎

preservation-𝓡𝓛 : (f : 𝕄 → 𝕄) (𝓵 : is-𝓛-function f) (𝓻 : is-𝓡-function f)
                → is-𝓛-function (𝓡 f 𝓻)
preservation-𝓡𝓛 f 𝓵 𝓻 =
  l (𝓡 f 𝓻 R)      ＝⟨refl⟩
  l (r (f R))      ＝⟨ (m-l (f R))⁻¹ ⟩
  m (l (f R))      ＝⟨ ap m 𝓵 ⟩
  m (m (f L))      ＝⟨refl⟩
  m (𝓡 f 𝓻 L)      ∎

preservation-𝓡𝓡 : (f : 𝕄 → 𝕄) (𝓵 : is-𝓛-function f) (𝓻 : is-𝓡-function f)
                → is-𝓡-function (𝓡 f 𝓻)
preservation-𝓡𝓡 f 𝓵 𝓻 =
  m (𝓡 f 𝓻 R)  ＝⟨refl⟩
  m (r (f R))  ＝⟨ 𝕄-cases-r (l ∘ r) (r ∘ l) refl (f R) ⟩
  r (l (f R))  ＝⟨ ap r 𝓵 ⟩
  r (m (f L))  ＝⟨refl⟩
  r (𝓡 f 𝓻 L)  ∎

is-𝓛𝓡-function : (𝕄 → 𝕄) → 𝓤₀ ̇
is-𝓛𝓡-function f = is-𝓛-function f × is-𝓡-function f

being-𝓛𝓡-function-is-prop : (f : 𝕄 → 𝕄) → is-prop (is-𝓛𝓡-function f)
being-𝓛𝓡-function-is-prop f = ×-is-prop 𝕄-is-set 𝕄-is-set

\end{code}

The desired subset of the function type 𝕄 → 𝕄 is this:

\begin{code}

F : 𝓤₀ ̇
F = Σ f ꞉ (𝕄 → 𝕄) , is-𝓛𝓡-function f

\end{code}

We now need to assume function extensionality.

(NB. We no longer need to know that F is a set, but we keep the
original proof.)

\begin{code}

open import UF.Base
open import UF.FunExt

module _ (fe  : Fun-Ext) where

 F-is-set : is-set F
 F-is-set = subsets-of-sets-are-sets (𝕄 → 𝕄) is-𝓛𝓡-function
             (Π-is-set fe (λ _ → 𝕄-is-set))
             (λ {f} → being-𝓛𝓡-function-is-prop f)

 𝑙𝑒𝑓𝑡 𝑟𝑖𝑔ℎ𝑡 : F → F
 𝑙𝑒𝑓𝑡 (f , (𝓵 , 𝓻))  = 𝓛 f 𝓵 , preservation-𝓛𝓛 f 𝓵 𝓻 , preservation-𝓛𝓡 f 𝓵 𝓻
 𝑟𝑖𝑔ℎ𝑡 (f , (𝓵 , 𝓻)) = 𝓡 f 𝓻 , preservation-𝓡𝓛 f 𝓵 𝓻 , preservation-𝓡𝓡 f 𝓵 𝓻

 𝐿𝑒𝑓𝑡 𝑅𝑖𝑔ℎ𝑡 : F
 𝐿𝑒𝑓𝑡  = l , refl , refl
 𝑅𝑖𝑔ℎ𝑡 = r , refl , refl

 F-eq-l : 𝐿𝑒𝑓𝑡 ＝ 𝑙𝑒𝑓𝑡 𝐿𝑒𝑓𝑡
 F-eq-l = to-subtype-＝ being-𝓛𝓡-function-is-prop γ
  where
   δ : l ∼ 𝓛 l refl
   δ = l-by-cases

   γ : l ＝ 𝓛 l refl
   γ = dfunext fe δ

 F-eq-lr : 𝑙𝑒𝑓𝑡 𝑅𝑖𝑔ℎ𝑡 ＝ 𝑟𝑖𝑔ℎ𝑡 𝐿𝑒𝑓𝑡
 F-eq-lr = to-subtype-＝ being-𝓛𝓡-function-is-prop v
  where
   i = λ (x : 𝕄) →
    𝕄-cases (l ∘ r) (m ∘ r) refl (l x) ＝⟨ 𝕄-cases-l _ _ refl x ⟩
    l (r x)                            ＝⟨ (m-l x)⁻¹ ⟩
    m (l x)                            ∎

   ii = λ (x : 𝕄) →
    𝕄-cases (l ∘ r) (m ∘ r) refl (r x) ＝⟨ 𝕄-cases-r _ _ refl x ⟩
    m (r x)                            ＝⟨ m-r x ⟩
    r (l x)                            ∎

   iii : 𝕄-cases (l ∘ r) (m ∘ r) refl
       ∼ 𝕄-cases (m ∘ l) (r ∘ l) refl
   iii = 𝕄-cases-uniqueness _ _ refl (𝕄-cases _ _ refl) (i , ii)

   iv : 𝓛 r refl ∼ 𝓡 l refl
   iv = iii

   v : 𝓛 r refl ＝ 𝓡 l refl
   v = dfunext fe iv


 F-eq-r : 𝑅𝑖𝑔ℎ𝑡 ＝ 𝑟𝑖𝑔ℎ𝑡 𝑅𝑖𝑔ℎ𝑡
 F-eq-r = to-subtype-＝ being-𝓛𝓡-function-is-prop γ
  where
   δ : r ∼ 𝓡 r refl
   δ = r-by-cases

   γ : r ＝ 𝓡 r refl
   γ = dfunext fe δ

 𝓕 : BS 𝓤₀
 𝓕 = (F , (𝐿𝑒𝑓𝑡 , 𝑅𝑖𝑔ℎ𝑡 , 𝑙𝑒𝑓𝑡 , 𝑟𝑖𝑔ℎ𝑡) , (F-eq-l , F-eq-lr , F-eq-r))

 mid : 𝕄 → F
 mid = 𝓜-rec 𝓕

 _⊕_ : 𝕄 → 𝕄 → 𝕄
 x ⊕ y = pr₁ (mid x) y

 ⊕-property : (x : 𝕄)
            → (l (x ⊕ R) ＝ m (x ⊕ L))
            × (m (x ⊕ R) ＝ r (x ⊕ L))
 ⊕-property x = pr₂ (mid x)

 mid-is-hom : is-hom 𝓜 𝓕 (𝓜-rec 𝓕)
 mid-is-hom = 𝓜-rec-is-hom 𝓕

 mid-is-hom-L : mid L ＝ 𝐿𝑒𝑓𝑡
 mid-is-hom-L = refl

 mid-is-hom-L' : (y : 𝕄) → L ⊕ y ＝ l y
 mid-is-hom-L' y = refl

 mid-is-hom-R : mid R ＝ 𝑅𝑖𝑔ℎ𝑡
 mid-is-hom-R = refl

 mid-is-hom-R' : (y : 𝕄) → R ⊕ y ＝ r y
 mid-is-hom-R' y = refl

 mid-is-hom-l : (x : 𝕄) → mid (l x) ＝ 𝑙𝑒𝑓𝑡 (mid x)
 mid-is-hom-l = is-hom-l 𝓜 𝓕 mid mid-is-hom

 mid-is-hom-l' : (x y : 𝕄)
               → (l x ⊕ L   ＝ l (x ⊕ L))
               × (l x ⊕ R   ＝ m (x ⊕ R))
               × (l x ⊕ l y ＝ l (x ⊕ y))
               × (l x ⊕ r y ＝ m (x ⊕ y))
 mid-is-hom-l' x y = u , v , w , t
  where
   α = λ y → l x ⊕ y             ＝⟨refl⟩
             pr₁ (mid (l x)) y   ＝⟨ happly (ap pr₁ (mid-is-hom-l x)) y ⟩
             pr₁ (𝑙𝑒𝑓𝑡 (mid x)) y  ＝⟨refl⟩
             𝕄-cases (l ∘ (x ⊕_)) (m ∘ (x ⊕_)) (pr₁ (⊕-property x)) y ∎

   u = α L
   v = α R
   w = α (l y) ∙ 𝕄-cases-l
                  (l ∘ (x ⊕_))
                  (m ∘ (x ⊕_))
                  (pr₁ (⊕-property x))
                  y
   t = α (r y) ∙ 𝕄-cases-r
                  (l ∘ (x ⊕_))
                  (m ∘ (x ⊕_))
                  (pr₁ (⊕-property x))
                  y

 mid-is-hom-r : (x : 𝕄) → mid (r x) ＝ 𝑟𝑖𝑔ℎ𝑡 (mid x)
 mid-is-hom-r = is-hom-r 𝓜 𝓕 mid mid-is-hom

 mid-is-hom-r' : (x y : 𝕄)
               → (r x ⊕ L   ＝ m (x ⊕ L))
               × (r x ⊕ R   ＝ r (x ⊕ R))
               × (r x ⊕ l y ＝ m (x ⊕ y))
               × (r x ⊕ r y ＝ r (x ⊕ y))
 mid-is-hom-r' x y = u , v , w , t
  where
   α = λ y → r x ⊕ y              ＝⟨refl⟩
             pr₁ (mid (r x)) y    ＝⟨ happly (ap pr₁ (mid-is-hom-r x)) y ⟩
             pr₁ (𝑟𝑖𝑔ℎ𝑡 (mid x)) y ＝⟨refl⟩
             𝕄-cases (m ∘ (x ⊕_)) (r ∘ (x ⊕_)) (pr₂ (⊕-property x)) y ∎

   u = α L
   v = α R
   w = α (l y) ∙ 𝕄-cases-l
                  (m ∘ (x ⊕_))
                  (r ∘ (x ⊕_))
                  (pr₂ (⊕-property x))
                  y
   t = α (r y) ∙ 𝕄-cases-r
                  (m ∘ (x ⊕_))
                  (r ∘ (x ⊕_))
                  (pr₂ (⊕-property x))
                  y

\end{code}

So, the set of defining equations is the following, where it can be
seen that there is some redundancy:

     (  l (x ⊕ R) ＝ m (x ⊕ L)    )
   × (  m (x ⊕ R) ＝ r (x ⊕ L)    )
   × (  L   ⊕ y   ＝ l y          )
   × (  R   ⊕ y   ＝ r y          )
   × (  l x ⊕ L   ＝ l (x ⊕ L)    )
   × (  l x ⊕ R   ＝ m (x ⊕ R)    )
   × (  l x ⊕ l y ＝ l (x ⊕ y)    )
   × (  l x ⊕ r y ＝ m (x ⊕ y)    )
   × (  r x ⊕ R   ＝ r (x ⊕ R)    )
   × (  r x ⊕ L   ＝ m (x ⊕ L)    )
   × (  r x ⊕ l y ＝ m (x ⊕ y)    )
   × (  r x ⊕ r y ＝ r (x ⊕ y)    )

The first two come from the binary system F and the remaining ones from the homomorphism condition and case analysis.

TODO. Next we want to show that

  _⊕_ : 𝕄 → 𝕄 → 𝕄

makes the initial binary system into the free midpoint algebra over
two generators (taken to be L and R, as expected), where the
midpoint axioms are

   (idempotency)    x ⊕ x ＝ x,
   (commutativity)  x ⊕ y ＝ y ⊕ x,
   (transposition)  (u ⊕ v) ⊕ (x ⊕ y) ＝ (u ⊕ x) ⊕ (v ⊕ y).

In fact, in the initial binary system, there is a unique midpoint
operation _⊕_ such that

   L ⊕ x = l x,
   R ⊕ x = r x.
