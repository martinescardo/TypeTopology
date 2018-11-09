Martin Escardo, 16 Dec 2016

Equivalent copy of the natural numbers with logarithmic-size elements.

We use a modification of binary notation to avoid leading zeros and
hence multiple representations of the same number.

The isomorphic copy is formally constructed from 0 iterating the
functions L(n)=2n+1 and R(n)=2n+2.

As an application, we construct a pairing function and hence an
equivalence ℕ × ℕ ≃ ℕ.

\begin{code}

module BinaryNaturals where

open import SpartanMLTT renaming (_+_ to _∔_)
open import UF-Equiv
open import UF-Base
open import UF-EquivalenceExamples

\end{code}

The doubling function n ↦ 2n:

\begin{code}

double : ℕ → ℕ
double zero    = zero
double(succ n) = succ(succ(double n))

\end{code}

The functions n ↦ 2n+1 and n ↦ 2n+2:

\begin{code}

L : ℕ → ℕ
L n = succ(double n)

R : ℕ → ℕ
R n = succ(L n)

\end{code}

Modified binary rendering of the natural numbers and its native
induction principle:

\begin{code}

data 𝔹 : U₀ ̇ where
 zero : 𝔹
 l    : 𝔹 → 𝔹
 r    : 𝔹 → 𝔹

\end{code}

The successor function n ↦ n+1 on 𝔹:

\begin{code}

Succ : 𝔹 → 𝔹
Succ zero  = l zero
Succ(l m)  = r m
Succ(r m)  = l(Succ m)

\end{code}

Conversion between the two renderings:

\begin{code}

unary : 𝔹 → ℕ
unary zero = zero
unary(l m) = L(unary m)
unary(r m) = R(unary m)

binary : ℕ → 𝔹
binary zero    = zero
binary(succ n) = Succ(binary n)

\end{code}

The size of a (binary) number and the base 2 logarithm of a (unary)
number. We have lg2 ((2^n)-1) = n (TODO).

\begin{code}

size : 𝔹 → ℕ
size zero  = zero
size (l m) = succ (size m)
size (r m) = succ (size m)

lg2 : ℕ → ℕ
lg2 n = size(binary n)

\end{code}

Next we show that the functions binary and unary are mutually
inverse, after we formulate and prove some lemmas for that.

First some commutation properties:

\begin{code}

ldiagram : ∀ n → binary(L n) ≡ l(binary n)
ldiagram zero    = refl
ldiagram(succ n) = ap (λ - → Succ(Succ -)) (ldiagram n)

rdiagram : ∀ n → binary(R n) ≡ r(binary n)
rdiagram zero    = refl
rdiagram(succ n) = ap (λ - → Succ(Succ -)) (rdiagram n)

sdiagram : ∀ m → unary(Succ m) ≡ succ(unary m)
sdiagram zero = refl
sdiagram(l m) = refl
sdiagram(r m) = ap L (sdiagram m)

\end{code}

The functions unary and binary are mutually inverse:

\begin{code}

unary-binary : ∀ n → unary(binary n) ≡ n
unary-binary zero    = refl
unary-binary(succ n) = g
 where
  IH : unary(binary n) ≡ n
  IH = unary-binary n
  a : succ(unary(binary n)) ≡ succ n
  a = ap succ IH
  g : unary(Succ(binary n)) ≡ succ n
  g = sdiagram(binary n) ∙ a

binary-unary : ∀ m → binary(unary m) ≡ m
binary-unary zero = refl
binary-unary(l m) = g
 where
  IH : binary(unary m) ≡ m
  IH = binary-unary m
  a : l(binary(unary m)) ≡ l m
  a = ap l IH
  g : binary(unary(l m)) ≡ l m
  g = ldiagram(unary m) ∙ a
binary-unary(r m) = g
 where
  IH : binary(unary m) ≡ m
  IH = binary-unary m
  a : r(binary(unary m)) ≡ r m
  a = ap r IH
  g : binary(unary(r m)) ≡ r m
  g = rdiagram(unary m) ∙ a

binary-equiv : 𝔹 ≃ ℕ
binary-equiv = qinveq unary (binary , binary-unary , unary-binary)

\end{code}

Induction principles induced by the equivalences:

\begin{code}

ℕ-induction : {A : ℕ → U ̇}
            → A zero
            → (∀ n → A n → A(succ n))
            → ∀ n → A n
ℕ-induction base step zero     = base
ℕ-induction base step (succ n) = step n (ℕ-induction base step n)

𝔹-induction : {B : 𝔹 → U ̇}
            → B zero
            → (∀ m → B m → B(l m))
            → (∀ m → B m → B(r m))
            → ∀ m → B m
𝔹-induction base stepl stepr zero  = base
𝔹-induction base stepl stepr (l m) = stepl m (𝔹-induction base stepl stepr m)
𝔹-induction base stepl stepr (r m) = stepr m (𝔹-induction base stepl stepr m)

unary-induction-on-𝔹 : {B : 𝔹 → U ̇}
                     → B zero
                     → (∀ n → B n → B(Succ n))
                     → ∀ n → B n
unary-induction-on-𝔹 {U} {B} base step = g
 where
  A : ℕ → U ̇
  A n = B (binary n)
  base' : A zero
  base' = base
  step' : (n : ℕ) → A n → A (succ n)
  step' n = step (binary n)
  a : ∀ n → A n
  a = ℕ-induction base' step'
  b : ∀ m → B(binary(unary m))
  b m = a (unary m)
  g : ∀ m → B m
  g m = transport B (binary-unary m) (b m)

binary-induction-on-ℕ : {A : ℕ → U ̇}
                     → A zero
                     → (∀ n → A n → A(L n))
                     → (∀ n → A n → A(R n))
                     → ∀ n → A n
binary-induction-on-ℕ {U} {A} base stepl stepr = g
 where
  B : 𝔹 → U ̇
  B m = A (unary m)
  base' : B zero
  base' = base
  stepl' : (m : 𝔹) → B m → B (l m)
  stepl' m = stepl (unary m)
  stepr' : (m : 𝔹) → B m → B (r m)
  stepr' m = stepr (unary m)
  b : ∀ m → B m
  b = 𝔹-induction base' stepl' stepr'
  a : ∀ n → A(unary(binary n))
  a n = b (binary n)
  g : ∀ n → A n
  g n = transport A (unary-binary n) (a n)

\end{code}

Some operations performed directly in modified binary, for the sake of
efficiency, with their correctness verified.

The doubling function n ↦ 2n:

\begin{code}

Double : 𝔹 → 𝔹
Double zero = zero
Double(l m) = r(Double m)
Double(r m) = Succ(Succ(r(Double m)))

Double-lemma : ∀ m → Succ(Succ(Double m)) ≡ Double(Succ m)
Double-lemma zero = refl
Double-lemma(l m) = refl
Double-lemma(r m) = ap r (Double-lemma m)

ddiagram : ∀ n → binary(double n) ≡ Double(binary n)
ddiagram zero    = refl
ddiagram(succ n) = g
 where
  IH : binary(double n) ≡ Double(binary n)
  IH = ddiagram n
  a : Succ(Succ(binary(double n))) ≡ Succ(Succ(Double(binary n)))
  a = ap (λ - → Succ(Succ -)) IH
  g : binary(double(succ n)) ≡ Double(binary(succ n))
  g = a ∙ Double-lemma(binary n)

\end{code}

Now addition, with a faster version in binary:

\begin{code}

_+_ : ℕ → ℕ → ℕ
x + zero = x
x + succ y = succ(x + y)

_+♭_ : 𝔹 → 𝔹 → 𝔹
x    +♭ zero = x
zero +♭ l y  = l y
l x  +♭ l y  = r(x +♭ y)
r x  +♭ l y  = l(Succ(x +♭ y))
zero +♭ r y  = r y
l x  +♭ r y  = l(Succ(x +♭ y))
r x  +♭ r y  = r(Succ(x +♭ y))

+♭-lemma : ∀ m n → Succ(m +♭ n) ≡ m +♭ Succ n
+♭-lemma zero   zero = refl
+♭-lemma (l m)  zero = refl
+♭-lemma (r m)  zero = refl
+♭-lemma zero  (l n) = refl
+♭-lemma (l m) (l n) = refl
+♭-lemma (r m) (l n) = refl
+♭-lemma zero  (r n) = refl
+♭-lemma (l m) (r n) = ap r (+♭-lemma m n)
+♭-lemma (r m) (r n) = ap (λ - → l(Succ -)) (+♭-lemma m n)

+diagram : ∀ m n → binary(m + n) ≡ binary m +♭ binary n
+diagram m zero     = refl
+diagram m (succ n) = g
 where
  IH : binary(m + n) ≡ binary m +♭ binary n
  IH = +diagram m n
  a : Succ(binary(m + n)) ≡ Succ(binary m +♭ binary n)
  a = ap Succ IH
  g : Succ(binary(m + n)) ≡ binary m +♭ Succ(binary n)
  g = a ∙ +♭-lemma (binary m) (binary n)

\end{code}

Even faster binary addition (linear time).  We define the following
operations with the following specifications:

\begin{code}

_+₀_ _+₁_ _+₂_ : 𝔹 → 𝔹 → 𝔹
Succ₂          : 𝔹 → 𝔹

+₀-spec    : ∀ x y → x +₀ y ≡ x +♭ y
+₁-spec    : ∀ x y → x +₁ y ≡ Succ(x +♭ y)
+₂-spec    : ∀ x y → x +₂ y ≡ Succ(Succ(x +♭ y))
Succ₂-spec : ∀ x →  Succ₂ x ≡ Succ(Succ x)

\end{code}

Definitions:

\begin{code}

x    +₀ zero = x
zero +₀ l y  = l y
l x  +₀ l y  = r(x +₀ y)
r x  +₀ l y  = l(x +₁ y)
zero +₀ r y  = r y
l x  +₀ r y  = l(x +₁ y)
r x  +₀ r y  = r(x +₁ y)

x    +₁ zero = Succ x
zero +₁ l y  = r y
l x  +₁ l y  = l(x +₁ y)
r x  +₁ l y  = r(x +₁ y)
zero +₁ r y  = l(Succ y)
l x  +₁ r y  = r(x +₁ y)
r x  +₁ r y  = l(x +₂ y)

x    +₂ zero = Succ₂ x
zero +₂ l y  = l(Succ y)
l x  +₂ l y  = r(x +₁ y)
r x  +₂ l y  = l(x +₂ y)
zero +₂ r y  = r(Succ y)
l x  +₂ r y  = l(x +₂ y)
r x  +₂ r y  = r(x +₂ y)

Succ₂ zero  = r zero
Succ₂ (l x) = l(Succ x)
Succ₂ (r x) = r(Succ x)

\end{code}

Correctness proof:

\begin{code}

+₀-spec x zero      = refl
+₀-spec zero (l y)  = refl
+₀-spec (l x) (l y) = ap r (+₀-spec x y)
+₀-spec (r x) (l y) = ap l (+₁-spec x y)
+₀-spec zero (r y)  = refl
+₀-spec (l x) (r y) = ap l (+₁-spec x y)
+₀-spec (r x) (r y) = ap r (+₁-spec x y)

+₁-spec x zero      = refl
+₁-spec zero (l y)  = refl
+₁-spec (l x) (l y) = ap l (+₁-spec x y)
+₁-spec (r x) (l y) = ap r (+₁-spec x y)
+₁-spec zero (r y)  = refl
+₁-spec (l x) (r y) = ap r (+₁-spec x y)
+₁-spec (r x) (r y) = ap l (+₂-spec x y)

+₂-spec x zero      = Succ₂-spec x
+₂-spec zero (l y)  = refl
+₂-spec (l x) (l y) = ap r (+₁-spec x y)
+₂-spec (r x) (l y) = ap l (+₂-spec x y)
+₂-spec zero (r y)  = refl
+₂-spec (l x) (r y) = ap l (+₂-spec x y)
+₂-spec (r x) (r y) = ap r (+₂-spec x y)

Succ₂-spec zero  = refl
Succ₂-spec (l x) = refl
Succ₂-spec (r x) = refl

\end{code}

Now multiplication.

\begin{code}

_⋆_ : ℕ → ℕ → ℕ
m ⋆ zero = zero
m ⋆ succ n = m ⋆ n + m -- m(n+1) = mn + m

_⋆♭_ : 𝔹 → 𝔹 → 𝔹
m ⋆♭ zero = zero
m ⋆♭ l n = Double(m ⋆♭ n) +♭ m
m ⋆♭ r n = Double(m ⋆♭ n +♭ m)

_⋆₁_ : 𝔹 → 𝔹 → 𝔹
m    ⋆₁ zero = zero
zero ⋆₁ l n  = zero
l m  ⋆₁ l n  = l(Double(m ⋆₁ n) +₀ m +₀ n) -- (2m+1)(2n+1) = 4mn + 2m + 2n + 1 = 2(2mn+m+n)+1
r m  ⋆₁ l n  = r(Double(m ⋆₁ n +₀ n) +₀ m) -- (2m+2)(2n+1) = 4mn + 2m + 4n + 2 = 2(2(mn+n)+m)+2
zero ⋆₁ r n  = zero
l m  ⋆₁ r n  = r(Double(m ⋆₁ n +₀ m) +₀ n)
r m  ⋆₁ r n  = Double(Double(m ⋆₁ n +₀ (m +₁ n))) -- (2m+2)(2n+2) = 4mn + 4m + 4n + 4 = 4(mn + m + n + 1)

\end{code}

We need a proof for multiplication. Here is feeble evidence for the
moment, in the form of an experiment:

\begin{code}

test : unary(binary 172 ⋆₁ binary 133) ≡ 172 ⋆ 133
test = refl

\end{code}

Faster double, by specializing addition x ↦ x + x:

\begin{code}

double₀ double₁ double₂ : 𝔹 → 𝔹
double₀-spec : ∀ x → double₀ x ≡ x +₀ x
double₁-spec : ∀ x → double₁ x ≡ x +₁ x
double₂-spec : ∀ x → double₂ x ≡ x +₂ x

\end{code}

Can be understood as transducer with three states:

\begin{code}

double₀ zero = zero
double₀(l x) = r(double₀ x)
double₀(r x) = r(double₁ x)

double₁ zero = l zero
double₁(l x) = l(double₁ x)
double₁(r x) = l(double₂ x)

double₂ zero = r zero
double₂(l x) = r(double₁ x)
double₂(r x) = r(double₂ x)

double₀-spec zero = refl
double₀-spec (l x) = ap r (double₀-spec x)
double₀-spec (r x) = ap r (double₁-spec x)

double₁-spec zero = refl
double₁-spec (l x) = ap l (double₁-spec x)
double₁-spec (r x) = ap l (double₂-spec x)

double₂-spec zero = refl
double₂-spec (l x) = ap r (double₁-spec x)
double₂-spec (r x) = ap r (double₂-spec x)

\end{code}

We get a pairing function as follows, using a rather minimal amount of
arithmetic (14th July 2018):

We use binary notation to simplify the definition. An alternative
would be to work with the usual unary notation, using binary
induction. However, this would prevent us from using pattern matching,
which gives a more intuitive definition.

\begin{code}

first' : 𝔹 → ℕ
first' zero = zero
first' (l b) = succ (first' b)
first' (r b) = zero

second' : 𝔹 → 𝔹
second' zero = zero
second' (l b) = second' b
second' (r b) = Succ b

pair' : ℕ → ℕ → 𝔹
pair' zero zero = zero
pair' (succ n) zero = l(pair' n zero)
pair' zero (succ k) = r (binary k)
pair' (succ n) (succ k) = l (pair' n (succ k))

pair'-claim : (n k : ℕ) → pair' (succ n) k ≡ l(pair' n k)
pair'-claim n zero = refl
pair'-claim n (succ k) = refl

first'-lemma : (n k : ℕ) → first'(pair' n k) ≡ n
first'-lemma zero zero = refl
first'-lemma zero (succ k) = refl
first'-lemma (succ n) zero = ap succ (first'-lemma n zero)
first'-lemma (succ n) (succ k) = ap succ (first'-lemma n (succ k))

second'-lemma : (n k : ℕ) → second'(pair' n k) ≡ binary k
second'-lemma zero zero = refl
second'-lemma zero (succ k) = refl
second'-lemma (succ n) zero = second'-lemma n zero
second'-lemma (succ n) (succ k) = second'-lemma n (succ k)

pair'-lemma : (b : 𝔹) → pair' (first' b) (unary(second' b)) ≡ b
pair'-lemma zero = refl
pair'-lemma (l b) = γ
 where
  IH : pair' (first' b) (unary (second' b)) ≡ b
  IH = pair'-lemma b
  c : pair' (succ (first' b)) (unary (second' b)) ≡ l (pair' (first' b) (unary (second' b)))
  c = pair'-claim (first' b) (unary (second' b))
  γ : pair' (succ (first' b)) (unary (second' b)) ≡ l b
  γ = c ∙ ap l IH
pair'-lemma (r b) = γ
 where
  p : r (binary (unary b)) ≡ r b
  p = ap r (binary-unary b)
  q : pair' zero (succ(unary b)) ≡ r b
  q = p
  γ : pair' zero (unary (Succ b)) ≡ r b
  γ = back-transport (λ - → pair' zero - ≡ r b) (sdiagram b) q

pair : ℕ × ℕ → ℕ
pair (n , k) = unary(pair' n k)

first second : ℕ → ℕ
first = first' ∘ binary
second = unary ∘ second' ∘ binary

first-pair : (n k : ℕ) → first (pair (n , k)) ≡ n
first-pair n k = back-transport
                  (λ - → first' - ≡ n)
                  (binary-unary (pair' n k))
                  (first'-lemma n k)

second-pair : (n k : ℕ) → second (pair (n , k)) ≡ k
second-pair n k = back-transport
                   (λ - → unary (second' -) ≡ k)
                   (binary-unary (pair' n k))
                   (ap unary (second'-lemma n k) ∙ unary-binary k)

riap : ℕ → ℕ × ℕ
riap m = (first m , second m)

pair-riap : (m : ℕ) → pair(riap m) ≡ m
pair-riap m = ap unary (pair'-lemma (binary m)) ∙ unary-binary m

riap-pair : (z : ℕ × ℕ) → riap(pair z) ≡ z
riap-pair (n , k) = to-×-≡ (first-pair n k) (second-pair n k)

pairing : ℕ × ℕ ≃ ℕ
pairing = qinveq pair  (riap , riap-pair , pair-riap)

\end{code}

We now show that ℕ + ℕ ≃ ℕ (July 2018).

\begin{code}

ℕ-plus-𝟙 : ℕ ∔ 𝟙 ≃ ℕ
ℕ-plus-𝟙 = qinveq f (g , ε , η)
 where
  f : ℕ ∔ 𝟙 {U₀} → ℕ
  f (inl n) = succ n
  f (inr *) = zero
  g : ℕ → ℕ ∔ 𝟙
  g zero = inr *
  g (succ n) = inl n
  η : (n : ℕ) → f (g n) ≡ n
  η zero = refl
  η (succ n) = refl
  ε : (z : ℕ ∔ 𝟙) → g (f z) ≡ z
  ε (inl n) = refl
  ε (inr *) = refl

two-𝔹-plus-𝟙 : 𝔹 ∔ 𝔹 ∔ 𝟙 ≃ 𝔹
two-𝔹-plus-𝟙 = qinveq f (g , ε , η)
 where
  f : 𝔹 ∔ 𝔹 ∔ 𝟙 {U₀} → 𝔹
  f (inl b) = l b
  f (inr (inl b)) = r b
  f (inr (inr *)) = zero
  g : 𝔹 → 𝔹 ∔ 𝔹 ∔ 𝟙
  g zero = inr (inr *)
  g (l b) = inl b
  g (r b) = inr (inl b)
  η : (b : 𝔹) → f (g b) ≡ b
  η zero = refl
  η (l b) = refl
  η (r b) = refl
  ε : (z : 𝔹 ∔ 𝔹 ∔ 𝟙) → g (f z) ≡ z
  ε (inl b) = refl
  ε (inr (inl b)) = refl
  ε (inr (inr *)) = refl

two-ℕ-plus-𝟙 : ℕ ∔ ℕ ∔ 𝟙 ≃ ℕ
two-ℕ-plus-𝟙 =
    ℕ ∔ (ℕ ∔ 𝟙)    ≃⟨ +-cong (≃-sym binary-equiv) (Ap+ 𝟙 (≃-sym binary-equiv)) ⟩
    𝔹 ∔ (𝔹 ∔ 𝟙)  ≃⟨ two-𝔹-plus-𝟙 ⟩
    𝔹             ≃⟨ binary-equiv ⟩
    ℕ ■

two-ℕ : ℕ ∔ ℕ ≃ ℕ
two-ℕ =
   ℕ ∔ ℕ        ≃⟨ Ap+ ℕ (≃-sym ℕ-plus-𝟙) ⟩
   (ℕ ∔ 𝟙) ∔ ℕ  ≃⟨ +comm ⟩
   ℕ ∔ ℕ ∔ 𝟙    ≃⟨ two-ℕ-plus-𝟙 ⟩
   ℕ ■

\end{code}

The following examples show that these equivalences compute:

\begin{code}

module examples where

 example-riap : riap 17 ≡ (1 , 4)
 example-riap = refl

 example-pair : pair (5 , 6) ≡ 415
 example-pair = refl

 ex17 : eqtofun (≃-sym two-ℕ) 17 ≡ inr 8
 ex17 = refl

 ex18 : eqtofun (≃-sym two-ℕ) 18 ≡ inl 9
 ex18 = refl

\end{code}

And finally the fixities assumed above:

\begin{code}

infixl 6 _+_
infixl 7 _⋆_
infixl 6 _+♭_
infixl 7 _⋆♭_
infixl 6 _+₁_
infixl 6 _+₀_
infixl 7 _⋆₁_

\end{code}
