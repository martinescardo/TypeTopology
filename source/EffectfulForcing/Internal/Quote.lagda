Currently porting those:
https://github.com/vrahli/opentt/blob/master/encoding2.lagda
https://github.com/vrahli/opentt/blob/master/encoding3.lagda

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

module EffectfulForcing.Internal.Quote where

open import MLTT.Spartan  hiding (rec ; _^_ ; _+_)
open import Naturals.Order renaming (_≤ℕ_ to _≤_; _<ℕ_ to _<_)
open import Naturals.Addition using (_+_; succ-right; sum-to-zero-gives-zero; addition-commutativity)
open import EffectfulForcing.MFPSAndVariations.SystemT using (type ; ι ; _⇒_ ; 〖_〗)
open import EffectfulForcing.Internal.SystemT
open import UF.Base using (transport₂ ; transport₃ ; ap₂ ; ap₃)

\end{code}

System T with quoting.

\begin{code}

data QT : (Γ : Cxt) (σ : type) → 𝓤₀ ̇  where
 Zero    : {Γ : Cxt} → QT Γ ι
 Succ    : {Γ : Cxt} → QT Γ ι → QT Γ ι
 Rec     : {Γ : Cxt} {σ : type} → QT Γ (ι ⇒ σ ⇒ σ) → QT Γ σ → QT Γ ι → QT Γ σ
 ν       : {Γ : Cxt} {σ : type} (i : ∈Cxt σ Γ)  → QT Γ σ
 ƛ       : {Γ : Cxt} {σ τ : type} → QT (Γ ,, σ) τ → QT Γ (σ ⇒ τ)
 _·_     : {Γ : Cxt} {σ τ : type} → QT Γ (σ ⇒ τ) → QT Γ σ → QT Γ τ
 Quote   : {Γ : Cxt} {σ : type} → QT Γ σ → QT Γ ι
 Unquote : {Γ : Cxt} {σ : type} → QT Γ ι → QT Γ σ

\end{code}

\begin{code}

_∧_ : 𝟚 → 𝟚 → 𝟚
₁ ∧ b = b
₀ ∧ b = ₀

infixr 6 _∧_

succ-injective : ∀ {m n} → succ m ＝ succ n → m ＝ n
succ-injective refl = refl

comp-ind-ℕ-aux2 : (P : ℕ → Set)
                → ((n : ℕ) → ((m : ℕ) → m < n → P m) → P n)
                → (n m : ℕ) → m ≤ n → P m
comp-ind-ℕ-aux2 P φ n m p = course-of-values-induction P φ m

<ℕind2 : (P : ℕ → Set)
       → ((n : ℕ) → ((m : ℕ) → m < n → P m) → P n)
       → (n : ℕ) → P n
<ℕind2 P ind n = comp-ind-ℕ-aux2 P ind n n (≤-refl n)

∧＝true→ₗ : {a b : 𝟚} → a ∧ b ＝ ₁ → a ＝ ₁
∧＝true→ₗ {₁} {b} x = refl

∧＝true→ᵣ : {a b : 𝟚} → a ∧ b ＝ ₁ → b ＝ ₁
∧＝true→ᵣ {₁} {b} x = x

∧＝true→1-3 : {a b c : 𝟚} → a ∧ b ∧ c ＝ ₁ → a ＝ ₁
∧＝true→1-3 {a} {b} {c} x = ∧＝true→ₗ {a} {b ∧ c} x

∧＝true→2-3 : {a b c : 𝟚} → a ∧ b ∧ c ＝ ₁ → b ＝ ₁
∧＝true→2-3 {a} {b} {c} x = ∧＝true→ₗ {b} {c} (∧＝true→ᵣ {a} {b ∧ c} x)

∧＝true→3-3 : {a b c : 𝟚} → a ∧ b ∧ c ＝ ₁ → c ＝ ₁
∧＝true→3-3 {a} {b} {c} x = ∧＝true→ᵣ {b} {c} (∧＝true→ᵣ {a} {b ∧ c} x)

pairingAux : ℕ → ℕ
pairingAux 0 = 0
pairingAux (succ i) = (succ i) + pairingAux i

pairing : ℕ × ℕ → ℕ
pairing (x , y) = y + pairingAux (y + x)

pairing3 : ℕ × ℕ × ℕ → ℕ
pairing3 (x , y , z) = pairing (x , pairing (y , z))

pairing4 : ℕ × ℕ × ℕ × ℕ → ℕ
pairing4 (x , y , z , w) = pairing (x , pairing3 (y , z , w))

unpairing : ℕ → ℕ × ℕ
unpairing 0 = 0 , 0
unpairing (succ n) with unpairing n
... | succ x , y = x , succ y
... | 0 , y = succ y , 0

-- n is (pairing x y), and we want to return x
pairing→₁ : (n : ℕ) → ℕ
pairing→₁ n = pr₁ (unpairing n)

-- n is (pairing x y), and we want to return y
pairing→₂ : (n : ℕ) → ℕ
pairing→₂ n = pr₂ (unpairing n)

-- n is (pairing3 x y z), and we want to return x
pairing3→₁ : (n : ℕ) → ℕ
pairing3→₁ n = pr₁ (unpairing n)

-- n is (pairing3 x y z), and we want to return y
pairing3→₂ : (n : ℕ) → ℕ
pairing3→₂ n = pr₁ (unpairing (pr₂ (unpairing n)))

-- n is (pairing3 x y z), and we want to return z
pairing3→₃ : (n : ℕ) → ℕ
pairing3→₃ n = pr₂ (unpairing (pr₂ (unpairing n)))

+＝0→ : (n m : ℕ) → n + m ＝ 0 → (n ＝ 0) × (m ＝ 0)
+＝0→ n m h = sum-to-zero-gives-zero m n h′ , sum-to-zero-gives-zero n m h
 where
  h′ : m + n ＝ 0
  h′ = m + n ＝⟨ addition-commutativity m n ⟩ n + m ＝⟨ h ⟩ 0 ∎

+0 : (n : ℕ) → n + 0 ＝ n
+0 0 = refl
+0 (succ n) = ap succ (+0 n)

pairingAux＝0→ : (n : ℕ) → pairingAux n ＝ 0 → n ＝ 0
pairingAux＝0→ = {!!}

pairing＝0→ : (x y : ℕ) → pairing (x , y) ＝ 0 → (x ＝ 0) × (y ＝ 0)
pairing＝0→ = {!!}

pairing-x0 : (x : ℕ) → pairing (x , 0) ＝ pairingAux x
pairing-x0 x = {!!}

pairing-s0 : (x : ℕ) → pairing (succ x , 0) ＝ succ (pairing (0 , x))
pairing-s0 x = {!!}

pairing-xs : (x y : ℕ) → pairing (x , succ y) ＝ succ (pairing (succ x , y))
pairing-xs x y = {!!}

＝pair : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {a₁ a₂ : A} {b₁ b₂ : B} → a₁ ＝ a₂ → b₁ ＝ b₂ → (a₁ , b₁) ＝ (a₂ , b₂)
＝pair {_} {_} {A} {B} {a₁} {a₂} {b₁} {b₂} refl refl = refl

＝pair→ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {a₁ a₂ : A} {b₁ b₂ : B} → (a₁ , b₁) ＝ (a₂ , b₂) → (a₁ ＝ a₂) × (b₁ ＝ b₂)
＝pair→ {_} {_} {A} {B} {a₁} {a₂} {b₁} {b₂} refl = refl , refl

¬succ＝0 : (a : ℕ) → ¬ (succ a ＝ 0)
¬succ＝0 a ()

unpairing-pairing-aux : (p : ℕ × ℕ) (n : ℕ) → pairing p ＝ n → unpairing n ＝ p
unpairing-pairing-aux (x , y) 0 h = ＝pair ((pr₁ (pairing＝0→ x y h)) ⁻¹) ((pr₂ (pairing＝0→ x y h)) ⁻¹)
unpairing-pairing-aux (x , 0) (succ n) h with x
... | 0 = 𝟘-elim (¬succ＝0 n (h ⁻¹))
... | succ x
 with unpairing-pairing-aux (0 , x) n
... | z with unpairing n
... | 0 , b = ap (λ k → succ k , 0) (pr₂ (＝pair→ (z (succ-injective ((pairing-s0 x) ⁻¹ ∙ h)))))
... | succ a , b = 𝟘-elim (¬succ＝0 a (pr₁ (＝pair→ (z (succ-injective ((pairing-s0 x) ⁻¹ ∙ h))))))
unpairing-pairing-aux (x , succ y) (succ n) h with unpairing-pairing-aux (succ x , y) n
... | z with unpairing n
... | 0 , b = 𝟘-elim (¬succ＝0 x ((pr₁ (＝pair→ (z (succ-injective ((pairing-xs x y) ⁻¹ ∙ h))))) ⁻¹))
... | succ a , b =
 ＝pair
  (succ-injective (pr₁ (＝pair→ (z (succ-injective ((pairing-xs x y) ⁻¹ ∙ h))))))
  (ap succ (pr₂ (＝pair→ (z (succ-injective ((pairing-xs x y) ⁻¹ ∙ h))))))

unpairing-pairing : (p : ℕ × ℕ) → unpairing (pairing p) ＝ p
unpairing-pairing p = unpairing-pairing-aux p (pairing p) refl

pairing→₁-pairing : (x₁ x₂ : ℕ) → pairing→₁ (pairing (x₁ , x₂)) ＝ x₁
pairing→₁-pairing x₁ x₂ = ap pr₁ (unpairing-pairing (x₁ , x₂))

＝pairing→₁ : {x₁ x₂ : ℕ} → x₁ ＝ x₂ → pairing→₁ x₁ ＝ pairing→₁ x₂
＝pairing→₁ {x₁} {x₂} refl = refl

pairing→₂-pairing : (x₁ x₂ : ℕ) → pairing→₂ (pairing (x₁ , x₂)) ＝ x₂
pairing→₂-pairing x₁ x₂ = ap pr₂ (unpairing-pairing (x₁ , x₂))

＝pairing→₂ : {x₁ x₂ : ℕ} → x₁ ＝ x₂ → pairing→₂ x₁ ＝ pairing→₂ x₂
＝pairing→₂ {x₁} {x₂} refl = refl

pairing3→₁-pairing3 : (x₁ x₂ x₃ : ℕ) → pairing3→₁ (pairing3 (x₁ , x₂ , x₃)) ＝ x₁
pairing3→₁-pairing3 x₁ x₂ x₃ = ap pr₁ (unpairing-pairing (x₁ , pairing (x₂ , x₃)))

＝pairing3→₁ : {x₁ x₂ : ℕ} → x₁ ＝ x₂ → pairing3→₁ x₁ ＝ pairing3→₁ x₂
＝pairing3→₁ {x₁} {x₂} refl = refl

pairing3→₂-pairing3 : (x₁ x₂ x₃ : ℕ) → pairing3→₂ (pairing3 (x₁ , x₂ , x₃)) ＝ x₂
pairing3→₂-pairing3 x₁ x₂ x₃ =
 ap (λ k → pr₁ (unpairing (pr₂ k))) (unpairing-pairing (x₁ , pairing (x₂ , x₃)))
 ∙ ap pr₁ (unpairing-pairing (x₂ , x₃))

＝pairing3→₂ : {x₁ x₂ : ℕ} → x₁ ＝ x₂ → pairing3→₂ x₁ ＝ pairing3→₂ x₂
＝pairing3→₂ {x₁} {x₂} refl = refl

pairing3→₃-pairing3 : (x₁ x₂ x₃ : ℕ) → pairing3→₃ (pairing3 (x₁ , x₂ , x₃)) ＝ x₃
pairing3→₃-pairing3 x₁ x₂ x₃ =
 ap (λ k → pr₂ (unpairing (pr₂ k))) (unpairing-pairing (x₁ , pairing (x₂ , x₃)))
 ∙ ap pr₂ (unpairing-pairing (x₂ , x₃))

＝pairing3→₃ : {x₁ x₂ : ℕ} → x₁ ＝ x₂ → pairing3→₃ x₁ ＝ pairing3→₃ x₂
＝pairing3→₃ {x₁} {x₂} refl = refl

pairing-inj : (p q : ℕ × ℕ) → pairing p ＝ pairing q → p ＝ q
pairing-inj p q h =
  (((unpairing-pairing p) ⁻¹) ∙ h1) ∙ (unpairing-pairing q)
  where
    h1 : unpairing (pairing p) ＝ unpairing (pairing q)
    h1 = ap unpairing h

unpairing＝ : (n : ℕ) → Σ x ꞉ ℕ , Σ y ꞉ ℕ , unpairing n ＝ (x , y)
unpairing＝ n with unpairing n
... | x , y = x , y , refl

fst-unpairing＝ : (n x y : ℕ) → unpairing n ＝ (x , y) → pr₁ (unpairing n) ＝ x
fst-unpairing＝ n x y u = ap pr₁ u

snd-unpairing＝ : (n x y : ℕ) → unpairing n ＝ (x , y) → pr₂ (unpairing n) ＝ y
snd-unpairing＝ n x y u = ap pr₂ u

pairing-unpairing : (n : ℕ) → pairing (unpairing n) ＝ n
pairing-unpairing 0 = refl
pairing-unpairing (succ n) with unpairing＝ n
... | succ x , y , p = {!!} --rewrite p = →s＝s (trans h1 (pairing-unpairing n))
  where
    h1 : y + succ ((y + x) + pairingAux (y + x)) ＝ pairing (unpairing n)
    h1 with unpairing n
    ... | a , b = {!!}
... | 0 , y , p = {!!} --rewrite p = →s＝s (trans h1 (pairing-unpairing n))
  where
    h1 : y + pairingAux y ＝ pairing (unpairing n)
    h1 with unpairing n
    ... | a , b = ap (λ k → y + pairingAux k) (+0 y ⁻¹) ∙ ap₂ (λ i j → pairing (i , j)) (pr₁ (＝pair→ p) ⁻¹) (pr₂ (＝pair→ p) ⁻¹)

unpairing-inj : (n m : ℕ) → unpairing n ＝ unpairing m → n ＝ m
unpairing-inj n m h =
  (((pairing-unpairing n) ⁻¹) ∙ h1) ∙ (pairing-unpairing m)
  where
    h1 : pairing (unpairing n) ＝ pairing (unpairing m)
    h1 = ap pairing h

+assoc-aux : (x y : ℕ) → x + x + (y + y) ＝ y + x + (y + x)
+assoc-aux x y = {!!}
{-
  rewrite +-comm y x
        | sym (+-assoc (x + y) x y)
        | +-assoc x y x
        | +-comm y x
        | sym (+-assoc x x y)
        | sym (+-assoc (x + x) y y)  = refl
-}

{-
pairing-spec-aux : (n x y : ℕ) → n ＝ y + x → pairing (x , y) * 2 ＝ y * 2 + n * suc n
pairing-spec-aux 0 x y h rewrite fst (+＝0→ y x (sym h)) | snd (+＝0→ y x (sym h)) = refl
pairing-spec-aux (suc n) 0 0 ()
pairing-spec-aux (suc n) (suc x) 0 h
  rewrite *-distribʳ-+ 2 x (pairingAux x)
        | sym (pairing-x0 x)
        | pairing-spec-aux n x 0 (suc-injective h)
        | suc-injective h
        | *-comm x 2
        | +0 x
        | *-suc x (suc x)
        | +-assoc x x (x * suc x)
  = refl
pairing-spec-aux (suc n) x (suc y) h
  rewrite *-distribʳ-+ 2 y (suc (y + x + pairingAux (y + x)))
        | +-comm y x
        | +-assoc x y (pairingAux (x + y))
        | *-distribʳ-+ 2 x (y + pairingAux (x + y))
        | +-comm x y
        | pairing-spec-aux n x y (suc-injective h)
        | suc-injective h
        | *-suc (y + x) (suc (y + x))
        | *-comm x 2
        | *-comm y 2
        | +0 y
        | +0 x
        | sym (+-assoc (y + x) (y + x) ((y + x) * suc (y + x)))
        | sym (+-assoc (x + x) (y + y) ((y + x) * suc (y + x)))
        | +assoc-aux x y = refl
-}

{-
pairing-spec : (x y : ℕ) → pairing (x , y) * 2 ＝ y * 2 + (y + x) * suc (y + x)
pairing-spec x y = pairing-spec-aux (y + x) x y refl
-}

{-
2∣+* : (x : ℕ) → 2 ∣ (x + x * x)
2∣+* 0 = divides 0 refl
2∣+* (suc x)
  rewrite *-suc x x
        | +-suc x (x + (x + x * x))
        | sym (+-assoc x x (x + x * x))
  with 2∣+* x
... | divides z q rewrite q = divides (1 + x + z) (→s＝s (→s＝s h1))
  where
    h1 : x + x + z * 2 ＝ (x + z) * 2
    h1 rewrite *-comm (x + z) 2
             | *-comm z 2
             | +0 z
             | +0 (x + z)
             | +-comm x z = +assoc-aux x z
-}

→＝+ₗ : {a b c : ℕ} → a ＝ b → a + c ＝ b + c
→＝+ₗ {a} {b} {c} refl = refl

{-
pairing-spec2 : (x y : ℕ) → pairing (x , y) ＝ y + (y + x) * suc (y + x) / 2
pairing-spec2 x y = trans (sym (m*n/n＝m (pairing (x , y)) 2)) (trans h1 h2)
  where
    h1 : (pairing (x , y) * 2) / 2 ＝ (y * 2 + (y + x) * suc (y + x)) / 2
    h1 rewrite sym (pairing-spec x y) = refl

    h3 : (y * 2 / 2) + ((y + x) + (y + x) * (y + x)) / 2 ＝ y + ((y + x) + (y + x) * (y + x)) / 2
    h3 = →＝+ₗ {y * 2 / 2} {y} {((y + x) + (y + x) * (y + x)) / 2} (m*n/n＝m y 2)

    h2 : (y * 2 + (y + x) * suc (y + x)) / 2 ＝ y + (y + x) * suc (y + x) / 2
    h2 rewrite *-suc (y + x) (y + x)
             | +-distrib-/-∣ʳ {y * 2} ((y + x) + (y + x) * (y + x)) {2} (2∣+* (y + x)) = h3
-}

{-
m≤m*m : (m : ℕ) → m ≤ m * m
m≤m*m 0 = ≤-refl
m≤m*m (suc m) = m≤m*n (suc m) (_≤_.s≤s _≤_.z≤n)
-}

{-
≤/2 : (y : ℕ) → y ≤ y * suc y / 2
≤/2 y rewrite *-suc y y = ≤-trans h1 h2
  where
    h0 : y ＝ y * 2 / 2
    h0 = sym (m*n/n＝m y 2)

    h1 : y ≤ y * 2 / 2
    h1 rewrite sym h0 = ≤-refl

    h3 : y * 2 ≤ y + y * y
    h3 rewrite *-suc y 1 | *-suc y 0 | *-zeroʳ y | +0 y = +-mono-≤ {y} {y} {y} {y * y} ≤-refl (m≤m*m y)

    h2 : y * 2 / 2 ≤ (y + (y * y)) / 2
    h2 = /-mono-≤ {y * 2} {y + (y * y)} {2} h3 ≤-refl
-}

{-
→≤/2 : (x y : ℕ) → x ≤ y → x ≤ y * suc y / 2
→≤/2 x y h = ≤-trans h (≤/2 y)
-}

{-
pairing-non-dec : (x y : ℕ) → y + x ≤ pairing (x , y)
pairing-non-dec x y
  rewrite pairing-spec2 x y
  = +-mono-≤ {y} {y} {x} {(y + x) * suc (y + x) / 2} ≤-refl h1
  where
    h1 : x ≤ (y + x) * suc (y + x) / 2
    h1 = →≤/2 x (y + x) (m≤n+m x y)
-}

#cons : ℕ
#cons = 8

#cons-1 : ℕ
#cons-1 = 7

encode : {Γ : Cxt} {σ : type} → QT Γ σ → ℕ
encode {Γ} {.ι} Zero = 0
encode {Γ} {.ι} (Succ t) = {!1 + encode t * #cons!}
encode {Γ} {σ} (Rec t t₁ t₂) = {!!}
encode {Γ} {σ} (ν i) = {!!}
encode {Γ} {σ ⇒ τ} (ƛ t) = {!!}
encode {Γ} {σ} (t · t₁) = {!!}
encode {Γ} {.ι} (Quote t) = {!!}
encode {Γ} {σ} (Unquote t) = {!!}

\end{code}
