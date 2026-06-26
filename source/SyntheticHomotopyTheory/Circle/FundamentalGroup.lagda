Tom de Jong, 19 June 2026.

Updated 26 June 2026 to work with fewer definitional computation rules
(cf. the file Circle.WithRewriting).

We show that the loop space of the circle is equivalent to the integers via the
mapping k : ℤ ↦ loopᵏ : pt ＝ pt.

\begin{code}

{-# OPTIONS --rewriting --without-K #-}

open import MLTT.Spartan
open import UF.Univalence

module SyntheticHomotopyTheory.Circle.FundamentalGroup
        (ua : is-univalent 𝓤₀)
       where

open import UF.FunExt
open import UF.UA-FunExt

private
 fe : funext 𝓤₀ 𝓤₀
 fe = univalence-gives-funext ua

open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Singleton-Properties
open import UF.Subsingletons
open import UF.Yoneda

open import SyntheticHomotopyTheory.Circle.Integers
open import SyntheticHomotopyTheory.Circle.Integers-Properties
open import SyntheticHomotopyTheory.Circle.Integers-SymmetricInduction
open import SyntheticHomotopyTheory.Circle.WithRewriting

\end{code}

We use what Egbert Rijke calls the fundamental theorem of identity types.
We construct a type family C over S¹ whose total space is contractible.

Informally, C is defined by:
 C (pt)   := ℤ               : 𝓤₀ ̇
 C (loop) := eqtoid succ-ℤ-≃ : ℤ ＝ ℤ

\begin{code}

private
 𝕤 : ℤ ＝ ℤ
 𝕤 = eqtoid ua ℤ ℤ succ-ℤ-≃

 C : S¹ → 𝓤₀ ̇
 C = S¹-recursion (𝓤₀ ̇ ) ℤ 𝕤

 C-on-loop : ap C loop ＝ 𝕤
 C-on-loop = S¹-recursion-comp-loop (𝓤₀ ̇ ) ℤ 𝕤

 C-transport-loop-is-succ : transport C loop ＝ succ-ℤ
 C-transport-loop-is-succ =
  transport C loop                        ＝⟨ I   ⟩
  idtofun (C pt) (C pt) (ap C loop)       ＝⟨refl⟩
  ⌜ idtoeq ℤ ℤ (ap C loop) ⌝              ＝⟨ II ⟩
  ⌜ idtoeq ℤ ℤ 𝕤 ⌝                        ＝⟨refl⟩
  ⌜ idtoeq ℤ ℤ (eqtoid ua ℤ ℤ succ-ℤ-≃) ⌝ ＝⟨ III ⟩
  ⌜ succ-ℤ-≃ ⌝                            ＝⟨refl⟩
  succ-ℤ                                  ∎
   where
    I   = transport-is-idtofun-after-ap C loop
    II  = ap (λ - → ⌜ idtoeq ℤ ℤ - ⌝) C-on-loop
    III = ap ⌜_⌝ (idtoeq-eqtoid ua ℤ ℤ succ-ℤ-≃)

 C-transport-loop⁻¹-is-pred : transport C (loop ⁻¹) ＝ pred-ℤ
 C-transport-loop⁻¹-is-pred =
  transport C (loop ⁻¹)                           ＝⟨ I   ⟩
  idtofun (C pt) (C pt) (ap C (loop ⁻¹))          ＝⟨ II  ⟩
  idtofun (C pt) (C pt) ((ap C loop) ⁻¹)          ＝⟨ III ⟩
  idtofun ℤ ℤ (𝕤 ⁻¹)                              ＝⟨ IV  ⟩
  ⌜ idtoeq ℤ ℤ (eqtoid ua ℤ ℤ (≃-sym succ-ℤ-≃)) ⌝ ＝⟨ V   ⟩
  ⌜ ≃-sym succ-ℤ-≃ ⌝                              ＝⟨refl⟩
  pred-ℤ                                          ∎
   where
    I   = transport-is-idtofun-after-ap C (loop ⁻¹)
    II  = ap (idtofun (C pt) (C pt)) ((ap-sym C loop) ⁻¹)
    III = ap (λ - → idtofun ℤ ℤ (- ⁻¹)) C-on-loop
    IV  = ap (idtofun ℤ ℤ) (eqtoid-inverse ua succ-ℤ-≃)
    V   = ap ⌜_⌝ (idtoeq-eqtoid ua ℤ ℤ (≃-sym succ-ℤ-≃))

\end{code}

We show that the total space of C is contractible by showing that it has the
universal property of singleton types.

\begin{code}

 ΣC-mapping-out-≃ : (X : 𝓤₀ ̇ ) → ((Σ s ꞉ S¹ , C s) → X) ≃ X
 ΣC-mapping-out-≃ X =
  ((Σ s ꞉ S¹ , C s) → X)                                  ≃⟨ I   ⟩
  (Π s ꞉ S¹ , (C s → X))                                  ≃⟨ II  ⟩
  (Σ f ꞉ (ℤ → X) , transport (λ - → C - → X) loop f ＝ f) ≃⟨ III ⟩
  (Σ f ꞉ (ℤ → X) , f ∘ transport C (loop ⁻¹) ＝ f)        ≃⟨ IV  ⟩
  (Σ f ꞉ (ℤ → X) , f ∘ pred-ℤ ＝ f)                       ≃⟨ V   ⟩
  X                                                       ■
   where
    I   = curry-uncurry' fe fe
    II  = S¹-dependent-universal-property-≃ fe (λ s → C s → X)
    III = Σ-cong (λ f → ＝-cong-l _ _ ( transport-along-→' C loop f))
    IV  = Σ-cong (λ f → ＝-cong-l _ _ (ap (f ∘_) C-transport-loop⁻¹-is-pred))
    V   = maps-equalizing-pred-ℤ-and-id-≃ fe X

\end{code}

The following definitional equality allows us to directly apply
≃-2-out-of-3-left in the contractibility proof.

\begin{code}

 observation : (X : 𝓤₀ ̇ ) → ⌜ ΣC-mapping-out-≃ X ⌝ ∘ (consts (Σ C) X) ∼ id
 observation X x = refl

 ΣC-is-singleton : is-singleton (Σ s ꞉ S¹ , C s)
 ΣC-is-singleton =
  singleton-if-universal-property⁻
   (λ X → ≃-2-out-of-3-left ⌜ ΣC-mapping-out-≃ X ⌝-is-equiv (id-is-equiv X))

\end{code}

We choose our equivalence so that refl gets send to 𝟎 : ℤ.

\begin{code}

 φ : (s : S¹) → pt ＝ s → C s
 φ s refl = 𝟎

\end{code}

The result now follows from the fundamental theorem of identity types,
a.k.a. Yoneda-Theorem-forth from UF.Yoneda.

\begin{code}

loop-space-is-ℤ : (pt ＝ pt) ≃ ℤ
loop-space-is-ℤ = φ pt , Yoneda-Theorem-forth pt φ ΣC-is-singleton pt

\end{code}

We now prove that the inverse of the above equivalence is given by k ↦ loopᵏ.

\begin{code}

private
 ϕ = ⌜ loop-space-is-ℤ ⌝

 _ : ϕ ＝ φ pt
 _ = refl

 _ : ϕ refl ＝ 𝟎
 _ = refl

\end{code}

The key is that any map like φ is natural w.r.t. transports and that transport
in the identity type pt ＝ s is given by path composition, the proof of which we
inline via a direct proof by path induction for our particular instance.

\begin{code}

 φ-naturality : {s₁ s₂ : S¹} (p : s₁ ＝ s₂) (q : pt ＝ s₁)
              → transport C p (φ s₁ q) ＝ φ s₂ (q ∙ p)
 φ-naturality refl q = refl

 ϕ-on-concatenated-loop : (q : pt ＝ pt) → ϕ (q ∙ loop) ＝ succ-ℤ (ϕ q)
 ϕ-on-concatenated-loop q =
  ϕ (q ∙ loop)           ＝⟨ (φ-naturality loop q) ⁻¹ ⟩
  transport C loop (ϕ q) ＝⟨ happly C-transport-loop-is-succ (ϕ q) ⟩
  succ-ℤ (ϕ q)           ∎

 ϕ-on-concatenated-loop⁻¹ : (q : pt ＝ pt) → ϕ (q ∙ loop ⁻¹) ＝ pred-ℤ (ϕ q)
 ϕ-on-concatenated-loop⁻¹ q =
  ϕ (q ∙ loop ⁻¹)             ＝⟨ (φ-naturality (loop ⁻¹) q) ⁻¹ ⟩
  transport C (loop ⁻¹) (ϕ q) ＝⟨ happly C-transport-loop⁻¹-is-pred (ϕ q) ⟩
  pred-ℤ (ϕ q)                ∎

\end{code}

Indeed, the promised result now follows swiftly.

\begin{code}

loop^ : (n : ℕ) → pt ＝ pt
loop^ 0 = refl
loop^ (succ n) = loop^ n ∙ loop

ϕ-loop-iterated : (n : ℕ) → ϕ (loop^ n) ＝ ℕ-to-ℤ₊ n
ϕ-loop-iterated zero = refl
ϕ-loop-iterated (succ n) =
 ϕ (loop^ n ∙ loop)   ＝⟨ ϕ-on-concatenated-loop (loop^ n) ⟩
 succ-ℤ (ϕ (loop^ n)) ＝⟨ ap succ-ℤ (ϕ-loop-iterated n) ⟩
 succ-ℤ (ℕ-to-ℤ₊ n)   ＝⟨ (ℕ-to-ℤ₊-on-succ n) ⁻¹ ⟩
 ℕ-to-ℤ₊ (succ n)     ∎

loop^⁻ : (n : ℕ) → pt ＝ pt
loop^⁻ 0 = refl
loop^⁻ (succ n) = loop^⁻ n ∙ (loop ⁻¹)

ϕ-loop⁻¹-iterated : (n : ℕ) → ϕ (loop^⁻ n) ＝ ℕ-to-ℤ₋ n
ϕ-loop⁻¹-iterated zero = refl
ϕ-loop⁻¹-iterated (succ n) =
 ϕ (loop^⁻ n ∙ (loop ⁻¹)) ＝⟨ ϕ-on-concatenated-loop⁻¹ (loop^⁻ n) ⟩
 pred-ℤ (ϕ (loop^⁻ n))    ＝⟨ ap pred-ℤ (ϕ-loop⁻¹-iterated n) ⟩
 pred-ℤ (ℕ-to-ℤ₋ n)       ＝⟨ (ℕ-to-ℤ₋-on-succ n) ⁻¹ ⟩
 ℕ-to-ℤ₋ (succ n)         ∎

loop^ℤ : (k : ℤ) → pt ＝ pt
loop^ℤ 𝟎 = refl
loop^ℤ (pos i) = loop^ (succ i)
loop^ℤ (neg i) = loop^⁻ (succ i)

ϕ-loop^ℤ : (k : ℤ) → ϕ (loop^ℤ k) ＝ k
ϕ-loop^ℤ 𝟎 = refl
ϕ-loop^ℤ (pos i) = ϕ-loop-iterated (succ i)
ϕ-loop^ℤ (neg i) = ϕ-loop⁻¹-iterated (succ i)

\end{code}