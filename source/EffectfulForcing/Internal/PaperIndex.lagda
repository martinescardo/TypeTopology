\begin{code}

module EffectfulForcing.Internal.PaperIndex where

open import EffectfulForcing.Internal.Correctness
open import EffectfulForcing.Internal.SystemT
open import EffectfulForcing.Internal.External
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import EffectfulForcing.MFPSAndVariations.SystemT using (type;〖_〗; ι; _⇒_)
open import MLTT.Sigma
open import MLTT.Spartan

\end{code}

\section{A System T Primer}

\begin{code}

Definition-1 : 𝓤₀  ̇
Definition-1 = Σ Γ ꞉ Cxt , Σ σ ꞉ type , T Γ σ

Definition-2 : {Γ : Cxt} {σ : type}
             → T Γ σ
             → (【 Γ 】 → 〖 σ 〗)
Definition-2 = ⟦_⟧

Definition-3 : {Γ : Cxt} → ℕ → T Γ ι
Definition-3 = numeral

Proposition-4 : {Γ : Cxt} (γ : 【 Γ 】) (n : ℕ) → n ＝ ⟦ numeral n ⟧ γ
Proposition-4 γ n = ⟦numeral⟧ γ n ⁻¹

\end{code}

\section{Oracless Effectful Forcing}

\begin{code}

Definition-5 : (I : 𝓤 ̇ ) →  (O : 𝓥  ̇ ) → (X : 𝓦  ̇) → 𝓤 ⊔ 𝓥 ⊔ 𝓦  ̇
Definition-5 = D

Definition-6 : {I : 𝓤  ̇} {O : 𝓥  ̇} {X : 𝓦  ̇} → D I O X → (I → O) → X
Definition-6 = dialogue

-- Definition-7a : {I : 𝓤  ̇} {O : 𝓥  ̇} {X : 𝓦  ̇}
--               → ((I → O) → X)
--               → {!!}
-- Definition-7a f = {!!}

\end{code}

\begin{code}

Definition-9 : {X : 𝓤  ̇} {Y : 𝓥  ̇} → (X → B Y) → B X → B Y
Definition-9 = kleisli-extension

Definition-10 : {X Y : 𝓤₀  ̇}
              → (X → Y)
              → B X
              → B Y
Definition-10 f = kleisli-extension (η ∘ f)

-- Definition-11 : {!!}
-- Definition-11 = {!!}

Definition-13 : B ℕ → B ℕ
Definition-13 = generic

Definition-14 : T₀ ((ι ⇒ ι) ⇒ ι) → B ℕ
Definition-14 = dialogue-tree

\end{code}
