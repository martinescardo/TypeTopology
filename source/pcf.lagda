To de Jong & Martin Escardo, 20 May 2019.

Combinatory version of Platek-Scott-Plotkin PCF.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

data type : Set where
  ι   : type
  _⇒_ : type → type → type

data PCF : (σ : type) → Set where
  Zero   : PCF ι
  Succ   : PCF(ι ⇒ ι)
  Pred   : PCF(ι ⇒ ι)
  ifZero : PCF (ι ⇒ ι ⇒ ι ⇒ ι)
  Fix    : {σ : type}     → PCF((σ ⇒ σ) ⇒ σ)
  K      : {σ τ : type}   → PCF(σ ⇒ τ ⇒ σ)
  S      : {ρ σ τ : type} → PCF((ρ ⇒ σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ ρ ⇒ τ)
  _·_    : {σ τ : type}   → PCF(σ ⇒ τ) → PCF σ → PCF τ

infixr 1 _⇒_
infixl 1 _·_

\end{code}
