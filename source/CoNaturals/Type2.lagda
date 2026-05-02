\begin{code}

{-# OPTIONS --safe --without-K #-}

module CoNaturals.Type2 where

open import TypeTopology.GenericConvergentSequence2
     renaming (
      ℕ∞'                   to ℕ∞ ;
      ℕ-to-ℕ∞'              to ℕ-to-ℕ∞ ;
      is-finite'            to is-finite ;
      size'                 to size ;
      being-finite'-is-prop to being-finite-is-prop ;
      ℕ∞'-to-ℕ→𝟚            to ℕ∞-to-ℕ→𝟚 ;
      ∞'                    to ∞ ;
      is-infinite-∞'        to is-infinite-∞ ;
      ℕ-to-ℕ∞'-is-finite'   to ℕ-to-ℕ∞-is-finite
      )
     public

open import CoNaturals.Type2Properties
             renaming (
              ℕ-to-ℕ∞'-diagonal      to ℕ-to-ℕ∞-diagonal ;
              ℕ∞'-equality-criterion to ℕ∞-equality-criterion ;
              ℕ-to-ℕ∞'-lc            to ℕ-to-ℕ∞-lc ;
              finite'-isolated       to finite-isolated ;
              size'-property'        to size-property
             )
     public

\end{code}
