-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K #-}

module InfinitePigeon.J-PigeonProgram where

open import InfinitePigeon.Cantor
open import InfinitePigeon.DataStructures
open import InfinitePigeon.J-FinitePigeon
open import InfinitePigeon.Logic
open import InfinitePigeon.Naturals
open import InfinitePigeon.Two

-- Given an infinite boolean sequence α and a natural number m, find a
-- boolean b and a finite list of length n with the indices of a
-- finite constant subsequence of α with value b at all
-- positions.
--
-- This is usually how such programs are specified in functional
-- programming (if they are at all). Here Theorem (defined in the
-- module FinitePigeon) is the program with the formal specification,
-- also formally checked. Once this is done we can erase the
-- specification.

pigeon-program : ₂ℕ →  ℕ  →  ₂  ×  List ℕ
pigeon-program α m = f(Theorem α m)
 where f : Finite-Pigeonhole α m → ₂ × List ℕ
       f(∃-intro b (∃-intro s proof)) = (b , list s)
