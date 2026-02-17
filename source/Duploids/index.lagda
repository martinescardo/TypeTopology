Jon Sterling, 16 Dec 2022

The goal of this library is to explore the theory of *duploids*, a categorical
semantics that unifies polarized sequent calculus, call-by-push-value, and
abstract machines. Duploids are introduced in the following paper:

   Munch-Maccagnoni, G. (2014). Models of a Non-associative Composition. In:
   Muscholl, A. (eds) Foundations of Software Science and Computation
   Structures. FoSSaCS 2014. Lecture Notes in Computer Science, vol
   8412. Springer, Berlin, Heidelberg.

   https://doi.org/10.1007/978-3-642-54830-7_26


A duploid is a generalization of a category that relaxes the associativity
condition in a way that is compatible with the viewpoint of morphisms as
*effectful* programs.

A "thunkable" morphism is one that satisfies an associativity law for
precomposition (being fed into other programs as input), whereas a "linear"
morphism is one that satisfies an associativity law for postcomposition
(consuming the outputs of other programs).

An object is "positive" when every map out of it is linear, and an object is
"negative" when every map into it is thunkable. A thunkable map between positive
objects corresponds a *value* in call-by-push-value, whereas a linear map
between negative objects corresponds to a *stack* in call-by-push-value. The
duploid analysis of polarity is, however, more refined than that of
call-by-push-value because we may speak directly of linear and thunkable maps
between objects regardless of their polarity. Thus in comparison to
call-by-push-value, the duploid perspective better explains the behavior of both
$λ$-abstractions (which are like "negative values") and case-expressions (which
are like "positive stacks").

Duploids have connectives (called "shifts") that take positive objects to
negative objects, and vice versa. From a duploid, it is possible to define the
*category* of positive objects and thunkable maps, and likewise the category of
negative objects and linear maps, and these shifts produce an adjunction between
these two categories reminiscent of call-by-push-value. We can reconstruct the
original duploid from this adjunction, by taking morphisms of the duploid to be
the oblique maps in the adjunction.

The Kleisli category for the induced monad is then the wide subcategory of the
duploid spanned by positive objects; the Kleisli category for the induced
comonad is the wide subcategory of the duploid spanned by negative objects. The
shifts again induce an adjunction between these two categories, but the
adjunction is flipped from the usual call-by-push-value direction: the shift
from positive to negative is a right adjoint rather than a left adjoint.

Every adjunction that arises from a duploid has a special "equalizing"
requirement that is similar to the condition in Moggi's monadic metalanguage
that the unit shall be a monomorphism. These adjunctions correspond exactly to
duploids, and they are reflective in the category of all adjunctions.

One of the initial goals of this development is to work out the details of this
structure theorem in a univalent setting.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Duploids.index where

import Duploids.DeductiveSystem
import Duploids.Depolarization
import Duploids.Preduploid
import Duploids.Duploid

\end{code}
