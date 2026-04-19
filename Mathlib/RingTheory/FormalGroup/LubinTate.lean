/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.FormalGroup.Basic

/-! # Lubin-Tate formal group laws

Let `R` be a commutative ring, a one dimensional formal group law is a formal power series
`F(X,Y) ∈ R⟦X,Y⟧` such that
· `F(X,Y) = X + Y + higher order terms`.
· `F(F(X,Y),Z) = F(X,F(Y,Z))`.

Under this definition, we can prove that `F(X,0) = X` and `F(0,X) = X`. Moreover, there is a
unique power series `i(X)` such that `F(X, i(X)) = 0`, which is considered to be the inverse
of the formal group law `F(X,Y)`.

## Main definitions/lemmas

* Definition of one dimensional formal group law.

* Properties: `F(X,0) = 0` and `F(0,X) = X`.

* Additive formal group laws and multiplicative formal group laws.

* Instance: Group instance defined by the formal group law `F` over the ideal
  `PowerSeries.hasEvalIdeal`.

## References
* [Hazewinkel, Michiel. Formal Groups and Applications][hazewinkel1978]

-/

@[expose] public section
