/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Init.Data.Rat.Basic

abbrev Qsqrtd (d : ℚ) : Type := QuadraticAlgebra ℚ d 0

-- star norm and trace on Qsqrtd
namespace Qsqrtd
-- star
abbrev trace (x : Qsqrtd d) : ℚ := x.re + (star x).re
abbrev norm {d : ℚ} (x : Qsqrtd d) : ℚ := QuadraticAlgebra.norm x
abbrev embed (r : ℚ) : Qsqrtd d := algebraMap ℚ (Qsqrtd d) r
end Qsqrtd
