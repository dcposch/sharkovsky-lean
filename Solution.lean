/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch
-/
import Sharkovsky
import Mathlib

/-!
# Proved solution

Comparator matches the identically named declaration in `Challenge.lean`.
-/

open Function Set

namespace Sharkovsky

theorem period_three_implies_all_periods
    {f : ℝ → ℝ} {I : Set ℝ} [OrdConnected I]
    (hf : ContinuousOn f I) (hI : MapsTo f I I)
    {x : ℝ} (hxI : x ∈ I) (hx : minimalPeriod f x = 3)
    {n : ℕ} (hn : 0 < n) :
    ∃ y ∈ I, minimalPeriod f y = n :=
  period_three_all hf hI hxI hx hn

end Sharkovsky
