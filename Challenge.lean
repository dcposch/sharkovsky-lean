/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch
-/
import Mathlib

/-!
# Period three implies all periods

Li and Yorke (1975) proved that a continuous interval map with a point of
least period 3 has a point of least period `n` for every `n ≥ 1`. The same
statement is the first case of Sharkovsky’s forcing theorem (1964): 3 is
maximal in the Sharkovsky order, so a period-3 orbit forces every other
least period.

This file is the audited statement surface. The argument is a two-interval
intermediate-value covering; it does not prove the full Sharkovsky order
or the Li–Yorke scrambled set.
-/

open Function Set

namespace Sharkovsky

/-- **Li–Yorke 1975 / Sharkovsky 1964 (period 3).** If a continuous self-map
of an interval has a point of least period 3, then it has a point of least
period `n` for every positive integer `n`. -/
theorem period_three_implies_all_periods
    {f : ℝ → ℝ} {I : Set ℝ} [OrdConnected I]
    (hf : ContinuousOn f I) (hI : MapsTo f I I)
    {x : ℝ} (hxI : x ∈ I) (hx : minimalPeriod f x = 3)
    {n : ℕ} (hn : 0 < n) :
    ∃ y ∈ I, minimalPeriod f y = n := by
  sorry

end Sharkovsky
