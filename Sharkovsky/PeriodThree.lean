/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch
-/
import Mathlib

/-!
# Period three implies all periods

A short intermediate-value argument that a continuous interval map with a
point of least period 3 has a point of least period `n` for every `n ≥ 1`.
This is the period-3 case of Sharkovsky’s theorem (1964) and the periodic-point
half of Li–Yorke (1975). The full Sharkovsky order and the Li–Yorke scrambled
set are not proved here.
-/

open Function Set

namespace Sharkovsky

variable {f : ℝ → ℝ}

/-- The equalizer of a continuous-on-Icc map with a constant is compact. -/
private lemma isCompact_eqOn_Icc {s t d : ℝ} (hf : ContinuousOn f (Icc s t)) :
    IsCompact {x : ℝ | x ∈ Icc s t ∧ f x = d} := by
  let Z : Set (Icc s t) := (Icc s t).restrict f ⁻¹' {d}
  have hZcl : IsClosed Z :=
    isClosed_singleton.preimage (continuousOn_iff_continuous_restrict.mp hf)
  have himg : Subtype.val '' Z = {x : ℝ | x ∈ Icc s t ∧ f x = d} := by
    ext x
    constructor
    · rintro ⟨⟨y, hy⟩, hfy, rfl⟩
      exact ⟨hy, hfy⟩
    · rintro ⟨hx, hfx⟩
      exact ⟨⟨x, hx⟩, hfx, rfl⟩
  exact himg ▸ hZcl.isCompact.image continuous_subtype_val

/-- If `J ⊆ f(I)` for closed intervals, a closed subinterval of `I` maps onto `J`. -/
private lemma exists_subinterval_image_eq {s t c d : ℝ} (_hst : s ≤ t) (hcd : c ≤ d)
    (hf : ContinuousOn f (Icc s t)) (hcover : Icc c d ⊆ f '' Icc s t) :
    ∃ p q, p ≤ q ∧ Icc p q ⊆ Icc s t ∧ f '' Icc p q = Icc c d := by
  obtain ⟨u, hu, hfu⟩ := hcover (left_mem_Icc.2 hcd)
  obtain ⟨v, hv, hfv⟩ := hcover (right_mem_Icc.2 hcd)
  rcases le_total u v with huv | hvu
  · -- `f u = c`, `f v = d`, `u ≤ v`: first hit of `d`, last hit of `c`.
    have hfuv : ContinuousOn f (Icc u v) := hf.mono (Icc_subset_Icc hu.1 hv.2)
    let S : Set ℝ := {x | x ∈ Icc u v ∧ f x = d}
    have hSne : S.Nonempty := ⟨v, ⟨right_mem_Icc.2 huv, hfv⟩⟩
    have hScp : IsCompact S := isCompact_eqOn_Icc hfuv
    let q := sInf S
    have hqS : q ∈ S := hScp.sInf_mem hSne
    have hqI : q ∈ Icc u v := hqS.1
    have hfq : f q = d := hqS.2
    have hf_le_d : ∀ x ∈ Icc u q, f x ≤ d := by
      intro x hx
      by_contra hxgt
      have hxgt : d < f x := lt_of_not_ge hxgt
      have hxlt : x < q := lt_of_le_of_ne hx.2 (by intro h; exact hxgt.ne' (h ▸ hfq))
      have hfIx : ContinuousOn f (Icc u x) :=
        hfuv.mono (Icc_subset_Icc le_rfl (hx.2.trans hqI.2))
      have hdmem : d ∈ Icc (f u) (f x) := ⟨hfu ▸ hcd, hxgt.le⟩
      obtain ⟨y, hy, hyf⟩ := (intermediate_value_Icc hx.1 hfIx) hdmem
      have hyS : y ∈ S := ⟨⟨hy.1, hy.2.trans (hx.2.trans hqI.2)⟩, hyf⟩
      exact (lt_of_le_of_lt hy.2 hxlt).not_ge (csInf_le hScp.bddBelow hyS)
    let T : Set ℝ := {x | x ∈ Icc u q ∧ f x = c}
    have hTne : T.Nonempty := ⟨u, ⟨left_mem_Icc.2 hqI.1, hfu⟩⟩
    have hTcp : IsCompact T :=
      isCompact_eqOn_Icc (hfuv.mono (Icc_subset_Icc le_rfl hqI.2))
    let p := sSup T
    have hpT : p ∈ T := hTcp.sSup_mem hTne
    have hpI : p ∈ Icc u q := hpT.1
    have hfp : f p = c := hpT.2
    have hpq : p ≤ q := hpI.2
    have hf_ge_c : ∀ x ∈ Icc p q, c ≤ f x := by
      intro x hx
      by_contra hxlt
      have hxlt : f x < c := lt_of_not_ge hxlt
      have hpx : p < x := lt_of_le_of_ne hx.1 (by intro h; exact hxlt.ne (h ▸ hfp))
      have hfIq : ContinuousOn f (Icc x q) :=
        hfuv.mono (Icc_subset_Icc (hpI.1.trans hx.1) hqI.2)
      have hcmem : c ∈ Icc (f x) (f q) := ⟨hxlt.le, hfq ▸ hcd⟩
      obtain ⟨y, hy, hyf⟩ := (intermediate_value_Icc hx.2 hfIq) hcmem
      have hyT : y ∈ T := ⟨⟨hpI.1.trans (hx.1.trans hy.1), hy.2⟩, hyf⟩
      exact (lt_of_lt_of_le hpx hy.1).not_ge (le_csSup hTcp.bddAbove hyT)
    have hmaps : MapsTo f (Icc p q) (Icc c d) := fun x hx =>
      ⟨hf_ge_c x hx, hf_le_d x ⟨hpI.1.trans hx.1, hx.2⟩⟩
    have hsurj : SurjOn f (Icc p q) (Icc c d) := by
      simpa [hfp, hfq] using
        (hfuv.mono (Icc_subset_Icc hpI.1 hqI.2)).surjOn_Icc
          (left_mem_Icc.2 hpq) (right_mem_Icc.2 hpq)
    refine ⟨p, q, hpq, Icc_subset_Icc hpI.1 hqI.2 |>.trans (Icc_subset_Icc hu.1 hv.2),
      subset_antisymm hmaps.image_subset hsurj⟩
  · -- `v ≤ u`: `f v = d`, `f u = c`. First hit of `c`, last hit of `d`.
    have hfvu : ContinuousOn f (Icc v u) := hf.mono (Icc_subset_Icc hv.1 hu.2)
    let S : Set ℝ := {x | x ∈ Icc v u ∧ f x = c}
    have hSne : S.Nonempty := ⟨u, ⟨right_mem_Icc.2 hvu, hfu⟩⟩
    have hScp : IsCompact S := isCompact_eqOn_Icc hfvu
    let p := sInf S
    have hpS : p ∈ S := hScp.sInf_mem hSne
    have hpI : p ∈ Icc v u := hpS.1
    have hfp : f p = c := hpS.2
    have hf_ge_c : ∀ x ∈ Icc v p, c ≤ f x := by
      intro x hx
      by_contra hxlt
      have hxlt : f x < c := lt_of_not_ge hxlt
      have hxlt' : x < p := lt_of_le_of_ne hx.2 (by intro h; exact hxlt.ne (h ▸ hfp))
      have hfIx : ContinuousOn f (Icc v x) :=
        hfvu.mono (Icc_subset_Icc le_rfl (hx.2.trans hpI.2))
      have hcmem : c ∈ Icc (f x) (f v) := ⟨hxlt.le, hfv ▸ hcd⟩
      obtain ⟨y, hy, hyf⟩ := (intermediate_value_Icc' hx.1 hfIx) hcmem
      have hyS : y ∈ S := ⟨⟨hy.1, hy.2.trans (hx.2.trans hpI.2)⟩, hyf⟩
      exact (lt_of_le_of_lt hy.2 hxlt').not_ge (csInf_le hScp.bddBelow hyS)
    let T : Set ℝ := {x | x ∈ Icc v p ∧ f x = d}
    have hTne : T.Nonempty := ⟨v, ⟨left_mem_Icc.2 hpI.1, hfv⟩⟩
    have hTcp : IsCompact T :=
      isCompact_eqOn_Icc (hfvu.mono (Icc_subset_Icc le_rfl hpI.2))
    let q := sSup T
    have hqT : q ∈ T := hTcp.sSup_mem hTne
    have hqI : q ∈ Icc v p := hqT.1
    have hfq : f q = d := hqT.2
    have hqp : q ≤ p := hqI.2
    have hf_le_d : ∀ x ∈ Icc q p, f x ≤ d := by
      intro x hx
      by_contra hxgt
      have hxgt : d < f x := lt_of_not_ge hxgt
      have hqx : q < x := lt_of_le_of_ne hx.1 (by intro h; exact hxgt.ne' (h ▸ hfq))
      have hfIx : ContinuousOn f (Icc x p) :=
        hfvu.mono (Icc_subset_Icc (hqI.1.trans hx.1) hpI.2)
      have hdmem : d ∈ Icc (f p) (f x) := ⟨hfp ▸ hcd, hxgt.le⟩
      obtain ⟨y, hy, hyf⟩ := (intermediate_value_Icc' hx.2 hfIx) hdmem
      have hyT : y ∈ T := ⟨⟨hqI.1.trans (hx.1.trans hy.1), hy.2⟩, hyf⟩
      exact (hqx.trans_le hy.1).not_ge (le_csSup hTcp.bddAbove hyT)
    have hmaps : MapsTo f (Icc q p) (Icc c d) := fun x hx =>
      ⟨hf_ge_c x ⟨hqI.1.trans hx.1, hx.2⟩, hf_le_d x hx⟩
    have hsurj : SurjOn f (Icc q p) (Icc c d) := by
      simpa [hfp, hfq] using
        (hfvu.mono (Icc_subset_Icc hqI.1 hpI.2)).surjOn_Icc
          (right_mem_Icc.2 hqp) (left_mem_Icc.2 hqp)
    refine ⟨q, p, hqp, Icc_subset_Icc hqI.1 hpI.2 |>.trans (Icc_subset_Icc hv.1 hu.2),
      subset_antisymm hmaps.image_subset hsurj⟩

/-- Index `-k` in `Fin n`. -/
private def loopIdx {n : ℕ} (hn : 0 < n) (k : ℕ) : Fin n :=
  ⟨(n - k % n) % n, Nat.mod_lt _ hn⟩

/-- Successor on `Fin n` that is defined even when `n = 1`. -/
private def finSucc {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

private lemma loopIdx_zero {n : ℕ} (hn : 0 < n) :
    loopIdx hn 0 = ⟨0, hn⟩ := by
  simp [loopIdx]

private lemma loopIdx_n {n : ℕ} (hn : 0 < n) :
    loopIdx hn n = ⟨0, hn⟩ := by
  simp [loopIdx]

private lemma loopIdx_succ {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : k < n) :
    loopIdx hn k = finSucc hn (loopIdx hn (k + 1)) := by
  refine Fin.ext ?_
  simp only [loopIdx, finSucc]
  rw [Nat.mod_eq_of_lt hk]
  by_cases hlast : k + 1 = n
  · rw [hlast, Nat.mod_self]
    have hk' : k = n - 1 := by omega
    rw [hk']
    have : n - (n - 1) = 1 := by omega
    rw [this, Nat.sub_zero, Nat.mod_self, zero_add]
  · have hk1 : k + 1 < n := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hk) hlast
    rw [Nat.mod_eq_of_lt hk1]
    rcases k.eq_zero_or_pos with rfl | hkpos
    · rw [Nat.sub_zero, Nat.mod_self, Nat.zero_add]
      have : n - 1 < n := Nat.sub_lt hn one_pos
      rw [Nat.mod_eq_of_lt this, Nat.sub_add_cancel (Nat.succ_le_of_lt hn), Nat.mod_self]
    · have hnk : n - k < n := Nat.sub_lt hn hkpos
      have hnk1 : n - (k + 1) < n := Nat.sub_lt hn (Nat.succ_pos _)
      rw [Nat.mod_eq_of_lt hnk, Nat.mod_eq_of_lt hnk1]
      have : n - (k + 1) + 1 = n - k := by omega
      rw [this, Nat.mod_eq_of_lt hnk]

/-- A loop of interval coverings yields a periodic point with that itinerary. -/
private lemma exists_periodic_pt_of_covering_loop {I : Set ℝ}
    (hf : ContinuousOn f I) (hmap : MapsTo f I I) {n : ℕ} (hn : 0 < n)
    (left right : Fin n → ℝ) (hle : ∀ i, left i ≤ right i)
    (hsub : ∀ i, Icc (left i) (right i) ⊆ I)
    (hcov : ∀ i, Icc (left (finSucc hn i)) (right (finSucc hn i)) ⊆
        f '' Icc (left i) (right i)) :
    ∃ y, IsPeriodicPt f n y ∧ ∀ k : Fin n, f^[k.val] y ∈ Icc (left k) (right k) := by
  have step : ∀ k (hk : k ≤ n), ∃ p q,
      p ≤ q ∧
      Icc p q ⊆ Icc (left (loopIdx hn k)) (right (loopIdx hn k)) ∧
      (f^[k]) '' Icc p q = Icc (left ⟨0, hn⟩) (right ⟨0, hn⟩) ∧
      ∀ x ∈ Icc p q, ∀ j (hj : j < k),
        f^[j] x ∈ Icc (left (loopIdx hn k + ⟨j, hj.trans_le hk⟩))
          (right (loopIdx hn k + ⟨j, hj.trans_le hk⟩)) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨left ⟨0, hn⟩, right ⟨0, hn⟩, hle ⟨0, hn⟩, by simp [loopIdx_zero], ?_, ?_⟩
      · simp
      · intro _ _ j hj
        cases hj
    | succ k ih =>
      have hklt : k < n := Nat.lt_of_succ_le hk
      obtain ⟨p, q, hpq, hpq_sub, himage, hitin⟩ := ih (Nat.le_of_succ_le hk)
      let i : Fin n := loopIdx hn (k + 1)
      have hi_succ : loopIdx hn k = finSucc hn i := loopIdx_succ hn hklt
      have hsrc : Icc p q ⊆ f '' Icc (left i) (right i) :=
        hpq_sub.trans (hi_succ ▸ hcov i)
      have hfsrc : ContinuousOn f (Icc (left i) (right i)) := hf.mono (hsub i)
      obtain ⟨p', q', hpq', hsub', himage'⟩ :=
        exists_subinterval_image_eq (hle i) hpq hfsrc hsrc
      refine ⟨p', q', hpq', ?_, ?_, ?_⟩
      · simpa [i] using hsub'
      · have : f^[k + 1] '' Icc p' q' = f^[k] '' (f '' Icc p' q') := by
          rw [iterate_succ, image_comp]
        rw [this, himage', himage]
      · intro x hx j hj
        have hmaps : MapsTo f (Icc p' q') (Icc p q) := by
          intro z hz
          have : f z ∈ f '' Icc p' q' := mem_image_of_mem _ hz
          rwa [himage'] at this
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · have hz : loopIdx hn (k + 1) + ⟨0, hj.trans_le hk⟩ = loopIdx hn (k + 1) := by
            ext
            simp [Fin.val_add, Nat.mod_eq_of_lt (loopIdx hn (k + 1)).isLt]
          simpa [i, hz] using hsub' hx
        · have hj' : j - 1 < k := by omega
          have hx' : f x ∈ Icc p q := hmaps hx
          have hit := hitin (f x) hx' (j - 1) hj'
          have hjn : j < n := hj.trans_le hk
          have hj1n : j - 1 < n := hj'.trans_le (Nat.le_of_succ_le hk)
          have hidx : loopIdx hn k + ⟨j - 1, hj1n⟩ = i + ⟨j, hjn⟩ := by
            apply Fin.ext
            have hi : loopIdx hn k = finSucc hn i := hi_succ
            rw [hi]
            simp only [Fin.val_add, finSucc]
            have : ((i.val + 1) % n + (j - 1)) % n
                = ((i.val + 1) % n + (j - 1) % n) % n := by
              rw [Nat.mod_eq_of_lt hj1n]
            rw [this, ← Nat.add_mod, show i.val + 1 + (j - 1) = i.val + j by omega]
          have : f^[j] x = f^[j - 1] (f x) := by
            conv_lhs => rw [← Nat.sub_add_cancel hjpos, iterate_succ_apply]
          simpa [this, hidx] using hit
  obtain ⟨p, q, hpq, hpq_sub, himage, hitin⟩ := step n le_rfl
  have hsub0 : Icc p q ⊆ I :=
    hpq_sub.trans (by simpa [loopIdx_n hn] using hsub ⟨0, hn⟩)
  have hcont : ContinuousOn (f^[n]) (Icc p q) := (hf.iterate hmap n).mono hsub0
  have hsurj : SurjOn (f^[n]) (Icc p q) (Icc p q) := by
    intro y hy
    have : y ∈ Icc (left ⟨0, hn⟩) (right ⟨0, hn⟩) := by
      simpa [loopIdx_n hn] using hpq_sub hy
    rwa [← himage] at this
  obtain ⟨y, hy, hfix⟩ := exists_mem_Icc_isFixedPt_of_surjOn hcont hpq hsurj
  refine ⟨y, hfix, ?_⟩
  intro k
  have h0k : (⟨0, hn⟩ : Fin n) + k = k := by
    ext
    simp [Fin.val_add, Nat.mod_eq_of_lt k.isLt]
  simpa [loopIdx_n hn, h0k] using hitin y hy k.val k.isLt

/-- Forward 3-cycle `a ↦ b ↦ c ↦ a` with `a < b < c`. -/
private lemma period_three_forward {I : Set ℝ} [OrdConnected I]
    (hf : ContinuousOn f I) (hmap : MapsTo f I I)
    {a b c : ℝ} (hab : a < b) (hbc : b < c) (haI : a ∈ I) (hcI : c ∈ I)
    (hfa : f a = b) (hfb : f b = c) (hfc : f c = a) {n : ℕ} (hn : 0 < n) :
    ∃ y ∈ I, minimalPeriod f y = n := by
  have hbI : b ∈ I := I.Icc_subset haI hcI ⟨hab.le, hbc.le⟩
  have hfL : ContinuousOn f (Icc a b) := hf.mono (I.Icc_subset haI hbI)
  have hfR : ContinuousOn f (Icc b c) := hf.mono (I.Icc_subset hbI hcI)
  have hLtoR : Icc b c ⊆ f '' Icc a b := by
    have : SurjOn f (Icc a b) (Icc b c) := by
      simpa [hfa, hfb] using
        hfL.surjOn_Icc (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le)
    exact this
  have hRtoBoth : Icc a c ⊆ f '' Icc b c := by
    have : SurjOn f (Icc b c) (Icc a c) := by
      simpa [hfb, hfc] using
        hfR.surjOn_Icc (right_mem_Icc.2 hbc.le) (left_mem_Icc.2 hbc.le)
    exact this
  have hRtoR : Icc b c ⊆ f '' Icc b c :=
    (Icc_subset_Icc hab.le le_rfl).trans hRtoBoth
  have hRtoL : Icc a b ⊆ f '' Icc b c :=
    (Icc_subset_Icc le_rfl hbc.le).trans hRtoBoth
  let left : Fin n → ℝ := fun i => if n = 1 ∨ i.val ≠ 0 then b else a
  let right : Fin n → ℝ := fun i => if n = 1 ∨ i.val ≠ 0 then c else b
  have hle : ∀ i, left i ≤ right i := by
    intro i
    by_cases h : n = 1 ∨ i.val ≠ 0
    · simp [left, right, h]; exact hbc.le
    · simp [left, right, h]; exact hab.le
  have hsubI : ∀ i, Icc (left i) (right i) ⊆ I := by
    intro i
    by_cases h : n = 1 ∨ i.val ≠ 0
    · simp [left, right, h]; exact I.Icc_subset hbI hcI
    · simp [left, right, h]; exact I.Icc_subset haI hbI
  have hcov : ∀ i, Icc (left (finSucc hn i)) (right (finSucc hn i)) ⊆
      f '' Icc (left i) (right i) := by
    intro i
    by_cases hn1 : n = 1
    · subst hn1
      simp [left, right]
      exact hRtoR
    · by_cases hi0 : i.val = 0
      · have hi1 : (finSucc hn i).val ≠ 0 := by
          intro h
          have : (1 : ℕ) % n = 0 := by
            simpa [finSucc, hi0] using h
          have : n ≤ 1 := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero this)
          omega
        simp [left, right, hn1, hi0, hi1]
        exact hLtoR
      · by_cases hlast : (finSucc hn i).val = 0
        · simp [left, right, hn1, hi0, hlast]
          exact hRtoL
        · simp [left, right, hn1, hi0, hlast]
          exact hRtoR
  obtain ⟨y, hyper, hyit⟩ :=
    exists_periodic_pt_of_covering_loop hf hmap hn left right hle hsubI hcov
  have hyI : y ∈ I := hsubI ⟨0, hn⟩ (by simpa using hyit ⟨0, hn⟩)
  refine ⟨y, hyI, ?_⟩
  have hpos : 0 < minimalPeriod f y := hyper.minimalPeriod_pos hn
  have hleP : minimalPeriod f y ≤ n := hyper.minimalPeriod_le hn
  apply le_antisymm hleP
  by_contra hlt
  have hlt : minimalPeriod f y < n := Nat.lt_of_not_ge hlt
  have hit0 := hyit ⟨0, hn⟩
  have hitk := hyit ⟨minimalPeriod f y, hlt⟩
  have hyfix : f^[minimalPeriod f y] y = y := iterate_minimalPeriod
  have hy0 : y ∈ Icc (left ⟨0, hn⟩) (right ⟨0, hn⟩) := by simpa using hit0
  have hyk : y ∈ Icc (left ⟨minimalPeriod f y, hlt⟩)
      (right ⟨minimalPeriod f y, hlt⟩) := by
    simpa [hyfix] using hitk
  have hyb : y = b := by
    by_cases hn1 : n = 1
    · omega
    · have h0 : left ⟨0, hn⟩ = a ∧ right ⟨0, hn⟩ = b := by
        simp [left, right, hn1]
      have hk : left ⟨minimalPeriod f y, hlt⟩ = b ∧
          right ⟨minimalPeriod f y, hlt⟩ = c := by
        have : (⟨minimalPeriod f y, hlt⟩ : Fin n).val ≠ 0 := hpos.ne'
        simp [left, right, hn1, this]
      have hyL : y ∈ Icc a b := by simpa [h0] using hy0
      have hyR : y ∈ Icc b c := by simpa [hk] using hyk
      exact le_antisymm hyL.2 hyR.1
  have hf2b : f^[2] b = a := by simp [hfb, hfc]
  rcases lt_trichotomy n 2 with hnlt | hneq | hngt
  · omega
  · subst hneq
    have : a = b := by
      have : f^[2] y = y := hyper
      simpa [hyb, hf2b] using this
    exact hab.ne this
  · have h2 : (2 : ℕ) < n := hngt
    have hit2 := hyit ⟨2, h2⟩
    have hn1 : n ≠ 1 := by omega
    have h2ne : (⟨2, h2⟩ : Fin n).val ≠ 0 := by simp
    have : f^[2] y ∈ Icc b c := by
      simpa [left, right, hn1, h2ne] using hit2
    have : a ∈ Icc b c := by simpa [hyb, hf2b] using this
    exact hab.not_ge this.1

/-- Backward 3-cycle `a ↦ c ↦ b ↦ a` with `a < b < c`. -/
private lemma period_three_backward {I : Set ℝ} [OrdConnected I]
    (hf : ContinuousOn f I) (hmap : MapsTo f I I)
    {a b c : ℝ} (hab : a < b) (hbc : b < c) (haI : a ∈ I) (hcI : c ∈ I)
    (hfa : f a = c) (hfc : f c = b) (hfb : f b = a) {n : ℕ} (hn : 0 < n) :
    ∃ y ∈ I, minimalPeriod f y = n := by
  have hbI : b ∈ I := I.Icc_subset haI hcI ⟨hab.le, hbc.le⟩
  have hfL : ContinuousOn f (Icc a b) := hf.mono (I.Icc_subset haI hbI)
  have hfR : ContinuousOn f (Icc b c) := hf.mono (I.Icc_subset hbI hcI)
  have hLtoBoth : Icc a c ⊆ f '' Icc a b := by
    have : SurjOn f (Icc a b) (Icc a c) := by
      simpa [hfa, hfb] using
        hfL.surjOn_Icc (right_mem_Icc.2 hab.le) (left_mem_Icc.2 hab.le)
    exact this
  have hRtoL : Icc a b ⊆ f '' Icc b c := by
    have : SurjOn f (Icc b c) (Icc a b) := by
      simpa [hfb, hfc] using
        hfR.surjOn_Icc (left_mem_Icc.2 hbc.le) (right_mem_Icc.2 hbc.le)
    exact this
  have hLtoL : Icc a b ⊆ f '' Icc a b :=
    (Icc_subset_Icc le_rfl hbc.le).trans hLtoBoth
  have hLtoR : Icc b c ⊆ f '' Icc a b :=
    (Icc_subset_Icc hab.le le_rfl).trans hLtoBoth
  let left : Fin n → ℝ := fun i => if n = 1 ∨ i.val ≠ 0 then a else b
  let right : Fin n → ℝ := fun i => if n = 1 ∨ i.val ≠ 0 then b else c
  have hle : ∀ i, left i ≤ right i := by
    intro i
    by_cases h : n = 1 ∨ i.val ≠ 0
    · simp [left, right, h]; exact hab.le
    · simp [left, right, h]; exact hbc.le
  have hsubI : ∀ i, Icc (left i) (right i) ⊆ I := by
    intro i
    by_cases h : n = 1 ∨ i.val ≠ 0
    · simp [left, right, h]; exact I.Icc_subset haI hbI
    · simp [left, right, h]; exact I.Icc_subset hbI hcI
  have hcov : ∀ i, Icc (left (finSucc hn i)) (right (finSucc hn i)) ⊆
      f '' Icc (left i) (right i) := by
    intro i
    by_cases hn1 : n = 1
    · subst hn1
      simp [left, right]
      exact hLtoL
    · by_cases hi0 : i.val = 0
      · have hi1 : (finSucc hn i).val ≠ 0 := by
          intro h
          have : (1 : ℕ) % n = 0 := by
            simpa [finSucc, hi0] using h
          have : n ≤ 1 := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero this)
          omega
        simp [left, right, hn1, hi0, hi1]
        exact hRtoL
      · by_cases hlast : (finSucc hn i).val = 0
        · simp [left, right, hn1, hi0, hlast]
          exact hLtoR
        · simp [left, right, hn1, hi0, hlast]
          exact hLtoL
  obtain ⟨y, hyper, hyit⟩ :=
    exists_periodic_pt_of_covering_loop hf hmap hn left right hle hsubI hcov
  have hyI : y ∈ I := hsubI ⟨0, hn⟩ (by simpa using hyit ⟨0, hn⟩)
  refine ⟨y, hyI, ?_⟩
  have hpos : 0 < minimalPeriod f y := hyper.minimalPeriod_pos hn
  have hleP : minimalPeriod f y ≤ n := hyper.minimalPeriod_le hn
  apply le_antisymm hleP
  by_contra hlt
  have hlt : minimalPeriod f y < n := Nat.lt_of_not_ge hlt
  have hit0 := hyit ⟨0, hn⟩
  have hitk := hyit ⟨minimalPeriod f y, hlt⟩
  have hyfix : f^[minimalPeriod f y] y = y := iterate_minimalPeriod
  have hyb : y = b := by
    by_cases hn1 : n = 1
    · omega
    · have h0 : left ⟨0, hn⟩ = b ∧ right ⟨0, hn⟩ = c := by
        simp [left, right, hn1]
      have hk : left ⟨minimalPeriod f y, hlt⟩ = a ∧
          right ⟨minimalPeriod f y, hlt⟩ = b := by
        have : (⟨minimalPeriod f y, hlt⟩ : Fin n).val ≠ 0 := hpos.ne'
        simp [left, right, hn1, this]
      have hyR : y ∈ Icc b c := by simpa [h0] using hit0
      have hyL : y ∈ Icc a b := by simpa [hyfix, hk] using hitk
      exact le_antisymm hyL.2 hyR.1
  have hf2b : f^[2] b = c := by simp [hfb, hfa]
  rcases lt_trichotomy n 2 with hnlt | hneq | hngt
  · omega
  · subst hneq
    have : c = b := by
      have : f^[2] y = y := hyper
      simpa [hyb, hf2b] using this
    exact hbc.ne this.symm
  · have h2 : (2 : ℕ) < n := hngt
    have hit2 := hyit ⟨2, h2⟩
    have hn1 : n ≠ 1 := by omega
    have h2ne : (⟨2, h2⟩ : Fin n).val ≠ 0 := by simp
    have : f^[2] y ∈ Icc a b := by
      simpa [left, right, hn1, h2ne] using hit2
    have : c ∈ Icc a b := by simpa [hyb, hf2b] using this
    exact hbc.not_ge this.2

private lemma orbit3_distinct {x : ℝ} (hx : minimalPeriod f x = 3) :
    x ≠ f x ∧ x ≠ f^[2] x ∧ f x ≠ f^[2] x := by
  have h01 :=
    (iterate_eq_iterate_iff_of_lt_minimalPeriod
      (by rw [hx]; omega) (by rw [hx]; omega) : f^[0] x = f^[1] x ↔ 0 = 1)
  have h02 :=
    (iterate_eq_iterate_iff_of_lt_minimalPeriod
      (by rw [hx]; omega) (by rw [hx]; omega) : f^[0] x = f^[2] x ↔ 0 = 2)
  have h12 :=
    (iterate_eq_iterate_iff_of_lt_minimalPeriod
      (by rw [hx]; omega) (by rw [hx]; omega) : f^[1] x = f^[2] x ↔ 1 = 2)
  refine ⟨?_, ?_, ?_⟩
  · intro h; exact zero_ne_one (h01.mp (by simpa using h))
  · intro h; exact (by omega : (0 : ℕ) ≠ 2) (h02.mp (by simpa using h))
  · intro h; exact (by omega : (1 : ℕ) ≠ 2) (h12.mp (by simpa using h))

private lemma orbit3_card {x : ℝ} (hx : minimalPeriod f x = 3) :
    ({x, f x, f^[2] x} : Finset ℝ).card = 3 := by
  obtain ⟨h01, h02, h12⟩ := orbit3_distinct hx
  have h02' : x ≠ f (f x) := by simpa [iterate_succ_apply', iterate_one] using h02
  have h12' : f x ≠ f (f x) := by simpa [iterate_succ_apply', iterate_one] using h12
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simpa using h12'
  · simp [h01, h02']

/-- **Li–Yorke / Sharkovsky (period 3).** A continuous self-map of an interval
with a point of least period 3 has a point of least period `n` for every `n > 0`. -/
theorem period_three_all {I : Set ℝ} [OrdConnected I]
    (hf : ContinuousOn f I) (hI : MapsTo f I I)
    {x : ℝ} (hxI : x ∈ I) (hx : minimalPeriod f x = 3)
    {n : ℕ} (hn : 0 < n) :
    ∃ y ∈ I, minimalPeriod f y = n := by
  let P : Finset ℝ := {x, f x, f^[2] x}
  have hPcard : P.card = 3 := orbit3_card hx
  have hPne : P.Nonempty := ⟨x, by simp [P]⟩
  let a := P.min' hPne
  let c := P.max' hPne
  have haP : a ∈ P := P.min'_mem hPne
  have hcP : c ∈ P := P.max'_mem hPne
  have ha_ne_c : a ≠ c := by
    intro hac
    have hunq : ∀ z ∈ P, z = a := by
      intro z hz
      exact le_antisymm ((P.le_max' z hz).trans hac.symm.le) (P.min'_le z hz)
    have : P.card = 1 :=
      Finset.card_eq_one.2 ⟨a, Finset.eq_singleton_iff_unique_mem.2 ⟨haP, hunq⟩⟩
    omega
  have hc_erase : c ∈ P.erase a := Finset.mem_erase.2 ⟨ha_ne_c.symm, hcP⟩
  have hrest_card : ((P.erase a).erase c).card = 1 := by
    have : (P.erase a).card = 2 := by
      rw [Finset.card_erase_of_mem haP, hPcard]
    rw [Finset.card_erase_of_mem hc_erase, this]
  obtain ⟨b, hbrest⟩ := Finset.card_pos.mp (by omega : 0 < ((P.erase a).erase c).card)
  have hbP : b ∈ P ∧ b ≠ a ∧ b ≠ c := by
    have := hbrest
    simp only [Finset.mem_erase] at this
    exact ⟨this.2.2, this.2.1, this.1⟩
  have hab : a < b :=
    lt_of_le_of_ne (P.min'_le b hbP.1) hbP.2.1.symm
  have hbc : b < c :=
    lt_of_le_of_ne (P.le_max' b hbP.1) hbP.2.2
  have hPeq : P = {a, b, c} := by
    have hsub : ({a, b, c} : Finset ℝ) ⊆ P := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact haP
      · exact hbP.1
      · exact hcP
    have hcard : ({a, b, c} : Finset ℝ).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simpa using hbP.2.2
      · simp [Finset.mem_insert, Finset.mem_singleton, hbP.2.1.symm, ha_ne_c]
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hPcard, hcard])).symm
  have hx_mem : x ∈ periodicPts f :=
    minimalPeriod_pos_iff_mem_periodicPts.mp (by omega)
  have horbitI : ∀ k : ℕ, f^[k] x ∈ I := fun k => (hI.iterate k) hxI
  have haI : a ∈ I := by
    have ha : a ∈ ({x, f x, f^[2] x} : Finset ℝ) := haP
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ha | ha | ha
    · rw [ha]; exact hxI
    · rw [ha]; exact horbitI 1
    · rw [ha]; exact horbitI 2
  have hcI : c ∈ I := by
    have hc : c ∈ ({x, f x, f^[2] x} : Finset ℝ) := hcP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with hc | hc | hc
    · rw [hc]; exact hxI
    · rw [hc]; exact horbitI 1
    · rw [hc]; exact horbitI 2
  have hf3 : f^[3] x = x := by rw [← hx, iterate_minimalPeriod]
  have hmemP : ∀ z ∈ P, f z ∈ P := by
    intro z hz
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
    rcases hz with hz | hz | hz
    · subst hz; simp
    · subst hz; simp
    · subst hz
      left
      have : f (f (f x)) = f^[3] x := by
        rw [iterate_succ_apply', iterate_succ_apply', iterate_one]
      exact this.trans hf3
  have hpera : minimalPeriod f a = 3 := by
    have ha : a ∈ ({x, f x, f^[2] x} : Finset ℝ) := haP
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ha | ha | ha
    · rw [ha]; exact hx
    · rw [ha, minimalPeriod_apply hx_mem, hx]
    · rw [ha, minimalPeriod_apply_iterate hx_mem 2, hx]
  have hfa_ne : f a ≠ a := by
    intro h
    have : minimalPeriod f a = 1 :=
      minimalPeriod_eq_one_iff_isFixedPt.2 h
    omega
  have hfa_bc : f a = b ∨ f a = c := by
    have hfaP : f a ∈ ({a, b, c} : Finset ℝ) := by
      rw [← hPeq]
      exact hmemP a haP
    have : f a = a ∨ f a = b ∨ f a = c := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hfaP
    exact this.resolve_left hfa_ne
  have hperb : minimalPeriod f b = 3 := by
    have hb : b ∈ ({x, f x, f^[2] x} : Finset ℝ) := hbP.1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with hb | hb | hb
    · rw [hb]; exact hx
    · rw [hb, minimalPeriod_apply hx_mem, hx]
    · rw [hb, minimalPeriod_apply_iterate hx_mem 2, hx]
  rcases hfa_bc with hfa | hfa
  · have hfb_ne_a : f b ≠ a := by
      intro h
      have : IsPeriodicPt f 2 a := by
        change f^[2] a = a
        simp [hfa, h]
      have : minimalPeriod f a ≤ 2 := this.minimalPeriod_le (by omega)
      omega
    have hfb_ne_b : f b ≠ b := by
      intro h
      have : minimalPeriod f b = 1 :=
        minimalPeriod_eq_one_iff_isFixedPt.2 h
      omega
    have hfb : f b = c := by
      have hfbP : f b ∈ ({a, b, c} : Finset ℝ) := by
        rw [← hPeq]
        exact hmemP b hbP.1
      have : f b = a ∨ f b = b ∨ f b = c := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hfbP
      exact (this.resolve_left hfb_ne_a).resolve_left hfb_ne_b
    have hfc : f c = a := by
      have : f^[3] a = a := by
        have := isPeriodicPt_minimalPeriod f a
        rwa [hpera] at this
      simpa [hfa, hfb] using this
    exact period_three_forward hf hI hab hbc haI hcI hfa hfb hfc hn
  · have hfc_ne_a : f c ≠ a := by
      intro h
      have : IsPeriodicPt f 2 a := by
        change f^[2] a = a
        simp [hfa, h]
      have : minimalPeriod f a ≤ 2 := this.minimalPeriod_le (by omega)
      omega
    have hperc : minimalPeriod f c = 3 := by
      have hc : c ∈ ({x, f x, f^[2] x} : Finset ℝ) := hcP
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with hc | hc | hc
      · rw [hc]; exact hx
      · rw [hc, minimalPeriod_apply hx_mem, hx]
      · rw [hc, minimalPeriod_apply_iterate hx_mem 2, hx]
    have hfc_ne_c : f c ≠ c := by
      intro h
      have : minimalPeriod f c = 1 :=
        minimalPeriod_eq_one_iff_isFixedPt.2 h
      omega
    have hfc : f c = b := by
      have hfcP : f c ∈ ({a, b, c} : Finset ℝ) := by
        rw [← hPeq]
        exact hmemP c hcP
      have : f c = a ∨ f c = b ∨ f c = c := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hfcP
      exact (this.resolve_left hfc_ne_a).resolve_right hfc_ne_c
    have hfb : f b = a := by
      have : f^[3] a = a := by
        have := isPeriodicPt_minimalPeriod f a
        rwa [hpera] at this
      simpa [hfa, hfc] using this
    exact period_three_backward hf hI hab hbc haI hcI hfa hfc hfb hn

end Sharkovsky
