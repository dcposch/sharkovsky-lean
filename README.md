# Period three implies all periods

Lean 4 / Mathlib proof that a continuous interval map with a point of
least period 3 has a point of least period \(n\) for every \(n\ge 1\).
This is the periodic-point half of Li–Yorke, *Period Three Implies Chaos*
(Amer. Math. Monthly 82 (1975)), and the first case of Sharkovsky’s
forcing theorem (Ukrain. Mat. Zh. 16 (1964)): 3 is maximal in the
Sharkovsky order.

The argument is a two-interval intermediate-value covering. It does
**not** prove the full Sharkovsky order, nor the Li–Yorke scrambled set.

Mehta’s CPP 2023 formalisation is Lean 3
([`b-mehta/sharkovsky`](https://github.com/b-mehta/sharkovsky)).
No Lean 4 pin was found in Mathlib Dynamics or as a standalone port, so
this repository is the substantive development.

This is a Palomar project. Submissions go to
<https://submit.palomar-registry.org/>.

## Repository map

- `Challenge.lean` — audited statement `Sharkovsky.period_three_implies_all_periods`.
- `Solution.lean` — the same declaration, proved.
- `Sharkovsky/PeriodThree.lean` — covering lemma and the two 3-cycle orientations.
- `comparator.json`, `formalization.yaml` — Palomar metadata.

## Verify

```sh
lake build Challenge Solution Sharkovsky
printf 'import Solution\n#print axioms Sharkovsky.period_three_implies_all_periods\n' \
  | lake env lean --stdin
./scripts/check_axioms.sh
ruby scripts/validate-formalization.rb
```

Lean 4.32.0, Mathlib v4.32.0. Forbidden: `native_decide`, `Lean.ofReduceBool`.
Permitted axioms: `propext`, `Classical.choice`, `Quot.sound`.
