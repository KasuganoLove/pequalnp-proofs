# Review of the frozen OR-budget TopForm adaptation

Reviewed `Pnp4201BudgetTopForm.lean` at SHA256 `4a6c8b5140f99a7c6730080441636ff51f76f3f33b286f6271fdd27c1d8c59d9`,330 lines/16,553 bytes. The author reported an ordinary Lean build with exit0 and empty log. This was an independent read-only source review; no compilation or source mutation was performed by the reviewer.

No defect was found in the budget accounting or minimum comparison domain:

* `V1_opCount` identifies V1's operation sequence with physical bypass, so the deleted gate is counted exactly once and all other operators are preserved.
* `V2_opCount` describes V2 as V1 followed by one OR. In its reader applications the deleted gate is proved to be OR, so `V2_orCount` is an equality with the original OR count.
* `BudgetLeast` compares only equivalent AO2 circuits with ORcount at most the current circuit's ORcount. `budget_reader_or` invokes that comparator on V1 after proving semantics, model preservation, and a nonincreasing OR count.
* `budget_reader_unique` first performs the equal-size/equal-OR V2 move, then deletes the other OR reader. Its final competitor is smaller and has no larger OR count. It does not require V2 itself to be smaller.
* `budget_least_of_same` transports the comparison property only with the stated equality of total size and OR count and equality of the full function.
* The TopForm induction decreases the AND-cone-pair measure, while the imported move lemmas preserve function and the new count lemma preserves ORcount. Junk cardinality preservation is explicitly retained.

The endpoint `exists_top_form_with_or_budget` appropriately proves TopForm, not all-AND cleanliness. In particular, its first minimization is over all equivalent circuits in the OR budget; an initially clean C does not thereby imply that the chosen minimum is clean. A separate clean-class minimum argument is required to add that conclusion. The author is developing that variant separately.

All semantic equalities are over all assignments. No finite-sample correctness or global OR lower bound is silently substituted. The frozen module imports upstream L_meta_1501 plus local research, so this review does not certify it as a Defs-only official submission artifact.
