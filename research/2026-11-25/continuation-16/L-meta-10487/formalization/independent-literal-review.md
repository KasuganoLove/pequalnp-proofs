# Independent review of the literal10486 candidate

Reviewed source: `L_meta_10486.literal.lean`,37,923 bytes, SHA256
`8594b4c63029520fca331029135bb7b19a0d0b8978de41c49ff2eb6462104ec8`.
This review read source and performed small ordinary Python data checks. It
did not run Lean, the strict checker or another signed search. The parent's
kernel rejection check was still pending when this review was recorded.

## Exact statement

The final theorem's type is byte-for-byte the current positive10486 statement
after removing the statement file's terminal newline. Its text SHA256 is
`d5975fb801d7798de99550a1dfecd2cc4b67addef55892ca665243c496bd84fa`.
The full posted statement file SHA256 is
`38b94667fa0cf4723b9295faf20e64afe6d42c02da75a8ea79859670ee22722f`.
No hypothesis was added to the public replacement theorem.

## Generic proof reuse

The entire generic Signed framework before `def F` is identical to the
checked L9539 reference after only namespace,1400→3192 and700→1596
replacements. The `bound_from_search` block differs only by the new domain
size7 and binary budget10, plus bit width. Thus it uses the literal proved
`build`/`compress`/`live`/`search_complete` engine, not the independently
written C++ optimizations.

The L9539 reference hash is
`f0ea1c9ca867450a030a85e2152c13be57db5b8f1f7ed96c891c06afe3edd876`.
Its Apache-2.0 attribution to L9136, L9146/partymejker, L8633/k-sandhu and
L8463/L1449 remains in the file. New comments identify the specialization.
Imports are Mathlib and PEqualNP.Defs. No sorry, admit, native_decide,
unsafe or new axiom declaration was observed.

## Sample table and witness

The seven numeric rows are within3192 bits. Decoding each of the1596 low/high
column pairs independently gives exactly the Cartesian product of114
positive and14 negative assignments, with no duplicate or missing pair.
Low-half assignments are positive; high-half assignments are negative.
Consequently every one of the3192 bits satisfies the actual theorem premise
`F sample = ~~~goal`, not the opposite polarity.

The twelve witness gates exactly match the already frozen `baseline12.json`.
All are binary AND/OR gates with earlier reads; the output is wire18.
Independent replay agrees with the literal fifteen-edge function on all128
assignments. No oneEach restriction or additional promise was introduced.

## Final counting argument

When any NOT occurs, the list-filter lemma gives
`binaryCost gates < gates.length`. The proposed kernel rejection gives
`10 < binaryCost gates`. Natural-number arithmetic therefore yields
`12 ≤ gates.length`, enough for the twelve-gate monotone witness.
When no NOT occurs, the original list is already AND/OR and is returned
unchanged. The public at-most-one-NOT premise is unused; this is a stronger
valid conclusion, not a missing assumption.

**Scope:** source, type-text, instance-data and final-argument review passed.
The decisive remaining validation is the parent's Lean proof of
`search 10 rows = false` and its subsequent full-file/official checks.
`independent-literal-audit.json` records the machine-readable checks.
