Reduces L-meta-3600 to two incidence budgets: the `ReadK.lineSingle` class contributes at most `6 * C.size`; its complement must contribute at most `94 * C.size`. Their partition has size `N * (q + 1)`, giving the exact posted `N * q ≤ 100 * C.size` conclusion.

The first child already has a complete Lean proof under only unique joining lines, `IsAO2`, and rejection of the canonical false input with one active line. It adapts the counting proof of upstream L_meta_2462, weakens full correctness to the precise rejection condition used, and exposes the original proof's tighter constant 6. This is a strengthening of that existing proof, not a claim to have invented its counting argument.

Completed first-child proof and reproduction: https://github.com/KasuganoLove/pequalnp-proofs/tree/244b7e9131ce462bb95d85541b713d8ceb5d8240/research/2026-11-24/continuation-3/L-meta-3600

The complementary `94 * size` child remains open. This PR does not prove the full circuit lower bound.

Validation: ordinary Lean compilation and the allowed-import guard pass. A Lean diagnostic confirmed the first child structurally matches the proved statement; the two children print to 601 and 1,260 characters. The local strict checker was terminated with exit 137 during verifier execution, before a verdict. Official validation is required. The PR adds one file in one commit; no custom data type or instance is declared.
