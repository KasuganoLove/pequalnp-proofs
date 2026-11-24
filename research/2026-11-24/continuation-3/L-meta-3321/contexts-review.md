# Independent review and proved local component for L-meta-3321

The full clean-AND normal-form theorem remains unproved. No counterexample to
its existential conclusion has been found in this bounded review. An unclean
representation alone would not disprove it, because an alternate circuit of
no greater size could exist.

## Proven local result

Fix two finite sets S,T of point inputs. For a line l, call the context safe
when every point assignment satisfying both OR(S) and OR(T) has an active
point incident with l. This is the semantic condition for the product
OR(S) AND OR(T) AND y_l to stay below the target incidence function.

The following are equivalent:

1. The line context is safe on every point assignment.
2. For every s in S and t in T, I(s,l) or I(t,l).
3. Every point of S lies on l, or every point of T lies on l.

The forward implication is witnessed by activating just s and t. For the
second-to-third implication, if S has a nonneighbor s, every member of T
must be a neighbor. This part does not require C4-freeness.

In a C4-free incidence, a set containing two distinct points lies wholly
on at most one line. The safe lines therefore form the union of the lines
containing S and the lines containing T. When |S| and |T| are at least two,
there are at most two distinct safe line contexts. When |S intersection T|
is at least two, every safe line contains that intersection, so at most one
safe line exists.

All six supporting theorems in `Pnp3321Contexts.lean` passed ordinary
Lean compilation (exit 0). The log has one tactic deprecation warning.
No strict checker was run. The validation manifest records the exact hash.

These bounds concern distinct line contexts, not the number of syntactic
readers. They do not cover mixed OR factors, an arbitrary OR chain between
reader and gate, or reader contexts consisting of several active lines.
They supply no no-growth global circuit rewrite by themselves.

## Existing formal results and the cost-model obstacle

`lean/PEqualNP/Outside/L_meta_950.lean` (the singleton-strip construction
beginning near line 259) and `L_meta_910.lean` (near line 146) already strip
singleton-true AND gates in `PEqualNP.AndCount.AndCountCircuit`. The pass
copies singleton sets into each reader's `leftVars`/`rightVars`, preserving
`AndCountCircuit.size`. In that model the OR sides are free and unbounded:
this size counts AND gates. It does not establish a nonincreasing number
of fan-in-two AND and OR gates as required by L-meta-3321.

`lean/PEqualNP/MetaComplexity/Helpers/LocClean.lean`, theorem `mclean_of`,
keeps total gate count from growing, but its `CleanL` is structural circuit
normalization (binary gates and earlier wires). It does not imply the
semantic cleanliness or singleton-false condition in the present task.

The definitions in `lean/PEqualNP/Defs/CleanedNonEdge.lean` explicitly track
AND readers through OR closures. They also warn that cleanliness of the
other side is a property of each reader, not of the dirty gate itself.
Any full rewrite must respect this sharing and account for the OR gates.

## Literature boundary

Jukna, *Disproving the Single Level Conjecture*, SIAM J. Comput. 36(1),
83-98 (2006), author PDF:
https://web.vu.lt/mif/s.jukna/ftp/single1.pdf

The K2,2-free lower bound discussed on PDF page 11 is explicitly for
single-level circuits. The paper's large-gap counterexamples use saturated
extensions, which add within-part edges and thus do not directly refute
this C4-free bipartite normalization claim. The paper therefore supplies
neither the missing normalization nor a counterexample to this exact task.
