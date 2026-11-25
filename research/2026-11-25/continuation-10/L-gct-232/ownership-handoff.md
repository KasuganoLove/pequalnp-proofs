# L-gct-232 ownership handoff

Stopped new mathematics on receipt of the root's stop message. The root reported a lease renewal response of HTTP 410 at 2026-11-25 08:44:48.770589 UTC. The stop message reached this worker after the orbit bookkeeping had completed. No Magma job, Lean proof, official checker run, lease operation, remote write, or submission was performed by this worker.

The root's subsequent allocator response at 08:47:55 UTC was null, so there is no current root-held GCT lease. Under the user's explicit completion criterion, the stage requires an official upstream PR and ACCEPTED verdict. Saving or committing this research archive does not complete the stage.

## Completed bounded direction search

`ownership_small_directions.cpp` uses exact Gaussian-integer arithmetic, with symmetric coordinates in the order `(00,01,02,03,11,12,13,22,23,33)`. The first nonzero coordinate is normalized to 1; this exhausts scalar-unit representatives of the specified alphabets. Counts include the zero vector, which is never accepted as a direction.

| Alphabet and support cap | Canonical vectors visited | Constant-permanent directions | Compatible pairs | Compatible triples | Independent triples |
| --- | ---: | ---: | ---: | ---: | ---: |
| `{0,1,-1}`, support ≤10 | 29,525 | 12 | 12 | 4 | 0 |
| `{0,1,-1,i,-i}`, support ≤6 | 295,103 | 18 | 12 | 4 | 0 |
| `{0,1,-1,i,-i}`, support ≤10 | 2,441,407 | 30 | 12 | 4 | 0 |

All three finite runs completed enumeration, pair checks, and triple checks. No witness was found. This is **not a nonexistence proof over arbitrary complex coefficients**, and it has not been independently replayed in Lean.

For a symmetric direction `T`, the implementation first checks the total entry sum `S=0`, then checks

`Q(T)=sum_{i,j} T_ij² - 2 sum_i (sum_j T_ij)² = 0`.

On `S=0`, this is the degree-two coefficient of `per(J+tT)`. The degree-three and degree-four coefficients are computed directly from all 24 permutations. Pair compatibility is tested by polarization using `A+B`, `A-B`, and `A+2B`, after the two individual directions are valid. These three evaluations force every mixed cubic and quartic coefficient to vanish. Triple compatibility uses `A+B+C`, `2A+B+C`, `A+2B+C`, `A+B+2C`; the runs in fact have no independent compatible triple, so no proposed witness relies on that final test.

Reproduce, after authorization for further task work:

```sh
g++ -O3 -std=c++20 ownership_small_directions.cpp -o ownership_small_directions
./ownership_small_directions real 10 45 ownership-real-small.json > ownership-real-small.log 2>&1
./ownership_small_directions gaussian 6 45 ownership-gaussian-small.json > ownership-gaussian-small.log 2>&1
./ownership_small_directions gaussian 10 45 ownership-gaussian-full-small.json > ownership-gaussian-full-small.log 2>&1
```

Exit 1 means no witness was found; it does not mean an execution failure. The JSON flags distinguish completed finite enumeration from a timeout. A temporary output-only modification to emit the direction list was reverted when the stop message arrived, without a new mathematical run. The frozen source again matches the version that produced the archived results. Rebuild from source; the local binary is not an archival input.

## General chart coverage bookkeeping

`ownership_pivot_orbits.py` and `ownership-pivot-orbits.json` enumerate all 120 triples of the 10 symmetric coordinate functions under simultaneous permutation of the four row and column indices. There are exactly 11 orbits. Representatives are:

`(0,1,2), (0,1,4), (0,1,5), (0,1,7), (0,1,8), (0,4,7), (0,4,8), (0,5,6), (1,2,3), (1,2,5), (1,2,6)`.

Their orbit sizes are `12,6,24,24,12,4,6,12,4,4,12`, summing to 120. The JSON records an explicit permutation transporting each representative to every member. It also records a nonpivot diagonal coordinate suitable for eliminating the total-entry-sum equation.

Why this covers possible three-dimensional spaces: the coordinate restrictions span the dual of any three-dimensional subspace, so some triple is a basis of that dual. Changing the basis of the candidate subspace makes those three coordinates an identity matrix. Simultaneous row/column permutation preserves symmetry, `J`, and the permanent. Thus one of the 11 full open pivot charts contains a transformed candidate. All other coordinates are free initially; removing one nonpivot diagonal using the linear coefficient leaves 18 parameters. The remaining constraints are 6 quadratic, 10 cubic, and 15 quartic coefficients.

**Implementation caution:** these are open charts in all 10 coordinates, not 11 chosen row-echelon strata in an already reduced 9-coordinate system. In particular, one must not impose zeros before pivots as in the existing 9-coordinate RREF generator and then claim these 11 cases cover all candidates. All 11 open charts retain 18 parameters, whereas the original 84 RREF strata can have fewer parameters on their boundary cases. No general-chart Gröbner calculation or certificate was produced here.

## Rank-one obstruction and failed fixed-u route

For `v` in `C^4`, let `e_k(v)` be its elementary symmetric functions. Direct expansion gives

`per(J+t vvᵀ) = sum_{k=0}^4 k!(4-k)! e_k(v)^2 t^k`.

Therefore a constant-permanent rank-one direction would force `e_1=e_2=e_3=e_4=0`. The monic polynomial with roots the four entries of `v` would be `z^4`, so `v=0`. Thus a constant-permanent space contains no nonzero symmetric rank-one direction. This argument is mathematical analysis, not a compiled Lean theorem in this checkpoint.

One candidate construction was to fix a nonzero `u` satisfying `sum u_i=0` and `u·u=0`, then take `T=uvᵀ+vuᵀ` for `v` in the three-dimensional space `u⊥`. This automatically satisfies the linear and quadratic coefficient conditions, but it contains `v=u`, hence the forbidden direction `2uuᵀ`. It cannot provide a counterexample. This excludes this specific fixed-u family only; it does **not** classify arbitrary candidates whose row-sum map has rank 1.

## Duplicate block expansion

The root had already completed a stronger reduced analysis of the disjoint-block two-plane. Before learning that, this worker started `ownership_block_extension.py`, which finished its coefficient expansion and linear elimination at 08:44:04 UTC. Its JSON has the linear solution and eight remaining coefficients. No Gröbner computation was done here, and it does not on its own prove extension rigidity. Prefer the root's `continuation-10/L-gct-232/block_extension_reduced.*` result. This duplicate expansion is retained only for provenance, not as a new result.

## Primary literature checked

- Melody Chan and Nathan Ilten, *Fano schemes of determinants and permanents*, Algebra & Number Theory 9(3), 2015, 629–678: https://msp.org/ant/2015/9-3/ant-v9-n3-p05-s.pdf . This studies linear spaces in homogeneous permanent-zero varieties for general matrices. It does not supply the present theorem for a symmetric affine space through `J` in a nonzero permanent fiber. In particular, its ambient torus action does not preserve this fixed affine basepoint.
- S. Maria Arulraj and K. Somasundaram, *Permanental Mates: Perturbations and Hwang's conjecture*, Applied Mathematics Letters 21, 2008, 786–790, DOI 10.1016/j.aml.2007.08.005. Institutional source: https://www.amrita.edu/publication/permanental-mates-perturbations-and-hwangs-conjecture/ . The relevant setting is real doubly-stochastic permanent mates and perturbations of symmetric starting matrices; this is not the complex transpose-symmetric three-dimensional problem here.
- P. Subramanian and K. Somasundaram, *Affine spaces and function mates* / institutional title *Function Mates*, Journal of Algebra and Applied Mathematics 11, 2013, 29–35. Institutional source: https://www.amrita.edu/publication/function-mates/ . Its abstract concerns generalized doubly-stochastic matrices and function mates on line segments. The abstract does not provide the needed maximum-dimensionality result. Full text was not obtained.

These searches found no usable exact theorem; that is not a claim that no relevant theorem exists. Positivity or real doubly-stochastic arguments must not be applied to arbitrary complex transpose-symmetric candidates.

## Remaining full-task obstacle

A genuine full proof still needs to exclude all three-planes with arbitrary complex coefficients, including nonzero row sums, or produce an explicit counterexample. The finite direction search, rank-one exclusion, block-plane extension result, and row-sum-zero chart result do not jointly cover that space. The 11-orbit bookkeeping provides a possible full computational coverage plan, but no complete exact solver certificate or Lean proof is present.

`ownership-artifacts.json` records hashes and timestamps for this worker's sources and results.
