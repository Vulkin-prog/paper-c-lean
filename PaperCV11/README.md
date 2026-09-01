# Paper C v1.1 Lean formalization line

This directory is the development overlay for the English Paper C v1.1
mathematical candidate and its technical companion, both dated 1 September
2026. It starts from the immutable retained-core authority commit
`b3cf107d2df629453a5da8e84f2bad29eea0bf94`.

The overlay imports and reuses the retained rc4 objects. It does not create a
second random-multiplicative-function model, modify an existing canonical
declaration, or reinterpret any of the four existing Palomar records.

The separate Lake library `PaperCV11` is deliberate: the historical
`core_source` digest and audit for the retained v1.0 record remain byte-stable
while the new endpoints are developed. A dedicated v1.1 Comparator and audit
manifest will be added only after the endpoint statements are frozen.

## Qualified first milestone

- `HardConditioningSaddle.lean` proves the exact max-min calculation
  `min a (2a)⁻¹ ≤ (sqrt 2)⁻¹`, with equality at `a = (sqrt 2)⁻¹`, and exposes
  `PaperC.paper_c_v1_1_hard_conditioning_saddle`.
- `TruncatedDefectCount.lean` isolates the exact finite support truncation
  needed before the Rankin tilt in Proposition 3.3.
- `RankinTilt.lean` proves the finite termwise Rankin comparison and closes it
  into the exact small-prime Euler product with exponent `-1 + sigma`.
- `RankinEnvelope.lean` turns that Euler product into the exponential form of
  (3.4), parameterized only by the remaining finite reciprocal-prime bound.
- `PrimeHarmonic.lean` proves that reciprocal-prime bound with the explicit
  absolute constant `120`, using only the retained Chebyshev shell estimate.
- `SharpKernelDefect.lean` fixes the exact `A(X,T)` count, closes the literal
  paper-shaped (3.4), and exposes
  `PaperC.paper_c_v1_1_sharp_kernel_defect_finite`.
- `SharpPrimeCutoff.lean` defines the v1.1 cutoff
  `floor (exp (S_N / sqrt 2))` without changing the historical
  `floor (B^2 * log B)` declaration.
- `SyndromeCollision.lean` gives a direct subset-syndrome proof of the short
  kernel-word extraction used by the Hamming steps.

These files contain no `sorry`, `admit`, `native_decide`, new axiom, unsafe
code, or partial definition.

## Frozen endpoint queue

The remaining article endpoints are developed under the names fixed by the
v1.1 handoff:

1. `paper_c_v1_1_sharp_kernel_defect`;
2. `paper_c_v1_1_terminal_density_closure`;
3. `paper_c_v1_1_two_window_profile`;
4. `paper_c_v1_1_quantitative_second_moment`;
5. `paper_c_v1_1_prime_separation_transfer`;
6. `paper_c_v1_1_dyadic_intensity_rate` and
   `paper_c_v1_1_moderate_window`;
7. `paper_c_v1_1_masked_first_moment_band` and
   `paper_c_v1_1_critical_mask_rate`;
8. the `delta = 1/2` macroscopic profile, deep-start complement and global
   interior rate;
9. the spatial/marked Laplace rates and finite-prefix void rate.

The final Kallenberg-type identification of vague Poisson point-process
convergence is not a mechanized endpoint. The v1.1 pass also excludes the
third moment, order-three relation sums, a lower bound of order `N^(7/4)`,
model-optimality of the hard saddle, the marginless lower moderate endpoint,
and a relative border-interior theorem in the moderate tail.

## Imported boundary

No seventh literature premise is introduced. The eventual v1.1 records retain
exactly the six existing interfaces: PNT, AGG89, BS93, ES86, LS04 and NR83.
The hard-conditioning saddle and Rankin estimate themselves require no new
external input.

The frozen AGG89 bridge currently exposes only the coarse bound
`dTV ≤ 2 * (b1 + b2)`. The v1.1 global rate needs the intensity-sensitive
factor `(1 ∧ lambda⁻¹)`. That factor must be proved internally or introduced
under a new additive bridge fingerprint; no historical interface or Palomar
record will be silently strengthened.
