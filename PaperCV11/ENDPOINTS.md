# Paper C v1.1 endpoint ledger

This ledger follows Appendix B.6 of the technical companion. A row marked
`internal` is a proof component; a row marked `Palomar target` is intended to
receive the exact public name shown only after its quantitative contract is
closed.

| Paper result | Intended Lean declaration | External statement interfaces | Status |
|---|---|---|---|
| Proposition 3.3 | `paper_c_v1_1_sharp_kernel_defect` | none | finite (3.4) closed as `paper_c_v1_1_sharp_kernel_defect_finite`; uniform compact-`a` consequence (3.5) open |
| Proposition 3.11 | `paper_c_v1_1_hard_conditioning_saddle` | none | algebraic endpoint proved |
| Theorem 6.16 | `paper_c_v1_1_terminal_density_closure` | NR83 | open |
| Theorem 7.3 | `paper_c_v1_1_two_window_profile` | ES86, NR83 | open |
| quantitative Theorem 1.5 | `paper_c_v1_1_quantitative_second_moment` | inherited proof closure | open |
| Theorem 3.10 | `paper_c_v1_1_prime_separation_transfer` | AGG89 | open |
| Corollary 3.12 | `paper_c_v1_1_dyadic_intensity_rate` | AGG89, ES86, NR83 | open |
| Theorem 1.2 | `paper_c_v1_1_moderate_window` | six frozen interfaces through closure | open |
| Proposition 7.7 | `paper_c_v1_1_masked_first_moment_band` | inherited arithmetic interfaces | open |
| Proposition 7.8 | `paper_c_v1_1_critical_mask_rate` | inherited arithmetic interfaces | open |
| Theorem 8.8 at `delta = 1/2` | `paper_c_v1_1_macroscopic_profile_half` | ES86, NR83 | Palomar target; open |
| Proposition 8.9 at `delta = 1/2` | `paper_c_v1_1_deep_start_rate_half` | PNT, BS93, LS04, NR83 | Palomar target; open |
| Theorem 8.10 | `paper_c_v1_1_global_interior_rate` | PNT, AGG89, BS93, ES86, LS04, NR83 | Palomar target; open |
| Theorem 8.12 | `paper_c_v1_1_spatial_laplace_rate` | six frozen interfaces through closure | final Palomar surface; open |
| Corollary 8.13 | `paper_c_v1_1_marked_laplace_and_tightness` | six frozen interfaces through closure | final Palomar surface; open |
| quantitative Corollary 8.15 | `paper_c_v1_1_prefix_void_rate` | six frozen interfaces through closure | final Palomar surface; open |

The published qualitative results corresponding to the old Theorem 16.2 and
Corollary 16.4 remain historical evidence; v1.1 adds quantitative rates beside
them and does not rename or strengthen those records.

## Qualification boundary

The preferred final Comparator surface contains the four global declarations
`global_interior_rate`, `spatial_laplace_rate`,
`marked_laplace_and_tightness`, and `prefix_void_rate`. The two
`delta = 1/2` inputs are suitable for separate earlier Palomar records if the
global Chen--Stein bridge is not yet closed.

The existing AGG89 interface supplies only the coarse factor `2 * (b1 + b2)`.
The quantitative v1.1 transfer requires the intensity-sensitive factor
`C * (1 ∧ lambda⁻¹) * (b1 + b2)`. This must be introduced additively; the
historical interface and every published Challenge/Solution pair stay
unchanged.
