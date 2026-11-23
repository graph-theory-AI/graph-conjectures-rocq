# Formalization to-do: LLM proofs not yet in Rocq

Proofs from `Graph-Theory-LLM-Proofs` that the adversarial referee judged correct (`CONFIRMED`, `MINOR_GAPS` or `ALREADY_KNOWN` in `verification/verdicts.json` and `verification_astra/verdicts.json`) and that have no checked formal resolution yet. Generated 2026-10-26, updated 2026-11-03.

**Already formalized, so not listed** (`graph-theory-rocq/meta/formal_resolutions.json`, all with closed assumptions): `AX_alon_tarsi_orientation_half_out_degree` (`2209.09107__00`), `AX_chromatic_cochromatic_gap_three_small_clique` (`2408.02400__00`), `AX_directed_kneser_graphs_existence` (`1812.02420__03`), `AX_fair_representation_bipartite_matching_under_representation` (`1611.03196__03`), `AX_list_ramsey_chromatic_family_exact` (`2103.15175__00`), `AX_tournament_clique_number_bounded_witness` (`2310.04265__09`), `AX_tournament_color_avoiding_path_non_transitive` (`2512.10438__00`).

**Formalized on 2026-10-28** (closed assumptions, checked with coqc; not yet registered in `formal_resolutions.json`): `AX_planar_fvs_face_packing_ratio_2` (`1912.01570__00`): `GTMisc.applications.planar_fvs_face_packing.resolution.conjecture2_connected_false`; `AX_large_chromatic_induced_path_uniquely_covered` (`1702.01094__01`): `Chromatic.applications.uniquely_covered_paths.resolution.stable_cover_unique_induced_path_disproved`; `AX_fractional_dichromatic_number_complexity` (`1812.02420__02`): `Digraph.applications.fractional_dichromatic.resolution.AX_fractional_dichromatic_number_complexity`.

**Formalized on 2026-11-03** (closed assumptions; not yet registered in `formal_resolutions.json`):
- `AX_bipartite_concatenation_psi_symmetry` (`1902.10878__01`): `Extremal.applications.psi_asymmetry.resolution.psi_asymmetry`;
- `AX_hypercube_subcube_partitions_dimension_2_asymptotics` (`2401.00299__02`): `Packing.applications.hypercube_square_partitions.resolution.hypercube_square_partitions_asymptotics_resolution`. This is unconditional: Propositions 1.6 and 1.10 of the source are proved too, the latter by an elementary nibble;
- `AX_induced_saturated_infinite_tournament_perturbation` (`2506.08810__03`): `Infinite.applications.tournament_perturbation.resolution.tournament_perturbation_disproof`.

All six resolutions of 2026-10-28 and 2026-11-03 are also accepted by rocq-comparator, with a `rocqchk` replay and no axioms. Their trusted statements and review checklist are in `graph-theory-rocq/challenges/`.

Conjectures are named by their canonical `graph-conjectures` name (`data/conjecture_names.json`); the old identifier, still the key of the review files and of the sibling repositories, follows in parentheses.

**Ordering.** Entries are grouped by the referee verdict and the solver's `would_publish` flag, from most to least important. Within a group they are sorted by the catalog's difficulty score (1 = small finite check, 5 = landmark conjecture), highest first. A harder source problem is taken as a more significant result. Ease of formalization is not considered.

`sol` = first campaign (`attacks/`, gpt-5.6-sol); `astra` = second campaign (gpt-6-astra, `attacks_opg/`, `attacks_arxiv_astra/`, `attacks_retry/`). For the 51 `sol` entries that are `CONFIRMED` or `ALREADY_KNOWN`, `graph-conjectures-rocq/TODO.md` gives a self-contained theorem statement.

## Summary

| # | name | old id | group | campaign | claim | score |
|---:|---|---|---:|---|---|---:|
| 1 | `AX_zombie_number_leaf_attachment_invariance` | `2008.03587__00` | 1 | astra | disproved | 2.5 |
| 2 | `AX_color_balanced_hamilton_cycle_bounds` | `2604.09449__03` | 1 | astra | proved | 2.5 |
| 3 | `AX_erdos_szekeres_collinear_variant_ell_dependence` | `2405.03455__00` | 1 | sol | proved | 2.5 |
| 4 | `AX_c4_free_counting_petersen_dodecahedron` | `2106.03261__01` | 1 | astra | partial | 2.3 |
| 5 | `AX_levine_hat_monotone_success_vanishes` | `2208.06858__01` | 1 | sol | disproved | 2.3 |
| 6 | `AX_geometric_graph_plane_path_cover_bound` | `2507.10840__01` | 1 | astra | proved | 2.1 |
| 7 | `AX_direct_product_multipartite_independence_equals_irredundance` | `1904.02595__00` | 1 | astra | proved | 2.0 |
| 8 | `OPG_3_connected_geodesic_cycles_peripheral_lengths` | `geodesic_cycles_and_tuttes_theorem` | 1 | astra | disproved | 2.0 |
| 9 | `OPG_orthogonality_graph_circular_chromatic_4` | `circular_colouring_the_orthogonality_graph` | 1 | astra | proved | 2.0 |
| 10 | `AX_c4_free_counting_lemma_characterization` | `2106.03261__00` | 2 | astra | partial | 2.2 |
| 11 | `AX_lipschitz_bijection_dictator_xor_inverse` | `1812.09215__00` | 2 | astra | disproved | 2.2 |
| 12 | `OPG_cycle_powers_equivalence_covering_number_linear` | `covering_powers_of_cycles_with_equivalence_subgraphs` | 2 | astra | disproved | 1.0 |
| 13 | `OPG_melnikov_valency_variety_chromatic_bound` | `melnikovs_valency_variety_problem` | 2 | astra | disproved | 1.0 |
| 14 | `AX_k6_minor_min_6_max_8` | `2204.10119__01` | 3 | sol | disproved | 3.9 |
| 15 | `AX_meyniel_cop_number_k_uniform_hypergraph` | `2307.15512__00` | 3 | sol | disproved | 3.5 |
| 16 | `AX_tree_pathwidth_path_partition_height_2k` | `1601.01886__00` | 3 | sol | proved | 3.5 |
| 17 | `AX_generic_norm_distinct_distances_lower_bound` | `2508.08870__00` | 3 | sol | disproved | 3.3 |
| 18 | `AX_digraph_strong_forward_cover_log_n` | `2304.03567__04` | 3 | sol | disproved | 3.1 |
| 19 | `AX_girth_5_planar_fractional_hub_colors` | `1809.05439__00` | 3 | sol | disproved | 3.0 |
| 20 | `AX_independent_set_apx_hard_nonsublinear_separators` | `1704.00125__01` | 3 | sol | disproved | 2.9 |
| 21 | `AX_tournament_clique_number_substitution_digraphs` | `2310.04265__11` | 3 | sol | disproved | 2.9 |
| 22 | `AX_exterior_algebra_mutually_annihilating_extremal` | `1907.06019__01` | 3 | sol | proved | 2.5 |
| 23 | `AX_long_odd_hole_heavy_path_lemma` | `1904.12273__01` | 3 | sol | disproved | 2.5 |
| 24 | `AX_quantum_sorting_poset_lower_bounds_equivalent` | `1902.06473__00` | 3 | sol | proved | 2.5 |
| 25 | `AX_arithmetic_progression_packing_two_regimes` | `2603.02786__03` | 3 | sol | disproved | 2.1 |
| 26 | `AX_group_connectivity_exponentially_many_flows` | `2005.09767__00` | 4 | sol | proved | 3.0 |
| 27 | `AX_digraph_forward_connected_pairs_request_approximation` | `2304.03567__03` | 4 | astra | partial | 2.5 |
| 28 | `AX_quasi_isometry_multiplicative_to_additive_classes` | `2509.09031__00` | 4 | astra | disproved | 2.5 |
| 29 | `AX_random_irregular_subgraph_property_range` | `2207.13651__00` | 4 | astra | proved | 2.5 |
| 30 | `AX_szeged_wiener_difference_2_connected_2n` | `1602.05184__00` | 4 | astra | proved | 2.5 |
| 31 | `AX_sublinear_separator_expansion_exponent_exact` | `2001.09679__00` | 4 | sol | proved | 2.4 |
| 32 | `AX_monochromatic_subset_sums_density_tight` | `2105.15195__00` | 4 | astra | proved | 2.3 |
| 33 | `AX_induced_even_cycle_saturation_polynomial_size` | `2505.24100__01` | 4 | sol | proved | 2.1 |
| 34 | `AX_random_embedding_faces_dense_logarithmic` | `2211.01032__02` | 4 | sol | proved | 2.1 |
| 35 | `OPG_random_lift_k5_chromatic_concentration` | `chromatic_number_of_random_lifts_of_complete_graphs` | 4 | astra | proved | 2.0 |
| 36 | `OPG_random_stable_roommates_solution_probability` | `random_stable_roommates` | 4 | astra | partial | 2.0 |
| 37 | `OPG_uniform_hypergraph_vizing_edge_coloring` | `a_generalization_of_vizings_theorem` | 4 | astra | disproved | 2.0 |
| 38 | `AX_random_embedding_faces_nonorientable_complete` | `2211.01032__03` | 4 | astra | proved | 1.9 |
| 39 | `AX_arithmetic_progression_packing_constant_4_3` | `2603.02786__00` | 4 | astra | proved | 1.5 |
| 40 | `OPG_circular_coloring_mixing_number_rational` | `mixing_circular_colourings_0` | 4 | astra | proved | 1.0 |
| 41 | `AX_distributed_coloring_sparse_sublinear_rounds` | `1802.05582__00` | 5 | sol | proved | 2.9 |
| 42 | `AX_distributed_delta_list_coloring_randomized_rounds` | `1802.05582__01` | 5 | sol | proved | 2.9 |
| 43 | `AX_runsort_permuton_horizontal_uniformity_direct` | `2106.14762__00` | 5 | sol | proved | 2.2 |
| 44 | `AX_near_eulerian_triangulation_precoloring_separated_faces` | `2312.13061__01` | 6 | sol | disproved | 2.9 |
| 45 | `AX_frozen_coloring_glauber_delta_o_n` | `1811.12650__00` | 6 | sol | proved | 2.3 |
| 46 | `AX_separation_choosability_grows_min_degree` | `1802.03727__00` | 7 | sol | proved | 3.5 |
| 47 | `AX_induced_even_cycle_saturation_edge_addition` | `2505.24100__00` | 7 | sol | proved | 3.3 |
| 48 | `AX_groups_uniform_twin_width_strictly_stronger` | `2204.12330__00` | 7 | sol | proved | 3.1 |
| 49 | `AX_annulus_digraph_winding_one_crossing_free` | `2410.13008__00` | 7 | sol | disproved | 3.1 |
| 50 | `AX_modular_chromatic_index_0k_graphs` | `2507.04254__00` | 7 | sol | disproved | 2.8 |
| 51 | `AX_rainbow_stacking_random_colorings_sharp_threshold` | `2405.14795__00` | 7 | sol | proved | 2.6 |
| 52 | `AX_bipartite_johnson_lindenstrauss_bounded_norms` | `1610.00239__00` | 7 | sol | proved | 2.6 |
| 53 | `AX_arithmetic_progression_packing_fixed_n` | `2603.02786__04` | 7 | astra | proved | 2.5 |
| 54 | `AX_c4_orientations_eulerian_avoidable` | `2510.11311__04` | 7 | astra | disproved | 2.2 |
| 55 | `AX_arithmetic_progression_packing_primes_asymptotic` | `2603.02786__01` | 7 | astra | proved | 2.1 |
| 56 | `AX_vertex_transitive_digraph_linear_perimeter_gap` | `2602.16333__00` | 7 | sol | proved | 2.1 |
| 57 | `AX_exterior_algebra_self_annihilating_extremal` | `1907.06019__00` | 7 | sol | proved | 2.0 |
| 58 | `OPG_0_2_graphs_chromatic_number_3` | `three_chromatic_0_2_graphs` | 7 | astra | proved | 2.0 |
| 59 | `OPG_edge_imbalance_multiset_graphic` | `imbalance_conjecture` | 7 | astra | proved | 2.0 |
| 60 | `OPG_k_edge_outerplanar_embedding_polynomial` | `finding_k_edge_outerplanar_graph_embeddings` | 7 | astra | proved | 2.0 |
| 61 | `AX_positive_square_energy_unicyclic_odd_cycle` | `2506.07264__01` | 7 | sol | proved | 1.8 |
| 62 | `AX_tournament_c_fas_paths_matchings_complexity` | `2402.10782__01` | 7 | astra | proved | 1.5 |
| 63 | `AX_heroes_oriented_star_delta_1_m_m` | `2306.04710__01` | 8 | sol | proved | 3.5 |
| 64 | `AX_planar_fractional_vertex_arboricity_2` | `2009.12189__00` | 8 | sol | disproved | 3.2 |
| 65 | `AX_pure_pairs_blockade_polynomial_ordered_graphs` | `2111.00532__01` | 8 | sol | proved | 3.2 |
| 66 | `AX_anticomplete_xy_paths_erdos_posa_optimal` | `2512.17232__00` | 8 | sol | disproved | 3.1 |
| 67 | `AX_bipartite_concatenation_phi_ceiling_formula` | `1902.10878__00` | 8 | sol | disproved | 3.1 |
| 68 | `AX_oriented_graph_semidegree_non_antidirected_paths` | `2503.23191__00` | 8 | sol | disproved | 3.1 |
| 69 | `AX_sublinear_separators_product_structure_tree_depth` | `2208.10074__00` | 8 | sol | disproved | 3.1 |
| 70 | `AX_threshold_ramsey_multiplicity_paths_exact` | `2108.00991__00` | 8 | sol | disproved | 3.1 |
| 71 | `AX_symmetric_intersecting_vector_families_polynomial_gain` | `1909.11578__02` | 8 | sol | disproved | 3.1 |
| 72 | `AX_cop_number_outerplanar_classification` | `1709.09050__01` | 8 | sol | proved | 3.0 |
| 73 | `AX_s_color_connected_vertices_asymptotic` | `2308.15387__00` | 8 | sol | disproved | 2.9 |
| 74 | `AX_flow_reconfiguration_5_flow_connected` | `2512.17342__00` | 8 | sol | disproved | 2.8 |
| 75 | `AX_pure_pairs_blockade_transversal_triangle_polynomial` | `2111.00532__00` | 8 | sol | proved | 2.8 |
| 76 | `AX_cubic_truncation_strong_6_edge_coloring` | `2511.02892__03` | 8 | sol | disproved | 2.7 |
| 77 | `AX_dom_enum_incomparability_st_free_posets` | `2004.07214__00` | 8 | sol | proved | 2.0 |
| 78 | `AX_color_balanced_bipartite_matching_sqrt_k` | `2604.09449__00` | 8 | sol | disproved | 1.9 |

## 1. Confirmed, new, and judged publishable (9)

Referee `CONFIRMED` and solver flag `would_publish`. The best targets.

### 1. `AX_zombie_number_leaf_attachment_invariance` — [Question 4.1](https://arxiv.org/abs/2008.03587)

- **Old id:** `2008.03587__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_zombie_number_leaf_attachment_invariance/ — *A note on deterministic zombies*
- **Campaign / verdict:** astra, claimed `disproved`, referee `CONFIRMED`, difficulty score 2.5 (tier 3); writeup `attacks_retry/2008.03587__00/output.md`
- **Claim:** A 59-vertex cactus requires at least three zombies, but adding one leaf produces a graph requiring exactly two.
- **Referee:** The explicit 59-vertex cactus works exactly as claimed — an independent exact game solver gives z(G) = 3 and z(H) = 2 with (v0, v11) the unique winning pair on H — so Question 4.1 of arXiv:2008.03587 is genuinely disproved.

### 2. `AX_color_balanced_hamilton_cycle_bounds` — [Problem 6.4](https://arxiv.org/abs/2604.09449)

- **Old id:** `2604.09449__03`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_color_balanced_hamilton_cycle_bounds/ — *Colour-balanced subgraphs*
- **Campaign / verdict:** astra, claimed `proved`, referee `CONFIRMED`, difficulty score 2.5 (tier 2); writeup `attacks_retry/2604.09449__03/output.md`
- **Claim:** The requested O(k^2) bound improves to O(k log(k+1)) for Hamilton cycles in both complete and complete bipartite graphs, including for bounded vector labels in an arbitrary norm.
- **Referee:** Every step checks out — the O(k log k) bound is proved in the source paper's own vector-label formulation (and in fact also improves the paper's cornerstone K_{n,n} matching theorem from O(k^2) to O(k log k)); no prior art found, and the only web hit tying this claim to the paper is this campaign's own repository.

### 3. `AX_erdos_szekeres_collinear_variant_ell_dependence` — [Open Problem (Introduction)](https://arxiv.org/abs/2405.03455)

- **Old id:** `2405.03455__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_erdos_szekeres_collinear_variant_ell_dependence/ — *Big line or big convex polygon*
- **Campaign / verdict:** sol, claimed `proved`, referee `CONFIRMED`, difficulty score 2.5 (tier 2); writeup `attacks/2405.03455__00/output.md`
- **Claim:** An alteration argument gives ES_l(n) <= ceil(l(4 ES_n(n))^((n-1)/(n-2))), so the source bound yields a uniform linear-in-l upper bound matching the lower bound in its l-dependence.
- **Referee:** The writeup's elementary alteration/transfer argument bootstrapping the source paper's own diagonal bound ES_n(n) < n^2 2^{n+C sqrt(n log n)} to a uniform linear-in-l upper bound ES_l(n) <= l 2^{n+C_1 sqrt(n log n)} is correct in every step, matches the linear lower bound, and does not appear in the indexed literature (the only citing paper, Furukawa arXiv:2501.03645, obtains a strictly weaker l * 4^{n+O(sqrt(n log n))}).

### 4. `AX_c4_free_counting_petersen_dodecahedron` — [Open Problem 2.17](https://arxiv.org/abs/2106.03261)

- **Old id:** `2106.03261__01`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_c4_free_counting_petersen_dodecahedron/ — *Which graphs can be counted in $C_4$-free graphs?*
- **Campaign / verdict:** astra, claimed `partial`, referee `CONFIRMED`, difficulty score 2.3 (tier 2); writeup `attacks_retry/2106.03261__01/output.md`
- **Claim:** An explicit asymptotically regular C4-free construction disproves Petersen countability; the dodecahedral case remains unresolved here.
- **Referee:** The construction is correct and does disprove countability of the Petersen graph in the exact sense of Conlon-Fox-Sudakov-Zhao Definition 1.3; every step checks out, the key forced-orthogonality lemma (a polarity form of Desargues' theorem) was verified exhaustively by computer, and the question is still listed as open in Conlon's August 2026 survey.

### 5. `AX_levine_hat_monotone_success_vanishes` — [Conjecture 2.2](https://arxiv.org/abs/2208.06858)

- **Old id:** `2208.06858__01`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_levine_hat_monotone_success_vanishes/ — *The success probability in Levine's hat problem, and independent sets i…*
- **Campaign / verdict:** sol, claimed `disproved`, referee `CONFIRMED`, difficulty score 2.3 (tier 2); writeup `attacks/2208.06858__01/output.md`
- **Claim:** A block-tribes construction gives balanced monotone strategies with success probability arbitrarily close to 1/2 for every number of players, so in fact p_monotone(t)=1/2.
- **Referee:** The block-tribes construction is correct under the source paper's exact definitions and disproves Conjecture 2.2 by showing p_monotone(t) = 1/2 for every t; every step was re-derived by hand and verified by exhaustive and exact computation.

### 6. `AX_geometric_graph_plane_path_cover_bound` — [Problem 5.1](https://arxiv.org/abs/2507.10840)

- **Old id:** `2507.10840__01`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_geometric_graph_plane_path_cover_bound/ — *Covering Complete Geometric Graphs by Monotone Paths*
- **Campaign / verdict:** astra, claimed `proved`, referee `CONFIRMED`, difficulty score 2.1 (tier 2); writeup `attacks_retry/2507.10840__01/output.md`
- **Claim:** An odd regular polygon with a central cluster yields point sets requiring at least 3n/4 - O(sqrt(n)) crossing-free paths.
- **Referee:** The odd-polygon-plus-central-cluster construction is correct and gives pi(A) >= 3n/4 - O(sqrt n), affirmatively answering Problem 9 of arXiv:2507.10840; exact-arithmetic ILP confirms pi = 4, 5, 6 for n = 6, 8, 10 against the trivial bounds 3, 4, 5.

### 7. `AX_direct_product_multipartite_independence_equals_irredundance` — [Conjecture 1.2](https://arxiv.org/abs/1904.02595)

- **Old id:** `1904.02595__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_direct_product_multipartite_independence_equals_irredundance/ — *Isoperimetry, Stability, and Irredundance in Direct Products*
- **Campaign / verdict:** astra, claimed `proved`, referee `CONFIRMED`, difficulty score 2.0 (tier 2); writeup `attacks_retry/1904.02595__00/output.md`
- **Claim:** A tensor-rank bound retaining the lonely vertices, combined with rank-nonincreasing coordinate compression, proves the conjecture for all complete multipartite factors.
- **Referee:** Every step re-derived and every load-bearing inequality independently verified by exhaustive computation; the rank-refined social bound t+2rho(A) <= 2^n and the weighted rank-defect inequality alpha_w - W(A) >= 2^n - 2rho(A) are both correct and tight, and together they do prove Alon-Defant Conjecture 1.2.

### 8. `OPG_3_connected_geodesic_cycles_peripheral_lengths` — Geodesic cycles and Tutte's Theorem

- **Old id:** `geodesic_cycles_and_tuttes_theorem`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/op/OPG_3_connected_geodesic_cycles_peripheral_lengths/
- **Campaign / verdict:** astra, claimed `disproved`, referee `CONFIRMED`, difficulty score 2.0 (tier 2); writeup `attacks_opg/geodesic_cycles_and_tuttes_theorem/output.md`
- **Claim:** The eight-vertex graph obtained by inserting a degree-three vertex into every face of a tetrahedron is a counterexample.
- **Referee:** The eight-vertex Kleetope of K4 really is a counterexample to Georgakopoulos–Sprüssel Problem 3 — every step of the writeup checks out, and an exact QF_LRA decision procedure (z3) proves UNSAT, i.e. no positive edge-length assignment on this graph makes all geodesic cycles peripheral.

### 9. `OPG_orthogonality_graph_circular_chromatic_4` — Circular colouring the orthogonality graph

- **Old id:** `circular_colouring_the_orthogonality_graph`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/op/OPG_orthogonality_graph_circular_chromatic_4/
- **Campaign / verdict:** astra, claimed `proved`, referee `CONFIRMED`, difficulty score 2.0 (tier 2); writeup `attacks_retry/circular_colouring_the_orthogonality_graph/output.md`
- **Claim:** A geometric odd-walk lemma excludes every homomorphism from O to a finite locally bipartite graph, and consequently proves χ_c(O)=4.
- **Referee:** The geometric odd-walk lemma is correct (re-verified in exact arithmetic on seven explicit triples and on ~4000 random ones), the locally-bipartite reduction and the K_{p/q} lemma are correct and sharp, so the proof that χ_c(𝒪) = 4 stands; it resolves Conjecture 4.41 of Ghebleh's 2007 SFU thesis, whose Theorem 4.40 (χ_c ≥ 11/3, not the catalog's 3.5) is the true published state of the art.

## 2. Confirmed and publishable, but with a novelty or scope caveat (4)

Referee `CONFIRMED` and `would_publish`, but the referee says part of the result is known or narrower than stated.

### 10. `AX_c4_free_counting_lemma_characterization` — [Question 1.1](https://arxiv.org/abs/2106.03261)

- **Old id:** `2106.03261__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_c4_free_counting_lemma_characterization/ — *Which graphs can be counted in $C_4$-free graphs?*
- **Campaign / verdict:** astra, claimed `partial`, referee `CONFIRMED`, difficulty score 2.2 (tier 2); writeup `attacks_retry/2106.03261__00/output.md`
- **Claim:** The Petersen graph is not countable: a twisted affine-polarity construction gives C4-free graphs with a positive Petersen prediction but no Petersen homomorphism.
- **Referee:** The construction is correct and genuinely disproves countability of the Petersen graph in the exact sense of Conlon-Fox-Sudakov-Zhao Definition 1.3 (which I retrieved verbatim); every step checks out, the load-bearing forced-orthogonality Lemma 1 was verified symbolically and exhaustively over PG(2,5) and PG(2,7), and the twisted/untwisted canonical-copy counts (0 vs 95/436/930/2930/4337 at q=101..191) confirm the mechanism -- but this settles only the Petersen half of Open Problem 2.17, not the catalog's main characterization question, and it duplicates the result already confirmed for the sibling target 2106.03261__01.
- **Caveat:** same result as `AX_c4_free_counting_petersen_dodecahedron` (#10); formalize once for both

### 11. `AX_lipschitz_bijection_dictator_xor_inverse` — [Informal Question (Section 2)](https://arxiv.org/abs/1812.09215)

- **Old id:** `1812.09215__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_lipschitz_bijection_dictator_xor_inverse/ — *Lipschitz bijections between boolean functions*
- **Campaign / verdict:** astra, claimed `disproved`, referee `CONFIRMED`, difficulty score 2.2 (tier 2); writeup `attacks_retry/1812.09215__00/output.md`
- **Claim:** No: every such bijection satisfies n <= 1+(k-1)+...+(k-1)^(D-1), where D is its inverse Lipschitz constant, and linear 2-Lipschitz tree maps attain the resulting bound.
- **Referee:** The counting argument is correct as written and I could not break it — every k-local Dictator-to-XOR bijection satisfies n <= 1+(k-1)+...+(k-1)^{D-1}, so Lip(phi^-1) >= 1 + log n/log k and the answer to Johnston-Scott's question is "no"; the matching construction in Section 3, however, is Rao-Shinkar's tree construction (arXiv:1501.03016, Theorem 2 and the generalisation remark) reproduced without attribution.
- **Caveat:** matching construction is Rao–Shinkar (arXiv:1501.03016) reproduced; only the lower bound is new

### 12. `OPG_cycle_powers_equivalence_covering_number_linear` — Covering powers of cycles with equivalence subgraphs

- **Old id:** `covering_powers_of_cycles_with_equivalence_subgraphs`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/op/OPG_cycle_powers_equivalence_covering_number_linear/
- **Campaign / verdict:** astra, claimed `disproved`, referee `CONFIRMED`, difficulty score 1.0 (tier 1); writeup `attacks_opg/covering_powers_of_cycles_with_equivalence_subgraphs/output.md`
- **Claim:** Noncomplete powers of cycles have equivalence covering number Θ(log(k+1)), contradicting the proposed Ω(k) lower bound.
- **Referee:** The construction and the rank lower bound are both correct and verified by brute force (eq(C_8^3)=eq(C_12^3)=3, eq(C_10^4)=4), so eq(C_n^k)=Theta(log k) and the Omega(k) conjecture is genuinely disproved — but the lower-bound half is a rediscovery of Alon (1986) Thm 1.1/Cor 1.2, and the source literature it contradicts (West's REGS page) contains a false assertion "eq(C_n^k)=k+1 when (k+1)|n" that Alon's own 1986 corollary already refutes.
- **Caveat:** lower-bound half is Alon (1986), Thm 1.1/Cor 1.2

### 13. `OPG_melnikov_valency_variety_chromatic_bound` — Melnikov's valency-variety problem

- **Old id:** `melnikovs_valency_variety_problem`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/op/OPG_melnikov_valency_variety_chromatic_bound/
- **Campaign / verdict:** astra, claimed `disproved`, referee `CONFIRMED`, difficulty score 1.0 (tier 1); writeup `attacks_opg/melnikovs_valency_variety_problem/output.md`
- **Claim:** A 37-vertex graph has chromatic number 3 and degree set {0,1,...,29}, making the proposed right-hand side equal to 3; moreover, 37 vertices is minimum.
- **Referee:** The 37-vertex graph was rebuilt from the prose and verified exactly (w=30, chi=3, RHS=3), the minimality proof checks out line by line and is corroborated by an independent mechanisation, so the problem is disproved as literally stated — but the counterexample lives entirely on the degenerate isolated vertex, and the min-degree->=1 version of Melnikov's question is untouched and remains open.
- **Caveat:** counterexample relies on a degenerate isolated vertex; min-degree-1 version still open

## 3. Confirmed, but narrow in scope (12)

Referee `CONFIRMED`, not flagged publishable.

### 14. `AX_k6_minor_min_6_max_8` — Informal Conjecture: min degree $\geq 6$, max degree $\leq 8$ forces $K_6$ minor

- **Old id:** `2204.10119__01`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_k6_minor_min_6_max_8/ — *Bipartite graphs with no $K_6$ minor*
- **Campaign / verdict:** sol, claimed `disproved`, referee `CONFIRMED`, difficulty score 3.9 (tier 4); writeup `attacks/2204.10119__01/output.md`
- **Claim:** An explicit 28-vertex 4-clique amalgam of two apex graphs is K6-minor-free and has degrees only 6, 7, and 8.
- **Referee:** The 28-vertex 4-clique amalgam of two apex graphs is fully machine-verified (degrees 6^22 7^4 8^2, both pieces apex-over-planar with certified embeddings) and the two supporting lemmas are sound textbook facts, so the graph has no K6 minor and genuinely refutes the parenthetical conjecture.

### 15. `AX_meyniel_cop_number_k_uniform_hypergraph` — Conjecture 1.4

- **Old id:** `2307.15512__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_meyniel_cop_number_k_uniform_hypergraph/ — *Catching a robber on a random $k$-uniform hypergraph*
- **Campaign / verdict:** sol, claimed `disproved`, referee `CONFIRMED`, difficulty score 3.5 (tier 4); writeup `attacks/2307.15512__00/output.md`
- **Claim:** A clique-plus-sparse-random-core construction gives k = Theta(sqrt(n)) and c(H) = Omega(n^(1/4) log n), exceeding sqrt(n/k) by a logarithmic factor.
- **Referee:** The clique-plus-random-attachment construction is sound — it yields connected k-graphs with k = Theta(sqrt(n)) and c(H) = Omega(sqrt(n/k) log n), refuting the uniform O(sqrt(n/k)) bound of Conjecture 1.4; every step re-derived by hand and validated by machine.

### 16. `AX_tree_pathwidth_path_partition_height_2k` — Optimality of factor 2 in Lemma 4

- **Old id:** `1601.01886__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_tree_pathwidth_path_partition_height_2k/ — *Pathwidth and nonrepetitive list coloring*
- **Campaign / verdict:** sol, claimed `proved`, referee `CONFIRMED`, difficulty score 3.5 (tier 3); writeup `attacks/1601.01886__00/output.md`
- **Claim:** For every k >= 1, an explicit tree has pathwidth k and minimum part-counting path-partition height 2k, so the factor 2 is sharp.
- **Referee:** The construction and all proofs check out (computationally verified up to |V|=764); the factor 2 in Lemma 4 is indeed unavoidable, with the exact optimum being height 2k-1 in the paper's edge-counting height convention (the writeup itself proves and flags this 2k vs 2k-1 convention point).

### 17. `AX_generic_norm_distinct_distances_lower_bound` — Conjecture 1.5

- **Old id:** `2508.08870__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_generic_norm_distinct_distances_lower_bound/ — *Distinct Directions and Distinct Distances in $\mathbb{R}^d$*
- **Campaign / verdict:** sol, claimed `disproved`, referee `CONFIRMED`, difficulty score 3.3 (tier 3); writeup `attacks/2508.08870__00/output.md`
- **Claim:** Two parallel arithmetic progressions already give noncollinear planar sets of n points with at most (3/2+o(1))n distinct distances in every norm.
- **Referee:** The disproof is correct — two parallel arithmetic progressions give a noncollinear planar n-point set with at most (3/2)n-2 distinct distances in every norm, and the general-d variant caps the coefficient at d-1+1/(2(d-1)) < d, refuting Conjecture 1.5 of arXiv:2508.08870 as stated (in both v1 and v2) for every d >= 2 and every norm, not just generic ones.

### 18. `AX_digraph_strong_forward_cover_log_n` — Conjecture 1

- **Old id:** `2304.03567__04`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_digraph_strong_forward_cover_log_n/ — *Temporalizing digraphs via linear-size balanced bi-trees*
- **Campaign / verdict:** sol, claimed `disproved`, referee `CONFIRMED`, difficulty score 3.1 (tier 3); writeup `attacks/2304.03567__04/output.md`
- **Claim:** A cyclic chain of directed three-way diamonds on 3m vertices has m vertex pairs such that any ordering forward-connects at most one of them.
- **Referee:** The diamond-chain construction is correct and machine-verified; under the source paper's own verbatim definition of forward cover it refutes Conjecture 1 of arXiv:2304.03567 with an n/3 lower bound.

### 19. `AX_girth_5_planar_fractional_hub_colors` — Informal conjecture on improved color ratio in Theorem 5

- **Old id:** `1809.05439__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_girth_5_planar_fractional_hub_colors/ — *Fractional coloring of planar graphs of girth five*
- **Campaign / verdict:** sol, claimed `disproved`, referee `CONFIRMED`, difficulty score 3.0 (tier 3); writeup `attacks/1809.05439__00/output.md`
- **Claim:** Under Theorem 5's triangle-free-planar quantifiers, a 23-vertex graph formed from two subdivided 5-wheels gives an explicit counterexample.
- **Referee:** The 23-vertex two-wheel construction is a correct, computationally verified counterexample to the concrete conjectured statement (subsets of {1..9}, all vertices >= 3 colors, x gets 5) under the intended triangle-free-planar quantifiers of Theorem 5.

### 20. `AX_independent_set_apx_hard_nonsublinear_separators` — Open Problem (Section 1.2): APX-hardness on classes without sublinear separators

- **Old id:** `1704.00125__01`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_independent_set_apx_hard_nonsublinear_separators/ — *Thin graph classes and polynomial-time approximation schemes*
- **Campaign / verdict:** sol, claimed `disproved`, referee `CONFIRMED`, difficulty score 2.9 (tier 3); writeup `attacks/1704.00125__01/output.md`
- **Claim:** Bipartite graphs of maximum degree at most 20 form a subgraph-closed class with linear separator lower bounds and exponential expansion, while Maximum Independent Set is exactly polynomial-time solvable.
- **Referee:** The counterexample (bipartite graphs of maximum degree 20) is mathematically correct and verified end-to-end, and it does refute the universal statement Dvořák wrote, but the refutation is assembled from textbook facts and kills only the "for example" formalization of a deliberately hedged prose question, not the underlying research program.

### 21. `AX_tournament_clique_number_substitution_digraphs` — Conjecture 6.1

- **Old id:** `2310.04265__11`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_tournament_clique_number_substitution_digraphs/ — *Clique number of tournaments*
- **Campaign / verdict:** sol, claimed `disproved`, referee `CONFIRMED`, difficulty score 2.9 (tier 3); writeup `attacks/2310.04265__11/output.md`
- **Claim:** A hereditary class whose members all satisfy directed clique number and dichromatic number at most two has a substitution closure containing digraphs of directed clique number two and arbitrarily large dichromatic number.
- **Referee:** The counterexample is correct — a hereditary class of oriented graphs with dic = diomega <= 2 whose substitution closure contains digraphs with diomega = 2 and unbounded dichromatic number, refuting Conjecture 6.1 as stated; every lemma checks out by hand and the base instances were verified exhaustively by computer.

### 22. `AX_exterior_algebra_mutually_annihilating_extremal` — [Question on extremal mutually annihilating pairs (Theorem 2.4)](https://arxiv.org/abs/1907.06019)

- **Old id:** `1907.06019__01`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_exterior_algebra_mutually_annihilating_extremal/ — *Combinatorics in the exterior algebra and the Bollobás Two Families The…*
- **Campaign / verdict:** sol, claimed `proved`, referee `CONFIRMED`, difficulty score 2.5 (tier 2); writeup `attacks/1907.06019__01/output.md`
- **Claim:** Every extremal mutually annihilating pair consists of two full exterior stars generated by the same one-dimensional subspace of V.
- **Referee:** The characterization of extremal mutually annihilating pairs as common v-stars is correct; every step checks out, the set-system equality lemma agrees with Matsumoto-Tokushige 1989 and with exhaustive computation, and the rigidity lemma was confirmed by exact nullspace computations.

### 23. `AX_long_odd_hole_heavy_path_lemma` — [Informal Conjecture (heavy path extension)](https://arxiv.org/abs/1904.12273)

- **Old id:** `1904.12273__01`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_long_odd_hole_heavy_path_lemma/ — *Detecting a long odd hole*
- **Campaign / verdict:** sol, claimed `disproved`, referee `CONFIRMED`, difficulty score 2.5 (tier 2); writeup `attacks/1904.12273__01/output.md`
- **Claim:** For every fixed long-hole threshold at least seven, a four-vertex C-major set admits no bounded catching path, although C is the unique long odd hole.
- **Referee:** The four-vertex counterexample is correct and computationally verified, and it even lives inside a "candidate" graph in the source paper's sense, so the heavy path extension of Chudnovsky-Scott-Seymour fails for every threshold ell >= 6 under any reasonable reading.

### 24. `AX_quantum_sorting_poset_lower_bounds_equivalent` — [Conjecture on LB and QLB equivalence](https://arxiv.org/abs/1902.06473)

- **Old id:** `1902.06473__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_quantum_sorting_poset_lower_bounds_equivalent/ — *Information-theoretic lower bounds for quantum sorting*
- **Campaign / verdict:** sol, claimed `proved`, referee `CONFIRMED`, difficulty score 2.5 (tier 2); writeup `attacks/1902.06473__00/output.md`
- **Claim:** Under normalized Lebesgue averaging on the chain polytope, QLB(P) lies between ln e(P) and (ln 2)^{-1}ln e(P), and hence between LB(P)/2 and LB(P)/ln 2.
- **Referee:** The writeup correctly proves ln e(P) <= QLB(P) <= log2 e(P) for all finite posets via Stanley's rank log-concavity, hence LB(P)/2 <= QLB(P) <= LB(P)/ln 2, resolving the source paper's conjecture with explicit constants; every step re-derived, all references verified against the arXiv TeX sources, and all claims confirmed computationally on every poset with at most 6 elements plus random posets on 7-8 elements.

### 25. `AX_arithmetic_progression_packing_two_regimes` — Conjecture 6

- **Old id:** `2603.02786__03`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_arithmetic_progression_packing_two_regimes/ — *Packing arithmetic progressions*
- **Campaign / verdict:** sol, claimed `disproved`, referee `CONFIRMED`, difficulty score 2.1 (tier 2); writeup `attacks/2603.02786__03/output.md`
- **Claim:** Integer-translate packings satisfy M_k(n) >= (6619/10800-o(1))nk^2/ln k when k=o(n), contradicting the conjectured constant 1/2.
- **Referee:** The writeup's elementary weighted-core counting argument is correct and yields M_k(n) >= (6619/10800 - o(1)) nk^2/ln k for k -> infinity, k = o(n), genuinely refuting the constant 1/2 in the first clause of Conjecture 6 of arXiv:2603.02786 while remaining consistent with the paper's proven bounds.

## 4. Correct modulo routine repairs, judged publishable (15)

Referee `MINOR_GAPS` and `would_publish`. The gaps must be repaired, at least on paper, before formalizing.

### 26. `AX_group_connectivity_exponentially_many_flows` — Conjecture 1.10

- **Old id:** `2005.09767__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_group_connectivity_exponentially_many_flows/ — *Many flows in the group connectivity setting*
- **Campaign / verdict:** sol, claimed `proved`, referee `MINOR_GAPS`, difficulty score 3.0 (tier 3); writeup `attacks/2005.09767__00/output.md`
- **Claim:** A finite-field support bound settles the order-7 case, while a CRT decomposition and three explicit families of flows give at least 3^{n/12} admissible Z_6-flows.
- **Referee:** The two genuinely new parts (Z_7 via the Alon–Füredi/footprint bound, Z_6 via a CRT three-family construction) survive full step-by-step and computational scrutiny; the only defect found is a trivially repairable small-n bookkeeping slack in extracting a uniform constant from the source's Theorem 1.9 for groups of order >= 8.

### 27. `AX_digraph_forward_connected_pairs_request_approximation` — [Problem 4](https://arxiv.org/abs/2304.03567)

- **Old id:** `2304.03567__03`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_digraph_forward_connected_pairs_request_approximation/ — *Temporalizing digraphs via linear-size balanced bi-trees*
- **Campaign / verdict:** astra, claimed `partial`, referee `MINOR_GAPS`, difficulty score 2.5 (tier 3); writeup `attacks_retry/2304.03567__03/output.md`
- **Claim:** An explicit gap reduction shows that RFCPP has no polynomial-time o(log |V|)-approximation unless P=NP, and hence rules out constant-factor approximation under that assumption.
- **Referee:** The gap reduction from directed two-linkage is correct and machine-verified end to end — RFCPP has no polytime o(log|V|)-approximation unless P=NP, answering Problem 4 of arXiv:2304.03567 negatively — but Lemma 7 silently re-derives the source paper's own Proposition 4 and the two-linkage NP-completeness is never cited.

### 28. `AX_quasi_isometry_multiplicative_to_additive_classes` — [Conjecture 1.2](https://arxiv.org/abs/2509.09031)

- **Old id:** `2509.09031__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_quasi_isometry_multiplicative_to_additive_classes/ — *Asymptotic structure. II. Path-width and additive quasi-isometry*
- **Campaign / verdict:** astra, claimed `disproved`, referee `MINOR_GAPS`, difficulty score 2.5 (tier 3); writeup `attacks_retry/2509.09031__00/output.md`
- **Claim:** A finite counterexample is obtained from a contraction- and subdivision-closed class whose branch vertices are pairwise joined by internally degree-two paths.
- **Referee:** No error found — the class of "thread-complete" graphs is genuinely contraction/subdivision-closed (verified exhaustively), the (2,1)-quasi-isometry and all Section-6 distance identities check out computationally, and the quantitative core reproduces exactly as an LP; several justifications are terse but all are routinely repairable, and the intricate rigidity Lemma 3.1 could only be checked by hand.

### 29. `AX_random_irregular_subgraph_property_range` — [Informal Conjecture on Property (*) for d = o(n/log n)](https://arxiv.org/abs/2207.13651)

- **Old id:** `2207.13651__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_random_irregular_subgraph_property_range/ — *On random irregular subgraphs*
- **Campaign / verdict:** astra, claimed `proved`, referee `MINOR_GAPS`, difficulty score 2.5 (tier 3); writeup `attacks_retry/2207.13651__00/output.md`
- **Claim:** A half-interval decomposition of the vertex labels, followed by read-d Hölder bounds for uniform spacings, proves Property (*) throughout d = o(n/log n).
- **Referee:** The half-interval (random-cut) decoupling is sound and every step survives an independent re-derivation plus numerical verification; the only real defect is that the load-bearing read-R Hölder lemma is asserted with a non-proof and no attribution (it is Finner's 1992 inequality), so subject to that repair the writeup does appear to close the Fox-Luo-Pham conjecture that H(G) satisfies Property (*) for all d = o(n/log n).

### 30. `AX_szeged_wiener_difference_2_connected_2n` — [Conjecture 5](https://arxiv.org/abs/1602.05184)

- **Old id:** `1602.05184__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_szeged_wiener_difference_2_connected_2n/ — *On the difference between the Szeged and Wiener index*
- **Campaign / verdict:** astra, claimed `proved`, referee `MINOR_GAPS`, difficulty score 2.5 (tier 2); writeup `attacks_retry/1602.05184__00/output.md`
- **Claim:** Every 2-connected graph outside the three exceptional families satisfies η(G) ≥ min{2n, 3n−10}, proving the conjecture for n ≥ 10.
- **Referee:** The proof of Conjecture 5 (η(G) ≥ 2n for 2-connected G, n ≥ 10, outside the three exceptional families) survives a full step-by-step audit and massive computation — every lemma holds on all 2-connected graphs up to n = 9 and the bound is exactly tight on all 900,969,091 2-connected graphs on 11 vertices — with only two one-line justification gaps and one missing attribution (the good-edge identity is Proposition 6 of the source paper).

### 31. `AX_sublinear_separator_expansion_exponent_exact` — [Informal open question on the exact value of $b_\varepsilon$](https://arxiv.org/abs/2001.09679)

- **Old id:** `2001.09679__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_sublinear_separator_expansion_exponent_exact/ — *A note on sublinear separators and expansion*
- **Campaign / verdict:** sol, claimed `proved`, referee `MINOR_GAPS`, difficulty score 2.4 (tier 2); writeup `attacks/2001.09679__00/output.md`
- **Claim:** A two-dimensional grid thickening of bounded-degree expanders attains expansion exponent 1/(2ε)-1 while retaining separator exponent 1-ε, closing Dvořák's gap.
- **Referee:** The grid-thickened-expander construction survives detailed hand and computational checking and does appear to give a class with separators Θ(n^{1-ε}) and expansion O(r^{1/(2ε)-1}), closing Dvořák's gap; the only real defects are a benign mismatch with Dvořák's exact (sup-based) definition of b_ε and a tersely sketched isolated-vertex padding step, both routinely repairable.

### 32. `AX_monochromatic_subset_sums_density_tight` — [Conjecture on tightness of the upper bound for all r ≥ 3](https://arxiv.org/abs/2105.15195)

- **Old id:** `2105.15195__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_monochromatic_subset_sums_density_tight/ — *The upper logarithmic density of monochromatic subset sums*
- **Campaign / verdict:** astra, claimed `proved`, referee `MINOR_GAPS`, difficulty score 2.3 (tier 2); writeup `attacks_retry/2105.15195__00/output.md`
- **Claim:** A prime-based reduction closes the interlacing gap and proves c_r = b_0^(r-1)/(2r) for every r >= 2.
- **Referee:** The argument survives every check I could apply and would prove Conlon-Fox-Pham's Conjecture 10, but the writeup misidentifies its own contribution — its advertised "key addition" (Lemma 3) is a weaker re-derivation of CFP's already-published Lemma 2, while the only genuinely new step (Lemma 1, the r>=3 form of CFP's Lemma 7) is inherited from the previous attempt and never identified as the novelty.

### 33. `AX_induced_even_cycle_saturation_polynomial_size` — [Question 1.8](https://arxiv.org/abs/2505.24100)

- **Old id:** `2505.24100__01`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_induced_even_cycle_saturation_polynomial_size/ — *Halfway to induced saturation for even cycles*
- **Campaign / verdict:** sol, claimed `proved`, referee `MINOR_GAPS`, difficulty score 2.1 (tier 2); writeup `attacks/2505.24100__01/output.md`
- **Claim:** Line graphs of cubic hypohamiltonian graphs give examples on exactly 3(t-1) vertices for all sufficiently large t, while the finitely many remaining values are absorbed into the constant term of a linear polynomial.
- **Referee:** The line-graph-of-cubic-hypohamiltonian construction is correct and fully verified by machine (answering Question 1.8 affirmatively with f linear, 3t-3 vertices for t >= 14), but the writeup cites Theorem 1.6 for 3 <= t <= 13 while the source paper states it only for t >= 5, a trivially repairable slip for t in {3,4} (fixed via Observation 1.5 of the same paper); note also that concurrent work (Choi, arXiv:2608.24202, Aug 2026) independently subsumes the yes/no answer via a stronger 8q-vertex induced-saturated construction.

### 34. `AX_random_embedding_faces_dense_logarithmic` — [Conjecture 9.3](https://arxiv.org/abs/2211.01032)

- **Old id:** `2211.01032__02`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_random_embedding_faces_dense_logarithmic/ — *Random Embeddings of Graphs: The Expected Number of Faces in Most Graph…*
- **Campaign / verdict:** sol, claimed `proved`, referee `MINOR_GAPS`, difficulty score 2.1 (tier 2); writeup `attacks/2211.01032__02/output.md`
- **Claim:** For simple graphs, deferred exposure of the random rotations gives an O(log n) upper bound, while weighted simple facial cycles give a matching Omega(log n) lower bound.
- **Referee:** After re-deriving every step by hand and verifying every checkable component computationally (exact enumeration and Monte Carlo), I found no substantive error — only a one-unit slip in an intermediate admissible-count in §3.2 and implicit large-n thresholds — so the writeup appears to genuinely prove Conjecture 9.3 for simple graphs, even improving the source's K_n upper constant to the Mauk–Stahl value 2; the strength of the claim warrants an independent expert pass.

### 35. `OPG_random_lift_k5_chromatic_concentration` — Chromatic number of random lifts of complete graphs

- **Old id:** `chromatic_number_of_random_lifts_of_complete_graphs`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/op/OPG_random_lift_k5_chromatic_concentration/
- **Campaign / verdict:** astra, claimed `proved`, referee `MINOR_GAPS`, difficulty score 2.0 (tier 2); writeup `attacks_opg/chromatic_number_of_random_lifts_of_complete_graphs/output.md`
- **Claim:** A random h-lift of K_5 has chromatic number 3 asymptotically almost surely.
- **Referee:** The load-bearing novelty — a Bregman/permanent bound that keeps the perfect-matching constraint Nir–Pérez-Giménez relaxed away, making the uniform overlap the global second-moment maximum at d=4 — survives full re-derivation and numerical attack, so the a.a.s. 3-colourability of random lifts of K_5 appears genuinely proved; only two standard-but-sketched analytic steps (the uniform local CLT of Lemma 2 and the small-subgraph-conditioning limit in §7) fall short of being written out.

### 36. `OPG_random_stable_roommates_solution_probability` — Random stable roommates

- **Old id:** `random_stable_roommates`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/op/OPG_random_stable_roommates_solution_probability/
- **Campaign / verdict:** astra, claimed `partial`, referee `MINOR_GAPS`, difficulty score 2.0 (tier 2); writeup `attacks_opg/random_stable_roommates/output.md`
- **Claim:** A planted-matching and short-cycle argument gives the partial upper bound P_n = O(n^{-1/6} sqrt(log n)), but does not establish the conjectured exponent 1/4.
- **Referee:** The planted-matching/short-cycle argument holds up under full re-derivation and simulation, and its P_n = O(n^{-1/6} sqrt(log n)) genuinely improves the published Chin-Michelen bound n^{-1/17}; the Mertens conjecture itself is untouched, and the only real defects are one unproved (but true) truncated-binomial inequality, a missing trivial case in the exchange lemma, and a total failure to cite or position against Chin-Michelen and Pittel.

### 37. `OPG_uniform_hypergraph_vizing_edge_coloring` — A generalization of Vizing's Theorem?

- **Old id:** `a_generalization_of_vizings_theorem`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/op/OPG_uniform_hypergraph_vizing_edge_coloring/
- **Campaign / verdict:** astra, claimed `disproved`, referee `MINOR_GAPS`, difficulty score 2.0 (tier 2); writeup `attacks_opg/a_generalization_of_vizings_theorem/output.md`
- **Claim:** A probabilistic construction gives a simple 100-uniform hypergraph with maximum 99-codegree at most 200 that requires at least 451 colors, contradicting the proposed bound of 299.
- **Referee:** I could not break the argument — every step, including the entropy matching-counting lemma, checks out under brute-force and independent re-derivation — but the single load-bearing error term (the o(N) in the counting lemma) is never quantified and in fact decays only like a 99th root, so the counterexample exists only for n around 10^455; that quantification is missing from the writeup.

### 38. `AX_random_embedding_faces_nonorientable_complete` — [Conjecture 9.5](https://arxiv.org/abs/2211.01032)

- **Old id:** `2211.01032__03`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_random_embedding_faces_nonorientable_complete/ — *Random Embeddings of Graphs: The Expected Number of Faces in Most Graph…*
- **Campaign / verdict:** astra, claimed `proved`, referee `MINOR_GAPS`, difficulty score 1.9 (tier 2); writeup `attacks_retry/2211.01032__03/output.md`
- **Claim:** A fixed-vertex decomposition proves E[F_n] <= ln n + O(1), with the stronger upper bound ln n + 1/4 + gamma/2 + o(1).
- **Referee:** The suspected violation of equation (11) at n=50 was Monte-Carlo noise from a single rare face — with 400k replicates every length-bin sits at exactly the slack (D/(n-2))^2 the inequality predicts — and after re-deriving every step and verifying the model reduction, the exposure lemma, (2), (5), (6), (9)-(11) and the final asymptotics computationally, I found no mathematical error, only a compressed conditioning argument for (11) and an unnamed large-n threshold.

### 39. `AX_arithmetic_progression_packing_constant_4_3` — [Conjecture 1](https://arxiv.org/abs/2603.02786)

- **Old id:** `2603.02786__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_arithmetic_progression_packing_constant_4_3/ — *Packing arithmetic progressions*
- **Campaign / verdict:** astra, claimed `proved`, referee `MINOR_GAPS`, difficulty score 1.5 (tier 1); writeup `attacks_retry/2603.02786__00/output.md`
- **Claim:** Fixed-size CRT-generic prime blocks, together with clustered residue classes for their multiples and a tail decomposition, give m(n) ~ (4/3)n^(3/2)/log n.
- **Referee:** Every step of the CRT-phase construction checks out and I verified the whole Section 5 block packing (composites included) by brute force, but the prime-range core is Theorem 1.1 of arXiv:2609.07487 (Hou-Liu-Zhao, 7 Sep 2026, nine days before the attack ran); only the bundle/colouring extension to composite differences is new.

### 40. `OPG_circular_coloring_mixing_number_rational` — Mixing Circular Colourings

- **Old id:** `mixing_circular_colourings_0`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/op/OPG_circular_coloring_mixing_number_rational/
- **Campaign / verdict:** astra, claimed `proved`, referee `MINOR_GAPS`, difficulty score 1.0 (tier 1); writeup `attacks_opg/mixing_circular_colourings_0/output.md`
- **Claim:** For an n-vertex graph with an edge, the circular mixing threshold is rational, with reduced numerator at most n+1.
- **Referee:** The argument (difference-constraint encoding of orientation classes + a Farey-type bound on zero-weight cycles) is sound and survived a full re-implementation against brute force on 360+ parameter pairs; the only real omission is that the writeup adopts a mixing convention and an unrestricted infimum taken from OPG's truncated rendering of Brewster-Noel Definition 1.2 without checking they agree with the source's "inf{r in Q : r >= chi_c(G) ...}" - they do, so the theorem stands as stated.

## 5. Correct modulo routine repairs (3)

Referee `MINOR_GAPS`, not flagged publishable. Written repairs for most are in `graph-theory-rocq/meta/GAP_REPAIRS.md`.

### 41. `AX_distributed_coloring_sparse_sublinear_rounds` — Open problem on sublinear round complexity

- **Old id:** `1802.05582__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_distributed_coloring_sparse_sublinear_rounds/ — *Distributed coloring in sparse graphs with fewer colors*
- **Campaign / verdict:** sol, claimed `proved`, referee `MINOR_GAPS`, difficulty score 2.9 (tier 3); writeup `attacks/1802.05582__00/output.md`
- **Claim:** In the intended deterministic LOCAL formulation, a high-degree-component decomposition gives a second algorithm running in O(n/d+polylog n) rounds, which combined with the quoted d-dependent algorithm yields a uniform o(n) bound.
- **Referee:** The high-degree/low-degree wrapper argument is mathematically sound (Lemma 2's weak-diameter bound and the deg+1 residual inequality both re-derive and verify computationally), giving a genuine uniform O(n^{4/5} log^{3/5} n) bound; what remains are routine repairable details — the mad(G)=d / clique-escape boundary of the source's Theorem 1.3, standard distributed-implementation details, and unverified novelty.

### 42. `AX_distributed_delta_list_coloring_randomized_rounds` — Question on randomized list-coloring round complexity

- **Old id:** `1802.05582__01`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_distributed_delta_list_coloring_randomized_rounds/ — *Distributed coloring in sparse graphs with fewer colors*
- **Campaign / verdict:** sol, claimed `proved`, referee `MINOR_GAPS`, difficulty score 2.9 (tier 3); writeup `attacks/1802.05582__01/output.md`
- **Claim:** Under the standard LOCAL-model formulation of Corollary 2.1, a randomized algorithm finds a Δ-list-coloring in O(log^2 n) rounds, with no polynomial dependence on Δ.
- **Referee:** The claimed O(log^2 n)-round randomized LOCAL Delta-list-coloring algorithm is mathematically sound (every lemma re-derived and computationally corroborated; 384 end-to-end simulated runs all succeeded); only routine repairs remain — informal bookkeeping in Lemma 2's branching count and an O(1)-round patch to match Corollary 2.1's exact "color or report infeasible" formulation — and no prior publication of the list variant was found.

### 43. `AX_runsort_permuton_horizontal_uniformity_direct` — [Direct Proof of Horizontal Uniformity](https://arxiv.org/abs/2106.14762)

- **Old id:** `2106.14762__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_runsort_permuton_horizontal_uniformity_direct/ — *The runsort permuton*
- **Campaign / verdict:** sol, claimed `proved`, referee `MINOR_GAPS`, difficulty score 2.2 (tier 2); writeup `attacks/2106.14762__00/output.md`
- **Claim:** A direct size-biased run-profile calculation gives interior density e^(y-1) in every block of runs sorted by its first entry, hence no dependence on x.
- **Referee:** The size-biased run-profile argument is mathematically sound and genuinely avoids the explicit characterization of R (all identities and the limiting measure verified symbolically and by n=10^6 Monte Carlo), but the concentration step (Section 3 of the writeup) is an outline whose routine details are left to the reader, and whether a probabilistic local-limit computation counts as the "direct combinatorial" proof the authors asked for is an irreducible judgment call that the writeup itself flags.

## 6. Partly formalized: finish the job (2)

Referee `MINOR_GAPS`; a supporting lemma is already checked in `graph-theory-rocq`.

### 44. `AX_near_eulerian_triangulation_precoloring_separated_faces` — Conjecture 4

- **Old id:** `2312.13061__01`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_near_eulerian_triangulation_precoloring_separated_faces/ — *Precoloring extension in planar near-Eulerian-triangulations*
- **Campaign / verdict:** sol, claimed `disproved`, referee `MINOR_GAPS`, difficulty score 2.9 (tier 3); writeup `attacks/2312.13061__01/output.md`
- **Claim:** For ℓ=6, a threefold-subdivided grid with a length-three boundary ear gives counterexamples for every d, using the viable precoloring (1,2,3,4,3,2).
- **Referee:** The counterexample is correct and Conjecture 4 as stated is disproved — I independently verified every structural hypothesis and the viability of the precoloring by computer, using the paper's actual definition of viability — but the writeup misattributes to the source a "signed weak-dual balance" definition of viability that is not the paper's definition, a gap I had to close myself.
- **Already done:** six-cycle viability certificate checked (`chromatic-theory/theories/applications/gap_repairs/viable_boundary.v`); arbitrary-parameter planar construction still open

### 45. `AX_frozen_coloring_glauber_delta_o_n` — [Informal: Δ = o(n) condition not necessary for Corollary 2](https://arxiv.org/abs/1811.12650)

- **Old id:** `1811.12650__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_frozen_coloring_glauber_delta_o_n/ — *Frozen $(Δ+1)$-colourings of bounded degree graphs*
- **Campaign / verdict:** sol, claimed `proved`, referee `MINOR_GAPS`, difficulty score 2.3 (tier 2); writeup `attacks/1811.12650__00/output.md`
- **Claim:** For every connected noncomplete n-vertex graph, the frozen proportion among its (Δ+1)-colourings is at most 4/(n+4), so Δ=o(n) is unnecessary in the intended asymptotic conclusion.
- **Referee:** The core theorem (frozen fraction <= 4/(n+4) for every connected G != K_{Delta+1}) is correct and was verified exhaustively by code on 1139 graphs with frozen colourings, but Section 6's Glauber consequence silently drops the Delta >= 3 hypothesis of the Feghali-Johnson-Paulusma theorem it invokes (false for cycles, e.g. C_9), a routine repair.
- **Already done:** finite frozen-colouring count bound checked (`chromatic-theory/theories/applications/gap_repairs/frozen_coloring_*.v`); Glauber-dynamics statement still open

## 7. Correct but already known, judged publishable by the solver (17)

Referee `ALREADY_KNOWN`. Formalizing still checks the proof, but adds no new result.

### 46. `AX_separation_choosability_grows_min_degree` — Conjecture 1.3

- **Old id:** `1802.03727__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_separation_choosability_grows_min_degree/ — *Separation choosability and dense bipartite induced subgraphs*
- **Campaign / verdict:** sol, claimed `proved`, referee `ALREADY_KNOWN`, difficulty score 3.5 (tier 4); writeup `attacks/1802.03727__00/output.md`
- **Claim:** The bipartite logarithmic lower bound transfers to all graphs by combining an affine-function obstruction for high chromatic number with a dense induced bipartite core in the low-chromatic case.
- **Referee:** The writeup's proof of Conjecture 1.3 verifies completely (every step valid, key construction confirmed by exhaustive computation), but the conjecture as stated already follows from published work — Kwan, Letzter, Sudakov and Tran (arXiv:1810.12144, Combinatorica 2020) proved Esperet–Kang–Thomassé's Conjecture 1.4, which the source paper itself states implies Conjecture 1.3 — although the writeup's quantitative strengthening and its chromatic-number route appear to be new.

### 47. `AX_induced_even_cycle_saturation_edge_addition` — Question 1.7

- **Old id:** `2505.24100__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_induced_even_cycle_saturation_edge_addition/ — *Halfway to induced saturation for even cycles*
- **Campaign / verdict:** sol, claimed `proved`, referee `ALREADY_KNOWN`, difficulty score 3.3 (tier 3); writeup `attacks/2505.24100__00/output.md`
- **Claim:** For every t at least 6, the Cartesian product G=K_{t-1} square C_{2t-3} is induced-C_{2t-2}-free and every non-edge is the pair of ends of an induced P_{2t-2}.
- **Referee:** The writeup's proof that K_{t-1} □ C_{2t-3} answers Question 1.7 is correct and was verified computationally for k=3..8, but the question's affirmative answer has been in the literature since Tennenhouse (2016), as the source paper's own authors acknowledge in arXiv:2606.24763 (Theorem 1.5), and is also subsumed by Choi's arXiv:2608.24202 (Aug 2026).

### 48. `AX_groups_uniform_twin_width_strictly_stronger` — Informal Conjecture (uniform twin-width strictly stronger than twin-width)

- **Old id:** `2204.12330__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_groups_uniform_twin_width_strictly_stronger/ — *Twin-width VII: groups*
- **Campaign / verdict:** sol, claimed `proved`, referee `ALREADY_KNOWN`, difficulty score 3.1 (tier 3); writeup `attacks/2204.12330__00/output.md`
- **Claim:** The proposed group of finitely supported permutations is a witness, because it is elementwise tame under a coset-convex order while its alternating subgroups force arbitrarily large translation grids under every order.
- **Referee:** The proof that Sym_fin(Z) has finite twin-width and infinite uniform twin-width is correct in every step I checked, but the separation was established three weeks before this review in Kontogeorgiou-Miraftab, "Quasirandomness and Uniform Twin-Width" (arXiv:2608.10150, 10 Aug 2026), by the same quasirandomness route with the same D^{1/4} exponent.

### 49. `AX_annulus_digraph_winding_one_crossing_free` — Conjecture 1.2

- **Old id:** `2410.13008__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_annulus_digraph_winding_one_crossing_free/ — *When all directed cycles have length three*
- **Campaign / verdict:** sol, claimed `disproved`, referee `ALREADY_KNOWN`, difficulty score 3.1 (tier 3); writeup `attacks/2410.13008__00/output.md`
- **Claim:** A 12-vertex strongly 2-connected oriented graph has a crossing drawing in the annulus with every directed cycle of winding one, but two equally oriented forced facial triangles preclude any such crossing-free drawing.
- **Referee:** The 12-vertex counterexample is correct and fully verified by exhaustive computation (it even survives the unsigned reading of "winding number one"), but the conjecture was already disproved by Daniel Carter in early 2025 — Seymour's own revised paper (April 16, 2025, Princeton website) relabels 1.2 "False conjecture".

### 50. `AX_modular_chromatic_index_0k_graphs` — Conjecture 13

- **Old id:** `2507.04254__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_modular_chromatic_index_0k_graphs/ — *On Modular Edge Colourings of Graphs*
- **Campaign / verdict:** sol, claimed `disproved`, referee `ALREADY_KNOWN`, difficulty score 2.8 (tier 3); writeup `attacks/2507.04254__00/output.md`
- **Claim:** For every even k there is a finite simple bipartite 0_k-graph G_k with chi'_k(G_k) at least ceil(7k/6).
- **Referee:** The writeup's disproof of Conjecture 13 (a bipartite 0_k-graph with chi'_k >= 7k/6) is correct in every step and verified computationally, but the conjecture was already refuted in the literature in August 2026 (arXiv:2608.10687, Guo-Wu, with the stronger bound (4-2sqrt(2)+o(1))k, and arXiv:2608.02239, Liu-Xu-Yang, refuting the underlying BCK conjecture with bound ~3k/2).

### 51. `AX_rainbow_stacking_random_colorings_sharp_threshold` — [Problem 3.1](https://arxiv.org/abs/2405.14795)

- **Old id:** `2405.14795__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_rainbow_stacking_random_colorings_sharp_threshold/ — *Rainbow Stackings of Random Edge-Colorings*
- **Campaign / verdict:** sol, claimed `proved`, referee `ALREADY_KNOWN`, difficulty score 2.6 (tier 3); writeup `attacks/2405.14795__00/output.md`
- **Claim:** For every fixed m, the first-moment quantity (n!)^(m-1)((r)_m/r^m)^(n choose 2) also gives the sufficient condition, yielding the required single integer threshold.
- **Referee:** The writeup's second-moment proof of a single sharp threshold at mN/(2 log n!) + (2m-1)/6 survives detailed checking, but the same result (same constant, essentially the same method) was already established by Liu, Ma, Xiang and Yan, arXiv:2606.31376 (30 June 2026).

### 52. `AX_bipartite_johnson_lindenstrauss_bounded_norms` — [Conjecture 2.4](https://arxiv.org/abs/1610.00239)

- **Old id:** `1610.00239__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_bipartite_johnson_lindenstrauss_bounded_norms/ — *Optimal compression of approximate inner products and dimension reducti…*
- **Campaign / verdict:** sol, claimed `proved`, referee `ALREADY_KNOWN`, difficulty score 2.6 (tier 3); writeup `attacks/1610.00239__00/output.md`
- **Claim:** A Gaussian quotient map, together with a localized Gaussian-width estimate for an absolute convex hull, gives the target dimension and uniformly bounded output norms.
- **Referee:** The writeup's self-contained proof of Alon-Klartag Conjecture 2.4 survives a full step-by-step and numerical check, but the conjecture was already confirmed in the literature by Vishesh Jain (arXiv:2608.13782, posted 2026-08-13, Remark (iii)) two and a half weeks before this attack was generated.

### 53. `AX_arithmetic_progression_packing_fixed_n` — [Conjecture 7](https://arxiv.org/abs/2603.02786)

- **Old id:** `2603.02786__04`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_arithmetic_progression_packing_fixed_n/ — *Packing arithmetic progressions*
- **Campaign / verdict:** astra, claimed `proved`, referee `ALREADY_KNOWN`, difficulty score 2.5 (tier 2); writeup `attacks_retry/2603.02786__04/output.md`
- **Claim:** A random-composition fractional tiling, rounded by edge-colouring and a reservoir, proves M_k(n)=nk+o(k) for every fixed n.
- **Referee:** The proof is, as far as I can check, correct and complete, but Conjecture 7 was already solved — with the same random-permutation/composition fractional-packing mechanism — by Mao, Wang, Wei and Yang, arXiv:2607.06113 (7 July 2026), two months before this attack ran.

### 54. `AX_c4_orientations_eulerian_avoidable` — [Question 6.4](https://arxiv.org/abs/2510.11311)

- **Old id:** `2510.11311__04`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_c4_orientations_eulerian_avoidable/ — *Extending Thomassen's conjecture to directed graphs*
- **Campaign / verdict:** astra, claimed `disproved`, referee `ALREADY_KNOWN`, difficulty score 2.2 (tier 2); writeup `attacks_retry/2510.11311__04/output.md`
- **Claim:** The anti-directed C4 is not Eulerian-avoidable: Eulerian oriented graphs can have arbitrarily large minimum out-degree while having no anti-directed-C4-free subdigraph of minimum out-degree 2.
- **Referee:** The proof is correct and I verified it by exhaustive/MILP search on D_2 and D_3, but it is Theorem 1.3 of Lei, Wang, Xu and Yang, arXiv:2609.14368 (13 Sep 2026) — the same layered Eulerian construction with the same parameters, posted four days before this attack ran.

### 55. `AX_arithmetic_progression_packing_primes_asymptotic` — [Conjecture 4](https://arxiv.org/abs/2603.02786)

- **Old id:** `2603.02786__01`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_arithmetic_progression_packing_primes_asymptotic/ — *Packing arithmetic progressions*
- **Campaign / verdict:** astra, claimed `proved`, referee `ALREADY_KNOWN`, difficulty score 2.1 (tier 2); writeup `attacks_retry/2603.02786__01/output.md`
- **Claim:** The conjectured asymptotic follows from an exact packing lemma for arithmetic-progression blocks of differences and the dense-subset Green–Tao theorem.
- **Referee:** The proof is correct as written (every step re-derived, Lemma 2 verified exhaustively by computer), but Conjecture 4 had already been proved ten days earlier by Hou, Liu and Zhao, arXiv:2609.07487 (7 Sep 2026), Theorem 1.2, by a different (lattice-covering) route.

### 56. `AX_vertex_transitive_digraph_linear_perimeter_gap` — [Conjecture 4.1](https://arxiv.org/abs/2602.16333)

- **Old id:** `2602.16333__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_vertex_transitive_digraph_linear_perimeter_gap/ — *Long cycles in vertex transitive digraphs*
- **Campaign / verdict:** sol, claimed `proved`, referee `ALREADY_KNOWN`, difficulty score 2.1 (tier 2); writeup `attacks/2602.16333__00/output.md`
- **Claim:** For every m at least 3, a strongly connected 2-outregular Cayley digraph on A4 x Z_m has order 12m and circumference at most 11m, so epsilon = 1/12 works.
- **Referee:** The writeup's proof is correct in every step (machine-verified down to brute force), but the conjecture was already resolved with the identical bound n/12 by Li and Methuku (arXiv:2607.05807, posted 2026-07-07), eight weeks before this attack ran on 2026-08-31.

### 57. `AX_exterior_algebra_self_annihilating_extremal` — [Question on extremal self-annihilating subspaces (Theorem 2.3)](https://arxiv.org/abs/1907.06019)

- **Old id:** `1907.06019__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_exterior_algebra_self_annihilating_extremal/ — *Combinatorics in the exterior algebra and the Bollobás Two Families The…*
- **Campaign / verdict:** sol, claimed `proved`, referee `ALREADY_KNOWN`, difficulty score 2.0 (tier 2); writeup `attacks/1907.06019__00/output.md`
- **Claim:** For n > 2r, the equality case of EKR makes the initial monomials a star, and a rigidity lemma forces the resulting graph map to be exterior multiplication by one vector.
- **Referee:** The writeup's proof of the Scott-Wilmer extremal characterization checks out step by step and computationally, but the result was already proved (over any field, and in a stronger Hilton-Milner form) by Bulavka, Gandini, and Woodroofe, arXiv:2406.17857 (June 2024), published in Trans. London Math. Soc. 12 (2025), e70022.

### 58. `OPG_0_2_graphs_chromatic_number_3` — Three-chromatic (0,2)-graphs

- **Old id:** `three_chromatic_0_2_graphs`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/op/OPG_0_2_graphs_chromatic_number_3/
- **Campaign / verdict:** astra, claimed `proved`, referee `ALREADY_KNOWN`, difficulty score 2.0 (tier 2); writeup `attacks_opg/three_chromatic_0_2_graphs/output.md`
- **Claim:** Every finite 3-colourable (0,2)-graph is bipartite, so none has chromatic number exactly three.
- **Referee:** The proof is correct — I could not break any step, and exhaustive enumeration of all (0,2)-graphs on at most 9 vertices (all graphs, 63 of them), all connected ones up to 14 vertices, and 500+ cube-like (0,2)-graphs up to 64 vertices found chi in {1,2,4} only and confirmed the load-bearing lemma every time — but the identical theorem, with the same two-lemma architecture (unique-4-cycle matching plus "square-closed edge label is a gradient" via a divergence argument), was posted to arXiv as 2607.10125 (Christopher Williamson, 11 July 2026), two months before this attack.

### 59. `OPG_edge_imbalance_multiset_graphic` — Imbalance conjecture

- **Old id:** `imbalance_conjecture`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/op/OPG_edge_imbalance_multiset_graphic/
- **Campaign / verdict:** astra, claimed `proved`, referee `ALREADY_KNOWN`, difficulty score 2.0 (tier 2); writeup `attacks_opg/imbalance_conjecture/output.md`
- **Claim:** A truncated-tail inequality for edge imbalances implies every Erdős–Gallai inequality and proves the conjecture.
- **Referee:** The proof is mathematically correct in every step I could check, but the identical theorem and the identical load-bearing "capacity"/truncated-tail lemma were posted to arXiv as 2608.09191 (Schreib & Yavari, v1 10 Aug 2026, v2 17 Aug 2026), five weeks before this attack ran.

### 60. `OPG_k_edge_outerplanar_embedding_polynomial` — Finding k-edge-outerplanar graph embeddings

- **Old id:** `finding_k_edge_outerplanar_graph_embeddings`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/op/OPG_k_edge_outerplanar_embedding_polynomial/
- **Campaign / verdict:** astra, claimed `proved`, referee `ALREADY_KNOWN`, difficulty score 2.0 (tier 2); writeup `attacks_opg/finding_k_edge_outerplanar_graph_embeddings/output.md`
- **Claim:** A polynomial-time SPQR dynamic program, using a two-bin scheduling recurrence at parallel nodes, computes a minimum edge-outerplanar embedding.
- **Referee:** The SPQR dynamic program is, as far as I could check, correct — every recurrence (S, P, Q, R, the two-arm P-node scheduling DP, the block-cut gluing lemma) reproduces brute force on thousands of small instances — but the theorem was already published two months earlier as arXiv:2607.08110 (H. Yu, 9 July 2026), which resolves Bentz's question by a different route.

### 61. `AX_positive_square_energy_unicyclic_odd_cycle` — [Conjecture 9.1](https://arxiv.org/abs/2506.07264)

- **Old id:** `2506.07264__01`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_positive_square_energy_unicyclic_odd_cycle/ — *Refinement of a conjecture on positive square energy of graphs*
- **Campaign / verdict:** sol, claimed `proved`, referee `ALREADY_KNOWN`, difficulty score 1.8 (tier 2); writeup `attacks/2506.07264__01/output.md`
- **Claim:** An exact phase-integral formula derived from the matching-polynomial decomposition of the characteristic polynomial determines the sign of s+(G)-s-(G).
- **Referee:** The writeup's proof is mathematically correct (every step verified, formulas confirmed computationally), but the conjecture was already proved — by essentially the same matching-polynomial/Coulson-integral argument — in Ning & Zeng, arXiv:2605.24668 (May 23, 2026).

### 62. `AX_tournament_c_fas_paths_matchings_complexity` — [Problem 4.4](https://arxiv.org/abs/2402.10782)

- **Old id:** `2402.10782__01`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_tournament_c_fas_paths_matchings_complexity/ — *Finding forest-orderings of tournaments is NP-complete*
- **Campaign / verdict:** astra, claimed `proved`, referee `ALREADY_KNOWN`, difficulty score 1.5 (tier 1); writeup `attacks_retry/2402.10782__01/output.md`
- **Claim:** The path-FAS problem is NP-complete, whereas the maximum-degree-1 FAS problem is polynomial-time solvable.
- **Referee:** Every step checks out and the 3-SAT reduction proving path-FAS NP-complete is correct and appears genuinely new, but the writeup's other announced half (matching-FAS in O(n^3)) and its self-declared "new ingredient" (the two-state U_m gadget, plus the score-localization lemma and the degree-d dynamic program) are all already published — Davot, Isenmann, Roy, Thiebaut, "Degreewidth: a new parameter for solving problems on tournaments" (arXiv:2212.06007, WG 2023) and Keeney, Lokshtanov, "Degreewidth on semi-complete digraphs" (WG 2024).

## 8. Correct but already known (16)

Referee `ALREADY_KNOWN`, not flagged publishable. Lowest priority.

### 63. `AX_heroes_oriented_star_delta_1_m_m` — Open problem: hero status of $\Delta(1,m,m')$ for degree-4 oriented stars

- **Old id:** `2306.04710__01`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_heroes_oriented_star_delta_1_m_m/ — *On heroes in digraphs with forbidden induced forests*
- **Campaign / verdict:** sol, claimed `proved`, referee `ALREADY_KNOWN`, difficulty score 3.5 (tier 4); writeup `attacks/2306.04710__01/output.md`
- **Claim:** For every m,m' and every orientation F of K_{1,4}, the pair is not dichromatically finite: suitable locally transitive orientations of L(K_{n,n}) are claw-free, directed-triangle-free, and have dichromatic number Ω(√n).
- **Referee:** The writeup's proof is correct in every step (all lemmas re-derived and computationally verified), and it resolves the open problem negatively for all (m, m', F); however, the load-bearing theorem — claw-free, directed-triangle-free oriented graphs of unbounded dichromatic number — was already proved by Aubian and Kuffner (arXiv:2602.08736, Feb 2026), from which the Delta(1,m,m') resolution follows immediately.

### 64. `AX_planar_fractional_vertex_arboricity_2` — Conjecture 1.1

- **Old id:** `2009.12189__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_planar_fractional_vertex_arboricity_2/ — *Fractional vertex-arboricity of planar graphs*
- **Campaign / verdict:** sol, claimed `disproved`, referee `ALREADY_KNOWN`, difficulty score 3.2 (tier 3); writeup `attacks/2009.12189__00/output.md`
- **Claim:** The planar dual of Tutte's 46-vertex non-Hamiltonian cubic polyhedral graph is a 25-vertex triangulation with fractional vertex-arboricity at least 88/43>2.
- **Referee:** The disproof is mathematically correct and computationally confirmed (the 25-vertex Tutte dual has va_f = 33/16 > 2, with the claimed certificate va_f >= 88/43 verified exactly), but Conjecture 1.1 was already refuted by Naserasr, Pham, Pujol and Zhou (arXiv:2505.16808, May 2025) and is also refuted a fortiori by the August 2026 counterexamples to the Albertson-Berman conjecture.

### 65. `AX_pure_pairs_blockade_polynomial_ordered_graphs` — Informal: which graphs H admit polynomial-size pure pairs

- **Old id:** `2111.00532__01`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_pure_pairs_blockade_polynomial_ordered_graphs/ — *Pure pairs. IX. Transversal trees*
- **Campaign / verdict:** sol, claimed `proved`, referee `ALREADY_KNOWN`, difficulty score 3.2 (tier 3); writeup `attacks/2111.00532__01/output.md`
- **Claim:** Under the standard fixed-position meaning of an ordered transversal copy, every finite ordered graph H has the requested property, with exponent c=1/(|H|-1).
- **Referee:** The proof is correct but proves exactly Theorem 1.2 of the source paper (the Erdős–Hajnal–Pach theorem, Geombinatorics 10 (2000), 64-68) — the catalog garbled the actual open question, which is the asymmetric strengthening |X| >= eps*W, |Y| >= eps*W^c, and that remains open.

### 66. `AX_anticomplete_xy_paths_erdos_posa_optimal` — Conjecture 6

- **Old id:** `2512.17232__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_anticomplete_xy_paths_erdos_posa_optimal/ — *An Induced $A$-Path Theorem*
- **Campaign / verdict:** sol, claimed `disproved`, referee `ALREADY_KNOWN`, difficulty score 3.1 (tier 3); writeup `attacks/2512.17232__00/output.md`
- **Claim:** A 16-vertex graph with four induced terminal-to-terminal paths has anti-complete packing number 1 but requires two closed-neighbourhood centers to destroy all (X,Y)-paths.
- **Referee:** The 16-vertex counterexample is correct (every claim verified by brute force) and refutes Conjecture 6 of arXiv:2512.17232v1 at k=2, but this refutation was already in the literature (Albrechtsen–Huynh–Jacobs–Knappe–Wollan, SIAM J. Discrete Math. 2024, Lemma 5 with d=2), and the source authors themselves revised the conjecture to |Z| <= k in arXiv v2 (2026-09-01), explicitly citing that construction.

### 67. `AX_bipartite_concatenation_phi_ceiling_formula` — Informal Conjecture (Introduction) — analogue of Kneser's theorem

- **Old id:** `1902.10878__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_bipartite_concatenation_phi_ceiling_formula/ — *Concatenating bipartite graphs*
- **Campaign / verdict:** sol, claimed `disproved`, referee `ALREADY_KNOWN`, difficulty score 3.1 (tier 3); writeup `attacks/1902.10878__00/output.md`
- **Claim:** For (x,y)=(2/5,1/4), an explicit 5-5-4 tripartite graph gives φ(x,y)=2/5, while every proposed ceiling expression is at least 1/2.
- **Referee:** The writeup's counterexample is mathematically correct, but the precise statement it refutes is the "wild conjecture" that the source paper itself already declares false and refutes with an explicit (13/27, 1/9) example in its introduction; the genuinely open problem (the correct characterisation of phi, "maybe something like it is true") is untouched.

### 68. `AX_oriented_graph_semidegree_non_antidirected_paths` — Question 5.1

- **Old id:** `2503.23191__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_oriented_graph_semidegree_non_antidirected_paths/ — *Two-block paths in oriented graphs of large semidegree*
- **Campaign / verdict:** sol, claimed `disproved`, referee `ALREADY_KNOWN`, difficulty score 3.1 (tier 3); writeup `attacks/2503.23191__00/output.md`
- **Claim:** For every even k at least 4, the balanced blow-up of a directed triangle omits a non-antidirected k-edge path.
- **Referee:** The counterexample is correct and computationally verified, but the identical observation was published by the source paper's own authors in arXiv:2503.23191v2 (1 Aug 2026), whose revised Question 5.1 (excluding "bouncing" paths) remains open.

### 69. `AX_sublinear_separators_product_structure_tree_depth` — Conjecture (product structure with bounded tree-depth and tight clique size)

- **Old id:** `2208.10074__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_sublinear_separators_product_structure_tree_depth/ — *Product structure of graph classes with strongly sublinear separators*
- **Campaign / verdict:** sol, claimed `disproved`, referee `ALREADY_KNOWN`, difficulty score 3.1 (tier 3); writeup `attacks/2208.10074__00/output.md`
- **Claim:** The literal tree-depth formulation is false: square grids force the tree-depth factor to be Ω(log log n) when the clique factor has size O(√n).
- **Referee:** The writeup's disproof of the literal (tree-depth) catalog statement is mathematically correct, but it is exactly Theorem 20 of the source paper itself (d = 2 case), which explicitly notes that the tree-depth strengthening of its Open Problem 6 is false; the actual open conjecture is about bounded tree-width and is untouched.

### 70. `AX_threshold_ramsey_multiplicity_paths_exact` — Conjecture 3

- **Old id:** `2108.00991__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_threshold_ramsey_multiplicity_paths_exact/ — *Threshold Ramsey multiplicity for paths and even cycles*
- **Campaign / verdict:** sol, claimed `disproved`, referee `ALREADY_KNOWN`, difficulty score 3.1 (tier 3); writeup `attacks/2108.00991__00/output.md`
- **Claim:** Explicit colorings of K_{r(P_k)} beat the conjectured count for every even k at least 4 and every odd k at least 5.
- **Referee:** The writeup's disproof of CFSW Conjecture 3 is fully correct (every count verified by brute force for k = 4..8), but the conjecture was already disproved, with strictly stronger bounds, by Huang, Yang and Chen (arXiv:2606.01996, 1 June 2026).

### 71. `AX_symmetric_intersecting_vector_families_polynomial_gain` — Polynomial improvement on symmetric intersecting family size bound

- **Old id:** `1909.11578__02`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_symmetric_intersecting_vector_families_polynomial_gain/ — *On symmetric intersecting families of vectors*
- **Campaign / verdict:** sol, claimed `disproved`, referee `ALREADY_KNOWN`, difficulty score 3.1 (tier 3); writeup `attacks/1909.11578__02/output.md`
- **Claim:** A cyclically invariant family defined by comparing the longest cyclic runs inside a support and its complement is intersecting and has only polynomially small density.
- **Referee:** The disproof is mathematically correct — every step verified analytically and computationally — but the construction and its consequence were already essentially known (Ellis–Kalai–Narayanan arXiv:1702.02607 runs family; Keller–Lifshitz–Marcus arXiv:2307.01356 publish the lifted transitive-symmetric vector family of density exp(-O(k log k log n)) "following a strategy suggested in [EKNS19, Section 4]").

### 72. `AX_cop_number_outerplanar_classification` — Classification of outerplanar graphs by cop number

- **Old id:** `1709.09050__01`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_cop_number_outerplanar_classification/ — *Topological directions in Cops and Robbers*
- **Campaign / verdict:** sol, claimed `proved`, referee `ALREADY_KNOWN`, difficulty score 3.0 (tier 3); writeup `attacks/1709.09050__01/output.md`
- **Claim:** A finite connected outerplanar graph is 1-cop-win exactly when it is chordal—equivalently, when every block on at least three vertices is maximal outerplanar—and otherwise its cop number is 2.
- **Referee:** The proof is correct (verified step-by-step and by exhaustive computation on all 86,356 connected outerplanar graphs with n <= 8), but the exact result was published in 2019 as Theorem 3.9 of Bonato, Breen, Brimkov, Carlson, English, Geneson, Hogben, Perry, Reinhart (arXiv:1903.10087, J. Combinatorics 13(1), 2022), which explicitly resolves this open problem from the Bonato-Mohar survey.

### 73. `AX_s_color_connected_vertices_asymptotic` — Conjecture 4.2

- **Old id:** `2308.15387__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_s_color_connected_vertices_asymptotic/ — *The power of many colours*
- **Campaign / verdict:** sol, claimed `disproved`, referee `ALREADY_KNOWN`, difficulty score 2.9 (tier 3); writeup `attacks/2308.15387__00/output.md`
- **Claim:** A binary vector-space difference colouring gives f(n,r,s) at most 2^s n/(r+1) when r=2^d-1, contradicting the proposed logarithmic factor already for s=1 and even for some s tending to infinity.
- **Referee:** The "counterexample" is verbatim the source paper's own Proposition 3.1 (Liu-Morris-Prince 2007), it refutes only an evident slip in the conjecture's stated range (the paper's own Theorem 1.1 already contradicts the literal "1 <= s" endpoint), and the intended open question — whether f(n,r,s) = s^2 (log r)^{1-o(1)} n / r for log log r <~ s <= sqrt(r)/log r — is untouched.

### 74. `AX_flow_reconfiguration_5_flow_connected` — Problem 1.1

- **Old id:** `2512.17342__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_flow_reconfiguration_5_flow_connected/ — *Nowhere-zero flow reconfiguration*
- **Campaign / verdict:** sol, claimed `disproved`, referee `ALREADY_KNOWN`, difficulty score 2.8 (tier 3); writeup `attacks/2512.17342__00/output.md`
- **Claim:** A simple cubic bridgeless planar graph on 38 vertices, obtained as the dual of two suitably colored icosahedra glued along a face, has a disconnected integer nowhere-zero 5-flow reconfiguration graph.
- **Referee:** The writeup's 38-vertex cubic planar counterexample is fully verified by exhaustive computation (all 235,856 simple cycles checked, twice, by independent enumerations), so F(G,5) is indeed disconnected — but Problem 1.1 was already answered negatively by Theorem 3.4 of the source paper itself (arXiv:2512.17342, since v2, April 2026), as the prompt's own abstract announces.

### 75. `AX_pure_pairs_blockade_transversal_triangle_polynomial` — Question 1.3

- **Old id:** `2111.00532__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_pure_pairs_blockade_transversal_triangle_polynomial/ — *Pure pairs. IX. Transversal trees*
- **Campaign / verdict:** sol, claimed `proved`, referee `ALREADY_KNOWN`, difficulty score 2.8 (tier 3); writeup `attacks/2111.00532__00/output.md`
- **Claim:** For the literal statement, there is always an anticomplete pair of size at least floor(sqrt(W)), so c=1/2 and epsilon=1/2 suffice.
- **Referee:** The proof is internally valid but resolves only a misquoted weakening of Question 1.3 (the catalog dropped the linear requirement |X| >= eps*W); the weakened statement is the K_3 case of Erdos-Hajnal-Pach (Theorem 1.2 of the same paper), and the actual open question remains open.

### 76. `AX_cubic_truncation_strong_6_edge_coloring` — [Problem 4.1](https://arxiv.org/abs/2511.02892)

- **Old id:** `2511.02892__03`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_cubic_truncation_strong_6_edge_coloring/ — *Open problems of the 33rd Workshop on Cycles and Colourings*
- **Campaign / verdict:** sol, claimed `disproved`, referee `ALREADY_KNOWN`, difficulty score 2.7 (tier 3); writeup `attacks/2511.02892__03/output.md`
- **Claim:** As written, the triangular prism is a diamond-free claw-free cubic graph with strong chromatic index 9, not 6.
- **Referee:** The writeup's mathematics is entirely correct, but its "counterexample" is the triangular prism — the exception already flagged in the problem's own preamble (Lv–Li–Zhang 2022) — so it refutes only a strawman literal reading; the intended conjecture is untouched by it (and was later genuinely disproved by an 18-vertex non-prism example, arXiv:2607.23462, July 2026).

### 77. `AX_dom_enum_incomparability_st_free_posets` — [Conjecture 7.1](https://arxiv.org/abs/2004.07214)

- **Old id:** `2004.07214__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_dom_enum_incomparability_st_free_posets/ — *Enumerating minimal dominating sets in the (in)comparability graphs of …*
- **Campaign / verdict:** sol, claimed `proved`, referee `ALREADY_KNOWN`, difficulty score 2.0 (tier 2); writeup `attacks/2004.07214__00/output.md`
- **Claim:** A linear extension of an S_t-free poset gives its incomparability graph linear mim-width at most t-1, and bounded linear mim-width admits a polynomial-time minimal-dominating-set extension oracle, hence polynomial-delay enumeration.
- **Referee:** The proof is mathematically correct and verified computationally, but its "main new observation" (Lemma 1) is literally Proposition 3.6 of Kang-Kwon-Strømme-Telle (TCS 2017), which together with Golovach et al. (Algorithmica 2018) already resolved Conjecture 7.1 before it was posed.

### 78. `AX_color_balanced_bipartite_matching_sqrt_k` — Conjecture 6.1

- **Old id:** `2604.09449__00`
- **Source:** https://graph-theory-ai.github.io/graph-conjectures/arxiv/AX_color_balanced_bipartite_matching_sqrt_k/ — *Colour-balanced subgraphs*
- **Campaign / verdict:** sol, claimed `disproved`, referee `ALREADY_KNOWN`, difficulty score 1.9 (tier 2); writeup `attacks/2604.09449__00/output.md`
- **Claim:** For the standard unnormalised ℓ1 representative discrepancy, the signing h(x_i y_j)=s_j e_i on K_{k,k} forces f_h(M)=k for every perfect matching.
- **Referee:** The counterexample is mathematically correct and refutes the catalog's extracted statement, but that statement is the erroneous v1 form of Conjecture 6.1, which the authors had already corrected in arXiv:2604.09449v2 (2026-07-11); the currently-open colour-balanced conjecture is untouched.
