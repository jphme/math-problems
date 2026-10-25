/-
Axiom audit: every main theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.
Checked by `lake env lean No19Tiling/Axioms.lean`; the recorded output is in README.md.
-/
import No19Tiling

open No19Tiling

-- Common
#print axioms scale_int_of_primitive3
#print axioms scale_nat_of_primitive3
#print axioms sq_add_sq_mod_four
#print axioms G2Triple.coprime_ab
#print axioms G2Triple.coprime_ac
#print axioms G2Triple.coprime_bc
#print axioms G2Triple.not_three_dvd_c
-- Group2
#print axioms G2Triple.primitive_A
#print axioms G2Triple.primitive_B
#print axioms G2Triple.primitive_C
#print axioms G2Triple.primitive_D
#print axioms G2Triple.countA_not_prime
#print axioms G2Triple.countB_not_prime
#print axioms G2Triple.countC_not_prime
#print axioms G2Triple.countD_not_prime
#print axioms G2Triple.lem_group2
#print axioms G2Triple.lem_group2_both_labelings
-- Group1
#print axioms G1Param.tile_primitive
#print axioms G1Param.triVec_primitive
#print axioms G1Param.isoVec_primitive
#print axioms eq_one_of_prime_sq_mul
#print axioms two_sq_sub_sq_mod_eight
#print axioms three_sq_sub_sq_mod_three
#print axioms G1Param.h_count_prime_mod8
#print axioms G1Param.g_count_prime_mod3
#print axioms G1Param.triquadratic
#print axioms G1Param.isoBeta
#print axioms G1Param.triquadratic_not_19_mod_24
#print axioms G1Param.isoBeta_not_19_mod_24
#print axioms G1Param.shape2Vec_primitive
#print axioms G1Param.shape2_not_prime
#print axioms G1Param.shape5_prime
#print axioms G1Param.shape5_not_3_mod_4
#print axioms G1Param.shape4_prime_no_c_edge
#print axioms G1Param.shape4_not_prime
#print axioms G1Param.shape4Vec_primitive
#print axioms G1Param.shape4_not_prime_rat
#print axioms G1Param.shape5Vec_primitive
#print axioms G1Param.shape5_not_3_mod_4_rat
-- Lattice
#print axioms G1Param.cast_b
#print axioms G1Param.g_eq
#print axioms G1Param.lattice_iff
#print axioms G1Param.decomp_shift
#print axioms G1Param.decomp_a
#print axioms G1Param.decomp_b
#print axioms G1Param.decomp_c_no_b
#print axioms G1Param.decomp_mb2c_lt_k
#print axioms G1Param.decomp_mbc
#print axioms G1Param.leg_no_b_edge
-- RowI
#print axioms norm_b_ne_one
#print axioms G2Triple.two_le_b
#print axioms G2Triple.two_le_a
#print axioms G2Triple.coprime_c_U
#print axioms G2Triple.rowI_primitive
#print axioms G2Triple.rowI_not_prime_of_dvd
#print axioms G2Triple.three_ab_mem
#print axioms G2Triple.not_three_dvd_d
#print axioms G2Triple.exists_three_dvd_a_add_b
#print axioms G2Triple.isCoprime_c
#print axioms G2Triple.isCoprime_d
#print axioms G2Triple.eps_kills_ideal
#print axioms G2Triple.d_mul_eps_rowI
#print axioms G2Triple.eps_rowIBoundary_eq_zero_iff
#print axioms G2Triple.b_dvd_of_rowIBoundary_mem
#print axioms G2Triple.rowI_not_prime
#print axioms G2Triple.rowI_not_prime_rat
#print axioms G2Triple.rowI_swap_not_prime
#print axioms G2Triple.ab_dvd_of_rowE
#print axioms G2Triple.rowE_not_prime
-- Assembly
#print axioms reduction
#print axioms main_theorem
#print axioms main_theorem_19_mod_24
#print axioms no_nineteen
