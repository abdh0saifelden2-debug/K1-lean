import K1Lean.Antipodal
import K1Lean.Leray
import K1Lean.LerayBox
import K1Lean.Parseval
import K1Lean.Surrogate

#check @Surrogate.isProjector
#print axioms Surrogate.projector_idempotent

#check @K1Lean.dft_star
#check @K1Lean.dft_ofReal_conj
#print axioms K1Lean.dft_star
#print axioms K1Lean.dft_ofReal_conj

#check @K1Lean.invDFT_selfConj
#check @K1Lean.invDFT_im_eq_zero
#check @K1Lean.invDFT_eq_ofReal_re
#print axioms K1Lean.invDFT_selfConj
#print axioms K1Lean.invDFT_im_eq_zero
#print axioms K1Lean.invDFT_eq_ofReal_re

#check @K1Lean.surrogateSpectrum
#check @K1Lean.surrogateSpectrum_star
#check @K1Lean.dft_invDFT
#check @K1Lean.norm_surrogateSpectrum
#check @K1Lean.norm_dft_invDFT_surrogateSpectrum
#check @K1Lean.phase_surrogateSpectrum
#print axioms K1Lean.surrogateSpectrum_star
#print axioms K1Lean.dft_invDFT
#print axioms K1Lean.norm_surrogateSpectrum
#print axioms K1Lean.norm_dft_invDFT_surrogateSpectrum
#print axioms K1Lean.phase_surrogateSpectrum

#check @K1Lean.parseval_complex
#check @K1Lean.parseval
#check @K1Lean.parseval_surrogateSpectrum
#print axioms K1Lean.parseval_complex
#print axioms K1Lean.parseval
#print axioms K1Lean.parseval_surrogateSpectrum

#check @K1Lean.mulSpectrum
#check @K1Lean.mulField
#check @K1Lean.mulSurrogate
#check @K1Lean.mulSpectrum_dft_star
#check @K1Lean.mulSpectrum_surrogate_star
#check @K1Lean.mulField_im_eq_zero
#check @K1Lean.mulSurrogate_im_eq_zero
#check @K1Lean.mulField_dft
#check @K1Lean.mulSurrogate_dft
#check @K1Lean.norm_mulSurrogate
#check @K1Lean.phase_mulSurrogate
#check @K1Lean.bin_energy_surrogateSpectrum
#check @K1Lean.bin_energy_mulSurrogate
#check @K1Lean.parseval_mulSurrogate
#print axioms K1Lean.mulSpectrum_dft_star
#print axioms K1Lean.mulSpectrum_surrogate_star
#print axioms K1Lean.mulField_im_eq_zero
#print axioms K1Lean.mulSurrogate_im_eq_zero
#print axioms K1Lean.mulField_dft
#print axioms K1Lean.mulSurrogate_dft
#print axioms K1Lean.norm_mulSurrogate
#print axioms K1Lean.phase_mulSurrogate
#print axioms K1Lean.bin_energy_surrogateSpectrum
#print axioms K1Lean.bin_energy_mulSurrogate
#print axioms K1Lean.parseval_mulSurrogate

#check @K1Lean.antipodalPhase
#check @K1Lean.antipodalPhase_admissible
#check @K1Lean.surrogateSpectrum_antipodalPhase
#check @K1Lean.antipodal
#check @K1Lean.antipodal_energy
#print axioms K1Lean.antipodalPhase_admissible
#print axioms K1Lean.surrogateSpectrum_antipodalPhase
#print axioms K1Lean.antipodal
#print axioms K1Lean.antipodal_energy

#check @K1Lean.leraySymbol
#check @K1Lean.leraySymbol_mulVec_self
#check @K1Lean.leraySymbol_transpose
#check @K1Lean.leraySymbol_vecMul_self
#check @K1Lean.leraySymbol_idem
#check @K1Lean.leraySymbol_neg
#print axioms K1Lean.leraySymbol_mulVec_self
#print axioms K1Lean.leraySymbol_transpose
#print axioms K1Lean.leraySymbol_vecMul_self
#print axioms K1Lean.leraySymbol_idem
#print axioms K1Lean.leraySymbol_neg

#check @K1Lean.Pc_ofReal
#check @K1Lean.P_idem
#check @K1Lean.Pc_idem
#check @K1Lean.divHat_Pc
#check @K1Lean.divHat_P
#check @K1Lean.P'
#check @K1Lean.P'_comp
#check @K1Lean.isProjector_toMatrix
#check @K1Lean.perMode_break
#print axioms K1Lean.Pc_ofReal
#print axioms K1Lean.P_idem
#print axioms K1Lean.Pc_idem
#print axioms K1Lean.divHat_Pc
#print axioms K1Lean.divHat_P
#print axioms K1Lean.P'
#print axioms K1Lean.P'_comp
#print axioms K1Lean.isProjector_toMatrix
#print axioms K1Lean.perMode_break

#check @K1Lean.kappa_zero_iff
#check @K1Lean.kappa_neg
#check @K1Lean.kappa_dot_ne_zero
#check @K1Lean.dft2_apply
#check @K1Lean.dft2_symm_apply
#check @K1Lean.dft2_star
#check @K1Lean.dft2_ofReal_conj
#check @K1Lean.dft2_comp_neg
#check @K1Lean.idft2_selfConj
#check @K1Lean.idft2_im_eq_zero
#check @K1Lean.idft2_eq_ofReal_re
#check @K1Lean.Phat
#check @K1Lean.PhatC
#check @K1Lean.PhatC_eq_leraySymbol
#check @K1Lean.Phat_zero
#check @K1Lean.PhatC_zero
#check @K1Lean.Phat_neg
#check @K1Lean.PhatC_neg
#check @K1Lean.PhatC_idem
#check @K1Lean.dft2Pi_apply
#check @K1Lean.dft2Pi_symm_apply
#check @K1Lean.mulPhat_apply
#check @K1Lean.Pc_apply
#check @K1Lean.P_apply
#check @K1Lean.surrogateSpectrum2
#check @K1Lean.surrogateField
#check @K1Lean.surrogateField_reality
#print axioms K1Lean.kappa_zero_iff
#print axioms K1Lean.kappa_neg
#print axioms K1Lean.kappa_dot_ne_zero
#print axioms K1Lean.dft2_apply
#print axioms K1Lean.dft2_symm_apply
#print axioms K1Lean.dft2_star
#print axioms K1Lean.dft2_ofReal_conj
#print axioms K1Lean.dft2_comp_neg
#print axioms K1Lean.idft2_selfConj
#print axioms K1Lean.idft2_im_eq_zero
#print axioms K1Lean.idft2_eq_ofReal_re
#print axioms K1Lean.PhatC_eq_leraySymbol
#print axioms K1Lean.Phat_zero
#print axioms K1Lean.PhatC_zero
#print axioms K1Lean.Phat_neg
#print axioms K1Lean.PhatC_neg
#print axioms K1Lean.PhatC_idem
#print axioms K1Lean.surrogateField_reality
