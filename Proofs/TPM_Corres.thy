theory TPM_Corres
imports
  RRelation
  "../Abstract/Abstract"
  "../lib/NondetCorres"
begin

definition "R \<equiv> UNIV :: (astate \<times> lifted_globals) set"

abbreviation "corres \<equiv> corres_underlying R False True"

locale sable_m = sable_verified +
  assumes TPM_PCRRead_corres:
    "PCRINDEX_rel i i' \<Longrightarrow>
      corres TPM_PCRRead_rel \<top> \<top> (TPM_PCRRead i) (TPM_PCRRead' i')"

      and TPM_NV_ReadValue_corres:
    "\<lbrakk>idx' = of_nat idx; off' = of_nat off\<rbrakk>
      \<Longrightarrow> corres RESULT_rel \<top> (\<lambda>s'. Ball (set (array_addrs data' size')) (is_valid_w8 s'))
      (TPM_NV_ReadValue idx off a)
      (TPM_NV_ReadValue' data' idx' off' size')"

end